"""Exercise the two CLIs as black boxes. The oracle and the native comparison use identical recipes."""
import base64
from concurrent.futures import ProcessPoolExecutor
import hashlib
import json
import os
from pathlib import Path
import re
import resource
import shutil
import signal
import subprocess
import tempfile

LIBDIR = 'src/libll'
LIBS = tuple(f'{LIBDIR}/{name}.ll' for name in ('c-lib', 'printf', 'rust-intrinsics'))
ARRAYS = 'tractor/c2rust-tests/arrays/'
TRACTOR = tuple(ARRAYS + name + '.ll' for name in ('arrays', 'incomplete_arrays', 'packed_arrays', 'variable_arrays')) + (LIBS[2],)
DEBUG = 'Examples/debug.ll'
ADD = 'tests/ll/add.ll'
DIRECT = {ADD, 'tests/ll/factorial.ll', 'tests/ll/gep2.ll', 'tests/ub/udiv.ll',
          'tests/ll/byte-freeze.ll', 'tests/perf/calls-fib.ll'}
# assertion.ml's four anchored Str patterns; NOASSERT and historical directives are not tests.
ASSERT = re.compile(rb'^[ \t]*;[ \t]*ASSERT[ \t]+(?:EQ[ \t]*:.*=|(?:SUCCEEDS|FAILS)[ \t]*:|UB[ \t]+[0-9]+[ \t]*:)')
MAIN = re.compile(rb'^[ \t]*define\b[^;\n]*?@(?:main|"main")[ \t]*\(', re.M)
SPAN = re.compile(rb'\[([^][\r\n]+?):(\d+)\.(\d+)-(\d+)\.(\d+)\]')
SUMMARY = re.compile(rb'\nPassed: (\d+)/(\d+)\nFailed: (\d+)/(\d+)\n+\Z')


def inputs_at(root):
    paths = [p.relative_to(root).as_posix() for base in ('tests', LIBDIR, 'tractor', 'utilities', 'Examples')
             for p in (root / base).rglob('*') if p.suffix in ('.ll', '.ll-bad') and p.is_file()]
    # The upstream OCaml harness passes paths to a shell. Only call it with names safe as shell words.
    for p in paths:
        if not re.fullmatch(r'[a-zA-Z0-9_./+=@-]+', p):
            raise ValueError(f'unsupported path for the upstream shell-based oracle: {p!r}')
    return sorted(paths, key=os.fsencode)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def b64(data):
    return base64.b64encode(data).decode('ascii')


def clang_version():
    version = subprocess.check_output(['clang', '--version']).splitlines()[0]
    if not re.search(rb'\bclang version 20\.1\.2\b', version):
        raise ValueError(f'pretty-print cases require clang 20.1.2 on PATH, found: {version!r}')


def limits():
    # One process group per invocation (Clang mode starts descendants). Limits are not golden outcomes.
    resource.setrlimit(resource.RLIMIT_CPU, (240, 241))
    # The native OCaml AST printer overflows the reference host's 8 MiB stack on several large inputs.
    resource.setrlimit(resource.RLIMIT_STACK, (8 << 20, 8 << 20))
    resource.setrlimit(resource.RLIMIT_FSIZE, (512 << 20, 512 << 20))
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))


def run(exe, argv, cwd, stdin):
    env = dict(os.environ, LC_ALL='C', TZ='UTC', OCAMLRUNPARAM='', LLVM_DISABLE_CRASH_REPORT='1')
    with tempfile.TemporaryFile() as out, tempfile.TemporaryFile() as err:
        with subprocess.Popen([exe, *argv], cwd=cwd, env=env, stdin=subprocess.PIPE, stdout=out, stderr=err,
                              start_new_session=True, preexec_fn=limits) as proc:
            try:
                proc.communicate(stdin, timeout=600)
            except subprocess.TimeoutExpired:
                os.killpg(proc.pid, signal.SIGKILL)
                raise RuntimeError(f'wall timeout running {exe.name} {argv!r}') from None
            if proc.returncode < 0:
                raise RuntimeError(f'{exe.name} {argv!r}: killed by signal {-proc.returncode}')
        out.seek(0)
        err.seek(0)
        return proc.returncode, out.read(), err.read()


def artifacts(directory):
    result = {}
    for f in sorted(directory.rglob('*')):
        if not f.is_file():
            continue
        if f.suffix == '.hist':
            # The only unordered artifact is a hash-table listing. Preserve row bytes and final newline.
            data = f.read_bytes()
            if data:
                end = data.endswith(b'\n')
                rows = data[:-1].split(b'\n') if end else data.split(b'\n')
                data = b'\n'.join(sorted(rows)) + (b'\n' if end else b'')
            digest = sha(data)
        else:
            with f.open('rb') as stream:
                h = hashlib.sha256()
                while chunk := stream.read(1 << 20):
                    h.update(chunk)
            digest = h.hexdigest()
        result[f.relative_to(directory.parent).as_posix()] = {'size': f.stat().st_size, 'sha256': digest}
    return result


def assertion_ids(data):
    return [{'line': i, 'directive': line.decode('ascii')} for i, line in enumerate(data.split(b'\n'), 1)
            if ASSERT.match(line)]


def assertions(path, ids, stdout, code, verbose):
    m = SUMMARY.search(stdout)
    if not m:
        if code in (0, 1):
            raise ValueError(f'{path}: suite exit {code} without its pass/fail summary')
        return {'executed': None, 'results': [dict(a, result='no-suite-result') for a in ids]}
    passed, n, failed, total = map(int, m.groups())
    if n != total or n != len(ids) or passed + failed != n or code != int(failed > 0):
        raise ValueError(f'{path}: {len(ids)} source assertions disagree with {m.group(0)!r}, exit {code}')
    if failed:
        detail = stdout[:m.start()].rsplit(b'\n' + path.encode() + b':', 1)[-1]
        marks = re.findall(rb'^ (PASSED|FAILED) - ', detail, re.M)
        if not verbose and failed == n:
            marks = [b'FAILED'] * n
        if len(marks) != n or marks.count(b'FAILED') != failed:
            raise ValueError(f'{path}: cannot match {n} source assertions to suite detail')
    else:
        # assert.ml omits *all* individual PASS rows for an all-pass file, even in verbose mode.
        marks = [b'PASSED'] * n
    return {'executed': n, 'passed': passed, 'failed': failed,
            'results': [dict(a, result=mark.decode().lower()) for a, mark in zip(ids, marks)]}


def category(code, stdout, stderr):
    if code == 0:
        return 'returned' if b'Program terminated with: ' in stdout else 'success'
    if SUMMARY.search(stdout):
        return 'assertion-failure'
    for marker, label in ((b'Uninterpreted Call:', 'uninterpreted-call'), (b'Undefined Behavior:', 'undefined-behavior'),
                          (b'Out Of Memory:', 'out-of-memory'), (b'LLVM Level Exception:', 'llvm-exception'),
                          (b'Failure("Failed:', 'failed'), (b'Parsing error:', 'parse-error'),
                          (b'Error in file ', 'input-error'), (b'InvalidAnonymousId', 'invalid-id'),
                          (b'found unsupported file type:', 'unsupported-extension'),
                          (b'Platform.PlatformError(', 'platform-error'),
                          (b'Stack overflow', 'stack-overflow')):
        if marker in stderr:
            return label
    return 'tool-error'


def run_fixture(task):
    root, vellvm, frontend, path = task
    data = (root / path).read_bytes()
    ids = assertion_ids(data)
    bad_ext = path.endswith('.ll-bad')
    llvm = path.removesuffix('-bad') if bad_ext else path
    roles = ['parser-validator' if bad_ext else 'parse-print']
    if ids:
        roles.append('assertions')
    if MAIN.search(data) and not bad_ext:
        roles.append('entry-main')
    if '.srctgt.' in path or (b'@src(' in data and b'@tgt(' in data):
        roles.append('paired-src-tgt')
    if path in LIBS or path in TRACTOR or path.startswith('utilities/vaargs/printf-src/'):
        roles.append('link-input')
    if path.startswith('tests/perf/'):
        roles.append('perf')
    row = {'path': path, 'sha256': sha(data), 'roles': roles, 'runs': []}

    def case(name, steps, *, files=None, links=(), stdin=b'', local_cwd='.', dirs=()):
        with tempfile.TemporaryDirectory(prefix='vellvm-case-') as tmp:
            sandbox = Path(tmp)
            cwd = sandbox / local_cwd
            cwd.mkdir(parents=True, exist_ok=True)
            staged = files if files is not None else {llvm: data}
            for relative, payload in staged.items():
                dest = sandbox / relative
                dest.parent.mkdir(parents=True, exist_ok=True)
                dest.write_bytes(payload)
            for dep in links:
                dest = cwd / dep
                dest.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(root / dep, dest)
            rec = {'name': name, 'cwd': local_cwd, 'input_files': {p: sha(b) for p, b in staged.items()},
                   'links': list(links), 'stdin_b64': b64(stdin), 'steps': []}
            if dirs:
                rec['empty_dirs'] = list(dirs)
                for d in dirs:
                    (cwd / d).mkdir()
            output_dirs = {'output'}
            for tool, *argv in steps:
                code, out, err = run(vellvm if tool == 'vellvm' else frontend, argv, cwd, stdin)
                if '-op' in argv:
                    output_dirs.add(argv[argv.index('-op') + 1])
                files_out = {p: info for d in sorted(output_dirs) for p, info in artifacts(cwd / d).items()}
                step = {'tool': tool, 'argv': argv, 'exit': code, 'category': category(code, out, err),
                        'stdout_b64': b64(out), 'stderr_b64': b64(err), 'artifacts': files_out}
                spans = SPAN.findall(out + b'\n' + err)
                if spans:
                    step['spans'] = [[f.decode(), *map(int, ns)] for f, *ns in spans]
                if m := re.search(rb'Error in file ([^\n]+?): Parsing error: line (\d+), column (\d+)', err):
                    step['parser_location'] = [m[1].decode(), int(m[2]), int(m[3])]
                if '-test-file' in argv:
                    p = argv[argv.index('-test-file') + 1]
                    step['assertions'] = assertions(p, assertion_ids((cwd / p).read_bytes()), out, code, '-v' in argv)
                rec['steps'].append(step)
            row['runs'].append(rec)
            return rec['steps'][-1]

    parse = case('parse', [('frontend', '-op', 'output', '-histogram-only', llvm)])
    row['parser'] = 'accept' if parse['exit'] == 0 else 'reject'
    case('ast', [('frontend', '-op', 'output', '-print-ast', llvm)])
    # This mode silently skips an original that Clang rejects; it is not evidence for Vellvm's parser.
    pp = case('clang-pretty-print', [('frontend', '-op', 'output', '-test-pp', llvm)])
    pp['clang_comparison'] = ('error' if pp['exit'] else 'compared' if any(p.endswith('.v.ll') for p in pp['artifacts'])
                              else 'original-not-accepted')
    if bad_ext:
        case('original-extension', [('frontend', '-print-ast', path)], files={path: data})
    if ids or path == DEBUG:
        if path == ARRAYS + 'array_tests.ll':
            links = TRACTOR
            args = [a for dep in links for a in ('-l', dep)]
        else:
            links, args = LIBS, ['-L', LIBDIR]
        case('source-assertions', [('vellvm', *args, '-v', '-test-file', llvm)], links=links)
    if path in DIRECT:
        case('direct-assertions', [('vellvm', '-test-file', llvm)])
    if 'entry-main' in roles:
        if path == ARRAYS + 'array_tests.ll':
            links, args = TRACTOR, [a for dep in TRACTOR for a in ('-l', dep)]
        elif path.startswith('utilities/vaargs/tests/'):
            links = ('utilities/vaargs/printf-src/printf.ll',)
            args = ['-l', *links]
        elif path == 'tests/ll/factorial.ll' or path == DEBUG:
            links, args = (), []
        else:
            links, args = LIBS, ['-L', LIBDIR]
        case('interpret-main', [('vellvm', *args, '-i', llvm)], links=links)
    if path == ADD:
        case('emit-and-reparse', [('vellvm', '-emit-llvm', '-op', 'emitted', llvm),
                                  ('frontend', '-op', 'hist-reparsed', '-histogram-only', 'emitted/add.v.ll'),
                                  ('frontend', '-op', 'hist-source', '-histogram-only', llvm)], dirs=('emitted',))
        case('transform-and-collide', [('vellvm', '-v', '-O', '-emit-llvm', llvm, llvm)])
        factorial = 'tests/ll/factorial.ll'
        case('positional-link-order', [('vellvm', '-i', llvm, factorial), ('vellvm', '-i', factorial, llvm)],
             links=(factorial,))
        if data.count(b'ASSERT EQ: i64 14') != 1:
            raise ValueError('wrong-assertion witness must change precisely one expectation')
        case('wrong-assertion', [('vellvm', '-test-file', llvm)],
             files={llvm: data.replace(b'ASSERT EQ: i64 14', b'ASSERT EQ: i64 15')})
        # Exercise immediate directory actions without letting a directory suite stand in for per-file evidence.
        case('frontend-dir', [('frontend', '-print-ast-dir', 'tests/ll')])
        case('frontend-suite', [('frontend', '-set-test-dir', 'tests/ll', '-test')])
        case('initialized-frontend-suite', [('frontend', '-op', 'output'),
                                           ('frontend', '-set-test-dir', 'tests/ll', '-test'),
                                           ('frontend', '-test-pp-dir', 'tests/ll')])
        case('assertion-dir', [('vellvm', '-test-dir', 'tests/ll')])
        case('pretty-print-dir', [('vellvm', '-test-pp-dir', 'tests/ll')])
        case('pretty-print-file', [('vellvm', '-test-pp-file', llvm)])
        case('combined-suite', [('vellvm', '-test')], local_cwd='src')
    if path == 'tests/must-fail/float-literal-size.ll':
        case('accepted-float-literal', [('vellvm', '-op', 'output', '-print-ast', llvm)])
    if path == 'tests/ub/udiv.ll':
        # compare.py's one-directive method preserves instruction line numbers and isolates the UB diagnostic.
        for label, call in (('zero-divisor', 'i32 7, i32 0'), ('ordinary-quotient', 'i32 7, i32 2'),
                            ('poison-dividend', 'i32 poison, i32 2')):
            keep = [a['line'] for a in ids if a['directive'].endswith(f'@udiv({call})')]
            if len(keep) != 1:
                raise ValueError(f'{path}: expected one assertion for {call}')
            text = b'\n'.join((b';' + line if i != keep[0] and ASSERT.match(line) else line)
                              for i, line in enumerate(data.split(b'\n'), 1))
            case(label, [('vellvm', '-test-file', llvm)], files={llvm: text})
    if path == 'tests/ll/args1.ll':
        case('argv-rest', [('vellvm', '-L', LIBDIR, '-interpret', llvm, '-args', 'args1', '-i', 'tail')], links=LIBS)
    if path == DEBUG:
        case('original-debugger', [('vellvm', '-debugger', llvm)],
             stdin=b'h\nb\nExamples/debug.ll\n6\npb\nc\ns\nbt\npg\npl\nrb\n0\nn\nc\n')
        case('live-debugger', [('vellvm', '-debugger', llvm)],
             stdin=b's\nb\nExamples/debug.ll\n2\npb\ns\nbt\npg\npl\nrb\n0\nn\nc\n')
        case('debug-trace', [('vellvm', '-debug', '-i', llvm)])
        missing = 'Examples/missing-ret.ll'
        case('missing-ret-operand', [('vellvm', '-print-ast', missing), ('frontend', '-print-ast', missing)],
             files={missing: b'define i32 @main() {\n  ret i32\n}\n'})
    return row


def fixture_rows(inputs, vellvm, frontend, paths):
    clang_version()
    for exe in (vellvm, frontend):
        if not exe.is_file() or not os.access(exe, os.X_OK):
            raise FileNotFoundError(f'not an executable: {exe}')
    args = ((inputs.resolve(), vellvm.resolve(), frontend.resolve(), p) for p in paths)
    with ProcessPoolExecutor(max_workers=min(6, len(paths) or 1)) as pool:
        yield from pool.map(run_fixture, args)


def write_baseline(inputs: Path, vellvm: Path, frontend: Path, output: Path) -> None:
    """Write cases.jsonl from the pinned oracle binaries. Never call with native binaries."""
    paths = inputs_at(inputs)
    # Both pins already track all thirteen generator targets: 542 tests, 8 .ll-bad,
    # 3 libraries, 5 tractor inputs, 12 utilities and the debugger witness.
    if len(paths) != 571 or not (DIRECT | {DEBUG} | set(LIBS) | set(TRACTOR)) <= set(paths):
        raise ValueError(f'incomplete fixture corpus: {inputs}')
    with tempfile.NamedTemporaryFile(dir=output.parent, mode='w', encoding='utf-8', delete=False) as stream:
        tmp = Path(stream.name)
        try:
            for row in fixture_rows(inputs, vellvm, frontend, paths):
                stream.write(json.dumps(row, separators=(',', ':')) + '\n')
            stream.close()
            tmp.replace(output)
        finally:
            tmp.unlink(missing_ok=True)
