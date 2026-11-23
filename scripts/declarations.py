"""Freeze declarations from a fully compiled, unmodified formal archive.

The .glob ranges are inclusive, in bytes. All output ranges are half-open.
For generated globals without a spelling in the file, name_* is empty; the
statement range is the generating command recorded by Rocq in the .vo.
An applied library functor contributes its module binding, not thousands of
copies of its dependency's globals. Only interactive submodules are traversed.
"""
import argparse
from bisect import bisect_right
from dataclasses import dataclass
import hashlib
import os
from pathlib import Path
import re
import subprocess
import tempfile

from rocq_reference import FORMAL_SWITCH
from source_commands import one_line, sentences
from source_contract import FORMAL, ROOT, source_modules

HEADER = ('source', 'module', 'declaration', 'kind', 'role', 'start_byte', 'end_byte',
          'name_start_byte', 'name_end_byte', 'lean_target', 'rocq_sort', 'rocq_type')
IDENT = r"[^\W\d][\w']*"
QUAL = rf'{IDENT}(?:\.{IDENT})*'
# .glob uses `prf` for several different source commands. In particular it is
# not a way of finding proofs introduced with `Definition`.
INTRO = re.compile(r'\b(Module Type|Theorem|Lemma|Proposition|Corollary|Remark|Fact|Property|'
                   r'Example|Definition|Fixpoint|CoFixpoint|Function|Equations|Instance|'
                   r'Record|Structure|Class|Inductive|CoInductive|Variant|Parameter|Parameters|'
                   r'Axiom|Axioms|Scheme|Let|Module)\b')
THEOREMS = {'Theorem', 'Lemma', 'Proposition', 'Corollary', 'Remark', 'Property', 'Fact', 'Example'}
GLOBALS = {'mod', 'modtype', 'prf', 'ind', 'rec', 'constr', 'proj', 'ax', 'inst', 'def', 'scheme'}
NON_GLOBAL = {'binder', 'var', 'sec', 'not', 'abbrev', 'tac'}

# Rocq 9.2's Module API returns the first inductive of a mutual block and no
# constructors. Expand the block rather than relying on a search blacklist or
# on vernacular keywords. Classification uses the sort of the generalized type.
QUERY = '''Require Import Ltac2.Ltac2 Ltac2.Module Ltac2.Printf.
Set Printing All.
Set Printing Fully Qualified.
Set Printing Width 1000000.
Set Printing Depth 1000000.
Ltac2 emit tag r :=
  let name := String.concat "." (List.map Ident.to_string (Env.path r)) in
  let s := Constr.type (Constr.type (Env.instantiate r)) in
  printf "@@R %s %s %t" tag name s.
Ltac2 field r := match r with
  | Std.IndRef i => let d := Ind.data i in
    List.iter (fun n => let b := Ind.get_block d n in
      emit "ind" (Std.IndRef (Ind.repr b));
      List.iter (fun j => emit "constr" (Std.ConstructRef (Ind.get_constructor b j)))
        (List.range 0 (Ind.nconstructors b))) (List.range 0 (Ind.nblocks d))
  | Std.ConstRef _ => emit "const" r
  | _ => Control.throw Assertion_failure
  end.
Ltac2 dump m :=
  List.iter (fun f => Module.Field.handle f {
    Module.Field.handle_submodule := (fun sub =>
      let k := if Module.is_modtype sub then "modtype" else "mod" in
      printf "@@M %s %a" k (fun _ => Module.to_message) sub);
    Module.Field.handle_reference := field;
    Module.Field.handle_rewrule := (fun _ => Control.throw Assertion_failure)
  }) (Option.get (Module.module_contents m)).
'''


def fail(message):
    raise ValueError(message)


def check_name(name):
    if not re.fullmatch(QUAL, name):
        fail(f'invalid Rocq global name: {name!r}')
    return name


@dataclass(frozen=True)
class Anchor:
    kind: str
    start: int
    end: int
    name_start: int | str
    name_end: int | str
    text: str


class Source:
    def __init__(self, archive, path, blob):
        self.path = path
        self.lib = 'Vellvm.' + path.removeprefix('src/rocq/').removesuffix('.v').replace('/', '.')
        source = archive / path
        self.data = data = source.read_bytes()
        if hashlib.sha1(b'blob %d\0' % len(data) + data).hexdigest() != blob:
            fail(f'{path}: archive source differs from Git at {FORMAL}')
        if not source.with_suffix('.vo').is_file():
            fail(f'{path}: missing compiled .vo')
        self.lines = [0, *(m.end() for m in re.finditer(b'\n', data))]
        self.commands = list(sentences(data))
        self.starts = [x[0] for x in self.commands]
        self.anchors = {}
        records = source.with_suffix('.glob').read_text().splitlines()
        if records[:2] != ['DIGEST ' + hashlib.md5(data).hexdigest(), 'F' + self.lib]:
            fail(f'{path}: wrong .glob digest or library name')
        for rec in records[2:]:
            if rec.startswith('R'):
                continue  # use sites are not declaration sites
            match = re.fullmatch(r'(\w+)\s+(\d+):(\d+) (\S+) (.+)', rec)
            if not match:
                fail(f'{path}: malformed .glob record {rec!r}')
            kind, start, last, scope, name = match.groups()
            if kind in NON_GLOBAL:
                continue
            if kind not in GLOBALS:
                fail(f'{path}: unclassified .glob definition record: {rec}')
            full = check_name('.'.join([self.lib, *([] if scope == '<>' else [scope]), name]))
            a, b = int(start), int(last) + 1
            cs, ce, text = self.command(a, b)
            if name == 'Unnamed_thm' and text.startswith('Goal '):
                endings = (t.strip() for _, _, t in self.commands[bisect_right(self.starts, cs):])
                if next((t for t in endings if t in ('Abort.', 'Qed.', 'Defined.', 'Admitted.')), '') == 'Abort.':
                    continue  # the printing probes have .glob entries but no .vo term
            spelled = data[a:b].decode() == full.rsplit('.', 1)[1]
            if not spelled and kind != 'scheme':
                fail(f'{path}: .glob span for {full} instead names {data[a:b]!r}')
            anchor = Anchor(kind, cs, ce, a if spelled else '', b if spelled else '', text)
            if previous := self.anchors.get(full):
                # Rocq dumps both the inductive and record views of a singleton
                # class. These two records designate exactly the same token.
                same = (a, b) == (previous.name_start, previous.name_end)
                if not same or (previous.kind, kind) not in (('ind', 'rec'), ('constr', 'proj')):
                    fail(f'{path}: duplicate .glob definition {full}')
            self.anchors[full] = anchor
        # The Recdef plugin emits use-site, but not definition, glob records
        # for Function. Take the spelling from its command and scope from the
        # global references, then require this exact name in the kernel below.
        self.functions = {}
        for cs, ce, text in self.commands:
            fn = re.match(rf'Function\s+({IDENT})\b', text)
            if not fn:
                continue
            ref = re.compile(rf'R\d+:\d+ {re.escape(self.lib)} (\S+) {re.escape(fn[1])} \w+')
            scopes = {m[1] for rec in records if (m := ref.fullmatch(rec))}
            if len(scopes) != 1:
                fail(f'{path}:{cs}: missing or ambiguous compiled scope for Function {fn[1]}')
            scope = scopes.pop()
            full = '.'.join([self.lib, *([] if scope == '<>' else [scope]), fn[1]])
            a = cs + len(text[:fn.start(1)].encode())
            b = a + len(fn[1].encode())
            if full in self.anchors or data[a:b] != fn[1].encode():
                fail(f'{path}:{cs}: duplicate or inconsistent Function anchor for {full}')
            anchor = Anchor('def', cs, ce, a, b, text)
            self.anchors[full] = self.functions[full] = anchor

    def command(self, a, b):
        i = bisect_right(self.starts, a) - 1
        if i >= 0:
            s, e, text = self.commands[i]
            if s <= a < b <= e:
                return s, e, text
        fail(f'{self.path}: location {a}:{b} is not in a source command')

    def generated_anchor(self, full, tag, loc):
        if loc is not None:
            a, b = loc
            start, end, text = self.command(a, b)
            spelled = self.data[a:b].decode() == full.rsplit('.', 1)[1]
            return Anchor(tag, start, end, a if spelled else '', b if spelled else '', text)
        # Program and Recdef can omit locations even from the serialized
        # environment. Their generated names identify a unique source command.
        ob = re.fullmatch(r'(.+?)(?:_func)?_obligation_\d+', full)
        if ob and (p := self.anchors.get(ob[1])) and re.match(r'Program\s+(Definition|Fixpoint)\b', p.text):
            return Anchor(tag, p.start, p.end, '', '', p.text)
        for fn, p in self.functions.items():
            scope, base = fn.rsplit('.', 1)
            family = rf'(?:R_)?{re.escape(base)}(?:_(?:\d+|terminate|equation|correct|complete|s?ind|rec|rect))?'
            if full.rpartition('.')[0] == scope and re.fullmatch(family, full.rpartition('.')[2]):
                return Anchor(tag, p.start, p.end, '', '', p.text)
        fail(f'{full}: no .glob entry, serialized declaration location, or unique generator')


def run_rocq(archive, directory, script):
    query = directory / 'InventoryQuery.v'
    query.write_text(script, encoding='utf-8')
    return subprocess.check_output([
        'opam', 'exec', '--switch=' + FORMAL_SWITCH, '--', 'rocq', 'repl', '-q', '-quiet',
        '-batch', '-top', 'InventoryQuery', '-R', archive / 'src/rocq', 'Vellvm',
        '-load-vernac-source', query,
    ], cwd=directory, text=True, encoding='utf-8', env=dict(os.environ, LC_ALL='C', TZ='UTC'))


def name_and_sort(sources, archive, directory):
    imports = '\n'.join(f'Require {s.lib}.' for s in sources) + '\n'
    queries, aliases, scopes = [], {}, {}
    for source in sources:
        walk = [source.lib]
        for full, anchor in source.anchors.items():
            if anchor.kind == 'modtype':
                # Instantiate with a fresh *abstract* module, not concrete
                # values (in particular, not with a particular word width).
                alias = 'Signature' + str(len(aliases))
                aliases['InventoryQuery.' + alias] = full
                queries.append(f'Declare Module {alias} : {full}.')
                walk.append('InventoryQuery.' + alias)
            elif anchor.kind == 'mod' and ':=' not in anchor.text:
                walk.append(full)
        for scope in walk:
            scopes[scope] = source
            queries.append(f'Ltac2 Eval printf "@@B {scope}"; dump module:({scope}).')
    declarations = '\n'.join(q for q in queries if q.startswith('Declare')) + '\n'
    output = run_rocq(archive, directory, QUERY + imports + '\n'.join(queries))
    fields, children, visited = {}, {}, set()
    for line in output.splitlines():
        if line.startswith('@@B '):
            _, scope = line.split()
            if scope in visited or scope not in scopes:
                fail(f'unexpected or duplicate query scope: {scope}')
            visited.add(scope)
        elif line.startswith('@@M '):
            _, kind, short = line.split()
            full = aliases.get(scope, scope) + '.' + short.rsplit('.', 1)[-1]
            if full in children:
                fail('duplicate compiled module: ' + full)
            children[full] = kind
        elif line.startswith('@@R '):
            _, kind, raw, sort = line.split(maxsplit=3)
            check_name(raw)
            owner, name = raw.rsplit('.', 1)
            if owner != scope:
                fail(f'{scope}: member {raw} has wrong owner')
            full = aliases.get(owner, owner) + '.' + name
            if full in fields:
                fail('duplicate elaborated global: ' + full)
            fields[full] = scopes[scope], raw, kind, sort
        elif line.strip() not in ('- : Ltac2.Init.unit = ()', '- : unit = ()', ''):
            fail(f'unrecognized kernel enumeration output: {line!r}')
    if visited != scopes.keys():
        fail(f'missing kernel query for {sorted(scopes.keys() - visited)}')
    expected = {k: a.kind for s in sources for k, a in s.anchors.items() if a.kind in ('mod', 'modtype')}
    if expected != children:
        fail(f'compiled module/.glob disagreement: {sorted(expected.items() ^ children.items())}')
    return imports + declarations, aliases, fields


def details(archive, directory, imports, aliases, fields):
    # About, unlike Check, reads the abstract universes and constraints directly
    # from the global in context; implicit arguments are not instantiated.
    commands = [imports, 'Set Printing All. Set Printing Fully Qualified. Set Printing Universes.',
                'Set Printing Width 1000000. Set Printing Depth 1000000.']
    for i, (_src, raw, _kind, _sort) in enumerate(fields.values()):
        commands.append(f'Redirect "g{i}" About {raw}.')
    run_rocq(archive, directory, '\n'.join(commands))
    for i, (name, (source, raw, tag, sort)) in enumerate(fields.items()):
        report = (directory / f'g{i}.out').read_text()
        first, blank, rest = report.partition('\n\n')
        m = re.fullmatch(re.escape(raw) + r'(@\{[^}]*\})?\s+:\s+(.+)', first, re.S)
        expands = re.search(r'(?m)^Expands to: (Constant|Inductive|Constructor) (\S+)', rest)
        if not blank or not m or not expands or expands[2] != raw:
            fail(f'{name}: cannot read exact type from About: {report[:300]}')
        binders, typ = m.groups()
        typ = one_line(((binders + ' ') if binders else '') + typ)
        if '...' in typ and re.search(r'(?<![\w.])\.\.\.(?![\w.])', typ):
            fail(f'{name}: truncated kernel type')
        for alias, original in aliases.items():
            typ = typ.replace(alias + '.', original + '.')
        loc = re.search(r'(?m)^Declared in library (\S+), line (\d+), characters (\d+)-(\d+)$', rest)
        if loc:
            if loc[1] != source.lib:
                fail(f'{name}: declaration location in a different library: {loc[1]}')
            base = source.lines[int(loc[2]) - 1]
            loc = base + int(loc[3]), base + int(loc[4])
        yield source, name, tag, sort, typ, loc


def classification(name, anchor, tag, sort, generated, in_interface):
    if anchor.kind in ('mod', 'modtype'):
        return ('module-type' if anchor.kind == 'modtype' else
                'module-application' if ':=' in anchor.text else 'module'), 'module'
    if tag == 'constr':
        return ('generated-constructor' if generated else 'constructor'), 'constructor'
    if generated:
        if re.search(r'_obligation_\d+$', name):
            return 'generated-obligation', 'proof'
        return 'generated-' + tag, ('type' if tag == 'ind' else
                                    'proof' if sort in ('Prop', 'SProp') else 'definition')
    if anchor.kind == 'scheme':
        return 'generated-scheme', 'proof' if sort in ('Prop', 'SProp') else 'definition'
    intro = INTRO.search(anchor.text)
    kind = intro[0] if intro else anchor.kind
    if anchor.kind == 'proj':
        return 'field', 'field'
    if anchor.kind == 'ax':
        if in_interface:
            return kind, 'field'
        # A closed proposition assumed by Rocq must be proved in Lean.
        return kind, 'proof' if sort in ('Prop', 'SProp') else 'parameter'
    if anchor.kind == 'inst':
        return 'Instance', 'instance'
    if tag == 'ind' or anchor.kind in ('ind', 'rec'):
        return kind, 'type'
    return kind, ('proof' if kind in THEOREMS or sort in ('Prop', 'SProp') else 'definition')


def cell(value):
    return str(value).replace('\\', '\\\\').replace('\t', '\\t').replace('\n', '\\n').replace('\r', '\\r')


def generate(repo: Path, archive: Path) -> str:
    archive = archive.resolve()
    files, blobs = source_modules(repo, FORMAL)
    sources = [Source(archive, path, blobs[path]) for path in files]
    rows, targets = [], set()
    interfaces = {k for s in sources for k, a in s.anchors.items() if a.kind == 'modtype'}

    def add(s, full, a, tag='', sort='', typ='', generated=False):
        owner, name = full.rsplit('.', 1)
        target = full.replace('Vellvm.Utils.ITreeUtil.', 'Vellvm.Utils.CTreeUtil.', 1)
        if target in targets or any('|' in field for field in (s.path, owner, name)):
            fail(f'colliding coverage key/target: {s.path} {full}')
        targets.add(target)
        kind, role = classification(name, a, tag, sort, generated, owner in interfaces)
        rows.append((s.path, owner, name, kind, role, a.start, a.end, a.name_start, a.name_end,
                     target, sort, typ))

    with tempfile.TemporaryDirectory(prefix='vellvm-declarations-') as tmp:
        directory = Path(tmp)
        imports, aliases, fields = name_and_sort(sources, archive, directory)
        for source in sources:
            for full, anchor in source.anchors.items():
                if anchor.kind in ('mod', 'modtype'):
                    add(source, full, anchor, typ=one_line(anchor.text))
                elif full not in fields:
                    fail(f'{source.path}:{anchor.start}: .glob global absent from .vo: {full}')
        for source, full, tag, sort, typ, loc in details(archive, directory, imports, aliases, fields):
            anchor = source.anchors.get(full)
            generated = anchor is None
            if generated:
                anchor = source.generated_anchor(full, tag, loc)
            add(source, full, anchor, tag, sort, typ, generated)
    if not rows:
        fail('empty declaration inventory')
    rows.sort(key=lambda row: (row[0], row[5], row[1], row[2]))
    return '\n'.join('\t'.join(map(cell, row)) for row in [HEADER, *rows]) + '\n'


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--archive', type=Path, default=Path('/tmp/vellvm-port-formal'))
    parser.add_argument('--repo', type=Path, default=Path(os.environ.get('VELLVM_SRC', ROOT.parent / 'vellvm')))
    parser.add_argument('--output', type=Path, default=ROOT / 'port/declarations.tsv')
    args = parser.parse_args()
    result = generate(args.repo, args.archive)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(result, encoding='utf-8')
    print(f'{args.output}: {result.count(chr(10)) - 1} compiled/source declarations')
