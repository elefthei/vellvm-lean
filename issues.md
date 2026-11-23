# The 36 failing assertions in the Vellvm baseline

**Resolved for port parity; not fixed as LLVM semantics.** Of 3,877 source assertions, 3,841 passed and 36 failed in [the pinned Vellvm executable](https://github.com/vellvm/vellvm/tree/7f0610c38d829b79bf6e867edf410c9e6f928f98). The Lean executable reproduced all 36 failures across the same 11 files. The port kept the original assertions, their `FAILED` results, diagnostics, and suite exit status `1`. It did not skip them or change their expected answers to make the suites green.

Each link below points to the **assertion**, not the instruction it exercises. `UB 87`, for example, means the fixture expects undefined behavior and names instruction line 87. The [assertion runner](Vellvm/CLI/Assertions.lean#L150-L168) checks the outcome category, not that the diagnostic reports that line. There are 33 `ASSERT UB`, two `ASSERT EQ` expecting poison, and one `ASSERT SUCCEEDS`. The **observed** column is what both executables did.

## 1. Function memory effects (6)

The calls parse and run. The semantic [call-attribute checks](Vellvm/Semantics/Attributes/Memory.lean) do not enforce the callee's permitted reads and writes under `memory(...)`. Each wrapper therefore finishes and returns `i32 0`. Fixing this upstream requires checking accesses during the call, including their origin; comparing memory before and after would miss issue 3.

| # | Assertion | Expected | Observed | Why it fails |
|---:|---|---|---|---|
| 1 | [`@call_mem_none_writes_global`](tests/ub/call-fn-attrs.ll#L96) | UB 87 | `i32 0` | A `memory(none)` callee stores `1` in `@g`. |
| 2 | [`@call_mem_read_writes_global`](tests/ub/call-fn-attrs.ll#L108) | UB 99 | `i32 0` | A `memory(read)` callee writes `@g` despite its read-only contract. |
| 3 | [`@call_mem_read_writes_same_value`](tests/ub/call-fn-attrs.ll#L123) | UB 114 | `i32 0` | The callee reads `@g` and writes the same value back. The store itself violates `memory(read)`. |
| 4 | [`@call_mem_argmem_read_writes_arg`](tests/ub/call-fn-attrs.ll#L137) | UB 127 | `i32 0` | `memory(argmem: read)` permits reading through `%p`; the callee stores through it. |
| 5 | [`@call_mem_argmem_only_writes_global`](tests/ub/call-fn-attrs.ll#L153) | UB 143 | `i32 0` | `memory(argmem: readwrite)` allows the store through `%p`, but not the subsequent store to the unrelated global `@g`. Both execute. |
| 6 | [`@call_mem_none_callsite`](tests/ub/call-fn-attrs.ll#L166) | UB 157 | `i32 0` | This time `memory(none)` is on the **call site**. It does not stop the callee's global store. |

## 2. Pointer permissions, capture, and initialization (20)

The model checks allocation provenance, but that is not the same as tracking *which argument or escaped copy* authorized an access. The [upstream gap analysis](tests/ub/README.md#L134-L157) distinguishes these missing checks from implemented value attributes such as `nonnull` and `noundef`. In particular, the three assertions in `call-ptr-attrs-unparsed.ll` are **not parse failures** at this pin.

| # | Assertion | Expected | Observed | Why it fails |
|---:|---|---|---|---|
| 7 | [`@call_readonly_writes`](tests/ub/call-ptr-attrs.ll#L52) | UB 42 | `i32 0` | The callee stores through its `readonly` parameter. The restriction belongs to that access path, not to the entire allocation. |
| 8 | [`@call_readonly_callsite`](tests/ub/call-ptr-attrs.ll#L83) | UB 73 | `i32 0` | The caller supplies `readonly`; the callee still writes through that argument. |
| 9 | [`@call_readnone_reads`](tests/ub/call-ptr-attrs.ll#L97) | UB 86 | `i32 0` | The callee loads through a `readnone` parameter and reads the zero the caller stored. |
| 10 | [`@call_readnone_writes`](tests/ub/call-ptr-attrs.ll#L110) | UB 100 | `i32 0` | The callee stores through a `readnone` parameter. |
| 11 | [`@captures_address_load`](tests/ub/call-ptr-attrs.ll#L171) | UB 167 | `i32 5` | After return, the caller dereferences a stashed `captures(address)` copy. That copy should allow address inspection, not reading the pointee. |
| 12 | [`@captures_none_store`](tests/ub/call-ptr-attrs.ll#L197) | UB 193 | `i32 0` | A pointer stashed despite `captures(none)` is recovered from `@slot` and used for a store after return. |
| 13 | [`@captures_read_provenance_store`](tests/ub/call-ptr-attrs.ll#L219) | UB 215 | `i32 0` | The stashed copy has read provenance only, but the later store succeeds. |
| 14 | [`@captures_none_callsite`](tests/ub/call-ptr-attrs.ll#L241) | UB 237 | `i32 0` | `captures(none)` is on the call-site argument. The escaped copy still works for a later write. |
| 15 | [`@captures_none_returned`](tests/ub/call-ptr-attrs.ll#L255) | UB 251 | `i32 0` | The escape is through the return value rather than `@slot`. The caller stores through the returned `captures(none)` pointer. |
| 16 | [`@call_nofree_frees`](tests/ub/call-ptr-attrs.ll#L272) | UB 262 | `i32 0` | The callee frees the allocation **through** its `nofree` parameter before returning. |
| 17 | [`@call_noalias_conflict`](tests/ub/call-ptr-attrs.ll#L304) | UB 293 | `i32 2` | `%p` and `%q` point to the same cell. The callee writes `1` through `noalias %p`, then `2` through `%q`; the load through `%p` sees `2`. |
| 18 | [`@call_init_volatile`](tests/ub/call-ptr-attrs.ll#L345) | UB 335 | `i32 0` | The first write to the `initializes((0, 4))` range is volatile. The model does not distinguish that first write from one after initialization. |
| 19 | [`@call_init_atomic`](tests/ub/call-ptr-attrs.ll#L358) | UB 348 | `i32 0` | The first write to the same range is atomic (`seq_cst`); the required first-write restriction is not enforced. |
| 20 | [`@call_init_reads_first`](tests/ub/call-ptr-attrs.ll#L391) | `i32 poison` | `i32 9` | A load before the callee initializes the range reads the caller's `9`. The later store of `1` does not change the value already read. |
| 21 | [`@call_writable_constant`](tests/ub/call-ptr-attrs.ll#L406) | UB 402 | `i32 0` | `@const_word` is readable for four bytes, but `writable dereferenceable(4)` also requires write access on entry. Checking readability alone lets the call return. |
| 22 | [`@captures_ret_other_path`](tests/ub/call-ptr-attrs-unparsed.ll#L47) | UB 43 | `i32 0` | Capture is permitted through `ret:` only. The caller writes through the separately stashed `@slot` copy, not the permitted return value. |
| 23 | [`@md_captures_address`](tests/ub/call-ptr-attrs-unparsed.ll#L59) | UB 55 | `i32 0` | Store metadata `!captures !{!"address"}` restricts the stored copy. Reloading it and writing through it still succeeds. |
| 24 | [`@md_captures_read_provenance`](tests/ub/call-ptr-attrs-unparsed.ll#L71) | UB 67 | `i32 4` | The stored copy permits the load of `4`, not the following store. No UB is raised, so the function returns the earlier load. |
| 25 | [`@call_nofreeobj_frees_other`](tests/ub/call-ptr-attrs-nofreeobj.ll#L27) | UB 17 | `i32 0` | `%p` has `nofreeobj`. Freeing the same object via `%q` is forbidden even though the free is not through `%p`. Compare issue 16. |
| 26 | [`@free_nofreeobj_return`](tests/ub/call-ptr-attrs-nofreeobj.ll#L40) | UB 36 | `i32 0` | The caller frees the object after receiving a `nofreeobj` return value. The model retains no such restriction after the call. |

## 3. Call targets and `inbounds` pointer arithmetic (3)

A missing function-table entry falls back to an [external call](Vellvm/Semantics/Denotation.lean#L58). Separately, the [GEP checks](Vellvm/Semantics/Operations/Gep.lean#L107) handle arithmetic wrap and a null base, but not the bounds of the originating allocation at each intermediate address. The distinction matters: a bad `inbounds` result should be **poison**; it is the later load through that pointer that should raise UB.

| # | Assertion | Expected | Observed | Why it fails |
|---:|---|---|---|---|
| 27 | [`@call_data_pointer`](tests/ub/call.ll#L66) | UB 62 | `Uninterpreted Call` | `@data` names an `i32` global, not code. Lookup misses and takes the external-call path; the runner correctly refuses to count that error as UB. |
| 28 | [`@gep_inbounds_oob_and_back`](tests/ub/getelementptr.ll#L51) | UB 47 | `i32 10` | Index `5` is beyond one-past a four-element array. Stepping back by `5` recovers element 0 numerically, but should not undo poison from the first GEP. |
| 29 | [`@gep_inbounds_oob_load`](tests/ub/getelementptr.ll#L73) | UB 69 | `i32 2` | Index `3` exceeds one-past a two-element allocation. The second GEP backs up by `2`; the model reads element 1 instead of propagating poison. |

## 4. Constant storage and stack lifetimes (6)

[`Write_byte`](Vellvm/Semantics/Implementations/Memory/Primitives.lean#L138-L142) checks that the byte exists and its allocation ID permits access, but not that the global was declared `constant`. The linked [`llvm.lifetime.start.p0` and `llvm.lifetime.end.p0`](src/libll/rust-intrinsics.ll#L34-L40) return without changing memory state. These are different gaps: a dead stack load should yield poison, while a store to the same dead object should raise UB.

| # | Assertion | Expected | Observed | Why it fails |
|---:|---|---|---|---|
| 30 | [`@store_to_constant_global`](tests/ub/store.ll#L148) | UB 144 | `i32 0` | A plain store writes `8` to constant global `@k`; the function returns normally. |
| 31 | [`@memcpy_to_constant`](tests/ub/intrinsics/memcpy.ll#L107) | UB 103 | `i32 0` | `memcpy` writes four bytes from `@src` into constant destination `@k`. This is not an overlap or bounds failure. |
| 32 | [`@memset_constant`](tests/ub/intrinsics/memset.ll#L63) | UB 59 | `i32 0` | `memset` writes four zero bytes to `@k`; the intrinsic reaches the same writable-byte path as a plain store. |
| 33 | [`@load_after_lifetime_end`](tests/ub/load.ll#L462) | `i32 poison` | `i32 1` | Ending the lifetime leaves the stored `1` readable. The fixture expects poison, not a trap. |
| 34 | [`@store_after_lifetime_end`](tests/ub/store.ll#L167) | UB 163 | `i32 0` | A store of `2` after `lifetime.end` still finds allocated, writable bytes. |
| 35 | [`@store_before_lifetime_start`](tests/ub/store.ll#L180) | UB 174 | `i32 0` | The store comes before the object's first `lifetime.start`. The model treats the allocation as live immediately. |

## 5. Rust array fixture: an unexpected UB (1)

| # | Assertion | Expected | Observed | Why it fails |
|---:|---|---|---|---|
| 36 | [`@_ZN11array_tests11test_arrays11test_buffer17h19ec7a6a9cf167f6E`](tractor/c2rust-tests/arrays/array_tests.ll#L18821) | Success | UB at `7996.10–7996.104` | `test_buffer` reaches a pointer load with `!align 4` and `!noundef`. The alignment promise fails for the loaded pointer; `!noundef` turns the resulting poison into UB. |

The `align 8` on [the load](tractor/c2rust-tests/arrays/array_tests.ll#L7995-L7996) describes the **slot** being read. The [`!align !446`](tractor/c2rust-tests/arrays/array_tests.ll#L12980) metadata promises four-byte alignment for the **pointer value** in the slot. That pointer is a bitcast of [`@alloc21`, declared `align 1`](tractor/c2rust-tests/arrays/array_tests.ll#L124). In a temporary copy run with the pinned oracle, removing only `!align !446` let the load pass with `!noundef` intact. The run then stopped at the [following `memcpy`](tractor/c2rust-tests/arrays/array_tests.ll#L8002), which also promises four-byte source alignment. Removing just the load annotation is **not** a fix. An upstream correction needs to reconcile the object's alignment with both uses.

## How to reproduce and interpret the result

For a single suite, run the same linked command as the oracle, for example:

```sh
lake exe vellvm -L src/libll -v -test-file tests/ub/call-fn-attrs.ll
```

That suite should report `Passed: 12/18`, `Failed: 6/18`, and exit `1`. For the Rust fixture, use the explicit `-l` arguments in its [Makefile](tractor/c2rust-tests/arrays/Makefile) or its `source-assertions` record in [`port/cases.jsonl`](port/cases.jsonl); it uses four array modules plus `rust-intrinsics.ll`.

For the port's acceptance test, build both binaries and run `python3 scripts/check-examples.py` with Clang 20.1.2 on `PATH`. The [comparator](scripts/check-examples.py) checks the per-assertion outcomes against the independent oracle, so **zero parity differences does not mean zero failed assertions**. If an upstream change fixes any of these issues, update the pinned reference and regenerate the evidence before expecting a different result here. The eight large-AST printer stack overflows are separate CLI artifact cases, not part of these 36 assertions.
