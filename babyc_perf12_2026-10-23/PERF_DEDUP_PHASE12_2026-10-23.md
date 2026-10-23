# PERF_DEDUP phase 12 — Linear VM hot-path (2026-10-23)

## Scope
Tuning Linear VM without changing semantic coverage or `.expect` files.
Environment: GCC `-Wall -O2`, `BABYC_PATH=linear`, `BABYC_STRICT=1`, `BABYC_ACCEL=0`,
`BABYC_NO_KERNEL=1`, `BABYC_NO_SHAPE_FP=1`, `BABYC_NO_MEMO=1`.
Baseline binary: `/tmp/babyc_baseline` (pre-patch).

## Patches (2 files)
- `src/ir_lin_light.c`
  - `IrFnCodeHasPtrSlots` no longer forces Light off under STRICT. Light is used
    when the body is already `LightFrameSafe` (no local-address / kernel / Idx / ptr).
    Scalar leaves (`call_loop`) skip full `IrCallFrame` + install.
  - Removed duplicate `ip++; LIGHT_NEXT();` on Light `IncG`.
- `src/ir_lin_exec.c`
  - `IrLinBrCmp` inlined for 32-bit signed/unsigned compares in the locals-regs
    tight loop; unknown tokens still go through `IrApplyBinOpRaw`.
  - `IrLinIncG` / `LoadGlobal` / `StoreGlobal` skip `LinTryParamIndexedAccess`.
  - Nested Linear scalar frames set `CompactClear=1` when
    `!HasPtrSlots && !HasArrayKernel && !HasKernel && IdxN<=0 && MetaLocalN<=0 && NameLocalN<=0`.

Opcode handlers `LoadGlobal` / `StoreGlobal` / `IncG` were not rewritten
(phases 8/10 already rejected direct encoding).

## A/B vs `/tmp/babyc_baseline` (n=7 paired, med)
| bench                | base_s   | cand_s   | paired% |
|----------------------|----------|----------|---------|
| call_loop            | 1.962659 | 1.342384 | -31.57% |
| dfs_rec              | 0.127724 | 0.125180 | -1.28%  |
| struct_score         | 0.432772 | 0.399691 | -6.66%  |
| isort                | 1.613504 | 1.562288 | -3.57%  |
| string_scan          | 1.982063 | 1.835988 | -7.26%  |
| string_scan_bounded  | 2.374345 | 2.149438 | -10.02% |

All six benches printed the expected last line.

## Gates
- Linear STRICT A0: 1148/1148, canonical invalid_nodes=0
- Linear STRICT A1: 1148/1148, canonical invalid_nodes=0
- uninit + Light-related numbered expects, 4 modes: 104/104
- `tools/test_fp_modes.py`: 132/132
- `tools/test_bytecode_vm.py`: 81/81
- `tools/test_string_scan_fastpath.py`: PASS
- Linear no-STRICT / tree matrix: not completed this pass (token cutoff)

## Not done
- Linear not promoted to default (binary32 still open).
- No further opcode-handler rewrites.

## Delta files
- `src/ir_lin_light.c`
- `src/ir_lin_exec.c`
- this report
