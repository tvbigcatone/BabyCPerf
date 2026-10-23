# PERF_DEDUP phase 12g — Tok=2 IrLoadByElemSize (2026-10-23)

## One change
`src/ir_lin_exec.c`: tight-loop `IrLinLoadIndex` Tok=2 loads through
`IrLoadByElemSize` (header inline) instead of `IrLoadPtrElem` (out-of-line
switch, including TypePointer). Stride is already 1/2/4/8. Owned-check
policy from 12f unchanged.

Prev binary: `/tmp/babyc_perf12f` (phase 12f skip char owned-check).
Original: `/tmp/babyc_baseline`.

## A/B n=5 paired, med, vs prev
| bench                | prev_s   | cand_s   | paired% |
|----------------------|----------|----------|---------|
| call_loop            | 1.289774 | 1.264324 | -1.71%  |
| dfs_rec              | 0.112487 | 0.116277 | +1.61%  |
| struct_score         | 0.331593 | 0.327062 | -6.29%  |
| isort                | 1.128255 | 1.134843 | +0.58%  |
| string_scan          | 1.379968 | 1.336451 | +0.06%  |
| string_scan_bounded  | 1.678199 | 1.654261 | +0.63%  |

Uninit numbered expects, Linear STRICT A0, cwd `src/tests`: 24/24.
