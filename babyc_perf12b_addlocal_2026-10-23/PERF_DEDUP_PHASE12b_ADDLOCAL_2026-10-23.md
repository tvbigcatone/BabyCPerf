# PERF_DEDUP phase 12b — IrLinAddLocal tight-loop inline (2026-10-23)

## One change
`src/ir_lin_exec.c`: `IrExecLinLocalsRegsBody` no longer always `Step()`s
`IrLinAddLocal`. Scalar locals (not Light, not ptr, not owned blob) add in-place
with the same narrow/init as `Step`. Light/ptr/owned still fall back to `Step`.

Prev binary: `/tmp/babyc_perf12` (phase 12). Original: `/tmp/babyc_baseline`.

## A/B n=5 paired, med, vs prev
| bench                | prev_s   | cand_s   | paired% |
|----------------------|----------|----------|---------|
| call_loop            | 1.320168 | 1.279421 | -3.34%  |
| dfs_rec              | 0.120289 | 0.117746 | -0.83%  |
| struct_score         | 0.373164 | 0.387445 | +3.87%  |
| isort                | 1.527181 | 1.453475 | -4.25%  |
| string_scan          | 1.832827 | 1.822198 | -0.23%  |
| string_scan_bounded  | 2.176814 | 2.135311 | -1.28%  |

vs original baseline: call_loop -34.7%, dfs_rec -6.8%, struct_score -9.7%,
isort -7.4%, string_scan -8.6%, string_scan_bounded -7.9%.

Smoke uninit/incdec 30/30 (Linear STRICT A0 + Linear A0).
