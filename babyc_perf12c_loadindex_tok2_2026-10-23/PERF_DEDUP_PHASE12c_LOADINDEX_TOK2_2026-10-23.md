# PERF_DEDUP phase 12c — IrLinLoadIndex Tok=2 tight-loop (2026-10-23)

## One change
`src/ir_lin_exec.c`: `IrExecLinLocalsRegsBody` inlines `IrLinLoadIndex` when
`Tok==2` and `Imm` is stride 1/2/4/8 (`*p` load). Packed `Imm>8` (source
coords) and every other index form still go through `LinTryParamIndexedAccess`
or `Step`. Null check + `IrLinCheckOwnedPointerAccess(..., Mark=0)` kept.

Prev binary: `/tmp/babyc_perf12b` (phase 12b AddLocal). Original: `/tmp/babyc_baseline`.

## A/B n=5 paired, med, vs prev
| bench                | prev_s   | cand_s   | paired% |
|----------------------|----------|----------|---------|
| call_loop            | 1.289054 | 1.298740 | +1.04%  |
| dfs_rec              | 0.115576 | 0.116205 | +0.85%  |
| struct_score         | 0.388548 | 0.359987 | -8.88%  |
| isort                | 1.435310 | 1.443696 | -0.10%  |
| string_scan          | 1.791251 | 1.582925 | -11.21% |
| string_scan_bounded  | 2.114988 | 1.956318 | -7.50%  |

Linear STRICT A0: 1148/1148, canonical invalid_nodes=0.
Smoke false-positive on `267_typedef_ptr_local.c` was cwd (fopen relative);
matrix cwd `src/tests` matches expect.
