# PERF_DEDUP phase 12f — Tok=2 skip es==1 owned-check (2026-10-23)

## One change
`src/ir_lin_exec.c`: the tight-loop `IrLinLoadIndex` Tok=2 path no longer
calls `IrLinCheckOwnedPointerAccess` when stride is 1 (char). Same contract
as Tok=6 in `Step` (`es>=2` only): host `strcpy` often writes `char[]`
without marking the init map. Stride 2/4/8 still check.

Prev binary: `/tmp/babyc_perf12e` (phase 12e local StoreIndex). Original: `/tmp/babyc_baseline`.

## A/B n=5 paired, med, vs prev
| bench                | prev_s   | cand_s   | paired% |
|----------------------|----------|----------|---------|
| call_loop            | 1.265913 | 1.308954 | +1.00%  |
| dfs_rec              | 0.116003 | 0.121711 | +2.91%  |
| struct_score         | 0.360213 | 0.366311 | -0.47%  |
| isort                | 1.143080 | 1.175757 | +0.48%  |
| string_scan          | 1.556185 | 1.420696 | -10.26% |
| string_scan_bounded  | 1.942553 | 1.687880 | -13.11% |

Uninit numbered expects, Linear STRICT A0, cwd `src/tests`: 24/24.
