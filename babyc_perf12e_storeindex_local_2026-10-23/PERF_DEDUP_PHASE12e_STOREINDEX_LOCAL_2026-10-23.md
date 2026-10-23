# PERF_DEDUP phase 12e — IrLinStoreIndex local-array (2026-10-23)

## One change
`src/ir_lin_exec.c`: `IrExecLinLocalsRegsBody` inlines `IrLinStoreIndex` when
`IdxMetaKind==0` and the slot is `LocalOwned` (array decay sets `LocalIsPtr`,
so that bit is not a veto). Tok=2/3/4/8 stay on `Step`. Pointer-into-caller
aliasing (`LocalIsPtr && !LocalOwned`) stays on `Step`. OOB `ProgramFail`s;
init-map bit is set when the map exists.

Prev binary: `/tmp/babyc_perf12d` (phase 12d local LoadIndex). Original: `/tmp/babyc_baseline`.

## A/B n=5 paired, med, vs prev
| bench                | prev_s   | cand_s   | paired% |
|----------------------|----------|----------|---------|
| call_loop            | 1.315248 | 1.286782 | -2.36%  |
| dfs_rec              | 0.110911 | 0.111906 | -1.55%  |
| struct_score         | 0.347882 | 0.347795 | +1.74%  |
| isort                | 1.273280 | 1.144828 | -8.79%  |
| string_scan          | 1.642327 | 1.605291 | -1.29%  |
| string_scan_bounded  | 1.892153 | 1.869194 | -2.64%  |

Smoke uninit/oob/array numbered expects, Linear STRICT A0, cwd `src/tests`: 154/154.
