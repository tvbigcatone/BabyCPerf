# PERF_DEDUP phase 12d — IrLinLoadIndex local-array (2026-10-23)

## One change
`src/ir_lin_exec.c`: `IrExecLinLocalsRegsBody` inlines `IrLinLoadIndex` when
`IdxMetaKind==0` (local array), owned/ptr slot, stride 1/2/4/8. OOB still
`ProgramFail`s. Uninit misses (no map or map bit 0) fall back to `Step` so
caret/diagnostics stay on the full path. Tok=2/6/7/ROW_DECAY unchanged.

AddRegLocal tight-loop attempt was measured as noise (`string_scan` +4.9%)
and reverted before this change.

Prev binary: `/tmp/babyc_perf12c` (phase 12c Tok=2). Original: `/tmp/babyc_baseline`.

## A/B n=5 paired, med, vs prev
| bench                | prev_s   | cand_s   | paired% |
|----------------------|----------|----------|---------|
| call_loop            | 1.318730 | 1.339724 | +1.59%  |
| dfs_rec              | 0.124735 | 0.124935 | +0.42%  |
| struct_score         | 0.374359 | 0.378022 | +1.00%  |
| isort                | 1.455816 | 1.280064 | -14.10% |
| string_scan          | 1.568555 | 1.612776 | +2.42%  |
| string_scan_bounded  | 2.018613 | 1.945990 | -0.83%  |

Smoke uninit/oob/array numbered expects, Linear STRICT A0, cwd `src/tests`: 154/154.
