# Independent verification record

Two independent, from-scratch verifications of this repository, both starting from the **public
clone only** (no files, caches or toolchains copied from any other machine).

| | Machine A | Machine B |
|---|---|---|
| Host | Linux server, **4 cores / 3.8 GB RAM** (+2 GB swap) | Windows 11, **12 logical cores / 31.7 GB RAM** |
| Path | `git clone` → `lake exe cache get` → `lake build` | same, on a **virgin** user profile (`ELAN_HOME` isolated) |
| Result | `Build completed successfully (3709 jobs).` | `Build completed successfully (3709 jobs).` |
| Wall clock | **22m21s** | **19m44s** (pure command time 14m20s) |
| Peak memory | ≥2.4 GB free throughout, no swap pressure | 9,106 MB summed over **6 concurrent** `lean` jobs |

Both runs end with the same job count as the development machine (3709), and both were followed by
the axiom audit below.

## Machine B: step-by-step timeline (Windows 11, 12 cores)

| Step | Time | Duration | Downloaded |
|---|---|---|---|
| `git clone` | 19:06:02 → 19:06:05 | 3.6 s | 772 KB (65 files, no `.lake`) |
| elan installer | 19:07:02 → 19:07:08 | 6.7 s | 2.5 MB |
| toolchain `lean4:v4.34.1` (fetched by elan from `lean-toolchain`) | 19:07:22 → 19:08:31 | 69.0 s | 562 MiB → 3,095 MB on disk |
| `lake exe cache get` | 19:09:16 → 19:15:27 | 371.1 s | mathlib `.git` 511 MB + 9 deps 370 MB + cache 430 MB → 6,366 MB oleans |
| **`lake build`** | 19:18:56 → **19:25:46** | **409.6 s** | — |
| `lake env lean RobustZ/Audit.lean` | 19:27:32 → 19:28:06 | 33.7 s | — |

Totals: **~1.88 GB** downloaded, **12.7 GB** net disk on `C:`. A second `lake build` after deleting
the project's own oleans reproduced 3709 jobs in 409.3 s.

## Raw output

```
Build completed successfully (3709 jobs).
```

```
'RobustZ.c_ge_four' depends on axioms: [propext, Classical.choice, Quot.sound]
'RobustZ.c_ge_four_or_grows' depends on axioms: [propext, Classical.choice, Quot.sound]
'RobustZ.h_zero_small_of_tau_le_scaled' depends on axioms: [propext, Classical.choice, Quot.sound]
'RobustZ.kernel_decay_tau_scaled' depends on axioms: [propext, Classical.choice, Quot.sound]
'RobustZ.norm_sum_le_of_moments' depends on axioms: [propext, Classical.choice, Quot.sound]
'RobustZ.h_zero_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
```

A comment-stripped scan of all sources finds **0** occurrences of `sorry`, `admit` or `axiom` in
proof terms (the only textual hits are inside `/-! … -/` doc comments in `RobustZ/FinalSmall.lean`),
and the build logs contain **0** `declaration uses 'sorry'` warnings.

In both runs the checked-out commit was confirmed against `lake-manifest.json`'s pinned mathlib
revision, and `git status --porcelain` was empty before building — i.e. the verified sources are
exactly the published sources.
