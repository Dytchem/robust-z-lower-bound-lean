# Independent verification record

Two things are recorded here.

* **The extended development shipped in the current revision** — explicit finite-order lower
  bounds, 45 modules, 3739 build jobs: the build record, the axiom audit and the `sorry` scan,
  each reproducible with the commands quoted below.
* **The from-scratch clone verifications of the earlier revision** — the `c ≥ 4` asymptotic
  bound only, 30 modules, 3709 jobs — run end to end on two independent machines, both starting
  from the **public clone only** (no files, caches or toolchains copied from any other machine).

## Build and audit — current revision

| Check | Command | Result |
|---|---|---|
| Full build | `LEAN_NUM_THREADS=2 nice -n 19 lake build` | `Build completed successfully (3739 jobs).`, exit 0 |
| Axiom audit | `lake env lean RobustZ/AuditFinal.lean` | 11 headlines, each exactly `[propext, Classical.choice, Quot.sound]`, exit 0 |
| `sorry` / `admit` / `axiom` | comment-stripped scan of all 46 Lean files | **0** occurrences |
| Compiler diagnostics | build log | 81 linter/deprecation warnings (unused `simp` arguments, `push_cast` / `push_neg` / `if_pos` / `if_neg` deprecations, unreferenced variable names), **0 errors**, **0** `declaration uses 'sorry'` |

The 3739 jobs are the extended development's (3709 for the previous revision): 15 new modules
on top of the original 30. The build record was produced in the development tree (mathlib as a
path dependency, see below) and re-checked here with the same command; Lake replayed the modules
that were already built and re-checked the remaining ones, which also confirms that the tree's
olean artifacts and its sources agree.

```
RobustZ/AuditEndgame.lean   RobustZ/AuditFinal.lean     RobustZ/CollarConc.lean
RobustZ/CutoffExplicit.lean RobustZ/EffAudit.lean       RobustZ/EffKernel.lean
RobustZ/Effective.lean      RobustZ/EffectiveCalc.lean  RobustZ/ElementaryBound.lean
RobustZ/Endgame.lean        RobustZ/M5Quad.lean         RobustZ/M5Sharp.lean
RobustZ/M5Sqrt.lean         RobustZ/SharpDeriv.lean     RobustZ/SharpDerivGen.lean
```

Only two of the previously published modules changed: the import list of the root aggregator
`RobustZ.lean` (now 41 imports) and `RobustZ/Audit.lean` (ten more `#print axioms` lines). The
other 29 modules are byte-identical to the published revision, so the earlier verification
record below still covers them.

Mathlib revision: the development tree builds against mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612` (= tag `v4.34.1`), exactly the revision pinned in
`lake-manifest.json`, with `lean-toolchain` = `leanprover/lean4:v4.34.1`.

## What the current revision proves

Statements read off the sources (`RobustZ/*.lean`); `cost θ` is the total `Z`-evolution angle and
`Admissible N φ L α θ` is order-`N` robustness at target `φ`.

| Lean name | File | Statement |
|---|---|---|
| `elementary_bound` | `RobustZ/ElementaryBound.lean` | `0 < φ ≤ π`: `2·(2·(2N+2)!·sin²(φ/4))^{1/(2N+2)} ≤ cost θ` |
| `elementary_bound_pi` | `RobustZ/ElementaryBound.lean` | `φ = π`: `2·((2N+2)!)^{1/(2N+2)} ≤ cost θ` (`q = 2N+2`) |
| `elementary_gt_four_over_e` | `RobustZ/ElementaryBound.lean` | `4(N+1)/e < 2·((2N+2)!)^{1/(2N+2)}`, i.e. the elementary bound dominates the paper's `4/e` per order |
| `endgame_bound` | `RobustZ/CollarConc.lean` | `a ≥ 2`, `N ≥ effN0End K₀ a`: `4(N+1)·(1 − a·(log(2N+2)/(2N+2))^{2/3}) ≤ cost θ` |
| `endgame_bound_of_le` | `RobustZ/CollarConc.lean` | same with `effN0End K a` for any `K ≥ K₀` |
| `endgame_bound_2_3_num` | `RobustZ/CollarConc.lean` | `a = 2.3`, `N ≥ 5010` |
| `endgame_bound_2_2_num` | `RobustZ/CollarConc.lean` | `a = 2.2`, `N ≥ 46000` |
| `all_N_bound_end` | `RobustZ/CollarConc.lean` | the max of the elementary and the sharpened bound, valid for **every** `N ≥ 1` |
| `collar_bound_concrete` | `RobustZ/CollarConc.lean` | `SharpCollarFrom (effN0End K a) 7 770 a 4` — discharges the collar hypothesis the earlier `effective_bound_of_sharp` assumed |
| `c_ge_four`, `c_ge_four_or_grows` | `RobustZ/Theorem.lean` | the previous release's `liminf_{N→∞} Tmin(N,φ)/N ≥ 4` (and its assumption-free dichotomy) |

The sharpened coefficient `4(1 − a(log q/q)^{2/3})` tends to **4** as `N → ∞`, `e` times the
elementary coefficient `4/e ≈ 1.4715`. The elementary bound holds at every `N` with no threshold,
so `all_N_bound_end` is a single unconditional bound valid for all `N ≥ 1`.

## Explicit constants

Every constant is a literal in the sources; nothing is left abstract.

| Quantity | Value | Source |
|---|---|---|
| First-order collar bound | `τ·M₁ ≤ 7·k²·ε` | `RobustZ/CollarConc.lean` (`collar_bound_concrete`) |
| Second-order collar bound | `τ²·M₂ ≤ 770·k⁴·ε` | `RobustZ/CollarConc.lean` (`collar_bound_concrete`) |
| Cutoff derivative constant | `K₀ = 21.1`, with `∀ x, \|σ'(x)\| ≤ K₀` and `∀ x, \|σ''(x)\| ≤ K₀` for `σ = Real.smoothTransition` | `RobustZ/CutoffExplicit.lean` |
| Contour-shift exponent | `μ(ρ) ≥ (47/50)·(1−ρ)^{3/2}` for `1/2 ≤ ρ < 1` (asymptotically optimal constant `2√2/3 = 0.9428…`) | `RobustZ/EffectiveCalc.lean` (`mu_lower_sharp`) |
| Contour-shift error constant | `D₀(ρ) ≤ 13·(1−ρ)^{-1/2}` for `3/4 ≤ ρ < 1` | `RobustZ/EffectiveCalc.lean` (`D0_le_inv_sqrt`) |
| Criterion threshold | `D₀(ρ(q))·e^{−q·μ(ρ(q))} < √(ρ(q))/(C·q)` for every `C > 0` and every `q ≥ q₀(C)`, `q₀(C) = max(10⁴, 7·max(C,100)^{6/7})` | `RobustZ/EffectiveCalc.lean` (`criterion_param_max`) |
| Order threshold | `effN0End K a = max (⌈256a³⌉, ⌈effQ0 7 770 K a 4 / 2⌉, ⌈effQmin a / 2⌉)` | `RobustZ/Endgame.lean` |

`k = 2N+1`, `q = 2N+2`, `ε = epsOf τ (δ'(ρ_a(q))) k`, `ρ_a(q) = 1 − a(log q/q)^{2/3}`.

## Raw output

```
Build completed successfully (3739 jobs).
```

```
'RobustZ.endgame_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'RobustZ.endgame_bound_2_2_num' depends on axioms: [propext, Classical.choice, Quot.sound]
'RobustZ.endgame_bound_2_3_num' depends on axioms: [propext, Classical.choice, Quot.sound]
'RobustZ.all_N_bound_end' depends on axioms: [propext, Classical.choice, Quot.sound]
'RobustZ.collar_bound_concrete' depends on axioms: [propext, Classical.choice, Quot.sound]
'RobustZ.elementary_bound_pi' depends on axioms: [propext, Classical.choice, Quot.sound]
'RobustZ.elementary_gt_four_over_e' depends on axioms: [propext, Classical.choice, Quot.sound]
'RobustZ.kernelProd_sqrt_param' depends on axioms: [propext, Classical.choice, Quot.sound]
'RobustZ.norm_deriv_psiA_scaled_collar_gen' depends on axioms: [propext, Classical.choice, Quot.sound]
'RobustZ.norm_deriv2_psiA_scaled_collar_gen' depends on axioms: [propext, Classical.choice, Quot.sound]
'RobustZ.effective_bound_of_sharp' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`RobustZ/AuditFinal.lean` is a member of the `RobustZ` library target, so `lake build` type-checks
it too; running it explicitly (as above) is what prints the `#print axioms` lines as `info:`
diagnostics. `RobustZ/AuditEndgame.lean`, `RobustZ/EffAudit.lean` and `RobustZ/Audit.lean` are
further `#print axioms` lists for the intermediate layers, all reporting the same three axioms.

The four audit lists (`Audit.lean` 16 lines, `AuditEndgame.lean` 17, `AuditFinal.lean` 11,
`EffAudit.lean` 11) were all re-run in the same conditions as the build; **all 55**
`#print axioms` lines read `[propext, Classical.choice, Quot.sound]` and none reads `sorryAx`.

## From-scratch clone verifications — earlier revision (3709 jobs)

Two independent, from-scratch verifications of the previously published revision
(the `c ≥ 4` asymptotic bound, 30 modules), both starting from the **public clone only**.

| | Machine A | Machine B |
|---|---|---|
| Host | Linux server, **4 cores / 3.8 GB RAM** (+2 GB swap) | Windows 11, **12 logical cores / 31.7 GB RAM** |
| Path | `git clone` → `lake exe cache get` → `lake build` | same, on a **virgin** user profile (`ELAN_HOME` isolated) |
| Result | `Build completed successfully (3709 jobs).` | `Build completed successfully (3709 jobs).` |
| Wall clock | **22m21s** | **19m44s** (pure command time 14m20s) |
| Peak memory | ≥2.4 GB free throughout, no swap pressure | 9,106 MB summed over **6 concurrent** `lean` jobs |

### Machine B: step-by-step timeline (Windows 11, 12 cores)

| Step | Time | Duration | Downloaded |
|---|---|---|---|
| `git clone` | 19:06:02 → 19:06:05 | 3.6 s | 772 KB (65 files, no `.lake`) |
| elan installer | 19:07:02 → 19:07:08 | 6.7 s | 2.5 MB |
| toolchain `lean4:v4.34.1` (fetched by elan from `lean-toolchain`) | 19:07:22 → 19:08:31 | 69.0 s | 562 MiB → 3,095 MB on disk |
| `lake exe cache get` | 19:09:16 → 19:15:27 | 371.1 s | mathlib `.git` 511 MB + 9 deps 370 MB + cache 430 MB → 6,366 MB oleans |
| **`lake build`** | 19:18:56 → **19:25:46** | **409.6 s** | — |
| `lake env lean RobustZ/Audit.lean` | 19:27:32 → 19:28:06 | 33.7 s | — |

Totals: **~1.88 GB** downloaded, **12.7 GB** net disk on `C:`. A second `lake build` after
deleting the project's own oleans reproduced 3709 jobs in 409.3 s.

Two notes for small machines. This Lake version (5.0.0, Lean 4.34.1) has **no `-j` flag** on
`lake build` — it schedules its own concurrency (2 jobs on the 4-core box, up to 6 on the
12-core one, which is why peak memory differs); passing `-j1` fails with
`error: unknown short option '-j'`. Keeping some swap available is still advisable, since
individual module compilations are memory-heavy.

The extended revision has **not** yet been through this two-machine from-scratch treatment; its
build record is the one above, produced in the development tree and re-checked with the same
command.

## Reproduce

```sh
git clone https://github.com/Dytchem/robust-z-lower-bound-lean.git
cd robust-z-lower-bound-lean

# 1. elan, if you do not have it yet
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
export PATH="$HOME/.elan/bin:$PATH"

# 2. mathlib sources + oleans (~430 MB download, ~6.4 GB on disk)
lake exe cache get

# 3. build (expected: Build completed successfully (3739 jobs))
LEAN_NUM_THREADS=2 nice -n 19 lake build

# 4. axiom audit (11 lines, all [propext, Classical.choice, Quot.sound])
lake env lean RobustZ/AuditFinal.lean

# 5. no sorry / admit / axiom in any proof term (comment-stripped scan)
python3 - <<'PY'
import re, pathlib
root = pathlib.Path('.')
def strip(s):
    out, i, d = [], 0, 0
    while i < len(s):
        if d == 0 and s.startswith('--', i):
            j = s.find('\n', i); i = len(s) if j < 0 else j; continue
        if s.startswith('/-', i): d += 1; i += 2; continue
        if s.startswith('-/', i) and d: d -= 1; i += 2; continue
        if d == 0: out.append(s[i])
        i += 1
    return ''.join(out)
files = sorted(list((root/'RobustZ').glob('*.lean')) + [root/'RobustZ.lean'])
hits = [(f, m.group(0)) for f in files for m in re.finditer(r'\b(sorry|admit|axiom)\b', strip(f.read_text()))]
print(f'{len(files)} files scanned, {len(hits)} hits')
PY
```

The repository keeps mathlib as a **pinned git dependency** (`git =
"https://github.com/leanprover-community/mathlib4"`, `rev = "v4.34.1"` →
`d13f23b723b8a846827a245b89c10fc7d3f11612` in `lake-manifest.json`), so a fresh clone builds on
any machine. The development tree the numbers above were recorded in used the same mathlib
revision as a **path** dependency (`/root/lean/mathlib4`); switching between the two layouts only
changes how mathlib is located, not what is compiled — see `README.md`.

## Scope notes

* The paper's numerical tables (heuristic local-search **upper** bounds on `T`) are not
  formalised and are not proved here.
* `N₀` is large (`5010` for `a = 2.3`, `46000` for `a = 2.2`) because of deliberately
  conservative constant bookkeeping, not because of a limitation of the method.
* Exact `4N` is not claimed: the LP-certified constructions show that the band + `q`-th order
  zero + boundedness + endpoint-value constraints alone already allow `T < 4N` from `N ≈ 21`
  on, so a pure carrier-based argument cannot reach `T ≥ 4N`.
