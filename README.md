# Robust composite `Z` rotations — explicit finite-order lower bounds, machine-checked

How much `Z`-evolution is unavoidable if a target `Z` rotation must stay accurate to order `N`
against an unknown error in the `Z` strength, when exact transverse (`X`) rotations are free?

Paper: [`paper/main.pdf`](paper/main.pdf) (submission format) ·
[`paper/main_arxiv.pdf`](paper/main_arxiv.pdf) (single-spaced) ·
verification page: <https://show.dytchem.cn/lean/>

## The model

* A sequence is an interleaving of costly `Z` evolutions and free `X` rotations.
* `T` = the total nominal `Z` angle of the sequence.
* Order-`N` robust = the evolution equals the target `Z(φ)` at zero error, and its first `N`
  derivatives with respect to the error scale vanish there.
* Throughout, `q := 2N+2`, and `0 < φ ≤ π` is the target angle.

## The bounds

Every order-`N` robust sequence satisfies each of the following.

**1. Direct Taylor bound (coefficient `2/e ≈ 0.736`), every `N`:**

$$T \ge 2\ [\ 2\ (N+1)!\ \sin(\phi/4)\ ]^{1/(N+1)}$$

**2. Elementary bound (coefficient `4/e ≈ 1.472`), every `N`:**

$$T \ge 2\ [\ 2\ q!\ \sin^{2}(\phi/4)\ ]^{1/q}$$

**3. Jensen bound (coefficient `2\pi/e ≈ 2.311`), every `N`:**

$$T \ge \frac{\pi q}{e}\ \sin^{2/q}(\phi/4)$$

**4. Weak-constant variant (coefficient `8/e ≈ 2.943`), every `N`:**

$$T \ge 4\ [\ \frac{q!\ \sin^{4}(\phi/4)}{10^{8}\ q^{4}}\ ]^{1/q}$$

**5. Exact criterion (coefficient `→ 4`) — an explicit, checkable inequality:**

> If the closed-form quantity of the paper (§VI and Appendix A) falls below `sin²(φ/4)` at a
> trial bandwidth `τ`, then `T > 2τ`.

At `φ = π` the criterion certifies, inside Lean and with every constant explicit,

$$T > 2,\ 2,\ 4,\ 8,\ 10,\ 14,\ 16,\ 18,\ 22,\ 24,\ 28 \qquad (N = 2,\dots,12),$$

and its closed form gives, for `N ≥ 17557`,

$$T \ge 4(N+1)\ [\ 1 - 6\ (\log q / q)^{2/3}\ ],$$

which is the linear growth `T ≥ (4+o(1)) N` and hence `liminf T_min / N ≥ 4`.

### How the coefficients compare

| bound | coefficient of `N` | holds for |
| --- | --- | --- |
| direct Taylor | `2/e ≈ 0.736` | every `N` |
| elementary | `4/e ≈ 1.472` | every `N` |
| Jensen | `2π/e ≈ 2.311` | every `N` |
| weak-constant variant | `8/e ≈ 2.943` | every `N` (constant `10⁸`) |
| exact criterion | `→ 4` | every `N` (checkable); closed form from `N ≥ 17557` |

The weak-constant variant overtakes the Jensen bound from about `N ≈ 73`, and is in turn
overtaken by the exact criterion's closed form from about `N ≈ 250`.

### The upper end

The known sequence with all nonzero `Z` angles equal to `π` has `T = (2N+1)π`; at `N = 1` it is
explicit: `θ = (π,π,π)`, `α = (2π/3, −2π/3, 2π/3)`. It costs (by a factor between `0.84` and
`0.93`) more than the sequences found by local search for `N ≤ 12`, so the asymptotic coefficient
of `T_min(N,π)/N` lies between `4` and `2π`, and whether the lower end is attained is open.

## Where each bound is machine-checked

[`main_inequalities/`](main_inequalities/) states each bound of the list above in a file of its
own, in the namespace `RobustZ.MainIneq`:

| bound | declaration | file |
| --- | --- | --- |
| 2. elementary | `elementary`, `elementary_pi` | `main_inequalities/Elementary.lean` |
| 3. Jensen | `jensen`, `jensen_pi` | `main_inequalities/Jensen.lean` |
| 4. weak-constant variant | `weak_constant` | `main_inequalities/WeakConstant.lean` |
| 5. exact criterion | `exact_criterion`, `closed_form` | `main_inequalities/ExactCriterion.lean` |
| 5. integers at `φ = π` | `cert_N2` … `cert_N12` | `main_inequalities/Certificates.lean` |
| 5. linear growth | `linear_growth`, `linear_growth_or_grows` | `main_inequalities/LinearGrowth.lean` |

Each file imports the tree holding its proof core — [`lean_sharp/wC`](lean_sharp/wC) (elementary,
exact criterion, certificates, linear growth), [`lean_sharp/wF`](lean_sharp/wF) (Jensen),
[`lean_sharp/wM`](lean_sharp/wM) (weak-constant variant) — and ends with `#print axioms` on its
theorems, so one command both re-proves the bound and reports what it rests on.

```sh
cd lean_sharp/wC && lake exe cache get && lake build     # likewise wF, wM, once per tree
main_inequalities/verify.sh                              # checks the six files above
```

The three trees remain the full development (54 + 35 + 47 modules); the direct Taylor bound (1) is
proved on paper in three lines, not in Lean. In the development checkout Mathlib is required by
path (`lean_sharp/*/lakefile.toml`), so a fresh clone should first replace that `require` by
`git = "https://github.com/leanprover-community/mathlib4", rev = "v4.34.1"`.

No `sorry`, `admit` or `axiom` occurs in the sources; every headline declaration depends only on
`[propext, Classical.choice, Quot.sound]`.

## Layout

| path | contents |
| --- | --- |
| `main_inequalities/` | each machine-checked bound of "The bounds", one file each, with `verify.sh` |
| `lean_sharp/{wC,wF,wM}` | the full development (proof cores) — see [`lean_sharp/README.md`](lean_sharp/README.md) |
| `paper/` | LaTeX sources, PDFs and the build script |
| `RobustZ/` | the superseded first version (tag `v1.0.0`); its documentation is in [`README_first_version.md`](README_first_version.md) |
| `VERIFICATION.md` | build and audit records |

The numerical side (local-search upper bounds, the angle lists and the figure scripts) is in the
paper's data set: <https://show.dytchem.cn/files/code.zip>.

License: Apache-2.0.
