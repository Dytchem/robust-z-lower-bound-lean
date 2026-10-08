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

Three independent Lean 4 + Mathlib trees under [`lean_sharp/`](lean_sharp/), each with its own
pinned toolchain and manifest.

| bound | declaration | file |
| --- | --- | --- |
| elementary | `elementary_bound`, `elementary_bound_pi` | `lean_sharp/wC/RobustZ/ElementaryBound.lean` |
| Jensen | `jensen_rung_final`, `jensen_rung_pi_final`, `jensen_ratio_tendsto` | `lean_sharp/wF/RobustZ/JensenBridge.lean`, `lean_sharp/wF/RobustZ/JensenRung.lean` |
| exact criterion | `new_rung_final`, `nr_closed_form` | `lean_sharp/wC/RobustZ/RungFinal.lean`, `lean_sharp/wC/RobustZ/NewRung.lean` |
| integers at `φ = π` | `cert_N2`–`cert_N4`, `cert_N5_tight`–`cert_N12_tight` | `lean_sharp/wC/RobustZ/RungFinal.lean`, `lean_sharp/wC/RobustZ/RungTight.lean` |
| weak-constant variant | `eight_over_e_bound` | `lean_sharp/wM/RobustZ/EightOverE.lean` |
| linear growth, with side conditions | `c_ge_four`, `c_ge_four_or_grows` | `lean_sharp/wC/RobustZ/Theorem.lean` |

The direct Taylor bound (1) is proved on paper in three lines, not in Lean.

```sh
cd lean_sharp/wC && lake exe cache get && lake build     # likewise wF, wM
```

No `sorry`, `admit` or `axiom` occurs in the sources; the `RobustZ/Audit*.lean` files print the
axioms of the headline declarations (`[propext, Classical.choice, Quot.sound]`).

## Layout

| path | contents |
| --- | --- |
| `lean_sharp/{wC,wF,wM}` | the current development — see [`lean_sharp/README.md`](lean_sharp/README.md) |
| `paper/` | LaTeX sources, PDFs and the build script |
| `RobustZ/` | the superseded first version (tag `v1.0.0`); its documentation is in [`README_first_version.md`](README_first_version.md) |
| `VERIFICATION.md` | build and audit records |

The numerical side (local-search upper bounds, the angle lists and the figure scripts) is in the
paper's data set: <https://show.dytchem.cn/files/code.zip>.

License: Apache-2.0.
