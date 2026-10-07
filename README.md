# Robust composite `Z` rotations — a machine-checked `c ≥ 4` lower bound

Lean 4 + Mathlib formalisation of the main theorem of
*The Linear Cost of High-Order Robust Composite `Z` Rotations*
(in-source working title: *Saturation of the Linear Lower Bound for High-Order Robust
Composite `Z` Rotations*, `main.tex`, Theorem 1): the minimal total `Z`-evolution angle of an
order-`N` robust composite `Z` rotation is at least linear in `N`, with slope at least `4`,

```
liminf_{N→∞}  T_min(N, φ) / N  ≥  4        (0 < φ ≤ π).
```

Everything below is checked by the Lean kernel; the only axioms used are `propext`,
`Classical.choice` and `Quot.sound` (see [Audit](#audit)).

## The formalised statement

The statement layer is `RobustZ/Statement.lean`. With `M2 = Matrix (Fin 2) (Fin 2) ℂ`,
`J_z = -I • σ_z`, `J_x = -I • σ_x`,

* `Zrot θ = NormedSpace.exp (θ • (1/2 : ℂ) • J_z)`, `Xrot α = exp (α • (1/2 : ℂ) • J_x)`;
* `U L α θ λ = ∏_{j<L} Xrot (α j) * Zrot (λ * θ j)` — the composite evolution;
* `cost θ = ∑ j, θ j`;
* `Admissible N φ L α θ` — all angles nonnegative, `U L α θ 1 = Zrot φ`, and the first `N`
  derivatives of `λ ↦ U L α θ λ` vanish at `λ = 1` (order-`N` robustness);
* `costs N φ = {T | ∃ L α θ, Admissible N φ L α θ ∧ T = cost θ}` and
  `Tmin N φ = sInf (costs N φ)`.

The main theorem, `RobustZ/Theorem.lean`:

```lean
theorem RobustZ.c_ge_four (φ : ℝ) (hφ0 : 0 < φ) (hφπ : φ ≤ Real.pi)
    (hne : ∀ N, (costs N φ).Nonempty)
    (hbdd : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop (fun N : ℕ => Tmin N φ / N)) :
    4 ≤ Filter.liminf (fun N : ℕ => Tmin N φ / N) Filter.atTop
```

The two extra hypotheses are bookkeeping on the formalisation side, not mathematical content:

* `hne` keeps `sInf` away from its junk value — Mathlib defines `sInf ∅ = 0`, so without it the
  claim would be vacuous-to-false for a target that admits no admissible construction.
* `hbdd` is the boundedness-above side condition that `Filter.le_liminf_of_le` needs. On `ℝ`,
  `Filter.liminf` is `sSup` of the eventual lower bounds, and `sSup` is junk (`0`) on a set that
  is not bounded above — so the boundedness hypothesis is genuinely required, not cosmetic.
  `RobustZ/Liminf.lean` documents this and proves the counterexample
  (`not_liminf_ge_of_eventually`, `a N = N * N`, `c = 1`).

Dropping `hbdd` gives the assumption-free dichotomy `RobustZ.c_ge_four_or_grows`, which concludes
either the same bound or that `Tmin N φ / N` eventually exceeds every real number:

```lean
theorem RobustZ.c_ge_four_or_grows (φ : ℝ) (hφ0 : 0 < φ) (hφπ : φ ≤ Real.pi)
    (hne : ∀ N, (costs N φ).Nonempty) :
    4 ≤ Filter.liminf (fun N : ℕ => Tmin N φ / N) Filter.atTop ∨
      ∀ M : ℝ, ∀ᶠ N in Filter.atTop, M ≤ Tmin N φ / N
```

## Build

The project depends on mathlib4 through a **pinned git dependency** — `git =
"https://github.com/leanprover-community/mathlib4"`, `rev = "v4.34.1"` in `lakefile.toml`,
resolved to `d13f23b723b8a846827a245b89c10fc7d3f11612` in `lake-manifest.json`. It is *not* a
local path dependency, so a fresh clone builds on any machine. `lean-toolchain` pins the compiler
to `leanprover/lean4:v4.34.1`.

```sh
git clone https://github.com/Dytchem/robust-z-lower-bound-lean.git
cd robust-z-lower-bound-lean

# 1. elan, if you do not have it yet
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
export PATH="$HOME/.elan/bin:$PATH"

# 2. mathlib sources + oleans (~5 GB, this takes a while)
lake exe cache get

# 3. build
lake build              # expected: Build completed successfully (3709 jobs)

# 4. axiom audit
lake env lean RobustZ/Audit.lean
```

`RobustZ/Audit.lean` is not part of the `RobustZ` library target, so `lake build` does not compile
it — run it explicitly as in step 4. On a machine with little RAM, use `lake build -j1`.

## Module map

**M2 — structure and statement layer**

| File | Content |
| --- | --- |
| `Statement.lean` | Definitions: Pauli generators, `Xrot`/`Zrot`, the composite `U`, `cost`, `Admissible`, `costs`, `Tmin`, and the error function `h = 1 - ½ tr[U₁† U_λ]`. |
| `Elementary.lean` | Anti-Hermiticity of `J_x`, `J_z`; unitarity of `Xrot`, `Zrot`, `U`, `V = U₁† U_λ`; `h = ¼ tr((V-1)†(V-1))` and hence `0 ≤ h ≤ 2`; `Tmin` is a genuine infimum. |
| `Flatness.lean` | Flatness doubling: `N`-th order flatness at `λ = 1` forces `analyticOrderAt h 1 ≥ 2N+2`, i.e. `h = (·-1)^(2N+2) · g` with `g` analytic (`h_flat`). |
| `ExpSum.lean` | `U_λ` and `h` are finite exponential sums with frequencies `\|ν\| ≤ τ = Σθⱼ/2`; with `h_flat` this yields the moment conditions `Σᵢ cᵢ P(νᵢ) e^{iνᵢ} = 0` fed to M3. |
| `HTrace.lean` | Endpoint value `h(0) = 1 - cos(φ/2)·cos(A/2)` with `A = Σαⱼ` — note the extra `cos(A/2)` factor, which is `1` only when `A ∈ 4πℤ`. |
| `HTraceLower.lean` | Hadamard conjugation `H Z(t) H⁻¹ = X(t)`, `tr(Z(φ)† X(a)) = 2 cos(φ/2) cos(a/2)`, and the `N`-independent bound `h(0) ≥ 1 - cos(φ/2) = 2 sin²(φ/4)`. |

**M3 — smearing**

| File | Content |
| --- | --- |
| `Smearing.lean` | The smooth cutoff `χ(μ) = σ((τ + B - \|μ\|)/B)` with `σ = Real.smoothTransition`, and `Ψ = (1 - P e^{iμ})·χ`, supported in `[-(τ+B), τ+B]`. |
| `CutoffDeriv.lean` | Scaling bounds `\|χ'\| ≤ K/B` and `\|χ''\| ≤ K/B²` with `K` a pure constant (compactness of `[0,1]` plus the chain rule). |
| `KernelBound.lean` | Two integrations by parts give the pointwise decay `‖κ(t)‖ ≤ (2πt²)⁻¹ ∫‖Ψ''‖`; the boundary terms vanish by compact support. |
| `KernelIntegrable.lean` | Continuity of the parameter integral plus domination by `A` on `[-1,1]` and `C·t⁻²` on the tails ⇒ the kernel is Bochner integrable. |
| `L1Bound.lean` | The elementary tail integrals `∫_R^∞ t⁻² = 1/R` used to split `∫‖κ‖`. |
| `Inversion.lean` | Reconciles Mathlib's Fourier normalisation (`𝓕 f w = ∫ v, 𝐞(-⟪v,w⟫) • f v`, no `(2π)⁻¹`) with the kernel, giving the inversion identity `∫ t, e^{iλt} κ(t) dt = Ψ(λ)`. |
| `SmearingMain.lean` | Main assembly `‖Σᵢ cᵢ‖ ≤ 8√(C₁C₂)`, plus the τ-scaled variant `norm_sum_le_of_moments_tau_scaled` with taper width `B = ετ/q²`. |

**M4 — band approximation and collar bounds**

| File | Content |
| --- | --- |
| `Approx.lean` | Fourier coefficients of `F(θ) = e^{-iτ cos θ}` and the contour-shift bound `\|cₙ\| ≤ exp(τ sinh δ - nδ)`. |
| `Band.lean` | Transports the `θ`-form approximation error to the band `\|μ\| ≤ τ`, with an explicit geometric decay constant (named `epsOf` where it is used, in `M5Apply.lean`). |
| `PsiBounds.lean` | Explicit bounds for `Ψ_A`, `Ψ` and their derivatives on the band, and continuity/differentiability of the cutoff. |
| `ChebDeriv.lean` | Chebyshev-derivative estimates: coefficient-wise bounds for `T_n'` and `T_n''` on `[-1,1]`, and derivative bounds for `approxPoly`. |
| `CollarBound.lean` | The collar `\|u\| ≤ 1+δ`: growth bounds for `T_n`, `T_n'` and for `approxPoly` outside the band. |

**M5 — assembly**

| File | Content |
| --- | --- |
| `M5Prelim.lean` | Self-contained API lemmas for the final assembly (`h_one`, `le_Tmin_of_forall`, …), using only the frozen M2 layer. |
| `M5Bridge.lean` | Bridges M4 to M3: composes `approxPoly τ k` with the linear substitution `u ↦ u/τ` to get `scaledApprox`. |
| `M5Apply.lean` | Applies M3 + M4 to `h(0)`, giving the pointwise bound `h(0) ≤ 8√(C₁C₂)` for admissible constructions. |
| `M5Scaled.lean` | The τ-uniform version at the paper's scale `B = ετ/q²`: the M3′ application, the second-derivative Chebyshev collar bound, the collar bounds `M₁`, `M₂`, and the sharpened `C₁C₂ ≤ 3000(1+K)(1+4/(1-e^{-δ'}))e^{δ'} q⁸ e^{-ηq}`. |
| `CollarTail.lean` | Cancellation-aware tail estimates on the collar: bounds for the error and its first two derivatives, exporting `Approx.norm_tail_le`'s collar analogue. |
| `KernelDecay.lean` | Localises the `FinalSmall` gap, proves the provable parts (Jacobi–Anger tails, `hasSum_fcoef_cosh`), and records the quantitative diagnosis. |
| `FinalConv.lean` | Squeezes `8√(C₁C₂)` below the endpoint constant, with support-aware bounds on `C₂`. |
| `FinalSmall.lean` | Endpoint smallness for `τ ≤ ρ(2N+2)`: if an admissible construction had `τ` below the threshold then `h(0) < 1 - cos(φ/2)`, contradicting the `N`-independent lower bound. |
| `Final.lean` | The `c ≥ 4` assembly: contradiction argument, then `liminf_ge_of_eventual` and `δ → 0`. |
| `Liminf.lean` | `liminf` versus eventual lower bounds, including an honest warning and a formal counterexample showing the boundedness side condition is necessary. |
| `Theorem.lean` | `c_ge_four` and the assumption-free dichotomy `c_ge_four_or_grows`. |

**Audit**

| File | Content |
| --- | --- |
| `Audit.lean` | `#print axioms` for the main theorem and the five load-bearing intermediate results. |

## Route

1. **Smooth taper instead of Hermite patching.** Truncation is done with
   `χ(μ) = σ((τ + B - \|μ\|)/B)`, `σ = Real.smoothTransition`, so `Ψ = (1 - P e^{iμ})χ` is
   compactly supported and `C²`; `CutoffDeriv.lean` gives the scaling `‖χ'‖ ≤ K/B`,
   `‖χ''‖ ≤ K/B²` with `K` a pure constant.
2. **Support-aware `∫‖Ψ''‖`.** `M5Scaled.lean` and `FinalConv.lean` bound
   `∫‖Ψ''‖ ≤ 2(τ+B)·M₂ + …` using the *true* support `[-(τ+B), τ+B]` rather than
   `[-(τ+B+1), τ+B+1]`. Dropping the gratuitous `1` is what prevents a `1/τ` blow-up as `τ → 0`.
3. **Taper width proportional to `τ`: `B = ετ/q²`, `q = 2N+2`.** Then `B/τ = ε/q²` is τ-free, so
   the collar's *relative* width stays bounded as `τ → 0`. The earlier `B = √ε` is τ-independent
   and makes the Chebyshev collar bounds grow exponentially; `M5Scaled.lean` supplies the
   τ-uniform replacement `norm_sum_le_of_moments_tau_scaled`.
4. **Collar derivative bounds from Chebyshev coefficient decay, not Markov.** `ChebDeriv.lean`
   and `CollarBound.lean` bound `T_n`, `T_n'`, `T_n''` on `|u| ≤ 1+δ` by explicit exponential
   decay in `n`; `M5Scaled.abs_deriv2_chebyshevT_le_exp` adds the missing second-derivative collar
   bound from Chebyshev's ODE `(1-X²)T_n'' = X T_n' - n²T_n`. A Markov-type inequality would lose
   exactly the factor that controls the collar.
5. **Truncation constants independent of `τ`.** §5 of `M5Scaled.lean` runs the arithmetic
   `B·M₁ ≤ 9εq`, `τ²M₂ ≤ 141q⁵`, `ε/B = q²/τ` to a fully explicit
   `C₁C₂ ≤ 3000(1+K)·(1+4/(1-e^{-δ'}))·e^{δ'}·q⁸·e^{-ηq}`, `η = δ' - ρ sinh δ' > 0`.

## Scope

This repository formalises **only** the `c ≥ 4` lower bound (Theorem 1, first inequality). Be
aware of the following.

* The paper's other two intermediate bounds (`c* ≥ 2/e` and `c* ≥ 4/e`), the reflection-symmetry
  argument and the Bernstein-ellipse analysis are **not** formalised here.
* `hne` and `hbdd` in `c_ge_four` are formalisation-side bookkeeping hypotheses, as explained
  above; `c_ge_four_or_grows` is the version without `hbdd`.
* The naive endpoint identity `h(0) = 1 - cos(φ/2)` is **false** in general; the true value is
  `1 - cos(φ/2)·cos(A/2)`. The proof uses the one-sided bound `h(0) ≥ 1 - cos(φ/2)`, which is valid
  for `0 ≤ φ ≤ π`. `HTrace.lean` and `HTraceLower.lean` keep both statements separate.
* The numerical tables in the paper are heuristic upper bounds computed from the analysis; they
  are not formalised and should not be read as proved.

## Audit

Two independent checks. First, no `sorry`, `admit` or `axiom` anywhere in the sources:

```sh
grep -rnE "\b(sorry|admit|axiom)\b" --include="*.lean" RobustZ RobustZ.lean
```

The only hits are prose inside `/-! … -/` doc comments (`RobustZ/FinalSmall.lean`), never a proof
term. A stronger check is the build log itself: Lean emits
`declaration uses 'sorry'` for any declaration closed by `sorry`, and a `sorry`-tainted proof would
also surface as `sorryAx` below.

Second, the transitive axiom set of the main theorem:

```sh
lake env lean RobustZ/Audit.lean
```

Expected output — every line exactly the three standard axioms, no `sorryAx`:

```
'RobustZ.c_ge_four' depends on axioms: [propext, Classical.choice, Quot.sound]
'RobustZ.c_ge_four_or_grows' depends on axioms: [propext, Classical.choice, Quot.sound]
'RobustZ.h_zero_small_of_tau_le_scaled' depends on axioms: [propext, Classical.choice, Quot.sound]
'RobustZ.kernel_decay_tau_scaled' depends on axioms: [propext, Classical.choice, Quot.sound]
'RobustZ.norm_sum_le_of_moments' depends on axioms: [propext, Classical.choice, Quot.sound]
'RobustZ.h_zero_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Layout

30 modules under `RobustZ/` (10467 lines) plus the root aggregator `RobustZ.lean` (29 lines),
10496 lines in total. Toolchain `leanprover/lean4:v4.34.1`; mathlib4 pinned at tag `v4.34.1`
(`d13f23b723b8a846827a245b89c10fc7d3f11612`) via `lake-manifest.json`.

## License

[Apache License 2.0](LICENSE) — Copyright 2026 Dytchem.
