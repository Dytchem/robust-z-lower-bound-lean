import RobustZ.NewRung
import RobustZ.RungFinal
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Tightened rung: improved Chebyshev second-derivative constant + re-certified numbers.

This module recovers the constant lost to two crude steps in `NewRung`/`RungFinal`:

* (T1) The Chebyshev second-derivative bound is improved from the tree's
  `|T_n''| ≤ 16·N^4` (`abs_deriv2_chebyshevT_le`) to `|T_n''| ≤ (13/10)·N^4`
  on `[-1,1]` (`abs_deriv2_chebyshevT_le_tight`).  The proof reuses the
  tree's `T_n''(cos θ)·sin^3θ = ψ_n(θ)` identity shape (re-proved here since
  the originals are `private`) and replaces the two lossy steps
  (`|n^3-n| ≤ N^3+N`, crude MVT giving `2N^4θ^3`, and `π^3 ≤ 64`) by
  `|n^3-n| ≤ N^3`, an antitone/`AntitoneOn` comparison giving
  `|ψ_n(θ)| ≤ N^4θ^3/3`, and `π^3 ≤ 31.01` (from `Real.pi_lt_d4`).
  The fully sharp `N^2(N^2-1)/3` would need cancellation in `∫sin(ns)sin s`
  (see the module doc below); `13/10` captures most of the `48×` gap at a
  fraction of the cost, and suffices for every target here.
* (T2) The `D2`-term of `nrCcal` drops from `32·η2·q^2` to
  `(13/5)·η2·q^2` (`nrCcal_tight`, with `nrCcal_tight_le`), and the L5
  assembly is re-run generically (`nr_main_rung_of_kappa`,
  `new_rung_final_tight`).
* (T3) The numeric certs use tighter enclosures: composite-logarithm
  `arcosh` lower bounds (e.g. `log(27/8) = 3log3-3log2`, needing the `lt_d9`
  upper bounds), `2/π ≤ 0.6367` (via `Real.pi_gt_d4`), and
  `2√(π/8) ≤ 1.26` (via `Real.pi_lt_d4`).

All cert names are `cert_N*_tight` so nothing here clashes with `RungFinal`.
-/

noncomputable section

namespace RobustZ

open scoped Real
open Finset MeasureTheory
open scoped Matrix Matrix.Norms.L2Operator

/-! ## §0. Tight Chebyshev second-derivative bound.

Copies of the `private` helpers from `ChebDeriv` (renamed with `_t`),
then the tight argument. -/

/-- `|n| = (n.natAbs : ℝ)` for integers (copy of a private lemma in `ChebDeriv`). -/
private lemma abs_int_cast_eq_t (n : ℤ) : |((n : ℤ) : ℝ)| = (n.natAbs : ℝ) := by
  obtain ⟨k, hk | hk⟩ := Int.eq_nat_or_neg n
  · rw [hk]; simp
  · rw [hk]; simp

/-- `θ ↦ T_n' (cos θ)` has derivative `T_n'' (cos θ) * (-sin θ)`
(copy of a private lemma in `ChebDeriv`). -/
private lemma hasDerivAt_chebT_deriv_cos_t (n : ℤ) (θ : ℝ) :
    HasDerivAt (fun x : ℝ => (Polynomial.Chebyshev.T ℝ n).derivative.eval (Real.cos x))
      ((Polynomial.Chebyshev.T ℝ n).derivative.derivative.eval (Real.cos θ) * (-Real.sin θ))
      θ :=
  (Polynomial.hasDerivAt (Polynomial.Chebyshev.T ℝ n).derivative (Real.cos θ)).comp θ
    (Real.hasDerivAt_cos θ)

/-- The key identity `T_n'' (cos θ) * sin θ ^ 3 = ψ_n θ`
(copy of a private lemma in `ChebDeriv`). -/
private lemma chebyshevT_deriv2_cos_mul_sin_t (n : ℤ) (θ : ℝ) :
    (Polynomial.Chebyshev.T ℝ n).derivative.derivative.eval (Real.cos θ) * Real.sin θ ^ 3
      = (n : ℝ) * Real.sin ((n : ℝ) * θ) * Real.cos θ
        - (n : ℝ) ^ 2 * Real.cos ((n : ℝ) * θ) * Real.sin θ := by
  have hD : HasDerivAt
      (fun x : ℝ => (Polynomial.Chebyshev.T ℝ n).derivative.eval (Real.cos x) * Real.sin x)
      (((Polynomial.Chebyshev.T ℝ n).derivative.derivative.eval (Real.cos θ) * (-Real.sin θ))
        * Real.sin θ
        + (Polynomial.Chebyshev.T ℝ n).derivative.eval (Real.cos θ) * Real.cos θ) θ :=
    (hasDerivAt_chebT_deriv_cos_t n θ).mul (Real.hasDerivAt_sin θ)
  have hE : HasDerivAt (fun x : ℝ => (n : ℝ) * Real.sin ((n : ℝ) * x))
      ((n : ℝ) * (Real.cos ((n : ℝ) * θ) * (n : ℝ))) θ := by
    have h := ((Real.hasDerivAt_sin ((n : ℝ) * θ)).comp θ
      ((hasDerivAt_id θ).const_mul (n : ℝ))).const_mul (n : ℝ)
    simpa [Function.comp, mul_one] using h
  have hfun : (fun x : ℝ =>
        (Polynomial.Chebyshev.T ℝ n).derivative.eval (Real.cos x) * Real.sin x)
      = fun x : ℝ => (n : ℝ) * Real.sin ((n : ℝ) * x) := by
    funext x
    have hid : (Polynomial.Chebyshev.T ℝ n).derivative.eval (Real.cos x) * Real.sin x
      = (n : ℝ) * Real.sin ((n : ℝ) * x) := by
        have hchain : HasDerivAt
            (fun x : ℝ => (Polynomial.Chebyshev.T ℝ n).eval (Real.cos x))
            ((Polynomial.Chebyshev.T ℝ n).derivative.eval (Real.cos x) * (-Real.sin x)) x :=
          (Polynomial.hasDerivAt (Polynomial.Chebyshev.T ℝ n) (Real.cos x)).comp x
            (Real.hasDerivAt_cos x)
        have hcos : HasDerivAt (fun x : ℝ => Real.cos ((n : ℝ) * x))
            (-((n : ℝ) * Real.sin ((n : ℝ) * x))) x := by
          have h := (Real.hasDerivAt_cos ((n : ℝ) * x)).comp x
            ((hasDerivAt_id x).const_mul (n : ℝ))
          convert h using 1
          · ext y; simp [Function.comp]
          · ring
        have hfun2 : (fun x : ℝ => (Polynomial.Chebyshev.T ℝ n).eval (Real.cos x))
            = fun x : ℝ => Real.cos ((n : ℝ) * x) :=
          funext fun x => Polynomial.Chebyshev.T_real_cos x n
        rw [hfun2] at hchain
        have h := hchain.unique hcos
        have key : (Polynomial.Chebyshev.T ℝ n).derivative.eval (Real.cos x) * Real.sin x
            = -((Polynomial.Chebyshev.T ℝ n).derivative.eval (Real.cos x) * (-Real.sin x)) := by
          ring
        rw [key, h]; ring
    exact hid
  rw [← hfun] at hE
  have huniq := hD.unique hE
  have hid : (Polynomial.Chebyshev.T ℝ n).derivative.eval (Real.cos θ) * Real.sin θ
      = (n : ℝ) * Real.sin ((n : ℝ) * θ) := by
    have hchain : HasDerivAt (fun x : ℝ => (Polynomial.Chebyshev.T ℝ n).eval (Real.cos x))
        ((Polynomial.Chebyshev.T ℝ n).derivative.eval (Real.cos θ) * (-Real.sin θ)) θ :=
      (Polynomial.hasDerivAt (Polynomial.Chebyshev.T ℝ n) (Real.cos θ)).comp θ
        (Real.hasDerivAt_cos θ)
    have hcos : HasDerivAt (fun x : ℝ => Real.cos ((n : ℝ) * x))
        (-((n : ℝ) * Real.sin ((n : ℝ) * θ))) θ := by
      have h := (Real.hasDerivAt_cos ((n : ℝ) * θ)).comp θ
        ((hasDerivAt_id θ).const_mul (n : ℝ))
      convert h using 1
      · ext y; simp [Function.comp]
      · ring
    have hfun2 : (fun x : ℝ => (Polynomial.Chebyshev.T ℝ n).eval (Real.cos x))
        = fun x : ℝ => Real.cos ((n : ℝ) * x) :=
      funext fun x => Polynomial.Chebyshev.T_real_cos x n
    rw [hfun2] at hchain
    have h := hchain.unique hcos
    have key : (Polynomial.Chebyshev.T ℝ n).derivative.eval (Real.cos θ) * Real.sin θ
        = -((Polynomial.Chebyshev.T ℝ n).derivative.eval (Real.cos θ) * (-Real.sin θ)) := by
      ring
    rw [key, h]; ring
  linear_combination -Real.sin θ * huniq + Real.cos θ * hid

/-- Derivative of `ψ_n` (copy of a private lemma in `ChebDeriv`). -/
private lemma hasDerivAt_psi_t (n : ℤ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (n : ℝ) * Real.sin ((n : ℝ) * s) * Real.cos s
        - (n : ℝ) ^ 2 * Real.cos ((n : ℝ) * s) * Real.sin s)
      (((n : ℝ) ^ 3 - (n : ℝ)) * Real.sin ((n : ℝ) * t) * Real.sin t) t := by
  have hsin : HasDerivAt (fun s : ℝ => Real.sin ((n : ℝ) * s))
      ((n : ℝ) * Real.cos ((n : ℝ) * t)) t := by
    have h := (Real.hasDerivAt_sin ((n : ℝ) * t)).comp t
      ((hasDerivAt_id t).const_mul (n : ℝ))
    convert h using 1
    · ext x; simp [Function.comp]
    · ring
  have hcosn : HasDerivAt (fun s : ℝ => Real.cos ((n : ℝ) * s))
      (-((n : ℝ) * Real.sin ((n : ℝ) * t))) t := by
    have h := (Real.hasDerivAt_cos ((n : ℝ) * t)).comp t
      ((hasDerivAt_id t).const_mul (n : ℝ))
    convert h using 1
    · ext x; simp [Function.comp]
    · ring
  have hA := (hsin.const_mul (n : ℝ)).mul (Real.hasDerivAt_cos t)
  have hB := (hcosn.const_mul ((n : ℝ) ^ 2)).mul (Real.hasDerivAt_sin t)
  convert hA.sub hB using 1
  ring

/-- Pointwise bound on `ψ_n'`: `|(n^3-n)·sin(nt)·sin t| ≤ N^4·t^2`. -/
lemma psi_pointwise_tight (n : ℤ) (t : ℝ) :
    |(((n : ℝ) ^ 3 - (n : ℝ))) * Real.sin (((n : ℝ)) * t) * Real.sin t|
      ≤ ((n.natAbs : ℝ)) ^ 4 * t ^ 2 := by
  set N : ℝ := (n.natAbs : ℝ) with hN
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hNabs : |(n : ℝ)| = N := abs_int_cast_eq_t n
  have hnsq : ((n : ℝ)) ^ 2 = N ^ 2 := by
    have h := sq_abs ((n : ℝ))
    rw [hNabs] at h
    exact h.symm
  have hcube : |(((n : ℝ)) ^ 3 - (n : ℝ))| ≤ N ^ 3 := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp [hN]
    · have h2 : 0 < n.natAbs := Int.natAbs_pos.mpr hn
      have hN1 : (1 : ℝ) ≤ N := by
        rw [hN]
        have h1 : 1 ≤ n.natAbs := h2
        exact_mod_cast h1
      have hNs : (1 : ℝ) ≤ N ^ 2 := by nlinarith [hN1, sq_nonneg (N - 1)]
      have e : ((n : ℝ)) ^ 3 - (n : ℝ) = (n : ℝ) * (((n : ℝ)) ^ 2 - 1) := by ring
      have e2 : |(n : ℝ) * (((n : ℝ)) ^ 2 - 1)| = N * |N ^ 2 - 1| := by
        rw [abs_mul, hNabs, hnsq]
      have hb : |N ^ 2 - 1| ≤ N ^ 2 := by
        rw [abs_le]
        constructor <;> linarith [hNs]
      calc |((n : ℝ)) ^ 3 - (n : ℝ)| = N * |N ^ 2 - 1| := by rw [e, e2]
        _ ≤ N * N ^ 2 := mul_le_mul_of_nonneg_left hb hN0
        _ = N ^ 3 := by ring
  have hs1 : |Real.sin (((n : ℝ)) * t)| ≤ N * |t| := by
    calc |Real.sin (((n : ℝ)) * t)| ≤ |((n : ℝ)) * t| := Real.abs_sin_le_abs
      _ = N * |t| := by rw [abs_mul, hNabs]
  have hs2 : |Real.sin t| ≤ |t| := Real.abs_sin_le_abs
  have hnn : (0 : ℝ) ≤ |(((n : ℝ)) ^ 3 - (n : ℝ))| := abs_nonneg _
  calc |(((n : ℝ)) ^ 3 - (n : ℝ)) * Real.sin (((n : ℝ)) * t) * Real.sin t|
      = |(((n : ℝ)) ^ 3 - (n : ℝ))| * (|Real.sin (((n : ℝ)) * t)| * |Real.sin t|) := by
        rw [abs_mul, abs_mul, mul_assoc]
    _ ≤ N ^ 3 * ((N * |t|) * |t|) :=
        mul_le_mul hcube (mul_le_mul hs1 hs2 (abs_nonneg _) (mul_nonneg hN0 (abs_nonneg _)))
          (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (pow_nonneg hN0 3)
    _ = N ^ 4 * (|t| ^ 2) := by ring
    _ = N ^ 4 * t ^ 2 := by rw [sq_abs t]

/-- `d/dt [t^3] = 3t^2` in the exact form produced by `hasDerivAt_pow`. -/
private lemma hpow3_t (t : ℝ) :
    HasDerivAt (fun s : ℝ => s ^ 3) (3 * t ^ 2) t := by
  have h := hasDerivAt_pow 3 t
  rwa [show ((3 : ℕ) : ℝ) * t ^ ((3 : ℕ) - 1) = 3 * t ^ 2 from by norm_num] at h

/-- One-sided integral-free bound: `sgn·ψ_n(θ) ≤ N^4θ^3/3` for `θ ≥ 0`,
via `AntitoneOn` comparison of `sgn·ψ - (N^4/3)t^3`. -/
lemma psi_upper_tight (n : ℤ) {θ : ℝ} (hθ0 : 0 ≤ θ) (sgn : ℝ)
    (hsgn : sgn = 1 ∨ sgn = -1) :
    sgn * (((n : ℝ)) * Real.sin (((n : ℝ)) * θ) * Real.cos θ
      - ((n : ℝ)) ^ 2 * Real.cos (((n : ℝ)) * θ) * Real.sin θ)
      ≤ ((n.natAbs : ℝ)) ^ 4 * θ ^ 3 / 3 := by
  set N : ℝ := (n.natAbs : ℝ) with hN
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hderiv : ∀ t : ℝ, HasDerivAt
      (fun s : ℝ => sgn * (((n : ℝ)) * Real.sin (((n : ℝ)) * s) * Real.cos s
        - ((n : ℝ)) ^ 2 * Real.cos (((n : ℝ)) * s) * Real.sin s) - (N ^ 4 / 3) * s ^ 3)
      (sgn * ((((n : ℝ)) ^ 3 - (n : ℝ)) * Real.sin (((n : ℝ)) * t) * Real.sin t)
        - (N ^ 4 / 3) * (3 * t ^ 2)) t := by
    intro t
    exact ((hasDerivAt_psi_t n t).const_mul sgn).sub ((hpow3_t t).const_mul (N ^ 4 / 3))
  have hcont : ContinuousOn
      (fun s : ℝ => sgn * (((n : ℝ)) * Real.sin (((n : ℝ)) * s) * Real.cos s
        - ((n : ℝ)) ^ 2 * Real.cos (((n : ℝ)) * s) * Real.sin s) - (N ^ 4 / 3) * s ^ 3)
      (Set.Icc 0 θ) := by
    apply Continuous.continuousOn
    fun_prop
  have hdiff : DifferentiableOn ℝ
      (fun s : ℝ => sgn * (((n : ℝ)) * Real.sin (((n : ℝ)) * s) * Real.cos s
        - ((n : ℝ)) ^ 2 * Real.cos (((n : ℝ)) * s) * Real.sin s) - (N ^ 4 / 3) * s ^ 3)
      (interior (Set.Icc 0 θ)) := by
    intro x hx
    rw [interior_Icc] at hx
    exact (hderiv x).differentiableAt.differentiableWithinAt
  have hanti : AntitoneOn
      (fun s : ℝ => sgn * (((n : ℝ)) * Real.sin (((n : ℝ)) * s) * Real.cos s
        - ((n : ℝ)) ^ 2 * Real.cos (((n : ℝ)) * s) * Real.sin s) - (N ^ 4 / 3) * s ^ 3)
      (Set.Icc 0 θ) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 θ) hcont hdiff
    intro x hx
    rw [interior_Icc] at hx
    have hde := (hderiv x).deriv
    rw [hde]
    have hpt := psi_pointwise_tight n x
    have hsgn1 : |sgn| = 1 := by rcases hsgn with rfl | rfl <;> norm_num
    have hsgn_le : sgn * ((((n : ℝ)) ^ 3 - (n : ℝ)) * Real.sin (((n : ℝ)) * x) * Real.sin x)
        ≤ |(((n : ℝ)) ^ 3 - (n : ℝ)) * Real.sin (((n : ℝ)) * x) * Real.sin x| := by
      have h1 := le_abs_self
        (sgn * ((((n : ℝ)) ^ 3 - (n : ℝ)) * Real.sin (((n : ℝ)) * x) * Real.sin x))
      rwa [abs_mul, hsgn1, one_mul] at h1
    have heq : (N ^ 4 / 3) * (3 * x ^ 2) = N ^ 4 * x ^ 2 := by ring
    linarith [hsgn_le, hpt, heq]
  have h01 : (0 : ℝ) ∈ Set.Icc 0 θ := Set.mem_Icc.mpr ⟨le_rfl, hθ0⟩
  have hθ1 : θ ∈ Set.Icc 0 θ := Set.mem_Icc.mpr ⟨hθ0, le_rfl⟩
  have hle := hanti h01 hθ1 hθ0
  have hpsi0 : ((n : ℝ)) * Real.sin (((n : ℝ)) * (0 : ℝ)) * Real.cos (0 : ℝ)
      - ((n : ℝ)) ^ 2 * Real.cos (((n : ℝ)) * (0 : ℝ)) * Real.sin (0 : ℝ) = 0 := by
    simp
  have hle2 : sgn * (((n : ℝ)) * Real.sin (((n : ℝ)) * θ) * Real.cos θ
      - ((n : ℝ)) ^ 2 * Real.cos (((n : ℝ)) * θ) * Real.sin θ)
      - (N ^ 4 / 3) * θ ^ 3 ≤ 0 := by
    have h := hle
    simp only [hpsi0] at h
    simpa using h
  calc sgn * (((n : ℝ)) * Real.sin (((n : ℝ)) * θ) * Real.cos θ
        - ((n : ℝ)) ^ 2 * Real.cos (((n : ℝ)) * θ) * Real.sin θ)
        = (sgn * (((n : ℝ)) * Real.sin (((n : ℝ)) * θ) * Real.cos θ
          - ((n : ℝ)) ^ 2 * Real.cos (((n : ℝ)) * θ) * Real.sin θ)
          - (N ^ 4 / 3) * θ ^ 3) + (N ^ 4 / 3) * θ ^ 3 := by ring
    _ ≤ 0 + (N ^ 4 / 3) * θ ^ 3 := by linarith [hle2]
    _ = N ^ 4 * θ ^ 3 / 3 := by ring

/-- MVT-free bound for `ψ_n` on `[0, θ]`. -/
lemma abs_psi_tight_le (n : ℤ) {θ : ℝ} (hθ0 : 0 ≤ θ) :
    |(n : ℝ) * Real.sin ((n : ℝ) * θ) * Real.cos θ
        - (n : ℝ) ^ 2 * Real.cos ((n : ℝ) * θ) * Real.sin θ|
      ≤ ((n.natAbs : ℝ)) ^ 4 * θ ^ 3 / 3 := by
  rw [abs_le]
  constructor
  · have h := psi_upper_tight n hθ0 (-1) (Or.inr rfl)
    linear_combination h
  · have h := psi_upper_tight n hθ0 1 (Or.inl rfl)
    linear_combination h

/-- Bound for `T_n''` at `cos θ`, `θ ∈ (0, π/2]`: `≤ (13/10)·N^4`. -/
lemma abs_deriv2_chebyshevT_cos_le_tight (n : ℤ) {θ : ℝ} (hθ0 : 0 < θ)
    (hθπ : θ ≤ Real.pi / 2) :
    |(Polynomial.Chebyshev.T ℝ n).derivative.derivative.eval (Real.cos θ)|
      ≤ 13 / 10 * ((n.natAbs : ℝ)) ^ 4 := by
  set N : ℝ := (n.natAbs : ℝ) with hN
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hθ0' : 0 ≤ θ := le_of_lt hθ0
  have hsinpos : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos, hθπ])
  have hid : |(Polynomial.Chebyshev.T ℝ n).derivative.derivative.eval (Real.cos θ)|
        * Real.sin θ ^ 3
      = |(n : ℝ) * Real.sin ((n : ℝ) * θ) * Real.cos θ
        - (n : ℝ) ^ 2 * Real.cos ((n : ℝ) * θ) * Real.sin θ| := by
    rw [← abs_of_pos (pow_pos hsinpos 3), ← abs_mul, chebyshevT_deriv2_cos_mul_sin_t n θ]
  have hψ := abs_psi_tight_le n hθ0'
  have hjordan : 2 / Real.pi * θ ≤ Real.sin θ := Real.mul_le_sin hθ0' hθπ
  have hrat : θ / Real.sin θ ≤ Real.pi / 2 := by
    have h2 : 2 * θ ≤ Real.pi * Real.sin θ := by
      have h := mul_le_mul_of_nonneg_right hjordan (le_of_lt Real.pi_pos)
      have e : (2 / Real.pi * θ) * Real.pi = 2 * θ := by
        calc (2 / Real.pi * θ) * Real.pi = (2 * θ / Real.pi) * Real.pi := by ring
          _ = 2 * θ := div_mul_cancel₀ _ (ne_of_gt Real.pi_pos)
      rwa [e, mul_comm (Real.sin θ) Real.pi] at h
    rw [div_le_iff₀ hsinpos]
    linarith [h2]
  have hcube : (θ / Real.sin θ) ^ 3 ≤ (Real.pi / 2) ^ 3 :=
    pow_le_pow_left₀ (div_nonneg hθ0' (le_of_lt hsinpos)) hrat 3
  have hπ3 : Real.pi ^ 3 ≤ (31.01 : ℝ) := by
    have h1 : Real.pi ^ 3 ≤ (3.1416 : ℝ) ^ 3 :=
      pow_le_pow_left₀ (le_of_lt Real.pi_pos) (le_of_lt Real.pi_lt_d4) 3
    norm_num at h1
    linarith [h1]
  have hsne : Real.sin θ ^ 3 ≠ 0 := pow_ne_zero 3 (ne_of_gt hsinpos)
  have h1 : |(Polynomial.Chebyshev.T ℝ n).derivative.derivative.eval (Real.cos θ)|
      = (|(n : ℝ) * Real.sin ((n : ℝ) * θ) * Real.cos θ
        - (n : ℝ) ^ 2 * Real.cos ((n : ℝ) * θ) * Real.sin θ|) / Real.sin θ ^ 3 :=
    eq_div_of_mul_eq hsne hid
  have heq : (N ^ 4 * θ ^ 3 / 3) / Real.sin θ ^ 3
      = N ^ 4 / 3 * (θ / Real.sin θ) ^ 3 := by
    field_simp
  calc |(Polynomial.Chebyshev.T ℝ n).derivative.derivative.eval (Real.cos θ)|
      = (|(n : ℝ) * Real.sin ((n : ℝ) * θ) * Real.cos θ
        - (n : ℝ) ^ 2 * Real.cos ((n : ℝ) * θ) * Real.sin θ|) / Real.sin θ ^ 3 := h1
    _ ≤ (N ^ 4 * θ ^ 3 / 3) / Real.sin θ ^ 3 :=
        (div_le_div_iff_of_pos_right (pow_pos hsinpos 3)).mpr hψ
    _ = N ^ 4 / 3 * (θ / Real.sin θ) ^ 3 := heq
    _ ≤ N ^ 4 / 3 * (Real.pi / 2) ^ 3 :=
        mul_le_mul_of_nonneg_left hcube (by positivity)
    _ = N ^ 4 * (Real.pi ^ 3 / 24) := by ring
    _ ≤ N ^ 4 * (31.01 / 24) :=
        mul_le_mul_of_nonneg_left (by linarith [hπ3]) (pow_nonneg hN0 4)
    _ ≤ 13 / 10 * N ^ 4 := by
        have hcc : (31.01 / 24 : ℝ) ≤ 13 / 10 := by norm_num
        calc N ^ 4 * (31.01 / 24) ≤ N ^ 4 * (13 / 10) :=
              mul_le_mul_of_nonneg_left hcc (pow_nonneg hN0 4)
          _ = 13 / 10 * N ^ 4 := by ring

/-- If `p (-x) = c * p x` pointwise then `p' (-x) = -(c * p' x)`
(copy of a private lemma in `ChebDeriv`). -/
private lemma deriv_eval_neg_of_eval_neg_t {p : Polynomial ℝ} {c : ℝ}
    (h : ∀ y : ℝ, p.eval (-y) = c * p.eval y) (x : ℝ) :
    p.derivative.eval (-x) = -(c * p.derivative.eval x) := by
  have hcomp : p.comp (-Polynomial.X) = Polynomial.C c * p := by
    apply Polynomial.funext
    intro y
    rw [Polynomial.eval_comp, Polynomial.eval_neg, Polynomial.eval_X, Polynomial.eval_mul,
      Polynomial.eval_C]
    exact h y
  have hder := congrArg Polynomial.derivative hcomp
  rw [Polynomial.derivative_comp, Polynomial.derivative_C_mul] at hder
  have hdX : Polynomial.derivative (-Polynomial.X : Polynomial ℝ) = -1 := by
    rw [show (-Polynomial.X : Polynomial ℝ) = Polynomial.C (-1) * Polynomial.X by simp,
      Polynomial.derivative_C_mul, Polynomial.derivative_X]
    simp
  rw [hdX] at hder
  have hval := congrArg (fun q : Polynomial ℝ => q.eval x) hder
  simp only [Polynomial.eval_mul, Polynomial.eval_neg, Polynomial.eval_one, Polynomial.eval_C,
    Polynomial.eval_comp, Polynomial.eval_X] at hval
  linarith [hval]

/-- Second derivative of `T_n` is even in absolute value
(copy of a private lemma in `ChebDeriv`). -/
private lemma abs_deriv2_chebyshevT_neg_t (n : ℤ) (x : ℝ) :
    |(Polynomial.Chebyshev.T ℝ n).derivative.derivative.eval (-x)|
      = |(Polynomial.Chebyshev.T ℝ n).derivative.derivative.eval x| := by
  have hc : |(((n.negOnePow : ℤ) : ℝ))| = 1 := by
    rw [← Int.cast_abs, Int.abs_negOnePow]
    norm_num
  have hT : ∀ y : ℝ, (Polynomial.Chebyshev.T ℝ n).eval (-y)
      = (((n.negOnePow : ℤ) : ℝ)) * (Polynomial.Chebyshev.T ℝ n).eval y :=
    fun y => Polynomial.Chebyshev.T_eval_neg ℝ n y
  have hp : ∀ y : ℝ, (Polynomial.Chebyshev.T ℝ n).derivative.eval (-y)
      = (-(((n.negOnePow : ℤ) : ℝ))) * (Polynomial.Chebyshev.T ℝ n).derivative.eval y := by
    intro y
    rw [deriv_eval_neg_of_eval_neg_t hT y]
    ring
  rw [deriv_eval_neg_of_eval_neg_t hp x, abs_neg, abs_mul, abs_neg, hc, one_mul]

/-- **Tight Chebyshev bound.** `|T_n''| ≤ (13/10) * N ^ 4` on `[-1, 1]`. -/
lemma abs_deriv2_chebyshevT_le_tight (n : ℤ) {u : ℝ} (hu : u ∈ Set.Icc (-1 : ℝ) 1) :
    |(Polynomial.Chebyshev.T ℝ n).derivative.derivative.eval u|
      ≤ 13 / 10 * ((n.natAbs : ℝ)) ^ 4 := by
  have hclosed : IsClosed {u : ℝ |
      |(Polynomial.Chebyshev.T ℝ n).derivative.derivative.eval u|
        ≤ 13 / 10 * ((n.natAbs : ℝ)) ^ 4} :=
    isClosed_le (Polynomial.continuous _).abs continuous_const
  have hIcc : Set.Icc (0 : ℝ) 1 ⊆ {u : ℝ |
      |(Polynomial.Chebyshev.T ℝ n).derivative.derivative.eval u|
        ≤ 13 / 10 * ((n.natAbs : ℝ)) ^ 4} := by
    rw [← closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    refine hclosed.closure_subset_iff.mpr fun u hu => ?_
    have hcos : Real.cos (Real.arccos u) = u :=
      Real.cos_arccos (by linarith [hu.1]) hu.2.le
    rw [← hcos]
    exact abs_deriv2_chebyshevT_cos_le_tight n (Real.arccos_pos.mpr hu.2)
      (le_of_lt (Real.arccos_lt_pi_div_two.mpr hu.1))
  by_cases h : 0 ≤ u
  · exact hIcc ⟨h, hu.2⟩
  · have hlt : u < 0 := not_le.mp h
    have h2 : -u ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith [hu.1]⟩
    exact (abs_deriv2_chebyshevT_neg_t n u) ▸ hIcc h2

/-- `T_n` has the same derivative over `ℂ` and over `ℝ` on the real axis
(copy of a private lemma in `ChebDeriv`). -/
private lemma chebyshevT_complex_derivative_eval_t (n : ℤ) (u : ℝ) :
    (Polynomial.Chebyshev.T ℂ n).derivative.eval (u : ℂ)
      = (((Polynomial.Chebyshev.T ℝ n).derivative.eval u : ℝ) : ℂ) := by
  have hA : HasDerivAt (fun y : ℝ => (Polynomial.Chebyshev.T ℂ n).eval (y : ℂ))
      ((Polynomial.Chebyshev.T ℂ n).derivative.eval (u : ℂ)) u :=
    (Polynomial.hasDerivAt (Polynomial.Chebyshev.T ℂ n) (u : ℂ)).comp_ofReal
  have hB : HasDerivAt (fun y : ℝ => (((Polynomial.Chebyshev.T ℝ n).eval y : ℝ) : ℂ))
      (((Polynomial.Chebyshev.T ℝ n).derivative.eval u : ℝ) : ℂ) u :=
    (Polynomial.hasDerivAt (Polynomial.Chebyshev.T ℝ n) u).ofReal_comp
  have hfun : (fun y : ℝ => (((Polynomial.Chebyshev.T ℝ n).eval y : ℝ) : ℂ))
      = fun y : ℝ => (Polynomial.Chebyshev.T ℂ n).eval (y : ℂ) :=
    funext fun y => Polynomial.Chebyshev.complex_ofReal_eval_T y n
  rw [hfun] at hB
  exact hA.unique hB

/-- `T_n''` has the same value over `ℂ` and over `ℝ` on the real axis
(copy of a private lemma in `ChebDeriv`). -/
private lemma chebyshevT_complex_derivative2_eval_t (n : ℤ) (u : ℝ) :
    (Polynomial.Chebyshev.T ℂ n).derivative.derivative.eval (u : ℂ)
      = (((Polynomial.Chebyshev.T ℝ n).derivative.derivative.eval u : ℝ) : ℂ) := by
  have hA : HasDerivAt (fun y : ℝ => (Polynomial.Chebyshev.T ℂ n).derivative.eval (y : ℂ))
      ((Polynomial.Chebyshev.T ℂ n).derivative.derivative.eval (u : ℂ)) u :=
    (Polynomial.hasDerivAt (Polynomial.Chebyshev.T ℂ n).derivative (u : ℂ)).comp_ofReal
  have hB : HasDerivAt
      (fun y : ℝ => (((Polynomial.Chebyshev.T ℝ n).derivative.eval y : ℝ) : ℂ))
      (((Polynomial.Chebyshev.T ℝ n).derivative.derivative.eval u : ℝ) : ℂ) u :=
    (Polynomial.hasDerivAt (Polynomial.Chebyshev.T ℝ n).derivative u).ofReal_comp
  have hfun : (fun y : ℝ => (((Polynomial.Chebyshev.T ℝ n).derivative.eval y : ℝ) : ℂ))
      = fun y : ℝ => (Polynomial.Chebyshev.T ℂ n).derivative.eval (y : ℂ) :=
    funext fun y => (chebyshevT_complex_derivative_eval_t n y).symm
  rw [hfun] at hB
  exact hA.unique hB

/-- Complex form of the tight second derivative bound. -/
lemma norm_deriv2_chebyshevT_complex_le_tight (n : ℤ) {u : ℝ}
    (hu : u ∈ Set.Icc (-1 : ℝ) 1) :
    ‖(Polynomial.Chebyshev.T ℂ n).derivative.derivative.eval (u : ℂ)‖
      ≤ 13 / 10 * ((n.natAbs : ℝ)) ^ 4 := by
  rw [chebyshevT_complex_derivative2_eval_t n u, Complex.norm_real]
  exact abs_deriv2_chebyshevT_le_tight n hu

/-! ## §1. Tight `D2` chain: `nrD2of_tight`, `nrCcal_tight`, `nr_kappa_le_tight`. -/

/-- Term-2 bound, in weighted form (tight `(13/10)k⁴`). -/
lemma nr_term2_le_tight (C : nrCheb) {μ : ℝ} (hμ : |μ| ≤ C.τ) (m : ℕ) :
    ‖nrTerm2 C.a C.τ C.q m μ‖
      ≤ ((13 / 5) / C.τ ^ 2)
        * ((((C.q : ℝ) + (m : ℝ)) ^ 4 * majorB C.τ (C.q + m))) := by
  have hτ : 0 < C.τ := by linarith [C.hτ1]
  have hu := nr_div_mem_Icc hτ hμ
  have hT := norm_deriv2_chebyshevT_complex_le_tight (((C.q + m : ℕ)) : ℤ) hu
  rw [Int.natAbs_natCast] at hT
  have hA := C.hA m
  have hτC : ‖((((C.τ : ℝ))) : ℂ) ^ 2‖ = C.τ ^ 2 := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ]
  have hkm : ((((C.q + m : ℕ)) : ℝ)) = (C.q : ℝ) + (m : ℝ) := by
    push_cast
    ring
  have hBnn : (0 : ℝ) ≤ 2 * majorB C.τ (C.q + m) :=
    mul_nonneg (by norm_num) (nr_majorB_nonneg _ _)
  unfold nrTerm2
  rw [norm_mul, norm_div, hτC]
  have hT16 : ‖(Polynomial.Chebyshev.T ℂ (((C.q + m : ℕ)) : ℤ)).derivative.derivative.eval
      (((μ / C.τ : ℝ)) : ℂ)‖ ≤ (13 / 10) * (((C.q : ℝ) + (m : ℝ)) ^ 4) := by
    have h1 := hT
    rwa [hkm] at h1
  have hT2 : ‖(Polynomial.Chebyshev.T ℂ (((C.q + m : ℕ)) : ℤ)).derivative.derivative.eval
      (((μ / C.τ : ℝ)) : ℂ)‖ / C.τ ^ 2
      ≤ ((13 / 10) * (((C.q : ℝ) + (m : ℝ)) ^ 4)) / C.τ ^ 2 := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hT16
      (inv_nonneg.mpr (pow_nonneg hτ.le 2))
  calc ‖C.a m‖ * (‖(Polynomial.Chebyshev.T ℂ (((C.q + m : ℕ)) : ℤ)).derivative.derivative.eval
        (((μ / C.τ : ℝ)) : ℂ)‖ / C.τ ^ 2)
      ≤ (2 * majorB C.τ (C.q + m)) * (((13 / 10) * (((C.q : ℝ) + (m : ℝ)) ^ 4)) / C.τ ^ 2) :=
        mul_le_mul hA hT2
          (div_nonneg (norm_nonneg _) (pow_nonneg hτ.le 2)) hBnn
    _ = ((13 / 5) / C.τ ^ 2)
        * ((((C.q : ℝ) + (m : ℝ)) ^ 4 * majorB C.τ (C.q + m))) := by
        ring

/-- `D2` bound value (tight `(13/10)`-form). -/
noncomputable def nrD2of_tight (C : nrCheb) : ℝ :=
  (13 / 10) * nrEta2of C.τ C.q * (C.q : ℝ) ^ 4 * nrE2 C.τ C.q / C.τ ^ 2

/-- L4 second-derivative bound (tight `(13/10)`-form). -/
lemma nr_D2_le_tight (C : nrCheb) {μ : ℝ} (hμ : |μ| ≤ C.τ) :
    ‖deriv (deriv C.Ψ) μ‖ ≤ nrD2of_tight C := by
  have hτ : 0 < C.τ := by linarith [C.hτ1]
  have hq2 : 2 ≤ C.q := C.hq2
  have hS := C.hSer2 μ hμ
  rw [← hS.tsum_eq]
  have hW1 : Summable
      (fun m : ℕ => ((((C.q : ℝ) + (m : ℝ)) ^ 4 * majorB C.τ (C.q + m)))) := by
    have h := nr_summable_weighted hτ hq2 C.hτq 2
    simpa using h
  have hCsum : Summable (fun m : ℕ => ((13 / 5) / C.τ ^ 2)
      * ((((C.q : ℝ) + (m : ℝ)) ^ 4 * majorB C.τ (C.q + m)))) :=
    hW1.mul_left ((13 / 5) / C.τ ^ 2)
  have hnorm : Summable (fun m : ℕ => ‖nrTerm2 C.a C.τ C.q m μ‖) :=
    Summable.of_nonneg_of_le (fun m => norm_nonneg _)
      (fun m => nr_term2_le_tight C hμ m) hCsum
  have hW := nr_weighted2 hτ hq2 C.hτq
  have hnnc : (0 : ℝ) ≤ (13 / 5) / C.τ ^ 2 :=
    div_nonneg (by norm_num) (pow_nonneg hτ.le 2)
  calc ‖∑' m : ℕ, nrTerm2 C.a C.τ C.q m μ‖
      ≤ ∑' m : ℕ, ‖nrTerm2 C.a C.τ C.q m μ‖ :=
        norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' m : ℕ, ((13 / 5) / C.τ ^ 2)
          * ((((C.q : ℝ) + (m : ℝ)) ^ 4 * majorB C.τ (C.q + m))) :=
        Summable.tsum_le_tsum (fun m => nr_term2_le_tight C hμ m) hnorm hCsum
    _ = ((13 / 5) / C.τ ^ 2) * (∑' m : ℕ, ((((C.q : ℝ) + (m : ℝ)) ^ 4
          * majorB C.τ (C.q + m)))) := tsum_mul_left
    _ ≤ ((13 / 5) / C.τ ^ 2) * ((C.q : ℝ) ^ 4 * nrEta2 (nrR C.τ C.q)
          * (∑' m : ℕ, majorB C.τ (C.q + m))) :=
        mul_le_mul_of_nonneg_left hW hnnc
    _ = nrD2of_tight C := by
        unfold nrD2of_tight nrEta2of nrE2
        ring

/-- Tight `D2` bound is nonnegative. -/
lemma nrD2of_tight_nonneg (C : nrCheb) : 0 ≤ nrD2of_tight C := by
  have hτ : 0 < C.τ := by linarith [C.hτ1]
  have heta := nrEta2_nonneg (nrR_nonneg C.τ C.q)
    (nrR_lt_one (nr_alpha_pos hτ C.hτq))
  unfold nrD2of_tight nrEta2of
  exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) heta)
    (pow_nonneg (Nat.cast_nonneg _) 4)) (nrE2_nonneg _ _))
    (pow_nonneg hτ.le 2)

/-- Restated tight `Ccal` (`D2`-term `(13/5)·η2·q²`). -/
noncomputable def nrCcal_tight (τ : ℝ) (q : ℕ) : ℝ :=
  (2 / Real.pi) * (1 / (q : ℝ))
    * Real.sqrt (2 * (1 + (nrB τ q) / τ) * (1 + (4 / 27) * (nrEta1of τ q))
      * ((13 / 5) * (nrEta2of τ q) * (q : ℝ) ^ 2 + 44
        + 2 * (12 + 16 / 27) * (nrEta1of τ q)))

/-- `nrCcal_tight ≥ 0`. -/
lemma nrCcal_tight_nonneg (τ : ℝ) (q : ℕ) (hqpos : (0 : ℝ) < (q : ℝ)) :
    0 ≤ nrCcal_tight τ q := by
  unfold nrCcal_tight
  have h1 : (0 : ℝ) ≤ 2 / Real.pi :=
    div_nonneg (by norm_num) Real.pi_pos.le
  have h2 : (0 : ℝ) ≤ 1 / (q : ℝ) :=
    div_nonneg (by norm_num) hqpos.le
  exact mul_nonneg (mul_nonneg h1 h2) (Real.sqrt_nonneg _)

/-- The tightened criterion dominates the old one: `nrCcal_tight ≤ nrCcal`. -/
lemma nrCcal_tight_le {τ : ℝ} (hτ : 0 < τ) {q : ℕ} (hlt : τ < (q : ℝ)) :
    nrCcal_tight τ q ≤ nrCcal τ q := by
  have hα := nr_alpha_pos hτ hlt
  have hr0 := nrR_nonneg τ q
  have hr1 := nrR_lt_one hα
  have he2nn : (0 : ℝ) ≤ nrEta2of τ q := by
    show 0 ≤ nrEta2 (nrR τ q)
    exact nrEta2_nonneg hr0 hr1
  have hqnn : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg _
  have hD : (13 / 5) * (nrEta2of τ q) * (q : ℝ) ^ 2
      ≤ 32 * (nrEta2of τ q) * (q : ℝ) ^ 2 := by
    have h : (13 / 5 : ℝ) * (nrEta2of τ q) ≤ 32 * (nrEta2of τ q) :=
      mul_le_mul_of_nonneg_right (by norm_num) he2nn
    exact mul_le_mul h (le_refl _) (sq_nonneg _) (mul_nonneg (by norm_num) he2nn)
  have harg : 2 * (1 + nrB τ q / τ) * (1 + (4 / 27) * (nrEta1of τ q))
        * ((13 / 5) * (nrEta2of τ q) * ((q : ℕ) : ℝ) ^ 2 + 44
          + 2 * (12 + 16 / 27) * (nrEta1of τ q))
      ≤ 2 * (1 + nrB τ q / τ) * (1 + (4 / 27) * (nrEta1of τ q))
        * (32 * (nrEta2of τ q) * ((q : ℕ) : ℝ) ^ 2 + 44
          + 2 * (12 + 16 / 27) * (nrEta1of τ q)) := by
    have hnn1 : (0 : ℝ) ≤ 2 * (1 + nrB τ q / τ) * (1 + (4 / 27) * (nrEta1of τ q)) := by
      have he1nn : (0 : ℝ) ≤ nrEta1of τ q := by
        have h := nrEta1_ge_one hr0 hr1
        show (0:ℝ) ≤ nrEta1 (nrR τ q)
        exact le_trans zero_le_one h
      have hBnn : (0 : ℝ) ≤ nrB τ q / τ := by
        unfold nrB
        exact div_nonneg (div_nonneg hτ.le (pow_nonneg hqnn 2)) hτ.le
      have p1 : (0 : ℝ) ≤ 1 + nrB τ q / τ := by linarith [hBnn]
      have p2 : (0 : ℝ) ≤ 1 + (4 / 27) * (nrEta1of τ q) := by
        have : (0:ℝ) ≤ (4 / 27) * (nrEta1of τ q) := mul_nonneg (by norm_num) he1nn
        linarith [this]
      exact mul_nonneg (mul_nonneg (by norm_num) p1) p2
    apply mul_le_mul_of_nonneg_left _ hnn1
    have hnn44 : (0 : ℝ) ≤ (44 : ℝ) := by norm_num
    have hnn3 : (0 : ℝ) ≤ 2 * (12 + 16 / 27) * (nrEta1of τ q) := by
      have he1nn : (0 : ℝ) ≤ nrEta1of τ q := by
        have h := nrEta1_ge_one hr0 hr1
        show (0:ℝ) ≤ nrEta1 (nrR τ q)
        exact le_trans zero_le_one h
      positivity
    linarith [hD, hnn44, hnn3]
  unfold nrCcal_tight nrCcal
  exact mul_le_mul (le_refl _)
    (Real.sqrt_le_sqrt harg) (Real.sqrt_nonneg _) (by positivity)

/-- `A·C` factored form, tight version. -/
lemma nr_AC_eq_tight (C : nrCheb) (hτ0 : C.τ ≠ 0) (hq0 : (C.q : ℝ) ≠ 0) :
    Realize.RealizeA C.τ (nrB C.τ C.q) (nrE2 C.τ C.q) (nrD1of C)
      * Realize.RealizeC C.τ (nrB C.τ C.q) (nrE2 C.τ C.q) (nrD1of C)
        (nrD2of_tight C) 4
      = ((C.q : ℝ) * nrE2 C.τ C.q) ^ 2
        * (2 * (1 + nrB C.τ C.q / C.τ)
          * (1 + 4 / 27 * nrEta1of C.τ C.q)
          * ((13 / 5) * nrEta2of C.τ C.q * (C.q : ℝ) ^ 2 + 44
            + 2 * (12 + 16 / 27) * nrEta1of C.τ C.q)) := by
  unfold Realize.RealizeA Realize.RealizeC nrD1of nrD2of_tight nrB
  field_simp
  ring

/-- L4 kernel bound, tight version: `‖κ‖₁ ≤ Ccal_tight·q²·E2`. -/
lemma nr_kappa_le_tight (C : nrCheb) :
    ∫ t : ℝ, ‖Realize.kap C.τ (nrB C.τ C.q) C.Ψ C.χ t‖
      ≤ nrCcal_tight C.τ C.q * (C.q : ℝ) ^ 2 * nrE2 C.τ C.q := by
  have hτ : 0 < C.τ := by linarith [C.hτ1]
  have hτ0 : C.τ ≠ 0 := ne_of_gt hτ
  have hq1 : 1 ≤ C.q := by have h := C.hq2; omega
  have hqR : (1 : ℝ) ≤ (C.q : ℝ) := by exact_mod_cast hq1
  have hqpos : (0 : ℝ) < (C.q : ℝ) := by linarith [hqR]
  have hq0 : (C.q : ℝ) ≠ 0 := ne_of_gt hqpos
  have hB0 : 0 < nrB C.τ C.q := by
    unfold nrB
    exact div_pos hτ (pow_pos hqpos 2)
  have hE0 : 0 < nrE2 C.τ C.q := nrE2_pos hτ hq1 C.hτq
  have hD1nn : 0 ≤ nrD1of C := nrD1of_nonneg C
  have hD2nn : 0 ≤ nrD2of_tight C := nrD2of_tight_nonneg C
  have hΨ0 : ∀ μ : ℝ, |μ| ≤ C.τ → ‖C.Ψ μ‖ ≤ nrE2 C.τ C.q :=
    fun μ hμ => nr_sup_le C hμ
  have hΨ1 : ∀ μ : ℝ, |μ| ≤ C.τ → ‖deriv C.Ψ μ‖ ≤ nrD1of C :=
    fun μ hμ => nr_D1_le C hμ
  have hΨ2 : ∀ μ : ℝ, |μ| ≤ C.τ → ‖deriv (deriv C.Ψ) μ‖ ≤ nrD2of_tight C :=
    fun μ hμ => nr_D2_le_tight C hμ
  have hkap := Realize.kap_L1_le C.hτ1 hB0 hE0 (show (1 : ℝ) ≤ 4 by norm_num)
    hD1nn hD2nn C.hΨ hΨ0 hΨ1 hΨ2 C.hχ C.hχ1 C.hχb C.hχd1 C.hχd2
  have hqe : (0 : ℝ) ≤ (C.q : ℝ) * nrE2 C.τ C.q :=
    mul_nonneg hqpos.le (nrE2_nonneg _ _)
  have hAC := nr_AC_eq_tight C hτ0 hq0
  calc ∫ t : ℝ, ‖Realize.kap C.τ (nrB C.τ C.q) C.Ψ C.χ t‖
      ≤ (2 / Real.pi) * Real.sqrt (Realize.RealizeA C.τ (nrB C.τ C.q)
          (nrE2 C.τ C.q) (nrD1of C)
          * Realize.RealizeC C.τ (nrB C.τ C.q) (nrE2 C.τ C.q) (nrD1of C)
            (nrD2of_tight C) 4) := hkap
    _ = (2 / Real.pi) * (((C.q : ℝ) * nrE2 C.τ C.q)
          * Real.sqrt (2 * (1 + nrB C.τ C.q / C.τ)
            * (1 + 4 / 27 * nrEta1of C.τ C.q)
            * ((13 / 5) * nrEta2of C.τ C.q * (C.q : ℝ) ^ 2 + 44
              + 2 * (12 + 16 / 27) * nrEta1of C.τ C.q))) := by
        rw [hAC, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hqe]
    _ = nrCcal_tight C.τ C.q * (C.q : ℝ) ^ 2 * nrE2 C.τ C.q := by
        unfold nrCcal_tight
        field_simp

/-! ## §2. Generic L5 rung (kernel bound as a parameter) and the tight wrapper. -/

/-- L5 main rung, generic in the kernel-bound constant `K`: if
`∫‖κ‖ ≤ K·q²·E2` and the tight-form criterion holds with `K`, then `2τ < cost`. -/
theorem nr_main_rung_of_kappa {N : ℕ} {φ : ℝ} {L : ℕ} {α θ : Fin L → ℝ} (C : nrCheb)
    (K : ℝ)
    (hN : 1 ≤ N) (hφ0 : 0 < φ) (hφπ : φ ≤ Real.pi)
    (hAdm : Admissible N φ L α θ)
    (hqN : C.q = 2 * N + 2)
    (hkap : ∫ t : ℝ, ‖Realize.kap C.τ (nrB C.τ C.q) C.Ψ C.χ t‖
      ≤ K * (C.q : ℝ) ^ 2 * nrE2 C.τ C.q)
    (hKnn : 0 ≤ K * (C.q : ℝ) ^ 2)
    (hmain : K * (C.q : ℝ) ^ 2 * nrE2star C.τ C.q
      < Real.sin (φ / 4) ^ 2) :
    2 * C.τ < cost θ := by
  by_contra hcon
  have hcon : cost θ ≤ 2 * C.τ := le_of_not_gt hcon
  obtain ⟨ι, hι, c, ν, hν, hrep, hmom, hsum0⟩ := h_moments N φ L α θ hAdm
  have hτ : 0 < C.τ := by linarith [C.hτ1]
  have hqpos : (0 : ℝ) < (C.q : ℝ) := by
    have h2 := C.hq2
    have : (0 : ℕ) < C.q := by omega
    exact_mod_cast this
  -- frequencies lie in the band
  have hTτ : ∀ i, |ν i| ≤ C.τ := by
    intro i
    have h1 := hν i
    have h2 : (∑ j, θ j) / 2 ≤ C.τ := by
      have hT : (∑ j, θ j) = cost θ := rfl
      rw [hT]
      linarith [hcon]
    linarith [h1, h2]
  -- shifted coefficients
  set Γ : ι → ℂ := fun i =>
    Complex.exp ((((ν i : ℝ)) : ℂ) * Complex.I) * c i with hΓdef
  have hΓ : ∀ i, Γ i =
      Complex.exp ((((ν i : ℝ)) : ℂ) * Complex.I) * c i := fun i => by
    rw [hΓdef]
  have hq : C.q = 2 * N + 2 := hqN
  -- `h(0) = Σ ΓΨ(ν)`
  have hPsi_sum : ∑ i, Γ i * C.Ψ (ν i) = ((h L α θ 0 : ℝ) : ℂ) := by
    have hQ0 : ∑ i, Γ i * C.Q.eval ((((ν i : ℝ)) : ℂ)) = 0 := by
      have h := nr_gamma_moments (q := C.q) hΓ
        (fun P hP => hmom P (hq ▸ hP)) C.Q C.hQ
      calc ∑ i, Γ i * C.Q.eval ((((ν i : ℝ)) : ℂ))
          = ∑ i, C.Q.eval ((((ν i : ℝ)) : ℂ)) * Γ i :=
            Finset.sum_congr rfl fun i _ => mul_comm _ _
        _ = 0 := h
    have hE : ∀ i ∈ Finset.univ,
        Γ i * Complex.exp (-((((ν i : ℝ)) : ℂ)) * Complex.I) = c i := by
      intro i _
      have hexp : Complex.exp ((((ν i : ℝ)) : ℂ) * Complex.I)
          * Complex.exp (-((((ν i : ℝ)) : ℂ)) * Complex.I) = 1 := by
        rw [← Complex.exp_add]
        have hz : ((((ν i : ℝ)) : ℂ) * Complex.I
            + -((((ν i : ℝ)) : ℂ)) * Complex.I) = 0 := by ring
        rw [hz, Complex.exp_zero]
      calc Γ i * Complex.exp (-((((ν i : ℝ)) : ℂ)) * Complex.I)
          = (Complex.exp ((((ν i : ℝ)) : ℂ) * Complex.I)
              * Complex.exp (-((((ν i : ℝ)) : ℂ)) * Complex.I)) * c i := by
              rw [hΓ i]; ring
        _ = 1 * c i := by rw [hexp]
        _ = c i := one_mul _
    have hEsum : ∑ i, Γ i * Complex.exp (-((((ν i : ℝ)) : ℂ)) * Complex.I)
        = ((h L α θ 0 : ℝ) : ℂ) := by
      calc ∑ i, Γ i * Complex.exp (-((((ν i : ℝ)) : ℂ)) * Complex.I)
          = ∑ i, c i := Finset.sum_congr rfl hE
        _ = ((h L α θ 0 : ℝ) : ℂ) := hsum0.symm
    have eΨ : ∀ i ∈ Finset.univ, Γ i * C.Ψ (ν i)
        = (Γ i * Complex.exp (-((((ν i : ℝ)) : ℂ)) * Complex.I))
          - Γ i * C.Q.eval ((((ν i : ℝ)) : ℂ)) := by
      intro i _
      rw [C.hΨeq (ν i) (hTτ i)]
      ring
    calc ∑ i, Γ i * C.Ψ (ν i)
        = ∑ i, ((Γ i * Complex.exp (-((((ν i : ℝ)) : ℂ)) * Complex.I))
          - Γ i * C.Q.eval ((((ν i : ℝ)) : ℂ))) :=
          Finset.sum_congr rfl eΨ
      _ = (∑ i, Γ i * Complex.exp (-((((ν i : ℝ)) : ℂ)) * Complex.I))
          - (∑ i, Γ i * C.Q.eval ((((ν i : ℝ)) : ℂ))) :=
          Finset.sum_sub_distrib _ _
      _ = ((h L α θ 0 : ℝ) : ℂ) - 0 := by rw [hEsum, hQ0]
      _ = ((h L α θ 0 : ℝ) : ℂ) := sub_zero _
  -- kernel data
  have hq1 : 1 ≤ C.q := by have h := C.hq2; omega
  have hB0 : 0 < nrB C.τ C.q := by
    unfold nrB
    exact div_pos hτ (pow_pos hqpos 2)
  have hE0 : 0 < nrE2 C.τ C.q := nrE2_pos hτ hq1 C.hτq
  have hD1nn : 0 ≤ nrD1of C := nrD1of_nonneg C
  have hD2nn : 0 ≤ nrD2of_tight C := nrD2of_tight_nonneg C
  have hΨ0 : ∀ μ : ℝ, |μ| ≤ C.τ → ‖C.Ψ μ‖ ≤ nrE2 C.τ C.q :=
    fun μ hμ => nr_sup_le C hμ
  have hΨ1 : ∀ μ : ℝ, |μ| ≤ C.τ → ‖deriv C.Ψ μ‖ ≤ nrD1of C :=
    fun μ hμ => nr_D1_le C hμ
  have hΨ2 : ∀ μ : ℝ, |μ| ≤ C.τ → ‖deriv (deriv C.Ψ) μ‖ ≤ nrD2of_tight C :=
    fun μ hμ => nr_D2_le_tight C hμ
  have hκint : Integrable (Realize.kap C.τ (nrB C.τ C.q) C.Ψ C.χ) :=
    Realize.kap_integrable C.hτ1 hB0 hE0 (show (1 : ℝ) ≤ 4 by norm_num)
      hD1nn hD2nn C.hΨ hΨ0 hΨ1 hΨ2 C.hχ C.hχ1 C.hχb C.hχd1 C.hχd2
  have hinv := Realize.inversion_on_band C.hτ1 hB0 hE0
    (show (1 : ℝ) ≤ 4 by norm_num) hD1nn hD2nn C.hΨ hΨ0 hΨ1 hΨ2 C.hχ
    C.hχ1 C.hχb C.hχd1 C.hχd2
  -- per-frequency inversion in `ExpSum` exponential form
  have hinv_i : ∀ i, (∫ t : ℝ, Realize.kap C.τ (nrB C.τ C.q) C.Ψ C.χ t
      * Complex.exp ((((ν i * t : ℝ)) : ℂ) * Complex.I)) = C.Ψ (ν i) := by
    intro i
    have h := hinv (ν i) (hTτ i)
    have eexp : ∀ t : ℝ, Complex.exp ((((ν i * t : ℝ)) : ℂ) * Complex.I)
        = Complex.exp ((((ν i : ℝ)) : ℂ) * Complex.I * ((t : ℝ) : ℂ)) := by
      intro t
      congr 1
      push_cast
      ring
    calc (∫ t : ℝ, Realize.kap C.τ (nrB C.τ C.q) C.Ψ C.χ t
          * Complex.exp ((((ν i * t : ℝ)) : ℂ) * Complex.I))
        = ∫ t : ℝ, Realize.kap C.τ (nrB C.τ C.q) C.Ψ C.χ t
          * Complex.exp ((((ν i : ℝ)) : ℂ) * Complex.I * ((t : ℝ) : ℂ)) := by
            refine MeasureTheory.integral_congr_ae
              (Filter.Eventually.of_forall fun t => ?_)
            simp only []
            rw [eexp t]
      _ = C.Ψ (ν i) := h
  -- per-term integrability
  have hFi : ∀ i ∈ Finset.univ,
      Integrable (fun t : ℝ => Realize.kap C.τ (nrB C.τ C.q) C.Ψ C.χ t
        * (Γ i * Complex.exp ((((ν i * t : ℝ)) : ℂ) * Complex.I))) := by
    intro i _
    have hcont : Continuous
        (fun t : ℝ => Γ i * Complex.exp ((((ν i * t : ℝ)) : ℂ) * Complex.I)) := by
      fun_prop
    have hbdd : ∀ᵐ t : ℝ, ‖Γ i
        * Complex.exp ((((ν i * t : ℝ)) : ℂ) * Complex.I)‖ ≤ ‖Γ i‖ := by
      refine Filter.Eventually.of_forall fun t => ?_
      have he : ‖Complex.exp ((((ν i * t : ℝ)) : ℂ) * Complex.I)‖ = 1 := by
        rw [Complex.norm_exp]
        have hre : ((((ν i * t : ℝ)) : ℂ) * Complex.I).re = 0 := by
          simp [Complex.mul_re]
        rw [hre, Real.exp_zero]
      rw [norm_mul, he, mul_one]
    exact hκint.mul_bdd hcont.aestronglyMeasurable hbdd
  -- `∫κ·G = ΣΓΨ`
  have hG : (∫ t : ℝ, Realize.kap C.τ (nrB C.τ C.q) C.Ψ C.χ t
      * (∑ i, Γ i * Complex.exp ((((ν i * t : ℝ)) : ℂ) * Complex.I)))
      = ∑ i, Γ i * C.Ψ (ν i) := by
    have eG : (fun t : ℝ => Realize.kap C.τ (nrB C.τ C.q) C.Ψ C.χ t
        * (∑ i, Γ i * Complex.exp ((((ν i * t : ℝ)) : ℂ) * Complex.I)))
        = (fun t : ℝ => ∑ i, Realize.kap C.τ (nrB C.τ C.q) C.Ψ C.χ t
          * (Γ i * Complex.exp ((((ν i * t : ℝ)) : ℂ) * Complex.I))) := by
      funext t
      rw [Finset.mul_sum]
    rw [eG, MeasureTheory.integral_finsetSum _ (fun i hi => hFi i hi)]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hIi : (∫ t : ℝ, Realize.kap C.τ (nrB C.τ C.q) C.Ψ C.χ t
        * (Γ i * Complex.exp ((((ν i * t : ℝ)) : ℂ) * Complex.I)))
        = Γ i * (∫ t : ℝ, Realize.kap C.τ (nrB C.τ C.q) C.Ψ C.χ t
          * Complex.exp ((((ν i * t : ℝ)) : ℂ) * Complex.I)) := by
      have e : (fun t : ℝ => Realize.kap C.τ (nrB C.τ C.q) C.Ψ C.χ t
          * (Γ i * Complex.exp ((((ν i * t : ℝ)) : ℂ) * Complex.I)))
          = (fun t : ℝ => Γ i * (Realize.kap C.τ (nrB C.τ C.q) C.Ψ C.χ t
            * Complex.exp ((((ν i * t : ℝ)) : ℂ) * Complex.I))) := by
        funext t
        ring
      rw [e, MeasureTheory.integral_const_mul]
    rw [hIi, hinv_i i]
  -- norm bound
  have hGint : Integrable (fun t : ℝ => Realize.kap C.τ (nrB C.τ C.q) C.Ψ C.χ t
      * (∑ i, Γ i * Complex.exp ((((ν i * t : ℝ)) : ℂ) * Complex.I))) := by
    have eG : (fun t : ℝ => Realize.kap C.τ (nrB C.τ C.q) C.Ψ C.χ t
        * (∑ i, Γ i * Complex.exp ((((ν i * t : ℝ)) : ℂ) * Complex.I)))
        = (fun t : ℝ => ∑ i, Realize.kap C.τ (nrB C.τ C.q) C.Ψ C.χ t
          * (Γ i * Complex.exp ((((ν i * t : ℝ)) : ℂ) * Complex.I))) := by
      funext t
      rw [Finset.mul_sum]
    rw [eG]
    exact MeasureTheory.integrable_finsetSum _ (fun i hi => hFi i hi)
  have hbnd : ‖(∫ t : ℝ, Realize.kap C.τ (nrB C.τ C.q) C.Ψ C.χ t
      * (∑ i, Γ i * Complex.exp ((((ν i * t : ℝ)) : ℂ) * Complex.I)))‖
      ≤ 2 * (K * (C.q : ℝ) ^ 2 * nrE2 C.τ C.q) := by
    have hle1 : ‖(∫ t : ℝ, Realize.kap C.τ (nrB C.τ C.q) C.Ψ C.χ t
        * (∑ i, Γ i * Complex.exp ((((ν i * t : ℝ)) : ℂ) * Complex.I)))‖
        ≤ ∫ t : ℝ, ‖Realize.kap C.τ (nrB C.τ C.q) C.Ψ C.χ t
          * (∑ i, Γ i * Complex.exp ((((ν i * t : ℝ)) : ℂ) * Complex.I))‖ :=
      MeasureTheory.norm_integral_le_integral_norm _
    have hle2 : (∫ t : ℝ, ‖Realize.kap C.τ (nrB C.τ C.q) C.Ψ C.χ t
        * (∑ i, Γ i * Complex.exp ((((ν i * t : ℝ)) : ℂ) * Complex.I))‖)
        ≤ ∫ t : ℝ, 2 * ‖Realize.kap C.τ (nrB C.τ C.q) C.Ψ C.χ t‖ := by
      apply MeasureTheory.integral_mono_ae hGint.norm
        (hκint.norm.const_mul 2)
      refine Filter.Eventually.of_forall fun t => ?_
      have h2 : ‖(∑ i, Γ i
          * Complex.exp ((((ν i * t : ℝ)) : ℂ) * Complex.I))‖ ≤ 2 := by
        have e : (∑ i, Γ i * Complex.exp ((((ν i * t : ℝ)) : ℂ) * Complex.I))
            = ((h L α θ (t + 1) : ℝ) : ℂ) := by
          have hr := hrep (t + 1)
          rw [hr]
          refine Finset.sum_congr rfl fun i _ => ?_
          have ex : Complex.exp ((((ν i * (t + 1) : ℝ)) : ℂ) * Complex.I)
              = Complex.exp ((((ν i * t : ℝ)) : ℂ) * Complex.I)
                * Complex.exp ((((ν i : ℝ)) : ℂ) * Complex.I) := by
            rw [← Complex.exp_add]
            congr 1
            push_cast
            ring
          rw [hΓ i, ex]
          ring
        rw [e, Complex.norm_real, Real.norm_eq_abs]
        exact nr_h_abs_le_two L α θ (t + 1)
      calc ‖Realize.kap C.τ (nrB C.τ C.q) C.Ψ C.χ t
            * (∑ i, Γ i * Complex.exp ((((ν i * t : ℝ)) : ℂ) * Complex.I))‖
          = ‖Realize.kap C.τ (nrB C.τ C.q) C.Ψ C.χ t‖
            * ‖(∑ i, Γ i * Complex.exp ((((ν i * t : ℝ)) : ℂ) * Complex.I))‖ :=
            norm_mul _ _
        _ ≤ ‖Realize.kap C.τ (nrB C.τ C.q) C.Ψ C.χ t‖ * 2 :=
            mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
        _ = 2 * ‖Realize.kap C.τ (nrB C.τ C.q) C.Ψ C.χ t‖ := mul_comm _ _
    have hle3 : (∫ t : ℝ, 2
        * ‖Realize.kap C.τ (nrB C.τ C.q) C.Ψ C.χ t‖)
        = 2 * ∫ t : ℝ, ‖Realize.kap C.τ (nrB C.τ C.q) C.Ψ C.χ t‖ := by
      rw [MeasureTheory.integral_const_mul]
    have hle4 : ∫ t : ℝ, ‖Realize.kap C.τ (nrB C.τ C.q) C.Ψ C.χ t‖
        ≤ K * (C.q : ℝ) ^ 2 * nrE2 C.τ C.q := hkap
    linarith [hle1, hle2, hle3, hle4]
  -- contradiction
  have h0R : 2 * Real.sin (φ / 4) ^ 2 ≤ h L α θ 0 :=
    two_mul_sin_sq_le_h_zero N L α θ hφ0 hφπ hAdm
  have h0C : ((h L α θ 0 : ℝ) : ℂ)
      = (∫ t : ℝ, Realize.kap C.τ (nrB C.τ C.q) C.Ψ C.χ t
        * (∑ i, Γ i * Complex.exp ((((ν i * t : ℝ)) : ℂ) * Complex.I))) := by
    rw [hG, hPsi_sum]
  have h0nn : (0 : ℝ) ≤ h L α θ 0 := by
    have hs : (0 : ℝ) ≤ Real.sin (φ / 4) ^ 2 := sq_nonneg _
    linarith [h0R, hs]
  have hfin : h L α θ 0 ≤ 2 * (K * (C.q : ℝ) ^ 2 * nrE2 C.τ C.q) := by
    have e : ‖((h L α θ 0 : ℝ) : ℂ)‖ = h L α θ 0 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0nn]
    rw [h0C] at e
    linarith [e, hbnd]
  have hE2s : nrE2 C.τ C.q ≤ nrE2star C.τ C.q :=
    nrE2_le_E2star hτ hq1 C.hτq
  have hCnn : (0 : ℝ) ≤ K * (C.q : ℝ) ^ 2 := hKnn
  have hfin2 : h L α θ 0
      ≤ 2 * (K * (C.q : ℝ) ^ 2 * nrE2star C.τ C.q) := by
    have hle : K * (C.q : ℝ) ^ 2 * nrE2 C.τ C.q
        ≤ K * (C.q : ℝ) ^ 2 * nrE2star C.τ C.q :=
      mul_le_mul_of_nonneg_left hE2s hCnn
    linarith [hfin, hle]
  linarith [h0R, hfin2, hmain]

/-- Unconditional tight rung: the exact-criterion rung with no `nrCheb`/inversion/
kernel hypotheses, using the tightened `nrCcal_tight` criterion. -/
theorem new_rung_final_tight {N : ℕ} {φ : ℝ} {L : ℕ} {α θ : Fin L → ℝ}
    (hN : 1 ≤ N) (hφ0 : 0 < φ) (hφπ : φ ≤ Real.pi)
    (hAdm : Admissible N φ L α θ) (τ : ℝ) (hτ1 : 1 ≤ τ)
    (hlt : τ < ((2 * N + 2 : ℕ) : ℝ))
    (hmain : nrCcal_tight τ (2 * N + 2) * ((((2 * N + 2 : ℕ)) : ℝ)) ^ 2
      * nrE2star τ (2 * N + 2) < Real.sin (φ / 4) ^ 2) :
    2 * τ < cost θ := by
  have hq2 : 2 ≤ 2 * N + 2 := by omega
  have hqpos : (0 : ℝ) < ((((2 * N + 2 : ℕ)) : ℝ)) := by
    have : (0 : ℕ) < 2 * N + 2 := by omega
    exact_mod_cast this
  have hKnn : 0 ≤ nrCcal_tight τ (2 * N + 2) * ((((2 * N + 2 : ℕ)) : ℝ)) ^ 2 :=
    mul_nonneg (nrCcal_tight_nonneg τ (2 * N + 2) hqpos) (sq_nonneg _)
  exact nr_main_rung_of_kappa (nrCheb_of_truncation τ (2 * N + 2) hτ1 hq2 hlt)
    _ hN hφ0 hφπ hAdm rfl (nr_kappa_le_tight _) hKnn hmain

/-! ## §3. Tight enclosure helpers. -/

/-- `Ccal_tight` upper bound from `η` upper bounds (with `(13/5)`-term and
`2/π ≤ 0.6367`). -/
lemma nrCcal_tight_le_of {τ : ℝ} {q : ℕ} {e1 e2 Cs : ℝ}
    (hq : (2 : ℝ) ≤ ((q : ℕ) : ℝ)) (hτ : (0 : ℝ) < τ) (hlt : τ < ((q : ℕ) : ℝ))
    (he1 : nrEta1of τ q ≤ e1) (he1nn : (0 : ℝ) ≤ e1)
    (he2 : nrEta2of τ q ≤ e2) (he2nn : (0 : ℝ) ≤ e2)
    (hCs : 2 * (1 + 1 / ((q : ℕ) : ℝ) ^ 2) * (1 + (4 / 27) * e1)
      * ((13 / 5) * e2 * ((q : ℕ) : ℝ) ^ 2 + 44 + 2 * (12 + 16 / 27) * e1)
      ≤ Cs ^ 2)
    (hCsnn : (0 : ℝ) ≤ Cs) :
    nrCcal_tight τ q ≤ (0.6367 : ℝ) * (1 / ((q : ℕ) : ℝ)) * Cs := by
  have hq0 : (0 : ℝ) < ((q : ℕ) : ℝ) := by linarith
  have hB : nrB τ q / τ = 1 / ((q : ℕ) : ℝ) ^ 2 :=
    nrB_div_eq (ne_of_gt hτ) (ne_of_gt hq0)
  have hαpos : (0 : ℝ) < besselAlpha τ ((q : ℕ) : ℝ) := by
    unfold besselAlpha
    exact Real.arcosh_pos ((one_lt_div hτ).mpr hlt)
  have hr0 := nrR_nonneg τ q
  have hr1 := nrR_lt_one hαpos
  have he1nn0 : (0 : ℝ) ≤ nrEta1of τ q := by
    have h := nrEta1_ge_one hr0 hr1
    have rfl1 : nrEta1of τ q = nrEta1 (nrR τ q) := rfl
    rw [rfl1]
    exact le_trans zero_le_one h
  have he2nn0 : (0 : ℝ) ≤ nrEta2of τ q := by
    have h := nrEta2_nonneg hr0 hr1
    have rfl2 : nrEta2of τ q = nrEta2 (nrR τ q) := rfl
    rw [rfl2]
    exact h
  have hpi : (2 : ℝ) / Real.pi ≤ 0.6367 := by
    rw [div_le_iff₀ Real.pi_pos]
    have h := Real.pi_gt_d4
    linarith [h]
  have f1 : (1 : ℝ) + (4 / 27) * (nrEta1of τ q) ≤ 1 + (4 / 27) * e1 :=
    add_le_add (le_refl _)
      (mul_le_mul_of_nonneg_left he1 (show (0 : ℝ) ≤ 4 / 27 by norm_num))
  have f2 : (13 / 5) * (nrEta2of τ q) * ((q : ℕ) : ℝ) ^ 2 + 44
        + 2 * (12 + 16 / 27) * (nrEta1of τ q)
      ≤ (13 / 5) * e2 * ((q : ℕ) : ℝ) ^ 2 + 44 + 2 * (12 + 16 / 27) * e1 := by
    have g1 : (13 / 5) * (nrEta2of τ q) * ((q : ℕ) : ℝ) ^ 2
        ≤ (13 / 5) * e2 * ((q : ℕ) : ℝ) ^ 2 :=
      mul_le_mul (mul_le_mul_of_nonneg_left he2 (by norm_num)) (le_refl _)
        (sq_nonneg _) (mul_nonneg (by norm_num) he2nn)
    have g2 : 2 * (12 + 16 / 27) * (nrEta1of τ q)
        ≤ 2 * (12 + 16 / 27) * e1 :=
      mul_le_mul_of_nonneg_left he1 (by norm_num)
    exact add_le_add (add_le_add g1 (le_refl _)) g2
  have harg : 2 * (1 + nrB τ q / τ) * (1 + (4 / 27) * (nrEta1of τ q))
        * ((13 / 5) * (nrEta2of τ q) * ((q : ℕ) : ℝ) ^ 2 + 44
          + 2 * (12 + 16 / 27) * (nrEta1of τ q))
      ≤ 2 * (1 + 1 / ((q : ℕ) : ℝ) ^ 2) * (1 + (4 / 27) * e1)
        * ((13 / 5) * e2 * ((q : ℕ) : ℝ) ^ 2 + 44 + 2 * (12 + 16 / 27) * e1) := by
    rw [hB]
    have i1 : 2 * (1 + 1 / ((q : ℕ) : ℝ) ^ 2) * (1 + (4 / 27) * (nrEta1of τ q))
        ≤ 2 * (1 + 1 / ((q : ℕ) : ℝ) ^ 2) * (1 + (4 / 27) * e1) := by
      apply mul_le_mul (le_refl _) f1 _ _
      · exact add_nonneg zero_le_one
          (mul_nonneg (by norm_num) he1nn0)
      · exact mul_nonneg (by norm_num)
          (add_nonneg zero_le_one
            (le_of_lt (one_div_pos.mpr (pow_pos hq0 2))))
    have j0 : (0 : ℝ) ≤ (13 / 5) * (nrEta2of τ q) * ((q : ℕ) : ℝ) ^ 2 + 44
        + 2 * (12 + 16 / 27) * (nrEta1of τ q) :=
      add_nonneg
        (add_nonneg
          (mul_nonneg (mul_nonneg (by norm_num) he2nn0) (sq_nonneg _))
          (by norm_num))
        (mul_nonneg (by norm_num) he1nn0)
    have j1 : (0 : ℝ) ≤ 2 * (1 + 1 / ((q : ℕ) : ℝ) ^ 2)
        * (1 + (4 / 27) * e1) := by
      have p : (0 : ℝ) ≤ 1 + (4 / 27) * e1 :=
        add_nonneg zero_le_one (mul_nonneg (by norm_num) he1nn)
      have q2 : (0 : ℝ) ≤ 2 * (1 + 1 / ((q : ℕ) : ℝ) ^ 2) :=
        mul_nonneg (by norm_num)
          (add_nonneg zero_le_one
            (le_of_lt (one_div_pos.mpr (pow_pos hq0 2))))
      exact mul_nonneg q2 p
    exact mul_le_mul i1 f2 j0 j1
  have hsqrt : Real.sqrt (2 * (1 + nrB τ q / τ) * (1 + (4 / 27) * (nrEta1of τ q))
        * ((13 / 5) * (nrEta2of τ q) * ((q : ℕ) : ℝ) ^ 2 + 44
          + 2 * (12 + 16 / 27) * (nrEta1of τ q))) ≤ Cs := by
    have hle : Real.sqrt (2 * (1 + nrB τ q / τ) * (1 + (4 / 27) * (nrEta1of τ q))
          * ((13 / 5) * (nrEta2of τ q) * ((q : ℕ) : ℝ) ^ 2 + 44
            + 2 * (12 + 16 / 27) * (nrEta1of τ q)))
        ≤ Real.sqrt (Cs ^ 2) :=
      Real.sqrt_le_sqrt (le_trans harg hCs)
    rwa [Real.sqrt_sq hCsnn] at hle
  have hqinv : (0 : ℝ) < 1 / ((q : ℕ) : ℝ) := one_div_pos.mpr hq0
  have hpre : (2 / Real.pi) * (1 / ((q : ℕ) : ℝ))
      ≤ (0.6367 : ℝ) * (1 / ((q : ℕ) : ℝ)) :=
    mul_le_mul_of_nonneg_right hpi hqinv.le
  unfold nrCcal_tight
  exact mul_le_mul hpre hsqrt (Real.sqrt_nonneg _)
    (mul_nonneg (by norm_num) hqinv.le)

/-- `2√(π/8) ≤ 1.26` (tighter than the `1.42` from `π ≤ 4`). -/
lemma two_sqrt_pi_div_8_le : 2 * Real.sqrt (Real.pi / 8) ≤ (1.26 : ℝ) := by
  have hpi : Real.pi ≤ (3.1416 : ℝ) := Real.pi_lt_d4.le
  have h : Real.sqrt (Real.pi / 8) ≤ Real.sqrt ((3.1416 : ℝ) / 8) :=
    Real.sqrt_le_sqrt (by linarith [hpi])
  have h4 : Real.sqrt ((3.1416 : ℝ) / 8) ≤ (0.63 : ℝ) := by
    rw [Real.sqrt_le_iff]
    refine ⟨by norm_num, by norm_num⟩
  calc 2 * Real.sqrt (Real.pi / 8) ≤ 2 * Real.sqrt ((3.1416 : ℝ) / 8) :=
        mul_le_mul_of_nonneg_left h (by norm_num)
    _ ≤ 2 * (0.63 : ℝ) := mul_le_mul_of_nonneg_left h4 (by norm_num)
    _ = (1.26 : ℝ) := by norm_num

/-- Generic tight-criterion assembly: from separate `Ccal`/`E2star` upper
bounds and a numeric check, conclude the tight criterion. -/
lemma nr_tight_criterion {τ : ℝ} {q : ℕ} {C0 E0 : ℝ}
    (hC : nrCcal_tight τ q ≤ C0)
    (hE : nrE2star τ q ≤ E0)
    (hQnn : (0 : ℝ) ≤ C0 * (q : ℝ) ^ 2)
    (hEnn : (0 : ℝ) ≤ nrE2star τ q)
    (hfin : C0 * ((q : ℝ)) ^ 2 * E0 < 1 / 2) :
    nrCcal_tight τ q * ((q : ℝ)) ^ 2 * nrE2star τ q < 1 / 2 := by
  have step1 : nrCcal_tight τ q * ((q : ℝ)) ^ 2 ≤ C0 * ((q : ℝ)) ^ 2 :=
    mul_le_mul_of_nonneg_right hC (sq_nonneg _)
  have step2 : (nrCcal_tight τ q * ((q : ℝ)) ^ 2) * nrE2star τ q
      ≤ (C0 * ((q : ℝ)) ^ 2) * E0 :=
    mul_le_mul step1 hE hEnn hQnn
  exact lt_of_le_of_lt step2 hfin
/-! ## §4. Tight certified numbers. -/

/-- Certified tight number at `N = 12` (`φ = π`): `cost θ ≥ 28`, via the tight criterion
at `τ = 14`, `q = 26` (criterion value `≈ 0.32 < 1/2`). -/
theorem cert_N12_tight {L : ℕ} {α θ : Fin L → ℝ}
    (hAdm : Admissible 12 Real.pi L α θ) : 28 ≤ cost θ := by
  have hmain : nrCcal_tight (14:ℝ) 26 * (((26:ℕ):ℝ)) ^ 2
      * nrE2star (14:ℝ) 26 < Real.sin (Real.pi / 4) ^ 2 := by
    rw [sin_pi_div_four_sq]
    have hx1 : (1 : ℝ) < ((26:ℕ):ℝ) / (14:ℝ) := by norm_num
    have hs1 : (1.56:ℝ) ^ 2 ≤ (((26:ℕ):ℝ) / (14:ℝ)) ^ 2 - 1 := by norm_num
    have hsq1 : (1.56:ℝ)
        ≤ Real.sqrt ((((26:ℕ):ℝ) / (14:ℝ)) ^ 2 - 1) :=
      (Real.le_sqrt (by norm_num) (by norm_num)).mpr hs1
    have hy : (27/8:ℝ) ≤ ((26:ℕ):ℝ) / (14:ℝ)
        + Real.sqrt ((((26:ℕ):ℝ) / (14:ℝ)) ^ 2 - 1) :=
      le_trans (show (27/8:ℝ) ≤ ((26:ℕ):ℝ) / (14:ℝ) + (1.56:ℝ) by norm_num)
        (add_le_add (le_refl _) hsq1)
    have hlog : Real.log ((27/8):ℝ) = 3*Real.log 3 - 3*Real.log 2 := by
      rw [show ((27/8):ℝ) = (3^3)/(2^3) from by norm_num,
        Real.log_div (by norm_num) (by norm_num),
        Real.log_pow,
        Real.log_pow]
      push_cast; ring
    have ha : Real.log ((27/8):ℝ) ≤ Real.arcosh (((26:ℕ):ℝ) / (14:ℝ)) :=
      log_le_arcosh hx1 (show (0 : ℝ) < ((27/8):ℝ) by norm_num) hy
    have hα : (3*1.0986122885-3*0.6931471808:ℝ) ≤ Real.arcosh (((26:ℕ):ℝ) / (14:ℝ)) :=
      calc (3*1.0986122885-3*0.6931471808:ℝ) ≤ 3*Real.log 3 - 3*Real.log 2 :=
            sub_le_sub (mul_le_mul_of_nonneg_left Real.log_three_gt_d9.le (by norm_num)) (mul_le_mul_of_nonneg_left Real.log_two_lt_d9.le (by norm_num))
        _ = Real.log ((27/8):ℝ) := hlog.symm
        _ ≤ Real.arcosh (((26:ℕ):ℝ) / (14:ℝ)) := ha
    have hba : besselAlpha (14:ℝ) ((26:ℕ):ℝ)
        = Real.arcosh (((26:ℕ):ℝ) / (14:ℝ)) := rfl
    have hr : nrR (14:ℝ) 26 ≤ ((8/27):ℝ) := by
      have e := exp_neg_arcosh_le_inv hx1 (show (0 : ℝ) < ((27/8):ℝ) by norm_num) hy
      unfold nrR
      rw [hba]
      have e2 : (1 : ℝ) / ((27/8):ℝ) = ((8/27):ℝ) := by norm_num
      rw [← e2]
      exact e
    have he1 : nrEta1of (14:ℝ) 26 ≤ ((25515/6859):ℝ) := by
      have hmono := nrEta1_mono (nrR_nonneg _ _) hr (by norm_num)
      have e : nrEta1 ((8/27):ℝ) = ((25515/6859):ℝ) := by unfold nrEta1; norm_num
      show nrEta1 (nrR (14:ℝ) 26) ≤ _
      calc nrEta1 (nrR (14:ℝ) 26) ≤ nrEta1 ((8/27):ℝ) := hmono
        _ = ((25515/6859):ℝ) := e
    have he2 : nrEta2of (14:ℝ) 26 ≤ ((75345795/2476099):ℝ) := by
      have hmono := nrEta2_mono (nrR_nonneg _ _) hr (by norm_num)
      have e : nrEta2 ((8/27):ℝ) = ((75345795/2476099):ℝ) := by unfold nrEta2; norm_num
      show nrEta2 (nrR (14:ℝ) 26) ≤ _
      calc nrEta2 (nrR (14:ℝ) 26) ≤ nrEta2 ((8/27):ℝ) := hmono
        _ = ((75345795/2476099):ℝ) := e
    have hsqU : Real.sqrt (((26:ℕ):ℝ) ^ 2 - (14:ℝ) ^ 2) ≤ (21.91:ℝ) := by
      rw [Real.sqrt_le_iff]
      refine ⟨by norm_num, by norm_num⟩
    have hsqL : (21.90:ℝ) ≤ Real.sqrt (((26:ℕ):ℝ) ^ 2 - (14:ℝ) ^ 2) :=
      (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
    have htlo : (4.67:ℝ)
        ≤ Real.sqrt (Real.sqrt (((26:ℕ):ℝ) ^ 2 - (14:ℝ) ^ 2)) := by
      have htlo2 : (4.67:ℝ) ^ 2
          ≤ Real.sqrt (((26:ℕ):ℝ) ^ 2 - (14:ℝ) ^ 2) :=
        le_trans (by norm_num) hsqL
      exact (Real.le_sqrt (by norm_num) (Real.sqrt_nonneg _)).mpr htlo2
    have hC := nrCcal_tight_le_of (show (2 : ℝ) ≤ ((26:ℕ):ℝ) by norm_num)
      (show (0 : ℝ) < (14:ℝ) by norm_num)
      (show (14:ℝ) < ((26:ℕ):ℝ) by norm_num)
      he1 (show (0 : ℝ) ≤ ((25515/6859):ℝ) by norm_num)
      he2 (show (0 : ℝ) ≤ ((75345795/2476099):ℝ) by norm_num)
      (show 2 * (1 + 1 / ((26:ℕ):ℝ) ^ 2) * (1 + (4 / 27) * ((25515/6859):ℝ))
        * ((13 / 5) * ((75345795/2476099):ℝ) * ((26:ℕ):ℝ) ^ 2 + 44 + 2 * (12 + 16 / 27) * ((25515/6859):ℝ))
        ≤ (408.17:ℝ) ^ 2 by norm_num)
      (show (0 : ℝ) ≤ (408.17:ℝ) by norm_num)
    have hF : ((9:ℕ):ℝ) ≤ besselF (14:ℝ) ((26:ℕ):ℝ) := by
      have hq : ((26:ℕ):ℝ) = (26:ℝ) := by norm_num
      have hk : ((9:ℕ):ℝ) = (9:ℝ) := by norm_num
      rw [hq, hk]
      unfold besselF besselAlpha
      have g1 : (3*1.0986122885-3*0.6931471808:ℝ) ≤ Real.arcosh ((26:ℝ) / (14:ℝ)) := by
        rw [← hq]
        exact hα
      have g2 : Real.sqrt ((26:ℝ) ^ 2 - (14:ℝ) ^ 2) ≤ (21.91:ℝ) := by
        rw [← hq]
        exact hsqU
      have hmul : (26:ℝ) * (3*1.0986122885-3*0.6931471808:ℝ)
          ≤ (26:ℝ) * Real.arcosh ((26:ℝ) / (14:ℝ)) :=
        mul_le_mul_of_nonneg_left g1 (by norm_num)
      have key : (9:ℝ) ≤ (26:ℝ) * (3*1.0986122885-3*0.6931471808:ℝ) - (21.91:ℝ) := by norm_num
      calc (9:ℝ) ≤ (26:ℝ) * (3*1.0986122885-3*0.6931471808:ℝ) - (21.91:ℝ) := key
        _ ≤ (26:ℝ) * Real.arcosh ((26:ℝ) / (14:ℝ))
            - Real.sqrt ((26:ℝ) ^ 2 - (14:ℝ) ^ 2) :=
          sub_le_sub hmul g2
    have hEpow : (8103:ℝ) ≤ (2.7182818283 : ℝ) ^ 9 := by norm_num
    have hexp : Real.exp (-(besselF (14:ℝ) ((26:ℕ):ℝ))) ≤ 1 / (8103:ℝ) :=
      nr_exp_neg_le hF hEpow (by norm_num)
    have hE := nrE2star_le_of hexp (show (0 : ℝ) ≤ 1 / (8103:ℝ) by norm_num)
      htlo (show (0 : ℝ) < (4.67:ℝ) by norm_num)
      hr (show ((8/27):ℝ) < 1 by norm_num)
      two_sqrt_pi_div_8_le (show (0 : ℝ) ≤ (1.26 : ℝ) by norm_num)
    have hC0nn : (0 : ℝ) ≤ (0.6367 : ℝ) * (1 / ((26:ℕ):ℝ)) * (408.17:ℝ) := by
      have h1 : (0 : ℝ) ≤ (0.6367 : ℝ) * (1 / ((26:ℕ):ℝ)) :=
        mul_nonneg (by norm_num)
          (le_of_lt (one_div_pos.mpr (by norm_num)))
      exact mul_nonneg h1 (by norm_num)
    have hQnn : (0 : ℝ)
        ≤ ((0.6367 : ℝ) * (1 / ((26:ℕ):ℝ)) * (408.17:ℝ)) * (((26:ℕ):ℝ)) ^ 2 :=
      mul_nonneg hC0nn (sq_nonneg _)
    have hαnn : (0 : ℝ) ≤ besselAlpha (14:ℝ) (((26:ℕ):ℝ)) := by
      rw [hba]
      exact le_trans (show (0:ℝ) ≤ (3*1.0986122885-3*0.6931471808:ℝ) by norm_num) hα
    have hEnn : (0 : ℝ) ≤ nrE2star (14:ℝ) 26 := nrE2star_nonneg hαnn
    have hfin : ((0.6367 : ℝ) * (1 / ((26:ℕ):ℝ)) * (408.17:ℝ)) * (((26:ℕ):ℝ)) ^ 2
        * ((1.26 : ℝ) * (1 / (8103:ℝ)) / ((4.67:ℝ) * (1 - ((8/27):ℝ)))) < 1 / 2 := by
      norm_num
    exact nr_tight_criterion hC hE hQnn hEnn hfin
  have hcost := new_rung_final_tight (hN := by norm_num) (hφ0 := Real.pi_pos)
    (hφπ := le_rfl) (hAdm := hAdm) (τ := (14 : ℝ)) (hτ1 := by norm_num)
    (hlt := by norm_num) hmain
  calc (28:ℝ) = 2 * (14:ℝ) := by norm_num
    _ ≤ cost θ := le_of_lt hcost


/-- Certified tight number at `N = 11` (`φ = π`): `cost θ ≥ 24`, via the tight criterion
at `τ = 12`, `q = 24` (criterion value `≈ 0.24 < 1/2`). -/
theorem cert_N11_tight {L : ℕ} {α θ : Fin L → ℝ}
    (hAdm : Admissible 11 Real.pi L α θ) : 24 ≤ cost θ := by
  have hmain : nrCcal_tight (12:ℝ) 24 * (((24:ℕ):ℝ)) ^ 2
      * nrE2star (12:ℝ) 24 < Real.sin (Real.pi / 4) ^ 2 := by
    rw [sin_pi_div_four_sq]
    have hx1 : (1 : ℝ) < ((24:ℕ):ℝ) / (12:ℝ) := by norm_num
    have hs1 : (1.73:ℝ) ^ 2 ≤ (((24:ℕ):ℝ) / (12:ℝ)) ^ 2 - 1 := by norm_num
    have hsq1 : (1.73:ℝ)
        ≤ Real.sqrt ((((24:ℕ):ℝ) / (12:ℝ)) ^ 2 - 1) :=
      (Real.le_sqrt (by norm_num) (by norm_num)).mpr hs1
    have hy : (18/5:ℝ) ≤ ((24:ℕ):ℝ) / (12:ℝ)
        + Real.sqrt ((((24:ℕ):ℝ) / (12:ℝ)) ^ 2 - 1) :=
      le_trans (show (18/5:ℝ) ≤ ((24:ℕ):ℝ) / (12:ℝ) + (1.73:ℝ) by norm_num)
        (add_le_add (le_refl _) hsq1)
    have hlog : Real.log ((18/5):ℝ) = Real.log 2 + 2*Real.log 3 - Real.log 5 := by
      rw [show ((18/5):ℝ) = (2*3^2)/5 from by norm_num,
        Real.log_div (by norm_num) (by norm_num),
        Real.log_mul (by norm_num) (by norm_num),
        Real.log_pow]
      push_cast; ring
    have ha : Real.log ((18/5):ℝ) ≤ Real.arcosh (((24:ℕ):ℝ) / (12:ℝ)) :=
      log_le_arcosh hx1 (show (0 : ℝ) < ((18/5):ℝ) by norm_num) hy
    have hα : (0.6931471803+2*1.0986122885-1.6094379126:ℝ) ≤ Real.arcosh (((24:ℕ):ℝ) / (12:ℝ)) :=
      calc (0.6931471803+2*1.0986122885-1.6094379126:ℝ) ≤ Real.log 2 + 2*Real.log 3 - Real.log 5 :=
            sub_le_sub (add_le_add Real.log_two_gt_d9.le (mul_le_mul_of_nonneg_left Real.log_three_gt_d9.le (by norm_num))) Real.log_five_lt_d9.le
        _ = Real.log ((18/5):ℝ) := hlog.symm
        _ ≤ Real.arcosh (((24:ℕ):ℝ) / (12:ℝ)) := ha
    have hba : besselAlpha (12:ℝ) ((24:ℕ):ℝ)
        = Real.arcosh (((24:ℕ):ℝ) / (12:ℝ)) := rfl
    have hr : nrR (12:ℝ) 24 ≤ ((5/18):ℝ) := by
      have e := exp_neg_arcosh_le_inv hx1 (show (0 : ℝ) < ((18/5):ℝ) by norm_num) hy
      unfold nrR
      rw [hba]
      have e2 : (1 : ℝ) / ((18/5):ℝ) = ((5/18):ℝ) := by norm_num
      rw [← e2]
      exact e
    have he1 : nrEta1of (12:ℝ) 24 ≤ ((7452/2197):ℝ) := by
      have hmono := nrEta1_mono (nrR_nonneg _ _) hr (by norm_num)
      have e : nrEta1 ((5/18):ℝ) = ((7452/2197):ℝ) := by unfold nrEta1; norm_num
      show nrEta1 (nrR (12:ℝ) 24) ≤ _
      calc nrEta1 (nrR (12:ℝ) 24) ≤ nrEta1 ((5/18):ℝ) := hmono
        _ = ((7452/2197):ℝ) := e
    have he2 : nrEta2of (12:ℝ) 24 ≤ ((9307548/371293):ℝ) := by
      have hmono := nrEta2_mono (nrR_nonneg _ _) hr (by norm_num)
      have e : nrEta2 ((5/18):ℝ) = ((9307548/371293):ℝ) := by unfold nrEta2; norm_num
      show nrEta2 (nrR (12:ℝ) 24) ≤ _
      calc nrEta2 (nrR (12:ℝ) 24) ≤ nrEta2 ((5/18):ℝ) := hmono
        _ = ((9307548/371293):ℝ) := e
    have hsqU : Real.sqrt (((24:ℕ):ℝ) ^ 2 - (12:ℝ) ^ 2) ≤ (20.79:ℝ) := by
      rw [Real.sqrt_le_iff]
      refine ⟨by norm_num, by norm_num⟩
    have hsqL : (20.78:ℝ) ≤ Real.sqrt (((24:ℕ):ℝ) ^ 2 - (12:ℝ) ^ 2) :=
      (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
    have htlo : (4.55:ℝ)
        ≤ Real.sqrt (Real.sqrt (((24:ℕ):ℝ) ^ 2 - (12:ℝ) ^ 2)) := by
      have htlo2 : (4.55:ℝ) ^ 2
          ≤ Real.sqrt (((24:ℕ):ℝ) ^ 2 - (12:ℝ) ^ 2) :=
        le_trans (by norm_num) hsqL
      exact (Real.le_sqrt (by norm_num) (Real.sqrt_nonneg _)).mpr htlo2
    have hC := nrCcal_tight_le_of (show (2 : ℝ) ≤ ((24:ℕ):ℝ) by norm_num)
      (show (0 : ℝ) < (12:ℝ) by norm_num)
      (show (12:ℝ) < ((24:ℕ):ℝ) by norm_num)
      he1 (show (0 : ℝ) ≤ ((7452/2197):ℝ) by norm_num)
      he2 (show (0 : ℝ) ≤ ((9307548/371293):ℝ) by norm_num)
      (show 2 * (1 + 1 / ((24:ℕ):ℝ) ^ 2) * (1 + (4 / 27) * ((7452/2197):ℝ))
        * ((13 / 5) * ((9307548/371293):ℝ) * ((24:ℕ):ℝ) ^ 2 + 44 + 2 * (12 + 16 / 27) * ((7452/2197):ℝ))
        ≤ (336.76:ℝ) ^ 2 by norm_num)
      (show (0 : ℝ) ≤ (336.76:ℝ) by norm_num)
    have hF : ((9:ℕ):ℝ) ≤ besselF (12:ℝ) ((24:ℕ):ℝ) := by
      have hq : ((24:ℕ):ℝ) = (24:ℝ) := by norm_num
      have hk : ((9:ℕ):ℝ) = (9:ℝ) := by norm_num
      rw [hq, hk]
      unfold besselF besselAlpha
      have g1 : (0.6931471803+2*1.0986122885-1.6094379126:ℝ) ≤ Real.arcosh ((24:ℝ) / (12:ℝ)) := by
        rw [← hq]
        exact hα
      have g2 : Real.sqrt ((24:ℝ) ^ 2 - (12:ℝ) ^ 2) ≤ (20.79:ℝ) := by
        rw [← hq]
        exact hsqU
      have hmul : (24:ℝ) * (0.6931471803+2*1.0986122885-1.6094379126:ℝ)
          ≤ (24:ℝ) * Real.arcosh ((24:ℝ) / (12:ℝ)) :=
        mul_le_mul_of_nonneg_left g1 (by norm_num)
      have key : (9:ℝ) ≤ (24:ℝ) * (0.6931471803+2*1.0986122885-1.6094379126:ℝ) - (20.79:ℝ) := by norm_num
      calc (9:ℝ) ≤ (24:ℝ) * (0.6931471803+2*1.0986122885-1.6094379126:ℝ) - (20.79:ℝ) := key
        _ ≤ (24:ℝ) * Real.arcosh ((24:ℝ) / (12:ℝ))
            - Real.sqrt ((24:ℝ) ^ 2 - (12:ℝ) ^ 2) :=
          sub_le_sub hmul g2
    have hEpow : (8103:ℝ) ≤ (2.7182818283 : ℝ) ^ 9 := by norm_num
    have hexp : Real.exp (-(besselF (12:ℝ) ((24:ℕ):ℝ))) ≤ 1 / (8103:ℝ) :=
      nr_exp_neg_le hF hEpow (by norm_num)
    have hE := nrE2star_le_of hexp (show (0 : ℝ) ≤ 1 / (8103:ℝ) by norm_num)
      htlo (show (0 : ℝ) < (4.55:ℝ) by norm_num)
      hr (show ((5/18):ℝ) < 1 by norm_num)
      two_sqrt_pi_div_8_le (show (0 : ℝ) ≤ (1.26 : ℝ) by norm_num)
    have hC0nn : (0 : ℝ) ≤ (0.6367 : ℝ) * (1 / ((24:ℕ):ℝ)) * (336.76:ℝ) := by
      have h1 : (0 : ℝ) ≤ (0.6367 : ℝ) * (1 / ((24:ℕ):ℝ)) :=
        mul_nonneg (by norm_num)
          (le_of_lt (one_div_pos.mpr (by norm_num)))
      exact mul_nonneg h1 (by norm_num)
    have hQnn : (0 : ℝ)
        ≤ ((0.6367 : ℝ) * (1 / ((24:ℕ):ℝ)) * (336.76:ℝ)) * (((24:ℕ):ℝ)) ^ 2 :=
      mul_nonneg hC0nn (sq_nonneg _)
    have hαnn : (0 : ℝ) ≤ besselAlpha (12:ℝ) (((24:ℕ):ℝ)) := by
      rw [hba]
      exact le_trans (show (0:ℝ) ≤ (0.6931471803+2*1.0986122885-1.6094379126:ℝ) by norm_num) hα
    have hEnn : (0 : ℝ) ≤ nrE2star (12:ℝ) 24 := nrE2star_nonneg hαnn
    have hfin : ((0.6367 : ℝ) * (1 / ((24:ℕ):ℝ)) * (336.76:ℝ)) * (((24:ℕ):ℝ)) ^ 2
        * ((1.26 : ℝ) * (1 / (8103:ℝ)) / ((4.55:ℝ) * (1 - ((5/18):ℝ)))) < 1 / 2 := by
      norm_num
    exact nr_tight_criterion hC hE hQnn hEnn hfin
  have hcost := new_rung_final_tight (hN := by norm_num) (hφ0 := Real.pi_pos)
    (hφπ := le_rfl) (hAdm := hAdm) (τ := (12 : ℝ)) (hτ1 := by norm_num)
    (hlt := by norm_num) hmain
  calc (24:ℝ) = 2 * (12:ℝ) := by norm_num
    _ ≤ cost θ := le_of_lt hcost


/-- Certified tight number at `N = 10` (`φ = π`): `cost θ ≥ 22`, via the tight criterion
at `τ = 11`, `q = 22` (criterion value `≈ 0.21 < 1/2`). -/
theorem cert_N10_tight {L : ℕ} {α θ : Fin L → ℝ}
    (hAdm : Admissible 10 Real.pi L α θ) : 22 ≤ cost θ := by
  have hmain : nrCcal_tight (11:ℝ) 22 * (((22:ℕ):ℝ)) ^ 2
      * nrE2star (11:ℝ) 22 < Real.sin (Real.pi / 4) ^ 2 := by
    rw [sin_pi_div_four_sq]
    have hx1 : (1 : ℝ) < ((22:ℕ):ℝ) / (11:ℝ) := by norm_num
    have hs1 : (1.73:ℝ) ^ 2 ≤ (((22:ℕ):ℝ) / (11:ℝ)) ^ 2 - 1 := by norm_num
    have hsq1 : (1.73:ℝ)
        ≤ Real.sqrt ((((22:ℕ):ℝ) / (11:ℝ)) ^ 2 - 1) :=
      (Real.le_sqrt (by norm_num) (by norm_num)).mpr hs1
    have hy : (18/5:ℝ) ≤ ((22:ℕ):ℝ) / (11:ℝ)
        + Real.sqrt ((((22:ℕ):ℝ) / (11:ℝ)) ^ 2 - 1) :=
      le_trans (show (18/5:ℝ) ≤ ((22:ℕ):ℝ) / (11:ℝ) + (1.73:ℝ) by norm_num)
        (add_le_add (le_refl _) hsq1)
    have hlog : Real.log ((18/5):ℝ) = Real.log 2 + 2*Real.log 3 - Real.log 5 := by
      rw [show ((18/5):ℝ) = (2*3^2)/5 from by norm_num,
        Real.log_div (by norm_num) (by norm_num),
        Real.log_mul (by norm_num) (by norm_num),
        Real.log_pow]
      push_cast; ring
    have ha : Real.log ((18/5):ℝ) ≤ Real.arcosh (((22:ℕ):ℝ) / (11:ℝ)) :=
      log_le_arcosh hx1 (show (0 : ℝ) < ((18/5):ℝ) by norm_num) hy
    have hα : (0.6931471803+2*1.0986122885-1.6094379126:ℝ) ≤ Real.arcosh (((22:ℕ):ℝ) / (11:ℝ)) :=
      calc (0.6931471803+2*1.0986122885-1.6094379126:ℝ) ≤ Real.log 2 + 2*Real.log 3 - Real.log 5 :=
            sub_le_sub (add_le_add Real.log_two_gt_d9.le (mul_le_mul_of_nonneg_left Real.log_three_gt_d9.le (by norm_num))) Real.log_five_lt_d9.le
        _ = Real.log ((18/5):ℝ) := hlog.symm
        _ ≤ Real.arcosh (((22:ℕ):ℝ) / (11:ℝ)) := ha
    have hba : besselAlpha (11:ℝ) ((22:ℕ):ℝ)
        = Real.arcosh (((22:ℕ):ℝ) / (11:ℝ)) := rfl
    have hr : nrR (11:ℝ) 22 ≤ ((5/18):ℝ) := by
      have e := exp_neg_arcosh_le_inv hx1 (show (0 : ℝ) < ((18/5):ℝ) by norm_num) hy
      unfold nrR
      rw [hba]
      have e2 : (1 : ℝ) / ((18/5):ℝ) = ((5/18):ℝ) := by norm_num
      rw [← e2]
      exact e
    have he1 : nrEta1of (11:ℝ) 22 ≤ ((7452/2197):ℝ) := by
      have hmono := nrEta1_mono (nrR_nonneg _ _) hr (by norm_num)
      have e : nrEta1 ((5/18):ℝ) = ((7452/2197):ℝ) := by unfold nrEta1; norm_num
      show nrEta1 (nrR (11:ℝ) 22) ≤ _
      calc nrEta1 (nrR (11:ℝ) 22) ≤ nrEta1 ((5/18):ℝ) := hmono
        _ = ((7452/2197):ℝ) := e
    have he2 : nrEta2of (11:ℝ) 22 ≤ ((9307548/371293):ℝ) := by
      have hmono := nrEta2_mono (nrR_nonneg _ _) hr (by norm_num)
      have e : nrEta2 ((5/18):ℝ) = ((9307548/371293):ℝ) := by unfold nrEta2; norm_num
      show nrEta2 (nrR (11:ℝ) 22) ≤ _
      calc nrEta2 (nrR (11:ℝ) 22) ≤ nrEta2 ((5/18):ℝ) := hmono
        _ = ((9307548/371293):ℝ) := e
    have hsqU : Real.sqrt (((22:ℕ):ℝ) ^ 2 - (11:ℝ) ^ 2) ≤ (19.06:ℝ) := by
      rw [Real.sqrt_le_iff]
      refine ⟨by norm_num, by norm_num⟩
    have hsqL : (19.05:ℝ) ≤ Real.sqrt (((22:ℕ):ℝ) ^ 2 - (11:ℝ) ^ 2) :=
      (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
    have htlo : (4.36:ℝ)
        ≤ Real.sqrt (Real.sqrt (((22:ℕ):ℝ) ^ 2 - (11:ℝ) ^ 2)) := by
      have htlo2 : (4.36:ℝ) ^ 2
          ≤ Real.sqrt (((22:ℕ):ℝ) ^ 2 - (11:ℝ) ^ 2) :=
        le_trans (by norm_num) hsqL
      exact (Real.le_sqrt (by norm_num) (Real.sqrt_nonneg _)).mpr htlo2
    have hC := nrCcal_tight_le_of (show (2 : ℝ) ≤ ((22:ℕ):ℝ) by norm_num)
      (show (0 : ℝ) < (11:ℝ) by norm_num)
      (show (11:ℝ) < ((22:ℕ):ℝ) by norm_num)
      he1 (show (0 : ℝ) ≤ ((7452/2197):ℝ) by norm_num)
      he2 (show (0 : ℝ) ≤ ((9307548/371293):ℝ) by norm_num)
      (show 2 * (1 + 1 / ((22:ℕ):ℝ) ^ 2) * (1 + (4 / 27) * ((7452/2197):ℝ))
        * ((13 / 5) * ((9307548/371293):ℝ) * ((22:ℕ):ℝ) ^ 2 + 44 + 2 * (12 + 16 / 27) * ((7452/2197):ℝ))
        ≤ (308.85:ℝ) ^ 2 by norm_num)
      (show (0 : ℝ) ≤ (308.85:ℝ) by norm_num)
    have hF : ((9:ℕ):ℝ) ≤ besselF (11:ℝ) ((22:ℕ):ℝ) := by
      have hq : ((22:ℕ):ℝ) = (22:ℝ) := by norm_num
      have hk : ((9:ℕ):ℝ) = (9:ℝ) := by norm_num
      rw [hq, hk]
      unfold besselF besselAlpha
      have g1 : (0.6931471803+2*1.0986122885-1.6094379126:ℝ) ≤ Real.arcosh ((22:ℝ) / (11:ℝ)) := by
        rw [← hq]
        exact hα
      have g2 : Real.sqrt ((22:ℝ) ^ 2 - (11:ℝ) ^ 2) ≤ (19.06:ℝ) := by
        rw [← hq]
        exact hsqU
      have hmul : (22:ℝ) * (0.6931471803+2*1.0986122885-1.6094379126:ℝ)
          ≤ (22:ℝ) * Real.arcosh ((22:ℝ) / (11:ℝ)) :=
        mul_le_mul_of_nonneg_left g1 (by norm_num)
      have key : (9:ℝ) ≤ (22:ℝ) * (0.6931471803+2*1.0986122885-1.6094379126:ℝ) - (19.06:ℝ) := by norm_num
      calc (9:ℝ) ≤ (22:ℝ) * (0.6931471803+2*1.0986122885-1.6094379126:ℝ) - (19.06:ℝ) := key
        _ ≤ (22:ℝ) * Real.arcosh ((22:ℝ) / (11:ℝ))
            - Real.sqrt ((22:ℝ) ^ 2 - (11:ℝ) ^ 2) :=
          sub_le_sub hmul g2
    have hEpow : (8103:ℝ) ≤ (2.7182818283 : ℝ) ^ 9 := by norm_num
    have hexp : Real.exp (-(besselF (11:ℝ) ((22:ℕ):ℝ))) ≤ 1 / (8103:ℝ) :=
      nr_exp_neg_le hF hEpow (by norm_num)
    have hE := nrE2star_le_of hexp (show (0 : ℝ) ≤ 1 / (8103:ℝ) by norm_num)
      htlo (show (0 : ℝ) < (4.36:ℝ) by norm_num)
      hr (show ((5/18):ℝ) < 1 by norm_num)
      two_sqrt_pi_div_8_le (show (0 : ℝ) ≤ (1.26 : ℝ) by norm_num)
    have hC0nn : (0 : ℝ) ≤ (0.6367 : ℝ) * (1 / ((22:ℕ):ℝ)) * (308.85:ℝ) := by
      have h1 : (0 : ℝ) ≤ (0.6367 : ℝ) * (1 / ((22:ℕ):ℝ)) :=
        mul_nonneg (by norm_num)
          (le_of_lt (one_div_pos.mpr (by norm_num)))
      exact mul_nonneg h1 (by norm_num)
    have hQnn : (0 : ℝ)
        ≤ ((0.6367 : ℝ) * (1 / ((22:ℕ):ℝ)) * (308.85:ℝ)) * (((22:ℕ):ℝ)) ^ 2 :=
      mul_nonneg hC0nn (sq_nonneg _)
    have hαnn : (0 : ℝ) ≤ besselAlpha (11:ℝ) (((22:ℕ):ℝ)) := by
      rw [hba]
      exact le_trans (show (0:ℝ) ≤ (0.6931471803+2*1.0986122885-1.6094379126:ℝ) by norm_num) hα
    have hEnn : (0 : ℝ) ≤ nrE2star (11:ℝ) 22 := nrE2star_nonneg hαnn
    have hfin : ((0.6367 : ℝ) * (1 / ((22:ℕ):ℝ)) * (308.85:ℝ)) * (((22:ℕ):ℝ)) ^ 2
        * ((1.26 : ℝ) * (1 / (8103:ℝ)) / ((4.36:ℝ) * (1 - ((5/18):ℝ)))) < 1 / 2 := by
      norm_num
    exact nr_tight_criterion hC hE hQnn hEnn hfin
  have hcost := new_rung_final_tight (hN := by norm_num) (hφ0 := Real.pi_pos)
    (hφπ := le_rfl) (hAdm := hAdm) (τ := (11 : ℝ)) (hτ1 := by norm_num)
    (hlt := by norm_num) hmain
  calc (22:ℝ) = 2 * (11:ℝ) := by norm_num
    _ ≤ cost θ := le_of_lt hcost


/-- Certified tight number at `N = 9` (`φ = π`): `cost θ ≥ 18`, via the tight criterion
at `τ = 9`, `q = 20` (criterion value `≈ 0.05 < 1/2`). -/
theorem cert_N9_tight {L : ℕ} {α θ : Fin L → ℝ}
    (hAdm : Admissible 9 Real.pi L α θ) : 18 ≤ cost θ := by
  have hmain : nrCcal_tight (9:ℝ) 20 * (((20:ℕ):ℝ)) ^ 2
      * nrE2star (9:ℝ) 20 < Real.sin (Real.pi / 4) ^ 2 := by
    rw [sin_pi_div_four_sq]
    have hx1 : (1 : ℝ) < ((20:ℕ):ℝ) / (9:ℝ) := by norm_num
    have hs1 : (1.98:ℝ) ^ 2 ≤ (((20:ℕ):ℝ) / (9:ℝ)) ^ 2 - 1 := by norm_num
    have hsq1 : (1.98:ℝ)
        ≤ Real.sqrt ((((20:ℕ):ℝ) / (9:ℝ)) ^ 2 - 1) :=
      (Real.le_sqrt (by norm_num) (by norm_num)).mpr hs1
    have hy : (81/20:ℝ) ≤ ((20:ℕ):ℝ) / (9:ℝ)
        + Real.sqrt ((((20:ℕ):ℝ) / (9:ℝ)) ^ 2 - 1) :=
      le_trans (show (81/20:ℝ) ≤ ((20:ℕ):ℝ) / (9:ℝ) + (1.98:ℝ) by norm_num)
        (add_le_add (le_refl _) hsq1)
    have hlog : Real.log ((81/20):ℝ) = 4*Real.log 3 - (2*Real.log 2 + Real.log 5) := by
      rw [show ((81/20):ℝ) = (3^4)/(2^2*5) from by norm_num,
        Real.log_div (by norm_num) (by norm_num),
        Real.log_pow,
        Real.log_mul (by norm_num) (by norm_num),
        Real.log_pow]
      push_cast; ring
    have ha : Real.log ((81/20):ℝ) ≤ Real.arcosh (((20:ℕ):ℝ) / (9:ℝ)) :=
      log_le_arcosh hx1 (show (0 : ℝ) < ((81/20):ℝ) by norm_num) hy
    have hα : (4*1.0986122885-(2*0.6931471808+1.6094379126):ℝ) ≤ Real.arcosh (((20:ℕ):ℝ) / (9:ℝ)) :=
      calc (4*1.0986122885-(2*0.6931471808+1.6094379126):ℝ) ≤ 4*Real.log 3 - (2*Real.log 2 + Real.log 5) :=
            sub_le_sub (mul_le_mul_of_nonneg_left Real.log_three_gt_d9.le (by norm_num)) (add_le_add (mul_le_mul_of_nonneg_left Real.log_two_lt_d9.le (by norm_num)) Real.log_five_lt_d9.le)
        _ = Real.log ((81/20):ℝ) := hlog.symm
        _ ≤ Real.arcosh (((20:ℕ):ℝ) / (9:ℝ)) := ha
    have hba : besselAlpha (9:ℝ) ((20:ℕ):ℝ)
        = Real.arcosh (((20:ℕ):ℝ) / (9:ℝ)) := rfl
    have hr : nrR (9:ℝ) 20 ≤ ((20/81):ℝ) := by
      have e := exp_neg_arcosh_le_inv hx1 (show (0 : ℝ) < ((81/20):ℝ) by norm_num) hy
      unfold nrR
      rw [hba]
      have e2 : (1 : ℝ) / ((81/20):ℝ) = ((20/81):ℝ) := by norm_num
      rw [← e2]
      exact e
    have he1 : nrEta1of (9:ℝ) 20 ≤ ((662661/226981):ℝ) := by
      have hmono := nrEta1_mono (nrR_nonneg _ _) hr (by norm_num)
      have e : nrEta1 ((20/81):ℝ) = ((662661/226981):ℝ) := by unfold nrEta1; norm_num
      show nrEta1 (nrR (9:ℝ) 20) ≤ _
      calc nrEta1 (nrR (9:ℝ) 20) ≤ nrEta1 ((20/81):ℝ) := hmono
        _ = ((662661/226981):ℝ) := e
    have he2 : nrEta2of (9:ℝ) 20 ≤ ((15347891421/844596301):ℝ) := by
      have hmono := nrEta2_mono (nrR_nonneg _ _) hr (by norm_num)
      have e : nrEta2 ((20/81):ℝ) = ((15347891421/844596301):ℝ) := by unfold nrEta2; norm_num
      show nrEta2 (nrR (9:ℝ) 20) ≤ _
      calc nrEta2 (nrR (9:ℝ) 20) ≤ nrEta2 ((20/81):ℝ) := hmono
        _ = ((15347891421/844596301):ℝ) := e
    have hsqU : Real.sqrt (((20:ℕ):ℝ) ^ 2 - (9:ℝ) ^ 2) ≤ (17.87:ℝ) := by
      rw [Real.sqrt_le_iff]
      refine ⟨by norm_num, by norm_num⟩
    have hsqL : (17.86:ℝ) ≤ Real.sqrt (((20:ℕ):ℝ) ^ 2 - (9:ℝ) ^ 2) :=
      (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
    have htlo : (4.22:ℝ)
        ≤ Real.sqrt (Real.sqrt (((20:ℕ):ℝ) ^ 2 - (9:ℝ) ^ 2)) := by
      have htlo2 : (4.22:ℝ) ^ 2
          ≤ Real.sqrt (((20:ℕ):ℝ) ^ 2 - (9:ℝ) ^ 2) :=
        le_trans (by norm_num) hsqL
      exact (Real.le_sqrt (by norm_num) (Real.sqrt_nonneg _)).mpr htlo2
    have hC := nrCcal_tight_le_of (show (2 : ℝ) ≤ ((20:ℕ):ℝ) by norm_num)
      (show (0 : ℝ) < (9:ℝ) by norm_num)
      (show (9:ℝ) < ((20:ℕ):ℝ) by norm_num)
      he1 (show (0 : ℝ) ≤ ((662661/226981):ℝ) by norm_num)
      he2 (show (0 : ℝ) ≤ ((15347891421/844596301):ℝ) by norm_num)
      (show 2 * (1 + 1 / ((20:ℕ):ℝ) ^ 2) * (1 + (4 / 27) * ((662661/226981):ℝ))
        * ((13 / 5) * ((15347891421/844596301):ℝ) * ((20:ℕ):ℝ) ^ 2 + 44 + 2 * (12 + 16 / 27) * ((662661/226981):ℝ))
        ≤ (233.72:ℝ) ^ 2 by norm_num)
      (show (0 : ℝ) ≤ (233.72:ℝ) by norm_num)
    have hF : ((10:ℕ):ℝ) ≤ besselF (9:ℝ) ((20:ℕ):ℝ) := by
      have hq : ((20:ℕ):ℝ) = (20:ℝ) := by norm_num
      have hk : ((10:ℕ):ℝ) = (10:ℝ) := by norm_num
      rw [hq, hk]
      unfold besselF besselAlpha
      have g1 : (4*1.0986122885-(2*0.6931471808+1.6094379126):ℝ) ≤ Real.arcosh ((20:ℝ) / (9:ℝ)) := by
        rw [← hq]
        exact hα
      have g2 : Real.sqrt ((20:ℝ) ^ 2 - (9:ℝ) ^ 2) ≤ (17.87:ℝ) := by
        rw [← hq]
        exact hsqU
      have hmul : (20:ℝ) * (4*1.0986122885-(2*0.6931471808+1.6094379126):ℝ)
          ≤ (20:ℝ) * Real.arcosh ((20:ℝ) / (9:ℝ)) :=
        mul_le_mul_of_nonneg_left g1 (by norm_num)
      have key : (10:ℝ) ≤ (20:ℝ) * (4*1.0986122885-(2*0.6931471808+1.6094379126):ℝ) - (17.87:ℝ) := by norm_num
      calc (10:ℝ) ≤ (20:ℝ) * (4*1.0986122885-(2*0.6931471808+1.6094379126):ℝ) - (17.87:ℝ) := key
        _ ≤ (20:ℝ) * Real.arcosh ((20:ℝ) / (9:ℝ))
            - Real.sqrt ((20:ℝ) ^ 2 - (9:ℝ) ^ 2) :=
          sub_le_sub hmul g2
    have hEpow : (22026:ℝ) ≤ (2.7182818283 : ℝ) ^ 10 := by norm_num
    have hexp : Real.exp (-(besselF (9:ℝ) ((20:ℕ):ℝ))) ≤ 1 / (22026:ℝ) :=
      nr_exp_neg_le hF hEpow (by norm_num)
    have hE := nrE2star_le_of hexp (show (0 : ℝ) ≤ 1 / (22026:ℝ) by norm_num)
      htlo (show (0 : ℝ) < (4.22:ℝ) by norm_num)
      hr (show ((20/81):ℝ) < 1 by norm_num)
      two_sqrt_pi_div_8_le (show (0 : ℝ) ≤ (1.26 : ℝ) by norm_num)
    have hC0nn : (0 : ℝ) ≤ (0.6367 : ℝ) * (1 / ((20:ℕ):ℝ)) * (233.72:ℝ) := by
      have h1 : (0 : ℝ) ≤ (0.6367 : ℝ) * (1 / ((20:ℕ):ℝ)) :=
        mul_nonneg (by norm_num)
          (le_of_lt (one_div_pos.mpr (by norm_num)))
      exact mul_nonneg h1 (by norm_num)
    have hQnn : (0 : ℝ)
        ≤ ((0.6367 : ℝ) * (1 / ((20:ℕ):ℝ)) * (233.72:ℝ)) * (((20:ℕ):ℝ)) ^ 2 :=
      mul_nonneg hC0nn (sq_nonneg _)
    have hαnn : (0 : ℝ) ≤ besselAlpha (9:ℝ) (((20:ℕ):ℝ)) := by
      rw [hba]
      exact le_trans (show (0:ℝ) ≤ (4*1.0986122885-(2*0.6931471808+1.6094379126):ℝ) by norm_num) hα
    have hEnn : (0 : ℝ) ≤ nrE2star (9:ℝ) 20 := nrE2star_nonneg hαnn
    have hfin : ((0.6367 : ℝ) * (1 / ((20:ℕ):ℝ)) * (233.72:ℝ)) * (((20:ℕ):ℝ)) ^ 2
        * ((1.26 : ℝ) * (1 / (22026:ℝ)) / ((4.22:ℝ) * (1 - ((20/81):ℝ)))) < 1 / 2 := by
      norm_num
    exact nr_tight_criterion hC hE hQnn hEnn hfin
  have hcost := new_rung_final_tight (hN := by norm_num) (hφ0 := Real.pi_pos)
    (hφπ := le_rfl) (hAdm := hAdm) (τ := (9 : ℝ)) (hτ1 := by norm_num)
    (hlt := by norm_num) hmain
  calc (18:ℝ) = 2 * (9:ℝ) := by norm_num
    _ ≤ cost θ := le_of_lt hcost


/-- Certified tight number at `N = 8` (`φ = π`): `cost θ ≥ 16`, via the tight criterion
at `τ = 8`, `q = 18` (criterion value `≈ 0.12 < 1/2`). -/
theorem cert_N8_tight {L : ℕ} {α θ : Fin L → ℝ}
    (hAdm : Admissible 8 Real.pi L α θ) : 16 ≤ cost θ := by
  have hmain : nrCcal_tight (8:ℝ) 18 * (((18:ℕ):ℝ)) ^ 2
      * nrE2star (8:ℝ) 18 < Real.sin (Real.pi / 4) ^ 2 := by
    rw [sin_pi_div_four_sq]
    have hx1 : (1 : ℝ) < ((18:ℕ):ℝ) / (8:ℝ) := by norm_num
    have hs1 : (2.0:ℝ) ^ 2 ≤ (((18:ℕ):ℝ) / (8:ℝ)) ^ 2 - 1 := by norm_num
    have hsq1 : (2.0:ℝ)
        ≤ Real.sqrt ((((18:ℕ):ℝ) / (8:ℝ)) ^ 2 - 1) :=
      (Real.le_sqrt (by norm_num) (by norm_num)).mpr hs1
    have hy : (25/6:ℝ) ≤ ((18:ℕ):ℝ) / (8:ℝ)
        + Real.sqrt ((((18:ℕ):ℝ) / (8:ℝ)) ^ 2 - 1) :=
      le_trans (show (25/6:ℝ) ≤ ((18:ℕ):ℝ) / (8:ℝ) + (2.0:ℝ) by norm_num)
        (add_le_add (le_refl _) hsq1)
    have hlog : Real.log ((25/6):ℝ) = 2*Real.log 5 - (Real.log 2 + Real.log 3) := by
      rw [show ((25/6):ℝ) = (5^2)/(2*3) from by norm_num,
        Real.log_div (by norm_num) (by norm_num),
        Real.log_pow,
        Real.log_mul (by norm_num) (by norm_num)]
      push_cast; ring
    have ha : Real.log ((25/6):ℝ) ≤ Real.arcosh (((18:ℕ):ℝ) / (8:ℝ)) :=
      log_le_arcosh hx1 (show (0 : ℝ) < ((25/6):ℝ) by norm_num) hy
    have hα : (2*1.6094379123-(0.6931471808+1.0986122888):ℝ) ≤ Real.arcosh (((18:ℕ):ℝ) / (8:ℝ)) :=
      calc (2*1.6094379123-(0.6931471808+1.0986122888):ℝ) ≤ 2*Real.log 5 - (Real.log 2 + Real.log 3) :=
            sub_le_sub (mul_le_mul_of_nonneg_left Real.log_five_gt_d9.le (by norm_num)) (add_le_add Real.log_two_lt_d9.le Real.log_three_lt_d9.le)
        _ = Real.log ((25/6):ℝ) := hlog.symm
        _ ≤ Real.arcosh (((18:ℕ):ℝ) / (8:ℝ)) := ha
    have hba : besselAlpha (8:ℝ) ((18:ℕ):ℝ)
        = Real.arcosh (((18:ℕ):ℝ) / (8:ℝ)) := rfl
    have hr : nrR (8:ℝ) 18 ≤ ((6/25):ℝ) := by
      have e := exp_neg_arcosh_le_inv hx1 (show (0 : ℝ) < ((25/6):ℝ) by norm_num) hy
      unfold nrR
      rw [hba]
      have e2 : (1 : ℝ) / ((25/6):ℝ) = ((6/25):ℝ) := by norm_num
      rw [← e2]
      exact e
    have he1 : nrEta1of (8:ℝ) 18 ≤ ((19375/6859):ℝ) := by
      have hmono := nrEta1_mono (nrR_nonneg _ _) hr (by norm_num)
      have e : nrEta1 ((6/25):ℝ) = ((19375/6859):ℝ) := by unfold nrEta1; norm_num
      show nrEta1 (nrR (8:ℝ) 18) ≤ _
      calc nrEta1 (nrR (8:ℝ) 18) ≤ nrEta1 ((6/25):ℝ) := hmono
        _ = ((19375/6859):ℝ) := e
    have he2 : nrEta2of (8:ℝ) 18 ≤ ((41869375/2476099):ℝ) := by
      have hmono := nrEta2_mono (nrR_nonneg _ _) hr (by norm_num)
      have e : nrEta2 ((6/25):ℝ) = ((41869375/2476099):ℝ) := by unfold nrEta2; norm_num
      show nrEta2 (nrR (8:ℝ) 18) ≤ _
      calc nrEta2 (nrR (8:ℝ) 18) ≤ nrEta2 ((6/25):ℝ) := hmono
        _ = ((41869375/2476099):ℝ) := e
    have hsqU : Real.sqrt (((18:ℕ):ℝ) ^ 2 - (8:ℝ) ^ 2) ≤ (16.13:ℝ) := by
      rw [Real.sqrt_le_iff]
      refine ⟨by norm_num, by norm_num⟩
    have hsqL : (16.12:ℝ) ≤ Real.sqrt (((18:ℕ):ℝ) ^ 2 - (8:ℝ) ^ 2) :=
      (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
    have htlo : (4.01:ℝ)
        ≤ Real.sqrt (Real.sqrt (((18:ℕ):ℝ) ^ 2 - (8:ℝ) ^ 2)) := by
      have htlo2 : (4.01:ℝ) ^ 2
          ≤ Real.sqrt (((18:ℕ):ℝ) ^ 2 - (8:ℝ) ^ 2) :=
        le_trans (by norm_num) hsqL
      exact (Real.le_sqrt (by norm_num) (Real.sqrt_nonneg _)).mpr htlo2
    have hC := nrCcal_tight_le_of (show (2 : ℝ) ≤ ((18:ℕ):ℝ) by norm_num)
      (show (0 : ℝ) < (8:ℝ) by norm_num)
      (show (8:ℝ) < ((18:ℕ):ℝ) by norm_num)
      he1 (show (0 : ℝ) ≤ ((19375/6859):ℝ) by norm_num)
      he2 (show (0 : ℝ) ≤ ((41869375/2476099):ℝ) by norm_num)
      (show 2 * (1 + 1 / ((18:ℕ):ℝ) ^ 2) * (1 + (4 / 27) * ((19375/6859):ℝ))
        * ((13 / 5) * ((41869375/2476099):ℝ) * ((18:ℕ):ℝ) ^ 2 + 44 + 2 * (12 + 16 / 27) * ((19375/6859):ℝ))
        ≤ (202.16:ℝ) ^ 2 by norm_num)
      (show (0 : ℝ) ≤ (202.16:ℝ) by norm_num)
    have hF : ((9:ℕ):ℝ) ≤ besselF (8:ℝ) ((18:ℕ):ℝ) := by
      have hq : ((18:ℕ):ℝ) = (18:ℝ) := by norm_num
      have hk : ((9:ℕ):ℝ) = (9:ℝ) := by norm_num
      rw [hq, hk]
      unfold besselF besselAlpha
      have g1 : (2*1.6094379123-(0.6931471808+1.0986122888):ℝ) ≤ Real.arcosh ((18:ℝ) / (8:ℝ)) := by
        rw [← hq]
        exact hα
      have g2 : Real.sqrt ((18:ℝ) ^ 2 - (8:ℝ) ^ 2) ≤ (16.13:ℝ) := by
        rw [← hq]
        exact hsqU
      have hmul : (18:ℝ) * (2*1.6094379123-(0.6931471808+1.0986122888):ℝ)
          ≤ (18:ℝ) * Real.arcosh ((18:ℝ) / (8:ℝ)) :=
        mul_le_mul_of_nonneg_left g1 (by norm_num)
      have key : (9:ℝ) ≤ (18:ℝ) * (2*1.6094379123-(0.6931471808+1.0986122888):ℝ) - (16.13:ℝ) := by norm_num
      calc (9:ℝ) ≤ (18:ℝ) * (2*1.6094379123-(0.6931471808+1.0986122888):ℝ) - (16.13:ℝ) := key
        _ ≤ (18:ℝ) * Real.arcosh ((18:ℝ) / (8:ℝ))
            - Real.sqrt ((18:ℝ) ^ 2 - (8:ℝ) ^ 2) :=
          sub_le_sub hmul g2
    have hEpow : (8103:ℝ) ≤ (2.7182818283 : ℝ) ^ 9 := by norm_num
    have hexp : Real.exp (-(besselF (8:ℝ) ((18:ℕ):ℝ))) ≤ 1 / (8103:ℝ) :=
      nr_exp_neg_le hF hEpow (by norm_num)
    have hE := nrE2star_le_of hexp (show (0 : ℝ) ≤ 1 / (8103:ℝ) by norm_num)
      htlo (show (0 : ℝ) < (4.01:ℝ) by norm_num)
      hr (show ((6/25):ℝ) < 1 by norm_num)
      two_sqrt_pi_div_8_le (show (0 : ℝ) ≤ (1.26 : ℝ) by norm_num)
    have hC0nn : (0 : ℝ) ≤ (0.6367 : ℝ) * (1 / ((18:ℕ):ℝ)) * (202.16:ℝ) := by
      have h1 : (0 : ℝ) ≤ (0.6367 : ℝ) * (1 / ((18:ℕ):ℝ)) :=
        mul_nonneg (by norm_num)
          (le_of_lt (one_div_pos.mpr (by norm_num)))
      exact mul_nonneg h1 (by norm_num)
    have hQnn : (0 : ℝ)
        ≤ ((0.6367 : ℝ) * (1 / ((18:ℕ):ℝ)) * (202.16:ℝ)) * (((18:ℕ):ℝ)) ^ 2 :=
      mul_nonneg hC0nn (sq_nonneg _)
    have hαnn : (0 : ℝ) ≤ besselAlpha (8:ℝ) (((18:ℕ):ℝ)) := by
      rw [hba]
      exact le_trans (show (0:ℝ) ≤ (2*1.6094379123-(0.6931471808+1.0986122888):ℝ) by norm_num) hα
    have hEnn : (0 : ℝ) ≤ nrE2star (8:ℝ) 18 := nrE2star_nonneg hαnn
    have hfin : ((0.6367 : ℝ) * (1 / ((18:ℕ):ℝ)) * (202.16:ℝ)) * (((18:ℕ):ℝ)) ^ 2
        * ((1.26 : ℝ) * (1 / (8103:ℝ)) / ((4.01:ℝ) * (1 - ((6/25):ℝ)))) < 1 / 2 := by
      norm_num
    exact nr_tight_criterion hC hE hQnn hEnn hfin
  have hcost := new_rung_final_tight (hN := by norm_num) (hφ0 := Real.pi_pos)
    (hφπ := le_rfl) (hAdm := hAdm) (τ := (8 : ℝ)) (hτ1 := by norm_num)
    (hlt := by norm_num) hmain
  calc (16:ℝ) = 2 * (8:ℝ) := by norm_num
    _ ≤ cost θ := le_of_lt hcost


/-- Certified tight number at `N = 7` (`φ = π`): `cost θ ≥ 14`, via the tight criterion
at `τ = 7`, `q = 16` (criterion value `≈ 0.09 < 1/2`). -/
theorem cert_N7_tight {L : ℕ} {α θ : Fin L → ℝ}
    (hAdm : Admissible 7 Real.pi L α θ) : 14 ≤ cost θ := by
  have hmain : nrCcal_tight (7:ℝ) 16 * (((16:ℕ):ℝ)) ^ 2
      * nrE2star (7:ℝ) 16 < Real.sin (Real.pi / 4) ^ 2 := by
    rw [sin_pi_div_four_sq]
    have hx1 : (1 : ℝ) < ((16:ℕ):ℝ) / (7:ℝ) := by norm_num
    have hs1 : (2.05:ℝ) ^ 2 ≤ (((16:ℕ):ℝ) / (7:ℝ)) ^ 2 - 1 := by norm_num
    have hsq1 : (2.05:ℝ)
        ≤ Real.sqrt ((((16:ℕ):ℝ) / (7:ℝ)) ^ 2 - 1) :=
      (Real.le_sqrt (by norm_num) (by norm_num)).mpr hs1
    have hy : (108/25:ℝ) ≤ ((16:ℕ):ℝ) / (7:ℝ)
        + Real.sqrt ((((16:ℕ):ℝ) / (7:ℝ)) ^ 2 - 1) :=
      le_trans (show (108/25:ℝ) ≤ ((16:ℕ):ℝ) / (7:ℝ) + (2.05:ℝ) by norm_num)
        (add_le_add (le_refl _) hsq1)
    have hlog : Real.log ((108/25):ℝ) = (2*Real.log 2 + 3*Real.log 3) - 2*Real.log 5 := by
      rw [show ((108/25):ℝ) = ((2^2*3^3))/(5^2) from by norm_num,
        Real.log_div (by norm_num) (by norm_num),
        Real.log_mul (by norm_num) (by norm_num),
        Real.log_pow,
        Real.log_pow,
        Real.log_pow]
      push_cast; ring
    have ha : Real.log ((108/25):ℝ) ≤ Real.arcosh (((16:ℕ):ℝ) / (7:ℝ)) :=
      log_le_arcosh hx1 (show (0 : ℝ) < ((108/25):ℝ) by norm_num) hy
    have hα : ((2*0.6931471803+3*1.0986122885)-2*1.6094379126:ℝ) ≤ Real.arcosh (((16:ℕ):ℝ) / (7:ℝ)) :=
      calc ((2*0.6931471803+3*1.0986122885)-2*1.6094379126:ℝ) ≤ (2*Real.log 2 + 3*Real.log 3) - 2*Real.log 5 :=
            sub_le_sub (add_le_add (mul_le_mul_of_nonneg_left Real.log_two_gt_d9.le (by norm_num)) (mul_le_mul_of_nonneg_left Real.log_three_gt_d9.le (by norm_num))) (mul_le_mul_of_nonneg_left Real.log_five_lt_d9.le (by norm_num))
        _ = Real.log ((108/25):ℝ) := hlog.symm
        _ ≤ Real.arcosh (((16:ℕ):ℝ) / (7:ℝ)) := ha
    have hba : besselAlpha (7:ℝ) ((16:ℕ):ℝ)
        = Real.arcosh (((16:ℕ):ℝ) / (7:ℝ)) := rfl
    have hr : nrR (7:ℝ) 16 ≤ ((25/108):ℝ) := by
      have e := exp_neg_arcosh_le_inv hx1 (show (0 : ℝ) < ((108/25):ℝ) by norm_num) hy
      unfold nrR
      rw [hba]
      have e2 : (1 : ℝ) / ((108/25):ℝ) = ((25/108):ℝ) := by norm_num
      rw [← e2]
      exact e
    have he1 : nrEta1of (7:ℝ) 16 ≤ ((1551312/571787):ℝ) := by
      have hmono := nrEta1_mono (nrR_nonneg _ _) hr (by norm_num)
      have e : nrEta1 ((25/108):ℝ) = ((1551312/571787):ℝ) := by unfold nrEta1; norm_num
      show nrEta1 (nrR (7:ℝ) 16) ≤ _
      calc nrEta1 (nrR (7:ℝ) 16) ≤ nrEta1 ((25/108):ℝ) := hmono
        _ = ((1551312/571787):ℝ) := e
    have he2 : nrEta2of (7:ℝ) 16 ≤ ((60949497168/3939040643):ℝ) := by
      have hmono := nrEta2_mono (nrR_nonneg _ _) hr (by norm_num)
      have e : nrEta2 ((25/108):ℝ) = ((60949497168/3939040643):ℝ) := by unfold nrEta2; norm_num
      show nrEta2 (nrR (7:ℝ) 16) ≤ _
      calc nrEta2 (nrR (7:ℝ) 16) ≤ nrEta2 ((25/108):ℝ) := hmono
        _ = ((60949497168/3939040643):ℝ) := e
    have hsqU : Real.sqrt (((16:ℕ):ℝ) ^ 2 - (7:ℝ) ^ 2) ≤ (14.39:ℝ) := by
      rw [Real.sqrt_le_iff]
      refine ⟨by norm_num, by norm_num⟩
    have hsqL : (14.38:ℝ) ≤ Real.sqrt (((16:ℕ):ℝ) ^ 2 - (7:ℝ) ^ 2) :=
      (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
    have htlo : (3.79:ℝ)
        ≤ Real.sqrt (Real.sqrt (((16:ℕ):ℝ) ^ 2 - (7:ℝ) ^ 2)) := by
      have htlo2 : (3.79:ℝ) ^ 2
          ≤ Real.sqrt (((16:ℕ):ℝ) ^ 2 - (7:ℝ) ^ 2) :=
        le_trans (by norm_num) hsqL
      exact (Real.le_sqrt (by norm_num) (Real.sqrt_nonneg _)).mpr htlo2
    have hC := nrCcal_tight_le_of (show (2 : ℝ) ≤ ((16:ℕ):ℝ) by norm_num)
      (show (0 : ℝ) < (7:ℝ) by norm_num)
      (show (7:ℝ) < ((16:ℕ):ℝ) by norm_num)
      he1 (show (0 : ℝ) ≤ ((1551312/571787):ℝ) by norm_num)
      he2 (show (0 : ℝ) ≤ ((60949497168/3939040643):ℝ) by norm_num)
      (show 2 * (1 + 1 / ((16:ℕ):ℝ) ^ 2) * (1 + (4 / 27) * ((1551312/571787):ℝ))
        * ((13 / 5) * ((60949497168/3939040643):ℝ) * ((16:ℕ):ℝ) ^ 2 + 44 + 2 * (12 + 16 / 27) * ((1551312/571787):ℝ))
        ≤ (171.20:ℝ) ^ 2 by norm_num)
      (show (0 : ℝ) ≤ (171.20:ℝ) by norm_num)
    have hF : ((9:ℕ):ℝ) ≤ besselF (7:ℝ) ((16:ℕ):ℝ) := by
      have hq : ((16:ℕ):ℝ) = (16:ℝ) := by norm_num
      have hk : ((9:ℕ):ℝ) = (9:ℝ) := by norm_num
      rw [hq, hk]
      unfold besselF besselAlpha
      have g1 : ((2*0.6931471803+3*1.0986122885)-2*1.6094379126:ℝ) ≤ Real.arcosh ((16:ℝ) / (7:ℝ)) := by
        rw [← hq]
        exact hα
      have g2 : Real.sqrt ((16:ℝ) ^ 2 - (7:ℝ) ^ 2) ≤ (14.39:ℝ) := by
        rw [← hq]
        exact hsqU
      have hmul : (16:ℝ) * ((2*0.6931471803+3*1.0986122885)-2*1.6094379126:ℝ)
          ≤ (16:ℝ) * Real.arcosh ((16:ℝ) / (7:ℝ)) :=
        mul_le_mul_of_nonneg_left g1 (by norm_num)
      have key : (9:ℝ) ≤ (16:ℝ) * ((2*0.6931471803+3*1.0986122885)-2*1.6094379126:ℝ) - (14.39:ℝ) := by norm_num
      calc (9:ℝ) ≤ (16:ℝ) * ((2*0.6931471803+3*1.0986122885)-2*1.6094379126:ℝ) - (14.39:ℝ) := key
        _ ≤ (16:ℝ) * Real.arcosh ((16:ℝ) / (7:ℝ))
            - Real.sqrt ((16:ℝ) ^ 2 - (7:ℝ) ^ 2) :=
          sub_le_sub hmul g2
    have hEpow : (8103:ℝ) ≤ (2.7182818283 : ℝ) ^ 9 := by norm_num
    have hexp : Real.exp (-(besselF (7:ℝ) ((16:ℕ):ℝ))) ≤ 1 / (8103:ℝ) :=
      nr_exp_neg_le hF hEpow (by norm_num)
    have hE := nrE2star_le_of hexp (show (0 : ℝ) ≤ 1 / (8103:ℝ) by norm_num)
      htlo (show (0 : ℝ) < (3.79:ℝ) by norm_num)
      hr (show ((25/108):ℝ) < 1 by norm_num)
      two_sqrt_pi_div_8_le (show (0 : ℝ) ≤ (1.26 : ℝ) by norm_num)
    have hC0nn : (0 : ℝ) ≤ (0.6367 : ℝ) * (1 / ((16:ℕ):ℝ)) * (171.20:ℝ) := by
      have h1 : (0 : ℝ) ≤ (0.6367 : ℝ) * (1 / ((16:ℕ):ℝ)) :=
        mul_nonneg (by norm_num)
          (le_of_lt (one_div_pos.mpr (by norm_num)))
      exact mul_nonneg h1 (by norm_num)
    have hQnn : (0 : ℝ)
        ≤ ((0.6367 : ℝ) * (1 / ((16:ℕ):ℝ)) * (171.20:ℝ)) * (((16:ℕ):ℝ)) ^ 2 :=
      mul_nonneg hC0nn (sq_nonneg _)
    have hαnn : (0 : ℝ) ≤ besselAlpha (7:ℝ) (((16:ℕ):ℝ)) := by
      rw [hba]
      exact le_trans (show (0:ℝ) ≤ ((2*0.6931471803+3*1.0986122885)-2*1.6094379126:ℝ) by norm_num) hα
    have hEnn : (0 : ℝ) ≤ nrE2star (7:ℝ) 16 := nrE2star_nonneg hαnn
    have hfin : ((0.6367 : ℝ) * (1 / ((16:ℕ):ℝ)) * (171.20:ℝ)) * (((16:ℕ):ℝ)) ^ 2
        * ((1.26 : ℝ) * (1 / (8103:ℝ)) / ((3.79:ℝ) * (1 - ((25/108):ℝ)))) < 1 / 2 := by
      norm_num
    exact nr_tight_criterion hC hE hQnn hEnn hfin
  have hcost := new_rung_final_tight (hN := by norm_num) (hφ0 := Real.pi_pos)
    (hφπ := le_rfl) (hAdm := hAdm) (τ := (7 : ℝ)) (hτ1 := by norm_num)
    (hlt := by norm_num) hmain
  calc (14:ℝ) = 2 * (7:ℝ) := by norm_num
    _ ≤ cost θ := le_of_lt hcost


/-- Certified tight number at `N = 6` (`φ = π`): `cost θ ≥ 10`, via the tight criterion
at `τ = 5`, `q = 14` (criterion value `≈ 0.06 < 1/2`). -/
theorem cert_N6_tight {L : ℕ} {α θ : Fin L → ℝ}
    (hAdm : Admissible 6 Real.pi L α θ) : 10 ≤ cost θ := by
  have hmain : nrCcal_tight (5:ℝ) 14 * (((14:ℕ):ℝ)) ^ 2
      * nrE2star (5:ℝ) 14 < Real.sin (Real.pi / 4) ^ 2 := by
    rw [sin_pi_div_four_sq]
    have hx1 : (1 : ℝ) < ((14:ℕ):ℝ) / (5:ℝ) := by norm_num
    have hs1 : (2.6:ℝ) ^ 2 ≤ (((14:ℕ):ℝ) / (5:ℝ)) ^ 2 - 1 := by norm_num
    have hsq1 : (2.6:ℝ)
        ≤ Real.sqrt ((((14:ℕ):ℝ) / (5:ℝ)) ^ 2 - 1) :=
      (Real.le_sqrt (by norm_num) (by norm_num)).mpr hs1
    have hy : (5:ℝ) ≤ ((14:ℕ):ℝ) / (5:ℝ)
        + Real.sqrt ((((14:ℕ):ℝ) / (5:ℝ)) ^ 2 - 1) :=
      le_trans (show (5:ℝ) ≤ ((14:ℕ):ℝ) / (5:ℝ) + (2.6:ℝ) by norm_num)
        (add_le_add (le_refl _) hsq1)
    have ha : Real.log (5:ℝ) ≤ Real.arcosh (((14:ℕ):ℝ) / (5:ℝ)) :=
      log_le_arcosh hx1 (show (0 : ℝ) < (5:ℝ) by norm_num) hy
    have hα : (1.6094379123:ℝ) ≤ Real.arcosh (((14:ℕ):ℝ) / (5:ℝ)) :=
      le_trans Real.log_five_gt_d9.le ha
    have hba : besselAlpha (5:ℝ) ((14:ℕ):ℝ)
        = Real.arcosh (((14:ℕ):ℝ) / (5:ℝ)) := rfl
    have hr : nrR (5:ℝ) 14 ≤ ((1/5):ℝ) := by
      have e := exp_neg_arcosh_le_inv hx1 (show (0 : ℝ) < ((5):ℝ) by norm_num) hy
      unfold nrR
      rw [hba]
      have e2 : (1 : ℝ) / ((5):ℝ) = ((1/5):ℝ) := by norm_num
      rw [← e2]
      exact e
    have he1 : nrEta1of (5:ℝ) 14 ≤ ((75/32):ℝ) := by
      have hmono := nrEta1_mono (nrR_nonneg _ _) hr (by norm_num)
      have e : nrEta1 ((1/5):ℝ) = ((75/32):ℝ) := by unfold nrEta1; norm_num
      show nrEta1 (nrR (5:ℝ) 14) ≤ _
      calc nrEta1 (nrR (5:ℝ) 14) ≤ nrEta1 ((1/5):ℝ) := hmono
        _ = ((75/32):ℝ) := e
    have he2 : nrEta2of (5:ℝ) 14 ≤ ((1425/128):ℝ) := by
      have hmono := nrEta2_mono (nrR_nonneg _ _) hr (by norm_num)
      have e : nrEta2 ((1/5):ℝ) = ((1425/128):ℝ) := by unfold nrEta2; norm_num
      show nrEta2 (nrR (5:ℝ) 14) ≤ _
      calc nrEta2 (nrR (5:ℝ) 14) ≤ nrEta2 ((1/5):ℝ) := hmono
        _ = ((1425/128):ℝ) := e
    have hsqU : Real.sqrt (((14:ℕ):ℝ) ^ 2 - (5:ℝ) ^ 2) ≤ (13.08:ℝ) := by
      rw [Real.sqrt_le_iff]
      refine ⟨by norm_num, by norm_num⟩
    have hsqL : (13.07:ℝ) ≤ Real.sqrt (((14:ℕ):ℝ) ^ 2 - (5:ℝ) ^ 2) :=
      (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
    have htlo : (3.61:ℝ)
        ≤ Real.sqrt (Real.sqrt (((14:ℕ):ℝ) ^ 2 - (5:ℝ) ^ 2)) := by
      have htlo2 : (3.61:ℝ) ^ 2
          ≤ Real.sqrt (((14:ℕ):ℝ) ^ 2 - (5:ℝ) ^ 2) :=
        le_trans (by norm_num) hsqL
      exact (Real.le_sqrt (by norm_num) (Real.sqrt_nonneg _)).mpr htlo2
    have hC := nrCcal_tight_le_of (show (2 : ℝ) ≤ ((14:ℕ):ℝ) by norm_num)
      (show (0 : ℝ) < (5:ℝ) by norm_num)
      (show (5:ℝ) < ((14:ℕ):ℝ) by norm_num)
      he1 (show (0 : ℝ) ≤ ((75/32):ℝ) by norm_num)
      he2 (show (0 : ℝ) ≤ ((1425/128):ℝ) by norm_num)
      (show 2 * (1 + 1 / ((14:ℕ):ℝ) ^ 2) * (1 + (4 / 27) * ((75/32):ℝ))
        * ((13 / 5) * ((1425/128):ℝ) * ((14:ℕ):ℝ) ^ 2 + 44 + 2 * (12 + 16 / 27) * ((75/32):ℝ))
        ≤ (125.09:ℝ) ^ 2 by norm_num)
      (show (0 : ℝ) ≤ (125.09:ℝ) by norm_num)
    have hF : ((9:ℕ):ℝ) ≤ besselF (5:ℝ) ((14:ℕ):ℝ) := by
      have hq : ((14:ℕ):ℝ) = (14:ℝ) := by norm_num
      have hk : ((9:ℕ):ℝ) = (9:ℝ) := by norm_num
      rw [hq, hk]
      unfold besselF besselAlpha
      have g1 : (1.6094379123:ℝ) ≤ Real.arcosh ((14:ℝ) / (5:ℝ)) := by
        rw [← hq]
        exact hα
      have g2 : Real.sqrt ((14:ℝ) ^ 2 - (5:ℝ) ^ 2) ≤ (13.08:ℝ) := by
        rw [← hq]
        exact hsqU
      have hmul : (14:ℝ) * (1.6094379123:ℝ)
          ≤ (14:ℝ) * Real.arcosh ((14:ℝ) / (5:ℝ)) :=
        mul_le_mul_of_nonneg_left g1 (by norm_num)
      have key : (9:ℝ) ≤ (14:ℝ) * (1.6094379123:ℝ) - (13.08:ℝ) := by norm_num
      calc (9:ℝ) ≤ (14:ℝ) * (1.6094379123:ℝ) - (13.08:ℝ) := key
        _ ≤ (14:ℝ) * Real.arcosh ((14:ℝ) / (5:ℝ))
            - Real.sqrt ((14:ℝ) ^ 2 - (5:ℝ) ^ 2) :=
          sub_le_sub hmul g2
    have hEpow : (8103:ℝ) ≤ (2.7182818283 : ℝ) ^ 9 := by norm_num
    have hexp : Real.exp (-(besselF (5:ℝ) ((14:ℕ):ℝ))) ≤ 1 / (8103:ℝ) :=
      nr_exp_neg_le hF hEpow (by norm_num)
    have hE := nrE2star_le_of hexp (show (0 : ℝ) ≤ 1 / (8103:ℝ) by norm_num)
      htlo (show (0 : ℝ) < (3.61:ℝ) by norm_num)
      hr (show ((1/5):ℝ) < 1 by norm_num)
      two_sqrt_pi_div_8_le (show (0 : ℝ) ≤ (1.26 : ℝ) by norm_num)
    have hC0nn : (0 : ℝ) ≤ (0.6367 : ℝ) * (1 / ((14:ℕ):ℝ)) * (125.09:ℝ) := by
      have h1 : (0 : ℝ) ≤ (0.6367 : ℝ) * (1 / ((14:ℕ):ℝ)) :=
        mul_nonneg (by norm_num)
          (le_of_lt (one_div_pos.mpr (by norm_num)))
      exact mul_nonneg h1 (by norm_num)
    have hQnn : (0 : ℝ)
        ≤ ((0.6367 : ℝ) * (1 / ((14:ℕ):ℝ)) * (125.09:ℝ)) * (((14:ℕ):ℝ)) ^ 2 :=
      mul_nonneg hC0nn (sq_nonneg _)
    have hαnn : (0 : ℝ) ≤ besselAlpha (5:ℝ) (((14:ℕ):ℝ)) := by
      rw [hba]
      exact le_trans (show (0:ℝ) ≤ (1.6094379123:ℝ) by norm_num) hα
    have hEnn : (0 : ℝ) ≤ nrE2star (5:ℝ) 14 := nrE2star_nonneg hαnn
    have hfin : ((0.6367 : ℝ) * (1 / ((14:ℕ):ℝ)) * (125.09:ℝ)) * (((14:ℕ):ℝ)) ^ 2
        * ((1.26 : ℝ) * (1 / (8103:ℝ)) / ((3.61:ℝ) * (1 - ((1/5):ℝ)))) < 1 / 2 := by
      norm_num
    exact nr_tight_criterion hC hE hQnn hEnn hfin
  have hcost := new_rung_final_tight (hN := by norm_num) (hφ0 := Real.pi_pos)
    (hφπ := le_rfl) (hAdm := hAdm) (τ := (5 : ℝ)) (hτ1 := by norm_num)
    (hlt := by norm_num) hmain
  calc (10:ℝ) = 2 * (5:ℝ) := by norm_num
    _ ≤ cost θ := le_of_lt hcost


/-- Certified tight number at `N = 5` (`φ = π`): `cost θ ≥ 8`, via the tight criterion
at `τ = 4`, `q = 12` (criterion value `≈ 0.04 < 1/2`). -/
theorem cert_N5_tight {L : ℕ} {α θ : Fin L → ℝ}
    (hAdm : Admissible 5 Real.pi L α θ) : 8 ≤ cost θ := by
  have hmain : nrCcal_tight (4:ℝ) 12 * (((12:ℕ):ℝ)) ^ 2
      * nrE2star (4:ℝ) 12 < Real.sin (Real.pi / 4) ^ 2 := by
    rw [sin_pi_div_four_sq]
    have hx1 : (1 : ℝ) < ((12:ℕ):ℝ) / (4:ℝ) := by norm_num
    have hs1 : (2.82:ℝ) ^ 2 ≤ (((12:ℕ):ℝ) / (4:ℝ)) ^ 2 - 1 := by norm_num
    have hsq1 : (2.82:ℝ)
        ≤ Real.sqrt ((((12:ℕ):ℝ) / (4:ℝ)) ^ 2 - 1) :=
      (Real.le_sqrt (by norm_num) (by norm_num)).mpr hs1
    have hy : (144/25:ℝ) ≤ ((12:ℕ):ℝ) / (4:ℝ)
        + Real.sqrt ((((12:ℕ):ℝ) / (4:ℝ)) ^ 2 - 1) :=
      le_trans (show (144/25:ℝ) ≤ ((12:ℕ):ℝ) / (4:ℝ) + (2.82:ℝ) by norm_num)
        (add_le_add (le_refl _) hsq1)
    have hlog : Real.log ((144/25):ℝ) = (4*Real.log 2 + 2*Real.log 3) - 2*Real.log 5 := by
      rw [show ((144/25):ℝ) = ((2^4*3^2))/(5^2) from by norm_num,
        Real.log_div (by norm_num) (by norm_num),
        Real.log_mul (by norm_num) (by norm_num),
        Real.log_pow,
        Real.log_pow,
        Real.log_pow]
      push_cast; ring
    have ha : Real.log ((144/25):ℝ) ≤ Real.arcosh (((12:ℕ):ℝ) / (4:ℝ)) :=
      log_le_arcosh hx1 (show (0 : ℝ) < ((144/25):ℝ) by norm_num) hy
    have hα : ((4*0.6931471803+2*1.0986122885)-2*1.6094379126:ℝ) ≤ Real.arcosh (((12:ℕ):ℝ) / (4:ℝ)) :=
      calc ((4*0.6931471803+2*1.0986122885)-2*1.6094379126:ℝ) ≤ (4*Real.log 2 + 2*Real.log 3) - 2*Real.log 5 :=
            sub_le_sub (add_le_add (mul_le_mul_of_nonneg_left Real.log_two_gt_d9.le (by norm_num)) (mul_le_mul_of_nonneg_left Real.log_three_gt_d9.le (by norm_num))) (mul_le_mul_of_nonneg_left Real.log_five_lt_d9.le (by norm_num))
        _ = Real.log ((144/25):ℝ) := hlog.symm
        _ ≤ Real.arcosh (((12:ℕ):ℝ) / (4:ℝ)) := ha
    have hba : besselAlpha (4:ℝ) ((12:ℕ):ℝ)
        = Real.arcosh (((12:ℕ):ℝ) / (4:ℝ)) := rfl
    have hr : nrR (4:ℝ) 12 ≤ ((25/144):ℝ) := by
      have e := exp_neg_arcosh_le_inv hx1 (show (0 : ℝ) < ((144/25):ℝ) by norm_num) hy
      unfold nrR
      rw [hba]
      have e2 : (1 : ℝ) / ((144/25):ℝ) = ((25/144):ℝ) := by norm_num
      rw [← e2]
      exact e
    have he1 : nrEta1of (4:ℝ) 12 ≤ ((3504384/1685159):ℝ) := by
      have hmono := nrEta1_mono (nrR_nonneg _ _) hr (by norm_num)
      have e : nrEta1 ((25/144):ℝ) = ((3504384/1685159):ℝ) := by unfold nrEta1; norm_num
      show nrEta1 (nrR (4:ℝ) 12) ≤ _
      calc nrEta1 (nrR (4:ℝ) 12) ≤ nrEta1 ((25/144):ℝ) := hmono
        _ = ((3504384/1685159):ℝ) := e
    have he2 : nrEta2of (4:ℝ) 12 ≤ ((201014970624/23863536599):ℝ) := by
      have hmono := nrEta2_mono (nrR_nonneg _ _) hr (by norm_num)
      have e : nrEta2 ((25/144):ℝ) = ((201014970624/23863536599):ℝ) := by unfold nrEta2; norm_num
      show nrEta2 (nrR (4:ℝ) 12) ≤ _
      calc nrEta2 (nrR (4:ℝ) 12) ≤ nrEta2 ((25/144):ℝ) := hmono
        _ = ((201014970624/23863536599):ℝ) := e
    have hsqU : Real.sqrt (((12:ℕ):ℝ) ^ 2 - (4:ℝ) ^ 2) ≤ (11.32:ℝ) := by
      rw [Real.sqrt_le_iff]
      refine ⟨by norm_num, by norm_num⟩
    have hsqL : (11.31:ℝ) ≤ Real.sqrt (((12:ℕ):ℝ) ^ 2 - (4:ℝ) ^ 2) :=
      (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
    have htlo : (3.36:ℝ)
        ≤ Real.sqrt (Real.sqrt (((12:ℕ):ℝ) ^ 2 - (4:ℝ) ^ 2)) := by
      have htlo2 : (3.36:ℝ) ^ 2
          ≤ Real.sqrt (((12:ℕ):ℝ) ^ 2 - (4:ℝ) ^ 2) :=
        le_trans (by norm_num) hsqL
      exact (Real.le_sqrt (by norm_num) (Real.sqrt_nonneg _)).mpr htlo2
    have hC := nrCcal_tight_le_of (show (2 : ℝ) ≤ ((12:ℕ):ℝ) by norm_num)
      (show (0 : ℝ) < (4:ℝ) by norm_num)
      (show (4:ℝ) < ((12:ℕ):ℝ) by norm_num)
      he1 (show (0 : ℝ) ≤ ((3504384/1685159):ℝ) by norm_num)
      he2 (show (0 : ℝ) ≤ ((201014970624/23863536599):ℝ) by norm_num)
      (show 2 * (1 + 1 / ((12:ℕ):ℝ) ^ 2) * (1 + (4 / 27) * ((3504384/1685159):ℝ))
        * ((13 / 5) * ((201014970624/23863536599):ℝ) * ((12:ℕ):ℝ) ^ 2 + 44 + 2 * (12 + 16 / 27) * ((3504384/1685159):ℝ))
        ≤ (92.55:ℝ) ^ 2 by norm_num)
      (show (0 : ℝ) ≤ (92.55:ℝ) by norm_num)
    have hF : ((9:ℕ):ℝ) ≤ besselF (4:ℝ) ((12:ℕ):ℝ) := by
      have hq : ((12:ℕ):ℝ) = (12:ℝ) := by norm_num
      have hk : ((9:ℕ):ℝ) = (9:ℝ) := by norm_num
      rw [hq, hk]
      unfold besselF besselAlpha
      have g1 : ((4*0.6931471803+2*1.0986122885)-2*1.6094379126:ℝ) ≤ Real.arcosh ((12:ℝ) / (4:ℝ)) := by
        rw [← hq]
        exact hα
      have g2 : Real.sqrt ((12:ℝ) ^ 2 - (4:ℝ) ^ 2) ≤ (11.32:ℝ) := by
        rw [← hq]
        exact hsqU
      have hmul : (12:ℝ) * ((4*0.6931471803+2*1.0986122885)-2*1.6094379126:ℝ)
          ≤ (12:ℝ) * Real.arcosh ((12:ℝ) / (4:ℝ)) :=
        mul_le_mul_of_nonneg_left g1 (by norm_num)
      have key : (9:ℝ) ≤ (12:ℝ) * ((4*0.6931471803+2*1.0986122885)-2*1.6094379126:ℝ) - (11.32:ℝ) := by norm_num
      calc (9:ℝ) ≤ (12:ℝ) * ((4*0.6931471803+2*1.0986122885)-2*1.6094379126:ℝ) - (11.32:ℝ) := key
        _ ≤ (12:ℝ) * Real.arcosh ((12:ℝ) / (4:ℝ))
            - Real.sqrt ((12:ℝ) ^ 2 - (4:ℝ) ^ 2) :=
          sub_le_sub hmul g2
    have hEpow : (8103:ℝ) ≤ (2.7182818283 : ℝ) ^ 9 := by norm_num
    have hexp : Real.exp (-(besselF (4:ℝ) ((12:ℕ):ℝ))) ≤ 1 / (8103:ℝ) :=
      nr_exp_neg_le hF hEpow (by norm_num)
    have hE := nrE2star_le_of hexp (show (0 : ℝ) ≤ 1 / (8103:ℝ) by norm_num)
      htlo (show (0 : ℝ) < (3.36:ℝ) by norm_num)
      hr (show ((25/144):ℝ) < 1 by norm_num)
      two_sqrt_pi_div_8_le (show (0 : ℝ) ≤ (1.26 : ℝ) by norm_num)
    have hC0nn : (0 : ℝ) ≤ (0.6367 : ℝ) * (1 / ((12:ℕ):ℝ)) * (92.55:ℝ) := by
      have h1 : (0 : ℝ) ≤ (0.6367 : ℝ) * (1 / ((12:ℕ):ℝ)) :=
        mul_nonneg (by norm_num)
          (le_of_lt (one_div_pos.mpr (by norm_num)))
      exact mul_nonneg h1 (by norm_num)
    have hQnn : (0 : ℝ)
        ≤ ((0.6367 : ℝ) * (1 / ((12:ℕ):ℝ)) * (92.55:ℝ)) * (((12:ℕ):ℝ)) ^ 2 :=
      mul_nonneg hC0nn (sq_nonneg _)
    have hαnn : (0 : ℝ) ≤ besselAlpha (4:ℝ) (((12:ℕ):ℝ)) := by
      rw [hba]
      exact le_trans (show (0:ℝ) ≤ ((4*0.6931471803+2*1.0986122885)-2*1.6094379126:ℝ) by norm_num) hα
    have hEnn : (0 : ℝ) ≤ nrE2star (4:ℝ) 12 := nrE2star_nonneg hαnn
    have hfin : ((0.6367 : ℝ) * (1 / ((12:ℕ):ℝ)) * (92.55:ℝ)) * (((12:ℕ):ℝ)) ^ 2
        * ((1.26 : ℝ) * (1 / (8103:ℝ)) / ((3.36:ℝ) * (1 - ((25/144):ℝ)))) < 1 / 2 := by
      norm_num
    exact nr_tight_criterion hC hE hQnn hEnn hfin
  have hcost := new_rung_final_tight (hN := by norm_num) (hφ0 := Real.pi_pos)
    (hφπ := le_rfl) (hAdm := hAdm) (τ := (4 : ℝ)) (hτ1 := by norm_num)
    (hlt := by norm_num) hmain
  calc (8:ℝ) = 2 * (4:ℝ) := by norm_num
    _ ≤ cost θ := le_of_lt hcost


end RobustZ
