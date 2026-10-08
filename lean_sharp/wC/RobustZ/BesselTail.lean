import RobustZ.Approx
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Sharpened Bessel tails (`LEAN_READY.md` L1/L2 = `REPORT.md` §2, Theorems 1.1–1.2)

For the Fourier coefficients `fcoef τ n` of `Approx.lean` (the paper's Jacobi–Anger
coefficients `c n τ`, defined by an explicit integral — no Bessel API is used),
with `α := arcosh (n/τ)` and `y := √(n²-τ²) = τ·sinh α`:

* **L1 (sharp form):** `‖fcoef τ n‖ ≤ exp (-(n*α)) * I0 y`,
  where `I0 y := (1/π)∫_0^π e^{y cos u} du`;
* **L1 (boxed form):** `‖fcoef τ n‖ ≤ exp (-(n*α - y)) * √(π/(8*√(n²-τ²)))`;
* **L2 (tail sum):** `∑' m, ‖fcoef τ (q+m)‖ ≤ B q * Tf ≤ B q * (1 + 1/αq)`,
  with `B`, `Tf` exactly as in `LEAN_READY.md` §0.

Proof ingredients (exactly those listed in `LEAN_READY.md`):
(i) the contour shift `integral_shift` of `Approx.lean` (already formalised there);
(ii) the identification of the shifted modulus integral with `I0`;
(iii) `I0 y ≤ e^y·√(π/(8y))` from `1 - cos u ≥ 2u²/π²` (via mathlib's Jordan
inequality `Real.mul_le_sin`) and the Gaussian integral `integral_gaussian_Ioi`;
(a) `f(q+j) - f(q) ≥ j*αq` via the hyperbolic parametrisation, whose only analytic
input is `sinh t ≤ t*cosh t` (`t ≥ 0`);
(c) the geometric series and `1 - e^{-x} ≥ x/(1+x)`.

Deviations from `LEAN_READY.md` (all conservative, none used downstream):
* strict `τ < n` (resp. `τ < q`) instead of `τ ≤ n`: at `τ = n` the boxed L1
  right-hand side is `exp(0)·√(π/0) = 0` in `ℝ` (division by zero), so the boxed
  form is only meaningful — and only ever used — for `τ < n`.
* the tail sum is indexed as `∑' m : ℕ, ‖fcoef τ (q+m)‖` rather than
  `∑' k : {k // q ≤ k}`; the two are canonically the same sum.
* the false quadratic lower bound of `REPORT.md` §2.3 is not used anywhere
  (only `f(q+j) - f(q) ≥ j*αq`, i.e. monotonicity of `f' = α`).
-/

noncomputable section

namespace RobustZ

/-! ## §0 conventions (from `LEAN_READY.md`) -/

/-- `I0 y = (1/π)∫_0^π e^{y cos u} du`. -/
def besselI0 (y : ℝ) : ℝ :=
  (Real.pi)⁻¹ * ∫ u in (0:ℝ)..Real.pi, Real.exp (y * Real.cos u)

/-- Debye phase `α(τ) k = arcosh (k/τ)`. -/
def besselAlpha (τ k : ℝ) : ℝ := Real.arcosh (k / τ)

/-- Debye exponent `f τ k = k*α - √(k²-τ²)`. -/
def besselF (τ k : ℝ) : ℝ := k * besselAlpha τ k - Real.sqrt (k^2 - τ^2)

/-- Majorant `B k = √(π/8)·exp(-f τ k)/(k²-τ²)^{1/4}` (via `√∘√`). -/
def majorB (τ : ℝ) (k : ℕ) : ℝ :=
  Real.sqrt (Real.pi/8) * Real.exp (-(besselF τ (k:ℝ)))
    / Real.sqrt (Real.sqrt ((k:ℝ)^2 - τ^2))

/-- Tail factor `Tf(α) = 1/(1-e^{-α})`. -/
def tailFactor (α : ℝ) : ℝ := 1 / (1 - Real.exp (-α))

/-! ## Auxiliary: continuous integrands -/

lemma cont_exp_cos (y : ℝ) : Continuous fun u : ℝ => Real.exp (y * Real.cos u) :=
  Real.continuous_exp.comp (continuous_const.mul Real.continuous_cos)

/-! ## A. The shifted modulus integral is `I0` -/

/-- Integral of a `T`-periodic continuous function over any length-`T` interval. -/
lemma integral_period_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {T : ℝ} (hper : ∀ x, f (x + T) = f x)
    (hf : Continuous f) (a : ℝ) :
    ∫ x in a..(a+T), f x = ∫ x in (0:ℝ)..T, f x := by
  have hadj1 : (∫ x in a..T, f x) + ∫ x in T..(a+T), f x = ∫ x in a..(a+T), f x :=
    intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)
  have hcomp : (∫ x in (0:ℝ)..a, f (x + T)) = ∫ x in (0:ℝ)+T..a+T, f x :=
    intervalIntegral.integral_comp_add_right f T
  rw [zero_add] at hcomp
  have hcongr : (∫ x in (0:ℝ)..a, f (x + T)) = ∫ x in (0:ℝ)..a, f x :=
    intervalIntegral.integral_congr fun x _ => hper x
  have hshift : (∫ x in T..(a+T), f x) = ∫ x in (0:ℝ)..a, f x := by
    rw [← hcomp]
    exact hcongr
  have hadj0 : (∫ x in (0:ℝ)..a, f x) + ∫ x in a..T, f x = ∫ x in (0:ℝ)..T, f x :=
    intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)
  calc (∫ x in a..(a+T), f x)
      = (∫ x in a..T, f x) + ∫ x in T..(a+T), f x := hadj1.symm
    _ = (∫ x in a..T, f x) + ∫ x in (0:ℝ)..a, f x := by rw [hshift]
    _ = ∫ x in (0:ℝ)..T, f x := (add_comm _ _).trans hadj0

/-- `∫_0^{2π} e^{y sin} = ∫_0^{2π} e^{y cos}` (reflection + periodicity). -/
lemma integral_sin_eq_cos (y : ℝ) :
    (∫ x in (0:ℝ)..(2*Real.pi), Real.exp (y * Real.sin x))
      = ∫ x in (0:ℝ)..(2*Real.pi), Real.exp (y * Real.cos x) := by
  have hrefl : ∀ x : ℝ, Real.exp (y * Real.sin x)
      = Real.exp (y * Real.cos (Real.pi/2 - x)) := by
    intro x
    rw [Real.cos_pi_div_two_sub]
  have hcomp : (∫ x in (0:ℝ)..(2*Real.pi), Real.exp (y * Real.cos (Real.pi/2 - x)))
      = ∫ x in (Real.pi/2 - 2*Real.pi)..(Real.pi/2 - 0), Real.exp (y * Real.cos x) :=
    intervalIntegral.integral_comp_sub_left
      (fun t : ℝ => Real.exp (y * Real.cos t)) (Real.pi/2)
  rw [show (Real.pi/2 - 2*Real.pi) = -(3*Real.pi/2) from by ring,
      show (Real.pi/2 - 0) = Real.pi/2 from by ring] at hcomp
  have hper : ∀ t : ℝ, Real.exp (y * Real.cos (t + 2*Real.pi))
      = Real.exp (y * Real.cos t) := by
    intro t
    rw [Real.cos_add_two_pi]
  have hwrap : (∫ x in (-(3*Real.pi/2))..(-(3*Real.pi/2)+2*Real.pi),
        Real.exp (y * Real.cos x))
      = ∫ x in (0:ℝ)..(2*Real.pi), Real.exp (y * Real.cos x) :=
    integral_period_eq hper (cont_exp_cos y) _
  rw [show (-(3*Real.pi/2)+2*Real.pi) = Real.pi/2 from by ring] at hwrap
  calc (∫ x in (0:ℝ)..(2*Real.pi), Real.exp (y * Real.sin x))
      = ∫ x in (0:ℝ)..(2*Real.pi), Real.exp (y * Real.cos (Real.pi/2 - x)) :=
        intervalIntegral.integral_congr fun x _ => hrefl x
    _ = ∫ x in (-(3*Real.pi/2))..(Real.pi/2), Real.exp (y * Real.cos x) := hcomp
    _ = ∫ x in (0:ℝ)..(2*Real.pi), Real.exp (y * Real.cos x) := hwrap

/-- `∫_0^{2π} e^{y cos} = 2∫_0^π e^{y cos}` (mirror symmetry `cos(2π-u) = cos u`). -/
lemma integral_cos_double (y : ℝ) :
    (∫ x in (0:ℝ)..(2*Real.pi), Real.exp (y * Real.cos x))
      = 2 * ∫ u in (0:ℝ)..Real.pi, Real.exp (y * Real.cos u) := by
  have hcont := cont_exp_cos y
  have hsplit : (∫ x in (0:ℝ)..(2*Real.pi), Real.exp (y * Real.cos x))
      = (∫ x in (0:ℝ)..Real.pi, Real.exp (y * Real.cos x))
        + ∫ x in Real.pi..(2*Real.pi), Real.exp (y * Real.cos x) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)).symm
  have hmirror : (∫ x in Real.pi..(2*Real.pi), Real.exp (y * Real.cos x))
      = ∫ u in (0:ℝ)..Real.pi, Real.exp (y * Real.cos u) := by
    have hrefl : ∀ x : ℝ, Real.exp (y * Real.cos (2*Real.pi - x))
        = Real.exp (y * Real.cos x) := by
      intro x
      rw [Real.cos_two_pi_sub]
    have hcomp : (∫ x in (0:ℝ)..Real.pi, Real.exp (y * Real.cos (2*Real.pi - x)))
        = ∫ x in (2*Real.pi - Real.pi)..(2*Real.pi - 0), Real.exp (y * Real.cos x) :=
      intervalIntegral.integral_comp_sub_left
        (fun t : ℝ => Real.exp (y * Real.cos t)) (2*Real.pi)
    rw [show (2*Real.pi - Real.pi) = Real.pi from by ring,
        show (2*Real.pi - 0) = 2*Real.pi from by ring] at hcomp
    rw [intervalIntegral.integral_congr (fun x _ => hrefl x)] at hcomp
    exact hcomp.symm
  rw [hsplit, hmirror, two_mul]

/-- Identification of the shifted modulus integral with `I0`
(`LEAN_READY.md` L1 ingredient (ii)). -/
lemma integral_sin_eq_I0 (y : ℝ) :
    (2*Real.pi)⁻¹ * (∫ x in (0:ℝ)..(2*Real.pi), Real.exp (y * Real.sin x))
      = besselI0 y := by
  have h2 : (2*Real.pi)⁻¹ * 2 = (Real.pi)⁻¹ := by
    rw [mul_inv]
    ring
  rw [integral_sin_eq_cos y, integral_cos_double y]
  unfold besselI0
  rw [← mul_assoc, h2]

/-! ## B. The `I0` bound -/

/-- `1 - cos u ≥ 2u²/π²` on `[0,π]` (Jordan's inequality `Real.mul_le_sin`). -/
lemma one_sub_cos_ge {u : ℝ} (hu0 : 0 ≤ u) (huπ : u ≤ Real.pi) :
    2 * u^2 / Real.pi^2 ≤ 1 - Real.cos u := by
  have hx0 : (0:ℝ) ≤ u/2 := by linarith
  have hxπ : u/2 ≤ Real.pi/2 := by linarith
  have hj := Real.mul_le_sin hx0 hxπ
  have hnn : (0:ℝ) ≤ 2/Real.pi*(u/2) :=
    mul_nonneg (div_nonneg (by norm_num) Real.pi_pos.le) hx0
  have hsq : (2/Real.pi*(u/2))^2 ≤ (Real.sin (u/2))^2 := by
    have h := mul_self_le_mul_self hnn hj
    rwa [← pow_two, ← pow_two] at h
  have heq : 1 - Real.cos u = 2 * (Real.sin (u/2))^2 := by
    have h2 : u = 2*(u/2) := by ring
    conv_lhs => rw [h2, Real.cos_two_mul_eq_one_sub]
    ring
  rw [heq]
  linear_combination 2 * hsq

/-- `I0 y ≤ e^y·√(π/(8y))` (`LEAN_READY.md` L1 ingredient (iii)). -/
lemma besselI0_le {y : ℝ} (hy : 0 < y) :
    besselI0 y ≤ Real.exp y * Real.sqrt (Real.pi / (8 * y)) := by
  set a : ℝ := 2*y/Real.pi^2 with ha
  have ha0 : 0 < a := by
    rw [ha]
    positivity
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have hpt : ∀ u ∈ Set.Icc (0:ℝ) Real.pi,
      Real.exp (y * Real.cos u) ≤ Real.exp y * Real.exp (-a*u^2) := by
    intro u hu
    have hcos := one_sub_cos_ge hu.1 hu.2
    have hle : y * Real.cos u ≤ y + -(a*u^2) := by
      have hy0 : (0:ℝ) ≤ y := hy.le
      have h2 : y * (2*u^2/Real.pi^2) ≤ y * (1 - Real.cos u) :=
        mul_le_mul_of_nonneg_left hcos hy0
      have h1 : (2*y/Real.pi^2)*u^2 ≤ y*(1 - Real.cos u) := by
        linear_combination h2
      rw [ha]
      linarith [h1]
    calc Real.exp (y * Real.cos u) ≤ Real.exp (y + -(a*u^2)) :=
          Real.exp_le_exp.mpr hle
      _ = Real.exp y * Real.exp (-a*u^2) := by rw [Real.exp_add, neg_mul]
  have hInt1 : IntervalIntegrable (fun u => Real.exp (y * Real.cos u))
      MeasureTheory.volume (0:ℝ) Real.pi := (cont_exp_cos y).intervalIntegrable _ _
  have hcontG : Continuous (fun u : ℝ => Real.exp y * Real.exp (-a*u^2)) := by
    fun_prop
  have hInt2 : IntervalIntegrable (fun u => Real.exp y * Real.exp (-a*u^2))
      MeasureTheory.volume (0:ℝ) Real.pi := hcontG.intervalIntegrable _ _
  have hI1 : (∫ u in (0:ℝ)..Real.pi, Real.exp (y * Real.cos u))
      ≤ ∫ u in (0:ℝ)..Real.pi, Real.exp y * Real.exp (-a*u^2) :=
    intervalIntegral.integral_mono_on hpi.le hInt1 hInt2 (fun u hu => hpt u hu)
  have hI2 : (∫ u in (0:ℝ)..Real.pi, Real.exp y * Real.exp (-a*u^2))
      = Real.exp y * ∫ u in (0:ℝ)..Real.pi, Real.exp (-a*u^2) :=
    intervalIntegral.integral_const_mul _ _
  have hI3 : (∫ u in (0:ℝ)..Real.pi, Real.exp (-a*u^2))
      ≤ ∫ u in Set.Ioi (0:ℝ), Real.exp (-a*u^2) := by
    rw [intervalIntegral.integral_of_le hpi.le]
    have hunion : Set.Ioc (0:ℝ) Real.pi ∪ Set.Ioi Real.pi = Set.Ioi (0:ℝ) :=
      Set.Ioc_union_Ioi_eq_Ioi hpi.le
    have hdisj : Disjoint (Set.Ioc (0:ℝ) Real.pi) (Set.Ioi Real.pi) := by
      rw [Set.disjoint_left]
      intro x hx1 hx2
      simp only [Set.mem_Ioc, Set.mem_Ioi] at hx1 hx2
      linarith
    have hIoi : MeasureTheory.IntegrableOn (fun u => Real.exp (-a*u^2))
        (Set.Ioi (0:ℝ)) MeasureTheory.volume :=
      (integrable_exp_neg_mul_sq ha0).integrableOn
    have h1 : MeasureTheory.IntegrableOn (fun u => Real.exp (-a*u^2))
        (Set.Ioc (0:ℝ) Real.pi) MeasureTheory.volume :=
      hIoi.mono_set Set.Ioc_subset_Ioi_self
    have h2 : MeasureTheory.IntegrableOn (fun u => Real.exp (-a*u^2))
        (Set.Ioi Real.pi) MeasureTheory.volume :=
      hIoi.mono_set (Set.Ioi_subset_Ioi hpi.le)
    rw [← hunion, MeasureTheory.setIntegral_union hdisj measurableSet_Ioi h1 h2]
    exact le_add_of_nonneg_right
      (MeasureTheory.setIntegral_nonneg measurableSet_Ioi (fun x _ => (Real.exp_pos _).le))
  have hG : (∫ u in Set.Ioi (0:ℝ), Real.exp (-a*u^2))
      = Real.sqrt (Real.pi/a)/2 :=
    integral_gaussian_Ioi a
  have hmid : (∫ u in (0:ℝ)..Real.pi, Real.exp (y * Real.cos u))
      ≤ Real.exp y * (Real.sqrt (Real.pi/a)/2) := by
    have e1 : (∫ u in (0:ℝ)..Real.pi, Real.exp (y * Real.cos u))
        ≤ Real.exp y * ∫ u in (0:ℝ)..Real.pi, Real.exp (-a*u^2) :=
      hI1.trans (le_of_eq hI2)
    have e2 : Real.exp y * ∫ u in (0:ℝ)..Real.pi, Real.exp (-a*u^2)
        ≤ Real.exp y * (Real.sqrt (Real.pi/a)/2) := by
      have : (∫ u in (0:ℝ)..Real.pi, Real.exp (-a*u^2))
          ≤ Real.sqrt (Real.pi/a)/2 := hI3.trans (le_of_eq hG)
      exact mul_le_mul_of_nonneg_left this (Real.exp_pos _).le
    exact e1.trans e2
  have hpa : (0:ℝ) ≤ Real.pi/a := by positivity
  have hpy : (0:ℝ) ≤ Real.pi/(8*y) := by positivity
  have hcancel : (Real.pi)⁻¹ * (Real.sqrt (Real.pi/a)/2)
      = Real.sqrt (Real.pi/(8*y)) := by
    have hsq2 : ((Real.pi)⁻¹ * (Real.sqrt (Real.pi/a)/2))^2
        = (Real.sqrt (Real.pi/(8*y)))^2 := by
      rw [mul_pow, div_pow, Real.sq_sqrt hpa, Real.sq_sqrt hpy, ha]
      have hpi0 : Real.pi ≠ 0 := Real.pi_ne_zero
      have hy0 : y ≠ 0 := ne_of_gt hy
      have ha0' : (0:ℝ) < 2*y/Real.pi^2 := by positivity
      field_simp
      ring
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq2 with h | h
    · exact h
    · have q1 : (0:ℝ) ≤ (Real.pi)⁻¹ * (Real.sqrt (Real.pi/a)/2) := by positivity
      have q2 : (0:ℝ) ≤ Real.sqrt (Real.pi/(8*y)) := Real.sqrt_nonneg _
      linarith
  have hfin : (Real.pi)⁻¹ * (Real.exp y * (Real.sqrt (Real.pi/a)/2))
      = Real.exp y * Real.sqrt (Real.pi/(8*y)) := by
    calc (Real.pi)⁻¹ * (Real.exp y * (Real.sqrt (Real.pi/a)/2))
        = Real.exp y * ((Real.pi)⁻¹ * (Real.sqrt (Real.pi/a)/2)) := by ring
      _ = Real.exp y * Real.sqrt (Real.pi/(8*y)) := by rw [hcancel]
  unfold besselI0
  calc (Real.pi)⁻¹ * (∫ u in (0:ℝ)..Real.pi, Real.exp (y * Real.cos u))
      ≤ (Real.pi)⁻¹ * (Real.exp y * (Real.sqrt (Real.pi/a)/2)) := by
        exact mul_le_mul_of_nonneg_left hmid (by positivity)
    _ = Real.exp y * Real.sqrt (Real.pi/(8*y)) := hfin

/-! ## C. The sharpened coefficient bound L1 -/

/-- `√(s²-τ²) = τ·sinh(arcosh(s/τ))`. -/
lemma sqrt_sq_sub_eq_mul_sinh {τ s : ℝ} (hτ : 0 < τ) (hs : τ ≤ s) :
    Real.sqrt (s^2 - τ^2) = τ * Real.sinh (Real.arcosh (s/τ)) := by
  have h1 : (1:ℝ) ≤ s/τ := (le_div_iff₀ hτ).mpr (by linarith)
  have hnn : (0:ℝ) ≤ s^2 - τ^2 := by
    have h2 : (0:ℝ) ≤ (s-τ)*(s+τ) := mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hτ0 : τ ≠ 0 := ne_of_gt hτ
  rw [Real.sinh_arcosh h1]
  have heq : (s/τ)^2 - 1 = (s^2-τ^2)/τ^2 := by
    field_simp
  rw [heq, Real.sqrt_div hnn, Real.sqrt_sq (le_of_lt hτ)]
  field_simp

/-- L1, sharp form: `‖c n τ‖ ≤ exp(-(n*α)) * I0(√(n²-τ²))`. -/
lemma fcoef_sharp {τ : ℝ} (hτ : 0 < τ) {n : ℕ} (hn : 1 ≤ n) (hlt : τ < (n:ℝ)) :
    ‖fcoef τ ((n:ℤ))‖ ≤ Real.exp (-(n:ℝ)*Real.arcosh ((n:ℝ)/τ))
      * besselI0 (Real.sqrt ((n:ℝ)^2-τ^2)) := by
  have hnR : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  set α : ℝ := Real.arcosh ((n:ℝ)/τ) with hα
  have h1τ : (1:ℝ) < (n:ℝ)/τ := (one_lt_div hτ).mpr hlt
  have hδ : 0 < α := Real.arcosh_pos h1τ
  set y : ℝ := τ * Real.sinh α with hy
  have hysqrt : y = Real.sqrt ((n:ℝ)^2-τ^2) := by
    rw [hy, hα]
    exact (sqrt_sq_sub_eq_mul_sinh hτ (by linarith)).symm
  have hshift := integral_shift (τ := τ) (n := ((n:ℤ))) hδ
  have hpt : ∀ θ : ℝ, ‖fz τ ((n:ℤ)) ((θ:ℂ) + (-α:ℂ) * Complex.I)‖
      = Real.exp (-(n:ℝ)*α) * Real.exp (y * Real.sin θ) := by
    intro θ
    rw [show (θ:ℂ) + (-α:ℂ) * Complex.I = (θ:ℂ) - ((α:ℝ):ℂ) * Complex.I by ring,
      norm_fz_shift]
    have hexp : τ * Real.sin θ * Real.sinh α - (((n:ℤ)):ℝ) * α
        = -(n:ℝ)*α + y * Real.sin θ := by
      rw [hy]
      push_cast
      ring
    rw [hexp, Real.exp_add]
  have h01 : (0:ℝ) ≤ 2*Real.pi := by positivity
  have hIntF : IntervalIntegrable
      (fun θ : ℝ => ‖fz τ ((n:ℤ)) ((θ:ℂ) + (-α:ℂ) * Complex.I)‖)
      MeasureTheory.volume (0:ℝ) (2*Real.pi) :=
    (((continuous_fz τ _).comp (by fun_prop :
      Continuous fun θ : ℝ => (θ:ℂ) + (-α:ℂ) * Complex.I)).norm.intervalIntegrable
      _ _)
  have hcontG : Continuous
      (fun θ : ℝ => Real.exp (-(n:ℝ)*α) * Real.exp (y * Real.sin θ)) :=
    continuous_const.mul (Real.continuous_exp.comp
      (continuous_const.mul Real.continuous_sin))
  have hIntG : IntervalIntegrable
      (fun θ : ℝ => Real.exp (-(n:ℝ)*α) * Real.exp (y * Real.sin θ))
      MeasureTheory.volume (0:ℝ) (2*Real.pi) := hcontG.intervalIntegrable _ _
  have hmono : (∫ θ in (0:ℝ)..(2*Real.pi),
        ‖fz τ ((n:ℤ)) ((θ:ℂ) + (-α:ℂ) * Complex.I)‖)
      ≤ ∫ θ in (0:ℝ)..(2*Real.pi),
        Real.exp (-(n:ℝ)*α) * Real.exp (y * Real.sin θ) :=
    intervalIntegral.integral_mono_on h01 hIntF hIntG (fun θ _ => le_of_eq (hpt θ))
  have hfactor : (∫ θ in (0:ℝ)..(2*Real.pi),
        Real.exp (-(n:ℝ)*α) * Real.exp (y * Real.sin θ))
      = Real.exp (-(n:ℝ)*α)
        * ∫ θ in (0:ℝ)..(2*Real.pi), Real.exp (y * Real.sin θ) :=
    intervalIntegral.integral_const_mul _ _
  have hnorm : ‖∫ θ in (0:ℝ)..(2*Real.pi),
        fz τ ((n:ℤ)) ((θ:ℂ) + (-α:ℂ) * Complex.I)‖
      ≤ Real.exp (-(n:ℝ)*α)
        * ∫ θ in (0:ℝ)..(2*Real.pi), Real.exp (y * Real.sin θ) :=
    (intervalIntegral.norm_integral_le_integral_norm h01).trans
      (hmono.trans (le_of_eq hfactor))
  rw [hysqrt] at hnorm
  have hscal : ‖((2*Real.pi)⁻¹:ℝ)‖ = (2*Real.pi)⁻¹ :=
    Real.norm_of_nonneg (by positivity)
  have h1 : ‖∫ θ in (0:ℝ)..(2*Real.pi), fz τ ((n:ℤ)) (θ:ℂ)‖
      = ‖∫ θ in (0:ℝ)..(2*Real.pi), fz τ ((n:ℤ)) ((θ:ℂ) + (0:ℂ) * Complex.I)‖ := by
    congr 2 with θ
    simp
  have hA := integral_sin_eq_I0 (Real.sqrt ((n:ℝ)^2-τ^2))
  rw [fcoef, norm_smul, hscal, h1, hshift]
  refine (mul_le_mul_of_nonneg_left hnorm (by positivity)).trans (le_of_eq ?_)
  calc (2*Real.pi)⁻¹ * (Real.exp (-(n:ℝ)*α)
        * ∫ θ in (0:ℝ)..(2*Real.pi),
          Real.exp (Real.sqrt ((n:ℝ)^2-τ^2) * Real.sin θ))
      = Real.exp (-(n:ℝ)*α) * ((2*Real.pi)⁻¹
        * ∫ θ in (0:ℝ)..(2*Real.pi),
          Real.exp (Real.sqrt ((n:ℝ)^2-τ^2) * Real.sin θ)) := by ring
    _ = Real.exp (-(n:ℝ)*α) * besselI0 (Real.sqrt ((n:ℝ)^2-τ^2)) := by rw [hA]

/-- L1, boxed form (the exact `LEAN_READY.md` L1 box). -/
theorem bessel_L1 {τ : ℝ} (hτ : 0 < τ) {n : ℕ} (hn : 1 ≤ n) (hlt : τ < (n:ℝ)) :
    ‖fcoef τ ((n:ℤ))‖ ≤ Real.exp (-((n:ℝ)*Real.arcosh ((n:ℝ)/τ)
      - Real.sqrt ((n:ℝ)^2-τ^2)))
      * Real.sqrt (Real.pi / (8 * Real.sqrt ((n:ℝ)^2-τ^2))) := by
  have hpos : (0:ℝ) < (n:ℝ)^2 - τ^2 := by
    have hn0 : (0:ℝ) < (n:ℝ) := by
      have : (1:ℕ) ≤ n := hn
      have h1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast this
      linarith
    have h1 : (0:ℝ) < (n:ℝ) - τ := by linarith [hlt]
    have h2 : (0:ℝ) < (n:ℝ) + τ := by linarith [hτ, hn0]
    have h3 : (n:ℝ)^2 - τ^2 = ((n:ℝ)-τ)*((n:ℝ)+τ) := by ring
    rw [h3]
    exact mul_pos h1 h2
  have hy0 : (0:ℝ) < Real.sqrt ((n:ℝ)^2-τ^2) := Real.sqrt_pos.mpr hpos
  have hI := besselI0_le hy0
  have hS := fcoef_sharp hτ hn hlt
  have hexp_eq : -(n:ℝ)*Real.arcosh ((n:ℝ)/τ) + Real.sqrt ((n:ℝ)^2-τ^2)
      = -((n:ℝ)*Real.arcosh ((n:ℝ)/τ) - Real.sqrt ((n:ℝ)^2-τ^2)) := by ring
  calc ‖fcoef τ ((n:ℤ))‖
      ≤ Real.exp (-(n:ℝ)*Real.arcosh ((n:ℝ)/τ))
        * besselI0 (Real.sqrt ((n:ℝ)^2-τ^2)) := hS
    _ ≤ Real.exp (-(n:ℝ)*Real.arcosh ((n:ℝ)/τ))
        * (Real.exp (Real.sqrt ((n:ℝ)^2-τ^2))
          * Real.sqrt (Real.pi/(8*Real.sqrt ((n:ℝ)^2-τ^2)))) :=
        mul_le_mul_of_nonneg_left hI (Real.exp_pos _).le
    _ = Real.exp (-((n:ℝ)*Real.arcosh ((n:ℝ)/τ) - Real.sqrt ((n:ℝ)^2-τ^2)))
        * Real.sqrt (Real.pi/(8*Real.sqrt ((n:ℝ)^2-τ^2))) := by
        rw [← mul_assoc, ← Real.exp_add, hexp_eq]

/-- `majorB` unfolds to the L1 right-hand side. -/
lemma majorB_eq {τ : ℝ} {k : ℕ} :
    majorB τ k = Real.exp (-(besselF τ (k:ℝ)))
      * Real.sqrt (Real.pi/(8*Real.sqrt ((k:ℝ)^2-τ^2))) := by
  unfold majorB
  have hD : Real.pi/(8*Real.sqrt ((k:ℝ)^2-τ^2))
      = (Real.pi/8)/Real.sqrt ((k:ℝ)^2-τ^2) := by ring
  rw [hD, Real.sqrt_div (by positivity : (0:ℝ) ≤ Real.pi/8)]
  ring

/-! ## D. The tail sum L2 -/

/-- `sinh` addition formula (real version via `exp`). -/
lemma sinh_add_eq (a b : ℝ) :
    Real.sinh (a + b) = Real.sinh a * Real.cosh b + Real.cosh a * Real.sinh b := by
  simp only [Real.sinh_eq, Real.cosh_eq]
  rw [Real.exp_add a b]
  have h1 : -((a + b)) = -a + -b := by ring
  rw [h1, Real.exp_add]
  ring

/-- `cosh` addition formula (real version via `exp`). -/
lemma cosh_add_eq (a b : ℝ) :
    Real.cosh (a + b) = Real.cosh a * Real.cosh b + Real.sinh a * Real.sinh b := by
  simp only [Real.sinh_eq, Real.cosh_eq]
  rw [Real.exp_add a b]
  have h1 : -((a + b)) = -a + -b := by ring
  rw [h1, Real.exp_add]
  ring

/-- Core estimate: `sinh t ≤ t*cosh t` for `t ≥ 0` (i.e. `tanh ≤ id`). -/
lemma sinh_le_mul_cosh {t : ℝ} (ht : 0 ≤ t) :
    Real.sinh t ≤ t * Real.cosh t := by
  rcases eq_or_lt_of_le ht with rfl | hpos
  · simp
  · have hd1 : Differentiable ℝ (fun s : ℝ => s * Real.cosh s) :=
      differentiable_id.mul Real.differentiable_cosh
    have hmono : MonotoneOn (fun s => s * Real.cosh s - Real.sinh s)
        (Set.Icc 0 t) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc 0 t)
      · exact (hd1.differentiableOn.sub
          Real.differentiable_sinh.differentiableOn).continuousOn
      · rw [interior_Icc]
        exact (hd1.differentiableOn.sub
          Real.differentiable_sinh.differentiableOn)
      · intro x hx
        rw [interior_Icc] at hx
        have hx0 : (0:ℝ) ≤ x := le_of_lt (Set.mem_Ioo.mp hx).1
        have hd : deriv (fun s => s * Real.cosh s - Real.sinh s) x
            = x * Real.sinh x := by
          have h1 : HasDerivAt (fun s => s * Real.cosh s)
              (1 * Real.cosh x + x * Real.sinh x) x :=
            (hasDerivAt_id' x).mul (Real.hasDerivAt_cosh x)
          have h2 : HasDerivAt Real.sinh (Real.cosh x) x := Real.hasDerivAt_sinh x
          have h3 := h1.sub h2
          have hfun : (fun s => s * Real.cosh s - Real.sinh s)
              = ((fun s => s * Real.cosh s) - Real.sinh) := rfl
          rw [hfun, h3.deriv]
          ring
        rw [hd]
        exact mul_nonneg hx0 (Real.sinh_nonneg_iff.mpr hx0)
    have h0 : (fun s => s * Real.cosh s - Real.sinh s) (0:ℝ) = 0 := by
      simp [Real.sinh_zero, Real.cosh_zero]
    have hle := hmono (Set.mem_Icc.mpr ⟨le_rfl, hpos.le⟩)
      (Set.mem_Icc.mpr ⟨ht, le_rfl⟩) ht
    rw [h0] at hle
    linarith [hle]

/-- `cosh t - 1 ≤ t*sinh t` for `t ≥ 0` (from the core estimate at `t/2`). -/
lemma cosh_sub_one_le_mul_sinh {t : ℝ} (ht : 0 ≤ t) :
    Real.cosh t - 1 ≤ t * Real.sinh t := by
  have e1 : Real.exp t = Real.exp (t/2) * Real.exp (t/2) := by
    conv_lhs => rw [show t = t/2 + t/2 from by ring]
    rw [Real.exp_add]
  have e2 : Real.exp (-t) = Real.exp (-(t/2)) * Real.exp (-(t/2)) := by
    conv_lhs => rw [show -t = -(t/2) + -(t/2) from by ring]
    rw [Real.exp_add]
  have e3 : Real.exp (t/2) * Real.exp (-(t/2)) = 1 := by
    rw [← Real.exp_add, show (t/2 + -(t/2) : ℝ) = 0 from by ring, Real.exp_zero]
  have hdb : Real.cosh t - 1 = 2 * Real.sinh (t/2) * Real.sinh (t/2) := by
    simp only [Real.cosh_eq, Real.sinh_eq]
    rw [e1, e2]
    linear_combination e3
  have h2s : Real.sinh t = 2 * (Real.sinh (t/2) * Real.cosh (t/2)) := by
    simp only [Real.sinh_eq, Real.cosh_eq]
    rw [e1, e2]
    ring
  have hi := sinh_le_mul_cosh (show (0:ℝ) ≤ t/2 by linarith)
  have hsnn : (0:ℝ) ≤ Real.sinh (t/2) := Real.sinh_nonneg_iff.mpr (by linarith)
  have hab : (2:ℝ) * Real.sinh (t/2) ≤ 2 * ((t/2) * Real.cosh (t/2)) := by
    linarith [hi]
  have step : 2 * Real.sinh (t/2) * Real.sinh (t/2)
      ≤ 2 * ((t/2) * Real.cosh (t/2)) * Real.sinh (t/2) :=
    mul_le_mul_of_nonneg_right hab hsnn
  have hSCnn : (0:ℝ) ≤ Real.sinh (t/2) * Real.cosh (t/2) :=
    mul_nonneg hsnn (Real.cosh_pos _).le
  calc Real.cosh t - 1 = 2 * Real.sinh (t/2) * Real.sinh (t/2) := hdb
    _ ≤ 2 * ((t/2) * Real.cosh (t/2)) * Real.sinh (t/2) := step
    _ = t * (Real.sinh (t/2) * Real.cosh (t/2)) := by ring
    _ ≤ t * Real.sinh t := by
        apply mul_le_mul_of_nonneg_left _ ht
        linarith [h2s, hSCnn]

/-- Hyperbolic key inequality: `cosh u*(u-v) ≥ sinh u - sinh v` for `0 ≤ v ≤ u`. -/
lemma cosh_mul_sub_ge_sinh_sub {u v : ℝ} (hv : 0 ≤ v) (hvu : v ≤ u) :
    Real.sinh u - Real.sinh v ≤ Real.cosh u * (u - v) := by
  set w : ℝ := u - v with hw
  have hw0 : (0:ℝ) ≤ w := by linarith
  have huw : u = v + w := by linarith
  rw [huw, sinh_add_eq, cosh_add_eq]
  have hi := sinh_le_mul_cosh hw0
  have hii := cosh_sub_one_le_mul_sinh hw0
  have hSv : (0:ℝ) ≤ Real.sinh v := Real.sinh_nonneg_iff.mpr hv
  have hCv : (0:ℝ) ≤ Real.cosh v := (Real.cosh_pos _).le
  have s1 : Real.sinh v * (Real.cosh w - 1)
      ≤ Real.sinh v * (w * Real.sinh w) :=
    mul_le_mul_of_nonneg_left hii hSv
  have s2 : Real.cosh v * Real.sinh w
      ≤ Real.cosh v * (w * Real.cosh w) :=
    mul_le_mul_of_nonneg_left hi hCv
  linarith [s1, s2]

/-- `f τ s - f τ q ≥ αq*(s-q)` for `τ ≤ q ≤ s`
(`LEAN_READY.md` L2 ingredient (a); no quadratic term is claimed). -/
lemma besselF_gap {τ q s : ℝ} (hτ : 0 < τ) (hq : τ ≤ q) (hs : q ≤ s) :
    besselAlpha τ q * (s - q) ≤ besselF τ s - besselF τ q := by
  have hτ0 : τ ≠ 0 := ne_of_gt hτ
  have hq1 : (1:ℝ) ≤ q/τ := (le_div_iff₀ hτ).mpr (by linarith)
  have hs1 : (1:ℝ) ≤ s/τ := (le_div_iff₀ hτ).mpr (by linarith)
  set u : ℝ := Real.arcosh (s/τ) with hu
  set v : ℝ := Real.arcosh (q/τ) with hv
  have hcos_s : s = τ * Real.cosh u := by
    rw [hu, Real.cosh_arcosh hs1, mul_comm τ (s/τ), div_mul_cancel₀ _ hτ0]
  have hcos_q : q = τ * Real.cosh v := by
    rw [hv, Real.cosh_arcosh hq1, mul_comm τ (q/τ), div_mul_cancel₀ _ hτ0]
  have hsin_s : Real.sqrt (s^2-τ^2) = τ * Real.sinh u := by
    rw [hu]
    exact sqrt_sq_sub_eq_mul_sinh hτ (by linarith)
  have hsin_q : Real.sqrt (q^2-τ^2) = τ * Real.sinh v := by
    rw [hv]
    exact sqrt_sq_sub_eq_mul_sinh hτ (by linarith)
  have huv : v ≤ u := by
    have hq0 : (0:ℝ) < q := lt_of_lt_of_le hτ hq
    have hs0 : (0:ℝ) < s := lt_of_lt_of_le hq0 hs
    rw [hu, hv]
    exact (Real.arcosh_le_arcosh (by positivity : (0:ℝ) < q/τ)
      (by positivity : (0:ℝ) < s/τ)).mpr
      ((div_le_div_iff_of_pos_right hτ).mpr hs)
  have hv0 : (0:ℝ) ≤ v := by
    rw [hv]
    exact Real.arcosh_nonneg hq1
  have hkey : (0:ℝ) ≤ Real.cosh u*(u-v) - (Real.sinh u - Real.sinh v) := by
    have h := cosh_mul_sub_ge_sinh_sub hv0 huv
    linarith
  have key : (0:ℝ) ≤ τ * (Real.cosh u*(u-v) - (Real.sinh u - Real.sinh v)) :=
    mul_nonneg (le_of_lt hτ) hkey
  have hid : (besselF τ s - besselF τ q) - besselAlpha τ q*(s-q)
      = τ * (Real.cosh u*(u-v) - (Real.sinh u - Real.sinh v)) := by
    unfold besselF besselAlpha
    rw [← hu, ← hv, hsin_s, hsin_q, hcos_s, hcos_q]
    ring
  linarith [hid, key]

/-- Majorant geometric decay `B(q+m) ≤ B(q)*exp(-αq*m)`
(the monotonicity used in `LEAN_READY.md` L3/L4). -/
lemma majorB_geom {τ : ℝ} (hτ : 0 < τ) {q : ℕ} (hq : 1 ≤ q) (hlt : τ < (q:ℝ))
    (m : ℕ) :
    majorB τ (q+m) ≤ majorB τ q * Real.exp (-(besselAlpha τ (q:ℝ))*(m:ℝ)) := by
  have hqR : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
  set s : ℝ := (((q+m : ℕ)):ℝ) with hs
  have hqm : (q:ℝ) ≤ s := by
    rw [hs]
    exact_mod_cast Nat.le_add_right q m
  have hDq : (0:ℝ) < (q:ℝ)^2 - τ^2 := by
    have h1 : (0:ℝ) < (q:ℝ) - τ := by linarith [hlt]
    have h2 : (0:ℝ) < (q:ℝ) + τ := by linarith [hτ, hqR]
    have h3 : (q:ℝ)^2 - τ^2 = ((q:ℝ)-τ)*((q:ℝ)+τ) := by ring
    rw [h3]
    exact mul_pos h1 h2
  have hDs : (0:ℝ) < s^2 - τ^2 := by
    have h1 : (0:ℝ) < s - τ := by linarith [hlt, hqm]
    have h2 : (0:ℝ) < s + τ := by
      have : (0:ℝ) ≤ s := by
        rw [hs]
        positivity
      linarith [hτ]
    have h3 : s^2 - τ^2 = (s-τ)*(s+τ) := by ring
    rw [h3]
    exact mul_pos h1 h2
  have hsm : s - (q:ℝ) = (m:ℝ) := by
    simp only [hs, Nat.cast_add]
    ring
  have hgap := besselF_gap hτ hlt.le hqm
  rw [hsm] at hgap
  have hE : Real.exp (-(besselF τ s))
      ≤ Real.exp (-(besselF τ (q:ℝ)))
        * Real.exp (-(besselAlpha τ (q:ℝ))*(m:ℝ)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith [hgap]
  have hsq2 : (q:ℝ)^2 ≤ s^2 := by nlinarith [hqm, hqR, hDq, hDs]
  have hrr : Real.sqrt (Real.sqrt ((q:ℝ)^2-τ^2))
      ≤ Real.sqrt (Real.sqrt (s^2-τ^2)) :=
    Real.sqrt_le_sqrt (Real.sqrt_le_sqrt (by linarith [hsq2]))
  have hR : (Real.sqrt (Real.sqrt (s^2-τ^2)))⁻¹
      ≤ (Real.sqrt (Real.sqrt ((q:ℝ)^2-τ^2)))⁻¹ := by
    rw [← one_div, ← one_div]
    exact one_div_le_one_div_of_le
      (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hDq)) hrr
  have hRs : (0:ℝ) ≤ (Real.sqrt (Real.sqrt (s^2-τ^2)))⁻¹ :=
    inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hEb : (0:ℝ) ≤ Real.sqrt (Real.pi/8) * (Real.exp (-(besselF τ (q:ℝ)))
      * Real.exp (-(besselAlpha τ (q:ℝ))*(m:ℝ))) := by
    positivity
  have hC : (0:ℝ) ≤ Real.sqrt (Real.pi/8) := Real.sqrt_nonneg _
  have e1 : Real.sqrt (Real.pi/8) * Real.exp (-(besselF τ s))
      ≤ Real.sqrt (Real.pi/8) * (Real.exp (-(besselF τ (q:ℝ)))
        * Real.exp (-(besselAlpha τ (q:ℝ))*(m:ℝ))) :=
    mul_le_mul_of_nonneg_left hE hC
  have e2 : Real.sqrt (Real.pi/8) * Real.exp (-(besselF τ s))
      * (Real.sqrt (Real.sqrt (s^2-τ^2)))⁻¹
      ≤ (Real.sqrt (Real.pi/8) * (Real.exp (-(besselF τ (q:ℝ)))
        * Real.exp (-(besselAlpha τ (q:ℝ))*(m:ℝ))))
        * (Real.sqrt (Real.sqrt ((q:ℝ)^2-τ^2)))⁻¹ :=
    mul_le_mul e1 hR hRs hEb
  have hrrw : (Real.sqrt (Real.pi/8) * Real.exp (-(besselF τ (q:ℝ)))
      / Real.sqrt (Real.sqrt ((q:ℝ)^2-τ^2)))
      * Real.exp (-(besselAlpha τ (q:ℝ))*(m:ℝ))
      = (Real.sqrt (Real.pi/8) * (Real.exp (-(besselF τ (q:ℝ)))
        * Real.exp (-(besselAlpha τ (q:ℝ))*(m:ℝ))))
        * (Real.sqrt (Real.sqrt ((q:ℝ)^2-τ^2)))⁻¹ := by
    rw [div_eq_mul_inv]
    ring
  have hstart : majorB τ (q+m)
      = Real.sqrt (Real.pi/8) * Real.exp (-(besselF τ s))
        / Real.sqrt (Real.sqrt (s^2-τ^2)) := by
    rw [hs]
    simp only [majorB]
  have hend : majorB τ q
      = Real.sqrt (Real.pi/8) * Real.exp (-(besselF τ (q:ℝ)))
        / Real.sqrt (Real.sqrt ((q:ℝ)^2-τ^2)) := by
    simp only [majorB]
  rw [hstart, hend, hrrw]
  exact e2

/-- `Tf(α) ≤ 1 + 1/α` from `1 - e^{-x} ≥ x/(1+x)`
(`LEAN_READY.md` L2 ingredient (c)). -/
lemma tailFactor_le {α : ℝ} (hα : 0 < α) : tailFactor α ≤ 1 + 1/α := by
  have he : (1:ℝ) + α ≤ Real.exp α := by
    have h := Real.add_one_le_exp α
    linarith
  have hep : (0:ℝ) < Real.exp α := Real.exp_pos α
  have h1α : (0:ℝ) < 1 + α := by linarith
  have hα0 : α ≠ 0 := ne_of_gt hα
  have h1α0 : (1:ℝ) + α ≠ 0 := ne_of_gt h1α
  have hsmall : Real.exp (-α) ≤ (1+α)⁻¹ := by
    rw [Real.exp_neg]
    exact (inv_le_inv₀ hep h1α).mpr he
  have hid : (1:ℝ) - (1+α)⁻¹ = α/(1+α) := by
    field_simp
    ring
  have hge : α/(1+α) ≤ 1 - Real.exp (-α) := by
    linarith [hsmall, hid]
  have hpos : (0:ℝ) < 1 - Real.exp (-α) := by
    have hdiv : (0:ℝ) < α/(1+α) := div_pos hα h1α
    linarith [hge]
  have hstep : 1/(1 - Real.exp (-α)) ≤ 1/(α/(1+α)) :=
    one_div_le_one_div_of_le (div_pos hα h1α) hge
  have hfin : (1:ℝ)/(α/(1+α)) = 1 + 1/α := by
    rw [one_div_div]
    field_simp
    ring
  rw [hfin] at hstep
  unfold tailFactor
  exact hstep

/-- L2, sharpened tail sum (the exact `LEAN_READY.md` L2 boxes;
the tail `∑_{k≥q}` is indexed by `k = q+m`). -/
theorem bessel_L2 {τ : ℝ} (hτ : 0 < τ) {q : ℕ} (hq : 2 ≤ q) (hlt : τ < (q:ℝ)) :
    (∑' m : ℕ, ‖fcoef τ ((((q+m : ℕ))):ℤ)‖)
      ≤ majorB τ q * tailFactor (besselAlpha τ (q:ℝ))
    ∧ majorB τ q * tailFactor (besselAlpha τ (q:ℝ))
      ≤ majorB τ q * (1 + 1 / besselAlpha τ (q:ℝ)) := by
  have hq1 : (1:ℕ) ≤ q := by omega
  have hα0 : (0:ℝ) < besselAlpha τ (q:ℝ) := by
    unfold besselAlpha
    apply Real.arcosh_pos
    exact (one_lt_div hτ).mpr hlt
  have hr0 : (0:ℝ) ≤ Real.exp (-(besselAlpha τ (q:ℝ))) := (Real.exp_pos _).le
  have hr1 : Real.exp (-(besselAlpha τ (q:ℝ))) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith [hα0]
  have hmaj : Summable
      (fun m : ℕ => majorB τ q * (Real.exp (-(besselAlpha τ (q:ℝ))))^m) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hpt : ∀ m : ℕ, ‖fcoef τ ((((q+m:ℕ))):ℤ)‖
      ≤ majorB τ q * (Real.exp (-(besselAlpha τ (q:ℝ))))^m := by
    intro m
    have h1m : (1:ℕ) ≤ q + m := by omega
    have hltm : τ < ((((q+m:ℕ))):ℝ) := by
      have hle : (q:ℝ) ≤ ((((q+m:ℕ))):ℝ) := by
        exact_mod_cast Nat.le_add_right q m
      linarith
    have hL1 := bessel_L1 hτ (n := q+m) h1m hltm
    have hM := majorB_geom hτ (q := q) hq1 hlt m
    have hexp : (Real.exp (-(besselAlpha τ (q:ℝ))))^(m:ℕ)
        = Real.exp (-(besselAlpha τ (q:ℝ))*(m:ℝ)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [hexp]
    have hL1' : ‖fcoef τ ((((q+m:ℕ))):ℤ)‖ ≤ majorB τ (q+m) := by
      rw [majorB_eq]
      unfold besselF
      exact hL1
    exact hL1'.trans hM
  have hnorm : Summable (fun m : ℕ => ‖fcoef τ ((((q+m:ℕ))):ℤ)‖) :=
    Summable.of_nonneg_of_le (fun m => norm_nonneg _) hpt hmaj
  have htsum : (∑' m : ℕ, ‖fcoef τ ((((q+m:ℕ))):ℤ)‖)
      ≤ ∑' m : ℕ, majorB τ q * (Real.exp (-(besselAlpha τ (q:ℝ))))^m :=
    Summable.tsum_le_tsum hpt hnorm hmaj
  have hval : (∑' m : ℕ, majorB τ q * (Real.exp (-(besselAlpha τ (q:ℝ))))^m)
      = majorB τ q * tailFactor (besselAlpha τ (q:ℝ)) := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
    unfold tailFactor
    ring
  have hMnn : (0:ℝ) ≤ majorB τ q := by
    unfold majorB
    positivity
  constructor
  · exact htsum.trans (le_of_eq hval)
  · exact mul_le_mul_of_nonneg_left (tailFactor_le hα0) hMnn

#print axioms besselI0
#print axioms besselAlpha
#print axioms besselF
#print axioms majorB
#print axioms tailFactor
#print axioms cont_exp_cos
#print axioms integral_period_eq
#print axioms integral_sin_eq_cos
#print axioms integral_cos_double
#print axioms integral_sin_eq_I0
#print axioms one_sub_cos_ge
#print axioms besselI0_le
#print axioms sqrt_sq_sub_eq_mul_sinh
#print axioms fcoef_sharp
#print axioms bessel_L1
#print axioms majorB_eq
#print axioms sinh_add_eq
#print axioms cosh_add_eq
#print axioms sinh_le_mul_cosh
#print axioms cosh_sub_one_le_mul_sinh
#print axioms cosh_mul_sub_ge_sinh_sub
#print axioms besselF_gap
#print axioms majorB_geom
#print axioms tailFactor_le
#print axioms bessel_L2

end RobustZ
