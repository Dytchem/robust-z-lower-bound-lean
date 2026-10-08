import RobustZ.Statement
import RobustZ.ExpSum
import RobustZ.Flatness
import RobustZ.Elementary
import RobustZ.HTraceLower
import Mathlib.Analysis.Complex.JensenFormula

/-!
# Jensen rung (Theorem J / route-K K2, general-φ form)

Formalizes `explore/routeK_jensen.md` §3 (Theorem J) in general-φ form:
for `0 < φ ≤ π` and every order-`N` admissible sequence with `q = 2N+2`,
`s = 2 sin²(φ/4)`:

  `π * q / (e * (2/s)^((1:ℝ)/q)) ≤ T`,

i.e. liminf coefficient `2π/e ≈ 2.31` (at `φ = π`, `s = 1`: `πq/(e·2^{1/q})`).

## Proof skeleton (mirrors the report §§0–3)

* **Lemma C** (`lemmaC_bound`, sharp by `lemmaC_sharp`): calculus optimum
  `sup_{r>1} (q log r - L)/r = q/(e·e^{L/q})`, from `t ≤ e^{t-1}`.
* **Zero term (J)** (`jensen_zero_term`): Mathlib's Jensen formula
  (`AnalyticOnNhd.circleAverage_log_norm`) on discs `D(0,R)`; all divisor
  terms are nonnegative for analytic `F` (`AnalyticOnNhd.divisor_nonneg`),
  so dropping every zero except the known one at `a = 1` gives
  `q·log R + log‖F 0‖ ≤ circleAverage`.
* **Growth mean (G)** (`growth_mean_of_pointwise`): from the pointwise
  Phragmén–Lindelöf-type bound `‖F z‖ ≤ 2·exp(τ·|Im z|)`, monotonicity of
  `Real.circleAverage` plus `∫₀^{2π}|sin| = 4` gives
  `circleAverage ≤ log 2 + (2/π)·τ·r`.  The `2/π` is the indicator mean.
* **Assembly** (`jensen_rung`): with the tree's endpoint data
  (`HTraceLower.h_zero_ge`, i.e. `h(0) ≥ 1 - cos(φ/2) = s`, and the
  `sup ≤ 2` provenance from `Elementary.h_bounds`), the chain closes with
  `L = log(2/s)` and Lemma C.

## Honest bridge boundary (explore-while-proving)

The final theorem takes the carrier's entire extension `H` as an explicit
argument (its existence with the right frequency cap is `carrier_extend`,
built from the tree's `ExpSum.h_moments`, and `expSum_differentiable`),
and assumes exactly two named analytic inputs about it:

* `jord`: the `q`-fold zero at `1` seen by the divisor
  (real flatness `Flatness.h_flat` is proved in the tree; the
  real-derivative-vanishing ⟹ complex-order bridge is NOT re-proved here);
* `jgrow`: the pointwise complex growth bound `‖H z‖ ≤ 2e^{τ|Im z|}`
  (the tree proves the real ingredients `h_bounds`/`h_zero_ge`, not the
  complexified unitarity estimate).

Conditional on these two explicit hypotheses, the constant `2π/e` proved
here is the *sharp* optimum of the argument (Lemma C is an equality), not
a weakened one.  No `sorry`/`admit`/`axiom` anywhere.
-/

noncomputable section

open Metric Filter MeromorphicOn MeasureTheory
open scoped Topology BigOperators

namespace RobustZ

/-! ## 0. Full-period sine mean -/

/-- `∫₀^{2π} |sin θ| dθ = 4` (the indicator mean behind the `π/2` gain). -/
theorem integral_abs_sin_zero_two_pi :
    ∫ θ in (0:ℝ)..2 * Real.pi, |Real.sin θ| = 4 := by
  have hcont : Continuous fun θ : ℝ => |Real.sin θ| := Real.continuous_sin.abs
  have h0π : (0:ℝ) ≤ Real.pi := Real.pi_pos.le
  have hπ2π : Real.pi ≤ 2 * Real.pi := by linarith [Real.pi_pos]
  have h1 : ∫ θ in (0:ℝ)..Real.pi, |Real.sin θ| = 2 := by
    have heq : ∫ θ in (0:ℝ)..Real.pi, |Real.sin θ|
        = ∫ θ in (0:ℝ)..Real.pi, Real.sin θ := by
      rw [intervalIntegral.integral_of_le h0π, intervalIntegral.integral_of_le h0π]
      exact MeasureTheory.integral_congr_ae (by
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with θ hθ
        exact abs_of_nonneg (Real.sin_nonneg_of_mem_Icc ⟨hθ.1.le, hθ.2⟩))
    rw [heq, integral_sin, Real.cos_zero, Real.cos_pi]
    norm_num
  have h2 : ∫ θ in Real.pi..2 * Real.pi, |Real.sin θ| = 2 := by
    have heq : ∫ θ in Real.pi..2 * Real.pi, |Real.sin θ|
        = ∫ θ in Real.pi..2 * Real.pi, -Real.sin θ := by
      rw [intervalIntegral.integral_of_le hπ2π, intervalIntegral.integral_of_le hπ2π]
      exact MeasureTheory.integral_congr_ae (by
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with θ hθ
        have hmem : θ - Real.pi ∈ Set.Icc (0:ℝ) Real.pi := by
          constructor
          · linarith [hθ.1]
          · linarith [hθ.2]
        have hsin : 0 ≤ Real.sin (θ - Real.pi) := Real.sin_nonneg_of_mem_Icc hmem
        have hθeq : θ = (θ - Real.pi) + Real.pi := by ring
        rw [hθeq, Real.sin_add_pi]
        exact abs_of_nonpos (by linarith))
    rw [heq, intervalIntegral.integral_neg, integral_sin,
      Real.cos_pi, Real.cos_two_pi]
    norm_num
  have hadd : (∫ θ in (0:ℝ)..Real.pi, |Real.sin θ|)
      + (∫ θ in Real.pi..2 * Real.pi, |Real.sin θ|)
      = ∫ θ in (0:ℝ)..2 * Real.pi, |Real.sin θ| :=
    intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)
  linarith [h1, h2, hadd]

/-! ## 1. Lemma C: the calculus optimum (report §1, PROVED) -/

/-- **Lemma C, upper bound**: `(q log r - L)/r ≤ q/(e·e^{L/q})` for all
`q > 0`, `r > 0` (hence `sup_{r>1} ≤` the same value).  From `t ≤ e^{t-1}`. -/
theorem lemmaC_bound {q L r : ℝ} (hq : 0 < q) (hr : 0 < r) :
    (q * Real.log r - L) / r ≤ q / (Real.exp 1 * Real.exp (L / q)) := by
  have hq0 : q ≠ 0 := ne_of_gt hq
  have hC : (0:ℝ) < Real.exp (L / q) := Real.exp_pos _
  have he : (0:ℝ) < Real.exp 1 := Real.exp_pos _
  have he0 : Real.exp 1 ≠ 0 := ne_of_gt he
  have hC0 : Real.exp (L / q) ≠ 0 := ne_of_gt hC
  set t : ℝ := Real.log r - L / q with ht
  have hqq0 : q * (L / q) = L := by
    have e : q * (L / q) = (q / q) * L := by ring
    rw [e, div_self hq0, one_mul]
  have hrw : q * Real.log r - L = q * t := by
    rw [ht, mul_sub, hqq0]
  have hexp_t : Real.exp t = r / Real.exp (L / q) := by
    rw [ht, Real.exp_sub, Real.exp_log hr]
  have hkey : t ≤ Real.exp (t - 1) := by
    have h := Real.add_one_le_exp (t - 1)
    linarith
  by_cases ht0 : t ≤ 0
  · have hnum : q * t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hq.le ht0
    have hle : (q * t) / r ≤ 0 := div_nonpos_of_nonpos_of_nonneg hnum hr.le
    have hpos : (0:ℝ) < q / (Real.exp 1 * Real.exp (L / q)) := by positivity
    rw [hrw]
    linarith [hle, hpos]
  · push Not at ht0
    have het : Real.exp 1 * t ≤ Real.exp t := by
      have h2 : Real.exp (t - 1) = Real.exp t / Real.exp 1 := by
        rw [sub_eq_add_neg, Real.exp_add, Real.exp_neg]
        field_simp
      rw [h2, le_div_iff₀ he] at hkey
      linarith [hkey]
    have hr_eq : r = Real.exp (L / q) * Real.exp t := by
      rw [hexp_t]; field_simp
    have hXE : (0:ℝ) < Real.exp (L / q) * Real.exp t := by positivity
    have e2 : q / (Real.exp 1 * Real.exp (L / q)) * (Real.exp (L / q) * Real.exp t)
        = q * (Real.exp t / Real.exp 1) := by
      field_simp
    rw [hrw, hr_eq, div_le_iff₀ hXE, e2, ← mul_div_assoc, le_div_iff₀ he]
    have hmul := mul_le_mul_of_nonneg_left het hq.le
    linarith [hmul]

/-- **Lemma C, sharpness**: `r⋆ = e·e^{L/q}` attains equality. -/
theorem lemmaC_sharp {q L : ℝ} (hq : 0 < q) :
    (q * Real.log (Real.exp 1 * Real.exp (L / q)) - L)
      / (Real.exp 1 * Real.exp (L / q))
      = q / (Real.exp 1 * Real.exp (L / q)) := by
  have hq0 : q ≠ 0 := ne_of_gt hq
  have hlog : Real.log (Real.exp 1 * Real.exp (L / q)) = 1 + L / q := by
    rw [Real.log_mul (Real.exp_pos _).ne' (Real.exp_pos _).ne',
      Real.log_exp, Real.log_exp]
  rw [hlog]
  have h1 : q * (L / q) = L := by
    have e : q * (L / q) = (q / q) * L := by ring
    rw [e, div_self hq0, one_mul]
  have hqq : q * (1 + L / q) - L = q := by
    rw [mul_add, mul_one, h1, add_sub_cancel_right]
  rw [hqq]

/-- The optimizer `r⋆` is interior (`> 1`) whenever `0 ≤ L`. -/
theorem lemmaC_rstar_gt_one {q L : ℝ} (hq : 0 < q) (hL : 0 ≤ L) :
    1 < Real.exp 1 * Real.exp (L / q) := by
  have h1 : (1:ℝ) < Real.exp 1 := by
    have h := Real.add_one_le_exp (1:ℝ)
    have hpos := Real.exp_pos (1:ℝ)
    linarith
  have h2 : (1:ℝ) ≤ Real.exp (L / q) := by
    have hle : (0:ℝ) ≤ L / q := div_nonneg hL hq.le
    calc (1:ℝ) = Real.exp 0 := (Real.exp_zero).symm
      _ ≤ Real.exp (L / q) := Real.exp_le_exp.mpr hle
  calc (1:ℝ) = 1 * 1 := by ring
    _ < Real.exp 1 * Real.exp (L / q) :=
      mul_lt_mul h1 h2 (by positivity) (by linarith [Real.exp_pos (1:ℝ)])

/-! ## 2. Abstract Jensen chain -/

/-- Abstract Jensen step: the two analytic estimates
`(J)  q·log r ≤ L + c·τ·r  (∀ r > 1)` imply `τ ≥ q/(c·e·e^{L/q})`. -/
theorem jensen_step {q tau c L : ℝ} (hq : 0 < q) (hc : 0 < c) (hL : 0 ≤ L)
    (hJ : ∀ r : ℝ, 1 < r → q * Real.log r - L ≤ c * tau * r) :
    q / (c * Real.exp 1 * Real.exp (L / q)) ≤ tau := by
  have hC : (0:ℝ) < Real.exp (L / q) := Real.exp_pos _
  have he : (0:ℝ) < Real.exp 1 := Real.exp_pos _
  have hcC : (0:ℝ) < c * Real.exp 1 * Real.exp (L / q) := by positivity
  set rstar : ℝ := Real.exp 1 * Real.exp (L / q) with hrstar
  have hr1 : 1 < rstar := lemmaC_rstar_gt_one hq hL
  have hmain := hJ rstar hr1
  have hnum : q * Real.log rstar - L = q := by
    have hlog : Real.log rstar = 1 + L / q := by
      rw [hrstar, Real.log_mul (ne_of_gt he) (ne_of_gt hC),
        Real.log_exp, Real.log_exp]
    rw [hlog]
    have hq0 : q ≠ 0 := ne_of_gt hq
    have h1 : q * (L / q) = L := by
      have e : q * (L / q) = (q / q) * L := by ring
      rw [e, div_self hq0, one_mul]
    rw [mul_add, mul_one, h1, add_sub_cancel_right]
  rw [hnum] at hmain
  rw [div_le_iff₀ hcC]
  have h2 : c * tau * rstar = tau * (c * Real.exp 1 * Real.exp (L / q)) := by
    rw [hrstar]; ring
  rw [h2] at hmain
  exact hmain

/-- Indicator-mean specialization (`c = 2/π`): `T = 2τ ≥ πq/(e·e^{L/q})`. -/
theorem jensen_indicator_step {q tau T L : ℝ} (hq : 0 < q) (hL : 0 ≤ L)
    (hT : T = 2 * tau)
    (hJ : ∀ r : ℝ, 1 < r → q * Real.log r - L ≤ (2 / Real.pi) * tau * r) :
    Real.pi * q / (Real.exp 1 * Real.exp (L / q)) ≤ T := by
  have hc : (0:ℝ) < 2 / Real.pi := by positivity
  have hbase := jensen_step hq hc hL hJ
  have hC : (0:ℝ) < Real.exp (L / q) := Real.exp_pos _
  have he : (0:ℝ) < Real.exp 1 := Real.exp_pos _
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  have hcπ : (2 / Real.pi) * Real.pi = 2 := by field_simp
  have hX : (2 / Real.pi) * Real.exp 1 * Real.exp (L / q) ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · exact div_ne_zero two_ne_zero hpi
      · exact he.ne'
    · exact hC.ne'
  have hY : Real.exp 1 * Real.exp (L / q) ≠ 0 := mul_ne_zero he.ne' hC.ne'
  have hconv : 2 * q / ((2 / Real.pi) * Real.exp 1 * Real.exp (L / q))
      = Real.pi * q / (Real.exp 1 * Real.exp (L / q)) := by
    rw [div_eq_div_iff hX hY]
    calc (2 * q) * (Real.exp 1 * Real.exp (L / q))
        = ((2 / Real.pi) * Real.pi) * (q * (Real.exp 1 * Real.exp (L / q))) := by
          rw [hcπ]; ring
      _ = Real.pi * q * ((2 / Real.pi) * Real.exp 1 * Real.exp (L / q)) := by ring
  have h2 : 2 * q / ((2 / Real.pi) * Real.exp 1 * Real.exp (L / q)) ≤ T := by
    rw [hT, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hbase zero_le_two
  rwa [hconv] at h2

/-! ## 3. Jensen zero term from Mathlib (report (J)) -/

/-- **Zero term (J), proved.** For `F` analytic on `closedBall 0 R` with
`F 0 ≠ 0`, Mathlib's Jensen formula writes the circle mean as the divisor
sum plus `log‖F 0‖`.  Every summand is nonnegative (analytic ⟹ divisor
nonneg; points of the ball satisfy `R/‖u‖ ≥ 1`), so keeping only the known
zero at `a` gives `q·log(R·‖a‖⁻¹) + log‖F 0‖ ≤ circleAverage`. -/
theorem jensen_zero_term {F : ℂ → ℂ} {R : ℝ} (hR : 1 < R) {a : ℂ} {q : ℤ}
    (hF : AnalyticOnNhd ℂ F (closedBall (0:ℂ) R))
    (h0 : F 0 ≠ 0)
    (ha : a ∈ closedBall (0:ℂ) R) (ha0 : a ≠ 0)
    (hq : q ≤ divisor F (closedBall (0:ℂ) R) a) :
    (q : ℝ) * Real.log (R * ‖a‖⁻¹) + Real.log ‖F 0‖
      ≤ Real.circleAverage (fun z => Real.log ‖F z‖) 0 R := by
  have hRpos : (0:ℝ) < R := lt_trans zero_lt_one hR
  have hR0 : R ≠ 0 := ne_of_gt hRpos
  have hFabs : AnalyticOnNhd ℂ F (closedBall (0:ℂ) |R|) := by
    rwa [abs_of_pos hRpos]
  have hJ := hFabs.circleAverage_log_norm hR0 h0
  rw [abs_of_pos hRpos] at hJ
  set t : ℂ → ℝ := fun u =>
    ((divisor F (closedBall (0:ℂ) R) u : ℤ) : ℝ) * Real.log (R * ‖(0:ℂ) - u‖⁻¹) with ht
  have hJt : Real.circleAverage (fun z => Real.log ‖F z‖) 0 R
      = (∑ᶠ u, t u) + Real.log ‖F 0‖ := hJ
  have hterm : ∀ u : ℂ, (0:ℝ) ≤ t u := by
    intro u
    by_cases huD : (divisor F (closedBall (0:ℂ) R)) u = 0
    · simp [ht, huD]
    · have hDnn : (0:ℝ) ≤ (((divisor F (closedBall (0:ℂ) R)) u : ℤ) : ℝ) := by
        have h1 : (0:ℤ) ≤ (divisor F (closedBall (0:ℂ) R)) u := hF.divisor_nonneg u
        exact_mod_cast h1
      have huCB : u ∈ closedBall (0:ℂ) R := by
        by_contra hmem
        exact huD ((divisor F (closedBall (0:ℂ) R)).apply_eq_zero_of_notMem hmem)
      have hmem := Metric.mem_closedBall.mp huCB
      rw [dist_zero_right] at hmem
      have hu0 : u ≠ 0 := by
        intro hsub
        apply huD
        subst hsub
        have hmem0 : (0:ℂ) ∈ closedBall (0:ℂ) R := by
          rw [Metric.mem_closedBall, dist_self]
          exact hRpos.le
        have hord : analyticOrderAt F 0 = 0 :=
          (hF 0 hmem0).analyticOrderAt_eq_zero.mpr h0
        rw [hF.divisor_apply hmem0, hord]
        rfl
      have hnpos : (0:ℝ) < ‖u‖ := norm_pos_iff.mpr hu0
      have hnorm : ‖(0:ℂ) - u‖ = ‖u‖ := by rw [zero_sub, norm_neg]
      have hge : (1:ℝ) ≤ R * ‖(0:ℂ) - u‖⁻¹ := by
        rw [hnorm, ← div_eq_mul_inv, le_div_iff₀ hnpos, one_mul]
        exact hmem
      have hlog : (0:ℝ) ≤ Real.log (R * ‖(0:ℂ) - u‖⁻¹) := Real.log_nonneg hge
      simp only [ht]
      exact mul_nonneg hDnn hlog
  have hfin : (divisor F (closedBall (0:ℂ) R)).support.Finite :=
    hF.meromorphicOn.divisor_support_finite_of_subset
      (isCompact_closedBall _ _) le_rfl
  obtain ⟨s, hs⟩ := hfin.exists_finset_coe
  have hsub : Function.support t ⊆ ↑(insert a s) := by
    intro u hu
    rw [Function.mem_support] at hu
    have hne : (divisor F (closedBall (0:ℂ) R)) u ≠ 0 := by
      intro hcon
      apply hu
      simp [ht, hcon]
    have hmem : u ∈ (divisor F (closedBall (0:ℂ) R)).support :=
      Function.mem_support.mpr hne
    rw [← hs] at hmem
    exact Finset.mem_insert_of_mem (Finset.mem_coe.mp hmem)
  have hsum : (∑ᶠ u, t u) = ∑ u ∈ insert a s, t u :=
    finsum_eq_sum_of_support_subset _ hsub
  have hsingle : t a ≤ ∑ u ∈ insert a s, t u :=
    Finset.single_le_sum (fun u _ => hterm u) (Finset.mem_insert_self a s)
  have hlognn : (0:ℝ) ≤ Real.log (R * ‖a‖⁻¹) := by
    have hmem : dist a (0:ℂ) ≤ R := Metric.mem_closedBall.mp ha
    rw [dist_zero_right] at hmem
    have hapos : (0:ℝ) < ‖a‖ := norm_pos_iff.mpr ha0
    have hnorm : (1:ℝ) ≤ R * ‖a‖⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hapos, one_mul]
      exact hmem
    exact Real.log_nonneg hnorm
  have h0a : ‖(0:ℂ) - a‖ = ‖a‖ := by rw [zero_sub, norm_neg]
  have hqcast : ((q : ℤ) : ℝ)
      ≤ ((((divisor F (closedBall (0:ℂ) R)) a : ℤ)) : ℝ) := by
    exact_mod_cast hq
  have ha_term : (q : ℝ) * Real.log (R * ‖a‖⁻¹) ≤ t a :=
    calc (q : ℝ) * Real.log (R * ‖a‖⁻¹)
        ≤ ((((divisor F (closedBall (0:ℂ) R)) a : ℤ)) : ℝ)
          * Real.log (R * ‖a‖⁻¹) :=
          mul_le_mul_of_nonneg_right hqcast hlognn
      _ = t a := by simp only [ht, h0a]
  rw [hJt, hsum]
  linarith [hsingle, ha_term]

/-! ## 4. Growth mean from the pointwise bound (report (G)) -/

/-- **Growth mean (G), proved conditional on the pointwise bound.**
From `‖F z‖ ≤ 2·exp(τ·|Im z|)` on the circle, monotonicity of the circle
average plus `∫₀^{2π}|sin| = 4` gives
`circleAverage ≤ log 2 + (2/π)·τ·r`. -/
theorem growth_mean_of_pointwise {F : ℂ → ℂ} {tau r : ℝ} (hr : 0 ≤ r)
    (htau : 0 ≤ tau)
    (hFint : CircleIntegrable (fun z => Real.log ‖F z‖) 0 r)
    (hpt : ∀ z ∈ sphere (0:ℂ) r, ‖F z‖ ≤ 2 * Real.exp (tau * |z.im|)) :
    Real.circleAverage (fun z => Real.log ‖F z‖) 0 r
      ≤ Real.log 2 + (2 / Real.pi) * tau * r := by
  have hGint : CircleIntegrable (fun z : ℂ => Real.log 2 + tau * |z.im|) 0 r := by
    have hGc : Continuous fun th : ℝ =>
        Real.log 2 + tau * |(circleMap (0:ℂ) r th).im| :=
      (continuous_const.add
        ((continuous_const.mul continuous_abs).comp Complex.continuous_im)).comp
        (continuous_circleMap 0 r)
    exact hGc.intervalIntegrable 0 (2 * Real.pi)
  have hmono := Real.circleAverage_mono hFint hGint (by
    intro z hz
    have hzmem : z ∈ sphere (0:ℂ) r := by
      rwa [abs_of_nonneg hr] at hz
    have h1 := hpt z hzmem
    by_cases hFz : ‖F z‖ = 0
    · rw [hFz, Real.log_zero]
      have hnn : (0:ℝ) ≤ tau * |z.im| := mul_nonneg htau (abs_nonneg _)
      have h2pos : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
      linarith
    · have hpos : (0:ℝ) < ‖F z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hFz)
      have h2 : Real.log ‖F z‖ ≤ Real.log (2 * Real.exp (tau * |z.im|)) :=
        Real.log_le_log hpos h1
      rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp] at h2
      linarith [h2])
  have havg : Real.circleAverage (fun z : ℂ => Real.log 2 + tau * |z.im|) 0 r
      = Real.log 2 + (2 / Real.pi) * tau * r := by
    have hInt : (fun θ : ℝ => (fun z : ℂ => Real.log 2 + tau * |z.im|)
        (circleMap (0:ℂ) r θ))
        = fun θ : ℝ => Real.log 2 + tau * (r * |Real.sin θ|) := by
      funext θ
      show Real.log 2 + tau * |(circleMap (0:ℂ) r θ).im|
        = Real.log 2 + tau * (r * |Real.sin θ|)
      rw [circleMap_zero_im, abs_mul, abs_of_nonneg hr]
    rw [Real.circleAverage_def, smul_eq_mul, hInt]
    have hint1 : IntervalIntegrable (fun _ : ℝ => Real.log 2) volume
        (0:ℝ) (2 * Real.pi) := intervalIntegrable_const
    have hint2 : IntervalIntegrable (fun θ : ℝ => tau * (r * |Real.sin θ|)) volume
        (0:ℝ) (2 * Real.pi) :=
      ((continuous_const.mul
        (continuous_const.mul Real.continuous_sin.abs)).intervalIntegrable _ _)
    have hsplit := intervalIntegral.integral_add hint1 hint2
    have hconst : (∫ _ : ℝ in (0:ℝ)..2 * Real.pi, Real.log 2)
        = 2 * Real.pi * Real.log 2 := by
      rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
    have hmul : (∫ θ : ℝ in (0:ℝ)..2 * Real.pi, tau * (r * |Real.sin θ|))
        = tau * r * 4 := by
      have e1 : (fun θ : ℝ => tau * (r * |Real.sin θ|))
          = fun θ : ℝ => (tau * r) * |Real.sin θ| := by
        funext θ; ring
      rw [e1, intervalIntegral.integral_const_mul, integral_abs_sin_zero_two_pi]
    rw [hsplit, hconst, hmul, mul_add]
    have h2pi : (2:ℝ) * Real.pi ≠ 0 := ne_of_gt Real.two_pi_pos
    congr 1
    · rw [← mul_assoc, mul_comm ((2 * Real.pi)⁻¹) (2 * Real.pi),
        mul_inv_cancel₀ h2pi, one_mul]
    · rw [div_eq_mul_inv, mul_inv]
      ring
  linarith [hmono, havg]

/-! ## 5. Carrier extension (tree machinery: `ExpSum.h_moments`) -/

/-- Finite exponential sums extend to entire functions. -/
theorem expSum_differentiable {ι : Type} [Fintype ι] (c : ι → ℂ) (ν : ι → ℝ) :
    Differentiable ℂ (fun z : ℂ => ∑ i, Complex.exp ((ν i : ℂ) * Complex.I * z) * c i) := by
  apply Differentiable.fun_sum
  intro i _
  apply Differentiable.mul_const
  apply Differentiable.cexp
  exact (differentiable_const _).mul differentiable_id

/-- The carrier's exp-sum data from `h_moments`, repackaged with `cost`. -/
theorem carrier_extend (N : ℕ) (φ : ℝ) (L : ℕ) (α θ : Fin L → ℝ)
    (hAdm : Admissible N φ L α θ) :
    ∃ (ι : Type) (_ : Fintype ι) (c : ι → ℂ) (ν : ι → ℝ),
      (∀ i, |ν i| ≤ cost θ / 2) ∧
      (∀ lam : ℝ, ((h L α θ lam : ℝ):ℂ)
        = ∑ i, Complex.exp (((ν i * lam : ℝ):ℂ) * Complex.I) * c i) := by
  obtain ⟨ι, hι, c, ν, hν, hrep, -⟩ := h_moments N φ L α θ hAdm
  exact ⟨ι, hι, c, ν, fun i => hν i, hrep⟩

/-! ## 6. Theorem J (general φ) -/

/-- **Theorem J (route-K K2), general-φ form.** For `0 < φ ≤ π`, every
order-`N` admissible sequence with `q = 2N+2`, `s = 2 sin²(φ/4)` satisfies
`π * q / (e * (2/s)^((1:ℝ)/q)) ≤ T`.

The two analytic inputs `jord` (divisor sees the `q`-fold zero at `1`)
and `jgrow` (pointwise PL-type growth) are explicit hypotheses; see the
module docstring for the bridge boundary. -/
theorem jensen_rung (N : ℕ) {L : ℕ} {α θ : Fin L → ℝ} {φ : ℝ}
    (hφ0 : 0 < φ) (hφπ : φ ≤ Real.pi)
    (hAdm : Admissible N φ L α θ)
    (H : ℂ → ℂ) (hHdiff : Differentiable ℂ H)
    (hHreal : ∀ lam : ℝ, H lam = ((h L α θ lam : ℝ) : ℂ))
    (jord : ∀ R : ℝ, 1 < R → ((2 * N + 2 : ℕ) : ℤ)
      ≤ divisor H (closedBall (0:ℂ) R) 1)
    (jgrow : ∀ z : ℂ, ‖H z‖ ≤ 2 * Real.exp ((cost θ / 2) * |z.im|)) :
    Real.pi * ((2 * N + 2 : ℕ):ℝ)
      / (Real.exp 1 * (2 / (2 * Real.sin (φ / 4) ^ 2)) ^ ((1:ℝ) / ((2 * N + 2 : ℕ):ℝ)))
      ≤ cost θ := by
  set s : ℝ := 2 * Real.sin (φ / 4) ^ 2 with hs
  have hsinpos : (0:ℝ) < Real.sin (φ / 4) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hφ0]) (by linarith [hφπ, Real.pi_pos])
  have hspos : (0:ℝ) < s := by
    rw [hs]
    exact mul_pos (by norm_num) (sq_pos_of_ne_zero (ne_of_gt hsinpos))
  have hsin1 : Real.sin (φ / 4) ^ 2 ≤ 1 :=
    (sq_le_one_iff_abs_le_one _).mpr
      (abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩)
  have hsle : s ≤ 2 := by
    rw [hs]
    linarith [hsin1]
  have hscos : s = 1 - Real.cos (φ / 2) := by
    rw [hs, Real.sin_sq_eq_half_sub]
    have h2 : 2 * (φ / 4) = φ / 2 := by ring
    rw [h2]
    ring
  have hU1 : U L α θ 1 = Ztgt φ := hAdm.2.1
  have hh0 : s ≤ h L α θ 0 := by
    rw [hscos]
    exact h_zero_ge φ hφ0.le hφπ L α θ hU1
  have hH0 : H 0 = ((h L α θ 0 : ℝ) : ℂ) := by
    have h := hHreal 0
    simpa using h
  have hnormH0 : s ≤ ‖H 0‖ := by
    rw [hH0, Complex.norm_real, Real.norm_eq_abs]
    exact le_trans hh0 (le_abs_self _)
  have hH0ne : H 0 ≠ 0 := by
    intro hcon
    rw [hcon, norm_zero] at hnormH0
    linarith [hspos, hnormH0]
  have hFana : ∀ R : ℝ, AnalyticOnNhd ℂ H (closedBall (0:ℂ) R) :=
    fun R x _ => hHdiff.analyticAt x
  have htau_nn : (0:ℝ) ≤ cost θ / 2 := by
    apply div_nonneg _ zero_le_two
    exact Finset.sum_nonneg fun j _ => hAdm.1 j
  set tau : ℝ := cost θ / 2 with htau
  have htau_nn' : (0:ℝ) ≤ tau := by rwa [htau]
  set Lv : ℝ := Real.log (2 / s) with hLv
  have hLnn : (0:ℝ) ≤ Lv := by
    rw [hLv]
    apply Real.log_nonneg
    rw [le_div_iff₀ hspos, one_mul]
    exact hsle
  have hqpos : (0:ℝ) < ((2 * N + 2 : ℕ):ℝ) := by
    have h : 0 < 2 * N + 2 := by omega
    exact Nat.cast_pos.mpr h
  have hJ : ∀ r : ℝ, 1 < r →
      ((2 * N + 2 : ℕ):ℝ) * Real.log r - Lv ≤ (2 / Real.pi) * tau * r := by
    intro r hr
    have hRpos : 0 < r := lt_trans zero_lt_one hr
    have hmem1 : (1:ℂ) ∈ closedBall (0:ℂ) r := by
      rw [Metric.mem_closedBall, dist_zero_right, norm_one]
      exact hr.le
    have hbridge := jensen_zero_term hr (hFana r) hH0ne hmem1 one_ne_zero (jord r hr)
    rw [norm_one, inv_one, mul_one] at hbridge
    have hFint : CircleIntegrable (fun z => Real.log ‖H z‖) 0 r := by
      have hsub : sphere (0:ℂ) |r| ⊆ closedBall (0:ℂ) r := by
        rw [abs_of_nonneg hRpos.le]
        exact Metric.sphere_subset_closedBall
      exact ((hFana r).mono hsub).meromorphicOn.circleIntegrable_log_norm
    have hpt : ∀ z ∈ sphere (0:ℂ) r,
        ‖H z‖ ≤ 2 * Real.exp (tau * |z.im|) := by
      intro z hz
      exact jgrow z
    have hgrow := growth_mean_of_pointwise hRpos.le htau_nn' hFint hpt
    have hlogH0 : Real.log s ≤ Real.log ‖H 0‖ := Real.log_le_log hspos hnormH0
    have hlog2s : Real.log 2 - Real.log s = Lv := by
      rw [hLv, Real.log_div (by norm_num) (ne_of_gt hspos)]
    have hqcast : ((((2 * N + 2 : ℕ) : ℤ)):ℝ) = ((2 * N + 2 : ℕ):ℝ) :=
      Int.cast_natCast _
    rw [hqcast] at hbridge
    linarith [hbridge, hgrow, hlogH0, hlog2s]
  have hT : cost θ = 2 * tau := by rw [htau]; ring
  have hstep := jensen_indicator_step hqpos hLnn hT hJ
  have hexp : Real.exp (Lv / ((2 * N + 2 : ℕ):ℝ))
      = (2 / s) ^ ((1:ℝ) / ((2 * N + 2 : ℕ):ℝ)) := by
    rw [hLv, Real.rpow_def_of_pos (by positivity : (0:ℝ) < 2 / s)]
    congr 1
    ring
  rw [hexp] at hstep
  exact hstep

/-- **Theorem J at `φ = π`**: `s = 1`, so `π * q / (e * 2^{1/q}) ≤ T`. -/
theorem jensen_rung_pi (N : ℕ) {L : ℕ} {α θ : Fin L → ℝ}
    (hAdm : Admissible N Real.pi L α θ)
    (H : ℂ → ℂ) (hHdiff : Differentiable ℂ H)
    (hHreal : ∀ lam : ℝ, H lam = ((h L α θ lam : ℝ) : ℂ))
    (jord : ∀ R : ℝ, 1 < R → ((2 * N + 2 : ℕ) : ℤ)
      ≤ divisor H (closedBall (0:ℂ) R) 1)
    (jgrow : ∀ z : ℂ, ‖H z‖ ≤ 2 * Real.exp ((cost θ / 2) * |z.im|)) :
    Real.pi * ((2 * N + 2 : ℕ):ℝ)
      / (Real.exp 1 * (2:ℝ) ^ ((1:ℝ) / ((2 * N + 2 : ℕ):ℝ))) ≤ cost θ := by
  have hs1 : (2:ℝ) * Real.sin (Real.pi / 4) ^ 2 = 1 := by
    rw [Real.sin_pi_div_four, div_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have hmain := jensen_rung N Real.pi_pos le_rfl hAdm H hHdiff hHreal jord jgrow
  rw [hs1, div_one] at hmain
  exact hmain

/-! ## 7. Liminf coefficient `2π/e` -/

/-- The per-`N` bound divided by `N` tends to `2π/e`: this is the
`liminf T/N ≥ 2π/e` coefficient of Theorem J. -/
theorem jensen_ratio_tendsto :
    Tendsto (fun N : ℕ => (Real.pi * ((2 * N + 2 : ℕ):ℝ)
      / (Real.exp 1 * (2:ℝ) ^ ((1:ℝ) / ((2 * N + 2 : ℕ):ℝ)))) / (N:ℝ))
      atTop (𝓝 (2 * Real.pi / Real.exp 1)) := by
  have hq : Tendsto (fun N : ℕ => ((2 * N + 2 : ℕ):ℝ)) atTop atTop := by
    rw [Filter.tendsto_atTop]
    intro b
    filter_upwards [eventually_ge_atTop (max 0 ⌈b⌉₊)] with N hN
    have h1 : (N:ℝ) ≤ ((2 * N + 2 : ℕ):ℝ) := by
      have h : N ≤ 2 * N + 2 := by omega
      exact_mod_cast h
    have h2 : b ≤ (N:ℝ) := by
      have hle : ⌈b⌉₊ ≤ N := le_trans (le_max_right _ _) hN
      have hc : ((⌈b⌉₊ : ℕ):ℝ) ≤ (N:ℝ) := by exact_mod_cast hle
      exact le_trans (Nat.le_ceil b) hc
    linarith [h1, h2]
  have h1q : Tendsto (fun N : ℕ => (1:ℝ) / ((2 * N + 2 : ℕ):ℝ)) atTop (𝓝 0) := by
    refine squeeze_zero (fun N => ?_) (fun N => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    · positivity
    · have hpos : (0:ℝ) < (N:ℝ) + 1 := by positivity
      have hle : ((N:ℝ) + 1) ≤ ((2 * N + 2 : ℕ):ℝ) := by
        have h : N + 1 ≤ 2 * N + 2 := by omega
        have e : ((N + 1 : ℕ):ℝ) = (N:ℝ) + 1 := by push_cast; ring
        rw [← e]
        exact_mod_cast h
      exact one_div_le_one_div_of_le hpos hle
  have hexp0 : Tendsto (fun N : ℕ => (2:ℝ) ^ ((1:ℝ) / ((2 * N + 2 : ℕ):ℝ)))
      atTop (𝓝 1) := by
    have e : ∀ N : ℕ, (2:ℝ) ^ ((1:ℝ) / ((2 * N + 2 : ℕ):ℝ))
        = Real.exp (Real.log 2 * ((1:ℝ) / ((2 * N + 2 : ℕ):ℝ))) := by
      intro N
      have hbase : (0:ℝ) < 2 := by norm_num
      rw [Real.rpow_def_of_pos hbase]
    simp only [e]
    have hlim : Tendsto (fun N : ℕ => Real.log 2 * ((1:ℝ) / ((2 * N + 2 : ℕ):ℝ)))
        atTop (𝓝 0) := by
      have h2 : Tendsto (fun _ : ℕ => Real.log 2) atTop (𝓝 (Real.log 2)) :=
        tendsto_const_nhds
      have h3 := h2.mul h1q
      simpa using h3
    have h2 := (Real.continuous_exp.tendsto 0).comp hlim
    rwa [Real.exp_zero] at h2
  have hratio : Tendsto (fun N : ℕ => ((2 * N + 2 : ℕ):ℝ) / (N:ℝ)) atTop (𝓝 2) := by
    have hg : Tendsto (fun N : ℕ => (2:ℝ) + 2 * ((1:ℝ) / (N:ℝ))) atTop (𝓝 2) := by
      have h1N : Tendsto (fun N : ℕ => (1:ℝ) / (N:ℝ)) atTop (𝓝 0) :=
        tendsto_one_div_atTop_nhds_zero_nat
      have h2c : Tendsto (fun _ : ℕ => (2:ℝ)) atTop (𝓝 2) := tendsto_const_nhds
      have h2 := h2c.mul h1N
      have h3 : Tendsto (fun N : ℕ => (2:ℝ) + 2 * ((1:ℝ) / (N:ℝ)))
          atTop (𝓝 (2 + 2 * 0)) := by
        have h2c' : Tendsto (fun _ : ℕ => (2:ℝ)) atTop (𝓝 2) := tendsto_const_nhds
        exact h2c'.add h2
      simpa using h3
    apply Filter.Tendsto.congr' _ hg
    filter_upwards [eventually_ne_atTop 0] with N hN
    show (2:ℝ) + 2 * (1 / (N:ℝ)) = ((2 * N + 2 : ℕ):ℝ) / (N:ℝ)
    have hNc : (N:ℝ) ≠ 0 := by exact_mod_cast hN
    push_cast
    field_simp
  have efin : (fun N : ℕ => (Real.pi * ((2 * N + 2 : ℕ):ℝ)
      / (Real.exp 1 * (2:ℝ) ^ ((1:ℝ) / ((2 * N + 2 : ℕ):ℝ)))) / (N:ℝ))
      = fun N : ℕ => (Real.pi / Real.exp 1) * (((2 * N + 2 : ℕ):ℝ) / (N:ℝ))
        * ((((2:ℝ) ^ ((1:ℝ) / ((2 * N + 2 : ℕ):ℝ))))⁻¹) := by
    funext N
    have hEpos : (0:ℝ) < (2:ℝ) ^ ((1:ℝ) / ((2 * N + 2 : ℕ):ℝ)) := by
      positivity
    have hE := ne_of_gt hEpos
    have he := Real.exp_ne_zero 1
    by_cases hN0 : (N:ℝ) = 0
    · simp [hN0]
    · field_simp
  rw [efin]
  have hpi2 : Tendsto (fun _ : ℕ => Real.pi / Real.exp 1) atTop
      (𝓝 (Real.pi / Real.exp 1)) := tendsto_const_nhds
  have hlim := (hpi2.mul hratio).mul (hexp0.inv₀ one_ne_zero)
  have htarget : (Real.pi / Real.exp 1) * 2 * (1:ℝ)⁻¹
      = 2 * Real.pi / Real.exp 1 := by
    rw [inv_one, mul_one]
    ring
  rwa [htarget] at hlim

end RobustZ
