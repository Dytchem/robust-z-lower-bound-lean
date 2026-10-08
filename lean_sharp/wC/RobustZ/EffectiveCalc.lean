/-
Copyright (c) 2025 RobustZ contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Effective real-analysis estimates for the sharpened contour-shift mechanism

This file collects the *purely real-analytic* input of the effective (sharpened)
argument.  Everything lives on `ℝ` and uses only `Real.log`, `Real.sqrt`,
`Real.exp` and `Real.rpow`.

The three objects are

* `mu ρ = log ((1 + √(1-ρ²))/ρ) - √(1-ρ²)` — the exponent gained by shifting the
  contour from `ℝ` to the line `Im = μ`, for `0 < ρ < 1`;
* `D0 ρ = (1 + 4/(1 - ρ/(1+√(1-ρ²)))) · ((1+√(1-ρ²))/ρ)` — the explicit constant
  of the contour-shift error bound;
* `rho q = 1 - 2 (log q / q)^{2/3}` — the radius of the sharpened mechanism.

Main results:

* `mu_lower`  : for `1/2 ≤ ρ < 1`,  `(9/10) (1-ρ)^{3/2} ≤ mu ρ`;
* `mu_lower_sharp` : for `1/2 ≤ ρ < 1`,  `(47/50) (1-ρ)^{3/2} ≤ mu ρ`
  (the asymptotic constant is `2√2/3 = 0.9428…`);
* `D0_le`     : for `1/2 ≤ ρ < 1`,  `D0 ρ ≤ 25/(1-ρ)`;
* `D0_le_eight`: for `3/4 ≤ ρ < 1`, `D0 ρ ≤ 8/(1-ρ)`;
* `D0_le_inv_sqrt`: for `3/4 ≤ ρ < 1`, `D0 ρ ≤ 13/√(1-ρ)` (the form the criterion uses);
* `criterion` : for `q ≥ 10^4`,
  `D0 (rho q) * exp (-(q * mu (rho q))) < √(rho q) / (100 q)`;
* `criterion_param` : for every `100 ≤ C` and `100 C^{7/6} ≤ q`,
  `D0 (rho q) * exp (-(q * mu (rho q))) < √(rho q) / (C q)`;
* `criterion_param_sharp` : for every `100 ≤ C` and `max (10^4) (7 C^{6/7}) ≤ q`
  (the same statement with a much better threshold in `C`);
* `criterion_param_max` : for **every** `C > 0` and `max (10^4) (7 (max C 100)^{6/7}) ≤ q`
  (unified: the threshold is `10^4` for `C ≤ 4794` and `7 C^{6/7}` beyond);
* `criterion_C4500` : for `q ≥ 10^4`, the criterion with `C = 4500`;
* `rho_ge_half`, `rho_ge_three_quarters`, `rho_lt_one` : the `q ≥ 10^4` side conditions.

The chain behind the criterion is
`D0 (rho q) ≤ (325/49) q^{1/3}` and `exp (-(q μ(rho q))) ≤ q^{-5/2}`, hence
`LHS ≤ (325/49) q^{-13/6}`, which beats `√(rho q)/(C q) ≥ (7/10)/(C q)` as soon as
`343 q^{7/6} > 3250 C`.
-/
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

noncomputable section

namespace RobustZ

open Real

/-! ## The three functions -/

/-- `μ(ρ) = log ((1+√(1-ρ²))/ρ) - √(1-ρ²)`: the contour-shift exponent. -/
def mu (ρ : ℝ) : ℝ :=
  Real.log ((1 + Real.sqrt (1 - ρ ^ 2)) / ρ) - Real.sqrt (1 - ρ ^ 2)

/-- `D0 ρ`: the explicit constant of the contour-shift error bound
`|error| ≤ D0 ρ · e^{-q μ(ρ)}`. -/
def D0 (ρ : ℝ) : ℝ :=
  (1 + 4 / (1 - ρ / (1 + Real.sqrt (1 - ρ ^ 2)))) * ((1 + Real.sqrt (1 - ρ ^ 2)) / ρ)

/-- `rho q = 1 - 2 (log q / q)^{2/3}`: the radius of the sharpened mechanism. -/
def rho (q : ℝ) : ℝ := 1 - 2 * (Real.log q / q) ^ ((2 : ℝ) / 3)

/-! ## Elementary bounds for `log` -/

/-- `log q ≤ 2 √q` for `q ≥ 1`. -/
private lemma log_le_two_sqrt (q : ℝ) (hq : 1 ≤ q) : Real.log q ≤ 2 * Real.sqrt q := by
  have hq0 : 0 < q := lt_of_lt_of_le one_pos hq
  have hs0 : 0 < Real.sqrt q := Real.sqrt_pos_of_pos hq0
  have h1 : Real.log q = 2 * Real.log (Real.sqrt q) := by
    rw [Real.log_sqrt (le_of_lt hq0)]; ring
  have h2 : Real.log (Real.sqrt q) ≤ Real.sqrt q - 1 := Real.log_le_sub_one_of_pos hs0
  linarith

/-! ## The artanh series bound

`log ((1+s)/(1-s)) ≥ 2s + 2s³/3 + 2s⁵/5` for `0 ≤ s ≤ 7/8`.  This is proved by
montonicity of `s ↦ log ((1+s)/(1-s)) - 2s - 2s³/3 - 2s⁵/5`, whose derivative is
`2s⁶/(1-s²) ≥ 0`. -/

private def Fser (x : ℝ) : ℝ :=
  Real.log ((1 + x) / (1 - x)) - (2 * x + (2 / 3) * x ^ 3 + (2 / 5) * x ^ 5 + (2 / 7) * x ^ 7)

private lemma hasDerivAt_Fser (x : ℝ) (hx : -1 < x) (hx1 : x < 1) :
    HasDerivAt Fser (2 * x ^ 8 / (1 - x ^ 2)) x := by
  have h1x : 1 - x ≠ 0 := by linarith
  have h1px : 1 + x ≠ 0 := by linarith
  have hx2 : 1 - x ^ 2 ≠ 0 := by
    have h : 1 - x ^ 2 = (1 - x) * (1 + x) := by ring
    rw [h]; exact mul_ne_zero h1x h1px
  have hlog : HasDerivAt (fun y : ℝ => Real.log ((1 + y) / (1 - y))) (2 / (1 - x ^ 2)) x := by
    have h1 : HasDerivAt (fun y : ℝ => (1 : ℝ) + y) 1 x := (hasDerivAt_id x).const_add 1
    have h2 : HasDerivAt (fun y : ℝ => (1 : ℝ) - y) (-1) x := (hasDerivAt_id x).const_sub 1
    have hne : ((fun y : ℝ => (1 + y) / (1 - y)) x) ≠ 0 := by
      show (1 + x) / (1 - x) ≠ 0
      exact div_ne_zero h1px h1x
    have h := (h1.div h2 h1x).log hne
    have hfun : ((fun y : ℝ => (1 + y)) / fun y : ℝ => (1 - y))
        = fun y : ℝ => (1 + y) / (1 - y) := rfl
    rw [hfun] at h
    convert h using 1
    field_simp
    ring
  have hpoly : HasDerivAt (fun y : ℝ => 2 * y + (2 / 3) * y ^ 3 + (2 / 5) * y ^ 5 + (2 / 7) * y ^ 7)
      (2 + 2 * x ^ 2 + 2 * x ^ 4 + 2 * x ^ 6) x := by
    have h1 : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
      simpa using (hasDerivAt_id x).const_mul (2 : ℝ)
    have h3 : HasDerivAt (fun y : ℝ => (2 / 3) * y ^ 3) ((2 / 3) * (3 * x ^ 2)) x := by
      simpa using ((hasDerivAt_id x).pow 3).const_mul ((2 : ℝ) / 3)
    have h5 : HasDerivAt (fun y : ℝ => (2 / 5) * y ^ 5) ((2 / 5) * (5 * x ^ 4)) x := by
      simpa using ((hasDerivAt_id x).pow 5).const_mul ((2 : ℝ) / 5)
    have h7 : HasDerivAt (fun y : ℝ => (2 / 7) * y ^ 7) ((2 / 7) * (7 * x ^ 6)) x := by
      simpa using ((hasDerivAt_id x).pow 7).const_mul ((2 : ℝ) / 7)
    have h := ((h1.add h3).add h5).add h7
    convert h using 1
    ring
  have h := hlog.sub hpoly
  unfold Fser
  convert h using 1
  field_simp
  ring

/-- The truncated artanh series bound. -/
private lemma log_series_aux (s : ℝ) (h0 : 0 ≤ s) (h1 : s ≤ 7 / 8) :
    2 * s + (2 / 3) * s ^ 3 + (2 / 5) * s ^ 5 + (2 / 7) * s ^ 7 ≤ Real.log ((1 + s) / (1 - s)) := by
  have hD : Convex ℝ (Set.Icc (0 : ℝ) (7 / 8)) := convex_Icc _ _
  have hcont : ContinuousOn Fser (Set.Icc (0 : ℝ) (7 / 8)) := by
    unfold Fser
    refine ContinuousOn.sub ?_ (by fun_prop)
    refine ContinuousOn.log ?_ ?_
    · refine ContinuousOn.div ?_ ?_ ?_
      · exact continuousOn_const.add continuousOn_id
      · exact continuousOn_const.sub continuousOn_id
      · intro x hx
        simp only [Set.mem_Icc] at hx
        have h1x : 0 < 1 - x := by linarith [hx.2]
        exact ne_of_gt h1x
    · intro x hx
      simp only [Set.mem_Icc] at hx
      have h1x : 0 < 1 - x := by linarith [hx.2]
      have h1px : 0 < 1 + x := by linarith [hx.1]
      exact ne_of_gt (div_pos h1px h1x)
  have hderiv : ∀ x ∈ interior (Set.Icc (0 : ℝ) (7 / 8)),
      HasDerivWithinAt Fser (2 * x ^ 8 / (1 - x ^ 2)) (interior (Set.Icc (0 : ℝ) (7 / 8))) x := by
    intro x hx
    rw [interior_Icc] at hx
    exact (hasDerivAt_Fser x (by linarith [hx.1]) (by linarith [hx.2])).hasDerivWithinAt
  have hnonneg : ∀ x ∈ interior (Set.Icc (0 : ℝ) (7 / 8)), 0 ≤ 2 * x ^ 8 / (1 - x ^ 2) := by
    intro x hx
    rw [interior_Icc] at hx
    have hx2 : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
    positivity
  have hmono := monotoneOn_of_hasDerivWithinAt_nonneg hD hcont hderiv hnonneg
  have hmem0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (7 / 8) := by norm_num
  have hmem : s ∈ Set.Icc (0 : ℝ) (7 / 8) := ⟨h0, h1⟩
  have hres := hmono hmem0 hmem h0
  have hF0 : Fser 0 = 0 := by simp [Fser]
  rw [hF0] at hres
  simp only [Fser] at hres
  linarith [hres]

/-! ## Numeric `rpow` helper -/

/-- If `y² ≤ x³` and `x, y ≥ 0` then `y ≤ x^{3/2}`. -/
private lemma le_rpow_three_halves {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (h : y ^ 2 ≤ x ^ 3) :
    y ≤ x ^ (3 / 2 : ℝ) := by
  have hx' : 0 ≤ x ^ (3 / 2 : ℝ) := Real.rpow_nonneg hx _
  have hsq : (x ^ (3 / 2 : ℝ)) ^ 2 = x ^ 3 := by
    rw [← Real.rpow_natCast (x ^ (3 / 2 : ℝ)) 2, ← Real.rpow_mul hx]
    norm_num
  have h2 : y ^ 2 ≤ (x ^ (3 / 2 : ℝ)) ^ 2 := by rw [hsq]; exact h
  have h3 : |y| ≤ |x ^ (3 / 2 : ℝ)| := sq_le_sq.mp h2
  rwa [abs_of_nonneg hy, abs_of_nonneg hx'] at h3

/-! ## The lower bound for `mu` -/

/-- `mu ρ ≥ s³/3 + s⁵/5` where `s = √(1-ρ²)`. -/
private lemma mu_ge_series (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hρ2 : 1 / 2 ≤ ρ) :
    (Real.sqrt (1 - ρ ^ 2)) ^ 3 / 3 + (Real.sqrt (1 - ρ ^ 2)) ^ 5 / 5
      + (Real.sqrt (1 - ρ ^ 2)) ^ 7 / 7 ≤ mu ρ := by
  set s := Real.sqrt (1 - ρ ^ 2) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = 1 - ρ ^ 2 := by
    rw [hs, Real.sq_sqrt]; nlinarith
  have hs_lt1 : s < 1 := by nlinarith [hs0, hs2, hρ0]
  have hs_le : s ≤ 7 / 8 := by
    have h2 : s ^ 2 ≤ (7 / 8 : ℝ) ^ 2 := by rw [hs2]; nlinarith
    nlinarith [hs0, h2]
  have hρne : ρ ≠ 0 := ne_of_gt hρ0
  have h1s : 1 - s ≠ 0 := by linarith
  have h1ps : 1 + s ≠ 0 := by linarith
  have hsq : ((1 + s) / ρ) ^ 2 = (1 + s) / (1 - s) := by
    field_simp
    nlinarith [hs2]
  have hlog2 : Real.log ((1 + s) / (1 - s)) = 2 * Real.log ((1 + s) / ρ) := by
    rw [← hsq, Real.log_pow]
    norm_num
  have hser := log_series_aux s hs0 hs_le
  rw [hlog2] at hser
  have hmu : mu ρ = Real.log ((1 + s) / ρ) - s := by rw [mu, ← hs]
  rw [hmu]
  linarith

/-- **(I)** For `1/2 ≤ ρ < 1`: `(9/10)(1-ρ)^{3/2} ≤ mu ρ`.

(Asymptotically `mu(1-ε) = (2√2/3) ε^{3/2} = 0.9428… ε^{3/2}`, so the constant `9/10`
is within `5%` of optimal; it comes from the three-term artanh series bound
`mu ρ ≥ s³/3 + s⁵/5 + s⁷/7`, `s = √(1-ρ²)`, together with `1-ρ = s²/(1+ρ)`.) -/
theorem mu_lower (ρ : ℝ) (h1 : 1 / 2 ≤ ρ) (h2 : ρ < 1) :
    (9 / 10) * (1 - ρ) ^ (3 / 2 : ℝ) ≤ mu ρ := by
  have hρ0 : 0 < ρ := by linarith
  set s := Real.sqrt (1 - ρ ^ 2) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = 1 - ρ ^ 2 := by
    rw [hs, Real.sq_sqrt]; nlinarith
  have hseries := mu_ge_series ρ hρ0 h2 h1
  have h1p : 0 < 1 + ρ := by linarith
  have hε : 1 - ρ = s ^ 2 / (1 + ρ) := by
    field_simp
    nlinarith [hs2]
  have hrpow : (1 - ρ) ^ (3 / 2 : ℝ) = s ^ 3 / (1 + ρ) ^ (3 / 2 : ℝ) := by
    rw [hε, Real.div_rpow (sq_nonneg s) (le_of_lt h1p)]
    congr 1
    rw [← Real.rpow_natCast s 2, ← Real.rpow_mul hs0]
    norm_num
  rw [hrpow]
  have hkey : (9 : ℝ) / 10 ≤ (1 / 3 + s ^ 2 / 5 + s ^ 4 / 7) * (1 + ρ) ^ (3 / 2 : ℝ) := by
    rcases le_or_gt ρ (3 / 5) with hreg | hreg
    · have hs2' : (16 : ℝ) / 25 ≤ s ^ 2 := by rw [hs2]; nlinarith
      have hf : (6823 : ℝ) / 13125 ≤ 1 / 3 + s ^ 2 / 5 + s ^ 4 / 7 := by nlinarith [hs2', hs0]
      have hp : (9 : ℝ) / 5 ≤ (1 + ρ) ^ (3 / 2 : ℝ) :=
        le_trans (le_rpow_three_halves (x := (3 : ℝ) / 2) (y := (9 : ℝ) / 5)
          (by norm_num) (by norm_num) (by norm_num))
          (Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num))
      have hm := mul_le_mul hf hp (by norm_num) (by positivity)
      linarith
    · rcases le_or_gt ρ (7 / 10) with hreg2 | hreg2
      · have hs2' : (51 : ℝ) / 100 ≤ s ^ 2 := by rw [hs2]; nlinarith
        have hf : (99223 : ℝ) / 210000 ≤ 1 / 3 + s ^ 2 / 5 + s ^ 4 / 7 := by nlinarith [hs2', hs0]
        have hp : (2 : ℝ) ≤ (1 + ρ) ^ (3 / 2 : ℝ) :=
          le_trans (le_rpow_three_halves (x := (8 : ℝ) / 5) (y := 2)
            (by norm_num) (by norm_num) (by norm_num))
            (Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num))
        have hm := mul_le_mul hf hp (by norm_num) (by positivity)
        linarith
      · rcases le_or_gt ρ (4 / 5) with hreg3 | hreg3
        · have hs2' : (9 : ℝ) / 25 ≤ s ^ 2 := by rw [hs2]; nlinarith
          have hf : (5563 : ℝ) / 13125 ≤ 1 / 3 + s ^ 2 / 5 + s ^ 4 / 7 := by nlinarith [hs2', hs0]
          have hp : (11 : ℝ) / 5 ≤ (1 + ρ) ^ (3 / 2 : ℝ) :=
            le_trans (le_rpow_three_halves (x := (17 : ℝ) / 10) (y := (11 : ℝ) / 5)
              (by norm_num) (by norm_num) (by norm_num))
              (Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num))
          have hm := mul_le_mul hf hp (by norm_num) (by positivity)
          linarith
        · rcases le_or_gt ρ (9 / 10) with hreg4 | hreg4
          · have hs2' : (19 : ℝ) / 100 ≤ s ^ 2 := by rw [hs2]; nlinarith
            have hf : (79063 : ℝ) / 210000 ≤ 1 / 3 + s ^ 2 / 5 + s ^ 4 / 7 := by
              nlinarith [hs2', hs0]
            have hp : (12 : ℝ) / 5 ≤ (1 + ρ) ^ (3 / 2 : ℝ) :=
              le_trans (le_rpow_three_halves (x := (9 : ℝ) / 5) (y := (12 : ℝ) / 5)
                (by norm_num) (by norm_num) (by norm_num))
                (Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num))
            have hm := mul_le_mul hf hp (by norm_num) (by positivity)
            linarith
          · rcases le_or_gt ρ (19 / 20) with hreg5 | hreg5
            · have hs2' : (39 : ℝ) / 400 ≤ s ^ 2 := by rw [hs2]; nlinarith
              have hf : (1190083 : ℝ) / 3360000 ≤ 1 / 3 + s ^ 2 / 5 + s ^ 4 / 7 := by
                nlinarith [hs2', hs0]
              have hp : (13 : ℝ) / 5 ≤ (1 + ρ) ^ (3 / 2 : ℝ) :=
                le_trans (le_rpow_three_halves (x := (19 : ℝ) / 10) (y := (13 : ℝ) / 5)
                  (by norm_num) (by norm_num) (by norm_num))
                  (Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num))
              have hm := mul_le_mul hf hp (by norm_num) (by positivity)
              linarith
            · have hf : (1 : ℝ) / 3 ≤ 1 / 3 + s ^ 2 / 5 + s ^ 4 / 7 := by
                nlinarith [hs0, sq_nonneg s]
              have hp : (68 : ℝ) / 25 ≤ (1 + ρ) ^ (3 / 2 : ℝ) :=
                le_trans (le_rpow_three_halves (x := (39 : ℝ) / 20) (y := (68 : ℝ) / 25)
                  (by norm_num) (by norm_num) (by norm_num))
                  (Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num))
              have hm := mul_le_mul hf hp (by norm_num) (by positivity)
              linarith
  have h1p32 : 0 < (1 + ρ) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos h1p _
  have hdiv : (9 : ℝ) / 10 / (1 + ρ) ^ (3 / 2 : ℝ) ≤ 1 / 3 + s ^ 2 / 5 + s ^ 4 / 7 := by
    rw [div_le_iff₀ h1p32]; linarith
  have hs3 : 0 ≤ s ^ 3 := by positivity
  calc (9 / 10) * (s ^ 3 / (1 + ρ) ^ (3 / 2 : ℝ))
      = s ^ 3 * ((9 : ℝ) / 10 / (1 + ρ) ^ (3 / 2 : ℝ)) := by ring
    _ ≤ s ^ 3 * (1 / 3 + s ^ 2 / 5 + s ^ 4 / 7) :=
        mul_le_mul_of_nonneg_left hdiv hs3
    _ = s ^ 3 / 3 + s ^ 5 / 5 + s ^ 7 / 7 := by ring
    _ ≤ mu ρ := hseries

/-! ## A sharper lower bound for `mu`

`mu(1-ε)/(ε^{3/2}) → 2√2/3 = 0.9428…`, so the constant `9/10` of `mu_lower` can be improved to
`47/50 = 0.94` (within `0.3%` of optimal).  The extra input is the tangent-line (convexity)
bound `(1+ρ)^{3/2} = (2-δ)^{3/2} ≥ 2√2 - (3√2/2) δ`, `δ = 1-ρ`, which is accurate near `ρ = 1`
where the bound is tight; away from `ρ = 1` the crude two-sided estimates of `mu_lower` suffice
with room to spare. -/

/-- The tangent-line (convexity) bound `(2-δ)^{3/2} ≥ 2√2 - (3√2/2) δ` for `0 ≤ δ ≤ 1/2`. -/
private lemma two_sub_rpow_ge (δ : ℝ) (_h0 : 0 ≤ δ) (h1 : δ ≤ 1 / 2) :
    2 * Real.sqrt 2 - (3 * Real.sqrt 2 / 2) * δ ≤ (2 - δ) ^ (3 / 2 : ℝ) := by
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have he : 2 * Real.sqrt 2 - (3 * Real.sqrt 2 / 2) * δ
      = Real.sqrt 2 * (2 - 3 * δ / 2) := by ring
  refine le_rpow_three_halves (by linarith) ?_ ?_
  · rw [he]
    exact mul_nonneg (Real.sqrt_nonneg 2) (by linarith)
  · rw [he, mul_pow, hsq]
    nlinarith [mul_nonneg (sq_nonneg δ) (by linarith : (0 : ℝ) ≤ 3 / 2 - δ)]

/-- **(I, sharp form)**  For `1/2 ≤ ρ < 1`: `(47/50)(1-ρ)^{3/2} ≤ mu ρ`.

The asymptotic constant is `2√2/3 = 0.9428…`, so `47/50 = 0.94` is within `0.3%` of optimal
(`mu_lower` gives `9/10`).  The proof uses the same three-term artanh series
`mu ρ ≥ s³/3 + s⁵/5 + s⁷/7`, `s = √(1-ρ²)`, but splits `ρ ∈ [1/2,1)` into five ranges and uses
the tangent-line bound near `ρ = 1`. -/
theorem mu_lower_sharp (ρ : ℝ) (h1 : 1 / 2 ≤ ρ) (h2 : ρ < 1) :
    (47 / 50) * (1 - ρ) ^ (3 / 2 : ℝ) ≤ mu ρ := by
  have hρ0 : 0 < ρ := by linarith
  set s := Real.sqrt (1 - ρ ^ 2) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = 1 - ρ ^ 2 := by
    rw [hs, Real.sq_sqrt]; nlinarith
  have hseries := mu_ge_series ρ hρ0 h2 h1
  have h1p : 0 < 1 + ρ := by linarith
  have hε : 1 - ρ = s ^ 2 / (1 + ρ) := by
    field_simp
    nlinarith [hs2]
  have hrpow : (1 - ρ) ^ (3 / 2 : ℝ) = s ^ 3 / (1 + ρ) ^ (3 / 2 : ℝ) := by
    rw [hε, Real.div_rpow (sq_nonneg s) (le_of_lt h1p)]
    congr 1
    rw [← Real.rpow_natCast s 2, ← Real.rpow_mul hs0]
    norm_num
  rw [hrpow]
  have hkey : (47 : ℝ) / 50 ≤ (1 / 3 + s ^ 2 / 5 + s ^ 4 / 7) * (1 + ρ) ^ (3 / 2 : ℝ) := by
    rcases le_or_gt (4 / 5) ρ with hreg1 | hreg1
    · -- `4/5 ≤ ρ`: tangent-line bound for `(1+ρ)^{3/2}`, exact `s² = δ(2-δ)`
      set δ := 1 - ρ with hδ
      have hδ0 : 0 ≤ δ := by linarith
      have hδ1 : δ ≤ 1 / 5 := by linarith
      have hs2δ : s ^ 2 = δ * (2 - δ) := by rw [hs2, hδ]; ring
      have hA : 1 / 3 + 2 * δ / 5 - δ ^ 2 / 5 ≤ 1 / 3 + s ^ 2 / 5 + s ^ 4 / 7 := by
        have h4 : (0 : ℝ) ≤ s ^ 4 := by positivity
        nlinarith [hs2δ, h4]
      have hB : 2 * Real.sqrt 2 - (3 * Real.sqrt 2 / 2) * δ ≤ (1 + ρ) ^ (3 / 2 : ℝ) := by
        have h := two_sub_rpow_ge δ hδ0 (by linarith)
        have hρδ : (2 : ℝ) - δ = 1 + ρ := by rw [hδ]; ring
        rwa [hρδ] at h
      have hc0 : 0 ≤ 2 * Real.sqrt 2 - (3 * Real.sqrt 2 / 2) * δ := by
        have he : 2 * Real.sqrt 2 - (3 * Real.sqrt 2 / 2) * δ
            = Real.sqrt 2 * (2 - 3 * δ / 2) := by ring
        rw [he]
        exact mul_nonneg (Real.sqrt_nonneg 2) (by linarith)
      have hP : (1 : ℝ) / 3
          ≤ (1 / 3 + 2 * δ / 5 - δ ^ 2 / 5) * (1 - 3 * δ / 4) := by
        nlinarith [hδ0, hδ1]
      have h2s : (47 : ℝ) / 50 ≤ 2 * Real.sqrt 2 / 3 := by
        have h1' : (141 : ℝ) / 50 ≤ Real.sqrt 8 := Real.le_sqrt_of_sq_le (by norm_num)
        have h2' : Real.sqrt 8 = 2 * Real.sqrt 2 := by
          rw [show (8 : ℝ) = 4 * 2 by norm_num, Real.sqrt_mul (by norm_num)]
          norm_num
        rw [h2'] at h1'
        linarith
      have hfac : 2 * Real.sqrt 2 - (3 * Real.sqrt 2 / 2) * δ
          = 2 * Real.sqrt 2 * (1 - 3 * δ / 4) := by ring
      have hS0 : (0 : ℝ) ≤ 2 * Real.sqrt 2 := by positivity
      have hgoal : (47 : ℝ) / 50 ≤ (1 / 3 + 2 * δ / 5 - δ ^ 2 / 5)
          * (2 * Real.sqrt 2 - (3 * Real.sqrt 2 / 2) * δ) := by
        rw [hfac]
        calc (47 : ℝ) / 50 ≤ 2 * Real.sqrt 2 / 3 := h2s
          _ = 2 * Real.sqrt 2 * (1 / 3) := by ring
          _ ≤ 2 * Real.sqrt 2 * ((1 / 3 + 2 * δ / 5 - δ ^ 2 / 5) * (1 - 3 * δ / 4)) :=
              mul_le_mul_of_nonneg_left hP hS0
          _ = (1 / 3 + 2 * δ / 5 - δ ^ 2 / 5) * (2 * Real.sqrt 2 * (1 - 3 * δ / 4)) := by ring
      have hprod := mul_le_mul hA hB hc0 (by positivity)
      linarith [hprod, hgoal]
    · rcases le_or_gt (3 / 4) ρ with hreg2 | hreg2
      · have hs2' : (9 : ℝ) / 25 ≤ s ^ 2 := by rw [hs2]; nlinarith
        have hf : (5563 : ℝ) / 13125 ≤ 1 / 3 + s ^ 2 / 5 + s ^ 4 / 7 := by
          nlinarith [hs2', hs0]
        have hp : (9 : ℝ) / 4 ≤ (1 + ρ) ^ (3 / 2 : ℝ) :=
          le_trans (le_rpow_three_halves (x := (7 : ℝ) / 4) (y := (9 : ℝ) / 4)
            (by norm_num) (by norm_num) (by norm_num))
            (Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num))
        have hm := mul_le_mul hf hp (by norm_num) (by positivity)
        linarith
      · rcases le_or_gt (7 / 10) ρ with hreg3 | hreg3
        · have hs2' : (7 : ℝ) / 16 ≤ s ^ 2 := by rw [hs2]; nlinarith
          have hf : (1721 : ℝ) / 3840 ≤ 1 / 3 + s ^ 2 / 5 + s ^ 4 / 7 := by
            nlinarith [hs2', hs0]
          have hp : (11 : ℝ) / 5 ≤ (1 + ρ) ^ (3 / 2 : ℝ) :=
            le_trans (le_rpow_three_halves (x := (17 : ℝ) / 10) (y := (11 : ℝ) / 5)
              (by norm_num) (by norm_num) (by norm_num))
              (Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num))
          have hm := mul_le_mul hf hp (by norm_num) (by positivity)
          linarith
        · rcases le_or_gt (3 / 5) ρ with hreg4 | hreg4
          · have hs2' : (51 : ℝ) / 100 ≤ s ^ 2 := by rw [hs2]; nlinarith
            have hf : (99223 : ℝ) / 210000 ≤ 1 / 3 + s ^ 2 / 5 + s ^ 4 / 7 := by
              nlinarith [hs2', hs0]
            have hp : (2 : ℝ) ≤ (1 + ρ) ^ (3 / 2 : ℝ) :=
              le_trans (le_rpow_three_halves (x := (8 : ℝ) / 5) (y := 2)
                (by norm_num) (by norm_num) (by norm_num))
                (Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num))
            have hm := mul_le_mul hf hp (by norm_num) (by positivity)
            linarith
          · have hs2' : (16 : ℝ) / 25 ≤ s ^ 2 := by rw [hs2]; nlinarith
            have hf : (6823 : ℝ) / 13125 ≤ 1 / 3 + s ^ 2 / 5 + s ^ 4 / 7 := by
              nlinarith [hs2', hs0]
            have hp : (90 : ℝ) / 49 ≤ (1 + ρ) ^ (3 / 2 : ℝ) :=
              le_trans (le_rpow_three_halves (x := (3 : ℝ) / 2) (y := (90 : ℝ) / 49)
                (by norm_num) (by norm_num) (by norm_num))
                (Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num))
            have hm := mul_le_mul hf hp (by norm_num) (by positivity)
            linarith
  have h1p32 : 0 < (1 + ρ) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos h1p _
  have hdiv : (47 : ℝ) / 50 / (1 + ρ) ^ (3 / 2 : ℝ) ≤ 1 / 3 + s ^ 2 / 5 + s ^ 4 / 7 := by
    rw [div_le_iff₀ h1p32]; linarith
  have hs3 : 0 ≤ s ^ 3 := by positivity
  calc (47 / 50) * (s ^ 3 / (1 + ρ) ^ (3 / 2 : ℝ))
      = s ^ 3 * ((47 : ℝ) / 50 / (1 + ρ) ^ (3 / 2 : ℝ)) := by ring
    _ ≤ s ^ 3 * (1 / 3 + s ^ 2 / 5 + s ^ 4 / 7) :=
        mul_le_mul_of_nonneg_left hdiv hs3
    _ = s ^ 3 / 3 + s ^ 5 / 5 + s ^ 7 / 7 := by ring
    _ ≤ mu ρ := hseries

/-! ## The bound for `D0` -/

/-- Closed form of `D0` in terms of `s = √(1-ρ²)`. -/
lemma D0_eq (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    D0 ρ = (5 * (1 + Real.sqrt (1 - ρ ^ 2)) - ρ) * (1 + Real.sqrt (1 - ρ ^ 2))
      / ((1 - ρ + Real.sqrt (1 - ρ ^ 2)) * ρ) := by
  have hs0 : 0 ≤ Real.sqrt (1 - ρ ^ 2) := Real.sqrt_nonneg _
  have h1s : 0 < 1 + Real.sqrt (1 - ρ ^ 2) := by linarith
  have hne : 1 - ρ + Real.sqrt (1 - ρ ^ 2) ≠ 0 := by linarith
  have hB : 1 - ρ / (1 + Real.sqrt (1 - ρ ^ 2))
      = (1 - ρ + Real.sqrt (1 - ρ ^ 2)) / (1 + Real.sqrt (1 - ρ ^ 2)) := by
    field_simp
    ring
  have hC : 1 + 4 * (1 + Real.sqrt (1 - ρ ^ 2)) / (1 - ρ + Real.sqrt (1 - ρ ^ 2))
      = (5 * (1 + Real.sqrt (1 - ρ ^ 2)) - ρ) / (1 - ρ + Real.sqrt (1 - ρ ^ 2)) := by
    field_simp
    ring
  rw [D0, hB, div_div_eq_mul_div, hC]
  field_simp
  try ring

/-- **(II)** For `1/2 ≤ ρ < 1`: `D0 ρ ≤ 25/(1-ρ)`.

(The literal constant `8` is *false* at `ρ = 1/2`, where `D0 (1/2) = 24.12… > 16`;
see `D0_le_eight` for the sharp constant on `ρ ≥ 3/4`.) -/
theorem D0_le (ρ : ℝ) (h1 : 1 / 2 ≤ ρ) (h2 : ρ < 1) : D0 ρ ≤ 25 / (1 - ρ) := by
  have hρ0 : 0 < ρ := by linarith
  have hε : 0 < 1 - ρ := by linarith
  have hs0 : 0 ≤ Real.sqrt (1 - ρ ^ 2) := Real.sqrt_nonneg _
  have hs2 : (Real.sqrt (1 - ρ ^ 2)) ^ 2 = 1 - ρ ^ 2 := Real.sq_sqrt (by nlinarith)
  have hs7 : Real.sqrt (1 - ρ ^ 2) ≤ 7 / 8 := by
    have h : (Real.sqrt (1 - ρ ^ 2)) ^ 2 ≤ (7 / 8 : ℝ) ^ 2 := by rw [hs2]; nlinarith
    nlinarith [hs0, h]
  have hspos : 0 < Real.sqrt (1 - ρ ^ 2) := Real.sqrt_pos_of_pos (by nlinarith)
  have hnum : (5 * (1 + Real.sqrt (1 - ρ ^ 2)) - ρ) * (1 + Real.sqrt (1 - ρ ^ 2))
      ≤ (1125 : ℝ) / 64 := by
    have hb : 1 + Real.sqrt (1 - ρ ^ 2) ≤ 15 / 8 := by linarith
    have hb0 : 0 ≤ 1 + Real.sqrt (1 - ρ ^ 2) := by linarith
    have ha : 5 * (1 + Real.sqrt (1 - ρ ^ 2)) - ρ ≤ 5 * (1 + Real.sqrt (1 - ρ ^ 2)) := by
      linarith
    have ha' : 5 * (1 + Real.sqrt (1 - ρ ^ 2)) ≤ 75 / 8 := by linarith
    have ha0 : 0 ≤ 5 * (1 + Real.sqrt (1 - ρ ^ 2)) - ρ := by linarith
    calc (5 * (1 + Real.sqrt (1 - ρ ^ 2)) - ρ) * (1 + Real.sqrt (1 - ρ ^ 2))
        ≤ (5 * (1 + Real.sqrt (1 - ρ ^ 2))) * (15 / 8) := by
          exact mul_le_mul ha hb hb0 (by linarith)
      _ ≤ (75 / 8) * (15 / 8) := by
          exact mul_le_mul_of_nonneg_right ha' (by norm_num)
      _ = (1125 : ℝ) / 64 := by norm_num
  have hden : (1 / 2) * Real.sqrt (1 - ρ ^ 2) ≤ (1 - ρ + Real.sqrt (1 - ρ ^ 2)) * ρ := by
    nlinarith [hs0, hε, h1]
  have hstep : D0 ρ ≤ (1125 : ℝ) / 32 / Real.sqrt (1 - ρ ^ 2) := by
    rw [D0_eq ρ hρ0 h2]
    calc (5 * (1 + Real.sqrt (1 - ρ ^ 2)) - ρ) * (1 + Real.sqrt (1 - ρ ^ 2))
          / ((1 - ρ + Real.sqrt (1 - ρ ^ 2)) * ρ)
        ≤ (1125 / 64) / ((1 / 2) * Real.sqrt (1 - ρ ^ 2)) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [hnum, hden, hs0, hε]
      _ = (1125 : ℝ) / 32 / Real.sqrt (1 - ρ ^ 2) := by ring
  have hmain : (1125 : ℝ) * (1 - ρ) ≤ 800 * Real.sqrt (1 - ρ ^ 2) := by
    have hsq : ((1125 : ℝ) * (1 - ρ)) ^ 2 ≤ (800 * Real.sqrt (1 - ρ ^ 2)) ^ 2 := by
      nlinarith [hs2, h1, h2]
    exact (pow_le_pow_iff_left₀ (by linarith) (by positivity) (by norm_num : (2 : ℕ) ≠ 0)).mp hsq
  have hfin : (1125 : ℝ) / 32 / Real.sqrt (1 - ρ ^ 2) ≤ 25 / (1 - ρ) := by
    rw [div_le_div_iff₀ hspos hε]
    linarith
  linarith [hstep, hfin]

/-- **(II, sharp form)** For `3/4 ≤ ρ < 1`: `D0 ρ ≤ 8/(1-ρ)`. -/
theorem D0_le_eight (ρ : ℝ) (h1 : 3 / 4 ≤ ρ) (h2 : ρ < 1) : D0 ρ ≤ 8 / (1 - ρ) := by
  have hρ0 : 0 < ρ := by linarith
  have hε : 0 < 1 - ρ := by linarith
  have hs0 : 0 ≤ Real.sqrt (1 - ρ ^ 2) := Real.sqrt_nonneg _
  have hs2 : (Real.sqrt (1 - ρ ^ 2)) ^ 2 = 1 - ρ ^ 2 := Real.sq_sqrt (by nlinarith)
  have hs7 : Real.sqrt (1 - ρ ^ 2) ≤ 3 / 4 := by
    have h : (Real.sqrt (1 - ρ ^ 2)) ^ 2 ≤ (3 / 4 : ℝ) ^ 2 := by rw [hs2]; nlinarith
    nlinarith [hs0, h]
  have hspos : 0 < Real.sqrt (1 - ρ ^ 2) := Real.sqrt_pos_of_pos (by nlinarith)
  have hnum : (5 * (1 + Real.sqrt (1 - ρ ^ 2)) - ρ) * (1 + Real.sqrt (1 - ρ ^ 2))
      ≤ (245 : ℝ) / 16 := by
    have hb : 1 + Real.sqrt (1 - ρ ^ 2) ≤ 7 / 4 := by linarith
    have hb0 : 0 ≤ 1 + Real.sqrt (1 - ρ ^ 2) := by linarith
    have ha : 5 * (1 + Real.sqrt (1 - ρ ^ 2)) - ρ ≤ 5 * (1 + Real.sqrt (1 - ρ ^ 2)) := by
      linarith
    have ha' : 5 * (1 + Real.sqrt (1 - ρ ^ 2)) ≤ 35 / 4 := by linarith
    have ha0 : 0 ≤ 5 * (1 + Real.sqrt (1 - ρ ^ 2)) - ρ := by linarith
    calc (5 * (1 + Real.sqrt (1 - ρ ^ 2)) - ρ) * (1 + Real.sqrt (1 - ρ ^ 2))
        ≤ (5 * (1 + Real.sqrt (1 - ρ ^ 2))) * (7 / 4) := by
          exact mul_le_mul ha hb hb0 (by linarith)
      _ ≤ (35 / 4) * (7 / 4) := by
          exact mul_le_mul_of_nonneg_right ha' (by norm_num)
      _ = (245 : ℝ) / 16 := by norm_num
  have hden : (3 / 4) * Real.sqrt (1 - ρ ^ 2) ≤ (1 - ρ + Real.sqrt (1 - ρ ^ 2)) * ρ := by
    nlinarith [hs0, hε, h1]
  have hstep : D0 ρ ≤ (245 : ℝ) / 12 / Real.sqrt (1 - ρ ^ 2) := by
    rw [D0_eq ρ hρ0 h2]
    calc (5 * (1 + Real.sqrt (1 - ρ ^ 2)) - ρ) * (1 + Real.sqrt (1 - ρ ^ 2))
          / ((1 - ρ + Real.sqrt (1 - ρ ^ 2)) * ρ)
        ≤ (245 / 16) / ((3 / 4) * Real.sqrt (1 - ρ ^ 2)) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [hnum, hden, hs0, hε]
      _ = (245 : ℝ) / 12 / Real.sqrt (1 - ρ ^ 2) := by ring
  have hmain : (245 : ℝ) * (1 - ρ) ≤ 96 * Real.sqrt (1 - ρ ^ 2) := by
    have hsq : ((245 : ℝ) * (1 - ρ)) ^ 2 ≤ (96 * Real.sqrt (1 - ρ ^ 2)) ^ 2 := by
      nlinarith [hs2, h1, h2]
    exact (pow_le_pow_iff_left₀ (by linarith) (by positivity) (by norm_num : (2 : ℕ) ≠ 0)).mp hsq
  have hfin : (245 : ℝ) / 12 / Real.sqrt (1 - ρ ^ 2) ≤ 8 / (1 - ρ) := by
    rw [div_le_div_iff₀ hspos hε]
    linarith
  linarith [hstep, hfin]

/-- **(II, square-root form)**  For `3/4 ≤ ρ < 1`: `D0 ρ ≤ 13/√(1-ρ)`.

This is the form used by the criterion.  It captures the true behaviour
(`D0 ρ · √(1-ρ) → 2√2` as `ρ → 1`), which the `1/(1-ρ)` bounds of `D0_le`/`D0_le_eight`
overshoot by a whole power of `ε` and which the criterion below exploits. -/
theorem D0_le_inv_sqrt (ρ : ℝ) (h1 : 3 / 4 ≤ ρ) (h2 : ρ < 1) :
    D0 ρ ≤ 13 / (1 - ρ) ^ (1 / 2 : ℝ) := by
  have hρ0 : 0 < ρ := by linarith
  have hε : 0 < 1 - ρ := by linarith
  have hs0 : 0 ≤ Real.sqrt (1 - ρ ^ 2) := Real.sqrt_nonneg _
  have hs2 : (Real.sqrt (1 - ρ ^ 2)) ^ 2 = 1 - ρ ^ 2 := Real.sq_sqrt (by nlinarith)
  have hspos : 0 < Real.sqrt (1 - ρ ^ 2) := Real.sqrt_pos_of_pos (by nlinarith)
  have hs23 : Real.sqrt (1 - ρ ^ 2) ≤ 2 / 3 := by
    have h : (Real.sqrt (1 - ρ ^ 2)) ^ 2 ≤ (2 / 3 : ℝ) ^ 2 := by rw [hs2]; nlinarith
    nlinarith [hs0, h]
  have hnum : (5 * (1 + Real.sqrt (1 - ρ ^ 2)) - ρ) * (1 + Real.sqrt (1 - ρ ^ 2))
      ≤ (455 : ℝ) / 36 := by
    have hb : 1 + Real.sqrt (1 - ρ ^ 2) ≤ 5 / 3 := by linarith
    have hb0 : 0 ≤ 1 + Real.sqrt (1 - ρ ^ 2) := by linarith
    have ha : 5 * (1 + Real.sqrt (1 - ρ ^ 2)) - ρ ≤ 91 / 12 := by linarith
    have ha0 : 0 ≤ 5 * (1 + Real.sqrt (1 - ρ ^ 2)) - ρ := by linarith
    calc (5 * (1 + Real.sqrt (1 - ρ ^ 2)) - ρ) * (1 + Real.sqrt (1 - ρ ^ 2))
        ≤ (91 / 12) * (5 / 3) := mul_le_mul ha hb hb0 (by norm_num)
      _ = (455 : ℝ) / 36 := by norm_num
  have hden : (3 / 4) * Real.sqrt (1 - ρ ^ 2) ≤ (1 - ρ + Real.sqrt (1 - ρ ^ 2)) * ρ := by
    nlinarith [hs0, hε, h1]
  have hstep : D0 ρ ≤ (455 : ℝ) / 27 / Real.sqrt (1 - ρ ^ 2) := by
    rw [D0_eq ρ hρ0 h2]
    calc (5 * (1 + Real.sqrt (1 - ρ ^ 2)) - ρ) * (1 + Real.sqrt (1 - ρ ^ 2))
          / ((1 - ρ + Real.sqrt (1 - ρ ^ 2)) * ρ)
        ≤ (455 / 36) / ((3 / 4) * Real.sqrt (1 - ρ ^ 2)) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [hnum, hden, hs0, hε]
      _ = (455 : ℝ) / 27 / Real.sqrt (1 - ρ ^ 2) := by ring
  have hmain : (455 : ℝ) / 27 * (1 - ρ) ^ (1 / 2 : ℝ) ≤ 13 * Real.sqrt (1 - ρ ^ 2) := by
    have hlt : ((1 - ρ) ^ (1 / 2 : ℝ)) ^ 2 = 1 - ρ := by
      rw [← Real.rpow_natCast ((1 - ρ) ^ (1 / 2 : ℝ)) 2, ← Real.rpow_mul (le_of_lt hε)]
      norm_num
    have hsq : ((455 : ℝ) / 27 * (1 - ρ) ^ (1 / 2 : ℝ)) ^ 2
        ≤ (13 * Real.sqrt (1 - ρ ^ 2)) ^ 2 := by
      rw [mul_pow, hlt]
      nlinarith [hs2, h1, hε]
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num : (2 : ℕ) ≠ 0)).mp hsq
  have hfin : (455 : ℝ) / 27 / Real.sqrt (1 - ρ ^ 2) ≤ 13 / (1 - ρ) ^ (1 / 2 : ℝ) := by
    rw [div_le_div_iff₀ hspos (Real.rpow_pos_of_pos hε _)]
    linarith [hmain]
  linarith [hstep, hfin]

/-! ## Elementary bounds on `log` (continued) -/

/-- `1 - 1/x ≤ log x` for `x > 0` (the harmonic lower bound, from
`log y ≤ y - 1` applied to `y = 1/x`). -/
private lemma one_sub_inv_le_log {x : ℝ} (hx : 0 < x) : 1 - 1 / x ≤ Real.log x := by
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 / x by positivity)
  rw [Real.log_div (by norm_num) (ne_of_gt hx), Real.log_one] at h
  linarith

/-- For `q ≥ 10^4` we have `3 ≤ log q` (hence `1 ≤ log q`). -/
private lemma log_ge_three (q : ℝ) (hq : (10 : ℝ) ^ 4 ≤ q) : 3 ≤ Real.log q := by
  have h1 : 1 - 1 / (10 : ℝ) ≤ Real.log 10 := one_sub_inv_le_log (by norm_num)
  have h2 : Real.log ((10 : ℝ) ^ 4) = 4 * Real.log 10 := Real.log_pow 10 4
  have h3 : Real.log ((10 : ℝ) ^ 4) ≤ Real.log q := Real.log_le_log (by norm_num) hq
  linarith

/-! ## The radius `rho q` -/

/-- `(log q)/q ≤ 1/23` for `q ≥ 10^4`. -/
private lemma log_div_self_le (q : ℝ) (hq : (10 : ℝ) ^ 4 ≤ q) : Real.log q / q ≤ 1 / 23 := by
  have hq0 : 0 < q := by linarith [hq]
  have hq1 : 1 ≤ q := by linarith [hq]
  have hlog := log_le_two_sqrt q hq1
  have hsq : (46 : ℝ) ≤ Real.sqrt q := Real.le_sqrt_of_sq_le (by linarith [hq])
  have hspos : 0 < Real.sqrt q := Real.sqrt_pos_of_pos hq0
  have h1 : Real.log q / q ≤ 2 / Real.sqrt q := by
    rw [div_le_div_iff₀ hq0 hspos]
    have h := mul_le_mul_of_nonneg_right hlog (Real.sqrt_nonneg q)
    nlinarith [h, Real.sq_sqrt (le_of_lt hq0)]
  have h2 : (2 : ℝ) / Real.sqrt q ≤ 1 / 23 := by
    rw [div_le_div_iff₀ hspos (by norm_num : (0 : ℝ) < 23)]
    linarith
  linarith

/-- If `0 ≤ x ≤ 1/8` then `x^{2/3} ≤ 1/4`. -/
private lemma rpow_two_thirds_le_quarter {x : ℝ} (hx : 0 ≤ x) (h : x ≤ 1 / 8) :
    x ^ (2 / 3 : ℝ) ≤ 1 / 4 := by
  have h1 : x ^ (2 / 3 : ℝ) ≤ (1 / 8 : ℝ) ^ (2 / 3 : ℝ) :=
    Real.rpow_le_rpow hx h (by norm_num)
  have h2 : (1 / 8 : ℝ) ^ (2 / 3 : ℝ) = 1 / 4 := by
    have h3 : ((1 : ℝ) / 2) ^ 3 = 1 / 8 := by norm_num
    rw [← h3, ← Real.rpow_natCast ((1 : ℝ) / 2) 3, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    norm_num
  linarith [h1, h2.le, h2.ge]

/-- If `0 ≤ x ≤ 1/23` then `x^{2/3} ≤ 1/8`. -/
private lemma rpow_two_thirds_le_eighth {x : ℝ} (hx : 0 ≤ x) (h : x ≤ 1 / 23) :
    x ^ (2 / 3 : ℝ) ≤ 1 / 8 := by
  have h1 : x ^ (2 / 3 : ℝ) ≤ (1 / 23 : ℝ) ^ (2 / 3 : ℝ) :=
    Real.rpow_le_rpow hx h (by norm_num)
  have h2 : ((1 / 23 : ℝ) ^ (2 / 3 : ℝ)) ^ 3 = (1 / 23 : ℝ) ^ 2 := by
    rw [← Real.rpow_natCast ((1 / 23 : ℝ) ^ (2 / 3 : ℝ)) 3,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 23)]
    norm_num
  have h3 : ((1 / 23 : ℝ) ^ (2 / 3 : ℝ)) ^ 3 ≤ ((1 : ℝ) / 8) ^ 3 := by
    rw [h2]; norm_num
  have h4 : (1 / 23 : ℝ) ^ (2 / 3 : ℝ) ≤ 1 / 8 :=
    (pow_le_pow_iff_left₀ (Real.rpow_nonneg (by norm_num) _) (by norm_num)
      (by norm_num : (3 : ℕ) ≠ 0)).mp h3
  linarith [h1, h4]

/-- For `q ≥ 10^4`, `rho q ≥ 3/4` (this is the range where the sharp constant
`D0 ρ ≤ 8/(1-ρ)` of `D0_le_eight` is available). -/
lemma rho_ge_three_quarters (q : ℝ) (hq : (10 : ℝ) ^ 4 ≤ q) : 3 / 4 ≤ rho q := by
  have hq0 : 0 < q := by linarith [hq]
  have hlogpos : 0 < Real.log q := Real.log_pos (by linarith [hq])
  have hx0 : 0 ≤ Real.log q / q := by positivity
  have h23 := log_div_self_le q hq
  have h8 : (Real.log q / q) ^ (2 / 3 : ℝ) ≤ 1 / 8 := rpow_two_thirds_le_eighth hx0 h23
  rw [rho]
  linarith

/-- For `q ≥ 10^4`, `rho q < 1`. -/
lemma rho_lt_one (q : ℝ) (hq : (10 : ℝ) ^ 4 ≤ q) : rho q < 1 := by
  have hq0 : 0 < q := by linarith [hq]
  have hlogpos : 0 < Real.log q := Real.log_pos (by linarith [hq])
  have hxpos : 0 < Real.log q / q := by positivity
  have hx : 0 < (Real.log q / q) ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hxpos _
  rw [rho]
  linarith

/-- For `q ≥ 10^4`, `1/2 ≤ rho q` (the hypothesis needed by `mu_lower`). -/
lemma rho_ge_half (q : ℝ) (hq : (10 : ℝ) ^ 4 ≤ q) : 1 / 2 ≤ rho q := by
  have hq0 : 0 < q := by linarith [hq]
  have hlogpos : 0 < Real.log q := Real.log_pos (by linarith [hq])
  have hx0 : 0 ≤ Real.log q / q := by positivity
  have h8 : Real.log q / q ≤ 1 / 8 := le_trans (log_div_self_le q hq) (by norm_num)
  have h4 : (Real.log q / q) ^ (2 / 3 : ℝ) ≤ 1 / 4 := rpow_two_thirds_le_quarter hx0 h8
  rw [rho]
  linarith

/-! ## The criterion -/

/-- `3250/343 < 100^{7/6}`, by raising to the 6th power. -/
private lemma key_hundred_rpow : (3250 : ℝ) / 343 < (100 : ℝ) ^ (7 / 6 : ℝ) := by
  have h1 : ((100 : ℝ) ^ (7 / 6 : ℝ)) ^ 6 = (100 : ℝ) ^ 7 := by
    rw [← Real.rpow_natCast ((100 : ℝ) ^ (7 / 6 : ℝ)) 6,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 100)]
    norm_num
  have h2 : ((3250 : ℝ) / 343) ^ 6 < ((100 : ℝ) ^ (7 / 6 : ℝ)) ^ 6 := by rw [h1]; norm_num
  exact (pow_lt_pow_iff_left₀ (by norm_num) (Real.rpow_nonneg (by norm_num) _)
    (by norm_num : (6 : ℕ) ≠ 0)).mp h2

/-- `325000 < 343 · 10^{14/3}` (the key at `C = 100`, `q = 10^4`). -/
private lemma key_ten_pow_four : (325000 : ℝ) < 343 * (10 : ℝ) ^ (14 / 3 : ℝ) := by
  have h1 : ((10 : ℝ) ^ (14 / 3 : ℝ)) ^ 3 = (10 : ℝ) ^ 14 := by
    rw [← Real.rpow_natCast ((10 : ℝ) ^ (14 / 3 : ℝ)) 3,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 10)]
    norm_num
  have h2 : ((325000 : ℝ) / 343) ^ 3 < ((10 : ℝ) ^ (14 / 3 : ℝ)) ^ 3 := by rw [h1]; norm_num
  have h3 : (325000 : ℝ) / 343 < (10 : ℝ) ^ (14 / 3 : ℝ) :=
    (pow_lt_pow_iff_left₀ (by norm_num) (Real.rpow_nonneg (by norm_num) _)
      (by norm_num : (3 : ℕ) ≠ 0)).mp h2
  linarith

/-- `3250·10^6 < 343 · 10^7` (the key at `C = 10^6`, `q = 10^6`). -/
private lemma key_ten_pow_six : (3250000000 : ℝ) < 343 * (10 : ℝ) ^ (7 : ℝ) := by
  norm_num

/-- `3250/343 < 7^{7/6}`, by raising to the 6th power.  This is the numeric key of the sharp
threshold `q ≥ 7 C^{6/7}` of `criterion_param_sharp` (it gives `343·7^{7/6} = 3320.8… > 3250`). -/
private lemma key_seven_rpow : (3250 : ℝ) / 343 < (7 : ℝ) ^ (7 / 6 : ℝ) := by
  have h1 : ((7 : ℝ) ^ (7 / 6 : ℝ)) ^ 6 = (7 : ℝ) ^ 7 := by
    rw [← Real.rpow_natCast ((7 : ℝ) ^ (7 / 6 : ℝ)) 6,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 7)]
    norm_num
  have h2 : ((3250 : ℝ) / 343) ^ 6 < ((7 : ℝ) ^ (7 / 6 : ℝ)) ^ 6 := by rw [h1]; norm_num
  exact (pow_lt_pow_iff_left₀ (by norm_num) (Real.rpow_nonneg (by norm_num) _)
    (by norm_num : (6 : ℕ) ≠ 0)).mp h2

/-- `7 · 4500^{6/7} ≤ 10^4`: the numeric key showing that the sharp threshold `7 C^{6/7}` is
below `10^4` for every `C ≤ 4500`. -/
private lemma key_four_thousand_five_hundred :
    7 * (4500 : ℝ) ^ (6 / 7 : ℝ) ≤ (10 : ℝ) ^ 4 := by
  have h1 : ((4500 : ℝ) ^ (6 / 7 : ℝ)) ^ 7 = (4500 : ℝ) ^ 6 := by
    rw [← Real.rpow_natCast ((4500 : ℝ) ^ (6 / 7 : ℝ)) 7,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4500)]
    norm_num
  have h2 : ((4500 : ℝ) ^ (6 / 7 : ℝ)) ^ 7 ≤ ((10 : ℝ) ^ 4 / 7) ^ 7 := by
    rw [h1]; norm_num
  have h3 : (4500 : ℝ) ^ (6 / 7 : ℝ) ≤ (10 : ℝ) ^ 4 / 7 :=
    (pow_le_pow_iff_left₀ (Real.rpow_nonneg (by norm_num) _) (by norm_num)
      (by norm_num : (7 : ℕ) ≠ 0)).mp h2
  linarith

/-- The upper bound for `D0 (rho q)` used by the criterion: `D0 (rho q) ≤ (325/49) q^{1/3}`
for `q ≥ 10^4`.  It combines `D0_le_inv_sqrt` with `1-ρ(q) = 2 (log q/q)^{2/3}` and
`log q ≥ 3`. -/
private lemma D0_criterion_bound (q : ℝ) (hq4 : (10 : ℝ) ^ 4 ≤ q) (h34 : 3 / 4 ≤ rho q)
    (hlt : rho q < 1) : D0 (rho q) ≤ 325 / 49 * q ^ (1 / 3 : ℝ) := by
  have hq0 : 0 < q := by
    have : (0 : ℝ) < (10 : ℝ) ^ 4 := by norm_num
    linarith
  have hlogpos : 0 < Real.log q := Real.log_pos (by linarith [hq4])
  have ht3 : 3 ≤ Real.log q := log_ge_three q hq4
  have htq : 0 < Real.log q / q := by positivity
  have ht13 : (0 : ℝ) < (Real.log q) ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hlogpos _
  have hq13 : (0 : ℝ) < q ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hq0 _
  have h := D0_le_inv_sqrt (rho q) h34 hlt
  have hone : 1 - rho q = 2 * (Real.log q / q) ^ (2 / 3 : ℝ) := by rw [rho]; ring
  rw [hone] at h
  have hpow : (2 * (Real.log q / q) ^ (2 / 3 : ℝ)) ^ (1 / 2 : ℝ)
      = Real.sqrt 2 * (Real.log q / q) ^ (1 / 3 : ℝ) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (Real.rpow_nonneg (le_of_lt htq) _),
      Real.sqrt_eq_rpow]
    congr 1
    rw [← Real.rpow_mul (le_of_lt htq)]
    norm_num
  rw [hpow] at h
  have heq : 13 / (Real.sqrt 2 * (Real.log q / q) ^ (1 / 3 : ℝ))
      = 13 / Real.sqrt 2 * (q / Real.log q) ^ (1 / 3 : ℝ) := by
    rw [Real.div_rpow (le_of_lt hlogpos) (le_of_lt hq0),
      Real.div_rpow (le_of_lt hq0) (le_of_lt hlogpos)]
    field_simp
  rw [heq] at h
  have hle1 : (q / Real.log q) ^ (1 / 3 : ℝ) ≤ 5 / 7 * q ^ (1 / 3 : ℝ) := by
    rw [Real.div_rpow (le_of_lt hq0) (le_of_lt hlogpos), div_le_iff₀ ht13]
    have ht13ge : (7 : ℝ) / 5 ≤ (Real.log q) ^ (1 / 3 : ℝ) := by
      have h1 : ((343 : ℝ) / 125) ^ (1 / 3 : ℝ) ≤ (Real.log q) ^ (1 / 3 : ℝ) :=
        Real.rpow_le_rpow (by norm_num) (by linarith) (by norm_num)
      have h2 : ((343 : ℝ) / 125) ^ (1 / 3 : ℝ) = 7 / 5 := by
        have h3 : ((7 : ℝ) / 5) ^ 3 = 343 / 125 := by norm_num
        rw [← h3, ← Real.rpow_natCast ((7 : ℝ) / 5) 3,
          ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 7 / 5)]
        norm_num
      linarith [h1, h2.le, h2.ge]
    nlinarith [ht13ge, hq13]
  have hle2 : 13 / Real.sqrt 2 ≤ 13 * (5 / 7) := by
    have h2 : (7 : ℝ) / 5 ≤ Real.sqrt 2 := by
      refine Real.le_sqrt_of_sq_le ?_
      norm_num
    have h3 : 1 / Real.sqrt 2 ≤ 5 / 7 := by
      have h4 := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 7 / 5) h2
      linarith [h4]
    calc 13 / Real.sqrt 2 = 13 * (1 / Real.sqrt 2) := by ring
      _ ≤ 13 * (5 / 7) := mul_le_mul_of_nonneg_left h3 (by norm_num)
  calc D0 (rho q) ≤ 13 / Real.sqrt 2 * (q / Real.log q) ^ (1 / 3 : ℝ) := h
    _ ≤ 13 * (5 / 7) * (5 / 7 * q ^ (1 / 3 : ℝ)) :=
        mul_le_mul hle2 hle1 (by positivity) (by linarith)
    _ = 325 / 49 * q ^ (1 / 3 : ℝ) := by ring

/-- **The core estimate.**  For `100 ≤ C`, `q ≥ 10^4` and the numeric key
`3250 C < 343 q^{7/6}`: `D0 (rho q) · e^{-q μ(rho q)} < √(rho q)/(C q)`. -/
private theorem criterion_core (C q : ℝ) (hC : 100 ≤ C) (hq4 : (10 : ℝ) ^ 4 ≤ q)
    (hkey : 3250 * C < 343 * q ^ (7 / 6 : ℝ)) :
    D0 (rho q) * Real.exp (-(q * mu (rho q))) < Real.sqrt (rho q) / (C * q) := by
  have hCpos : 0 < C := by linarith
  have hq0 : 0 < q := by
    have : (0 : ℝ) < (10 : ℝ) ^ 4 := by norm_num
    linarith
  have h34 : 3 / 4 ≤ rho q := rho_ge_three_quarters q hq4
  have hhalf : 1 / 2 ≤ rho q := by linarith
  have hlt1 : rho q < 1 := rho_lt_one q hq4
  have hlogpos : 0 < Real.log q := Real.log_pos (by linarith [hq4])
  have htq : 0 < Real.log q / q := by positivity
  have hone : 1 - rho q = 2 * (Real.log q / q) ^ (2 / 3 : ℝ) := by rw [rho]; ring
  -- (1) upper bound for `D0`
  have hD0 : D0 (rho q) ≤ 325 / 49 * q ^ (1 / 3 : ℝ) :=
    D0_criterion_bound q hq4 h34 hlt1
  -- (2) lower bound for `q * mu (rho q)` and the exponential
  have hmu := mu_lower (rho q) hhalf hlt1
  have hpow : (1 - rho q) ^ (3 / 2 : ℝ) = (2 : ℝ) ^ (3 / 2 : ℝ) * (Real.log q / q) := by
    have h1 : (1 - rho q) ^ (3 / 2 : ℝ) = (2 * (Real.log q / q) ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ) := by
      rw [hone]
    rw [h1, Real.mul_rpow (x := (2 : ℝ)) (y := (Real.log q / q) ^ (2 / 3 : ℝ))
      (z := (3 / 2 : ℝ)) (by norm_num) (Real.rpow_nonneg (le_of_lt htq) _)]
    have h2 : ((Real.log q / q) ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ) = Real.log q / q := by
      rw [← Real.rpow_mul (le_of_lt htq)]
      norm_num
    rw [h2]
  have hqm : (5 : ℝ) / 2 * Real.log q ≤ q * mu (rho q) := by
    have hc : (5 : ℝ) / 2 ≤ (9 : ℝ) / 10 * (2 : ℝ) ^ (3 / 2 : ℝ) := by
      have h := le_rpow_three_halves (x := (2 : ℝ)) (y := (25 : ℝ) / 9)
        (by norm_num) (by norm_num) (by norm_num)
      linarith
    have halg : q * ((9 : ℝ) / 10 * ((2 : ℝ) ^ (3 / 2 : ℝ) * (Real.log q / q)))
        = ((9 : ℝ) / 10 * (2 : ℝ) ^ (3 / 2 : ℝ)) * Real.log q := by
      field_simp [ne_of_gt hq0]
    have step1 : q * ((9 : ℝ) / 10 * (1 - rho q) ^ (3 / 2 : ℝ)) ≤ q * mu (rho q) :=
      mul_le_mul_of_nonneg_left hmu (le_of_lt hq0)
    have step2 : (5 : ℝ) / 2 * Real.log q
        ≤ q * ((9 : ℝ) / 10 * (1 - rho q) ^ (3 / 2 : ℝ)) := by
      rw [hpow, halg]
      exact mul_le_mul_of_nonneg_right hc (le_of_lt hlogpos)
    linarith
  have hexp : Real.exp (-(q * mu (rho q))) ≤ q ^ (-(5 / 2 : ℝ)) := by
    have h1 : Real.exp (-(q * mu (rho q))) ≤ Real.exp (-((5 : ℝ) / 2 * Real.log q)) :=
      Real.exp_le_exp.mpr (by linarith)
    have h2 : Real.exp (-((5 : ℝ) / 2 * Real.log q)) = q ^ (-(5 / 2 : ℝ)) := by
      rw [Real.rpow_def_of_pos hq0]
      rw [show (-((5 : ℝ) / 2 * Real.log q)) = Real.log q * (-(5 / 2 : ℝ)) by ring]
    rw [h2] at h1
    exact h1
  -- (3) lower bound for the right-hand side
  have hsqrt : (7 : ℝ) / 10 ≤ Real.sqrt (rho q) := by
    refine Real.le_sqrt_of_sq_le ?_
    nlinarith [hhalf]
  have hRHS : (7 : ℝ) / 10 / (C * q) ≤ Real.sqrt (rho q) / (C * q) :=
    div_le_div_of_nonneg_right hsqrt (by positivity)
  -- (4) the two sides
  have hLHS : D0 (rho q) * Real.exp (-(q * mu (rho q))) ≤ 325 / 49 * q ^ (-(13 / 6 : ℝ)) := by
    have h1 := mul_le_mul hD0 hexp (by positivity) (by positivity)
    have h2 : 325 / 49 * q ^ (1 / 3 : ℝ) * q ^ (-(5 / 2 : ℝ))
        = 325 / 49 * q ^ (-(13 / 6 : ℝ)) := by
      rw [mul_assoc, ← Real.rpow_add hq0]
      norm_num
    linarith [h1, h2.le]
  have hmain : 325 / 49 * q ^ (-(13 / 6 : ℝ)) < (7 : ℝ) / 10 / (C * q) := by
    rw [lt_div_iff₀ (by positivity : (0 : ℝ) < C * q)]
    have hp : q ^ (-(13 / 6 : ℝ)) * q = q ^ (-(7 / 6 : ℝ)) := by
      have h : q ^ (-(13 / 6 : ℝ)) * q = q ^ (-(13 / 6 : ℝ)) * q ^ (1 : ℝ) := by
        rw [Real.rpow_one]
      rw [h, ← Real.rpow_add hq0]
      norm_num
    have hq76 : (0 : ℝ) < q ^ (-(7 / 6 : ℝ)) := Real.rpow_pos_of_pos hq0 _
    have hone' : q ^ (7 / 6 : ℝ) * q ^ (-(7 / 6 : ℝ)) = 1 := by
      rw [← Real.rpow_add hq0]; norm_num
    have hone'' : (343 : ℝ) * q ^ (7 / 6 : ℝ) * q ^ (-(7 / 6 : ℝ)) = 343 := by
      rw [mul_assoc, hone', mul_one]
    have hmul := mul_lt_mul_of_pos_right hkey hq76
    rw [hone''] at hmul
    have halg : 325 / 49 * q ^ (-(13 / 6 : ℝ)) * (C * q)
        = (3250 * C * q ^ (-(7 / 6 : ℝ))) * (7 / 10) / 343 := by
      rw [← hp]; ring
    rw [halg]
    linarith [hmul]
  calc D0 (rho q) * Real.exp (-(q * mu (rho q)))
      ≤ 325 / 49 * q ^ (-(13 / 6 : ℝ)) := hLHS
    _ < (7 : ℝ) / 10 / (C * q) := hmain
    _ ≤ Real.sqrt (rho q) / (C * q) := hRHS

/-- **(III, parametric form)**  For every `100 ≤ C` and every `q ≥ 100 C^{7/6}` the
sharpened mechanism's criterion holds with the constant `C`:
`D0 (rho q) · exp (-(q μ(rho q))) < √(rho q)/(C q)`. -/
theorem criterion_param (C q : ℝ) (hC : 100 ≤ C) (hq : 100 * C ^ (7 / 6 : ℝ) ≤ q) :
    D0 (rho q) * Real.exp (-(q * mu (rho q))) < Real.sqrt (rho q) / (C * q) := by
  have hCpos : 0 < C := by linarith
  have hCpow : 0 < C ^ (7 / 6 : ℝ) := Real.rpow_pos_of_pos hCpos _
  have hq4 : (10 : ℝ) ^ 4 ≤ q := by
    have h3 : (100 : ℝ) ≤ (100 : ℝ) ^ (7 / 6 : ℝ) := by
      calc (100 : ℝ) = (100 : ℝ) ^ (1 : ℝ) := (Real.rpow_one 100).symm
        _ ≤ (100 : ℝ) ^ (7 / 6 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    have h4 : (100 : ℝ) ^ (7 / 6 : ℝ) ≤ C ^ (7 / 6 : ℝ) :=
      Real.rpow_le_rpow (by norm_num) hC (by norm_num)
    nlinarith [h3, h4, hq]
  have hkey : 3250 * C < 343 * q ^ (7 / 6 : ℝ) := by
    have hsplit : ((100 : ℝ) * C ^ (7 / 6 : ℝ)) ^ (7 / 6 : ℝ)
        = (100 : ℝ) ^ (7 / 6 : ℝ) * C ^ (49 / 36 : ℝ) := by
      rw [Real.mul_rpow (by norm_num) (le_of_lt hCpow), ← Real.rpow_mul (le_of_lt hCpos)]
      norm_num
    have hq76 : (100 : ℝ) ^ (7 / 6 : ℝ) * C ^ (49 / 36 : ℝ) ≤ q ^ (7 / 6 : ℝ) := by
      have h := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ 100 * C ^ (7 / 6 : ℝ)) hq
        (by norm_num : (0 : ℝ) ≤ 7 / 6)
      rwa [hsplit] at h
    have hC1 : C ≤ C ^ (49 / 36 : ℝ) := by
      calc C = C ^ (1 : ℝ) := (Real.rpow_one C).symm
        _ ≤ C ^ (49 / 36 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    have hC49 : (100 : ℝ) ^ (7 / 6 : ℝ) * C ≤ q ^ (7 / 6 : ℝ) := by
      have h := mul_le_mul_of_nonneg_left hC1 (by positivity : (0 : ℝ) ≤ (100 : ℝ) ^ (7 / 6 : ℝ))
      linarith [hq76, h]
    have h100 : (3250 : ℝ) / 343 < (100 : ℝ) ^ (7 / 6 : ℝ) := key_hundred_rpow
    nlinarith [hC49, h100, hCpos]
  exact criterion_core C q hC hq4 hkey

/-- **(III)**  For `q ≥ 10^4` the criterion holds with `C = 100`:
`D0 (rho q) · exp (-(q μ(rho q))) < √(rho q)/(100 q)`. -/
theorem criterion (q : ℝ) (hq : (10 : ℝ) ^ 4 ≤ q) :
    D0 (rho q) * Real.exp (-(q * mu (rho q))) < Real.sqrt (rho q) / (100 * q) := by
  refine criterion_core 100 q (by norm_num) hq ?_
  have hq76 : (10 : ℝ) ^ (14 / 3 : ℝ) ≤ q ^ (7 / 6 : ℝ) := by
    have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ (10 : ℝ) ^ 4) hq
      (by norm_num : (0 : ℝ) ≤ 7 / 6)
    have heq : ((10 : ℝ) ^ 4) ^ (7 / 6 : ℝ) = (10 : ℝ) ^ (14 / 3 : ℝ) := by
      rw [← Real.rpow_natCast (10 : ℝ) 4, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 10)]
      norm_num
    rwa [heq] at h
  have hk := key_ten_pow_four
  linarith

/-- The criterion with `C = 10^6` at `q ≥ 10^6` (the constant the assembly may need:
`C_total` up to `10^6`).  At `q = 10^6` this chain supports `C < 10^7·343/3250 = 1.05·10^6`. -/
theorem criterion_C1e6 (q : ℝ) (hq : (10 : ℝ) ^ 6 ≤ q) :
    D0 (rho q) * Real.exp (-(q * mu (rho q))) < Real.sqrt (rho q) / (10 ^ 6 * q) := by
  refine criterion_core (10 ^ 6) q (by norm_num) (by linarith [hq]) ?_
  have hq76 : (10 : ℝ) ^ (7 : ℝ) ≤ q ^ (7 / 6 : ℝ) := by
    have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ (10 : ℝ) ^ 6) hq
      (by norm_num : (0 : ℝ) ≤ 7 / 6)
    have heq : ((10 : ℝ) ^ 6) ^ (7 / 6 : ℝ) = (10 : ℝ) ^ (7 : ℝ) := by
      rw [← Real.rpow_natCast (10 : ℝ) 6, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 10)]
      norm_num
    rwa [heq] at h
  have hk := key_ten_pow_six
  linarith

/-- **(III, sharp parametric form)**  For every `100 ≤ C` and every `q ≥ max (10^4) (7 C^{6/7})`
the criterion holds with the constant `C`:
`D0 (rho q) · exp (-(q μ(rho q))) < √(rho q)/(C q)`.

The chain behind `criterion_core` only needs `343 q^{7/6} > 3250 C`, i.e. `q > (3250C/343)^{6/7}`
(with `(3250/343)^{6/7} = 6.87…`); the clean sufficient condition `q ≥ 7 C^{6/7}` is available
because `7^{7/6} = 9.6816… > 3250/343 = 9.4752…`.  This strictly improves `criterion_param`
(threshold `100 C^{7/6}`): at `C = 10^6` the threshold drops from `10^9` to `9.73·10^5`, and for
`C ≤ 4794` it is just `10^4`. -/
theorem criterion_param_sharp (C q : ℝ) (hC : 100 ≤ C)
    (hq : max ((10 : ℝ) ^ 4) (7 * C ^ (6 / 7 : ℝ)) ≤ q) :
    D0 (rho q) * Real.exp (-(q * mu (rho q))) < Real.sqrt (rho q) / (C * q) := by
  have hCpos : 0 < C := by linarith
  have hq4 : (10 : ℝ) ^ 4 ≤ q := le_trans (le_max_left _ _) hq
  have hq7 : 7 * C ^ (6 / 7 : ℝ) ≤ q := le_trans (le_max_right _ _) hq
  refine criterion_core C q hC hq4 ?_
  have hq76 : 7 ^ (7 / 6 : ℝ) * C ≤ q ^ (7 / 6 : ℝ) := by
    have h1 : (7 * C ^ (6 / 7 : ℝ)) ^ (7 / 6 : ℝ) ≤ q ^ (7 / 6 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hq7 (by norm_num)
    have h2 : (7 * C ^ (6 / 7 : ℝ)) ^ (7 / 6 : ℝ) = 7 ^ (7 / 6 : ℝ) * C := by
      rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg (le_of_lt hCpos) _),
        ← Real.rpow_mul (le_of_lt hCpos)]
      norm_num
    rwa [h2] at h1
  have hk : (3250 : ℝ) < 343 * 7 ^ (7 / 6 : ℝ) := by
    have h := mul_lt_mul_of_pos_left key_seven_rpow (by norm_num : (0 : ℝ) < 343)
    have h' : (343 : ℝ) * ((3250 : ℝ) / 343) = 3250 := by norm_num
    linarith [h, h']
  have hkC : (3250 : ℝ) * C < (343 * 7 ^ (7 / 6 : ℝ)) * C :=
    mul_lt_mul_of_pos_right hk hCpos
  have h2 : (343 * 7 ^ (7 / 6 : ℝ)) * C ≤ 343 * q ^ (7 / 6 : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hq76 (by norm_num : (0 : ℝ) ≤ 343)
    nlinarith [h]
  linarith

/-- **(III, small constant)**  For `0 < C ≤ 100` the criterion holds already for `q ≥ 10^4`:
the `C = 100` statement `criterion` only has to be divided by a smaller constant. -/
theorem criterion_small_C (C q : ℝ) (hC0 : 0 < C) (hC : C ≤ 100) (hq : (10 : ℝ) ^ 4 ≤ q) :
    D0 (rho q) * Real.exp (-(q * mu (rho q))) < Real.sqrt (rho q) / (C * q) := by
  refine lt_of_lt_of_le (criterion q hq) ?_
  have hq0 : (0 : ℝ) < q := by
    have : (0 : ℝ) < (10 : ℝ) ^ 4 := by norm_num
    linarith
  exact div_le_div_of_nonneg_left (Real.sqrt_nonneg (rho q)) (by positivity)
    (mul_le_mul_of_nonneg_right hC (le_of_lt hq0))

/-- **(III, unified sharp form)**  For **every** `C > 0` and every
`q ≥ max (10^4) (7 (max C 100)^{6/7})` the criterion holds:
`D0 (rho q) · exp (-(q μ(rho q))) < √(rho q)/(C q)`.

This is the single statement the assembly can use: the explicit threshold
`q0 C = max (10^4) (7 (max C 100)^{6/7})` equals `10^4` for `0 < C ≤ 4794`
(because `7·100^{6/7} = 357.4…` and `7 C^{6/7} ≤ 10^4 ⟺ C ≤ 4794.2…`), and equals `7 C^{6/7}`
for larger `C`. -/
theorem criterion_param_max (C q : ℝ) (hC0 : 0 < C)
    (hq : max ((10 : ℝ) ^ 4) (7 * (max C 100) ^ (6 / 7 : ℝ)) ≤ q) :
    D0 (rho q) * Real.exp (-(q * mu (rho q))) < Real.sqrt (rho q) / (C * q) := by
  rcases le_or_gt C 100 with hC | hC
  · exact criterion_small_C C q hC0 hC (le_trans (le_max_left _ _) hq)
  · rw [max_eq_left (le_of_lt hC)] at hq
    exact criterion_param_sharp C q (le_of_lt hC) hq

/-- **(III, concrete large constant at `q ≥ 10^4`)**  With `C = 4500` the criterion holds for all
`q ≥ 10^4`.  (At `q = 10^4` the sharp chain `343 q^{7/6} > 3250 C` itself supports `C < 4898`.) -/
theorem criterion_C4500 (q : ℝ) (hq : (10 : ℝ) ^ 4 ≤ q) :
    D0 (rho q) * Real.exp (-(q * mu (rho q))) < Real.sqrt (rho q) / (4500 * q) := by
  refine criterion_param_sharp 4500 q (by norm_num) (max_le hq ?_)
  linarith [key_four_thousand_five_hundred]

/-- **(III, existence form)**  There is an explicit `q0` with the criterion for `C = 100`. -/
theorem criterion_exists : ∃ q0 : ℝ, ∀ q : ℝ, q0 ≤ q →
    D0 (rho q) * Real.exp (-(q * mu (rho q))) < Real.sqrt (rho q) / (100 * q) :=
  ⟨(10 : ℝ) ^ 4, fun q hq => criterion q hq⟩

/-- `(4000/7) < 10^{35/12}`, by raising to the 12th power. -/
theorem D0_half_gt_sixteen : 16 < D0 (1 / 2) := by
  have h3lo : (5 : ℝ) / 3 ≤ Real.sqrt 3 := Real.le_sqrt_of_sq_le (by norm_num)
  have h3hi : Real.sqrt 3 ≤ (7 : ℝ) / 4 := by
    have h : (3 : ℝ) ≤ ((7 : ℝ) / 4) ^ 2 := by norm_num
    calc Real.sqrt 3 ≤ Real.sqrt (((7 : ℝ) / 4) ^ 2) := Real.sqrt_le_sqrt h
      _ = (7 : ℝ) / 4 := Real.sqrt_sq (by norm_num)
  have hs : Real.sqrt (1 - (1 / 2) ^ 2) = Real.sqrt 3 / 2 := by
    have h : (1 : ℝ) - (1 / 2) ^ 2 = 3 / 4 := by norm_num
    rw [h, Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  rw [D0, hs]
  set s := Real.sqrt 3 / 2 with hsd
  have hslo : (5 : ℝ) / 6 ≤ s := by rw [hsd]; linarith
  have hshi : s ≤ (7 : ℝ) / 8 := by rw [hsd]; linarith
  have h1s : 0 < 1 + s := by linarith
  have hA : (1 / 2) / (1 + s) ≤ 3 / 11 := by
    rw [div_le_iff₀ h1s]; linarith
  have hB : (4 : ℝ) / 15 ≤ (1 / 2) / (1 + s) := by
    rw [le_div_iff₀ h1s]; linarith
  have hDpos : 0 < 1 - (1 / 2) / (1 + s) := by linarith
  have hDle : 1 - (1 / 2) / (1 + s) ≤ 11 / 15 := by linarith
  have h4 : (60 : ℝ) / 11 ≤ 4 / (1 - (1 / 2) / (1 + s)) := by
    have h1 := one_div_le_one_div_of_le hDpos hDle
    have h2 : 4 / (11 / 15) ≤ 4 / (1 - (1 / 2) / (1 + s)) := by
      rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 11 / 15) hDpos]
      linarith [h1]
    linarith [h2]
  have h2s : (11 : ℝ) / 3 ≤ (1 + s) / (1 / 2) := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 1 / 2)]; linarith
  have hmul := mul_le_mul h4 h2s (by norm_num) (by positivity)
  linarith [hmul]

end RobustZ
