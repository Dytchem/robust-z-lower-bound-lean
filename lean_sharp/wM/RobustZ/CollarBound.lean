/-
Copyright (c) 2025 RobustZ project. All rights reserved.

Collar bounds: Chebyshev growth outside `[-1, 1]` and bounds for `approxPoly` on the
collar `|u| ≤ 1 + B / τ`.

Main results:
* `RobustZ.abs_chebyshevT_le_exp` : `|T_j u| ≤ exp (|j| * 2 * √δ)` for `|u| ≤ 1 + δ`.
* `RobustZ.abs_deriv_chebyshevT_le_exp` : the same for `T_j'`, with the factor `j ^ 2`.
* `RobustZ.norm_approxPoly_le_collar` : on the collar `|u| ≤ 1 + B / τ`, under
  `2 √(B/τ) ≤ δ'/2`, `‖approxPoly τ k (u)‖ ≤ exp (τ sinh δ') * 4 / (1 - exp (-δ')) + 1`.
* `RobustZ.norm_deriv_approxPoly_le_collar` : the same for the derivative, with the extra
  factor `k ^ 2`.
* `RobustZ.norm_approxPoly_le_collar_gen`, `RobustZ.norm_deriv_approxPoly_le_collar_gen` :
  versions with the sharp hypothesis `2 √(B/τ) < δ'` and the explicit ratio
  `r = exp (2 √(B/τ) - δ') < 1` in the constant (the two lemmas above are derived from
  these via `r ≤ exp (-δ'/2)`).

The hypotheses only need `0 ≤ τ` (`τ = 0` is allowed: then `B / τ = 0` and the collar is
`|u| ≤ 1`); no strict positivity of `τ` is required.
-/
import RobustZ.ChebDeriv
import Mathlib.Analysis.SpecialFunctions.Arcosh

open Complex
namespace RobustZ

open scoped Real

noncomputable section

/-! ## Elementary hyperbolic estimates -/

/-- `1 + δ ≤ cosh (2 √δ)` for `δ ≥ 0`. -/
private lemma one_add_le_cosh_two_sqrt {δ : ℝ} (hδ : 0 ≤ δ) :
    1 + δ ≤ Real.cosh (2 * Real.sqrt δ) := by
  have hs0 : 0 ≤ Real.sqrt δ := Real.sqrt_nonneg δ
  have hsinh : Real.sqrt δ ≤ Real.sinh (Real.sqrt δ) := Real.self_le_sinh_iff.mpr hs0
  have hsinh0 : 0 ≤ Real.sinh (Real.sqrt δ) := Real.sinh_nonneg_iff.mpr hs0
  have hsq : δ ≤ Real.sinh (Real.sqrt δ) ^ 2 := by
    have h : Real.sqrt δ ^ 2 = δ := Real.sq_sqrt hδ
    nlinarith [hsinh, hsinh0, hs0, h]
  have hcosh : Real.cosh (2 * Real.sqrt δ)
      = Real.cosh (Real.sqrt δ) ^ 2 + Real.sinh (Real.sqrt δ) ^ 2 := by
    rw [show 2 * Real.sqrt δ = Real.sqrt δ + Real.sqrt δ by ring, Real.cosh_add]
    ring
  have hc : Real.cosh (Real.sqrt δ) ^ 2 = Real.sinh (Real.sqrt δ) ^ 2 + 1 := Real.cosh_sq _
  rw [hcosh, hc]
  linarith

/-- `cosh x ≤ exp x` for `x ≥ 0`. -/
private lemma cosh_le_exp {x : ℝ} (hx : 0 ≤ x) : Real.cosh x ≤ Real.exp x := by
  have h : Real.exp (-x) ≤ Real.exp x := Real.exp_le_exp.mpr (by linarith)
  have h2 : Real.cosh x = (Real.exp x + Real.exp (-x)) / 2 := Real.cosh_eq x
  linarith

/-! ## Chebyshev polynomials -/

/-- `|T_j u| ≤ 1` on `[-1, 1]`. -/
private lemma abs_chebT_eval_le_one (j : ℤ) {u : ℝ} (hu : |u| ≤ 1) :
    |(Polynomial.Chebyshev.T ℝ j).eval u| ≤ 1 := by
  have h1 : -1 ≤ u := by linarith [neg_abs_le u]
  have h2 : u ≤ 1 := by linarith [le_abs_self u]
  have hcos : Real.cos (Real.arccos u) = u := Real.cos_arccos h1 h2
  rw [← hcos, Polynomial.Chebyshev.T_real_cos (Real.arccos u) j]
  exact Real.abs_cos_le_one _

/-- `|T_j u| = |T_j |u||`. -/
private lemma abs_chebT_eval_abs (j : ℤ) (u : ℝ) :
    |(Polynomial.Chebyshev.T ℝ j).eval u| = |(Polynomial.Chebyshev.T ℝ j).eval (|u|)| := by
  rcases le_or_gt 0 u with h | h
  · rw [abs_of_nonneg h]
  · have huu : u = -|u| := by rw [abs_of_neg h]; ring
    have hc : |(((j.negOnePow : ℤ) : ℝ))| = 1 := by
      rw [← Int.cast_abs, Int.abs_negOnePow]
      norm_num
    conv_lhs => rw [huu]
    rw [Polynomial.Chebyshev.T_eval_neg ℝ j (|u|), abs_mul, hc, one_mul]

/-- **Chebyshev growth outside `[-1, 1]`.** For `|u| ≤ 1 + δ` and `δ ≥ 0`,
`|T_j(u)| ≤ exp (|j| * 2 * √δ)`. -/
lemma abs_chebyshevT_le_exp (j : ℤ) {u δ : ℝ} (hδ : 0 ≤ δ) (hu : |u| ≤ 1 + δ) :
    |(Polynomial.Chebyshev.T ℝ j).eval u| ≤ Real.exp (|(j : ℝ)| * 2 * Real.sqrt δ) := by
  have ht0 : 0 ≤ 2 * Real.sqrt δ := by positivity
  have hexp1 : 1 ≤ Real.exp (|(j : ℝ)| * 2 * Real.sqrt δ) := Real.one_le_exp (by positivity)
  rcases le_or_gt |u| 1 with hsm | hbg
  · exact (abs_chebT_eval_le_one j hsm).trans hexp1
  · have hvu : 1 ≤ |u| := le_of_lt hbg
    have hcosh : Real.cosh (Real.arcosh |u|) = |u| := Real.cosh_arcosh hvu
    have hle : Real.arcosh |u| ≤ 2 * Real.sqrt δ := by
      have h3 : Real.cosh (Real.arcosh (|u|)) ≤ Real.cosh (2 * Real.sqrt δ) := by
        rw [hcosh]
        exact hu.trans (one_add_le_cosh_two_sqrt hδ)
      have h4 : |Real.arcosh (|u|)| ≤ |2 * Real.sqrt δ| := Real.cosh_le_cosh.mp h3
      rw [abs_of_nonneg (Real.arcosh_nonneg hvu), abs_of_nonneg ht0] at h4
      exact h4
    have hT : (Polynomial.Chebyshev.T ℝ j).eval |u|
        = Real.cosh ((j : ℝ) * Real.arcosh |u|) := by
      conv_lhs => rw [← hcosh]
      exact Polynomial.Chebyshev.T_real_cosh (Real.arcosh |u|) j
    rw [abs_chebT_eval_abs j u, hT, abs_of_pos (Real.cosh_pos _)]
    have habs : Real.cosh ((j : ℝ) * Real.arcosh |u|)
        = Real.cosh (|(j : ℝ)| * Real.arcosh |u|) := by
      rw [← Real.cosh_abs, abs_mul, abs_of_nonneg (Real.arcosh_nonneg hvu)]
    rw [habs]
    have harg0 : 0 ≤ |(j : ℝ)| * Real.arcosh (|u|) :=
      mul_nonneg (abs_nonneg (j : ℝ)) (Real.arcosh_nonneg hvu)
    refine (cosh_le_exp harg0).trans (Real.exp_le_exp.mpr ?_)
    calc |(j : ℝ)| * Real.arcosh (|u|) ≤ |(j : ℝ)| * (2 * Real.sqrt δ) :=
          mul_le_mul_of_nonneg_left hle (abs_nonneg (j : ℝ))
      _ = |(j : ℝ)| * 2 * Real.sqrt δ := by ring

/-! ## Collar bounds for `approxPoly` -/

/-- Arithmetic core of the collar constant: for `s = exp (-δ'/2)` and `0 < s < 1`,
`1 + 2 s / (1 - s) ≤ 4 / (1 - exp (-δ'))`. -/
private lemma one_add_two_mul_div_le_four (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) {δ' : ℝ}
    (hse : s ^ 2 = Real.exp (-δ')) :
    1 + 2 * s / (1 - s) ≤ 4 / (1 - Real.exp (-δ')) := by
  have h1s : 0 < 1 - s := by linarith
  have h1ps : 0 < 1 + s := by linarith
  have hfac : 1 - Real.exp (-δ') = (1 - s) * (1 + s) := by
    rw [← hse]
    ring
  have hlhs : 1 + 2 * s / (1 - s) = (1 + s) / (1 - s) := by
    field_simp
    ring
  have hsq : (1 + s) ^ 2 ≤ 4 := by
    have h2 : 1 + s ≤ 2 := by linarith
    nlinarith [h2, h1ps.le]
  rw [hlhs, hfac, div_le_iff₀ h1s]
  have hsimp : 4 / ((1 - s) * (1 + s)) * (1 - s) = 4 / (1 + s) := by
    field_simp
  rw [hsimp, le_div_iff₀ h1ps]
  nlinarith [hsq]

/-- **General collar bound for `approxPoly`.**  Under the hypothesis `2 √(B/τ) < δ'` the
polynomial `approxPoly τ k` is bounded on the collar `|u| ≤ 1 + B/τ` by
`exp (τ sinh δ') * (1 + 2 r / (1 - r))` with the explicit ratio
`r = exp (2 √(B/τ) - δ') < 1`; the bound is uniform in `k`. -/
lemma norm_approxPoly_le_collar_gen (τ : ℝ) (hτ : 0 ≤ τ) {δ' : ℝ} (hδ' : 0 < δ') (k : ℕ)
    {B : ℝ} (hB : 0 < B) (hsmall : 2 * Real.sqrt (B / τ) < δ')
    {u : ℝ} (hu : |u| ≤ 1 + B / τ) :
    ‖(approxPoly τ k).eval (u : ℂ)‖
      ≤ Real.exp (τ * Real.sinh δ')
        * (1 + 2 * Real.exp (2 * Real.sqrt (B / τ) - δ')
            / (1 - Real.exp (2 * Real.sqrt (B / τ) - δ'))) := by
  have hδ0 : 0 ≤ B / τ := by positivity
  set E : ℝ := Real.exp (τ * Real.sinh δ') with hE
  set r : ℝ := Real.exp (2 * Real.sqrt (B / τ) - δ') with hr
  have hE0 : 0 < E := by rw [hE]; positivity
  have hr0 : 0 < r := by rw [hr]; positivity
  have hr1 : r < 1 := by
    rw [hr]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hpow : ∀ m : ℕ, Real.exp (((m + 1 : ℕ) : ℝ) * (2 * Real.sqrt (B / τ) - δ'))
      = r ^ (m + 1) := by
    intro m
    rw [hr, ← Real.exp_nat_mul]
  have hgeom : ∑ m ∈ Finset.range (k - 1), r ^ m ≤ (1 - r)⁻¹ := by
    have h := geom_sum_mul_neg r (k - 1)
    have h1 : (∑ m ∈ Finset.range (k - 1), r ^ m) * (1 - r) ≤ 1 := by
      rw [h]
      have h2 : (0 : ℝ) ≤ r ^ (k - 1) := by positivity
      linarith
    have h2 : 0 < 1 - r := by linarith
    rw [inv_eq_one_div, le_div_iff₀ h2]
    exact h1
  have hterm : ∀ m ∈ Finset.range (k - 1),
      ‖2 * fcoef τ ((m : ℤ) + 1) * (Polynomial.Chebyshev.T ℂ ((m : ℤ) + 1)).eval (u : ℂ)‖
        ≤ 2 * E * r ^ (m + 1) := by
    intro m _
    have hcast : |((((m : ℤ) + 1 : ℤ)) : ℝ)| = ((m + 1 : ℕ) : ℝ) := by
      have h0 : (0 : ℤ) ≤ (m : ℤ) + 1 := by omega
      rw [abs_of_nonneg (by exact_mod_cast h0)]
      push_cast
      ring
    have hf : ‖fcoef τ ((m : ℤ) + 1)‖
        ≤ E * Real.exp (-(((m + 1 : ℕ) : ℝ) * δ')) := by
      have h := norm_fcoef_le τ hτ hδ' ((m : ℤ) + 1)
      rw [hcast] at h
      have h2 : Real.exp (τ * Real.sinh δ' - ((m + 1 : ℕ) : ℝ) * δ')
          = E * Real.exp (-(((m + 1 : ℕ) : ℝ) * δ')) := by
        rw [hE, Real.exp_sub, Real.exp_neg, div_eq_mul_inv]
      rwa [h2] at h
    have hTb : ‖(Polynomial.Chebyshev.T ℂ ((m : ℤ) + 1)).eval (u : ℂ)‖
        ≤ Real.exp (((m + 1 : ℕ) : ℝ) * (2 * Real.sqrt (B / τ))) := by
      have h1 : ‖(Polynomial.Chebyshev.T ℂ ((m : ℤ) + 1)).eval (u : ℂ)‖
          = |(Polynomial.Chebyshev.T ℝ ((m : ℤ) + 1)).eval u| := by
        rw [← Polynomial.Chebyshev.complex_ofReal_eval_T u ((m : ℤ) + 1)]
        exact Complex.norm_real _
      rw [h1]
      have h2 := abs_chebyshevT_le_exp ((m : ℤ) + 1) hδ0 hu
      rw [hcast] at h2
      refine h2.trans (le_of_eq ?_)
      rw [show ((m + 1 : ℕ) : ℝ) * 2 * Real.sqrt (B / τ)
        = ((m + 1 : ℕ) : ℝ) * (2 * Real.sqrt (B / τ)) from by ring]
    have hexp : Real.exp (-(((m + 1 : ℕ) : ℝ) * δ'))
          * Real.exp (((m + 1 : ℕ) : ℝ) * (2 * Real.sqrt (B / τ)))
        = Real.exp (((m + 1 : ℕ) : ℝ) * (2 * Real.sqrt (B / τ) - δ')) := by
      rw [← Real.exp_add,
        show -(((m + 1 : ℕ) : ℝ) * δ')
            + ((m + 1 : ℕ) : ℝ) * (2 * Real.sqrt (B / τ))
          = ((m + 1 : ℕ) : ℝ) * (2 * Real.sqrt (B / τ) - δ') from by ring]
    calc ‖2 * fcoef τ ((m : ℤ) + 1)
          * (Polynomial.Chebyshev.T ℂ ((m : ℤ) + 1)).eval (u : ℂ)‖
        = 2 * ‖fcoef τ ((m : ℤ) + 1)‖
            * ‖(Polynomial.Chebyshev.T ℂ ((m : ℤ) + 1)).eval (u : ℂ)‖ := by
          rw [norm_mul, norm_mul]
          norm_num
      _ ≤ 2 * (E * Real.exp (-(((m + 1 : ℕ) : ℝ) * δ')))
            * Real.exp (((m + 1 : ℕ) : ℝ) * (2 * Real.sqrt (B / τ))) := by
          have h1 : (0 : ℝ) ≤ ‖fcoef τ ((m : ℤ) + 1)‖ := norm_nonneg _
          have h2 : (0 : ℝ) ≤
              ‖(Polynomial.Chebyshev.T ℂ ((m : ℤ) + 1)).eval (u : ℂ)‖ := norm_nonneg _
          nlinarith [hf, hTb, h1, h2]
      _ = 2 * E * (Real.exp (-(((m + 1 : ℕ) : ℝ) * δ'))
            * Real.exp (((m + 1 : ℕ) : ℝ) * (2 * Real.sqrt (B / τ)))) := by ring
      _ = 2 * E * Real.exp (((m + 1 : ℕ) : ℝ) * (2 * Real.sqrt (B / τ) - δ')) := by
          rw [hexp]
      _ = 2 * E * r ^ (m + 1) := by rw [hpow m]
  have hc0 : ‖fcoef τ 0‖ ≤ E := by
    have h := norm_fcoef_le τ hτ hδ' 0
    rw [hE]
    simpa using h
  have hsplit : (approxPoly τ k).eval (u : ℂ)
      = fcoef τ 0 + ∑ m ∈ Finset.range (k - 1),
          2 * fcoef τ ((m : ℤ) + 1)
            * (Polynomial.Chebyshev.T ℂ ((m : ℤ) + 1)).eval (u : ℂ) := by
    rw [approxPoly, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_finsetSum]
    congr 1
    exact Finset.sum_congr rfl fun m _ => by rw [Polynomial.eval_mul, Polynomial.eval_C]
  have hsum : ‖∑ m ∈ Finset.range (k - 1),
        2 * fcoef τ ((m : ℤ) + 1) * (Polynomial.Chebyshev.T ℂ ((m : ℤ) + 1)).eval (u : ℂ)‖
      ≤ 2 * E * (r * (1 - r)⁻¹) := by
    refine (norm_sum_le (Finset.range (k - 1)) _).trans ?_
    calc ∑ m ∈ Finset.range (k - 1),
          ‖2 * fcoef τ ((m : ℤ) + 1)
            * (Polynomial.Chebyshev.T ℂ ((m : ℤ) + 1)).eval (u : ℂ)‖
        ≤ ∑ m ∈ Finset.range (k - 1), 2 * E * r ^ (m + 1) := Finset.sum_le_sum hterm
      _ = 2 * E * r * ∑ m ∈ Finset.range (k - 1), r ^ m := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun m _ => by rw [pow_succ]; ring
      _ ≤ 2 * E * (r * (1 - r)⁻¹) := by
          have h1 : r * ∑ m ∈ Finset.range (k - 1), r ^ m ≤ r * (1 - r)⁻¹ :=
            mul_le_mul_of_nonneg_left hgeom hr0.le
          calc 2 * E * r * ∑ m ∈ Finset.range (k - 1), r ^ m
              = 2 * E * (r * ∑ m ∈ Finset.range (k - 1), r ^ m) := by ring
            _ ≤ 2 * E * (r * (1 - r)⁻¹) := mul_le_mul_of_nonneg_left h1 (by positivity)
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  calc ‖fcoef τ 0‖ + ‖∑ m ∈ Finset.range (k - 1),
        2 * fcoef τ ((m : ℤ) + 1) * (Polynomial.Chebyshev.T ℂ ((m : ℤ) + 1)).eval (u : ℂ)‖
      ≤ E + 2 * E * (r * (1 - r)⁻¹) := add_le_add hc0 hsum
    _ = E * (1 + 2 * r / (1 - r)) := by rw [div_eq_mul_inv]; ring
    _ = Real.exp (τ * Real.sinh δ')
        * (1 + 2 * Real.exp (2 * Real.sqrt (B / τ) - δ')
            / (1 - Real.exp (2 * Real.sqrt (B / τ) - δ'))) := by rw [hE, hr]

/-- **Collar bound for `approxPoly`.**  If `2 √(B/τ) ≤ δ'/2` then on the collar
`|u| ≤ 1 + B/τ` the polynomial `approxPoly τ k` is bounded by
`exp (τ sinh δ') * 4 / (1 - exp (-δ')) + 1`, uniformly in `k`. -/
lemma norm_approxPoly_le_collar (τ : ℝ) (hτ : 0 ≤ τ) {δ' : ℝ} (hδ' : 0 < δ') (k : ℕ)
    {B : ℝ} (hB : 0 < B) (hsmall : 2 * Real.sqrt (B / τ) ≤ δ' / 2)
    {u : ℝ} (hu : |u| ≤ 1 + B / τ) :
    ‖(approxPoly τ k).eval (u : ℂ)‖
      ≤ Real.exp (τ * Real.sinh δ') * 4 / (1 - Real.exp (-δ')) + 1 := by
  have hlt : 2 * Real.sqrt (B / τ) < δ' := by linarith
  refine (norm_approxPoly_le_collar_gen τ hτ hδ' k hB hlt hu).trans ?_
  set s : ℝ := Real.exp (-(δ' / 2)) with hs
  set r : ℝ := Real.exp (2 * Real.sqrt (B / τ) - δ') with hr
  have hE0 : (0 : ℝ) < Real.exp (τ * Real.sinh δ') := Real.exp_pos _
  have hr0 : 0 < r := by rw [hr]; positivity
  have hr1 : r < 1 := by rw [hr]; exact Real.exp_lt_one_iff.mpr (by linarith)
  have hs0 : 0 < s := by rw [hs]; positivity
  have hs1 : s < 1 := by rw [hs]; exact Real.exp_lt_one_iff.mpr (by linarith)
  have hrle : r ≤ s := by
    rw [hr, hs]
    exact Real.exp_le_exp.mpr (by linarith)
  have hse : s ^ 2 = Real.exp (-δ') := by
    rw [hs, ← Real.exp_nat_mul]
    congr 1
    ring
  have h2r : 2 * r / (1 - r) ≤ 2 * s / (1 - s) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    refine mul_le_mul (by linarith) ?_ (inv_nonneg.mpr (by linarith)) (by positivity)
    exact (inv_le_inv₀ (by linarith : (0 : ℝ) < 1 - r)
      (by linarith : (0 : ℝ) < 1 - s)).mpr (by linarith)
  have hmono : 1 + 2 * r / (1 - r) ≤ 1 + 2 * s / (1 - s) := by linarith
  have hfinal : 1 + 2 * s / (1 - s) ≤ 4 / (1 - Real.exp (-δ')) :=
    one_add_two_mul_div_le_four s hs0 hs1 hse
  calc Real.exp (τ * Real.sinh δ') * (1 + 2 * r / (1 - r))
      ≤ Real.exp (τ * Real.sinh δ') * (1 + 2 * s / (1 - s)) :=
        mul_le_mul_of_nonneg_left hmono hE0.le
    _ ≤ Real.exp (τ * Real.sinh δ') * (4 / (1 - Real.exp (-δ'))) :=
        mul_le_mul_of_nonneg_left hfinal hE0.le
    _ = Real.exp (τ * Real.sinh δ') * 4 / (1 - Real.exp (-δ')) := by ring
    _ ≤ Real.exp (τ * Real.sinh δ') * 4 / (1 - Real.exp (-δ')) + 1 := by linarith

/-! ## Derivative bounds -/

/-- `|j| = j.natAbs` for `j : ℤ`. -/
private lemma abs_intCast_eq_natAbs (j : ℤ) : |((j : ℤ) : ℝ)| = (j.natAbs : ℝ) := by
  obtain ⟨k, hk | hk⟩ := Int.eq_nat_or_neg j
  · rw [hk]; simp
  · rw [hk]; simp

/-- `1 - q ^ m ≤ m * (1 - q)` for `0 ≤ q ≤ 1`. -/
private lemma one_sub_pow_le (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1) (m : ℕ) :
    1 - q ^ m ≤ (m : ℝ) * (1 - q) := by
  induction m with
  | zero => simp
  | succ n ih =>
    have hq : q ^ n ≤ 1 := pow_le_one₀ h0 h1
    calc 1 - q ^ (n + 1) = (1 - q ^ n) + q ^ n * (1 - q) := by ring
      _ ≤ (n : ℝ) * (1 - q) + 1 * (1 - q) := by
            have h2 : q ^ n * (1 - q) ≤ 1 * (1 - q) :=
              mul_le_mul_of_nonneg_right hq (by linarith)
            linarith
      _ = ((n + 1 : ℕ) : ℝ) * (1 - q) := by push_cast; ring

/-- `sinh (m t) ≤ m e^{(m-1)t} sinh t` for `t ≥ 0`. -/
private lemma sinh_nat_mul_le (m : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    Real.sinh ((m : ℝ) * t) ≤ (m : ℝ) * Real.exp (((m : ℝ) - 1) * t) * Real.sinh t := by
  rcases eq_or_lt_of_le ht with h | h
  · subst h
    simp
  · have hsinh : 0 < Real.sinh t := Real.sinh_pos_iff.mpr h
    have hq0 : 0 ≤ Real.exp (-(2 * t)) := (Real.exp_pos _).le
    have hq1 : Real.exp (-(2 * t)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hkey := one_sub_pow_le (Real.exp (-(2 * t))) hq0 hq1 m
    have hexp_neg : Real.exp (-t) = Real.exp t * Real.exp (-(2 * t)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hs : 2 * Real.sinh t = Real.exp t * (1 - Real.exp (-(2 * t))) := by
      rw [Real.sinh_eq, hexp_neg]
      ring
    have hsm : 2 * Real.sinh ((m : ℝ) * t)
        = Real.exp ((m : ℝ) * t) * (1 - Real.exp (-(2 * t)) ^ m) := by
      rw [Real.sinh_eq]
      have hexp : Real.exp (-((m : ℝ) * t))
          = Real.exp ((m : ℝ) * t) * Real.exp (-(2 * t)) ^ m := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        ring
      rw [hexp]
      ring
    have hmul : Real.exp (((m : ℝ) - 1) * t) * Real.exp t = Real.exp ((m : ℝ) * t) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have h2 : 2 * Real.sinh ((m : ℝ) * t)
        ≤ (m : ℝ) * Real.exp (((m : ℝ) - 1) * t) * (2 * Real.sinh t) := by
      rw [hsm, hs]
      calc Real.exp ((m : ℝ) * t) * (1 - Real.exp (-(2 * t)) ^ m)
          ≤ Real.exp ((m : ℝ) * t) * ((m : ℝ) * (1 - Real.exp (-(2 * t)))) :=
            mul_le_mul_of_nonneg_left hkey (Real.exp_pos _).le
        _ = (m : ℝ) * Real.exp (((m : ℝ) - 1) * t)
              * (Real.exp t * (1 - Real.exp (-(2 * t)))) := by
            rw [hmul.symm]
            ring
    have hgoal : Real.sinh ((m : ℝ) * t) * 2
        ≤ ((m : ℝ) * Real.exp (((m : ℝ) - 1) * t) * Real.sinh t) * 2 := by
      linarith [h2]
    exact le_of_mul_le_mul_right hgoal (by norm_num)

/-- `T_j' (cosh s) * sinh s = j * sinh (j s)`. -/
private lemma deriv_chebT_cosh_mul_sinh (j : ℤ) (s : ℝ) :
    (Polynomial.Chebyshev.T ℝ j).derivative.eval (Real.cosh s) * Real.sinh s
      = (j : ℝ) * Real.sinh ((j : ℝ) * s) := by
  have h1 : HasDerivAt (fun θ : ℝ => (Polynomial.Chebyshev.T ℝ j).eval (Real.cosh θ))
      ((Polynomial.Chebyshev.T ℝ j).derivative.eval (Real.cosh s) * Real.sinh s) s :=
    (Polynomial.hasDerivAt (Polynomial.Chebyshev.T ℝ j) (Real.cosh s)).comp s
      (Real.hasDerivAt_cosh s)
  have h2 : HasDerivAt (Real.cosh ∘ fun θ : ℝ => (j : ℝ) * θ)
      (Real.sinh ((j : ℝ) * s) * (j : ℝ)) s := by
    have hin : HasDerivAt (fun θ : ℝ => (j : ℝ) * θ) (j : ℝ) s := by
      simpa using (hasDerivAt_id s).const_mul (j : ℝ)
    exact (Real.hasDerivAt_cosh ((j : ℝ) * s)).comp s hin
  have hfun : (fun θ : ℝ => (Polynomial.Chebyshev.T ℝ j).eval (Real.cosh θ))
      = fun θ : ℝ => Real.cosh ((j : ℝ) * θ) :=
    funext fun θ => Polynomial.Chebyshev.T_real_cosh θ j
  have h2' : HasDerivAt (fun θ : ℝ => (Polynomial.Chebyshev.T ℝ j).eval (Real.cosh θ))
      (Real.sinh ((j : ℝ) * s) * (j : ℝ)) s := by
    rw [hfun]
    exact h2
  exact (h1.unique h2').trans (mul_comm _ _)

/-- Parity trick for the derivative of a polynomial. -/
private lemma deriv_eval_neg_of_eval_neg {p : Polynomial ℝ} {c : ℝ}
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

/-- `|T_j' u| = |T_j' |u||`. -/
private lemma abs_deriv_chebT_eval_abs (j : ℤ) (u : ℝ) :
    |(Polynomial.Chebyshev.T ℝ j).derivative.eval u|
      = |(Polynomial.Chebyshev.T ℝ j).derivative.eval (|u|)| := by
  rcases le_or_gt 0 u with h | h
  · rw [abs_of_nonneg h]
  · have huu : u = -|u| := by rw [abs_of_neg h]; ring
    have hT : ∀ y : ℝ, (Polynomial.Chebyshev.T ℝ j).eval (-y)
        = (((j.negOnePow : ℤ) : ℝ)) * (Polynomial.Chebyshev.T ℝ j).eval y :=
      fun y => Polynomial.Chebyshev.T_eval_neg ℝ j y
    have hp := deriv_eval_neg_of_eval_neg hT (|u|)
    have hc : |(((j.negOnePow : ℤ) : ℝ))| = 1 := by
      rw [← Int.cast_abs, Int.abs_negOnePow]
      norm_num
    conv_lhs => rw [huu]
    rw [hp, abs_neg, abs_mul, hc, one_mul]

/-- `|sinh (j s)| = sinh (|j| s)` for `j : ℤ`, `s ≥ 0`. -/
private lemma abs_sinh_intCast_mul (j : ℤ) {s : ℝ} (hs : 0 ≤ s) :
    |Real.sinh ((j : ℝ) * s)| = Real.sinh ((j.natAbs : ℝ) * s) := by
  rcases le_or_gt 0 (j : ℝ) with hj | hj
  · have hjm : (j : ℝ) = (j.natAbs : ℝ) := by
      rw [← abs_intCast_eq_natAbs j, abs_of_nonneg hj]
    rw [hjm, abs_of_nonneg (Real.sinh_nonneg_iff.mpr (by positivity))]
  · have hjm : (j : ℝ) = -((j.natAbs : ℝ)) := by
      have h := abs_intCast_eq_natAbs j
      rw [abs_of_neg hj] at h
      linarith
    rw [hjm, neg_mul, Real.sinh_neg, abs_neg,
      abs_of_nonneg (Real.sinh_nonneg_iff.mpr (by positivity))]

/-- Complex/real correspondence for the derivative of `T_n` on the real axis. -/
private lemma norm_deriv_chebT_complex_eval (n : ℤ) (u : ℝ) :
    ‖(Polynomial.Chebyshev.T ℂ n).derivative.eval (u : ℂ)‖
      = |(Polynomial.Chebyshev.T ℝ n).derivative.eval u| := by
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
  rw [hA.unique hB]
  exact Complex.norm_real _

/-- **Derivative growth outside `[-1, 1]`.**  For `|u| ≤ 1 + δ` and `δ ≥ 0`,
`|T_j'(u)| ≤ j ^ 2 * exp (|j| * 2 * √δ)`. -/
lemma abs_deriv_chebyshevT_le_exp (j : ℤ) {u δ : ℝ} (hδ : 0 ≤ δ) (hu : |u| ≤ 1 + δ) :
    |(Polynomial.Chebyshev.T ℝ j).derivative.eval u|
      ≤ (j : ℝ) ^ 2 * Real.exp (|(j : ℝ)| * 2 * Real.sqrt δ) := by
  have hexp1 : 1 ≤ Real.exp (|(j : ℝ)| * 2 * Real.sqrt δ) := Real.one_le_exp (by positivity)
  have hcast : ((j.natAbs : ℝ)) ^ 2 = (j : ℝ) ^ 2 := by
    rw [← abs_intCast_eq_natAbs j, sq_abs]
  rcases le_or_gt |u| 1 with hsm | hbg
  · have hu' : u ∈ Set.Icc (-1 : ℝ) 1 :=
      ⟨by linarith [neg_abs_le u], by linarith [le_abs_self u]⟩
    refine (abs_deriv_chebyshevT_le j hu').trans ?_
    rw [hcast]
    exact le_mul_of_one_le_right (sq_nonneg _) hexp1
  · have hvu : 1 ≤ |u| := le_of_lt hbg
    have hs0 : 0 < Real.arcosh (|u|) := Real.arcosh_pos hbg
    have hsnn : 0 ≤ Real.arcosh (|u|) := hs0.le
    have hcosh : Real.cosh (Real.arcosh (|u|)) = |u| := Real.cosh_arcosh hvu
    have hle : Real.arcosh (|u|) ≤ 2 * Real.sqrt δ := by
      have h3 : Real.cosh (Real.arcosh (|u|)) ≤ Real.cosh (2 * Real.sqrt δ) := by
        rw [hcosh]
        exact hu.trans (one_add_le_cosh_two_sqrt hδ)
      have h4 : |Real.arcosh (|u|)| ≤ |2 * Real.sqrt δ| := Real.cosh_le_cosh.mp h3
      rw [abs_of_nonneg hsnn, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.sqrt δ)] at h4
      exact h4
    have hid := deriv_chebT_cosh_mul_sinh j (Real.arcosh (|u|))
    rw [hcosh] at hid
    have habs_id : |(Polynomial.Chebyshev.T ℝ j).derivative.eval (|u|)|
          * Real.sinh (Real.arcosh (|u|))
        = |(j : ℝ)| * Real.sinh ((j.natAbs : ℝ) * Real.arcosh (|u|)) := by
      have h1 : |(Polynomial.Chebyshev.T ℝ j).derivative.eval (|u|)|
            * Real.sinh (Real.arcosh (|u|))
          = |(Polynomial.Chebyshev.T ℝ j).derivative.eval (|u|)
            * Real.sinh (Real.arcosh (|u|))| := by
        rw [abs_mul, abs_of_pos (Real.sinh_pos_iff.mpr hs0)]
      rw [h1, hid, abs_mul, abs_sinh_intCast_mul j hsnn]
    have hsinh_le := sinh_nat_mul_le j.natAbs hsnn
    have hmain : |(Polynomial.Chebyshev.T ℝ j).derivative.eval (|u|)|
          * Real.sinh (Real.arcosh (|u|))
        ≤ ((j : ℝ) ^ 2 * Real.exp (((j.natAbs : ℝ) - 1) * Real.arcosh (|u|)))
          * Real.sinh (Real.arcosh (|u|)) := by
      rw [habs_id]
      calc |(j : ℝ)| * Real.sinh ((j.natAbs : ℝ) * Real.arcosh (|u|))
          ≤ |(j : ℝ)| * ((j.natAbs : ℝ) * Real.exp (((j.natAbs : ℝ) - 1) * Real.arcosh (|u|))
              * Real.sinh (Real.arcosh (|u|))) :=
            mul_le_mul_of_nonneg_left hsinh_le (abs_nonneg _)
        _ = ((j : ℝ) ^ 2 * Real.exp (((j.natAbs : ℝ) - 1) * Real.arcosh (|u|)))
              * Real.sinh (Real.arcosh (|u|)) := by
            rw [abs_intCast_eq_natAbs j, ← hcast]
            ring
    have hfin := le_of_mul_le_mul_right hmain (Real.sinh_pos_iff.mpr hs0)
    have hcast2 : |(Polynomial.Chebyshev.T ℝ j).derivative.eval u|
        = |(Polynomial.Chebyshev.T ℝ j).derivative.eval (|u|)| := abs_deriv_chebT_eval_abs j u
    rw [hcast2]
    refine hfin.trans ?_
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (sq_nonneg _)
    have h1 : ((j.natAbs : ℝ) - 1) * Real.arcosh (|u|)
        ≤ (j.natAbs : ℝ) * Real.arcosh (|u|) := by nlinarith [hsnn]
    have h2 : (j.natAbs : ℝ) * Real.arcosh (|u|)
        ≤ (j.natAbs : ℝ) * (2 * Real.sqrt δ) :=
      mul_le_mul_of_nonneg_left hle (by positivity)
    calc ((j.natAbs : ℝ) - 1) * Real.arcosh (|u|)
        ≤ (j.natAbs : ℝ) * Real.arcosh (|u|) := h1
      _ ≤ (j.natAbs : ℝ) * (2 * Real.sqrt δ) := h2
      _ = |(j : ℝ)| * 2 * Real.sqrt δ := by
          rw [abs_intCast_eq_natAbs j]
          ring

/-- The `2 s/(1-s)` form of the collar constant. -/
private lemma two_mul_self_div_le (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) {δ' : ℝ}
    (hse : s ^ 2 = Real.exp (-δ')) :
    2 * (s * (1 - s)⁻¹) ≤ 4 / (1 - Real.exp (-δ')) := by
  have h := one_add_two_mul_div_le_four s hs0 hs1 hse
  have h1 : 2 * s / (1 - s) ≤ 1 + 2 * s / (1 - s) := by
    have h2 : 0 ≤ s / (1 - s) := by positivity
    linarith
  calc 2 * (s * (1 - s)⁻¹) = 2 * s / (1 - s) := by
        rw [div_eq_mul_inv]
        ring
    _ ≤ 1 + 2 * s / (1 - s) := h1
    _ ≤ 4 / (1 - Real.exp (-δ')) := h

/-- **General collar bound for the derivative of `approxPoly`.**  Under the hypothesis
`2 √(B/τ) < δ'` the derivative of `approxPoly τ k` is bounded on the collar `|u| ≤ 1 + B/τ`
by `exp (τ sinh δ') * (1 + 2 r / (1 - r)) * k ^ 2` with `r = exp (2 √(B/τ) - δ') < 1`. -/
lemma norm_deriv_approxPoly_le_collar_gen (τ : ℝ) (hτ : 0 ≤ τ) {δ' : ℝ} (hδ' : 0 < δ')
    (k : ℕ) {B : ℝ} (hB : 0 < B) (hsmall : 2 * Real.sqrt (B / τ) < δ')
    {u : ℝ} (hu : |u| ≤ 1 + B / τ) :
    ‖deriv (fun x : ℝ => (approxPoly τ k).eval (x : ℂ)) u‖
      ≤ Real.exp (τ * Real.sinh δ')
        * (1 + 2 * Real.exp (2 * Real.sqrt (B / τ) - δ')
            / (1 - Real.exp (2 * Real.sqrt (B / τ) - δ'))) * (k : ℝ) ^ 2 := by
  have hδ0 : 0 ≤ B / τ := by positivity
  set E : ℝ := Real.exp (τ * Real.sinh δ') with hE
  set r : ℝ := Real.exp (2 * Real.sqrt (B / τ) - δ') with hr
  have hE0 : 0 < E := by rw [hE]; positivity
  have hr0 : 0 < r := by rw [hr]; positivity
  have hr1 : r < 1 := by
    rw [hr]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hpow : ∀ m : ℕ, Real.exp (((m + 1 : ℕ) : ℝ) * (2 * Real.sqrt (B / τ) - δ'))
      = r ^ (m + 1) := by
    intro m
    rw [hr, ← Real.exp_nat_mul]
  have hgeom : ∑ m ∈ Finset.range (k - 1), r ^ m ≤ (1 - r)⁻¹ := by
    have h := geom_sum_mul_neg r (k - 1)
    have h1 : (∑ m ∈ Finset.range (k - 1), r ^ m) * (1 - r) ≤ 1 := by
      rw [h]
      have h2 : (0 : ℝ) ≤ r ^ (k - 1) := by positivity
      linarith
    have h2 : 0 < 1 - r := by linarith
    rw [inv_eq_one_div, le_div_iff₀ h2]
    exact h1
  rw [deriv_poly_ofReal, eval_derivative_approxPoly]
  refine (norm_sum_le (Finset.range (k - 1)) _).trans ?_
  have hterm : ∀ m ∈ Finset.range (k - 1),
      ‖2 * fcoef τ ((m : ℤ) + 1)
        * (Polynomial.Chebyshev.T ℂ ((m : ℤ) + 1)).derivative.eval (u : ℂ)‖
        ≤ 2 * E * r ^ (m + 1) * (k : ℝ) ^ 2 := by
    intro m hm
    have hmk : m + 1 ≤ k := by
      have h := Finset.mem_range.mp hm
      omega
    have hkc : (((m + 1 : ℕ)) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hmk
    have hcast : |((((m : ℤ) + 1 : ℤ)) : ℝ)| = ((m + 1 : ℕ) : ℝ) := by
      have h0 : (0 : ℤ) ≤ (m : ℤ) + 1 := by omega
      rw [abs_of_nonneg (by exact_mod_cast h0)]
      push_cast
      ring
    have hf : ‖fcoef τ ((m : ℤ) + 1)‖
        ≤ E * Real.exp (-(((m + 1 : ℕ) : ℝ) * δ')) := by
      have h := norm_fcoef_le τ hτ hδ' ((m : ℤ) + 1)
      rw [hcast] at h
      have h2 : Real.exp (τ * Real.sinh δ' - ((m + 1 : ℕ) : ℝ) * δ')
          = E * Real.exp (-(((m + 1 : ℕ) : ℝ) * δ')) := by
        rw [hE, Real.exp_sub, Real.exp_neg, div_eq_mul_inv]
      rwa [h2] at h
    have hTb : ‖(Polynomial.Chebyshev.T ℂ ((m : ℤ) + 1)).derivative.eval (u : ℂ)‖
        ≤ (k : ℝ) ^ 2 * Real.exp (((m + 1 : ℕ) : ℝ) * (2 * Real.sqrt (B / τ))) := by
      have h1 := norm_deriv_chebT_complex_eval ((m : ℤ) + 1) u
      rw [h1]
      have h2 := abs_deriv_chebyshevT_le_exp ((m : ℤ) + 1) hδ0 hu
      rw [hcast] at h2
      refine h2.trans ?_
      have h3 : (((m + 1 : ℕ)) : ℝ) ^ 2 ≤ (k : ℝ) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hkc 2
      calc (((m + 1 : ℕ)) : ℝ) ^ 2
            * Real.exp (((m + 1 : ℕ) : ℝ) * 2 * Real.sqrt (B / τ))
          ≤ (k : ℝ) ^ 2 * Real.exp (((m + 1 : ℕ) : ℝ) * 2 * Real.sqrt (B / τ)) :=
            mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
        _ = (k : ℝ) ^ 2 * Real.exp (((m + 1 : ℕ) : ℝ) * (2 * Real.sqrt (B / τ))) := by
            rw [show ((m + 1 : ℕ) : ℝ) * 2 * Real.sqrt (B / τ)
              = ((m + 1 : ℕ) : ℝ) * (2 * Real.sqrt (B / τ)) from by ring]
    have hexp : Real.exp (-(((m + 1 : ℕ) : ℝ) * δ'))
          * Real.exp (((m + 1 : ℕ) : ℝ) * (2 * Real.sqrt (B / τ)))
        = Real.exp (((m + 1 : ℕ) : ℝ) * (2 * Real.sqrt (B / τ) - δ')) := by
      rw [← Real.exp_add,
        show -(((m + 1 : ℕ) : ℝ) * δ')
            + ((m + 1 : ℕ) : ℝ) * (2 * Real.sqrt (B / τ))
          = ((m + 1 : ℕ) : ℝ) * (2 * Real.sqrt (B / τ) - δ') from by ring]
    calc ‖2 * fcoef τ ((m : ℤ) + 1)
          * (Polynomial.Chebyshev.T ℂ ((m : ℤ) + 1)).derivative.eval (u : ℂ)‖
        = 2 * ‖fcoef τ ((m : ℤ) + 1)‖
            * ‖(Polynomial.Chebyshev.T ℂ ((m : ℤ) + 1)).derivative.eval (u : ℂ)‖ := by
          rw [norm_mul, norm_mul]
          norm_num
      _ ≤ 2 * (E * Real.exp (-(((m + 1 : ℕ) : ℝ) * δ')))
            * ((k : ℝ) ^ 2 * Real.exp (((m + 1 : ℕ) : ℝ) * (2 * Real.sqrt (B / τ)))) := by
          have h1 : (0 : ℝ) ≤ ‖fcoef τ ((m : ℤ) + 1)‖ := norm_nonneg _
          have h2 : (0 : ℝ) ≤
              ‖(Polynomial.Chebyshev.T ℂ ((m : ℤ) + 1)).derivative.eval (u : ℂ)‖ := norm_nonneg _
          nlinarith [hf, hTb, h1, h2]
      _ = 2 * E * (k : ℝ) ^ 2 * (Real.exp (-(((m + 1 : ℕ) : ℝ) * δ'))
            * Real.exp (((m + 1 : ℕ) : ℝ) * (2 * Real.sqrt (B / τ)))) := by ring
      _ = 2 * E * (k : ℝ) ^ 2 * Real.exp (((m + 1 : ℕ) : ℝ) * (2 * Real.sqrt (B / τ) - δ')) := by
          rw [hexp]
      _ = 2 * E * (k : ℝ) ^ 2 * r ^ (m + 1) := by rw [hpow m]
      _ = 2 * E * r ^ (m + 1) * (k : ℝ) ^ 2 := by ring
  have hsum : ∑ m ∈ Finset.range (k - 1),
        ‖2 * fcoef τ ((m : ℤ) + 1)
          * (Polynomial.Chebyshev.T ℂ ((m : ℤ) + 1)).derivative.eval (u : ℂ)‖
      ≤ E * (1 + 2 * r / (1 - r)) * (k : ℝ) ^ 2 := by
    calc ∑ m ∈ Finset.range (k - 1),
          ‖2 * fcoef τ ((m : ℤ) + 1)
            * (Polynomial.Chebyshev.T ℂ ((m : ℤ) + 1)).derivative.eval (u : ℂ)‖
        ≤ ∑ m ∈ Finset.range (k - 1), 2 * E * r ^ (m + 1) * (k : ℝ) ^ 2 :=
          Finset.sum_le_sum hterm
      _ = 2 * E * (k : ℝ) ^ 2 * ∑ m ∈ Finset.range (k - 1), r ^ (m + 1) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun m _ => by ring
      _ = 2 * E * (k : ℝ) ^ 2 * ((∑ m ∈ Finset.range (k - 1), r ^ m) * r) := by
          rw [Finset.sum_mul]
          have h : (∑ m ∈ Finset.range (k - 1), r ^ (m + 1))
              = ∑ m ∈ Finset.range (k - 1), r ^ m * r :=
            Finset.sum_congr rfl fun m _ => by rw [pow_succ]
          rw [h]
      _ ≤ 2 * E * (k : ℝ) ^ 2 * ((1 - r)⁻¹ * r) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hgeom hr0.le) (by positivity)
      _ = 2 * E * (r * (1 - r)⁻¹) * (k : ℝ) ^ 2 := by ring
      _ ≤ E * (1 + 2 * r / (1 - r)) * (k : ℝ) ^ 2 := by
          have h1 : 2 * r / (1 - r) ≤ 1 + 2 * r / (1 - r) := by linarith
          calc 2 * E * (r * (1 - r)⁻¹) * (k : ℝ) ^ 2
              = E * (2 * r / (1 - r)) * (k : ℝ) ^ 2 := by rw [div_eq_mul_inv]; ring
            _ ≤ E * (1 + 2 * r / (1 - r)) * (k : ℝ) ^ 2 :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hE0.le) (sq_nonneg _)
  calc ∑ m ∈ Finset.range (k - 1),
        ‖2 * fcoef τ ((m : ℤ) + 1)
          * (Polynomial.Chebyshev.T ℂ ((m : ℤ) + 1)).derivative.eval (u : ℂ)‖
      ≤ E * (1 + 2 * r / (1 - r)) * (k : ℝ) ^ 2 := hsum
    _ = Real.exp (τ * Real.sinh δ')
        * (1 + 2 * Real.exp (2 * Real.sqrt (B / τ) - δ')
            / (1 - Real.exp (2 * Real.sqrt (B / τ) - δ'))) * (k : ℝ) ^ 2 := by rw [hE, hr]

/-- **Collar bound for the derivative of `approxPoly`.**  If `2 √(B/τ) ≤ δ'/2` then on the
collar `|u| ≤ 1 + B/τ` the derivative of `approxPoly τ k` is bounded by
`exp (τ sinh δ') * 4 / (1 - exp (-δ')) * k ^ 2 + 1`. -/
lemma norm_deriv_approxPoly_le_collar (τ : ℝ) (hτ : 0 ≤ τ) {δ' : ℝ} (hδ' : 0 < δ') (k : ℕ)
    {B : ℝ} (hB : 0 < B) (hsmall : 2 * Real.sqrt (B / τ) ≤ δ' / 2)
    {u : ℝ} (hu : |u| ≤ 1 + B / τ) :
    ‖deriv (fun x : ℝ => (approxPoly τ k).eval (x : ℂ)) u‖
      ≤ Real.exp (τ * Real.sinh δ') * 4 / (1 - Real.exp (-δ')) * (k : ℝ) ^ 2 + 1 := by
  have hlt : 2 * Real.sqrt (B / τ) < δ' := by linarith
  refine (norm_deriv_approxPoly_le_collar_gen τ hτ hδ' k hB hlt hu).trans ?_
  set s : ℝ := Real.exp (-(δ' / 2)) with hs
  set r : ℝ := Real.exp (2 * Real.sqrt (B / τ) - δ') with hr
  have hE0 : (0 : ℝ) < Real.exp (τ * Real.sinh δ') := Real.exp_pos _
  have hr0 : 0 < r := by rw [hr]; positivity
  have hr1 : r < 1 := by rw [hr]; exact Real.exp_lt_one_iff.mpr (by linarith)
  have hs0 : 0 < s := by rw [hs]; positivity
  have hs1 : s < 1 := by rw [hs]; exact Real.exp_lt_one_iff.mpr (by linarith)
  have hrle : r ≤ s := by
    rw [hr, hs]
    exact Real.exp_le_exp.mpr (by linarith)
  have hse : s ^ 2 = Real.exp (-δ') := by
    rw [hs, ← Real.exp_nat_mul]
    congr 1
    ring
  have h2r : 2 * r / (1 - r) ≤ 2 * s / (1 - s) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    refine mul_le_mul (by linarith) ?_ (inv_nonneg.mpr (by linarith)) (by positivity)
    exact (inv_le_inv₀ (by linarith : (0 : ℝ) < 1 - r)
      (by linarith : (0 : ℝ) < 1 - s)).mpr (by linarith)
  have hmono : 1 + 2 * r / (1 - r) ≤ 1 + 2 * s / (1 - s) := by linarith
  have hfinal : 1 + 2 * s / (1 - s) ≤ 4 / (1 - Real.exp (-δ')) :=
    one_add_two_mul_div_le_four s hs0 hs1 hse
  calc Real.exp (τ * Real.sinh δ') * (1 + 2 * r / (1 - r)) * (k : ℝ) ^ 2
      ≤ Real.exp (τ * Real.sinh δ') * (1 + 2 * s / (1 - s)) * (k : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmono hE0.le) (sq_nonneg _)
    _ ≤ Real.exp (τ * Real.sinh δ') * (4 / (1 - Real.exp (-δ'))) * (k : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfinal hE0.le) (sq_nonneg _)
    _ = Real.exp (τ * Real.sinh δ') * 4 / (1 - Real.exp (-δ')) * (k : ℝ) ^ 2 := by ring
    _ ≤ Real.exp (τ * Real.sinh δ') * 4 / (1 - Real.exp (-δ')) * (k : ℝ) ^ 2 + 1 := by linarith

end

end RobustZ
