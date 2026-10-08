import RobustZ.NewRung
import RobustZ.Approx
import RobustZ.BesselTail
import RobustZ.ChebDeriv
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Chebyshev bundle discharge (D1).

Construct `nrCheb` from the tree's real Chebyshev truncation:
`a m = 2 * fcoef τ (q+m)`, `Q = (approxPoly τ q).comp (C τ⁻¹ * X)`,
`Ψ μ = exp(-iμ) - Q(μ)`, `χ ≡ 1`.

* (i) `‖a m‖ ≤ 2 * majorB τ (q+m)` via `bessel_L1`.
* (ii)-(iv) `HasSum` for `Ψ`, `Ψ'`, `Ψ''` via finite-sum limit (for `Ψ`)
  and termwise differentiation (`hasDerivAt_tsum_of_isPreconnected`
  + continuity extension to endpoints).
-/

noncomputable section

namespace RobustZ

set_option maxHeartbeats 800000

open scoped Real
open Finset Filter Topology

/-- Remainder coefficients: `2 * fcoef`. -/
noncomputable def cbA (τ : ℝ) (q : ℕ) (m : ℕ) : ℂ :=
  2 * fcoef τ (((q + m : ℕ)) : ℤ)

/-- Scaling polynomial `C τ⁻¹ * X` (maps `μ ↦ μ/τ`). -/
noncomputable def cbScale (τ : ℝ) : Polynomial ℂ :=
  Polynomial.C ((((τ⁻¹ : ℝ)) : ℂ)) * Polynomial.X

/-- Truncation polynomial in `μ`: `approxPoly τ q` rescaled. -/
noncomputable def cbQ (τ : ℝ) (q : ℕ) : Polynomial ℂ :=
  (approxPoly τ q).comp (cbScale τ)

/-- Remainder function `Ψ μ = e^{-iμ} - Q(μ)`. -/
noncomputable def cbPsi (τ : ℝ) (q : ℕ) (μ : ℝ) : ℂ :=
  Complex.exp (-((μ : ℂ)) * Complex.I) - (cbQ τ q).eval ((μ : ℂ))

/-- Cutoff `χ ≡ 1` (satisfies all `nrCheb` χ-fields with `K = 4`). -/
noncomputable def cbChi : ℝ → ℝ := fun _ => 1

/-- `cbScale` evaluates to `μ/τ`. -/
lemma cbScale_eval (τ : ℝ) (hτ : τ ≠ 0) (μ : ℝ) :
    (cbScale τ).eval ((μ : ℂ)) = (((μ / τ : ℝ)) : ℂ) := by
  unfold cbScale
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  have h : ((((τ⁻¹ : ℝ)) : ℂ)) * ((μ : ℂ)) = (((μ / τ : ℝ)) : ℂ) := by
    push_cast
    rw [div_eq_mul_inv]
    ring
  exact h

/-- `cbQ` evaluates to `approxPoly` at `μ/τ`. -/
lemma cbQ_eval (τ : ℝ) (hτ : τ ≠ 0) (q : ℕ) (μ : ℝ) :
    (cbQ τ q).eval ((μ : ℂ)) = (approxPoly τ q).eval (((μ / τ : ℝ)) : ℂ) := by
  unfold cbQ
  rw [Polynomial.eval_comp, cbScale_eval τ hτ μ]

/-- `natDegree (C a * X) = 1` for `a ≠ 0`. -/
lemma natDegree_C_mul_X' (a : ℂ) (ha : a ≠ 0) :
    (Polynomial.C a * Polynomial.X : Polynomial ℂ).natDegree = 1 := by
  rw [Polynomial.natDegree_C_mul ha, Polynomial.natDegree_X]

/-- `cbScale` has degree 1 when `τ ≠ 0`. -/
lemma cbScale_natDegree (τ : ℝ) (hτ : τ ≠ 0) : (cbScale τ).natDegree = 1 := by
  unfold cbScale
  apply natDegree_C_mul_X'
  simp only [ne_eq, Complex.ofReal_eq_zero]
  exact inv_ne_zero hτ

/-- Each `approxPoly` summand has degree `≤ m+1`. -/
lemma approxPoly_summand_natDegree_le (τ : ℝ) (m : ℕ) :
    (Polynomial.C (2 * fcoef τ ((m : ℤ) + 1))
      * Polynomial.Chebyshev.T ℂ ((m : ℤ) + 1)).natDegree ≤ m + 1 := by
  have hT : (Polynomial.Chebyshev.T ℂ ((m : ℤ) + 1)).natDegree = m + 1 := by
    rw [Polynomial.Chebyshev.natDegree_T]
    have e : (((m : ℤ) + 1).natAbs) = m + 1 := by
      have h1 : ((m : ℤ) + 1) = (((m + 1 : ℕ)) : ℤ) := by push_cast; ring
      rw [h1, Int.natAbs_natCast]
    rw [e]
  calc (Polynomial.C (2 * fcoef τ ((m : ℤ) + 1))
        * Polynomial.Chebyshev.T ℂ ((m : ℤ) + 1)).natDegree
      ≤ (Polynomial.Chebyshev.T ℂ ((m : ℤ) + 1)).natDegree :=
        Polynomial.natDegree_C_mul_le _ _
    _ = m + 1 := hT

/-- `approxPoly τ q` has degree `< q` (for `1 ≤ q`). -/
lemma approxPoly_natDegree_lt (τ : ℝ) (q : ℕ) (hq : 1 ≤ q) :
    (approxPoly τ q).natDegree < q := by
  have hbound : ∀ m ∈ Finset.range (q - 1),
      (Polynomial.C (2 * fcoef τ ((m : ℤ) + 1))
        * Polynomial.Chebyshev.T ℂ ((m : ℤ) + 1)).natDegree ≤ q - 1 := by
    intro m hm
    have hm' : m + 1 ≤ q - 1 := by
      have hmem : m < q - 1 := Finset.mem_range.mp hm
      omega
    exact (approxPoly_summand_natDegree_le τ m).trans hm'
  have hsum : (∑ m ∈ Finset.range (q - 1),
      (Polynomial.C (2 * fcoef τ ((m : ℤ) + 1))
        * Polynomial.Chebyshev.T ℂ ((m : ℤ) + 1))).natDegree ≤ q - 1 :=
    Polynomial.natDegree_sum_le_of_forall_le _ _ hbound
  have hC0 : (Polynomial.C (fcoef τ 0)).natDegree ≤ q - 1 := by
    rw [Polynomial.natDegree_C]
    exact Nat.zero_le _
  have hadd : (approxPoly τ q).natDegree ≤ q - 1 := by
    unfold approxPoly
    calc (Polynomial.C (fcoef τ 0) + ∑ m ∈ Finset.range (q - 1),
        (Polynomial.C (2 * fcoef τ ((m : ℤ) + 1))
          * Polynomial.Chebyshev.T ℂ ((m : ℤ) + 1))).natDegree
        ≤ max (Polynomial.C (fcoef τ 0)).natDegree
          (∑ m ∈ Finset.range (q - 1),
            (Polynomial.C (2 * fcoef τ ((m : ℤ) + 1))
              * Polynomial.Chebyshev.T ℂ ((m : ℤ) + 1))).natDegree :=
          Polynomial.natDegree_add_le _ _
      _ ≤ q - 1 := max_le hC0 hsum
  omega

/-- `cbQ` has degree `< q`. -/
lemma cbQ_natDegree_lt (τ : ℝ) (hτ : τ ≠ 0) (q : ℕ) (hq : 1 ≤ q) :
    (cbQ τ q).natDegree < q := by
  unfold cbQ
  rw [Polynomial.natDegree_comp, cbScale_natDegree τ hτ, mul_one]
  exact approxPoly_natDegree_lt τ q hq

/-- `ofReal` as `ℝ → ℂ` is smooth. -/
lemma ofReal_contDiff (n : WithTop ℕ∞) :
    ContDiff ℝ n (fun μ : ℝ => ((μ : ℂ))) :=
  Complex.ofRealCLM.contDiff

/-- Any complex polynomial evaluated at `ofReal` is smooth. -/
lemma poly_ofReal_contDiff (p : Polynomial ℂ) (n : WithTop ℕ∞) :
    ContDiff ℝ n (fun μ : ℝ => p.eval ((μ : ℂ))) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa [Polynomial.eval_add] using hp.add hq
  | monomial k a =>
    have hX : ContDiff ℝ n (fun μ : ℝ => ((μ : ℂ))) := ofReal_contDiff n
    have hpow : ContDiff ℝ n (fun μ : ℝ => ((μ : ℂ)) ^ k) := hX.pow k
    have heq : (fun μ : ℝ => (Polynomial.monomial k a).eval ((μ : ℂ)))
        = (fun μ : ℝ => a * (((μ : ℂ)) ^ k)) := by
      funext μ
      rw [Polynomial.eval_monomial]
    rw [heq]
    exact (contDiff_const (c := a)).mul hpow

/-- The exponential factor is smooth. -/
lemma expNeg_contDiff :
    ContDiff ℝ 2 (fun μ : ℝ => Complex.exp (-((μ : ℂ)) * Complex.I)) := by
  have hinner : ContDiff ℝ (2 : WithTop ℕ∞) (fun μ : ℝ => -((μ : ℂ)) * Complex.I) := by
    have hof : ContDiff ℝ (2 : WithTop ℕ∞) (fun μ : ℝ => ((μ : ℂ))) :=
      ofReal_contDiff _
    have hneg : ContDiff ℝ (2 : WithTop ℕ∞) (fun μ : ℝ => -((μ : ℂ))) :=
      hof.neg
    simpa using hneg.mul (contDiff_const (c := Complex.I))
  exact hinner.cexp

/-- `cbPsi` is `C²`. -/
lemma cbPsi_contDiff (τ : ℝ) (q : ℕ) : ContDiff ℝ 2 (cbPsi τ q) := by
  unfold cbPsi
  exact expNeg_contDiff.sub (poly_ofReal_contDiff (cbQ τ q) 2)

/-- `cbChi` is `C²`. -/
lemma cbChi_contDiff : ContDiff ℝ 2 cbChi := by
  unfold cbChi
  exact contDiff_const

/-- `μ/τ ∈ [-1,1]` for `|μ| ≤ τ`, `0 < τ`. -/
lemma cb_div_mem (τ μ : ℝ) (hτ : 0 < τ) (hμ : |μ| ≤ τ) :
    μ / τ ∈ Set.Icc (-1 : ℝ) 1 := by
  have h1 : |μ / τ| ≤ 1 := by
    rw [abs_div, abs_of_pos hτ]
    exact (div_le_one hτ).mpr hμ
  exact Set.mem_Icc.mpr ⟨(abs_le.mp h1).1, (abs_le.mp h1).2⟩

/-- Term-0 bound for `cbA` (mirrors `nr_term0_le`). -/
lemma cb_term0_le (τ : ℝ) (q : ℕ) (hτ1 : 1 ≤ τ)
    (μ : ℝ) (hμ : |μ| ≤ τ) (m : ℕ)
    (hA : ‖cbA τ q m‖ ≤ 2 * majorB τ (q + m)) :
    ‖nrTerm0 (cbA τ q) τ q m μ‖ ≤ 2 * majorB τ (q + m) := by
  have hτ : 0 < τ := by linarith
  have hu := cb_div_mem τ μ hτ hμ
  have hT := nr_norm_chebT_le_one (((q + m : ℕ)) : ℤ) hu
  have hBnn : (0 : ℝ) ≤ 2 * majorB τ (q + m) :=
    mul_nonneg (by norm_num) (nr_majorB_nonneg _ _)
  unfold nrTerm0
  rw [norm_mul]
  exact (mul_le_mul hA hT (norm_nonneg _) hBnn).trans_eq (mul_one _)

/-- Summability of term-0 at a fixed `μ`. -/
lemma cb_summable_term0 (τ : ℝ) (hτ1 : 1 ≤ τ) (q : ℕ) (hq1 : 1 ≤ q)
    (hlt : τ < (q : ℝ)) (μ : ℝ) (hμ : |μ| ≤ τ)
    (hA : ∀ m, ‖cbA τ q m‖ ≤ 2 * majorB τ (q + m)) :
    Summable (fun m : ℕ => nrTerm0 (cbA τ q) τ q m μ) := by
  have hτ : 0 < τ := by linarith
  have hCsum : Summable (fun m : ℕ => 2 * majorB τ (q + m)) :=
    (nr_summable_majorB hτ hq1 hlt).mul_left 2
  have hnorm : Summable (fun m : ℕ => ‖nrTerm0 (cbA τ q) τ q m μ‖) :=
    Summable.of_nonneg_of_le (fun m => norm_nonneg _)
      (fun m => cb_term0_le τ q hτ1 μ hμ m (hA m)) hCsum
  exact Summable.of_norm hnorm

/-- Pick `θ ∈ Ioc 0 2π` with `cos θ = μ/τ`. -/
lemma cb_pick_theta (τ : ℝ) (hτ : 0 < τ) (μ : ℝ) (hμ : |μ| ≤ τ) :
    ∃ θ : ℝ, θ ∈ Set.Ioc 0 (2 * Real.pi) ∧ Real.cos θ = μ / τ := by
  have hu_le : μ / τ ≤ 1 := by
    rw [div_le_one hτ]
    exact (abs_le.mp hμ).2
  have hu_ge : -1 ≤ μ / τ := by
    have h1 : -(τ) ≤ μ := (abs_le.mp hμ).1
    have h2 : (-1 : ℝ) * τ ≤ μ := by linarith
    rw [le_div_iff₀ hτ]
    linarith
  by_cases hu1 : μ / τ = 1
  · refine ⟨2 * Real.pi, ⟨by positivity, le_rfl⟩, ?_⟩
    rw [Real.cos_two_pi, hu1]
  · have hlt : μ / τ < 1 := lt_of_le_of_ne hu_le hu1
    refine ⟨Real.arccos (μ / τ), ⟨?_, ?_⟩, Real.cos_arccos hu_ge hu_le⟩
    · have hpos : 0 < Real.arccos (μ / τ) := by
        have h1 : Real.arccos (μ / τ) ≠ 0 := by
          intro h0
          have hcos : Real.cos (Real.arccos (μ / τ)) = 1 := by
            rw [h0, Real.cos_zero]
          rw [Real.cos_arccos hu_ge hu_le] at hcos
          exact hu1 hcos
        have hnn : 0 ≤ Real.arccos (μ / τ) := Real.arccos_nonneg _
        exact lt_of_le_of_ne hnn (Ne.symm h1)
      exact hpos
    · have hle : Real.arccos (μ / τ) ≤ Real.pi := Real.arccos_le_pi _
      have h2pi : Real.pi < 2 * Real.pi := by
        have hpi : 0 < Real.pi := Real.pi_pos
        linarith
      linarith

/-- Geometric tail `r^K → 0` helper. -/
lemma cb_geom_tendsto (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (C : ℝ) :
    Filter.Tendsto (fun K : ℕ => C * r ^ K) Filter.atTop (nhds 0) := by
  have hlim : Filter.Tendsto (fun K : ℕ => r ^ K) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
  have e : (0 : ℝ) = C * 0 := by ring
  rw [e]
  exact hlim.const_mul C

/-- `exp(-iμ) = exp(-iτ cosθ)` when `cosθ = μ/τ`. -/
lemma cb_exp_eq (τ μ θ : ℝ) (hτ : τ ≠ 0) (hcos : Real.cos θ = μ / τ) :
    (Complex.exp (-((μ : ℂ)) * Complex.I))
      = (Complex.exp (-((τ : ℂ)) * Complex.I * Complex.cos ((θ : ℂ)))) := by
  have hμeq : τ * Real.cos θ = μ := by
    rw [hcos]
    field_simp
  have hμC : ((μ : ℂ)) = ((τ : ℂ)) * Complex.cos ((θ : ℂ)) := by
    have e1 : ((μ : ℂ)) = (((τ * Real.cos θ : ℝ)) : ℂ) := by
      rw [hμeq]
    rw [e1]
    simp [Complex.ofReal_cos]
  congr 1
  rw [hμC]
  ring

/-- `ofReal (μ/τ) = ofReal (cosθ)` rewriting. -/
lemma cb_ofReal_eq (μ τ θ : ℝ) (hcos : Real.cos θ = μ / τ) :
    (Complex.ofReal (μ / τ)) = Complex.ofReal (Real.cos θ) := by
  rw [hcos]

/-- `approxPoly_{q+K}(μ/τ) → exp(-iμ)` (with `δ = 1`). -/
lemma cb_approx_tendsto (τ : ℝ) (hτ0 : 0 ≤ τ) (q : ℕ) (hq1 : 1 ≤ q)
    (μ θ : ℝ) (hθ : θ ∈ Set.Ioc 0 (2 * Real.pi))
    (hcos : Real.cos θ = μ / τ) :
    Filter.Tendsto (fun K : ℕ => (approxPoly τ (q + K)).eval
      (Complex.ofReal (μ / τ))) Filter.atTop
      (nhds (Complex.exp (-((τ : ℂ)) * Complex.I * Complex.cos ((θ : ℂ))))) := by
  have hδ : (0 : ℝ) < 1 := by norm_num
  have hr0 : (0 : ℝ) ≤ Real.exp (-1 : ℝ) := Real.exp_nonneg _
  have hr1 : Real.exp (-1 : ℝ) < 1 := by
    rw [Real.exp_lt_one_iff]
    norm_num
  have hr_ne : (1 : ℝ) - Real.exp (-1 : ℝ) ≠ 0 := by
    have hpos : (0 : ℝ) < 1 - Real.exp (-1 : ℝ) := by linarith
    exact ne_of_gt hpos
  -- Rewrite `ofReal (μ/τ)` as `ofReal (cosθ)`
  have heq_of : Complex.ofReal (μ / τ) = Complex.ofReal (Real.cos θ) :=
    cb_ofReal_eq μ τ θ hcos
  -- `‖c_{q+K}‖ ≤ E * r^{q+K}` with `E = exp(τ sinh1)`, `r = exp(-1)`
  have hcoef : ∀ K : ℕ,
      ‖fcoef τ ((↑(q + K) : ℕ) : ℤ)‖
        ≤ Real.exp (τ * Real.sinh 1) * Real.exp (-1 : ℝ) ^ (q + K) := by
    intro K
    have hb := norm_fcoef_le τ hτ0 hδ ((↑(q + K) : ℕ) : ℤ)
    have habs2 : |((((↑(q + K) : ℕ) : ℤ) : ℝ))| = (((q + K : ℕ) : ℝ)) := by
      rw [Int.cast_natCast]
      exact abs_of_nonneg (Nat.cast_nonneg _)
    rw [habs2] at hb
    have hexp : Real.exp (τ * Real.sinh 1 - (((q + K : ℕ) : ℝ)) * 1)
        = Real.exp (τ * Real.sinh 1) * Real.exp (-1 : ℝ) ^ (q + K) := by
      have e : τ * Real.sinh 1 - (((q + K : ℕ) : ℝ)) * 1
          = τ * Real.sinh 1 + ((((q + K : ℕ) : ℝ)) * (-1)) := by ring
      rw [e, Real.exp_add]
      congr 1
      rw [Real.exp_nat_mul]
    exact hb.trans (le_of_eq hexp)
  -- Bound for each `K`
  have hbound : ∀ K : ℕ, ‖Complex.exp (-((τ : ℂ)) * Complex.I * Complex.cos ((θ : ℂ)))
      - (approxPoly τ (q + K)).eval (Complex.ofReal (μ / τ))‖
      ≤ (Real.exp (τ * Real.sinh 1) * Real.exp (-1 : ℝ) ^ (q + K))
        + (4 * Real.exp (τ * Real.sinh 1) * Real.exp (-1 : ℝ) ^ (q + K)
          / (1 - Real.exp (-1 : ℝ))) := by
    intro K
    have hqk1 : 1 ≤ q + K := by omega
    have hle := exp_sub_approxPoly_le τ hτ0 hδ hθ hqk1
    rw [heq_of] at ⊢
    exact hle.trans (add_le_add (hcoef K) le_rfl)
  -- RHS `→ 0`
  have htail1 : Filter.Tendsto
      (fun K : ℕ => Real.exp (τ * Real.sinh 1) * Real.exp (-1 : ℝ) ^ (q + K))
      Filter.atTop (nhds 0) := by
    have hpow : Filter.Tendsto (fun K : ℕ => Real.exp (-1 : ℝ) ^ (q + K))
        Filter.atTop (nhds 0) := by
      have hbase : Filter.Tendsto (fun K : ℕ => Real.exp (-1 : ℝ) ^ K)
          Filter.atTop (nhds 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
      have heq : (fun K : ℕ => Real.exp (-1 : ℝ) ^ (q + K))
          = (fun K : ℕ => Real.exp (-1 : ℝ) ^ q * Real.exp (-1 : ℝ) ^ K) := by
        funext K
        rw [pow_add]
      rw [heq]
      have e0 : (0 : ℝ) = Real.exp (-1 : ℝ) ^ q * 0 := by ring
      rw [e0]
      exact hbase.const_mul _
    have e0 : (0 : ℝ) = Real.exp (τ * Real.sinh 1) * 0 := by ring
    have hmul : Filter.Tendsto
        (fun K : ℕ => Real.exp (τ * Real.sinh 1) * (Real.exp (-1 : ℝ) ^ (q + K)))
        Filter.atTop (nhds (Real.exp (τ * Real.sinh 1) * 0)) :=
      hpow.const_mul _
    rw [← e0] at hmul
    -- `E * r^{q+K}` vs `E * (r^{q+K})` same (mul comm not needed, same)
    exact hmul
  have htail2 : Filter.Tendsto
      (fun K : ℕ => 4 * Real.exp (τ * Real.sinh 1) * Real.exp (-1 : ℝ) ^ (q + K)
        / (1 - Real.exp (-1 : ℝ)))
      Filter.atTop (nhds 0) := by
    have h0 : Filter.Tendsto
        (fun K : ℕ => 4 * Real.exp (τ * Real.sinh 1) * Real.exp (-1 : ℝ) ^ (q + K))
        Filter.atTop (nhds 0) := by
      have hpow : Filter.Tendsto (fun K : ℕ => Real.exp (-1 : ℝ) ^ (q + K))
          Filter.atTop (nhds 0) := by
        have hbase : Filter.Tendsto (fun K : ℕ => Real.exp (-1 : ℝ) ^ K)
            Filter.atTop (nhds 0) :=
          tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
        have heq : (fun K : ℕ => Real.exp (-1 : ℝ) ^ (q + K))
            = (fun K : ℕ => Real.exp (-1 : ℝ) ^ q * Real.exp (-1 : ℝ) ^ K) := by
          funext K
          rw [pow_add]
        rw [heq]
        have e0 : (0 : ℝ) = Real.exp (-1 : ℝ) ^ q * 0 := by ring
        rw [e0]
        exact hbase.const_mul _
      have e0 : (4 * Real.exp (τ * Real.sinh 1) * 0 : ℝ) = 0 := by ring
      -- Rewrite `4*E*r^{...}` as `(4*E) * (r^{...})`
      have heq2 : (fun K : ℕ => 4 * Real.exp (τ * Real.sinh 1)
          * Real.exp (-1 : ℝ) ^ (q + K))
          = (fun K : ℕ => (4 * Real.exp (τ * Real.sinh 1))
            * (Real.exp (-1 : ℝ) ^ (q + K))) := by
        funext K
        ring
      rw [heq2]
      have hmul := hpow.const_mul (4 * Real.exp (τ * Real.sinh 1))
      rw [e0] at hmul
      exact hmul
    have e0 : (0 : ℝ) = 0 / (1 - Real.exp (-1 : ℝ)) := by simp
    have heq3 : (fun K : ℕ => 4 * Real.exp (τ * Real.sinh 1)
        * Real.exp (-1 : ℝ) ^ (q + K) / (1 - Real.exp (-1 : ℝ)))
        = (fun K : ℕ => (4 * Real.exp (τ * Real.sinh 1)
          * Real.exp (-1 : ℝ) ^ (q + K)) / (1 - Real.exp (-1 : ℝ))) := by
      funext K
      ring
    rw [heq3, e0]
    exact h0.div_const _
  have hsum0 : Filter.Tendsto
      (fun K : ℕ => (Real.exp (τ * Real.sinh 1) * Real.exp (-1 : ℝ) ^ (q + K))
        + (4 * Real.exp (τ * Real.sinh 1) * Real.exp (-1 : ℝ) ^ (q + K)
          / (1 - Real.exp (-1 : ℝ))))
      Filter.atTop (nhds (0 + 0)) :=
    htail1.add htail2
  rw [add_zero] at hsum0
  -- Squeeze `‖exp - approxPoly| → 0`
  have hnorm0 : Filter.Tendsto
      (fun K : ℕ => ‖Complex.exp (-((τ : ℂ)) * Complex.I * Complex.cos ((θ : ℂ)))
        - (approxPoly τ (q + K)).eval (Complex.ofReal (μ / τ))‖)
      Filter.atTop (nhds 0) :=
    squeeze_zero (fun K => norm_nonneg _) hbound hsum0
  -- Hence `exp - approxPoly → 0`, so `approxPoly → exp`
  have hsub0 : Filter.Tendsto
      (fun K : ℕ => Complex.exp (-((τ : ℂ)) * Complex.I * Complex.cos ((θ : ℂ)))
        - (approxPoly τ (q + K)).eval (Complex.ofReal (μ / τ)))
      Filter.atTop (nhds 0) :=
    (tendsto_zero_iff_norm_tendsto_zero).mpr hnorm0
  have hconst : Filter.Tendsto
      (fun _ : ℕ => Complex.exp (-((τ : ℂ)) * Complex.I * Complex.cos ((θ : ℂ))))
      Filter.atTop
      (nhds (Complex.exp (-((τ : ℂ)) * Complex.I * Complex.cos ((θ : ℂ))))) :=
    tendsto_const_nhds
  have hlim := hconst.sub hsub0
  simp only [sub_sub_cancel, sub_zero] at hlim
  exact hlim

/-- Finite partial sums equal `approxPoly` differences. -/
lemma cb_finite_sum (τ : ℝ) (hτ : τ ≠ 0) (q : ℕ) (hq1 : 1 ≤ q) (μ : ℝ) (K : ℕ) :
    (∑ m ∈ Finset.range K, (nrTerm0 (cbA τ q) τ q m μ))
      = ((approxPoly τ (q + K)).eval (Complex.ofReal (μ / τ))
        - (approxPoly τ q).eval (Complex.ofReal (μ / τ))) := by
  have hqk : (q + K) - 1 = (q - 1) + K := by omega
  have hcast : ∀ m : ℕ, ((↑(q - 1 + m) + 1 : ℤ) = (↑(q + m) : ℤ)) := by
    intro m
    have heq : q - 1 + m + 1 = q + m := by omega
    have e1 : ((↑(q - 1 + m) + 1 : ℤ) = (↑(q - 1 + m + 1) : ℤ)) := by
      push_cast
      ring
    rw [e1, heq]
  -- Unfold `nrTerm0` + `cbA`
  have hexpand : ∀ m : ℕ, (nrTerm0 (cbA τ q) τ q m μ)
      = ((2 * fcoef τ (↑(q + m) : ℤ))
        * ((Polynomial.Chebyshev.T ℂ (↑(q + m) : ℤ)).eval
          (Complex.ofReal (μ / τ)))) := by
    intro m
    unfold nrTerm0 cbA
    ring
  -- `approxPoly` evals
  have heval : ∀ k : ℕ, ((approxPoly τ k).eval (Complex.ofReal (μ / τ)))
      = (fcoef τ 0 + ∑ m ∈ Finset.range (k - 1),
        (((2 * fcoef τ ((m : ℤ) + 1))
          * ((Polynomial.Chebyshev.T ℂ ((m : ℤ) + 1)).eval
            (Complex.ofReal (μ / τ)))))) := by
    intro k
    unfold approxPoly
    rw [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_finsetSum]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Polynomial.eval_mul, Polynomial.eval_C]
  rw [heval (q + K), heval q, hqk]
  rw [Finset.sum_range_add
    (fun m => (((2 * fcoef τ ((m : ℤ) + 1))
      * ((Polynomial.Chebyshev.T ℂ ((m : ℤ) + 1)).eval
        (Complex.ofReal (μ / τ))))))]
  have hmain : (∑ m ∈ Finset.range K, (nrTerm0 (cbA τ q) τ q m μ))
      = (∑ m ∈ Finset.range K, (((2 * fcoef τ ((↑(q - 1 + m) + 1 : ℤ)))
        * ((Polynomial.Chebyshev.T ℂ ((↑(q - 1 + m) + 1 : ℤ))).eval
          (Complex.ofReal (μ / τ)))))) := by
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hexpand m, hcast m]
  rw [hmain]
  ring

/-- Coefficient bound via `bessel_L1`. -/
lemma cbA_bound (τ : ℝ) (hτ : 0 < τ) (q : ℕ) (hq2 : 2 ≤ q)
    (hlt : τ < (q : ℝ)) (m : ℕ) :
    ‖cbA τ q m‖ ≤ 2 * majorB τ (q + m) := by
  unfold cbA
  have hqm1 : 1 ≤ q + m := by omega
  have hltm : τ < ((((q + m : ℕ))) : ℝ) := by
    have hle : (q : ℝ) ≤ ((((q + m : ℕ))) : ℝ) := by
      exact_mod_cast Nat.le_add_right q m
    linarith
  have hL1 := bessel_L1 hτ hqm1 hltm
  have hL1' : ‖fcoef τ ((((q + m : ℕ))) : ℤ)‖ ≤ majorB τ (q + m) := by
    rw [majorB_eq]
    unfold besselF
    exact hL1
  have hnorm2 : ‖(2 : ℂ)‖ = 2 := by
    rw [show (2 : ℂ) = (((2 : ℝ)) : ℂ) by norm_num, Complex.norm_real]
    norm_num
  calc ‖2 * fcoef τ (((q + m : ℕ)) : ℤ)‖
      = ‖(2 : ℂ)‖ * ‖fcoef τ (((q + m : ℕ)) : ℤ)‖ := norm_mul _ _
    _ = 2 * ‖fcoef τ (((q + m : ℕ)) : ℤ)‖ := by rw [hnorm2]
    _ ≤ 2 * majorB τ (q + m) :=
        mul_le_mul_of_nonneg_left hL1' (by norm_num)

/-- `HasDerivAt` for each term-0 (uses `ℂ→ℂ` + `ℝ→ℂ` scomp to get `ℂ • ℂ`). -/
lemma cb_hasDerivAt0 (τ : ℝ) (hτ : 0 < τ) (q m : ℕ) (y : ℝ) :
    HasDerivAt (fun μ : ℝ => nrTerm0 (cbA τ q) τ q m μ)
      (nrTerm1 (cbA τ q) τ q m y) y := by
  have hτ0 : τ ≠ 0 := ne_of_gt hτ
  -- Unfold to `a * T(ofReal (·/τ))` (definitionally equal, no proof needed)
  have heq_fun : (fun μ : ℝ => nrTerm0 (cbA τ q) τ q m μ)
      = (fun μ : ℝ => cbA τ q m
        * (Polynomial.Chebyshev.T ℂ (↑(q + m) : ℤ)).eval
          (Complex.ofReal (μ / τ))) :=
    rfl
  have heq_deriv : nrTerm1 (cbA τ q) τ q m y
      = cbA τ q m * (((Polynomial.Chebyshev.T ℂ (↑(q + m) : ℤ)).derivative.eval
        (Complex.ofReal (y / τ)) / ((τ : ℝ) : ℂ))) :=
    rfl
  rw [heq_fun, heq_deriv]
  -- Inner `h : ℝ → ℂ`, `h μ = ofReal (μ/τ)`, with deriv `ofReal (1/τ) : ℂ`
  have hhR : HasDerivAt (fun μ : ℝ => μ / τ) ((1 : ℝ) / τ) y := by
    simpa using (hasDerivAt_id y).div_const τ
  have h_inner : HasDerivAt (fun μ : ℝ => Complex.ofReal (μ / τ))
      (Complex.ofReal ((1 : ℝ) / τ)) y :=
    hhR.ofReal_comp
  -- Outer `g₁ : ℂ → ℂ`, `g₁ z = p.eval z`, with complex deriv
  have hp : HasDerivAt
      (fun z : ℂ => (Polynomial.Chebyshev.T ℂ (↑(q + m) : ℤ)).eval z)
      (((Polynomial.Chebyshev.T ℂ (↑(q + m) : ℤ)).derivative.eval
        (Complex.ofReal (y / τ)))) (Complex.ofReal (y / τ)) :=
    Polynomial.hasDerivAt _ _
  -- `scomp` with `𝕜=ℝ`, `𝕜'=ℂ`: `(g₁ ∘ h)' = h' • g₁'` with `ℂ • ℂ`
  have hcomp : HasDerivAt
      ((fun z : ℂ => (Polynomial.Chebyshev.T ℂ (↑(q + m) : ℤ)).eval z)
        ∘ (fun μ : ℝ => Complex.ofReal (μ / τ)))
      ((Complex.ofReal ((1 : ℝ) / τ))
        • ((Polynomial.Chebyshev.T ℂ (↑(q + m) : ℤ)).derivative.eval
          (Complex.ofReal (y / τ)))) y := by
    exact hp.scomp y h_inner
  have hfun_eq : ((fun z : ℂ => (Polynomial.Chebyshev.T ℂ (↑(q + m) : ℤ)).eval z)
        ∘ (fun μ : ℝ => Complex.ofReal (μ / τ)))
      = (fun μ : ℝ => (Polynomial.Chebyshev.T ℂ (↑(q + m) : ℤ)).eval
        (Complex.ofReal (μ / τ))) := rfl
  rw [hfun_eq] at hcomp
  have hsmul_eq : ((Complex.ofReal ((1 : ℝ) / τ))
        • ((Polynomial.Chebyshev.T ℂ (↑(q + m) : ℤ)).derivative.eval
          (Complex.ofReal (y / τ))))
      = (((Polynomial.Chebyshev.T ℂ (↑(q + m) : ℤ)).derivative.eval
        (Complex.ofReal (y / τ)) / ((τ : ℝ) : ℂ))) := by
    rw [smul_eq_mul]
    have hof : (Complex.ofReal ((1 : ℝ) / τ)) = 1 / ((τ : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hof]
    ring
  rw [hsmul_eq] at hcomp
  exact hcomp.const_mul (cbA τ q m)

/-- `HasDerivAt` for each term-1 (gives term-2). -/
lemma cb_hasDerivAt1 (τ : ℝ) (hτ : 0 < τ) (q m : ℕ) (y : ℝ) :
    HasDerivAt (fun μ : ℝ => nrTerm1 (cbA τ q) τ q m μ)
      (nrTerm2 (cbA τ q) τ q m y) y := by
  have hτ0 : τ ≠ 0 := ne_of_gt hτ
  have hτC0 : ((τ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hτ0
  have heq_fun : ∀ μ : ℝ, nrTerm1 (cbA τ q) τ q m μ
      = cbA τ q m * ((Polynomial.Chebyshev.T ℂ (↑(q + m) : ℤ)).derivative.eval
        (Complex.ofReal (μ / τ)) / ((τ : ℝ) : ℂ)) :=
    fun μ => rfl
  have heq_deriv : nrTerm2 (cbA τ q) τ q m y
      = cbA τ q m * (((Polynomial.Chebyshev.T ℂ (↑(q + m) : ℤ)).derivative.derivative.eval
        (Complex.ofReal (y / τ)) / ((τ : ℝ) : ℂ) / ((τ : ℝ) : ℂ))) := by
    unfold nrTerm2
    ring
  simp only [heq_fun, heq_deriv]
  -- Inner `T'.eval(ofReal (·/τ))` has deriv `T''.eval/τ` (from previous pattern)
  have hhR : HasDerivAt (fun μ : ℝ => μ / τ) ((1 : ℝ) / τ) y := by
    simpa using (hasDerivAt_id y).div_const τ
  have h_inner : HasDerivAt (fun μ : ℝ => Complex.ofReal (μ / τ))
      (Complex.ofReal ((1 : ℝ) / τ)) y :=
    hhR.ofReal_comp
  have hp : HasDerivAt
      (fun z : ℂ => (Polynomial.Chebyshev.T ℂ (↑(q + m) : ℤ)).derivative.eval z)
      (((Polynomial.Chebyshev.T ℂ (↑(q + m) : ℤ)).derivative.derivative.eval
        (Complex.ofReal (y / τ)))) (Complex.ofReal (y / τ)) :=
    Polynomial.hasDerivAt _ _
  have hcomp : HasDerivAt
      ((fun z : ℂ => (Polynomial.Chebyshev.T ℂ (↑(q + m) : ℤ)).derivative.eval z)
        ∘ (fun μ : ℝ => Complex.ofReal (μ / τ)))
      ((Complex.ofReal ((1 : ℝ) / τ))
        • ((Polynomial.Chebyshev.T ℂ (↑(q + m) : ℤ)).derivative.derivative.eval
          (Complex.ofReal (y / τ)))) y := by
    exact hp.scomp y h_inner
  have hfun_eq : ((fun z : ℂ => (Polynomial.Chebyshev.T ℂ (↑(q + m) : ℤ)).derivative.eval z)
        ∘ (fun μ : ℝ => Complex.ofReal (μ / τ)))
      = (fun μ : ℝ => (Polynomial.Chebyshev.T ℂ (↑(q + m) : ℤ)).derivative.eval
        (Complex.ofReal (μ / τ))) := rfl
  rw [hfun_eq] at hcomp
  have hsmul_eq : ((Complex.ofReal ((1 : ℝ) / τ))
        • ((Polynomial.Chebyshev.T ℂ (↑(q + m) : ℤ)).derivative.derivative.eval
          (Complex.ofReal (y / τ))))
      = (((Polynomial.Chebyshev.T ℂ (↑(q + m) : ℤ)).derivative.derivative.eval
        (Complex.ofReal (y / τ)) / ((τ : ℝ) : ℂ))) := by
    rw [smul_eq_mul]
    have hof : (Complex.ofReal ((1 : ℝ) / τ)) = 1 / ((τ : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hof]
    ring
  -- `t' = T'.eval(...)`, `t'' = T''.eval/τ`, then `/τ` via `div_const`
  have ht'_deriv : HasDerivAt
      (fun μ : ℝ => (Polynomial.Chebyshev.T ℂ (↑(q + m) : ℤ)).derivative.eval
        (Complex.ofReal (μ / τ)))
      (((Polynomial.Chebyshev.T ℂ (↑(q + m) : ℤ)).derivative.derivative.eval
        (Complex.ofReal (y / τ)) / ((τ : ℝ) : ℂ))) y := by
    rw [← hsmul_eq]
    exact hcomp
  have hdiv : HasDerivAt
      (fun μ : ℝ => (Polynomial.Chebyshev.T ℂ (↑(q + m) : ℤ)).derivative.eval
        (Complex.ofReal (μ / τ)) / ((τ : ℝ) : ℂ))
      ((((Polynomial.Chebyshev.T ℂ (↑(q + m) : ℤ)).derivative.derivative.eval
        (Complex.ofReal (y / τ)) / ((τ : ℝ) : ℂ)) / ((τ : ℝ) : ℂ))) y :=
    ht'_deriv.div_const _
  exact hdiv.const_mul (cbA τ q m)

/-- Term-1 bound for `cbA` (mirrors `nr_term1_le`). -/
lemma cb_term1_le (τ : ℝ) (q : ℕ) (hτ1 : 1 ≤ τ)
    (μ : ℝ) (hμ : |μ| ≤ τ) (m : ℕ)
    (hA : ‖cbA τ q m‖ ≤ 2 * majorB τ (q + m)) :
    ‖nrTerm1 (cbA τ q) τ q m μ‖
      ≤ (2 / τ) * ((((q : ℝ) + (m : ℝ)) ^ 2 * majorB τ (q + m))) := by
  have hτ : 0 < τ := by linarith
  have hu := cb_div_mem τ μ hτ hμ
  have hT := norm_deriv_chebyshevT_complex_le (((q + m : ℕ)) : ℤ) hu
  rw [Int.natAbs_natCast] at hT
  have hτC : ‖((((τ : ℝ))) : ℂ)‖ = τ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ]
  have hkm : ((((q + m : ℕ)) : ℝ)) = (q : ℝ) + (m : ℝ) := by
    push_cast
    ring
  have hBnn : (0 : ℝ) ≤ 2 * majorB τ (q + m) :=
    mul_nonneg (by norm_num) (nr_majorB_nonneg _ _)
  unfold nrTerm1
  rw [norm_mul, norm_div, hτC]
  have hT2 : ‖(Polynomial.Chebyshev.T ℂ (((q + m : ℕ)) : ℤ)).derivative.eval
      (((μ / τ : ℝ)) : ℂ)‖ / τ ≤ (((q : ℝ) + (m : ℝ)) ^ 2) / τ := by
    have hle : ‖(Polynomial.Chebyshev.T ℂ (((q + m : ℕ)) : ℤ)).derivative.eval
        (((μ / τ : ℝ)) : ℂ)‖ ≤ (((q : ℝ) + (m : ℝ)) ^ 2) := by
      rw [← hkm]
      exact hT
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hle (inv_nonneg.mpr hτ.le)
  calc ‖cbA τ q m‖ * (‖(Polynomial.Chebyshev.T ℂ (((q + m : ℕ)) : ℤ)).derivative.eval
        (((μ / τ : ℝ)) : ℂ)‖ / τ)
      ≤ (2 * majorB τ (q + m)) * ((((q : ℝ) + (m : ℝ)) ^ 2) / τ) :=
        mul_le_mul hA hT2 (div_nonneg (norm_nonneg _) hτ.le) hBnn
    _ = (2 / τ) * ((((q : ℝ) + (m : ℝ)) ^ 2 * majorB τ (q + m))) := by
        ring

/-- Term-2 bound for `cbA` (mirrors `nr_term2_le`). -/
lemma cb_term2_le (τ : ℝ) (q : ℕ) (hτ1 : 1 ≤ τ)
    (μ : ℝ) (hμ : |μ| ≤ τ) (m : ℕ)
    (hA : ‖cbA τ q m‖ ≤ 2 * majorB τ (q + m)) :
    ‖nrTerm2 (cbA τ q) τ q m μ‖
      ≤ (32 / τ ^ 2)
        * ((((q : ℝ) + (m : ℝ)) ^ 4 * majorB τ (q + m))) := by
  have hτ : 0 < τ := by linarith
  have hu := cb_div_mem τ μ hτ hμ
  have hT := norm_deriv2_chebyshevT_complex_le (((q + m : ℕ)) : ℤ) hu
  rw [Int.natAbs_natCast] at hT
  have hτC : ‖((((τ : ℝ))) : ℂ) ^ 2‖ = τ ^ 2 := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ]
  have hkm : ((((q + m : ℕ)) : ℝ)) = (q : ℝ) + (m : ℝ) := by
    push_cast
    ring
  have hBnn : (0 : ℝ) ≤ 2 * majorB τ (q + m) :=
    mul_nonneg (by norm_num) (nr_majorB_nonneg _ _)
  unfold nrTerm2
  rw [norm_mul, norm_div, hτC]
  have hT16 : ‖(Polynomial.Chebyshev.T ℂ (((q + m : ℕ)) : ℤ)).derivative.derivative.eval
      (((μ / τ : ℝ)) : ℂ)‖ ≤ 16 * (((q : ℝ) + (m : ℝ)) ^ 4) := by
    have h1 := hT
    rwa [hkm] at h1
  have hT2 : ‖(Polynomial.Chebyshev.T ℂ (((q + m : ℕ)) : ℤ)).derivative.derivative.eval
      (((μ / τ : ℝ)) : ℂ)‖ / τ ^ 2
      ≤ (16 * (((q : ℝ) + (m : ℝ)) ^ 4)) / τ ^ 2 := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hT16
      (inv_nonneg.mpr (pow_nonneg hτ.le 2))
  calc ‖cbA τ q m‖ * (‖(Polynomial.Chebyshev.T ℂ (((q + m : ℕ)) : ℤ)).derivative.derivative.eval
        (((μ / τ : ℝ)) : ℂ)‖ / τ ^ 2)
      ≤ (2 * majorB τ (q + m)) * ((16 * (((q : ℝ) + (m : ℝ)) ^ 4)) / τ ^ 2) :=
        mul_le_mul hA hT2
          (div_nonneg (norm_nonneg _) (pow_nonneg hτ.le 2)) hBnn
    _ = (32 / τ ^ 2)
        * ((((q : ℝ) + (m : ℝ)) ^ 4 * majorB τ (q + m))) := by
        ring

/-- Majorant summability for term-1. -/
lemma cb_summable_major1 (τ : ℝ) (hτ : 0 < τ) (q : ℕ) (hq2 : 2 ≤ q)
    (hlt : τ < (q : ℝ)) :
    Summable (fun m : ℕ => (2 / τ) * ((((q : ℝ) + (m : ℝ)) ^ 2 * majorB τ (q + m)))) := by
  have hW : Summable
      (fun m : ℕ => ((((q : ℝ) + (m : ℝ)) ^ 2 * majorB τ (q + m)))) := by
    have h := nr_summable_weighted hτ hq2 hlt 1
    simpa using h
  exact hW.mul_left (2 / τ)

/-- Majorant summability for term-2. -/
lemma cb_summable_major2 (τ : ℝ) (hτ : 0 < τ) (q : ℕ) (hq2 : 2 ≤ q)
    (hlt : τ < (q : ℝ)) :
    Summable (fun m : ℕ => (32 / τ ^ 2)
      * ((((q : ℝ) + (m : ℝ)) ^ 4 * majorB τ (q + m)))) := by
  have hW : Summable
      (fun m : ℕ => ((((q : ℝ) + (m : ℝ)) ^ 4 * majorB τ (q + m)))) := by
    have h := nr_summable_weighted hτ hq2 hlt 2
    simpa using h
  exact hW.mul_left (32 / τ ^ 2)

/-- `HasSum` for `Ψ` (level 0). -/
lemma cb_hasSum0 (τ : ℝ) (hτ1 : 1 ≤ τ) (q : ℕ) (hq2 : 2 ≤ q)
    (hlt : τ < (q : ℝ)) (μ : ℝ) (hμ : |μ| ≤ τ) :
    HasSum (fun m : ℕ => nrTerm0 (cbA τ q) τ q m μ) (cbPsi τ q μ) := by
  have hτ : 0 < τ := by linarith
  have hτ0 : τ ≠ 0 := ne_of_gt hτ
  have hτ0le : 0 ≤ τ := le_of_lt hτ
  have hq1 : 1 ≤ q := by omega
  have hA : ∀ m, ‖cbA τ q m‖ ≤ 2 * majorB τ (q + m) :=
    fun m => cbA_bound τ hτ q hq2 hlt m
  have hsumm : Summable (fun m : ℕ => nrTerm0 (cbA τ q) τ q m μ) :=
    cb_summable_term0 τ hτ1 q hq1 hlt μ hμ hA
  obtain ⟨θ, hθmem, hcos⟩ := cb_pick_theta τ hτ μ hμ
  have hlimA := cb_approx_tendsto τ hτ0le q hq1 μ θ hθmem hcos
  have hexp_eq := cb_exp_eq τ μ θ hτ0 hcos
  rw [← hexp_eq] at hlimA
  -- `hlimA : Tendsto (approxPoly_{q+K}(u)) (𝓝 (exp(-μI)))`
  have hQeq : (cbQ τ q).eval ((μ : ℂ))
      = (approxPoly τ q).eval (Complex.ofReal (μ / τ)) := cbQ_eval τ hτ0 q μ
  have hPsi_eq : cbPsi τ q μ
      = Complex.exp (-((μ : ℂ)) * Complex.I)
        - (approxPoly τ q).eval (Complex.ofReal (μ / τ)) := by
    unfold cbPsi
    rw [hQeq]
  have hpartial : Filter.Tendsto
      (fun K : ℕ => ∑ m ∈ Finset.range K, (nrTerm0 (cbA τ q) τ q m μ))
      Filter.atTop (nhds (cbPsi τ q μ)) := by
    have hsub := hlimA.sub_const
      ((approxPoly τ q).eval (Complex.ofReal (μ / τ)))
    rw [hPsi_eq]
    -- `hsub : Tendsto (F_K - C) (𝓝 (exp - C))`, rewrite `F_K - C` as `∑`
    have heq : (fun K : ℕ => (approxPoly τ (q + K)).eval (Complex.ofReal (μ / τ))
        - (approxPoly τ q).eval (Complex.ofReal (μ / τ)))
        = (fun K : ℕ => ∑ m ∈ Finset.range K, (nrTerm0 (cbA τ q) τ q m μ)) := by
      funext K
      exact (cb_finite_sum τ hτ0 q hq1 μ K).symm
    rw [heq] at hsub
    exact hsub
  have htsum_eq : (∑' m : ℕ, nrTerm0 (cbA τ q) τ q m μ) = cbPsi τ q μ :=
    tendsto_nhds_unique hsumm.hasSum.tendsto_sum_nat hpartial
  rw [← htsum_eq]
  exact hsumm.hasSum

/-- Interior `HasSum` for `Ψ'` (on `Ioo`). -/
lemma cb_hasSum1_interior (τ : ℝ) (hτ1 : 1 ≤ τ) (q : ℕ) (hq2 : 2 ≤ q)
    (hlt : τ < (q : ℝ)) (y : ℝ) (hy : y ∈ Set.Ioo (-τ) τ) :
    HasSum (fun m : ℕ => nrTerm1 (cbA τ q) τ q m y) (deriv (cbPsi τ q) y) := by
  have hτ : 0 < τ := by linarith
  have hq1 : 1 ≤ q := by omega
  have hA : ∀ m, ‖cbA τ q m‖ ≤ 2 * majorB τ (q + m) :=
    fun m => cbA_bound τ hτ q hq2 hlt m
  -- Open preconnected `s`
  set s : Set ℝ := Set.Ioo (-τ) τ with hs_def
  have hs : IsOpen s := isOpen_Ioo
  have hs' : IsPreconnected s := (convex_Ioo _ _).isPreconnected
  -- Majorant
  have hu : Summable
      (fun m : ℕ => (2 / τ) * ((((q : ℝ) + (m : ℝ)) ^ 2 * majorB τ (q + m)))) :=
    cb_summable_major1 τ hτ q hq2 hlt
  -- `g`, `g'`
  have hg : ∀ n (z : ℝ), z ∈ s →
      HasDerivAt (fun μ : ℝ => nrTerm0 (cbA τ q) τ q n μ)
        (nrTerm1 (cbA τ q) τ q n z) z := by
    intro n z _
    exact cb_hasDerivAt0 τ hτ q n z
  have hg' : ∀ n (z : ℝ), z ∈ s →
      ‖nrTerm1 (cbA τ q) τ q n z‖
        ≤ (2 / τ) * ((((q : ℝ) + ((n : ℝ))) ^ 2 * majorB τ (q + n))) := by
    intro n z hz
    have hz_abs : |z| ≤ τ := by
      have hlt_abs : |z| < τ := by
        rw [hs_def] at hz
        exact abs_lt.mpr ⟨by linarith [hz.1], by linarith [hz.2]⟩
      exact le_of_lt hlt_abs
    exact cb_term1_le τ q hτ1 z hz_abs n (hA n)
  have hy0 : (0 : ℝ) ∈ s := by
    rw [hs_def]
    exact ⟨by linarith, by linarith⟩
  have hg0 : Summable (fun n : ℕ => nrTerm0 (cbA τ q) τ q n (0 : ℝ)) := by
    have h0_abs : |(0 : ℝ)| ≤ τ := by simp; linarith
    exact cb_summable_term0 τ hτ1 q hq1 hlt 0 h0_abs hA
  have hHas : HasDerivAt (fun z : ℝ => ∑' n : ℕ, nrTerm0 (cbA τ q) τ q n z)
      (∑' n : ℕ, nrTerm1 (cbA τ q) τ q n y) y :=
    hasDerivAt_tsum_of_isPreconnected hu hs hs' hg hg' hy0 hg0 hy
  -- `tsum = Ψ` on `s`
  have heqOn : Set.EqOn (fun z : ℝ => ∑' n : ℕ, nrTerm0 (cbA τ q) τ q n z)
      (cbPsi τ q) s := by
    intro z hz
    have hz_abs : |z| ≤ τ := by
      have hlt_abs : |z| < τ := by
        rw [hs_def] at hz
        exact abs_lt.mpr ⟨by linarith [hz.1], by linarith [hz.2]⟩
      exact le_of_lt hlt_abs
    exact (cb_hasSum0 τ hτ1 q hq2 hlt z hz_abs).tsum_eq
  have hmem : s ∈ nhds y := hs.mem_nhds hy
  have hev : (cbPsi τ q) =ᶠ[nhds y]
      (fun z : ℝ => ∑' n : ℕ, nrTerm0 (cbA τ q) τ q n z) := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨s, hmem, fun z hz => ?_⟩
    exact (heqOn hz).symm
  have hHasPsi : HasDerivAt (cbPsi τ q)
      (∑' n : ℕ, nrTerm1 (cbA τ q) τ q n y) y :=
    hHas.congr_of_eventuallyEq hev
  have hderiv_eq : deriv (cbPsi τ q) y
      = (∑' n : ℕ, nrTerm1 (cbA τ q) τ q n y) :=
    hHasPsi.deriv
  have hz_abs : |y| ≤ τ := by
    have hlt_abs : |y| < τ := by
      rw [hs_def] at hy
      exact abs_lt.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
    exact le_of_lt hlt_abs
  have hsum : Summable (fun m : ℕ => nrTerm1 (cbA τ q) τ q m y) := by
    have hCsum := cb_summable_major1 τ hτ q hq2 hlt
    have hnorm : Summable (fun m : ℕ => ‖nrTerm1 (cbA τ q) τ q m y‖) :=
      Summable.of_nonneg_of_le (fun m => norm_nonneg _)
        (fun m => cb_term1_le τ q hτ1 y hz_abs m (hA m)) hCsum
    exact Summable.of_norm hnorm
  rw [hderiv_eq]
  exact hsum.hasSum

/-- Sequence inside `Ioo` converging to `τ` (for endpoint extension). -/
lemma cb_seq_right (τ : ℝ) (hτ : 0 < τ) :
    ∃ a : ℕ → ℝ, (∀ n, a n ∈ Set.Ioo (-τ) τ)
      ∧ Filter.Tendsto a Filter.atTop (nhds τ)
      ∧ (∀ n, a n ∈ Set.Icc (-τ) τ) := by
  set a : ℕ → ℝ := fun n : ℕ => τ * ((((n + 1 : ℕ) : ℝ)) / ((((n + 2 : ℕ) : ℝ)))) with ha
  have hIoo : ∀ n, a n ∈ Set.Ioo (-τ) τ := by
    intro n
    rw [ha]
    have hpos1 : (0 : ℝ) ≤ ((((n + 1 : ℕ) : ℝ))) := Nat.cast_nonneg _
    have hpos2 : (0 : ℝ) < ((((n + 2 : ℕ) : ℝ))) := by
      have : (0 : ℕ) < n + 2 := by omega
      exact_mod_cast this
    have hfrac_lt : ((((n + 1 : ℕ) : ℝ))) / ((((n + 2 : ℕ) : ℝ))) < 1 := by
      rw [div_lt_one hpos2]
      have : n + 1 < n + 2 := by omega
      exact_mod_cast this
    have hfrac_nn : (0 : ℝ) ≤ ((((n + 1 : ℕ) : ℝ))) / ((((n + 2 : ℕ) : ℝ))) :=
      div_nonneg hpos1 hpos2.le
    constructor
    · calc -τ < 0 := by linarith
        _ ≤ τ * (((((n + 1 : ℕ) : ℝ))) / ((((n + 2 : ℕ) : ℝ)))) := by
          apply mul_nonneg hτ.le hfrac_nn
    · calc τ * (((((n + 1 : ℕ) : ℝ))) / ((((n + 2 : ℕ) : ℝ))))
          < τ * 1 := by
            apply mul_lt_mul_of_pos_left hfrac_lt hτ
        _ = τ := mul_one _
  have hlim : Filter.Tendsto a Filter.atTop (nhds τ) := by
    rw [ha]
    have hlim_frac : Filter.Tendsto
        (fun n : ℕ => ((((n + 1 : ℕ) : ℝ))) / ((((n + 2 : ℕ) : ℝ))))
        Filter.atTop (nhds 1) := by
      have h1 : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((((n : ℕ) : ℝ)) + 2))
          Filter.atTop (nhds 0) := by
        have hbase : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((((n : ℕ) : ℝ)) + 1))
            Filter.atTop (nhds 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        apply squeeze_zero (fun n => by positivity) _ hbase
        intro n
        apply one_div_le_one_div_of_le _ _
        · have hpos : (0 : ℝ) < ((((n : ℕ) : ℝ)) + 1) := by positivity
          exact hpos
        · have hle : ((((n : ℕ) : ℝ)) + 1) ≤ ((((n : ℕ) : ℝ)) + 2) := by linarith
          exact hle
      have heq : (fun n : ℕ => ((((n + 1 : ℕ) : ℝ))) / ((((n + 2 : ℕ) : ℝ))))
          = (fun n : ℕ => 1 - 1 / (((((n : ℕ) : ℝ))) + 2)) := by
        funext n
        have hcast1 : ((((n + 1 : ℕ) : ℝ))) = ((((n : ℕ) : ℝ))) + 1 := by
          push_cast
          ring
        have hcast2 : ((((n + 2 : ℕ) : ℝ))) = ((((n : ℕ) : ℝ))) + 2 := by
          push_cast
          ring
        rw [hcast1, hcast2]
        field_simp
        ring
      rw [heq]
      have hlim0 : Filter.Tendsto (fun n : ℕ => (1 : ℝ) - 1 / (((((n : ℕ) : ℝ))) + 2))
          Filter.atTop (nhds (1 - 0)) :=
        tendsto_const_nhds.sub h1
      rw [sub_zero] at hlim0
      exact hlim0
    have hlim_mul : Filter.Tendsto
        (fun n : ℕ => τ * (((((n + 1 : ℕ) : ℝ))) / ((((n + 2 : ℕ) : ℝ)))))
        Filter.atTop (nhds (τ * 1)) :=
      hlim_frac.const_mul τ
    rw [mul_one] at hlim_mul
    exact hlim_mul
  exact ⟨a, hIoo, hlim, fun n => Set.Ioo_subset_Icc_self (hIoo n)⟩

/-- `HasSum` for `Ψ'` on closed band (with endpoint extension). -/
lemma cb_hasSum1 (τ : ℝ) (hτ1 : 1 ≤ τ) (q : ℕ) (hq2 : 2 ≤ q)
    (hlt : τ < (q : ℝ)) (y : ℝ) (hy : |y| ≤ τ) :
    HasSum (fun m : ℕ => nrTerm1 (cbA τ q) τ q m y) (deriv (cbPsi τ q) y) := by
  have hτ : 0 < τ := by linarith
  have hq1 : 1 ≤ q := by omega
  have hA : ∀ m, ‖cbA τ q m‖ ≤ 2 * majorB τ (q + m) :=
    fun m => cbA_bound τ hτ q hq2 hlt m
  by_cases hmem : y ∈ Set.Ioo (-τ) τ
  · exact cb_hasSum1_interior τ hτ1 q hq2 hlt y hmem
  · have hyIcc : y ∈ Set.Icc (-τ) τ := Set.mem_Icc.mpr (abs_le.mp hy)
    have hy_eq : y = -τ ∨ y = τ := by
      have hmem2 : ¬(-τ < y ∧ y < τ) := by
        simpa [Set.mem_Ioo] using hmem
      have h1 : y ≤ -τ ∨ τ ≤ y := by
        have h2 : ¬(-τ < y) ∨ ¬(y < τ) := not_and_or.mp hmem2
        rcases h2 with h | h
        · left
          exact le_of_not_gt h
        · right
          exact le_of_not_gt h
      rcases h1 with hle | hge
      · have hge2 : -τ ≤ y := (Set.mem_Icc.mp hyIcc).1
        left
        exact le_antisymm hle hge2
      · have hle2 : y ≤ τ := (Set.mem_Icc.mp hyIcc).2
        right
        exact le_antisymm hle2 hge
    have hcont_deriv : ContinuousOn (deriv (cbPsi τ q)) (Set.Icc (-τ) τ) := by
      have hcont : Continuous (deriv (cbPsi τ q)) :=
        (cbPsi_contDiff τ q).continuous_deriv (by norm_num)
      exact hcont.continuousOn
    have hcont_tsum : ContinuousOn
        (fun x : ℝ => ∑' m : ℕ, nrTerm1 (cbA τ q) τ q m x)
        (Set.Icc (-τ) τ) := by
      have hu := cb_summable_major1 τ hτ q hq2 hlt
      have hbound : ∀ n (x : ℝ), x ∈ Set.Icc (-τ) τ →
          ‖nrTerm1 (cbA τ q) τ q n x‖
            ≤ (2 / τ) * ((((q : ℝ) + ((n : ℝ))) ^ 2 * majorB τ (q + n))) := by
        intro n x hx
        have hx_abs : |x| ≤ τ := abs_le.mpr (Set.mem_Icc.mp hx)
        exact cb_term1_le τ q hτ1 x hx_abs n (hA n)
      have hunif := tendstoUniformlyOn_tsum hu hbound
      have hfin : ∃ᶠ t : Finset ℕ in Filter.atTop,
          ContinuousOn (fun x : ℝ => ∑ n ∈ t, nrTerm1 (cbA τ q) τ q n x)
            (Set.Icc (-τ) τ) := by
        apply Filter.Frequently.of_forall
        intro t
        apply continuousOn_finsetSum
        intro n _
        have hdiff : Differentiable ℝ
            (fun μ : ℝ => nrTerm1 (cbA τ q) τ q n μ) := by
          intro x
          exact (cb_hasDerivAt1 τ hτ q n x).differentiableAt
        exact hdiff.continuous.continuousOn
      exact hunif.continuousOn hfin
    have heqOn : Set.EqOn (deriv (cbPsi τ q))
        (fun x : ℝ => ∑' m : ℕ, nrTerm1 (cbA τ q) τ q m x)
        (Set.Ioo (-τ) τ) := by
      intro z hz
      have hHas := cb_hasSum1_interior τ hτ1 q hq2 hlt z hz
      exact hHas.tsum_eq.symm
    have hsum_y : Summable (fun m : ℕ => nrTerm1 (cbA τ q) τ q m y) := by
      have hCsum := cb_summable_major1 τ hτ q hq2 hlt
      have hnorm : Summable (fun m : ℕ => ‖nrTerm1 (cbA τ q) τ q m y‖) :=
        Summable.of_nonneg_of_le (fun m => norm_nonneg _)
          (fun m => cb_term1_le τ q hτ1 y hy m (hA m)) hCsum
      exact Summable.of_norm hnorm
    have heq_at : deriv (cbPsi τ q) y
        = (∑' m : ℕ, nrTerm1 (cbA τ q) τ q m y) := by
      obtain ⟨a, ha_mem, ha_lim, ha_Icc⟩ := cb_seq_right τ hτ
      have ha_neg_mem : ∀ n, (-a n) ∈ Set.Ioo (-τ) τ := by
        intro n
        have habs : |a n| < τ := abs_lt.mpr (ha_mem n)
        have habs2 : |-a n| < τ := by
          rw [abs_neg]
          exact habs
        exact abs_lt.mp habs2
      have ha_neg_Icc : ∀ n, (-a n) ∈ Set.Icc (-τ) τ := by
        intro n
        exact Set.Ioo_subset_Icc_self (ha_neg_mem n)
      have ha_neg_lim : Filter.Tendsto (fun n : ℕ => -a n) Filter.atTop (nhds (-τ)) := by
        have hneg : Filter.Tendsto (fun n : ℕ => -a n) Filter.atTop (nhds (-τ)) :=
          ha_lim.neg
        -- `-(a n)` vs `-a n`? Same (`Neg.neg` vs `fun n => -a n`)? Actually `ha_lim.neg` gives `Tendsto (fun n => -(a n)) ...`? Which is `fun n => -a n` definitionally? Good.
        exact hneg
      rcases hy_eq with rfl | h_y_pos
      · -- `y = -τ`, use `-a` (here `y` substituted by `-τ`)
        have hmem_Icc : (-τ) ∈ Set.Icc (-τ) τ :=
          Set.mem_Icc.mpr ⟨le_rfl, by linarith⟩
        have hcontW_deriv : Filter.Tendsto (deriv (cbPsi τ q))
            (nhdsWithin (-τ) (Set.Icc (-τ) τ)) (nhds (deriv (cbPsi τ q) (-τ))) :=
          hcont_deriv.continuousWithinAt hmem_Icc
        have hcontW_tsum : Filter.Tendsto
            (fun x : ℝ => ∑' m : ℕ, nrTerm1 (cbA τ q) τ q m x)
            (nhdsWithin (-τ) (Set.Icc (-τ) τ))
            (nhds (∑' m : ℕ, nrTerm1 (cbA τ q) τ q m (-τ))) :=
          hcont_tsum.continuousWithinAt hmem_Icc
        have hlim_within : Filter.Tendsto (fun n : ℕ => -a n) Filter.atTop
            (nhdsWithin (-τ) (Set.Icc (-τ) τ)) :=
          tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ha_neg_lim
            (Filter.Eventually.of_forall ha_neg_Icc)
        have hlim1 : Filter.Tendsto
            (fun n : ℕ => deriv (cbPsi τ q) (-a n)) Filter.atTop
            (nhds (deriv (cbPsi τ q) (-τ))) :=
          hcontW_deriv.comp hlim_within
        have hlim2 : Filter.Tendsto
            (fun n : ℕ => ∑' m : ℕ, nrTerm1 (cbA τ q) τ q m (-a n)) Filter.atTop
            (nhds (∑' m : ℕ, nrTerm1 (cbA τ q) τ q m (-τ))) :=
          hcontW_tsum.comp hlim_within
        have heq_seq : (fun n : ℕ => deriv (cbPsi τ q) (-a n))
            = (fun n : ℕ => ∑' m : ℕ, nrTerm1 (cbA τ q) τ q m (-a n)) := by
          funext n
          exact heqOn (ha_neg_mem n)
        rw [heq_seq] at hlim1
        exact tendsto_nhds_unique hlim1 hlim2
      · -- `y = τ`, use `a` (here `y` with `h_y_pos : y = τ`)
        rw [h_y_pos]
        have hmem_Icc : (τ) ∈ Set.Icc (-τ) τ :=
          Set.mem_Icc.mpr ⟨by linarith, le_rfl⟩
        have hcontW_deriv : Filter.Tendsto (deriv (cbPsi τ q))
            (nhdsWithin (τ) (Set.Icc (-τ) τ)) (nhds (deriv (cbPsi τ q) (τ))) :=
          hcont_deriv.continuousWithinAt hmem_Icc
        have hcontW_tsum : Filter.Tendsto
            (fun x : ℝ => ∑' m : ℕ, nrTerm1 (cbA τ q) τ q m x)
            (nhdsWithin (τ) (Set.Icc (-τ) τ))
            (nhds (∑' m : ℕ, nrTerm1 (cbA τ q) τ q m (τ))) :=
          hcont_tsum.continuousWithinAt hmem_Icc
        have hlim_within : Filter.Tendsto a Filter.atTop
            (nhdsWithin (τ) (Set.Icc (-τ) τ)) :=
          tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ha_lim
            (Filter.Eventually.of_forall ha_Icc)
        have hlim1 : Filter.Tendsto
            (fun n : ℕ => deriv (cbPsi τ q) (a n)) Filter.atTop
            (nhds (deriv (cbPsi τ q) (τ))) :=
          hcontW_deriv.comp hlim_within
        have hlim2 : Filter.Tendsto
            (fun n : ℕ => ∑' m : ℕ, nrTerm1 (cbA τ q) τ q m (a n)) Filter.atTop
            (nhds (∑' m : ℕ, nrTerm1 (cbA τ q) τ q m (τ))) :=
          hcontW_tsum.comp hlim_within
        have heq_seq : (fun n : ℕ => deriv (cbPsi τ q) (a n))
            = (fun n : ℕ => ∑' m : ℕ, nrTerm1 (cbA τ q) τ q m (a n)) := by
          funext n
          exact heqOn (ha_mem n)
        rw [heq_seq] at hlim1
        exact tendsto_nhds_unique hlim1 hlim2
    rw [heq_at]
    exact hsum_y.hasSum

/-- Interior `HasSum` for `Ψ''` (on `Ioo`). -/
lemma cb_hasSum2_interior (τ : ℝ) (hτ1 : 1 ≤ τ) (q : ℕ) (hq2 : 2 ≤ q)
    (hlt : τ < (q : ℝ)) (y : ℝ) (hy : y ∈ Set.Ioo (-τ) τ) :
    HasSum (fun m : ℕ => nrTerm2 (cbA τ q) τ q m y)
      (deriv (deriv (cbPsi τ q)) y) := by
  have hτ : 0 < τ := by linarith
  have hq1 : 1 ≤ q := by omega
  have hA : ∀ m, ‖cbA τ q m‖ ≤ 2 * majorB τ (q + m) :=
    fun m => cbA_bound τ hτ q hq2 hlt m
  set s : Set ℝ := Set.Ioo (-τ) τ with hs_def
  have hs : IsOpen s := isOpen_Ioo
  have hs' : IsPreconnected s := (convex_Ioo _ _).isPreconnected
  have hu : Summable
      (fun m : ℕ => (32 / τ ^ 2) * ((((q : ℝ) + (m : ℝ)) ^ 4 * majorB τ (q + m)))) :=
    cb_summable_major2 τ hτ q hq2 hlt
  have hg : ∀ n (z : ℝ), z ∈ s →
      HasDerivAt (fun μ : ℝ => nrTerm1 (cbA τ q) τ q n μ)
        (nrTerm2 (cbA τ q) τ q n z) z := by
    intro n z _
    exact cb_hasDerivAt1 τ hτ q n z
  have hg' : ∀ n (z : ℝ), z ∈ s →
      ‖nrTerm2 (cbA τ q) τ q n z‖
        ≤ (32 / τ ^ 2) * ((((q : ℝ) + ((n : ℝ))) ^ 4 * majorB τ (q + n))) := by
    intro n z hz
    have hz_abs : |z| ≤ τ := by
      have hlt_abs : |z| < τ := by
        rw [hs_def] at hz
        exact abs_lt.mpr ⟨by linarith [hz.1], by linarith [hz.2]⟩
      exact le_of_lt hlt_abs
    exact cb_term2_le τ q hτ1 z hz_abs n (hA n)
  have hy0 : (0 : ℝ) ∈ s := by
    rw [hs_def]
    exact ⟨by linarith, by linarith⟩
  -- `Summable (term1·0)` for `hg0` (needs `u1`? Actually `Summable (g·y₀)` with `g=term1`)
  have hg0 : Summable (fun n : ℕ => nrTerm1 (cbA τ q) τ q n (0 : ℝ)) := by
    have h0_abs : |(0 : ℝ)| ≤ τ := by simp; linarith
    have hCsum := cb_summable_major1 τ hτ q hq2 hlt
    have hnorm : Summable (fun m : ℕ => ‖nrTerm1 (cbA τ q) τ q m (0 : ℝ)‖) :=
      Summable.of_nonneg_of_le (fun m => norm_nonneg _)
        (fun m => cb_term1_le τ q hτ1 0 h0_abs m (hA m)) hCsum
    exact Summable.of_norm hnorm
  have hHas : HasDerivAt (fun z : ℝ => ∑' n : ℕ, nrTerm1 (cbA τ q) τ q n z)
      (∑' n : ℕ, nrTerm2 (cbA τ q) τ q n y) y :=
    hasDerivAt_tsum_of_isPreconnected hu hs hs' hg hg' hy0 hg0 hy
  -- `tsum1 = deriv Ψ` on `s` (from level-1 interior)
  have heqOn1 : Set.EqOn (fun z : ℝ => ∑' n : ℕ, nrTerm1 (cbA τ q) τ q n z)
      (deriv (cbPsi τ q)) s := by
    intro z hz
    exact (cb_hasSum1_interior τ hτ1 q hq2 hlt z hz).tsum_eq
  have hmem : s ∈ nhds y := hs.mem_nhds hy
  have hev : (deriv (cbPsi τ q)) =ᶠ[nhds y]
      (fun z : ℝ => ∑' n : ℕ, nrTerm1 (cbA τ q) τ q n z) := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨s, hmem, fun z hz => ?_⟩
    exact (heqOn1 hz).symm
  have hHasDeriv : HasDerivAt (deriv (cbPsi τ q))
      (∑' n : ℕ, nrTerm2 (cbA τ q) τ q n y) y :=
    hHas.congr_of_eventuallyEq hev
  have hderiv_eq : deriv (deriv (cbPsi τ q)) y
      = (∑' n : ℕ, nrTerm2 (cbA τ q) τ q n y) :=
    hHasDeriv.deriv
  have hz_abs : |y| ≤ τ := by
    have hlt_abs : |y| < τ := by
      rw [hs_def] at hy
      exact abs_lt.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
    exact le_of_lt hlt_abs
  have hsum : Summable (fun m : ℕ => nrTerm2 (cbA τ q) τ q m y) := by
    have hCsum := cb_summable_major2 τ hτ q hq2 hlt
    have hnorm : Summable (fun m : ℕ => ‖nrTerm2 (cbA τ q) τ q m y‖) :=
      Summable.of_nonneg_of_le (fun m => norm_nonneg _)
        (fun m => cb_term2_le τ q hτ1 y hz_abs m (hA m)) hCsum
    exact Summable.of_norm hnorm
  rw [hderiv_eq]
  exact hsum.hasSum

/-- `HasSum` for `Ψ''` on closed band (with endpoint extension). -/
lemma cb_hasSum2 (τ : ℝ) (hτ1 : 1 ≤ τ) (q : ℕ) (hq2 : 2 ≤ q)
    (hlt : τ < (q : ℝ)) (y : ℝ) (hy : |y| ≤ τ) :
    HasSum (fun m : ℕ => nrTerm2 (cbA τ q) τ q m y)
      (deriv (deriv (cbPsi τ q)) y) := by
  have hτ : 0 < τ := by linarith
  have hq1 : 1 ≤ q := by omega
  have hA : ∀ m, ‖cbA τ q m‖ ≤ 2 * majorB τ (q + m) :=
    fun m => cbA_bound τ hτ q hq2 hlt m
  by_cases hmem : y ∈ Set.Ioo (-τ) τ
  · exact cb_hasSum2_interior τ hτ1 q hq2 hlt y hmem
  · have hyIcc : y ∈ Set.Icc (-τ) τ := Set.mem_Icc.mpr (abs_le.mp hy)
    have hy_eq : y = -τ ∨ y = τ := by
      have hmem2 : ¬(-τ < y ∧ y < τ) := by
        simpa [Set.mem_Ioo] using hmem
      have h1 : y ≤ -τ ∨ τ ≤ y := by
        have h2 : ¬(-τ < y) ∨ ¬(y < τ) := not_and_or.mp hmem2
        rcases h2 with h | h
        · left
          exact le_of_not_gt h
        · right
          exact le_of_not_gt h
      rcases h1 with hle | hge
      · have hge2 : -τ ≤ y := (Set.mem_Icc.mp hyIcc).1
        left
        exact le_antisymm hle hge2
      · have hle2 : y ≤ τ := (Set.mem_Icc.mp hyIcc).2
        right
        exact le_antisymm hle2 hge
    have hcont_deriv2 : ContinuousOn (deriv (deriv (cbPsi τ q)))
        (Set.Icc (-τ) τ) := by
      have hcd1 : ContDiff ℝ 1 (deriv (cbPsi τ q)) := by
        have hcd := cbPsi_contDiff τ q
        -- `ContDiff 2 → ContDiff 1 (deriv)` via `deriv'`
        have h2 : (2 : WithTop ℕ∞) = 1 + 1 := by norm_num
        rw [h2] at hcd
        exact hcd.deriv'
      have hcont : Continuous (deriv (deriv (cbPsi τ q))) :=
        hcd1.continuous_deriv (by norm_num)
      exact hcont.continuousOn
    have hcont_tsum2 : ContinuousOn
        (fun x : ℝ => ∑' m : ℕ, nrTerm2 (cbA τ q) τ q m x)
        (Set.Icc (-τ) τ) := by
      have hu := cb_summable_major2 τ hτ q hq2 hlt
      have hbound : ∀ n (x : ℝ), x ∈ Set.Icc (-τ) τ →
          ‖nrTerm2 (cbA τ q) τ q n x‖
            ≤ (32 / τ ^ 2) * ((((q : ℝ) + ((n : ℝ))) ^ 4 * majorB τ (q + n))) := by
        intro n x hx
        have hx_abs : |x| ≤ τ := abs_le.mpr (Set.mem_Icc.mp hx)
        exact cb_term2_le τ q hτ1 x hx_abs n (hA n)
      have hunif := tendstoUniformlyOn_tsum hu hbound
      have hfin : ∃ᶠ t : Finset ℕ in Filter.atTop,
          ContinuousOn (fun x : ℝ => ∑ n ∈ t, nrTerm2 (cbA τ q) τ q n x)
            (Set.Icc (-τ) τ) := by
        apply Filter.Frequently.of_forall
        intro t
        apply continuousOn_finsetSum
        intro n _
        -- Each `nrTerm2` continuous (polynomial comp affine, via `fun_prop`+`Continuity`)
        have hcont_n : Continuous (fun μ : ℝ => nrTerm2 (cbA τ q) τ q n μ) := by
          unfold nrTerm2
          fun_prop
        exact hcont_n.continuousOn
      exact hunif.continuousOn hfin
    have heqOn : Set.EqOn (deriv (deriv (cbPsi τ q)))
        (fun x : ℝ => ∑' m : ℕ, nrTerm2 (cbA τ q) τ q m x)
        (Set.Ioo (-τ) τ) := by
      intro z hz
      have hHas := cb_hasSum2_interior τ hτ1 q hq2 hlt z hz
      exact hHas.tsum_eq.symm
    have hsum_y : Summable (fun m : ℕ => nrTerm2 (cbA τ q) τ q m y) := by
      have hCsum := cb_summable_major2 τ hτ q hq2 hlt
      have hnorm : Summable (fun m : ℕ => ‖nrTerm2 (cbA τ q) τ q m y‖) :=
        Summable.of_nonneg_of_le (fun m => norm_nonneg _)
          (fun m => cb_term2_le τ q hτ1 y hy m (hA m)) hCsum
      exact Summable.of_norm hnorm
    have heq_at : deriv (deriv (cbPsi τ q)) y
        = (∑' m : ℕ, nrTerm2 (cbA τ q) τ q m y) := by
      obtain ⟨a, ha_mem, ha_lim, ha_Icc⟩ := cb_seq_right τ hτ
      have ha_neg_mem : ∀ n, (-a n) ∈ Set.Ioo (-τ) τ := by
        intro n
        have habs : |a n| < τ := abs_lt.mpr (ha_mem n)
        have habs2 : |-a n| < τ := by
          rw [abs_neg]
          exact habs
        exact abs_lt.mp habs2
      have ha_neg_Icc : ∀ n, (-a n) ∈ Set.Icc (-τ) τ := by
        intro n
        exact Set.Ioo_subset_Icc_self (ha_neg_mem n)
      have ha_neg_lim : Filter.Tendsto (fun n : ℕ => -a n) Filter.atTop (nhds (-τ)) :=
        ha_lim.neg
      rcases hy_eq with rfl | h_y_pos
      · -- `y = -τ`
        have hmem_Icc : (-τ) ∈ Set.Icc (-τ) τ :=
          Set.mem_Icc.mpr ⟨le_rfl, by linarith⟩
        have hcontW_deriv : Filter.Tendsto (deriv (deriv (cbPsi τ q)))
            (nhdsWithin (-τ) (Set.Icc (-τ) τ))
            (nhds (deriv (deriv (cbPsi τ q)) (-τ))) :=
          hcont_deriv2.continuousWithinAt hmem_Icc
        have hcontW_tsum : Filter.Tendsto
            (fun x : ℝ => ∑' m : ℕ, nrTerm2 (cbA τ q) τ q m x)
            (nhdsWithin (-τ) (Set.Icc (-τ) τ))
            (nhds (∑' m : ℕ, nrTerm2 (cbA τ q) τ q m (-τ))) :=
          hcont_tsum2.continuousWithinAt hmem_Icc
        have hlim_within : Filter.Tendsto (fun n : ℕ => -a n) Filter.atTop
            (nhdsWithin (-τ) (Set.Icc (-τ) τ)) :=
          tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ha_neg_lim
            (Filter.Eventually.of_forall ha_neg_Icc)
        have hlim1 : Filter.Tendsto
            (fun n : ℕ => deriv (deriv (cbPsi τ q)) (-a n)) Filter.atTop
            (nhds (deriv (deriv (cbPsi τ q)) (-τ))) :=
          hcontW_deriv.comp hlim_within
        have hlim2 : Filter.Tendsto
            (fun n : ℕ => ∑' m : ℕ, nrTerm2 (cbA τ q) τ q m (-a n)) Filter.atTop
            (nhds (∑' m : ℕ, nrTerm2 (cbA τ q) τ q m (-τ))) :=
          hcontW_tsum.comp hlim_within
        have heq_seq : (fun n : ℕ => deriv (deriv (cbPsi τ q)) (-a n))
            = (fun n : ℕ => ∑' m : ℕ, nrTerm2 (cbA τ q) τ q m (-a n)) := by
          funext n
          exact heqOn (ha_neg_mem n)
        rw [heq_seq] at hlim1
        exact tendsto_nhds_unique hlim1 hlim2
      · -- `y = τ` with `h_y_pos : y = τ`
        rw [h_y_pos]
        have hmem_Icc : (τ) ∈ Set.Icc (-τ) τ :=
          Set.mem_Icc.mpr ⟨by linarith, le_rfl⟩
        have hcontW_deriv : Filter.Tendsto (deriv (deriv (cbPsi τ q)))
            (nhdsWithin (τ) (Set.Icc (-τ) τ)) (nhds (deriv (deriv (cbPsi τ q)) (τ))) :=
          hcont_deriv2.continuousWithinAt hmem_Icc
        have hcontW_tsum : Filter.Tendsto
            (fun x : ℝ => ∑' m : ℕ, nrTerm2 (cbA τ q) τ q m x)
            (nhdsWithin (τ) (Set.Icc (-τ) τ))
            (nhds (∑' m : ℕ, nrTerm2 (cbA τ q) τ q m (τ))) :=
          hcont_tsum2.continuousWithinAt hmem_Icc
        have hlim_within : Filter.Tendsto a Filter.atTop
            (nhdsWithin (τ) (Set.Icc (-τ) τ)) :=
          tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ha_lim
            (Filter.Eventually.of_forall ha_Icc)
        have hlim1 : Filter.Tendsto
            (fun n : ℕ => deriv (deriv (cbPsi τ q)) (a n)) Filter.atTop
            (nhds (deriv (deriv (cbPsi τ q)) (τ))) :=
          hcontW_deriv.comp hlim_within
        have hlim2 : Filter.Tendsto
            (fun n : ℕ => ∑' m : ℕ, nrTerm2 (cbA τ q) τ q m (a n)) Filter.atTop
            (nhds (∑' m : ℕ, nrTerm2 (cbA τ q) τ q m (τ))) :=
          hcontW_tsum.comp hlim_within
        have heq_seq : (fun n : ℕ => deriv (deriv (cbPsi τ q)) (a n))
            = (fun n : ℕ => ∑' m : ℕ, nrTerm2 (cbA τ q) τ q m (a n)) := by
          funext n
          exact heqOn (ha_mem n)
        rw [heq_seq] at hlim1
        exact tendsto_nhds_unique hlim1 hlim2
    rw [heq_at]
    exact hsum_y.hasSum

/-- Bundle from truncation (D1 discharge, parametric). -/
noncomputable def nrCheb_of_truncation (τ : ℝ) (q : ℕ) (hτ1 : 1 ≤ τ) (hq2 : 2 ≤ q)
    (hlt : τ < (q : ℝ)) : nrCheb where
  q := q
  τ := τ
  Ψ := cbPsi τ q
  a := cbA τ q
  Q := cbQ τ q
  χ := cbChi
  hq2 := hq2
  hτ1 := hτ1
  hτq := hlt
  hΨ := cbPsi_contDiff τ q
  hA := fun m => cbA_bound τ (by linarith) q hq2 hlt m
  hSer0 := fun μ hμ => cb_hasSum0 τ hτ1 q hq2 hlt μ hμ
  hSer1 := fun μ hμ => cb_hasSum1 τ hτ1 q hq2 hlt μ hμ
  hSer2 := fun μ hμ => cb_hasSum2 τ hτ1 q hq2 hlt μ hμ
  hQ := by
    have hτ0 : τ ≠ 0 := by
      have : 0 < τ := by linarith
      exact ne_of_gt this
    have hq1 : 1 ≤ q := by omega
    exact cbQ_natDegree_lt τ hτ0 q hq1
  hΨeq := fun μ _ => rfl
  hχ := cbChi_contDiff
  hχ1 := fun μ _ => rfl
  hχb := fun μ => by
    show ‖cbChi μ‖ ≤ 1
    unfold cbChi
    simp
  hχd1 := fun μ => by
    have hτ : 0 < τ := by linarith
    have hqpos : (0 : ℝ) < (q : ℝ) := by
      have : (0 : ℕ) < q := by omega
      exact_mod_cast this
    have hBpos : 0 < nrB τ q := by
      unfold nrB
      exact div_pos hτ (pow_pos hqpos 2)
    have hderiv : deriv cbChi μ = 0 := deriv_const μ 1
    rw [hderiv]
    simp only [norm_zero]
    exact div_nonneg (by norm_num) hBpos.le
  hχd2 := fun μ => by
    have hτ : 0 < τ := by linarith
    have hqpos : (0 : ℝ) < (q : ℝ) := by
      have : (0 : ℕ) < q := by omega
      exact_mod_cast this
    have hBpos : 0 < nrB τ q := by
      unfold nrB
      exact div_pos hτ (pow_pos hqpos 2)
    have h1 : deriv cbChi = fun _ => (0 : ℝ) := by
      funext x
      exact deriv_const x 1
    have hderiv2 : deriv (deriv cbChi) μ = 0 := by
      rw [h1]
      exact deriv_const μ 0
    rw [hderiv2]
    simp only [norm_zero]
    exact div_nonneg (by norm_num) (pow_nonneg hBpos.le 2)

/-- Concrete instance (`τ = 1`, `q = 4`) for audit (`: nrCheb` with no args). -/
noncomputable def nrCheb_concrete : nrCheb :=
  nrCheb_of_truncation 1 4 (by norm_num) (by norm_num) (by norm_num)

end RobustZ





