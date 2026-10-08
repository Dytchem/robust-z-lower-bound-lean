import RobustZ.Band

/-!
# M4 → M3 的桥接

`Band.exists_approx_band_geometric` 给的是「`approxPoly τ k` 在 `μ/τ` 处的值逼近 `e^{-iμ}`」，
而 `SmearingMain` 需要的是「某个多项式在 `μ` 处的值逼近 `e^{-iμ}`」。
把 `approxPoly τ k` 与线性代换 `u ↦ u/τ` 复合即得。
-/

noncomputable section

namespace RobustZ

open Polynomial

/-- 复合 `u ↦ u/τ` 之后的多项式（作为 `μ` 的多项式）。 -/
noncomputable def scaledApprox (τ : ℝ) (k : ℕ) : Polynomial ℂ :=
  (approxPoly τ k).comp (Polynomial.C ((τ⁻¹ : ℝ) : ℂ) * Polynomial.X)

lemma scaledApprox_eval (τ : ℝ) (hτ : τ ≠ 0) (k : ℕ) (μ : ℝ) :
    (scaledApprox τ k).eval ((μ : ℂ)) = (approxPoly τ k).eval (((μ / τ : ℝ)) : ℂ) := by
  rw [scaledApprox, Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X]
  congr 2
  push_cast
  field_simp

/-- `approxPoly τ k` 的次数 `≤ k - 1`。 -/
lemma approxPoly_natDegree_le (τ : ℝ) (k : ℕ) : (approxPoly τ k).natDegree ≤ k - 1 := by
  rw [approxPoly]
  refine (Polynomial.natDegree_add_le _ _).trans ?_
  rw [Polynomial.natDegree_C, Nat.zero_max]
  refine (Polynomial.natDegree_sum_le _ _).trans ?_
  refine Finset.sup_le fun m hm => ?_
  have hstep : (Polynomial.C (2 * fcoef τ ((m : ℤ) + 1))
        * Polynomial.Chebyshev.T ℂ ((m : ℤ) + 1)).natDegree
      ≤ (Polynomial.C (2 * fcoef τ ((m : ℤ) + 1))).natDegree
        + (Polynomial.Chebyshev.T ℂ ((m : ℤ) + 1)).natDegree := Polynomial.natDegree_mul_le
  refine hstep.trans ?_
  rw [Polynomial.natDegree_C, Polynomial.Chebyshev.natDegree_T, zero_add]
  have h1 : m < k - 1 := Finset.mem_range.mp hm
  have h2 : ((m : ℤ) + 1).natAbs = m + 1 := by omega
  omega

/-- 更紧的次数界（M5 需要）：`natDegree (scaledApprox τ k) ≤ k - 1`，于是 `k ≥ 1` 时 `< k`。 -/
lemma scaledApprox_natDegree_le (τ : ℝ) (k : ℕ) : (scaledApprox τ k).natDegree ≤ k - 1 := by
  have hdeg : (Polynomial.C ((τ⁻¹ : ℝ) : ℂ) * Polynomial.X : Polynomial ℂ).natDegree ≤ 1 := by
    have hstep : (Polynomial.C ((τ⁻¹ : ℝ) : ℂ) * Polynomial.X : Polynomial ℂ).natDegree
        ≤ (Polynomial.C ((τ⁻¹ : ℝ) : ℂ)).natDegree + Polynomial.X.natDegree :=
      Polynomial.natDegree_mul_le
    rw [Polynomial.natDegree_C, Polynomial.natDegree_X] at hstep
    omega
  have hcomp : (scaledApprox τ k).natDegree
      ≤ (approxPoly τ k).natDegree
        * (Polynomial.C ((τ⁻¹ : ℝ) : ℂ) * Polynomial.X : Polynomial ℂ).natDegree :=
    Polynomial.natDegree_comp_le
  have hmul : (approxPoly τ k).natDegree * (Polynomial.C ((τ⁻¹ : ℝ) : ℂ) * Polynomial.X : Polynomial ℂ).natDegree
      ≤ (k - 1) * 1 := Nat.mul_le_mul (approxPoly_natDegree_le τ k) hdeg
  omega

lemma scaledApprox_natDegree_lt (τ : ℝ) (k : ℕ) : (scaledApprox τ k).natDegree < k + 1 := by
  have hcomp : (scaledApprox τ k).natDegree
      ≤ (approxPoly τ k).natDegree
        * (Polynomial.C ((τ⁻¹ : ℝ) : ℂ) * Polynomial.X : Polynomial ℂ).natDegree :=
    Polynomial.natDegree_comp_le
  refine lt_of_le_of_lt hcomp ?_
  have hdeg : (Polynomial.C ((τ⁻¹ : ℝ) : ℂ) * Polynomial.X : Polynomial ℂ).natDegree ≤ 1 := by
    have hstep : (Polynomial.C ((τ⁻¹ : ℝ) : ℂ) * Polynomial.X : Polynomial ℂ).natDegree
        ≤ (Polynomial.C ((τ⁻¹ : ℝ) : ℂ)).natDegree + Polynomial.X.natDegree :=
      Polynomial.natDegree_mul_le
    rw [Polynomial.natDegree_C, Polynomial.natDegree_X] at hstep
    omega
  refine lt_of_le_of_lt (Nat.mul_le_mul (approxPoly_natDegree_le τ k) hdeg) ?_
  omega

end RobustZ
