/-
Copyright (c) 2025 RobustZ project. All rights reserved.

# `SharpDeriv`：`Ψ_A` 的 **线性于 `ε`** 的 collar 导数界

`M5Scaled.norm_deriv_psiA_scaled_collar_le` / `norm_deriv2_psiA_scaled_collar_le` 给出的
`M₁`、`M₂` 是**绝对**界（形如 `k³E/τ`、`k⁵E/τ²`，`E = e^{τ sinh δ'}`），与带内逼近误差
`ε` 无关；这正是 `FinalSmall` §6 诊断出的缺口。本文件给出正确的**有抵消**版本。

设 `P = scaledApprox τ k`（`e^{-iμ}` 的 Chebyshev 截断）、
`Q μ = e^{-iμ} - P(μ)`（即 `psiA P μ` 乘上模 1 因子），并设**尾部系数衰减假设**

`hcoef : ∀ j, ‖fcoef τ (k+j)‖ ≤ ε * r^j`

（可用 `fcoef_bound` + `epsOf` 直接兑现，见 §7 的 `fcoef_tail_le_epsOf`）。则在整个 collar
`|μ| ≤ τ + B` 上

* `‖Q μ‖           ≤ 4 ε`（值，`norm_sharpErr_le`）
* `‖Q' μ‖          ≤ 8 (k/τ)² ε`（`norm_deriv_sharpErr_le`）
* `‖Q'' μ‖         ≤ 512 (k/τ)⁴ ε`（`norm_deriv2_sharpErr_le`）

**关键点**：collar 上真正小的是**带抵消的和** `Σ_m c_m T_m(u)`（`|T_m(cosh w)| = cosh(mw)`
指数增长，但系数相位使其和对消），而不是 `Σ_m |c_m| |T_m(u)|`。所以证明走
`KernelDecay.hasSum_fcoef_cosh`（collar 上的 Jacobi–Anger 恒等式）+ 级数重整 +
`Mathlib.Analysis.Calculus.SmoothSeries` 的逐项求导。

常数来源（`β := B/τ`、`G := e^{2√β}`、`ρ := r·G`）：
* `|T_n'| ≤ n²G^n`（`CollarBound.abs_deriv_chebyshevT_le_exp`）、
  `|T_n''| ≤ 32n⁴G^n`（`M5Scaled.abs_deriv2_chebyshevT_le_exp`）；
* `Σ_j ρ^j (k+j)² ≤ k² Σ_j ρ^j 4^j ≤ 2k²`（`ρ ≤ 1/8`）；
* `Σ_j ρ^j (k+j)⁴ ≤ k⁴ Σ_j ρ^j 2·8^j ≤ 4k⁴`（`ρ ≤ 1/16`）；
* `G^k ≤ 2`。
-/
import RobustZ.M5Scaled
import RobustZ.CollarTail
import Mathlib.Analysis.Complex.ExponentialBounds

noncomputable section

namespace RobustZ

open Filter MeasureTheory
open scoped Real Topology ComplexConjugate

set_option maxHeartbeats 1000000

/-! ## §1 系数共轭：`conj c_n = (-1)^n c_n` -/

/-- `fz τ n` 的共轭等于 `fz (-τ) (-n)`。 -/
lemma conj_fz (τ : ℝ) (n : ℤ) (x : ℝ) :
    (starRingEnd ℂ) (fz τ n (x : ℂ)) = fz (-τ) (-n) (x : ℂ) := by
  simp only [fz]
  rw [map_mul, ← Complex.exp_conj, ← Complex.exp_conj]
  rw [← Complex.ofReal_cos x]
  simp only [map_mul, map_neg, map_intCast, Complex.conj_ofReal, Complex.conj_I]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- `((-1)^n : ℤ) : ℂ) = (-1 : ℂ)^n`（`negOnePow` 与 `zpow` 的桥）。 -/
lemma negOnePow_cast_complex (n : ℤ) : (((n.negOnePow : ℤ)) : ℂ) = (-1 : ℂ) ^ n := by
  rcases Int.even_or_odd n with h | h
  · rw [Int.negOnePow_even n h, Even.neg_one_zpow h]
    norm_num
  · rw [Int.negOnePow_odd n h, Odd.neg_one_zpow h]
    norm_num

/-- `e^{-inπ} = (-1)^n`。 -/
lemma exp_neg_int_mul_pi_I (n : ℤ) :
    Complex.exp (-(n : ℂ) * Complex.I * (Real.pi : ℂ)) = (((n.negOnePow : ℤ)) : ℂ) := by
  have hpi : Complex.exp (-((Real.pi : ℂ) * Complex.I)) = -1 := by
    rw [Complex.exp_neg, Complex.exp_pi_mul_I, inv_neg, inv_one]
  have hrw : (-(n : ℂ) * Complex.I * (Real.pi : ℂ))
      = (n : ℂ) * (-((Real.pi : ℂ) * Complex.I)) := by ring
  rw [hrw, Complex.exp_int_mul, hpi, negOnePow_cast_complex]

/-- 区间积分与共轭可交换。 -/
lemma integral_conj_interval (a b : ℝ) (f : ℝ → ℂ) :
    (∫ x in a..b, (starRingEnd ℂ) (f x)) = (starRingEnd ℂ) (∫ x in a..b, f x) := by
  rcases le_or_gt a b with h | h
  · rw [intervalIntegral.integral_of_le h, integral_conj, intervalIntegral.integral_of_le h]
  · rw [intervalIntegral.integral_of_ge h.le, intervalIntegral.integral_of_ge h.le, map_neg,
      integral_conj]

/-- `fcoef (-τ) n = (-1)^n fcoef τ n`（`θ ↦ θ + π` 平移）。 -/
lemma fcoef_neg_tau (τ : ℝ) (n : ℤ) :
    fcoef (-τ) n = (((n.negOnePow : ℤ)) : ℂ) * fcoef τ n := by
  have hper : Function.Periodic (fun x : ℝ => fz (-τ) n (x : ℂ)) (2 * Real.pi) := by
    intro x
    show fz (-τ) n ((x + 2 * Real.pi : ℝ) : ℂ) = fz (-τ) n (x : ℂ)
    rw [show ((x + 2 * Real.pi : ℝ) : ℂ) = (x : ℂ) + 2 * (Real.pi : ℂ) by push_cast; ring]
    exact fz_periodic (-τ) n (x : ℂ)
  -- 平移 π：`∫ fz(-τ) n θ = ∫ fz(-τ) n (θ+π)`
  have hshift : (∫ θ in (0 : ℝ)..(2 * Real.pi), fz (-τ) n (θ : ℂ))
      = ∫ θ in (0 : ℝ)..(2 * Real.pi), fz (-τ) n (((θ + Real.pi : ℝ)) : ℂ) := by
    rw [intervalIntegral.integral_comp_add_right (fun θ : ℝ => fz (-τ) n (θ : ℂ)) (Real.pi)]
    rw [show (0 : ℝ) + Real.pi = Real.pi by ring,
      show (2 : ℝ) * Real.pi + Real.pi = Real.pi + 2 * Real.pi by ring]
    simpa using (hper.intervalIntegral_add_eq (Real.pi) 0).symm
  -- 逐点：`fz(-τ) n (θ+π) = (-1)^n fz τ n θ`
  have hpoint : ∀ θ : ℝ, fz (-τ) n (((θ + Real.pi : ℝ)) : ℂ)
      = (((n.negOnePow : ℤ)) : ℂ) * fz τ n (θ : ℂ) := by
    intro θ
    have harg1 : (-(n : ℂ) * Complex.I * (((θ + Real.pi : ℝ)) : ℂ))
        = (-(n : ℂ) * Complex.I * (θ : ℂ)) + (-(n : ℂ) * Complex.I * (Real.pi : ℂ)) := by
      push_cast
      ring
    have hcos : Complex.cos ((((θ + Real.pi : ℝ)) : ℂ)) = -Complex.cos (θ : ℂ) := by
      rw [show (((θ + Real.pi : ℝ)) : ℂ) = (θ : ℂ) + (Real.pi : ℂ) by push_cast; ring,
        Complex.cos_add_pi]
    have harg2 : (-(((-τ : ℝ)) : ℂ) * Complex.I * Complex.cos ((((θ + Real.pi : ℝ)) : ℂ)))
        = -(τ : ℂ) * Complex.I * Complex.cos (θ : ℂ) := by
      rw [hcos]
      push_cast
      ring
    simp only [fz, harg1, harg2, Complex.exp_add, exp_neg_int_mul_pi_I]
    ring
  have hcongr : (∫ θ in (0 : ℝ)..(2 * Real.pi), fz (-τ) n (((θ + Real.pi : ℝ)) : ℂ))
      = ∫ θ in (0 : ℝ)..(2 * Real.pi), (((n.negOnePow : ℤ)) : ℂ) * fz τ n (θ : ℂ) :=
    intervalIntegral.integral_congr fun θ _ => hpoint θ
  rw [fcoef, fcoef, Algebra.smul_def, Algebra.smul_def, hshift, hcongr,
    intervalIntegral.integral_const_mul]
  ring

/-- **系数共轭对称**：`conj (fcoef τ n) = (-1)^n fcoef τ n`（偶数频实、奇数频纯虚）。 -/
lemma conj_fcoef (τ : ℝ) (n : ℤ) :
    (starRingEnd ℂ) (fcoef τ n) = (((n.negOnePow : ℤ)) : ℂ) * fcoef τ n := by
  have hsmul : ∀ (c : ℝ) (z : ℂ), (starRingEnd ℂ) (c • z) = c • (starRingEnd ℂ) z := by
    intro c z
    have h1 : c • z = Complex.ofReal c * z := by rw [Algebra.smul_def]; rfl
    have h2 : c • (starRingEnd ℂ) z = Complex.ofReal c * (starRingEnd ℂ) z := by
      rw [Algebra.smul_def]; rfl
    rw [h1, h2, map_mul, Complex.conj_ofReal]
  have h1 : (starRingEnd ℂ) (fcoef τ n) = fcoef (-τ) (-n) := by
    rw [fcoef, fcoef, hsmul, ← integral_conj_interval]
    congr 1
    refine intervalIntegral.integral_congr fun θ _ => ?_
    exact conj_fz τ n θ
  rw [h1, fcoef_neg (-τ) n, fcoef_neg_tau]

/-! ## §2 误差函数的反射对称 -/

/-- `approxPoly` 的系数展开（任意复数点）。 -/
lemma approxPoly_eval_eq (τ : ℝ) (k : ℕ) (x : ℂ) :
    (approxPoly τ k).eval x
      = fcoef τ 0 + ∑ m ∈ Finset.range (k - 1), 2 * fcoef τ ((m : ℤ) + 1)
          * (Polynomial.Chebyshev.T ℂ ((m : ℤ) + 1)).eval x := by
  simp only [approxPoly, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_finsetSum,
    Polynomial.eval_mul]

/-- `(T ℂ n).eval (-x) = (-1)^n (T ℂ n).eval x`。 -/
lemma chebyshevT_complex_eval_neg (n : ℤ) (x : ℂ) :
    (Polynomial.Chebyshev.T ℂ n).eval (-x)
      = (((n.negOnePow : ℤ)) : ℂ) * (Polynomial.Chebyshev.T ℂ n).eval x :=
  Polynomial.Chebyshev.T_eval_neg ℂ n x

/-- `(T ℂ n).eval x` 在实点上取实值。 -/
lemma chebyshevT_complex_eval_conj_ofReal (n : ℤ) (u : ℝ) :
    (starRingEnd ℂ) ((Polynomial.Chebyshev.T ℂ n).eval (u : ℂ))
      = (Polynomial.Chebyshev.T ℂ n).eval (u : ℂ) := by
  rw [← Polynomial.Chebyshev.complex_ofReal_eval_T u n, Complex.conj_ofReal]

/-- **`approxPoly` 的反射**：`P(-u) = conj (P u)`（实的 `u`）。 -/
lemma approxPoly_eval_neg (τ : ℝ) (k : ℕ) (u : ℝ) :
    (approxPoly τ k).eval (-(u : ℂ))
      = (starRingEnd ℂ) ((approxPoly τ k).eval (u : ℂ)) := by
  rw [approxPoly_eval_eq, approxPoly_eval_eq, map_add, map_sum]
  congr 1
  · rw [conj_fcoef τ 0]
    simp
  · refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_mul, map_mul, map_ofNat, conj_fcoef, chebyshevT_complex_eval_neg,
      chebyshevT_complex_eval_conj_ofReal]
    ring

/-- 误差函数 `Q μ = e^{-iμ} - P(μ)`，`P = scaledApprox τ k`。 -/
def sharpErr (τ : ℝ) (k : ℕ) (μ : ℝ) : ℂ :=
  Complex.exp (-(μ : ℂ) * Complex.I) - (scaledApprox τ k).eval (μ : ℂ)

lemma sharpErr_def (τ : ℝ) (k : ℕ) (μ : ℝ) :
    sharpErr τ k μ = Complex.exp (-(μ : ℂ) * Complex.I) - (scaledApprox τ k).eval (μ : ℂ) :=
  rfl

/-- `‖sharpErr τ k μ‖ = ‖psiA (scaledApprox τ k) μ‖`。 -/
lemma norm_sharpErr_eq_norm_psiA (τ : ℝ) (k : ℕ) (μ : ℝ) :
    ‖sharpErr τ k μ‖ = ‖psiA (scaledApprox τ k) μ‖ := by
  rw [sharpErr_def, ← norm_psiA_eq (scaledApprox τ k) μ]

/-- **反射对称**：`Q(-μ) = conj (Q μ)`。 -/
lemma sharpErr_neg (τ : ℝ) (hτ : τ ≠ 0) (k : ℕ) (μ : ℝ) :
    sharpErr τ k (-μ) = (starRingEnd ℂ) (sharpErr τ k μ) := by
  have hP : (scaledApprox τ k).eval ((-μ : ℝ) : ℂ)
      = (starRingEnd ℂ) ((scaledApprox τ k).eval ((μ : ℝ) : ℂ)) := by
    rw [scaledApprox_eval τ hτ k (-μ), scaledApprox_eval τ hτ k μ,
      show ((-μ : ℝ) / τ) = -((μ / τ : ℝ)) by ring]
    rw [Complex.ofReal_neg]
    exact approxPoly_eval_neg τ k (μ / τ)
  have hexp : Complex.exp (-((-μ : ℝ) : ℂ) * Complex.I)
      = (starRingEnd ℂ) (Complex.exp (-((μ : ℝ) : ℂ) * Complex.I)) := by
    have h2 : (-((-μ : ℝ) : ℂ)) * Complex.I = (μ : ℂ) * Complex.I := by push_cast; ring
    have h3 : (starRingEnd ℂ) (-((μ : ℝ) : ℂ) * Complex.I) = (μ : ℂ) * Complex.I := by
      simp only [map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I]
      ring
    rw [h2, ← Complex.exp_conj, h3]
  rw [sharpErr_def, sharpErr_def, map_sub, hexp, hP]

/-! ## §3 Chebyshev 尾部级数 -/

/-- Chebyshev 尾部级数 `Σ_{j} 2 c_{k+j} T_{k+j}(u)`。 -/
noncomputable def chebTail (τ : ℝ) (k : ℕ) (u : ℝ) : ℂ :=
  ∑' j : ℕ, 2 * fcoef τ (((k + j : ℕ)) : ℤ)
    * (((Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).eval u : ℝ) : ℂ)

/-- 复数级数与共轭可交换。 -/
lemma conj_tsum (f : ℕ → ℂ) :
    (starRingEnd ℂ) (∑' n, f n) = ∑' n, (starRingEnd ℂ) (f n) :=
  Complex.conjCLE.map_tsum

/-- 尾部级数的反射对称：`S(-u) = conj (S u)`。 -/
lemma chebTail_neg (τ : ℝ) (k : ℕ) (u : ℝ) :
    chebTail τ k (-u) = (starRingEnd ℂ) (chebTail τ k u) := by
  rw [chebTail, chebTail]
  rw [conj_tsum]
  refine tsum_congr fun j => ?_
  rw [map_mul, map_mul, map_ofNat, conj_fcoef, Polynomial.Chebyshev.T_eval_neg,
    Complex.conj_ofReal]
  push_cast
  ring



/-! ## §4 恒等式：闭 collar 上 `Q(τu)` 等于 Chebyshev 尾部级数 -/

/-- 频带形式的 `n` 频项：`c_n e^{inθ}`（即 `fterm`）。 -/
noncomputable def freqTerm (τ θ : ℝ) (m : ℤ) : ℂ :=
  fcoef τ m * Complex.exp ((m : ℂ) * Complex.I * (θ : ℂ))

/-- 频带尾部（正频）第 `j` 项。 -/
noncomputable def tailA (τ θ : ℝ) (k : ℕ) (j : ℕ) : ℂ := freqTerm τ θ (((k + j : ℕ)) : ℤ)

/-- 频带尾部（负频）第 `j` 项。 -/
noncomputable def tailB (τ θ : ℝ) (k : ℕ) (j : ℕ) : ℂ := freqTerm τ θ (-(((k + j : ℕ)) : ℤ))

/-- collar 形式的 `n` 频项：`c_n e^{-nw}`（即 `Gcoef τ 0 w n`）。 -/
noncomputable def collTerm (τ w : ℝ) (m : ℤ) : ℂ :=
  fcoef τ m * Complex.exp (-(m : ℂ) * (w : ℂ))

/-- collar 尾部（衰减指数）第 `j` 项。 -/
noncomputable def tailP (τ w : ℝ) (k : ℕ) (j : ℕ) : ℂ := collTerm τ w (((k + j : ℕ)) : ℤ)

/-- collar 尾部（增长指数）第 `j` 项。 -/
noncomputable def tailQ (τ w : ℝ) (k : ℕ) (j : ℕ) : ℂ := collTerm τ w (-(((k + j : ℕ)) : ℤ))

lemma fterm_eq_freqTerm (τ θ : ℝ) (m : ℤ) : fterm τ θ m = freqTerm τ θ m := rfl

lemma Gcoef_zero_eq_collTerm (τ w : ℝ) (m : ℤ) : Gcoef τ 0 w m = collTerm τ w m := by
  rw [Gcoef_zero_apply, collTerm]

/-- `2 cos x = e^{ix} + e^{-ix}`。 -/
lemma two_cos_eq_exp_add (x : ℝ) :
    ((2 : ℂ) * (Real.cos x : ℝ)) = Complex.exp ((x : ℂ) * Complex.I)
      + Complex.exp (-(x : ℂ) * Complex.I) := by
  rw [← exp_add_exp_neg_mul_I x]

/-- `2 cosh x = e^{x} + e^{-x}`。 -/
lemma two_cosh_eq_exp_add (x : ℝ) :
    ((2 : ℂ) * (Real.cosh x : ℝ)) = Complex.exp (x : ℂ) + Complex.exp (-(x : ℂ)) := by
  have h1 : ((Real.cosh x : ℝ) : ℂ) = (((Real.exp x + Real.exp (-x)) / 2 : ℝ) : ℂ) := by
    rw [Real.cosh_eq]
  rw [h1, Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_exp, Complex.ofReal_exp,
    Complex.ofReal_neg, Complex.ofReal_ofNat]
  ring

/-- 频带恒等式（`θ ∈ (0, 2π]`）：`Q(τ cos θ)` 等于对称 Chebyshev 尾部级数。 -/
lemma sharpErr_cos_eq_chebTail (τ : ℝ) (hτ : 0 < τ) {k : ℕ} (hk : 1 ≤ k) {θ : ℝ}
    (hθ : θ ∈ Set.Ioc 0 (2 * Real.pi)) :
    sharpErr τ k (τ * Real.cos θ) = chebTail τ k (Real.cos θ) := by
  have hHas := hasSum_exp_fcoef τ hτ.le (δ := 1) (by norm_num) hθ
  have hTail := exp_eq_sum_add_tail τ hτ.le (δ := 1) (by norm_num) hθ k
  have hFin := sum_fterm_eq_approxPoly τ hk θ
  -- 可和性
  have hsumA : Summable (tailA τ θ k) := by
    have h : Summable (fun j : ℕ => freqTerm τ θ (((k + j : ℕ)) : ℤ)) :=
      hHas.summable.comp_injective (fun a b hab => by omega)
    exact h.congr fun j => rfl
  have hsumB : Summable (tailB τ θ k) := by
    have h : Summable (fun j : ℕ => freqTerm τ θ (-(((k + j : ℕ)) : ℤ))) :=
      hHas.summable.comp_injective (fun a b hab => by omega)
    exact h.congr fun j => rfl
  -- 有限部分的余项 `c_k e^{-ikθ}` 就是 `tailB τ θ k 0`
  have hB0 : fcoef τ (k : ℤ) * Complex.exp (-((k : ℤ) : ℂ) * Complex.I * (θ : ℂ))
      = tailB τ θ k 0 := by
    simp only [tailB, freqTerm, Nat.add_zero, fcoef_neg]
    push_cast
    ring
  -- 尾部展开式 = `Σ (A n + B (n+1))`
  have hT : (∑' n : ℕ, (fterm τ θ (((n + k : ℕ)) : ℤ) + fterm τ θ (-(((n + k : ℕ)) : ℤ) - 1)))
      = ∑' n : ℕ, (tailA τ θ k n + tailB τ θ k (n + 1)) := by
    refine tsum_congr fun n => ?_
    have h1 : fterm τ θ (((n + k : ℕ)) : ℤ) = tailA τ θ k n := by
      simp only [fterm, tailA, freqTerm]
      rw [show (((n + k : ℕ)) : ℤ) = (((k + n : ℕ)) : ℤ) by omega]
    have h2 : fterm τ θ (-(((n + k : ℕ)) : ℤ) - 1) = tailB τ θ k (n + 1) := by
      simp only [fterm, tailB, freqTerm]
      rw [show -(((n + k : ℕ)) : ℤ) - 1 = -((((k + (n + 1) : ℕ)) : ℤ)) by push_cast; ring,
        fcoef_neg]
    rw [h1, h2]
  -- Chebyshev 侧 = `Σ (A j + B j)`
  have hcheb : chebTail τ k (Real.cos θ) = ∑' j : ℕ, (tailA τ θ k j + tailB τ θ k j) := by
    rw [chebTail]
    refine tsum_congr fun j => ?_
    rw [Polynomial.Chebyshev.T_real_cos]
    rw [show (↑(((k + j : ℕ)) : ℤ) : ℝ) = (((k + j : ℕ)) : ℝ) by push_cast; ring]
    rw [show (2 : ℂ) * fcoef τ (((k + j : ℕ)) : ℤ)
          * ((Real.cos ((((k + j : ℕ)) : ℝ) * θ) : ℝ) : ℂ)
        = fcoef τ (((k + j : ℕ)) : ℤ)
          * (2 * ((Real.cos ((((k + j : ℕ)) : ℝ) * θ) : ℝ) : ℂ)) by ring]
    rw [two_cos_eq_exp_add (((k + j : ℕ)) * θ)]
    simp only [tailA, tailB, freqTerm]
    push_cast
    ring_nf
    rw [show (-(↑k : ℤ) - ↑j) = -((↑k : ℤ) + ↑j) by ring, fcoef_neg]
    ring
  -- 指数函数、链式法则
  have hexp : Complex.exp (-((τ * Real.cos θ : ℝ) : ℂ) * Complex.I)
      = Complex.exp (-(τ : ℂ) * Complex.I * Complex.cos (θ : ℂ)) := by
    congr 1
    rw [← Complex.ofReal_cos θ]
    push_cast
    ring
  have hτne : τ ≠ 0 := ne_of_gt hτ
  have hscale : (scaledApprox τ k).eval (((τ * Real.cos θ : ℝ)) : ℂ)
      = (approxPoly τ k).eval ((Real.cos θ : ℝ) : ℂ) := by
    rw [scaledApprox_eval τ hτne k (τ * Real.cos θ),
      show ((τ * Real.cos θ : ℝ) / τ) = Real.cos θ by field_simp]
  have hsplitB : tailB τ θ k 0 + (∑' n : ℕ, tailB τ θ k (n + 1)) = ∑' n : ℕ, tailB τ θ k n := by
    have h := hsumB.sum_add_tsum_nat_add 1
    simpa using h
  have hsumBshift : Summable fun n : ℕ => tailB τ θ k (n + 1) :=
    (summable_nat_add_iff 1).mpr hsumB
  have hmain : Complex.exp (-(τ : ℂ) * Complex.I * Complex.cos (θ : ℂ))
        - (approxPoly τ k).eval ((Real.cos θ : ℝ) : ℂ)
      = tailB τ θ k 0 + ∑' n : ℕ, (fterm τ θ (((n + k : ℕ)) : ℤ)
          + fterm τ θ (-(((n + k : ℕ)) : ℤ) - 1)) := by
    rw [hTail, hFin, hB0]
    ring
  rw [sharpErr_def, hexp, hscale, hmain, hT, hcheb, Summable.tsum_add hsumA hsumBshift,
    Summable.tsum_add hsumA hsumB,
    show tailB τ θ k 0 + (∑' n, tailA τ θ k n + ∑' n, tailB τ θ k (n + 1))
      = (∑' n, tailA τ θ k n) + (tailB τ θ k 0 + ∑' n, tailB τ θ k (n + 1)) by ring,
    hsplitB]

/-- collar 恒等式（`w > 0`）：`Q(τ cosh w)` 等于对称 Chebyshev 尾部级数。 -/
lemma sharpErr_cosh_eq_chebTail (τ : ℝ) (hτ : 0 < τ) {k : ℕ} (hk : 1 ≤ k) {w : ℝ}
    (hw : 0 < w) :
    sharpErr τ k (τ * Real.cosh w) = chebTail τ k (Real.cosh w) := by
  have hδ : (0 : ℝ) < w + 1 := by linarith
  have hHas := hasSum_fcoef_cosh τ hτ.le hδ hw (by linarith : w < w + 1)
  have hs : Summable (fun m : ℤ => Gcoef τ 0 w m) := by
    have h : Summable (fun m : ℤ => collTerm τ w m) := hHas.summable
    simpa only [Gcoef_zero_eq_collTerm] using h
  have hspl := tsum_Gcoef_split τ 0 (w := w) hs k
  have hFin := finitePart_eq_approxPoly_add τ w hk
  -- 可和性
  have hsumP : Summable (tailP τ w k) := by
    have h : Summable (fun j : ℕ => Gcoef τ 0 w (((k + j : ℕ)) : ℤ)) :=
      hs.comp_injective (fun a b hab => by omega)
    exact h.congr fun j => by rw [Gcoef_zero_eq_collTerm]; rfl
  have hsumQ : Summable (tailQ τ w k) := by
    have h : Summable (fun j : ℕ => Gcoef τ 0 w (-(((k + j : ℕ)) : ℤ))) :=
      hs.comp_injective (fun a b hab => by omega)
    exact h.congr fun j => by rw [Gcoef_zero_eq_collTerm]; rfl
  -- 有限部分的余项 `c_k e^{kw}` 就是 `tailQ τ w k 0`
  have hQ0 : fcoef τ (k : ℤ) * Complex.exp (((k : ℤ) : ℂ) * (w : ℂ)) = tailQ τ w k 0 := by
    simp only [tailQ, collTerm, Nat.add_zero, fcoef_neg]
    push_cast
    ring_nf
  -- 尾部展开式 = `Σ (P n + Q (n+1))`
  have hT : tailPart τ 0 w k = ∑' n : ℕ, (tailP τ w k n + tailQ τ w k (n + 1)) := by
    rw [tailPart]
    refine tsum_congr fun n => ?_
    have h1 : Gcoef τ 0 w (((n + k : ℕ)) : ℤ) = tailP τ w k n := by
      simp only [Gcoef_zero_eq_collTerm, tailP, collTerm]
      rw [show (((n + k : ℕ)) : ℤ) = (((k + n : ℕ)) : ℤ) by omega]
    have h2 : Gcoef τ 0 w (-(((n + k : ℕ)) : ℤ) - 1) = tailQ τ w k (n + 1) := by
      simp only [Gcoef_zero_eq_collTerm, tailQ, collTerm]
      rw [show -(((n + k : ℕ)) : ℤ) - 1 = -((((k + (n + 1) : ℕ)) : ℤ)) by push_cast; ring,
        fcoef_neg]
    rw [h1, h2]
  -- Chebyshev 侧 = `Σ (P j + Q j)`
  have hcheb : chebTail τ k (Real.cosh w) = ∑' j : ℕ, (tailP τ w k j + tailQ τ w k j) := by
    rw [chebTail]
    refine tsum_congr fun j => ?_
    rw [Polynomial.Chebyshev.T_real_cosh]
    rw [show (↑(((k + j : ℕ)) : ℤ) : ℝ) = (((k + j : ℕ)) : ℝ) by push_cast; ring]
    rw [show (2 : ℂ) * fcoef τ (((k + j : ℕ)) : ℤ)
          * ((Real.cosh ((((k + j : ℕ)) : ℝ) * w) : ℝ) : ℂ)
        = fcoef τ (((k + j : ℕ)) : ℤ)
          * (2 * ((Real.cosh ((((k + j : ℕ)) : ℝ) * w) : ℝ) : ℂ)) by ring]
    rw [two_cosh_eq_exp_add ((((k + j : ℕ)) : ℝ) * w)]
    simp only [tailP, tailQ, collTerm, freqTerm]
    push_cast
    ring_nf
    rw [show (-(↑k : ℤ) - ↑j) = -((↑k : ℤ) + ↑j) by ring, fcoef_neg]
    ring
  -- 指数函数、链式法则
  have hτne : τ ≠ 0 := ne_of_gt hτ
  have hexp : Complex.exp (-((τ * Real.cosh w : ℝ) : ℂ) * Complex.I)
      = Complex.exp (-(τ : ℂ) * Complex.I * ((Real.cosh w : ℝ) : ℂ)) := by
    congr 1
    push_cast
    ring
  have hscale : (scaledApprox τ k).eval (((τ * Real.cosh w : ℝ)) : ℂ)
      = (approxPoly τ k).eval ((Real.cosh w : ℝ) : ℂ) := by
    rw [scaledApprox_eval τ hτne k (τ * Real.cosh w),
      show ((τ * Real.cosh w : ℝ) / τ) = Real.cosh w by field_simp]
  have hmain : Complex.exp (-(τ : ℂ) * Complex.I * ((Real.cosh w : ℝ) : ℂ))
        - (approxPoly τ k).eval ((Real.cosh w : ℝ) : ℂ)
      = tailQ τ w k 0 + tailPart τ 0 w k := by
    have h1 : Complex.exp (-(τ : ℂ) * Complex.I * ((Real.cosh w : ℝ) : ℂ))
        = ∑' n : ℤ, Gcoef τ 0 w n := by
      rw [← hHas.tsum_eq]
      exact tsum_congr fun n => (Gcoef_zero_eq_collTerm τ w n).symm
    rw [h1, hspl, hFin, hQ0]
    ring
  rw [sharpErr_def, hexp, hscale, hmain, hT, hcheb, Summable.tsum_add hsumP
    ((summable_nat_add_iff 1).mpr hsumQ), Summable.tsum_add hsumP hsumQ,
    show tailQ τ w k 0 + (∑' n, tailP τ w k n + ∑' n, tailQ τ w k (n + 1))
      = (∑' n, tailP τ w k n) + (tailQ τ w k 0 + ∑' n, tailQ τ w k (n + 1)) by ring]
  have hsplitQ : tailQ τ w k 0 + (∑' n : ℕ, tailQ τ w k (n + 1)) = ∑' n : ℕ, tailQ τ w k n := by
    have h := hsumQ.sum_add_tsum_nat_add 1
    simpa using h
  rw [hsplitQ]

/-! ## §5 `ε`-线性的 collar 导数界

记号：`g := 2√(B/τ)`（collar 上 `|T_n|` 的增长指数），`ρ := r·e^g`。
假设尾部系数几何衰减 `‖c_{k+j}‖ ≤ ε·r^j`、`ρ ≤ 1/32`、`k·g ≤ 1`、`B/τ ≤ 1/2`。 -/

/-! ### 5.1 几何级数的显式界 -/

/-- `(j:ℝ) + 1 ≤ 2^j`。 -/
lemma natCast_add_one_le_two_pow (j : ℕ) : ((j : ℝ) + 1) ≤ (2 : ℝ) ^ j := by
  have h : j + 1 ≤ 2 ^ j := by
    rcases Nat.eq_zero_or_pos j with h | h
    · subst h; norm_num
    · exact Nat.succ_le_of_lt Nat.lt_two_pow_self
  exact_mod_cast h

/-- `((j:ℝ)+1)^2 ≤ 4^j`。 -/
lemma add_one_pow_two_le_four_pow (j : ℕ) : ((j : ℝ) + 1) ^ 2 ≤ (4 : ℝ) ^ j := by
  have h := natCast_add_one_le_two_pow j
  calc ((j : ℝ) + 1) ^ 2 ≤ ((2 : ℝ) ^ j) ^ 2 := pow_le_pow_left₀ (by positivity) h 2
    _ = (4 : ℝ) ^ j := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul, Nat.mul_comm j 2]

/-- `((j:ℝ)+1)^4 ≤ 16^j`。 -/
lemma add_one_pow_four_le_sixteen_pow (j : ℕ) : ((j : ℝ) + 1) ^ 4 ≤ (16 : ℝ) ^ j := by
  have h := natCast_add_one_le_two_pow j
  calc ((j : ℝ) + 1) ^ 4 ≤ ((2 : ℝ) ^ j) ^ 4 := pow_le_pow_left₀ (by positivity) h 4
    _ = (16 : ℝ) ^ j := by
        rw [show (16 : ℝ) = 2 ^ 4 by norm_num, ← pow_mul, ← pow_mul, Nat.mul_comm j 4]

/-- `Σ_j (j+1)²ρ^j ≤ 8/7`（`16ρ ≤ 1/2`）。 -/
lemma tsum_add_one_pow_two_mul_geometric_le {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : 16 * ρ ≤ 1 / 2) :
    ∑' j : ℕ, ((j : ℝ) + 1) ^ 2 * ρ ^ j ≤ 8 / 7 := by
  have h4 : 4 * ρ ≤ 1 / 8 := by linarith
  have h4' : (4 : ℝ) * ρ < 1 := by linarith
  have h4nn : (0 : ℝ) ≤ 4 * ρ := by linarith
  have hg : Summable (fun j : ℕ => ((4 : ℝ) * ρ) ^ j) :=
    summable_geometric_of_lt_one h4nn h4'
  have hpt : ∀ j : ℕ, ((j : ℝ) + 1) ^ 2 * ρ ^ j ≤ ((4 : ℝ) * ρ) ^ j := by
    intro j
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right (add_one_pow_two_le_four_pow j) (pow_nonneg hρ0 j)
  have hf : Summable (fun j : ℕ => ((j : ℝ) + 1) ^ 2 * ρ ^ j) :=
    Summable.of_nonneg_of_le (fun j => by positivity) hpt hg
  calc ∑' j : ℕ, ((j : ℝ) + 1) ^ 2 * ρ ^ j
      ≤ ∑' j : ℕ, ((4 : ℝ) * ρ) ^ j := Summable.tsum_le_tsum hpt hf hg
    _ = (1 - 4 * ρ)⁻¹ := tsum_geometric_of_lt_one h4nn h4'
    _ ≤ 8 / 7 := by
        have h1 : (0 : ℝ) < 1 - 4 * ρ := by linarith
        rw [inv_le_comm₀ h1 (by norm_num : (0 : ℝ) < 8 / 7)]
        norm_num
        linarith

/-- `Σ_j (j+1)⁴ρ^j ≤ 2`（`16ρ ≤ 1/2`）。 -/
lemma tsum_add_one_pow_four_mul_geometric_le {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : 16 * ρ ≤ 1 / 2) :
    ∑' j : ℕ, ((j : ℝ) + 1) ^ 4 * ρ ^ j ≤ 2 := by
  have h16' : (16 : ℝ) * ρ < 1 := by linarith
  have h16nn : (0 : ℝ) ≤ 16 * ρ := by linarith
  have hg : Summable (fun j : ℕ => ((16 : ℝ) * ρ) ^ j) :=
    summable_geometric_of_lt_one h16nn h16'
  have hpt : ∀ j : ℕ, ((j : ℝ) + 1) ^ 4 * ρ ^ j ≤ ((16 : ℝ) * ρ) ^ j := by
    intro j
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right (add_one_pow_four_le_sixteen_pow j) (pow_nonneg hρ0 j)
  have hf : Summable (fun j : ℕ => ((j : ℝ) + 1) ^ 4 * ρ ^ j) :=
    Summable.of_nonneg_of_le (fun j => by positivity) hpt hg
  calc ∑' j : ℕ, ((j : ℝ) + 1) ^ 4 * ρ ^ j
      ≤ ∑' j : ℕ, ((16 : ℝ) * ρ) ^ j := Summable.tsum_le_tsum hpt hf hg
    _ = (1 - 16 * ρ)⁻¹ := tsum_geometric_of_lt_one h16nn h16'
    _ ≤ 2 := by
        have h1 : (0 : ℝ) < 1 - 16 * ρ := by linarith
        rw [inv_le_comm₀ h1 (by norm_num : (0 : ℝ) < 2)]
        norm_num
        linarith

/-- `Σ_j (j+1)²ρ^j` 可和（`4ρ < 1`）。 -/
lemma summable_add_one_pow_two_mul_geometric {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : 4 * ρ < 1) :
    Summable (fun j : ℕ => ((j : ℝ) + 1) ^ 2 * ρ ^ j) :=
  Summable.of_nonneg_of_le (fun j => by positivity)
    (fun j => by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right (add_one_pow_two_le_four_pow j) (pow_nonneg hρ0 j))
    (summable_geometric_of_lt_one (by linarith) hρ1)

/-- `Σ_j (j+1)⁴ρ^j` 可和（`16ρ < 1`）。 -/
lemma summable_add_one_pow_four_mul_geometric {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : 16 * ρ < 1) :
    Summable (fun j : ℕ => ((j : ℝ) + 1) ^ 4 * ρ ^ j) :=
  Summable.of_nonneg_of_le (fun j => by positivity)
    (fun j => by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right (add_one_pow_four_le_sixteen_pow j) (pow_nonneg hρ0 j))
    (summable_geometric_of_lt_one (by linarith) hρ1)

/-! ### 5.2 尾部导数级数的定义与 `ε`-线性界 -/

/-- Chebyshev 尾部级数的**一阶导**：`Σ_j 2 c_{k+j} T'_{k+j}(u)`。 -/
noncomputable def chebTailD1 (τ : ℝ) (k : ℕ) (u : ℝ) : ℂ :=
  ∑' j : ℕ, 2 * fcoef τ (((k + j : ℕ)) : ℤ)
    * ((((Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).derivative.eval u : ℝ)) : ℂ)

/-- Chebyshev 尾部级数的**二阶导**：`Σ_j 2 c_{k+j} T''_{k+j}(u)`。 -/
noncomputable def chebTailD2 (τ : ℝ) (k : ℕ) (u : ℝ) : ℂ :=
  ∑' j : ℕ, 2 * fcoef τ (((k + j : ℕ)) : ℤ)
    * ((((Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).derivative.derivative.eval u : ℝ)) : ℂ)

/-- 尾部一阶导级数在 collar 上的 `ε`-线性界：`‖Σ_j 2c_{k+j}T'_{k+j}(u)‖ ≤ (16/7)k²εe^{kg}`。 -/
lemma norm_chebTailD1_le (τ B : ℝ) (hτ : 0 < τ) (hB : 0 < B) {k : ℕ} (hk : 1 ≤ k)
    {ε r : ℝ} (hε : 0 ≤ ε) (hr : 0 ≤ r)
    (hdec : ∀ j : ℕ, ‖fcoef τ (((k + j : ℕ)) : ℤ)‖ ≤ ε * r ^ j)
    (hρ : r * Real.exp (2 * Real.sqrt (B / τ)) ≤ 1 / 32)
    {u : ℝ} (hu : |u| ≤ 1 + B / τ) :
    ‖chebTailD1 τ k u‖
      ≤ (16 / 7) * Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ))) * (k : ℝ) ^ 2 * ε := by
  set g : ℝ := 2 * Real.sqrt (B / τ) with hg
  set ρ : ℝ := r * Real.exp g with hρdef
  have hg0 : 0 ≤ g := by rw [hg]; positivity
  have hρ0 : 0 ≤ ρ := by rw [hρdef]; positivity
  have hρle : ρ ≤ 1 / 32 := by rw [hρdef, hg]; exact hρ
  have hρ16 : 16 * ρ ≤ 1 / 2 := by linarith
  have hBτ0 : 0 ≤ B / τ := by positivity
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkj : ∀ j : ℕ, (((k + j : ℕ)) : ℝ) ≤ (k : ℝ) * ((j : ℝ) + 1) := by
    intro j
    push_cast
    nlinarith [hk1, (Nat.cast_nonneg j : (0 : ℝ) ≤ (j : ℝ))]
  have hpt : ∀ j : ℕ, ‖2 * fcoef τ (((k + j : ℕ)) : ℤ)
        * ((((Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).derivative.eval u : ℝ)) : ℂ)‖
      ≤ (2 * ε * Real.exp ((k : ℝ) * g) * (k : ℝ) ^ 2) * (((j : ℝ) + 1) ^ 2 * ρ ^ j) := by
    intro j
    have habs : |((((k + j : ℕ)) : ℤ) : ℝ)| = (((k + j : ℕ)) : ℝ) :=
      abs_of_nonneg (by positivity)
    have hT := abs_deriv_chebyshevT_le_exp (((k + j : ℕ)) : ℤ) hBτ0 hu
    rw [habs] at hT
    have hTg : |(Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).derivative.eval u|
        ≤ (((k + j : ℕ)) : ℝ) ^ 2 * Real.exp ((((k + j : ℕ)) : ℝ) * g) := by
      refine hT.trans (le_of_eq ?_)
      rw [hg]
      push_cast
      ring_nf
    have hT2 : |(Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).derivative.eval u|
        ≤ (((k : ℝ) * ((j : ℝ) + 1)) ^ 2)
          * (Real.exp ((k : ℝ) * g) * (Real.exp g) ^ j) := by
      refine hTg.trans ?_
      have hexp : Real.exp ((((k + j : ℕ)) : ℝ) * g)
          = Real.exp ((k : ℝ) * g) * (Real.exp g) ^ j := by
        rw [show ((((k + j : ℕ)) : ℝ) * g) = (k : ℝ) * g + (j : ℝ) * g by push_cast; ring,
          Real.exp_add]
        congr 1
        exact Real.exp_nat_mul g j
      rw [hexp]
      have hsq : (((k + j : ℕ)) : ℝ) ^ 2 ≤ ((k : ℝ) * ((j : ℝ) + 1)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (hkj j) 2
      have hE : (0 : ℝ) ≤ Real.exp ((k : ℝ) * g) * (Real.exp g) ^ j := by positivity
      exact mul_le_mul_of_nonneg_right hsq hE
    have hsplit : ‖2 * fcoef τ (((k + j : ℕ)) : ℤ)
        * ((((Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).derivative.eval u : ℝ)) : ℂ)‖
        = 2 * ‖fcoef τ (((k + j : ℕ)) : ℤ)‖
          * |(Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).derivative.eval u| := by
      rw [norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs]
    rw [hsplit]
    have htarget : (2 * ε * Real.exp ((k : ℝ) * g) * (k : ℝ) ^ 2) * (((j : ℝ) + 1) ^ 2 * ρ ^ j)
        = 2 * (ε * r ^ j) * (((k : ℝ) * ((j : ℝ) + 1)) ^ 2
            * (Real.exp ((k : ℝ) * g) * (Real.exp g) ^ j)) := by
      rw [hρdef, mul_pow]
      ring
    rw [htarget]
    have hc0 : (0 : ℝ) ≤ ‖fcoef τ (((k + j : ℕ)) : ℤ)‖ := norm_nonneg _
    have hT0 : (0 : ℝ) ≤ |(Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).derivative.eval u| :=
      abs_nonneg _
    have h1 := hdec j
    have h2 := hT2
    have h3 : (0 : ℝ) ≤ ε * r ^ j := by positivity
    have h4 : (0 : ℝ) ≤ ((k : ℝ) * ((j : ℝ) + 1)) ^ 2
        * (Real.exp ((k : ℝ) * g) * (Real.exp g) ^ j) := by positivity
    nlinarith [h1, h2, h3, h4, hc0, hT0,
      mul_nonneg (sub_nonneg.mpr h1) hT0, mul_nonneg hc0 (sub_nonneg.mpr h2)]
  have hmaj : Summable (fun j : ℕ =>
      (2 * ε * Real.exp ((k : ℝ) * g) * (k : ℝ) ^ 2) * (((j : ℝ) + 1) ^ 2 * ρ ^ j)) :=
    (Summable.mul_left _ (summable_add_one_pow_two_mul_geometric hρ0 (by linarith)))
  have hs : Summable (fun j : ℕ => ‖2 * fcoef τ (((k + j : ℕ)) : ℤ)
        * ((((Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).derivative.eval u : ℝ)) : ℂ)‖) :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _) hpt hmaj
  calc ‖chebTailD1 τ k u‖
      = ‖∑' j : ℕ, 2 * fcoef τ (((k + j : ℕ)) : ℤ)
          * ((((Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).derivative.eval u : ℝ)) : ℂ)‖ := rfl
    _ ≤ ∑' j : ℕ, ‖2 * fcoef τ (((k + j : ℕ)) : ℤ)
          * ((((Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).derivative.eval u : ℝ)) : ℂ)‖ :=
        norm_tsum_le_tsum_norm hs
    _ ≤ ∑' j : ℕ, (2 * ε * Real.exp ((k : ℝ) * g) * (k : ℝ) ^ 2)
          * (((j : ℝ) + 1) ^ 2 * ρ ^ j) := Summable.tsum_le_tsum hpt hs hmaj
    _ = (2 * ε * Real.exp ((k : ℝ) * g) * (k : ℝ) ^ 2)
          * ∑' j : ℕ, (((j : ℝ) + 1) ^ 2 * ρ ^ j) := tsum_mul_left
    _ ≤ (2 * ε * Real.exp ((k : ℝ) * g) * (k : ℝ) ^ 2) * (8 / 7) := by
        refine mul_le_mul_of_nonneg_left
          (tsum_add_one_pow_two_mul_geometric_le (ρ := ρ) hρ0 hρ16) ?_
        positivity
    _ = (16 / 7) * Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ))) * (k : ℝ) ^ 2 * ε := by
        rw [hg]; ring

/-- 尾部二阶导级数在 collar 上的 `ε`-线性界：`‖Σ_j 2c_{k+j}T''_{k+j}(u)‖ ≤ 128k⁴εe^{kg}`。 -/
lemma norm_chebTailD2_le (τ B : ℝ) (hτ : 0 < τ) (hB : 0 < B) {k : ℕ} (hk : 1 ≤ k)
    {ε r : ℝ} (hε : 0 ≤ ε) (hr : 0 ≤ r)
    (hdec : ∀ j : ℕ, ‖fcoef τ (((k + j : ℕ)) : ℤ)‖ ≤ ε * r ^ j)
    (hρ : r * Real.exp (2 * Real.sqrt (B / τ)) ≤ 1 / 32) (hBτ : B / τ ≤ 1 / 2)
    {u : ℝ} (hu : |u| ≤ 1 + B / τ) :
    ‖chebTailD2 τ k u‖
      ≤ 128 * Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ))) * (k : ℝ) ^ 4 * ε := by
  set g : ℝ := 2 * Real.sqrt (B / τ) with hg
  set ρ : ℝ := r * Real.exp g with hρdef
  have hg0 : 0 ≤ g := by rw [hg]; positivity
  have hρ0 : 0 ≤ ρ := by rw [hρdef]; positivity
  have hρle : ρ ≤ 1 / 32 := by rw [hρdef, hg]; exact hρ
  have hρ16 : 16 * ρ ≤ 1 / 2 := by linarith
  have hBτ0 : 0 ≤ B / τ := by positivity
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkj : ∀ j : ℕ, (((k + j : ℕ)) : ℝ) ≤ (k : ℝ) * ((j : ℝ) + 1) := by
    intro j
    push_cast
    nlinarith [hk1, (Nat.cast_nonneg j : (0 : ℝ) ≤ (j : ℝ))]
  have hpt : ∀ j : ℕ, ‖2 * fcoef τ (((k + j : ℕ)) : ℤ)
        * ((((Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).derivative.derivative.eval u : ℝ)) : ℂ)‖
      ≤ (64 * ε * Real.exp ((k : ℝ) * g) * (k : ℝ) ^ 4) * (((j : ℝ) + 1) ^ 4 * ρ ^ j) := by
    intro j
    have habs : |((((k + j : ℕ)) : ℤ) : ℝ)| = (((k + j : ℕ)) : ℝ) :=
      abs_of_nonneg (by positivity)
    have hT := abs_deriv2_chebyshevT_le_exp (((k + j : ℕ)) : ℤ) hBτ0 hBτ hu
    rw [habs] at hT
    have hTg : |(Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).derivative.derivative.eval u|
        ≤ 32 * (((k + j : ℕ)) : ℝ) ^ 4 * Real.exp ((((k + j : ℕ)) : ℝ) * g) := by
      refine hT.trans (le_of_eq ?_)
      rw [hg]
      push_cast
      ring_nf
    have hT2 : |(Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).derivative.derivative.eval u|
        ≤ 32 * ((k : ℝ) * ((j : ℝ) + 1)) ^ 4
          * (Real.exp ((k : ℝ) * g) * (Real.exp g) ^ j) := by
      refine hTg.trans ?_
      have hexp : Real.exp ((((k + j : ℕ)) : ℝ) * g)
          = Real.exp ((k : ℝ) * g) * (Real.exp g) ^ j := by
        rw [show ((((k + j : ℕ)) : ℝ) * g) = (k : ℝ) * g + (j : ℝ) * g by push_cast; ring,
          Real.exp_add]
        congr 1
        exact Real.exp_nat_mul g j
      rw [hexp]
      have hsq : (((k + j : ℕ)) : ℝ) ^ 4 ≤ ((k : ℝ) * ((j : ℝ) + 1)) ^ 4 :=
        pow_le_pow_left₀ (by positivity) (hkj j) 4
      have hE : (0 : ℝ) ≤ Real.exp ((k : ℝ) * g) * (Real.exp g) ^ j := by positivity
      nlinarith [hsq, hE, Real.exp_pos ((k : ℝ) * g)]
    have hsplit : ‖2 * fcoef τ (((k + j : ℕ)) : ℤ)
        * ((((Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).derivative.derivative.eval u : ℝ)) : ℂ)‖
        = 2 * ‖fcoef τ (((k + j : ℕ)) : ℤ)‖
          * |(Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).derivative.derivative.eval u| := by
      rw [norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs]
    rw [hsplit]
    have htarget : (64 * ε * Real.exp ((k : ℝ) * g) * (k : ℝ) ^ 4) * (((j : ℝ) + 1) ^ 4 * ρ ^ j)
        = 2 * (ε * r ^ j) * (32 * ((k : ℝ) * ((j : ℝ) + 1)) ^ 4
            * (Real.exp ((k : ℝ) * g) * (Real.exp g) ^ j)) := by
      rw [hρdef, mul_pow]
      ring
    rw [htarget]
    have hc0 : (0 : ℝ) ≤ ‖fcoef τ (((k + j : ℕ)) : ℤ)‖ := norm_nonneg _
    have hT0 : (0 : ℝ) ≤
      |(Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).derivative.derivative.eval u| := abs_nonneg _
    have h1 := hdec j
    have h2 := hT2
    have h3 : (0 : ℝ) ≤ ε * r ^ j := by positivity
    have h4 : (0 : ℝ) ≤ 32 * ((k : ℝ) * ((j : ℝ) + 1)) ^ 4
        * (Real.exp ((k : ℝ) * g) * (Real.exp g) ^ j) := by positivity
    nlinarith [h1, h2, h3, h4, hc0, hT0,
      mul_nonneg (sub_nonneg.mpr h1) hT0, mul_nonneg hc0 (sub_nonneg.mpr h2)]
  have hmaj : Summable (fun j : ℕ =>
      (64 * ε * Real.exp ((k : ℝ) * g) * (k : ℝ) ^ 4) * (((j : ℝ) + 1) ^ 4 * ρ ^ j)) :=
    (Summable.mul_left _ (summable_add_one_pow_four_mul_geometric hρ0 (by linarith)))
  have hs : Summable (fun j : ℕ => ‖2 * fcoef τ (((k + j : ℕ)) : ℤ)
        * ((((Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).derivative.derivative.eval u : ℝ)) : ℂ)‖) :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _) hpt hmaj
  calc ‖chebTailD2 τ k u‖
      = ‖∑' j : ℕ, 2 * fcoef τ (((k + j : ℕ)) : ℤ)
          * ((((Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).derivative.derivative.eval u : ℝ)) : ℂ)‖ :=
        rfl
    _ ≤ ∑' j : ℕ, ‖2 * fcoef τ (((k + j : ℕ)) : ℤ)
          * ((((Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).derivative.derivative.eval u : ℝ)) : ℂ)‖ :=
        norm_tsum_le_tsum_norm hs
    _ ≤ ∑' j : ℕ, (64 * ε * Real.exp ((k : ℝ) * g) * (k : ℝ) ^ 4)
          * (((j : ℝ) + 1) ^ 4 * ρ ^ j) := Summable.tsum_le_tsum hpt hs hmaj
    _ = (64 * ε * Real.exp ((k : ℝ) * g) * (k : ℝ) ^ 4)
          * ∑' j : ℕ, (((j : ℝ) + 1) ^ 4 * ρ ^ j) := tsum_mul_left
    _ ≤ (64 * ε * Real.exp ((k : ℝ) * g) * (k : ℝ) ^ 4) * 2 := by
        refine mul_le_mul_of_nonneg_left
          (tsum_add_one_pow_four_mul_geometric_le (ρ := ρ) hρ0 hρ16) ?_
        positivity
    _ = 128 * Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ))) * (k : ℝ) ^ 4 * ε := by
        rw [hg]; ring

/-! ### 5.3 单项 collar 界与逐项求导 -/

/-- 单项 `2c_{k+j}T_{k+j}(y)` 的 collar 界。 -/
lemma norm_chebTail_term_le (τ B : ℝ) (hτ : 0 < τ) (hB : 0 < B) {k j : ℕ}
    {ε r : ℝ} (hε : 0 ≤ ε) (hr : 0 ≤ r)
    (hdec : ∀ i : ℕ, ‖fcoef τ (((k + i : ℕ)) : ℤ)‖ ≤ ε * r ^ i)
    {y : ℝ} (hy : |y| ≤ 1 + B / τ) :
    ‖2 * fcoef τ (((k + j : ℕ)) : ℤ)
        * ((((Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).eval y : ℝ)) : ℂ)‖
      ≤ 2 * ε * Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ)))
        * (r * Real.exp (2 * Real.sqrt (B / τ))) ^ j := by
  set g : ℝ := 2 * Real.sqrt (B / τ) with hg
  have hg0 : 0 ≤ g := by rw [hg]; positivity
  have hBτ0 : 0 ≤ B / τ := by positivity
  have habs : |((((k + j : ℕ)) : ℤ) : ℝ)| = (((k + j : ℕ)) : ℝ) :=
    abs_of_nonneg (by positivity)
  have hT := abs_chebyshevT_le_exp (((k + j : ℕ)) : ℤ) hBτ0 hy
  rw [habs] at hT
  have hTg : |(Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).eval y|
      ≤ Real.exp ((((k + j : ℕ)) : ℝ) * g) := by
    refine hT.trans (le_of_eq ?_)
    rw [hg]; push_cast; ring_nf
  have hexp : Real.exp ((((k + j : ℕ)) : ℝ) * g)
      = Real.exp ((k : ℝ) * g) * (Real.exp g) ^ j := by
    rw [show ((((k + j : ℕ)) : ℝ) * g) = (k : ℝ) * g + (j : ℝ) * g by push_cast; ring,
      Real.exp_add]
    congr 1
    exact Real.exp_nat_mul g j
  have hsplit : ‖2 * fcoef τ (((k + j : ℕ)) : ℤ)
        * ((((Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).eval y : ℝ)) : ℂ)‖
      = 2 * ‖fcoef τ (((k + j : ℕ)) : ℤ)‖
        * |(Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).eval y| := by
    rw [norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs]
  calc ‖2 * fcoef τ (((k + j : ℕ)) : ℤ)
        * ((((Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).eval y : ℝ)) : ℂ)‖
      = 2 * ‖fcoef τ (((k + j : ℕ)) : ℤ)‖
        * |(Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).eval y| := hsplit
    _ ≤ 2 * (ε * r ^ j) * (Real.exp ((k : ℝ) * g) * (Real.exp g) ^ j) := by
        have h1 := hdec j
        have h2 : |(Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).eval y|
            ≤ Real.exp ((k : ℝ) * g) * (Real.exp g) ^ j := by
          rw [← hexp]; exact hTg
        have h3 : (0 : ℝ) ≤ ‖fcoef τ (((k + j : ℕ)) : ℤ)‖ := norm_nonneg _
        have h4 : (0 : ℝ) ≤ |(Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).eval y| :=
          abs_nonneg _
        have h5 : (0 : ℝ) ≤ Real.exp ((k : ℝ) * g) * (Real.exp g) ^ j := by positivity
        have h6 : (0 : ℝ) ≤ ε * r ^ j := by positivity
        nlinarith [h1, h2, h3, h4, h5, h6,
          mul_nonneg (sub_nonneg.mpr h1) h4, mul_nonneg h3 (sub_nonneg.mpr h2)]
    _ = 2 * ε * Real.exp ((k : ℝ) * g) * (r * Real.exp g) ^ j := by rw [mul_pow]; ring
    _ = 2 * ε * Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ)))
        * (r * Real.exp (2 * Real.sqrt (B / τ))) ^ j := by rw [hg]

/-- 单项 `2c_{k+j}T'_{k+j}(y)` 的 collar 界。 -/
lemma norm_chebTailD1_term_le (τ B : ℝ) (hτ : 0 < τ) (hB : 0 < B) {k j : ℕ} (hk : 1 ≤ k)
    {ε r : ℝ} (hε : 0 ≤ ε) (hr : 0 ≤ r)
    (hdec : ∀ i : ℕ, ‖fcoef τ (((k + i : ℕ)) : ℤ)‖ ≤ ε * r ^ i)
    {y : ℝ} (hy : |y| ≤ 1 + B / τ) :
    ‖2 * fcoef τ (((k + j : ℕ)) : ℤ)
        * ((((Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).derivative.eval y : ℝ)) : ℂ)‖
      ≤ 2 * ε * Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ))) * (k : ℝ) ^ 2
        * (((j : ℝ) + 1) ^ 2 * (r * Real.exp (2 * Real.sqrt (B / τ))) ^ j) := by
  set g : ℝ := 2 * Real.sqrt (B / τ) with hg
  have hg0 : 0 ≤ g := by rw [hg]; positivity
  have hBτ0 : 0 ≤ B / τ := by positivity
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkj : (((k + j : ℕ)) : ℝ) ≤ (k : ℝ) * ((j : ℝ) + 1) := by
    push_cast
    nlinarith [hk1, (Nat.cast_nonneg j : (0 : ℝ) ≤ (j : ℝ))]
  have habs : |((((k + j : ℕ)) : ℤ) : ℝ)| = (((k + j : ℕ)) : ℝ) :=
    abs_of_nonneg (by positivity)
  have hT := abs_deriv_chebyshevT_le_exp (((k + j : ℕ)) : ℤ) hBτ0 hy
  rw [habs] at hT
  have hTg : |(Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).derivative.eval y|
      ≤ (((k + j : ℕ)) : ℝ) ^ 2 * Real.exp ((((k + j : ℕ)) : ℝ) * g) := by
    refine hT.trans (le_of_eq ?_)
    rw [hg]; push_cast; ring_nf
  have hexp : Real.exp ((((k + j : ℕ)) : ℝ) * g)
      = Real.exp ((k : ℝ) * g) * (Real.exp g) ^ j := by
    rw [show ((((k + j : ℕ)) : ℝ) * g) = (k : ℝ) * g + (j : ℝ) * g by push_cast; ring,
      Real.exp_add]
    congr 1
    exact Real.exp_nat_mul g j
  have hsplit : ‖2 * fcoef τ (((k + j : ℕ)) : ℤ)
        * ((((Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).derivative.eval y : ℝ)) : ℂ)‖
      = 2 * ‖fcoef τ (((k + j : ℕ)) : ℤ)‖
        * |(Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).derivative.eval y| := by
    rw [norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs]
  calc ‖2 * fcoef τ (((k + j : ℕ)) : ℤ)
        * ((((Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).derivative.eval y : ℝ)) : ℂ)‖
      = 2 * ‖fcoef τ (((k + j : ℕ)) : ℤ)‖
        * |(Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).derivative.eval y| := hsplit
    _ ≤ 2 * (ε * r ^ j)
        * (((k : ℝ) * ((j : ℝ) + 1)) ^ 2 * (Real.exp ((k : ℝ) * g) * (Real.exp g) ^ j)) := by
        have h1 := hdec j
        have h2 : |(Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).derivative.eval y|
            ≤ ((k : ℝ) * ((j : ℝ) + 1)) ^ 2
              * (Real.exp ((k : ℝ) * g) * (Real.exp g) ^ j) := by
          refine hTg.trans ?_
          rw [hexp]
          have hsq : (((k + j : ℕ)) : ℝ) ^ 2 ≤ ((k : ℝ) * ((j : ℝ) + 1)) ^ 2 :=
            pow_le_pow_left₀ (by positivity) hkj 2
          have hE : (0 : ℝ) ≤ Real.exp ((k : ℝ) * g) * (Real.exp g) ^ j := by positivity
          exact mul_le_mul_of_nonneg_right hsq hE
        have h3 : (0 : ℝ) ≤ ‖fcoef τ (((k + j : ℕ)) : ℤ)‖ := norm_nonneg _
        have h4 : (0 : ℝ) ≤
          |(Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).derivative.eval y| := abs_nonneg _
        have h5 : (0 : ℝ) ≤ ((k : ℝ) * ((j : ℝ) + 1)) ^ 2
            * (Real.exp ((k : ℝ) * g) * (Real.exp g) ^ j) := by positivity
        have h6 : (0 : ℝ) ≤ ε * r ^ j := by positivity
        nlinarith [h1, h2, h3, h4, h5, h6,
          mul_nonneg (sub_nonneg.mpr h1) h4, mul_nonneg h3 (sub_nonneg.mpr h2)]
    _ = 2 * ε * Real.exp ((k : ℝ) * g) * (k : ℝ) ^ 2 * (((j : ℝ) + 1) ^ 2 * (r * Real.exp g) ^ j) := by
        rw [mul_pow]; ring
    _ = 2 * ε * Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ))) * (k : ℝ) ^ 2
        * (((j : ℝ) + 1) ^ 2 * (r * Real.exp (2 * Real.sqrt (B / τ))) ^ j) := by rw [hg]

/-- 单项 `2c_{k+j}T''_{k+j}(y)` 的 collar 界。 -/
lemma norm_chebTailD2_term_le (τ B : ℝ) (hτ : 0 < τ) (hB : 0 < B) {k j : ℕ} (hk : 1 ≤ k)
    {ε r : ℝ} (hε : 0 ≤ ε) (hr : 0 ≤ r)
    (hdec : ∀ i : ℕ, ‖fcoef τ (((k + i : ℕ)) : ℤ)‖ ≤ ε * r ^ i)
    (hBτ : B / τ ≤ 1 / 2) {y : ℝ} (hy : |y| ≤ 1 + B / τ) :
    ‖2 * fcoef τ (((k + j : ℕ)) : ℤ)
        * ((((Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).derivative.derivative.eval y : ℝ)) : ℂ)‖
      ≤ 64 * ε * Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ))) * (k : ℝ) ^ 4
        * (((j : ℝ) + 1) ^ 4 * (r * Real.exp (2 * Real.sqrt (B / τ))) ^ j) := by
  set g : ℝ := 2 * Real.sqrt (B / τ) with hg
  have hg0 : 0 ≤ g := by rw [hg]; positivity
  have hBτ0 : 0 ≤ B / τ := by positivity
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkj : (((k + j : ℕ)) : ℝ) ≤ (k : ℝ) * ((j : ℝ) + 1) := by
    push_cast
    nlinarith [hk1, (Nat.cast_nonneg j : (0 : ℝ) ≤ (j : ℝ))]
  have habs : |((((k + j : ℕ)) : ℤ) : ℝ)| = (((k + j : ℕ)) : ℝ) :=
    abs_of_nonneg (by positivity)
  have hT := abs_deriv2_chebyshevT_le_exp (((k + j : ℕ)) : ℤ) hBτ0 hBτ hy
  rw [habs] at hT
  have hTg : |(Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).derivative.derivative.eval y|
      ≤ 32 * (((k + j : ℕ)) : ℝ) ^ 4 * Real.exp ((((k + j : ℕ)) : ℝ) * g) := by
    refine hT.trans (le_of_eq ?_)
    rw [hg]; push_cast; ring_nf
  have hexp : Real.exp ((((k + j : ℕ)) : ℝ) * g)
      = Real.exp ((k : ℝ) * g) * (Real.exp g) ^ j := by
    rw [show ((((k + j : ℕ)) : ℝ) * g) = (k : ℝ) * g + (j : ℝ) * g by push_cast; ring,
      Real.exp_add]
    congr 1
    exact Real.exp_nat_mul g j
  have hsplit : ‖2 * fcoef τ (((k + j : ℕ)) : ℤ)
        * ((((Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).derivative.derivative.eval y : ℝ)) : ℂ)‖
      = 2 * ‖fcoef τ (((k + j : ℕ)) : ℤ)‖
        * |(Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).derivative.derivative.eval y| := by
    rw [norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs]
  calc ‖2 * fcoef τ (((k + j : ℕ)) : ℤ)
        * ((((Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).derivative.derivative.eval y : ℝ)) : ℂ)‖
      = 2 * ‖fcoef τ (((k + j : ℕ)) : ℤ)‖
        * |(Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).derivative.derivative.eval y| := hsplit
    _ ≤ 2 * (ε * r ^ j)
        * (32 * ((k : ℝ) * ((j : ℝ) + 1)) ^ 4
          * (Real.exp ((k : ℝ) * g) * (Real.exp g) ^ j)) := by
        have h1 := hdec j
        have h2 : |(Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).derivative.derivative.eval y|
            ≤ 32 * ((k : ℝ) * ((j : ℝ) + 1)) ^ 4
              * (Real.exp ((k : ℝ) * g) * (Real.exp g) ^ j) := by
          refine hTg.trans ?_
          rw [hexp]
          have hsq : (((k + j : ℕ)) : ℝ) ^ 4 ≤ ((k : ℝ) * ((j : ℝ) + 1)) ^ 4 :=
            pow_le_pow_left₀ (by positivity) hkj 4
          have hE : (0 : ℝ) ≤ Real.exp ((k : ℝ) * g) * (Real.exp g) ^ j := by positivity
          nlinarith [hsq, hE, Real.exp_pos ((k : ℝ) * g)]
        have h3 : (0 : ℝ) ≤ ‖fcoef τ (((k + j : ℕ)) : ℤ)‖ := norm_nonneg _
        have h4 : (0 : ℝ) ≤
          |(Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).derivative.derivative.eval y| := abs_nonneg _
        have h5 : (0 : ℝ) ≤ 32 * ((k : ℝ) * ((j : ℝ) + 1)) ^ 4
            * (Real.exp ((k : ℝ) * g) * (Real.exp g) ^ j) := by positivity
        have h6 : (0 : ℝ) ≤ ε * r ^ j := by positivity
        nlinarith [h1, h2, h3, h4, h5, h6,
          mul_nonneg (sub_nonneg.mpr h1) h4, mul_nonneg h3 (sub_nonneg.mpr h2)]
    _ = 64 * ε * Real.exp ((k : ℝ) * g) * (k : ℝ) ^ 4
          * (((j : ℝ) + 1) ^ 4 * (r * Real.exp g) ^ j) := by rw [mul_pow]; ring
    _ = 64 * ε * Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ))) * (k : ℝ) ^ 4
        * (((j : ℝ) + 1) ^ 4 * (r * Real.exp (2 * Real.sqrt (B / τ))) ^ j) := by rw [hg]

/-- **Chebyshev 尾部级数逐项求导**：`chebTail` 的导数是 `chebTailD1`。 -/
lemma hasDerivAt_chebTail (τ B : ℝ) (hτ : 0 < τ) (hB : 0 < B) {k : ℕ} (hk : 1 ≤ k)
    {ε r : ℝ} (hε : 0 ≤ ε) (hr : 0 ≤ r)
    (hdec : ∀ i : ℕ, ‖fcoef τ (((k + i : ℕ)) : ℤ)‖ ≤ ε * r ^ i)
    (hρ : r * Real.exp (2 * Real.sqrt (B / τ)) ≤ 1 / 32)
    {u : ℝ} (hu : |u| < 1 + B / τ) :
    HasDerivAt (fun z : ℝ => chebTail τ k z) (chebTailD1 τ k u) u := by
  set g : ℝ := 2 * Real.sqrt (B / τ) with hg
  set ρ : ℝ := r * Real.exp g with hρdef
  have hρ0 : 0 ≤ ρ := by rw [hρdef]; positivity
  have h4ρ : 4 * ρ < 1 := by rw [hρdef, hg] at hρ ⊢; linarith
  have hmem : u ∈ Set.Ioo (-(1 + B / τ)) (1 + B / τ) := by
    rw [Set.mem_Ioo]
    exact abs_lt.mp hu
  have hmaj : Summable (fun j : ℕ =>
      2 * ε * Real.exp ((k : ℝ) * g) * (k : ℝ) ^ 2 * (((j : ℝ) + 1) ^ 2 * ρ ^ j)) :=
    (Summable.mul_left _ (summable_add_one_pow_two_mul_geometric hρ0 h4ρ))
  have hbd : ∀ j : ℕ, ∀ y ∈ Set.Ioo (-(1 + B / τ)) (1 + B / τ),
      ‖2 * fcoef τ (((k + j : ℕ)) : ℤ)
        * ((((Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).derivative.eval y : ℝ)) : ℂ)‖
      ≤ 2 * ε * Real.exp ((k : ℝ) * g) * (k : ℝ) ^ 2 * (((j : ℝ) + 1) ^ 2 * ρ ^ j) := by
    intro j y hy
    have hy' : |y| ≤ 1 + B / τ := by
      have h := hy
      rw [Set.mem_Ioo] at h
      exact le_of_lt (abs_lt.mpr h)
    have h := norm_chebTailD1_term_le (k := k) (j := j) τ B hτ hB hk hε hr hdec hy'
    simpa only [hρdef, hg] using h
  have hf0 : Summable (fun j : ℕ => 2 * fcoef τ (((k + j : ℕ)) : ℤ)
      * ((((Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).eval u : ℝ)) : ℂ)) := by
    refine Summable.of_norm ?_
    refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_) hmaj
    have hu' : |u| ≤ 1 + B / τ := le_of_lt hu
    have h := norm_chebTail_term_le (k := k) (j := j) τ B hτ hB hε hr hdec hu'
    rw [← hg] at h
    have h1 : (r * Real.exp g) ^ j ≤ ((j : ℝ) + 1) ^ 2 * ρ ^ j := by
      rw [hρdef]
      have h2 : (1 : ℝ) ≤ ((j : ℝ) + 1) ^ 2 := by
        nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ (j : ℝ))]
      have h3 : (0 : ℝ) ≤ (r * Real.exp g) ^ j := by positivity
      nlinarith [h2, h3]
    have h4 : (0 : ℝ) ≤ Real.exp ((k : ℝ) * g) := (Real.exp_pos _).le
    have h6 : (0 : ℝ) ≤ ε := hε
    have h7 : (0 : ℝ) ≤ ((j : ℝ) + 1) ^ 2 * ρ ^ j := by positivity
    have h8 : (0 : ℝ) ≤ (r * Real.exp g) ^ j := by positivity
    calc ‖2 * fcoef τ (((k + j : ℕ)) : ℤ)
          * ((((Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).eval u : ℝ)) : ℂ)‖
        ≤ 2 * ε * Real.exp ((k : ℝ) * g) * (r * Real.exp g) ^ j := h
      _ ≤ 2 * ε * Real.exp ((k : ℝ) * g) * (((j : ℝ) + 1) ^ 2 * ρ ^ j) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ 2 * ε * Real.exp ((k : ℝ) * g) * (k : ℝ) ^ 2 * (((j : ℝ) + 1) ^ 2 * ρ ^ j) := by
          have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
          have hk2 : (1 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
          have hA : (0 : ℝ) ≤ 2 * ε * Real.exp ((k : ℝ) * g) * (((j : ℝ) + 1) ^ 2 * ρ ^ j) := by
            positivity
          calc 2 * ε * Real.exp ((k : ℝ) * g) * (((j : ℝ) + 1) ^ 2 * ρ ^ j)
              = (2 * ε * Real.exp ((k : ℝ) * g) * (((j : ℝ) + 1) ^ 2 * ρ ^ j)) * 1 := by ring
            _ ≤ (2 * ε * Real.exp ((k : ℝ) * g) * (((j : ℝ) + 1) ^ 2 * ρ ^ j)) * (k : ℝ) ^ 2 :=
                mul_le_mul_of_nonneg_left hk2 hA
            _ = 2 * ε * Real.exp ((k : ℝ) * g) * (k : ℝ) ^ 2 * (((j : ℝ) + 1) ^ 2 * ρ ^ j) := by
                ring
  refine hasDerivAt_tsum_of_isPreconnected
    (u := fun j : ℕ => 2 * ε * Real.exp ((k : ℝ) * g) * (k : ℝ) ^ 2 * (((j : ℝ) + 1) ^ 2 * ρ ^ j))
    (g := fun j : ℕ => fun y : ℝ => 2 * fcoef τ (((k + j : ℕ)) : ℤ)
      * ((((Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).eval y : ℝ)) : ℂ))
    (g' := fun j : ℕ => fun y : ℝ => 2 * fcoef τ (((k + j : ℕ)) : ℤ)
      * ((((Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).derivative.eval y : ℝ)) : ℂ))
    (t := Set.Ioo (-(1 + B / τ)) (1 + B / τ))
    hmaj isOpen_Ioo isPreconnected_Ioo ?_ hbd hmem hf0 hmem
  intro n y _
  exact ((Polynomial.hasDerivAt (Polynomial.Chebyshev.T ℝ (((k + n : ℕ)) : ℤ)) y).ofReal_comp).const_mul _

/-- **`chebTailD1` 逐项求导**：其导数是 `chebTailD2`。 -/
lemma hasDerivAt_chebTailD1 (τ B : ℝ) (hτ : 0 < τ) (hB : 0 < B) {k : ℕ} (hk : 1 ≤ k)
    {ε r : ℝ} (hε : 0 ≤ ε) (hr : 0 ≤ r)
    (hdec : ∀ i : ℕ, ‖fcoef τ (((k + i : ℕ)) : ℤ)‖ ≤ ε * r ^ i)
    (hρ : r * Real.exp (2 * Real.sqrt (B / τ)) ≤ 1 / 32) (hBτ : B / τ ≤ 1 / 2)
    {u : ℝ} (hu : |u| < 1 + B / τ) :
    HasDerivAt (fun z : ℝ => chebTailD1 τ k z) (chebTailD2 τ k u) u := by
  set g : ℝ := 2 * Real.sqrt (B / τ) with hg
  set ρ : ℝ := r * Real.exp g with hρdef
  have hρ0 : 0 ≤ ρ := by rw [hρdef]; positivity
  have h16ρ : 16 * ρ < 1 := by rw [hρdef, hg] at hρ ⊢; linarith
  have hmem : u ∈ Set.Ioo (-(1 + B / τ)) (1 + B / τ) := by
    rw [Set.mem_Ioo]
    exact abs_lt.mp hu
  have hmaj : Summable (fun j : ℕ =>
      64 * ε * Real.exp ((k : ℝ) * g) * (k : ℝ) ^ 4 * (((j : ℝ) + 1) ^ 4 * ρ ^ j)) :=
    (Summable.mul_left _ (summable_add_one_pow_four_mul_geometric hρ0 h16ρ))
  have hbd : ∀ j : ℕ, ∀ y ∈ Set.Ioo (-(1 + B / τ)) (1 + B / τ),
      ‖2 * fcoef τ (((k + j : ℕ)) : ℤ)
        * ((((Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).derivative.derivative.eval y : ℝ)) : ℂ)‖
      ≤ 64 * ε * Real.exp ((k : ℝ) * g) * (k : ℝ) ^ 4 * (((j : ℝ) + 1) ^ 4 * ρ ^ j) := by
    intro j y hy
    have hy' : |y| ≤ 1 + B / τ := by
      have h := hy
      rw [Set.mem_Ioo] at h
      exact le_of_lt (abs_lt.mpr h)
    have h := norm_chebTailD2_term_le (k := k) (j := j) τ B hτ hB hk hε hr hdec hBτ hy'
    simpa only [hρdef, hg] using h
  have hf0 : Summable (fun j : ℕ => 2 * fcoef τ (((k + j : ℕ)) : ℤ)
      * ((((Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).derivative.eval u : ℝ)) : ℂ)) := by
    refine Summable.of_norm ?_
    refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_) hmaj
    have hu' : |u| ≤ 1 + B / τ := le_of_lt hu
    have h := norm_chebTailD1_term_le (k := k) (j := j) τ B hτ hB hk hε hr hdec hu'
    rw [← hg] at h
    have h1 : (0 : ℝ) ≤ (k : ℝ) ^ 2 := by positivity
    have h2 : (0 : ℝ) ≤ ((j : ℝ) + 1) ^ 2 * ρ ^ j := by positivity
    have h3 : (0 : ℝ) ≤ Real.exp ((k : ℝ) * g) := (Real.exp_pos _).le
    have h4 : (0 : ℝ) ≤ ε := hε
    have h5 : ((j : ℝ) + 1) ^ 2 * ρ ^ j ≤ ((j : ℝ) + 1) ^ 4 * ρ ^ j := by
      have h6 : (1 : ℝ) ≤ ((j : ℝ) + 1) ^ 2 := by
        nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ (j : ℝ))]
      have h7 : (0 : ℝ) ≤ ρ ^ j := by positivity
      nlinarith [h6, h7, h2]
    calc ‖2 * fcoef τ (((k + j : ℕ)) : ℤ)
          * ((((Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).derivative.eval u : ℝ)) : ℂ)‖
        ≤ 2 * ε * Real.exp ((k : ℝ) * g) * (k : ℝ) ^ 2 * (((j : ℝ) + 1) ^ 2 * ρ ^ j) := h
      _ ≤ 2 * ε * Real.exp ((k : ℝ) * g) * (k : ℝ) ^ 2 * (((j : ℝ) + 1) ^ 4 * ρ ^ j) :=
          mul_le_mul_of_nonneg_left h5 (by positivity)
      _ ≤ 2 * ε * Real.exp ((k : ℝ) * g) * (k : ℝ) ^ 4 * (((j : ℝ) + 1) ^ 4 * ρ ^ j) := by
          have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
          have hk2 : (1 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
          have hk4 : (k : ℝ) ^ 2 ≤ (k : ℝ) ^ 4 := by nlinarith [hk2]
          have hB : (0 : ℝ) ≤ 2 * ε * Real.exp ((k : ℝ) * g)
            * (((j : ℝ) + 1) ^ 4 * ρ ^ j) := by positivity
          calc 2 * ε * Real.exp ((k : ℝ) * g) * (k : ℝ) ^ 2 * (((j : ℝ) + 1) ^ 4 * ρ ^ j)
              = (2 * ε * Real.exp ((k : ℝ) * g) * (((j : ℝ) + 1) ^ 4 * ρ ^ j)) * (k : ℝ) ^ 2 := by
                ring
            _ ≤ (2 * ε * Real.exp ((k : ℝ) * g) * (((j : ℝ) + 1) ^ 4 * ρ ^ j)) * (k : ℝ) ^ 4 :=
                mul_le_mul_of_nonneg_left hk4 hB
            _ = 2 * ε * Real.exp ((k : ℝ) * g) * (k : ℝ) ^ 4 * (((j : ℝ) + 1) ^ 4 * ρ ^ j) := by
                ring
      _ ≤ 64 * ε * Real.exp ((k : ℝ) * g) * (k : ℝ) ^ 4 * (((j : ℝ) + 1) ^ 4 * ρ ^ j) := by
          have hB : (0 : ℝ) ≤ ε * Real.exp ((k : ℝ) * g) * (k : ℝ) ^ 4
            * (((j : ℝ) + 1) ^ 4 * ρ ^ j) := by positivity
          nlinarith [hB]
  refine hasDerivAt_tsum_of_isPreconnected
    (u := fun j : ℕ => 64 * ε * Real.exp ((k : ℝ) * g) * (k : ℝ) ^ 4 * (((j : ℝ) + 1) ^ 4 * ρ ^ j))
    (g := fun j : ℕ => fun y : ℝ => 2 * fcoef τ (((k + j : ℕ)) : ℤ)
      * ((((Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).derivative.eval y : ℝ)) : ℂ))
    (g' := fun j : ℕ => fun y : ℝ => 2 * fcoef τ (((k + j : ℕ)) : ℤ)
      * ((((Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).derivative.derivative.eval y : ℝ)) : ℂ))
    (t := Set.Ioo (-(1 + B / τ)) (1 + B / τ))
    hmaj isOpen_Ioo isPreconnected_Ioo ?_ hbd hmem hf0 hmem
  intro n y _
  exact ((Polynomial.hasDerivAt (Polynomial.Chebyshev.T ℝ (((k + n : ℕ)) : ℤ)).derivative y).ofReal_comp).const_mul _

/-! ### 5.4 collar 恒等式、导数恒等式与闭 collar 上的最终界 -/

/-- `x ↦ e^{-ix}` 的导数。 -/
lemma hasDerivAt_exp_neg_I (μ : ℝ) :
    HasDerivAt (fun x : ℝ => Complex.exp (-(x : ℂ) * Complex.I))
      (-Complex.I * Complex.exp (-(μ : ℂ) * Complex.I)) μ := by
  have hlin : HasDerivAt (fun w : ℂ => -w * Complex.I) (-Complex.I) ((μ : ℝ) : ℂ) := by
    have h := (hasDerivAt_id ((μ : ℝ) : ℂ)).neg.mul_const Complex.I
    have h3 : (-(1 : ℂ)) * Complex.I = -Complex.I := by ring
    rw [h3] at h
    exact h
  have hexp : HasDerivAt Complex.exp (Complex.exp (-(μ : ℂ) * Complex.I)) (-(μ : ℂ) * Complex.I) :=
    Complex.hasDerivAt_exp _
  have h := HasDerivAt.comp ((μ : ℝ) : ℂ) hexp hlin
  have h4 : Complex.exp (-(μ : ℂ) * Complex.I) * (-Complex.I)
      = -Complex.I * Complex.exp (-(μ : ℂ) * Complex.I) := by ring
  rw [h4] at h
  simpa [Function.comp_def] using h.comp_ofReal

/-- `sharpErr τ k` 的显式导数（用于连续性）。 -/
lemma deriv_sharpErr_eq (τ : ℝ) (k : ℕ) (μ : ℝ) :
    deriv (sharpErr τ k) μ
      = -Complex.I * Complex.exp (-(μ : ℂ) * Complex.I)
        - (scaledApprox τ k).derivative.eval ((μ : ℝ) : ℂ) := by
  have h1 := hasDerivAt_exp_neg_I μ
  have h2 : HasDerivAt (fun x : ℝ => (scaledApprox τ k).eval ((x : ℝ) : ℂ))
      ((scaledApprox τ k).derivative.eval ((μ : ℝ) : ℂ)) μ :=
    (Polynomial.hasDerivAt (scaledApprox τ k) ((μ : ℝ) : ℂ)).comp_ofReal
  have h3 := h1.sub h2
  change deriv (fun x : ℝ => Complex.exp (-(x : ℂ) * Complex.I)
    - (scaledApprox τ k).eval ((x : ℝ) : ℂ)) μ
    = -Complex.I * Complex.exp (-(μ : ℂ) * Complex.I)
      - (scaledApprox τ k).derivative.eval ((μ : ℝ) : ℂ)
  exact h3.deriv

/-- `deriv (deriv (sharpErr τ k))` 连续。 -/
lemma continuous_deriv2_sharpErr (τ : ℝ) (k : ℕ) :
    Continuous (deriv (deriv (sharpErr τ k))) := by
  have h2 : deriv (fun μ : ℝ => -Complex.I * Complex.exp (-(μ : ℂ) * Complex.I)
      - (scaledApprox τ k).derivative.eval ((μ : ℝ) : ℂ))
      = fun μ : ℝ => -Complex.exp (-(μ : ℂ) * Complex.I)
        - (scaledApprox τ k).derivative.derivative.eval ((μ : ℝ) : ℂ) := by
    funext μ
    have hd1 : HasDerivAt (fun x : ℝ => -Complex.I * Complex.exp (-(x : ℂ) * Complex.I))
        (-Complex.I * (-Complex.I * Complex.exp (-(μ : ℂ) * Complex.I))) μ :=
      (hasDerivAt_exp_neg_I μ).const_mul (-Complex.I)
    have hd2 : HasDerivAt (fun x : ℝ => (scaledApprox τ k).derivative.eval ((x : ℝ) : ℂ))
        ((scaledApprox τ k).derivative.derivative.eval ((μ : ℝ) : ℂ)) μ :=
      (Polynomial.hasDerivAt (scaledApprox τ k).derivative ((μ : ℝ) : ℂ)).comp_ofReal
    have hd := hd1.sub hd2
    have hd' : deriv (fun μ : ℝ => -Complex.I * Complex.exp (-(μ : ℂ) * Complex.I)
        - (scaledApprox τ k).derivative.eval ((μ : ℝ) : ℂ)) μ
        = -Complex.I * (-Complex.I * Complex.exp (-(μ : ℂ) * Complex.I))
          - (scaledApprox τ k).derivative.derivative.eval ((μ : ℝ) : ℂ) := hd.deriv
    rw [hd']
    ring_nf
    rw [show Complex.I ^ 2 = -1 by rw [sq, Complex.I_mul_I]]
    ring
  rw [show deriv (deriv (sharpErr τ k)) = deriv (fun μ : ℝ =>
      -Complex.I * Complex.exp (-(μ : ℂ) * Complex.I)
        - (scaledApprox τ k).derivative.eval ((μ : ℝ) : ℂ)) from by
    rw [show deriv (sharpErr τ k) = fun μ : ℝ =>
        -Complex.I * Complex.exp (-(μ : ℂ) * Complex.I)
          - (scaledApprox τ k).derivative.eval ((μ : ℝ) : ℂ) from
      funext fun μ => deriv_sharpErr_eq τ k μ]]
  rw [h2]
  refine Continuous.sub ?_ ?_
  · exact (Complex.continuous_exp.comp (by fun_prop)).neg
  · exact (Polynomial.continuous (scaledApprox τ k).derivative.derivative).comp
      Complex.continuous_ofReal

/-- `deriv (sharpErr τ k)` 连续。 -/
lemma continuous_deriv_sharpErr (τ : ℝ) (k : ℕ) : Continuous (deriv (sharpErr τ k)) := by
  rw [show deriv (sharpErr τ k) = fun μ : ℝ =>
      -Complex.I * Complex.exp (-(μ : ℂ) * Complex.I)
        - (scaledApprox τ k).derivative.eval ((μ : ℝ) : ℂ) from
    funext fun μ => deriv_sharpErr_eq τ k μ]
  refine Continuous.sub ?_ ?_
  · exact continuous_const.mul (Complex.continuous_exp.comp (by fun_prop))
  · exact (Polynomial.continuous (scaledApprox τ k).derivative).comp Complex.continuous_ofReal

/-- `sharpErr τ k` 在任意点可微。 -/
lemma differentiableAt_sharpErr (τ : ℝ) (k : ℕ) (x : ℝ) : DifferentiableAt ℝ (sharpErr τ k) x := by
  change DifferentiableAt ℝ (fun y : ℝ => Complex.exp (-(y : ℂ) * Complex.I)
    - (scaledApprox τ k).eval ((y : ℝ) : ℂ)) x
  refine DifferentiableAt.sub ?_ ?_
  · exact Complex.differentiableAt_exp.comp x (by fun_prop)
  · exact ((Polynomial.hasDerivAt (scaledApprox τ k) (x : ℂ)).comp_ofReal).differentiableAt

/-- **闭 collar 上的恒等式**（`-1 ≤ u`，即 `u` 落在 `cos` 分支或右半 collar）。 -/
lemma chebTail_eq_sharpErr_collar (τ : ℝ) (hτ : 0 < τ) {k : ℕ} (hk : 1 ≤ k) (B : ℝ)
    {u : ℝ} (hu : |u| ≤ 1 + B / τ) (hu1 : -1 ≤ u) :
    chebTail τ k u = sharpErr τ k (τ * u) := by
  rcases le_or_gt u 1 with hle | hgt
  · rcases eq_or_lt_of_le (Real.arccos_nonneg u) with h0 | hpos
    · have huone : u = 1 := by
        have h3 := Real.cos_arccos hu1 hle
        rw [← h3, ← h0, Real.cos_zero]
      rw [huone, mul_one]
      simpa using (sharpErr_cos_eq_chebTail τ hτ hk (θ := 2 * Real.pi)
        ⟨by positivity, le_refl _⟩).symm
    · have hπ : Real.arccos u ≤ 2 * Real.pi := by
        have := Real.arccos_le_pi u
        linarith [Real.pi_pos]
      have h := sharpErr_cos_eq_chebTail τ hτ hk (θ := Real.arccos u) ⟨hpos, hπ⟩
      rw [Real.cos_arccos hu1 hle] at h
      exact h.symm
  · have h1 : 1 ≤ u := le_of_lt hgt
    have h := sharpErr_cosh_eq_chebTail τ hτ hk (w := Real.arcosh u) (Real.arcosh_pos hgt)
    rw [Real.cosh_arcosh h1] at h
    exact h.symm

/-- 负半 collar 的恒等式（由反射对称）。 -/
lemma chebTail_eq_sharpErr_collar_neg (τ : ℝ) (hτ : 0 < τ) {k : ℕ} (hk : 1 ≤ k) (B : ℝ)
    {u : ℝ} (hu : |u| ≤ 1 + B / τ) (hu1 : u ≤ -1) :
    chebTail τ k u = sharpErr τ k (τ * u) := by
  have h2 : -u ≤ 1 + B / τ := by
    rw [show -u = |u| by rw [abs_of_nonpos (by linarith)]]
    exact hu
  have h3 : chebTail τ k (-u) = sharpErr τ k (τ * (-u)) :=
    chebTail_eq_sharpErr_collar τ hτ hk B (u := -u)
      (by rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ -u)]; exact h2) (by linarith)
  have h4 : chebTail τ k u = (starRingEnd ℂ) (chebTail τ k (-u)) := by
    have h := chebTail_neg τ k (-u)
    rwa [neg_neg] at h
  have h5 : sharpErr τ k (τ * u) = (starRingEnd ℂ) (sharpErr τ k (τ * (-u))) := by
    have h := sharpErr_neg τ (ne_of_gt hτ) k (-(τ * u))
    rw [neg_neg, show -(τ * u) = τ * (-u) by ring] at h
    exact h
  rw [h4, h3, h5]

/-- **collar 上的恒等式（统一形式）**。 -/
lemma chebTail_eq_sharpErr_collar_all (τ : ℝ) (hτ : 0 < τ) {k : ℕ} (hk : 1 ≤ k) (B : ℝ)
    {u : ℝ} (hu : |u| ≤ 1 + B / τ) :
    chebTail τ k u = sharpErr τ k (τ * u) := by
  rcases le_or_gt (-1) u with h | h
  · exact chebTail_eq_sharpErr_collar τ hτ hk B hu h
  · exact chebTail_eq_sharpErr_collar_neg τ hτ hk B hu (le_of_lt h)

/-- **一阶导恒等式（开 collar）**：`deriv Q μ = chebTailD1 τ k (μ/τ)/τ`。 -/
lemma deriv_sharpErr_eq_chebTailD1 (τ B : ℝ) (hτ : 0 < τ) (hB : 0 < B) {k : ℕ} (hk : 1 ≤ k)
    {ε r : ℝ} (hε : 0 ≤ ε) (hr : 0 ≤ r)
    (hdec : ∀ j : ℕ, ‖fcoef τ (((k + j : ℕ)) : ℤ)‖ ≤ ε * r ^ j)
    (hρ : r * Real.exp (2 * Real.sqrt (B / τ)) ≤ 1 / 32)
    {μ : ℝ} (hμ : |μ| < τ + B) :
    deriv (sharpErr τ k) μ = chebTailD1 τ k (μ / τ) / τ := by
  have hτne : τ ≠ 0 := ne_of_gt hτ
  have hτneC : ((τ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hτne
  have hu : |μ / τ| < 1 + B / τ := by
    rw [abs_div, abs_of_pos hτ, div_lt_iff₀ hτ]
    have h : (1 + B / τ) * τ = τ + B := by field_simp
    rw [h]; exact hμ
  have _hu := hu
  have hev : (fun z : ℝ => sharpErr τ k (τ * z)) =ᶠ[𝓝 (μ / τ)]
      (fun z : ℝ => chebTail τ k z) := by
    refine Filter.eventually_of_mem ((isOpen_lt continuous_abs continuous_const).mem_nhds hu)
      fun z hz => ?_
    rw [Set.mem_ofPred_eq] at hz
    exact (chebTail_eq_sharpErr_collar_all τ hτ hk B (le_of_lt hz)).symm
  have hder := Filter.EventuallyEq.deriv_eq hev
  have h1 : deriv (fun z : ℝ => sharpErr τ k (τ * z)) (μ / τ)
      = ((τ : ℝ) : ℂ) * deriv (sharpErr τ k) (τ * (μ / τ)) := by
    have hl : HasDerivAt (sharpErr τ k) (deriv (sharpErr τ k) (τ * (μ / τ))) (τ * (μ / τ)) :=
      (differentiableAt_sharpErr τ k (τ * (μ / τ))).hasDerivAt
    have hf : HasDerivAt (fun z : ℝ => τ * z) τ (μ / τ) := by
      simpa using (hasDerivAt_id (μ / τ)).const_mul τ
    have hcomp := (hl.hasFDerivAt).comp_hasDerivAt (μ / τ) hf
    have hd := hcomp.deriv
    rw [ContinuousLinearMap.toSpanSingleton_apply, Complex.real_smul] at hd
    exact hd
  have h2 : deriv (fun z : ℝ => chebTail τ k z) (μ / τ) = chebTailD1 τ k (μ / τ) :=
    (hasDerivAt_chebTail τ B hτ hB hk hε hr hdec hρ hu).deriv
  rw [h1, h2] at hder
  have hτu : τ * (μ / τ) = μ := by field_simp
  rw [hτu, mul_comm] at hder
  rw [eq_div_iff hτneC]
  exact hder

/-- **二阶导恒等式（开 collar）**：`deriv (deriv Q) μ = chebTailD2 τ k (μ/τ)/τ²`。 -/
lemma deriv2_sharpErr_eq_chebTailD2 (τ B : ℝ) (hτ : 0 < τ) (hB : 0 < B) {k : ℕ} (hk : 1 ≤ k)
    {ε r : ℝ} (hε : 0 ≤ ε) (hr : 0 ≤ r)
    (hdec : ∀ j : ℕ, ‖fcoef τ (((k + j : ℕ)) : ℤ)‖ ≤ ε * r ^ j)
    (hρ : r * Real.exp (2 * Real.sqrt (B / τ)) ≤ 1 / 32) (hBτ : B / τ ≤ 1 / 2)
    {μ : ℝ} (hμ : |μ| < τ + B) :
    deriv (deriv (sharpErr τ k)) μ = chebTailD2 τ k (μ / τ) / τ ^ 2 := by
  have hτne : τ ≠ 0 := ne_of_gt hτ
  have hτneC : ((τ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hτne
  have hu : |μ / τ| < 1 + B / τ := by
    rw [abs_div, abs_of_pos hτ, div_lt_iff₀ hτ]
    have h : (1 + B / τ) * τ = τ + B := by field_simp
    rw [h]; exact hμ
  have hev : (deriv (sharpErr τ k)) =ᶠ[𝓝 μ]
      (fun x : ℝ => chebTailD1 τ k (x / τ) / τ) := by
    refine Filter.eventually_of_mem ((isOpen_lt continuous_abs continuous_const).mem_nhds hμ)
      fun x hx => ?_
    rw [Set.mem_ofPred_eq] at hx
    exact deriv_sharpErr_eq_chebTailD1 τ B hτ hB hk hε hr hdec hρ hx
  have hder := Filter.EventuallyEq.deriv_eq hev
  have hinner : HasDerivAt (fun x : ℝ => x / τ) (1 / τ) μ := by
    simpa using (hasDerivAt_id μ).div_const τ
  have houter : HasDerivAt (chebTailD1 τ k) (chebTailD2 τ k (μ / τ)) (μ / τ) :=
    hasDerivAt_chebTailD1 τ B hτ hB hk hε hr hdec hρ hBτ hu
  have hcomp := (houter.hasFDerivAt).comp_hasDerivAt μ hinner
  have hdiv : HasDerivAt (fun x : ℝ => chebTailD1 τ k (x / τ) / τ)
      (((τ⁻¹ : ℝ) : ℂ) * chebTailD2 τ k (μ / τ) / τ) μ := by
    have hd := hcomp.div_const τ
    rw [ContinuousLinearMap.toSpanSingleton_apply, Complex.real_smul] at hd
    simpa [Function.comp_def] using hd
  rw [hdiv.deriv] at hder
  rw [Complex.ofReal_inv] at hder
  rw [hder]
  simp only [div_eq_mul_inv]
  rw [show (((τ : ℝ) : ℂ) ^ 2)⁻¹ = ((τ : ℝ) : ℂ)⁻¹ * ((τ : ℝ) : ℂ)⁻¹ by rw [sq, mul_inv]]
  ring

/-- **collar 上的值界**：`‖Q(τu)‖ ≤ 3εe^{kg}`。 -/
lemma norm_chebTail_le (τ B : ℝ) (hτ : 0 < τ) (hB : 0 < B) {k : ℕ}
    {ε r : ℝ} (hε : 0 ≤ ε) (hr : 0 ≤ r)
    (hdec : ∀ j : ℕ, ‖fcoef τ (((k + j : ℕ)) : ℤ)‖ ≤ ε * r ^ j)
    (hρ : r * Real.exp (2 * Real.sqrt (B / τ)) ≤ 1 / 32)
    {u : ℝ} (hu : |u| ≤ 1 + B / τ) :
    ‖chebTail τ k u‖ ≤ 3 * Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ))) * ε := by
  set g : ℝ := 2 * Real.sqrt (B / τ) with hg
  set ρ : ℝ := r * Real.exp g with hρdef
  have hρ0 : 0 ≤ ρ := by rw [hρdef]; positivity
  have hρ1 : ρ < 1 := lt_of_le_of_lt hρ (by norm_num)
  have hpt : ∀ j : ℕ, ‖2 * fcoef τ (((k + j : ℕ)) : ℤ)
        * ((((Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).eval u : ℝ)) : ℂ)‖
      ≤ 2 * ε * Real.exp ((k : ℝ) * g) * ρ ^ j := by
    intro j
    have h := norm_chebTail_term_le (k := k) (j := j) τ B hτ hB hε hr hdec hu
    have h2 : (r * Real.exp (2 * Real.sqrt (B / τ))) ^ j = ρ ^ j := by rw [hρdef, hg]
    rw [← hg, h2] at h
    exact h
  have hmaj : Summable (fun j : ℕ => 2 * ε * Real.exp ((k : ℝ) * g) * ρ ^ j) :=
    (summable_geometric_of_lt_one hρ0 hρ1).mul_left _
  have hs : Summable (fun j : ℕ => ‖2 * fcoef τ (((k + j : ℕ)) : ℤ)
        * ((((Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).eval u : ℝ)) : ℂ)‖) :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _) hpt hmaj
  calc ‖chebTail τ k u‖
      ≤ ∑' j : ℕ, ‖2 * fcoef τ (((k + j : ℕ)) : ℤ)
          * ((((Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).eval u : ℝ)) : ℂ)‖ :=
        norm_tsum_le_tsum_norm hs
    _ ≤ ∑' j : ℕ, 2 * ε * Real.exp ((k : ℝ) * g) * ρ ^ j := Summable.tsum_le_tsum hpt hs hmaj
    _ = 2 * ε * Real.exp ((k : ℝ) * g) * (1 - ρ)⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hρ0 hρ1]
    _ ≤ 3 * Real.exp ((k : ℝ) * g) * ε := by
        have h2 : (1 - ρ)⁻¹ ≤ 3 / 2 := by
          rw [inv_le_comm₀ (by linarith : (0 : ℝ) < 1 - ρ) (by norm_num : (0 : ℝ) < 3 / 2)]
          norm_num
          linarith
        have h3 : (0 : ℝ) ≤ ε * Real.exp ((k : ℝ) * g) := by positivity
        nlinarith [h2, h3]

/-- **闭 collar 上的一阶导界（`ε`-线性）**：`‖Q' μ‖ ≤ 7k²ε/τ`。 -/
theorem norm_deriv_sharpErr_le (τ B : ℝ) (hτ : 0 < τ) (hB : 0 < B) {k : ℕ} (hk : 1 ≤ k)
    {ε r : ℝ} (hε : 0 ≤ ε) (hr : 0 ≤ r)
    (hdec : ∀ j : ℕ, ‖fcoef τ (((k + j : ℕ)) : ℤ)‖ ≤ ε * r ^ j)
    (hρ : r * Real.exp (2 * Real.sqrt (B / τ)) ≤ 1 / 32)
    (hkB : (k : ℝ) * (2 * Real.sqrt (B / τ)) ≤ 1) :
    ∀ μ : ℝ, |μ| ≤ τ + B → ‖deriv (sharpErr τ k) μ‖ ≤ 7 * ((k : ℝ) ^ 2 / τ) * ε := by
  intro μ hμ
  set C : ℝ := 7 * ((k : ℝ) ^ 2 / τ) * ε with hC
  have hsub : Set.Ioo (-(τ + B)) (τ + B) ⊆ {x : ℝ | ‖deriv (sharpErr τ k) x‖ ≤ C} := by
    intro x hx
    rw [Set.mem_Ioo] at hx
    rw [Set.mem_setOf_eq]
    have hx' : |x| < τ + B := abs_lt.mpr hx
    rw [deriv_sharpErr_eq_chebTailD1 τ B hτ hB hk hε hr hdec hρ hx', norm_div,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ]
    have hxτ : |x / τ| ≤ 1 + B / τ := by
      rw [abs_div, abs_of_pos hτ, div_le_iff₀ hτ]
      have h : (1 + B / τ) * τ = τ + B := by field_simp
      rw [h]; exact le_of_lt hx'
    have h2 := norm_chebTailD1_le τ B hτ hB hk hε hr hdec hρ hxτ
    have hexp3 : Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ))) ≤ 3 := by
      have h1 : Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ))) ≤ Real.exp 1 :=
        Real.exp_le_exp.mpr hkB
      have h2 : Real.exp 1 ≤ 3 := le_of_lt Real.exp_one_lt_three
      linarith
    have hstep : (16 / 7) * Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ))) * (k : ℝ) ^ 2 * ε
        ≤ 7 * ((k : ℝ) ^ 2 * ε) := by
      calc (16 / 7) * Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ))) * (k : ℝ) ^ 2 * ε
          = ((16 / 7) * Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ)))) * ((k : ℝ) ^ 2 * ε) := by
            ring
        _ ≤ 7 * ((k : ℝ) ^ 2 * ε) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            nlinarith [hexp3]
    calc ‖chebTailD1 τ k (x / τ)‖ / τ
        ≤ ((16 / 7) * Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ))) * (k : ℝ) ^ 2 * ε) / τ :=
          div_le_div_of_nonneg_right h2 hτ.le
      _ ≤ (7 * ((k : ℝ) ^ 2 * ε)) / τ := div_le_div_of_nonneg_right hstep hτ.le
      _ = C := by rw [hC]; ring
  have hcl : IsClosed {x : ℝ | ‖deriv (sharpErr τ k) x‖ ≤ C} :=
    isClosed_le (continuous_norm.comp (continuous_deriv_sharpErr τ k)) continuous_const
  have hclosure : closure (Set.Ioo (-(τ + B)) (τ + B)) = Set.Icc (-(τ + B)) (τ + B) :=
    closure_Ioo (by linarith : -(τ + B) ≠ τ + B)
  have hIcc : μ ∈ Set.Icc (-(τ + B)) (τ + B) := by
    rw [Set.mem_Icc]; exact abs_le.mp hμ
  exact hcl.closure_subset_iff.mpr hsub (by rw [hclosure]; exact hIcc)

/-- **闭 collar 上的二阶导界（`ε`-线性）**：`‖Q'' μ‖ ≤ 384k⁴ε/τ²`。 -/
theorem norm_deriv2_sharpErr_le (τ B : ℝ) (hτ : 0 < τ) (hB : 0 < B) {k : ℕ} (hk : 1 ≤ k)
    {ε r : ℝ} (hε : 0 ≤ ε) (hr : 0 ≤ r)
    (hdec : ∀ j : ℕ, ‖fcoef τ (((k + j : ℕ)) : ℤ)‖ ≤ ε * r ^ j)
    (hρ : r * Real.exp (2 * Real.sqrt (B / τ)) ≤ 1 / 32) (hBτ : B / τ ≤ 1 / 2)
    (hkB : (k : ℝ) * (2 * Real.sqrt (B / τ)) ≤ 1) :
    ∀ μ : ℝ, |μ| ≤ τ + B → ‖deriv (deriv (sharpErr τ k)) μ‖ ≤ 384 * ((k : ℝ) ^ 4 / τ ^ 2) * ε := by
  intro μ hμ
  set C : ℝ := 384 * ((k : ℝ) ^ 4 / τ ^ 2) * ε with hC
  have hsub : Set.Ioo (-(τ + B)) (τ + B) ⊆ {x : ℝ | ‖deriv (deriv (sharpErr τ k)) x‖ ≤ C} := by
    intro x hx
    rw [Set.mem_Ioo] at hx
    rw [Set.mem_setOf_eq]
    have hx' : |x| < τ + B := abs_lt.mpr hx
    rw [deriv2_sharpErr_eq_chebTailD2 τ B hτ hB hk hε hr hdec hρ hBτ hx', norm_div,
      norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ]
    have hxτ : |x / τ| ≤ 1 + B / τ := by
      rw [abs_div, abs_of_pos hτ, div_le_iff₀ hτ]
      have h : (1 + B / τ) * τ = τ + B := by field_simp
      rw [h]; exact le_of_lt hx'
    have h2 := norm_chebTailD2_le τ B hτ hB hk hε hr hdec hρ hBτ hxτ
    have hexp3 : Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ))) ≤ 3 := by
      have h1 : Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ))) ≤ Real.exp 1 :=
        Real.exp_le_exp.mpr hkB
      have h2 : Real.exp 1 ≤ 3 := le_of_lt Real.exp_one_lt_three
      linarith
    have hstep : 128 * Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ))) * (k : ℝ) ^ 4 * ε
        ≤ 384 * ((k : ℝ) ^ 4 * ε) := by
      calc 128 * Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ))) * (k : ℝ) ^ 4 * ε
          = (128 * Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ)))) * ((k : ℝ) ^ 4 * ε) := by ring
        _ ≤ 384 * ((k : ℝ) ^ 4 * ε) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            nlinarith [hexp3]
    calc ‖chebTailD2 τ k (x / τ)‖ / τ ^ 2
        ≤ (128 * Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ))) * (k : ℝ) ^ 4 * ε) / τ ^ 2 :=
          div_le_div_of_nonneg_right h2 (by positivity)
      _ ≤ (384 * ((k : ℝ) ^ 4 * ε)) / τ ^ 2 := div_le_div_of_nonneg_right hstep (by positivity)
      _ = C := by rw [hC]; ring
  have hcl : IsClosed {x : ℝ | ‖deriv (deriv (sharpErr τ k)) x‖ ≤ C} :=
    isClosed_le (continuous_norm.comp (continuous_deriv2_sharpErr τ k)) continuous_const
  have hclosure : closure (Set.Ioo (-(τ + B)) (τ + B)) = Set.Icc (-(τ + B)) (τ + B) :=
    closure_Ioo (by linarith : -(τ + B) ≠ τ + B)
  have hIcc : μ ∈ Set.Icc (-(τ + B)) (τ + B) := by
    rw [Set.mem_Icc]; exact abs_le.mp hμ
  exact hcl.closure_subset_iff.mpr hsub (by rw [hclosure]; exact hIcc)

/-! ### 5.5 `ε` 更松时的 `k²/τ²` 变体 与 `psiA` 推论 -/

/-- **二阶导的 `k²/τ²` 变体**：若几何衰减锚定在 `C`（`‖c_{k+j}‖ ≤ C r^j`）且 `k²C ≤ ε`，
则 `‖Q'' μ‖ ≤ 384·k²ε/τ²`（比 `norm_deriv2_sharpErr_le` 强 `k²` 倍）。 -/
theorem norm_deriv2_sharpErr_le_sq (τ B : ℝ) (hτ : 0 < τ) (hB : 0 < B) {k : ℕ} (hk : 1 ≤ k)
    {ε r C : ℝ} (hε : 0 ≤ ε) (hr : 0 ≤ r) (hC : 0 ≤ C)
    (hdec : ∀ j : ℕ, ‖fcoef τ (((k + j : ℕ)) : ℤ)‖ ≤ C * r ^ j)
    (hCk : (k : ℝ) ^ 2 * C ≤ ε)
    (hρ : r * Real.exp (2 * Real.sqrt (B / τ)) ≤ 1 / 32) (hBτ : B / τ ≤ 1 / 2)
    (hkB : (k : ℝ) * (2 * Real.sqrt (B / τ)) ≤ 1) :
    ∀ μ : ℝ, |μ| ≤ τ + B → ‖deriv (deriv (sharpErr τ k)) μ‖ ≤ 384 * ((k : ℝ) ^ 2 / τ ^ 2) * ε := by
  have hmain := norm_deriv2_sharpErr_le τ B hτ hB hk hC hr hdec hρ hBτ hkB
  intro μ hμ
  refine (hmain μ hμ).trans ?_
  rw [show 384 * ((k : ℝ) ^ 4 / τ ^ 2) * C = 384 * ((k : ℝ) ^ 2 / τ ^ 2) * ((k : ℝ) ^ 2 * C) by
    ring]
  exact mul_le_mul_of_nonneg_left hCk (by positivity)

/-- **一阶导的 `k/τ` 变体**（同样的锚定假设）：`‖Q' μ‖ ≤ 7·kε/τ`。 -/
theorem norm_deriv_sharpErr_le_sq (τ B : ℝ) (hτ : 0 < τ) (hB : 0 < B) {k : ℕ} (hk : 1 ≤ k)
    {ε r C : ℝ} (hε : 0 ≤ ε) (hr : 0 ≤ r) (hC : 0 ≤ C)
    (hdec : ∀ j : ℕ, ‖fcoef τ (((k + j : ℕ)) : ℤ)‖ ≤ C * r ^ j)
    (hCk : (k : ℝ) ^ 2 * C ≤ ε)
    (hρ : r * Real.exp (2 * Real.sqrt (B / τ)) ≤ 1 / 32)
    (hkB : (k : ℝ) * (2 * Real.sqrt (B / τ)) ≤ 1) :
    ∀ μ : ℝ, |μ| ≤ τ + B → ‖deriv (sharpErr τ k) μ‖ ≤ 7 * ((k : ℝ) / τ) * ε := by
  have hmain := norm_deriv_sharpErr_le τ B hτ hB hk hC hr hdec hρ hkB
  intro μ hμ
  refine (hmain μ hμ).trans ?_
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk2 : (0 : ℝ) < (k : ℝ) := by linarith
  calc 7 * ((k : ℝ) ^ 2 / τ) * C = 7 * ((k : ℝ) / τ) * ((k : ℝ) * C) := by
        field_simp
    _ ≤ 7 * ((k : ℝ) / τ) * ε := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        calc (k : ℝ) * C = (k : ℝ) * C * 1 := by ring
          _ ≤ (k : ℝ) * C * (k : ℝ) :=
              mul_le_mul_of_nonneg_left hk1 (by positivity)
          _ = (k : ℝ) ^ 2 * C := by ring
          _ ≤ ε := hCk

/-- `‖e^{iμ}‖ = 1`。 -/
lemma norm_exp_mul_I (μ : ℝ) : ‖Complex.exp ((μ : ℂ) * Complex.I)‖ = 1 := by
  rw [Complex.norm_exp]
  have h : (((μ : ℂ) * Complex.I)).re = 0 := by simp [Complex.mul_re]
  rw [h, Real.exp_zero]

/-- **collar 上 `Q` 的值界（`|μ| ≤ τ+B` 形式）**。 -/
lemma norm_sharpErr_collar_le (τ B : ℝ) (hτ : 0 < τ) (hB : 0 < B) {k : ℕ} (hk : 1 ≤ k)
    {ε r : ℝ} (hε : 0 ≤ ε) (hr : 0 ≤ r)
    (hdec : ∀ j : ℕ, ‖fcoef τ (((k + j : ℕ)) : ℤ)‖ ≤ ε * r ^ j)
    (hρ : r * Real.exp (2 * Real.sqrt (B / τ)) ≤ 1 / 32)
    {μ : ℝ} (hμ : |μ| ≤ τ + B) :
    ‖sharpErr τ k μ‖ ≤ 3 * Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ))) * ε := by
  have hu : |μ / τ| ≤ 1 + B / τ := by
    rw [abs_div, abs_of_pos hτ, div_le_iff₀ hτ]
    have h : (1 + B / τ) * τ = τ + B := by field_simp
    rw [h]; exact hμ
  have h := norm_chebTail_le τ B hτ hB hε hr hdec hρ hu
  rw [chebTail_eq_sharpErr_collar_all τ hτ hk B hu] at h
  rwa [show τ * (μ / τ) = μ by field_simp] at h

/-- `dpsiA (scaledApprox τ k) μ` 用 `Q` 表示：`e^{iμ}Q'(μ) + i e^{iμ}Q(μ)`。 -/
lemma dpsiA_scaledApprox_eq (τ : ℝ) (k : ℕ) (μ : ℝ) :
    dpsiA (scaledApprox τ k) μ
      = Complex.exp ((μ : ℂ) * Complex.I) * deriv (sharpErr τ k) μ
        + Complex.exp ((μ : ℂ) * Complex.I) * Complex.I * sharpErr τ k μ := by
  have hP' : (scaledApprox τ k).derivative.eval ((μ : ℂ))
      = -Complex.I * Complex.exp (-(μ : ℂ) * Complex.I) - deriv (sharpErr τ k) μ := by
    rw [deriv_sharpErr_eq]; ring
  have hP : (scaledApprox τ k).eval ((μ : ℂ))
      = Complex.exp (-(μ : ℂ) * Complex.I) - sharpErr τ k μ := by
    rw [sharpErr_def]; ring
  rw [dpsiA, hP', hP]
  ring

/-- **`ψ_A` 一阶导的 sharp collar 界**：`‖(ψ_A)'‖ ≤ (7k²/τ + 9)ε`。 -/
theorem norm_deriv_psiA_scaled_collar_sharp (τ B : ℝ) (hτ : 0 < τ) (hB : 0 < B) {k : ℕ}
    (hk : 1 ≤ k) {ε r : ℝ} (hε : 0 ≤ ε) (hr : 0 ≤ r)
    (hdec : ∀ j : ℕ, ‖fcoef τ (((k + j : ℕ)) : ℤ)‖ ≤ ε * r ^ j)
    (hρ : r * Real.exp (2 * Real.sqrt (B / τ)) ≤ 1 / 32)
    (hkB : (k : ℝ) * (2 * Real.sqrt (B / τ)) ≤ 1) :
    ∀ μ : ℝ, |μ| ≤ τ + B →
      ‖deriv (fun x : ℝ => psiA (scaledApprox τ k) x) μ‖
        ≤ (7 * ((k : ℝ) ^ 2 / τ) + 9) * ε := by
  intro μ hμ
  rw [deriv_psiA, dpsiA_scaledApprox_eq]
  have h1 := norm_deriv_sharpErr_le τ B hτ hB hk hε hr hdec hρ hkB μ hμ
  have h2 := norm_sharpErr_collar_le τ B hτ hB hk hε hr hdec hρ hμ
  have h3 : Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ))) ≤ 3 := by
    have h1 : Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ))) ≤ Real.exp 1 :=
      Real.exp_le_exp.mpr hkB
    exact h1.trans (le_of_lt Real.exp_one_lt_three)
  have h4 : ‖sharpErr τ k μ‖ ≤ 9 * ε := by
    refine h2.trans ?_
    nlinarith [h3, hε]
  have h5 : ‖Complex.exp ((μ : ℂ) * Complex.I) * Complex.I * sharpErr τ k μ‖ ≤ 9 * ε := by
    rw [norm_mul, norm_mul, norm_exp_mul_I, Complex.norm_I, one_mul, one_mul]
    exact h4
  have h6 : ‖Complex.exp ((μ : ℂ) * Complex.I) * deriv (sharpErr τ k) μ‖
      ≤ 7 * ((k : ℝ) ^ 2 / τ) * ε := by
    rw [norm_mul, norm_exp_mul_I, one_mul]
    exact h1
  calc ‖Complex.exp ((μ : ℂ) * Complex.I) * deriv (sharpErr τ k) μ
        + Complex.exp ((μ : ℂ) * Complex.I) * Complex.I * sharpErr τ k μ‖
      ≤ ‖Complex.exp ((μ : ℂ) * Complex.I) * deriv (sharpErr τ k) μ‖
        + ‖Complex.exp ((μ : ℂ) * Complex.I) * Complex.I * sharpErr τ k μ‖ := norm_add_le _ _
    _ ≤ 7 * ((k : ℝ) ^ 2 / τ) * ε + 9 * ε := add_le_add h6 h5
    _ = (7 * ((k : ℝ) ^ 2 / τ) + 9) * ε := by ring

/-- `Q''` 的显式表达式（`Q = e^{-iμ} - P`）。 -/
lemma deriv2_sharpErr_eq_formula (τ : ℝ) (k : ℕ) (μ : ℝ) :
    deriv (deriv (sharpErr τ k)) μ
      = -Complex.exp (-(μ : ℂ) * Complex.I)
        - (scaledApprox τ k).derivative.derivative.eval ((μ : ℝ) : ℂ) := by
  rw [show deriv (sharpErr τ k) = fun x : ℝ => -Complex.I * Complex.exp (-(x : ℂ) * Complex.I)
      - (scaledApprox τ k).derivative.eval ((x : ℝ) : ℂ) from
    funext fun x => deriv_sharpErr_eq τ k x]
  have h1 : HasDerivAt (fun x : ℝ => -Complex.I * Complex.exp (-(x : ℂ) * Complex.I))
      (-Complex.I * (-Complex.I * Complex.exp (-(μ : ℂ) * Complex.I))) μ :=
    (hasDerivAt_exp_neg_I μ).const_mul (-Complex.I)
  have h2 : HasDerivAt (fun x : ℝ => (scaledApprox τ k).derivative.eval ((x : ℝ) : ℂ))
      ((scaledApprox τ k).derivative.derivative.eval ((μ : ℝ) : ℂ)) μ :=
    hasDerivAt_poly_eval_real (scaledApprox τ k).derivative μ
  have h3 := h1.sub h2
  refine h3.deriv.trans ?_
  ring_nf
  rw [show Complex.I ^ 2 = -1 by rw [sq, Complex.I_mul_I]]
  ring

/-- `deriv (dpsiA (scaledApprox τ k))` 的显式表达式。 -/
lemma deriv_dpsiA_eq (τ : ℝ) (k : ℕ) (μ : ℝ) :
    deriv (dpsiA (scaledApprox τ k)) μ
      = -((scaledApprox τ k).derivative.derivative.eval ((μ : ℂ))
            * Complex.exp ((μ : ℂ) * Complex.I)
          + 2 * ((scaledApprox τ k).derivative.eval ((μ : ℂ))
            * (Complex.exp ((μ : ℂ) * Complex.I) * Complex.I))
          + (scaledApprox τ k).eval ((μ : ℂ)) * (-Complex.exp ((μ : ℂ) * Complex.I))) := by
  rw [show dpsiA (scaledApprox τ k) = fun x : ℝ =>
      -((scaledApprox τ k).derivative.eval ((x : ℂ)) * Complex.exp ((x : ℂ) * Complex.I)
        + (scaledApprox τ k).eval ((x : ℂ))
          * (Complex.exp ((x : ℂ) * Complex.I) * Complex.I)) from rfl]
  have h1 : HasDerivAt (fun x : ℝ => (scaledApprox τ k).derivative.eval ((x : ℂ))
      * Complex.exp ((x : ℂ) * Complex.I))
      ((scaledApprox τ k).derivative.derivative.eval ((μ : ℂ)) * Complex.exp ((μ : ℂ) * Complex.I)
        + (scaledApprox τ k).derivative.eval ((μ : ℂ))
          * (Complex.exp ((μ : ℂ) * Complex.I) * Complex.I)) μ :=
    (hasDerivAt_poly_eval_real (scaledApprox τ k).derivative μ).mul (hasDerivAt_exp_mul_I μ)
  have h2 : HasDerivAt (fun x : ℝ => (scaledApprox τ k).eval ((x : ℂ))
      * (Complex.exp ((x : ℂ) * Complex.I) * Complex.I))
      ((scaledApprox τ k).derivative.eval ((μ : ℂ))
        * (Complex.exp ((μ : ℂ) * Complex.I) * Complex.I)
        + (scaledApprox τ k).eval ((μ : ℂ))
          * ((Complex.exp ((μ : ℂ) * Complex.I) * Complex.I) * Complex.I)) μ :=
    (hasDerivAt_poly_eval_real (scaledApprox τ k) μ).mul
      ((hasDerivAt_exp_mul_I μ).mul_const Complex.I)
  have h3 := (h1.add h2).neg
  refine h3.deriv.trans ?_
  ring_nf
  rw [show Complex.I ^ 2 = -1 by rw [sq, Complex.I_mul_I]]
  ring

/-- `deriv (deriv (psiA (scaledApprox τ k)))` 用 `Q` 表示。 -/
lemma deriv2_psiA_scaledApprox_eq (τ : ℝ) (k : ℕ) (μ : ℝ) :
    deriv (deriv (fun x : ℝ => psiA (scaledApprox τ k) x)) μ
      = Complex.exp ((μ : ℂ) * Complex.I) * deriv (deriv (sharpErr τ k)) μ
        + 2 * (Complex.exp ((μ : ℂ) * Complex.I) * Complex.I * deriv (sharpErr τ k) μ)
        - Complex.exp ((μ : ℂ) * Complex.I) * sharpErr τ k μ := by
  rw [deriv_psiA, deriv_dpsiA_eq]
  have hP'' : (scaledApprox τ k).derivative.derivative.eval ((μ : ℂ))
      = -Complex.exp (-(μ : ℂ) * Complex.I) - deriv (deriv (sharpErr τ k)) μ := by
    rw [deriv2_sharpErr_eq_formula]; ring
  have hP' : (scaledApprox τ k).derivative.eval ((μ : ℂ))
      = -Complex.I * Complex.exp (-(μ : ℂ) * Complex.I) - deriv (sharpErr τ k) μ := by
    rw [deriv_sharpErr_eq]; ring
  have hP : (scaledApprox τ k).eval ((μ : ℂ))
      = Complex.exp (-(μ : ℂ) * Complex.I) - sharpErr τ k μ := by
    rw [sharpErr_def]; ring
  rw [hP'', hP', hP]
  ring_nf
  rw [show Complex.I ^ 2 = -1 by rw [sq, Complex.I_mul_I]]
  ring

/-- **`ψ_A` 二阶导的 sharp collar 界**：`‖(ψ_A)''‖ ≤ (384k⁴/τ² + 14k²/τ + 9)ε`。 -/
theorem norm_deriv2_psiA_scaled_collar_sharp (τ B : ℝ) (hτ : 0 < τ) (hB : 0 < B) {k : ℕ}
    (hk : 1 ≤ k) {ε r : ℝ} (hε : 0 ≤ ε) (hr : 0 ≤ r)
    (hdec : ∀ j : ℕ, ‖fcoef τ (((k + j : ℕ)) : ℤ)‖ ≤ ε * r ^ j)
    (hρ : r * Real.exp (2 * Real.sqrt (B / τ)) ≤ 1 / 32) (hBτ : B / τ ≤ 1 / 2)
    (hkB : (k : ℝ) * (2 * Real.sqrt (B / τ)) ≤ 1) :
    ∀ μ : ℝ, |μ| ≤ τ + B →
      ‖deriv (deriv (fun x : ℝ => psiA (scaledApprox τ k) x)) μ‖
        ≤ (384 * ((k : ℝ) ^ 4 / τ ^ 2) + 14 * ((k : ℝ) ^ 2 / τ) + 9) * ε := by
  intro μ hμ
  rw [deriv2_psiA_scaledApprox_eq]
  have h1 := norm_deriv2_sharpErr_le τ B hτ hB hk hε hr hdec hρ hBτ hkB μ hμ
  have h2 := norm_deriv_sharpErr_le τ B hτ hB hk hε hr hdec hρ hkB μ hμ
  have h3 := norm_sharpErr_collar_le τ B hτ hB hk hε hr hdec hρ hμ
  have hexp3 : Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ))) ≤ 3 := by
    have h1 : Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ))) ≤ Real.exp 1 :=
      Real.exp_le_exp.mpr hkB
    exact h1.trans (le_of_lt Real.exp_one_lt_three)
  have h4 : ‖sharpErr τ k μ‖ ≤ 9 * ε := by
    refine h3.trans ?_
    nlinarith [hexp3, hε]
  have h5 : ‖Complex.exp ((μ : ℂ) * Complex.I) * deriv (deriv (sharpErr τ k)) μ‖
      ≤ 384 * ((k : ℝ) ^ 4 / τ ^ 2) * ε := by
    rw [norm_mul, norm_exp_mul_I, one_mul]; exact h1
  have h6 : ‖2 * (Complex.exp ((μ : ℂ) * Complex.I) * Complex.I * deriv (sharpErr τ k) μ)‖
      ≤ 14 * ((k : ℝ) ^ 2 / τ) * ε := by
    rw [norm_mul, norm_mul, norm_mul, norm_exp_mul_I, Complex.norm_I, Complex.norm_ofNat,
      one_mul, one_mul]
    have := h2
    nlinarith [h2, hε]
  have h7 : ‖Complex.exp ((μ : ℂ) * Complex.I) * sharpErr τ k μ‖ ≤ 9 * ε := by
    rw [norm_mul, norm_exp_mul_I, one_mul]; exact h4
  calc ‖Complex.exp ((μ : ℂ) * Complex.I) * deriv (deriv (sharpErr τ k)) μ
        + 2 * (Complex.exp ((μ : ℂ) * Complex.I) * Complex.I * deriv (sharpErr τ k) μ)
        - Complex.exp ((μ : ℂ) * Complex.I) * sharpErr τ k μ‖
      ≤ ‖Complex.exp ((μ : ℂ) * Complex.I) * deriv (deriv (sharpErr τ k)) μ
          + 2 * (Complex.exp ((μ : ℂ) * Complex.I) * Complex.I * deriv (sharpErr τ k) μ)‖
        + ‖Complex.exp ((μ : ℂ) * Complex.I) * sharpErr τ k μ‖ := norm_sub_le _ _
    _ ≤ (‖Complex.exp ((μ : ℂ) * Complex.I) * deriv (deriv (sharpErr τ k)) μ‖
          + ‖2 * (Complex.exp ((μ : ℂ) * Complex.I) * Complex.I * deriv (sharpErr τ k) μ)‖)
        + ‖Complex.exp ((μ : ℂ) * Complex.I) * sharpErr τ k μ‖ := by
        have := norm_add_le (Complex.exp ((μ : ℂ) * Complex.I) * deriv (deriv (sharpErr τ k)) μ)
          (2 * (Complex.exp ((μ : ℂ) * Complex.I) * Complex.I * deriv (sharpErr τ k) μ))
        linarith
    _ ≤ (384 * ((k : ℝ) ^ 4 / τ ^ 2) * ε + 14 * ((k : ℝ) ^ 2 / τ) * ε) + 9 * ε := by
        linarith [h5, h6, h7]
    _ = (384 * ((k : ℝ) ^ 4 / τ ^ 2) + 14 * ((k : ℝ) ^ 2 / τ) + 9) * ε := by ring

/-- **装配形状（一阶导）**：`τ·M₁ ≤ 16·k·ε`（`M₁ = sup_{|μ|≤τ+B}‖(ψ_A)'‖`）。

假设：`‖c_{k+j}‖ ≤ C r^j`、`k²C ≤ ε`、`ρ = r·e^{2√(B/τ)} ≤ 1/32`、`k·2√(B/τ) ≤ 1`、`τ ≤ k`。 -/
theorem tau_mul_norm_deriv_psiA_le (τ B : ℝ) (hτ : 0 < τ) (hB : 0 < B) {k : ℕ} (hk : 1 ≤ k)
    {ε r C : ℝ} (hε : 0 ≤ ε) (hr : 0 ≤ r) (hC : 0 ≤ C)
    (hdec : ∀ j : ℕ, ‖fcoef τ (((k + j : ℕ)) : ℤ)‖ ≤ C * r ^ j)
    (hCk : (k : ℝ) ^ 2 * C ≤ ε)
    (hρ : r * Real.exp (2 * Real.sqrt (B / τ)) ≤ 1 / 32)
    (hkB : (k : ℝ) * (2 * Real.sqrt (B / τ)) ≤ 1) (hτk : τ ≤ (k : ℝ)) :
    ∀ μ : ℝ, |μ| ≤ τ + B →
      τ * ‖deriv (fun x : ℝ => psiA (scaledApprox τ k) x) μ‖ ≤ 16 * (k : ℝ) * ε := by
  have hmain := norm_deriv_psiA_scaled_collar_sharp τ B hτ hB hk hC hr hdec hρ hkB
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkn : (0 : ℝ) ≤ (k : ℝ) := by linarith
  have hkC : (k : ℝ) * C ≤ ε := by
    calc (k : ℝ) * C = (k : ℝ) * C * 1 := by ring
      _ ≤ (k : ℝ) * C * (k : ℝ) := mul_le_mul_of_nonneg_left hk1 (by positivity)
      _ = (k : ℝ) ^ 2 * C := by ring
      _ ≤ ε := hCk
  intro μ hμ
  have h1 := hmain μ hμ
  have h2 : τ * ((7 * ((k : ℝ) ^ 2 / τ) + 9) * C) = (7 * (k : ℝ) ^ 2 + 9 * τ) * C := by
    field_simp
  calc τ * ‖deriv (fun x : ℝ => psiA (scaledApprox τ k) x) μ‖
      ≤ τ * ((7 * ((k : ℝ) ^ 2 / τ) + 9) * C) := mul_le_mul_of_nonneg_left h1 hτ.le
    _ = (7 * (k : ℝ) ^ 2 + 9 * τ) * C := h2
    _ ≤ 16 * (k : ℝ) * ε := by
        have h3 : 7 * (k : ℝ) ^ 2 * C ≤ 7 * ((k : ℝ) * ε) := by
          rw [show (7 : ℝ) * (k : ℝ) ^ 2 * C = (7 * (k : ℝ)) * ((k : ℝ) * C) by ring]
          rw [show (7 : ℝ) * ((k : ℝ) * ε) = (7 * (k : ℝ)) * ε by ring]
          exact mul_le_mul_of_nonneg_left hkC (by positivity)
        have h4 : 9 * τ * C ≤ 9 * ((k : ℝ) * ε) := by
          have hτε : τ * C ≤ (k : ℝ) * ε :=
            ((mul_le_mul_of_nonneg_right hτk hC).trans hkC).trans
              (by calc ε = ε * 1 := by ring
                    _ ≤ ε * (k : ℝ) := mul_le_mul_of_nonneg_left hk1 hε
                    _ = (k : ℝ) * ε := by ring)
          rw [show (9 : ℝ) * τ * C = 9 * (τ * C) by ring]
          exact mul_le_mul_of_nonneg_left hτε (by norm_num)
        rw [show (7 * (k : ℝ) ^ 2 + 9 * τ) * C = 7 * (k : ℝ) ^ 2 * C + 9 * τ * C by ring]
        linarith [h3, h4]

/-- **装配形状（二阶导）**：`τ²·M₂ ≤ 512·k²·ε`。 -/
theorem tau_sq_mul_norm_deriv2_psiA_le (τ B : ℝ) (hτ : 0 < τ) (hB : 0 < B) {k : ℕ} (hk : 1 ≤ k)
    {ε r C : ℝ} (hε : 0 ≤ ε) (hr : 0 ≤ r) (hC : 0 ≤ C)
    (hdec : ∀ j : ℕ, ‖fcoef τ (((k + j : ℕ)) : ℤ)‖ ≤ C * r ^ j)
    (hCk : (k : ℝ) ^ 2 * C ≤ ε)
    (hρ : r * Real.exp (2 * Real.sqrt (B / τ)) ≤ 1 / 32) (hBτ : B / τ ≤ 1 / 2)
    (hkB : (k : ℝ) * (2 * Real.sqrt (B / τ)) ≤ 1) (hτk : τ ≤ (k : ℝ)) :
    ∀ μ : ℝ, |μ| ≤ τ + B →
      τ ^ 2 * ‖deriv (deriv (fun x : ℝ => psiA (scaledApprox τ k) x)) μ‖
        ≤ 512 * (k : ℝ) ^ 2 * ε := by
  have hmain := norm_deriv2_psiA_scaled_collar_sharp τ B hτ hB hk hC hr hdec hρ hBτ hkB
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkn : (0 : ℝ) ≤ (k : ℝ) := by linarith
  have hk2 : (0 : ℝ) ≤ (k : ℝ) ^ 2 := by positivity
  intro μ hμ
  have h1 := hmain μ hμ
  have h2 : τ ^ 2 * ((384 * ((k : ℝ) ^ 4 / τ ^ 2) + 14 * ((k : ℝ) ^ 2 / τ) + 9) * C)
      = (384 * (k : ℝ) ^ 4 + 14 * ((k : ℝ) ^ 2 * τ) + 9 * τ ^ 2) * C := by
    field_simp
  calc τ ^ 2 * ‖deriv (deriv (fun x : ℝ => psiA (scaledApprox τ k) x)) μ‖
      ≤ τ ^ 2 * ((384 * ((k : ℝ) ^ 4 / τ ^ 2) + 14 * ((k : ℝ) ^ 2 / τ) + 9) * C) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = (384 * (k : ℝ) ^ 4 + 14 * ((k : ℝ) ^ 2 * τ) + 9 * τ ^ 2) * C := h2
    _ ≤ 512 * (k : ℝ) ^ 2 * ε := by
        have hk2C : (k : ℝ) ^ 2 * C ≤ ε := hCk
        have hkC1 : (k : ℝ) * C ≤ ε := by
          calc (k : ℝ) * C = (k : ℝ) * C * 1 := by ring
            _ ≤ (k : ℝ) * C * (k : ℝ) := mul_le_mul_of_nonneg_left hk1 (by positivity)
            _ = (k : ℝ) ^ 2 * C := by ring
            _ ≤ ε := hCk
        have h3 : 384 * (k : ℝ) ^ 4 * C ≤ 384 * ((k : ℝ) ^ 2 * ε) := by
          rw [show (384 : ℝ) * (k : ℝ) ^ 4 * C
              = (384 * (k : ℝ) ^ 2) * ((k : ℝ) ^ 2 * C) by ring]
          rw [show (384 : ℝ) * ((k : ℝ) ^ 2 * ε) = (384 * (k : ℝ) ^ 2) * ε by ring]
          exact mul_le_mul_of_nonneg_left hk2C (by positivity)
        have h4 : 14 * ((k : ℝ) ^ 2 * τ) * C ≤ 14 * ((k : ℝ) ^ 2 * ε) := by
          rw [show (14 : ℝ) * ((k : ℝ) ^ 2 * τ) * C
              = (14 * (k : ℝ) ^ 2) * (τ * C) by ring]
          rw [show (14 : ℝ) * ((k : ℝ) ^ 2 * ε) = (14 * (k : ℝ) ^ 2) * ε by ring]
          exact mul_le_mul_of_nonneg_left
            ((mul_le_mul_of_nonneg_right hτk hC).trans hkC1) (by positivity)
        have h5 : 9 * τ ^ 2 * C ≤ 9 * ((k : ℝ) ^ 2 * ε) := by
          have h5a : τ ^ 2 * C ≤ (k : ℝ) ^ 2 * ε :=
            ((mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hτ.le hτk 2) hC).trans hCk).trans
              (by calc ε = ε * 1 := by ring
                    _ ≤ ε * (k : ℝ) ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith [hk1]) hε
                    _ = (k : ℝ) ^ 2 * ε := by ring)
          rw [show (9 : ℝ) * τ ^ 2 * C = 9 * (τ ^ 2 * C) by ring]
          exact mul_le_mul_of_nonneg_left h5a (by norm_num)
        rw [show (384 * (k : ℝ) ^ 4 + 14 * ((k : ℝ) ^ 2 * τ) + 9 * τ ^ 2) * C
            = 384 * (k : ℝ) ^ 4 * C + 14 * ((k : ℝ) ^ 2 * τ) * C + 9 * τ ^ 2 * C by ring]
        linarith [h3, h4, h5, mul_nonneg hk2 hε]

end RobustZ
