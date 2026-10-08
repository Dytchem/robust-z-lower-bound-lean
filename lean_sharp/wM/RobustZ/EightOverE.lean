import RobustZ.M5Apply
import RobustZ.ElementaryBound
import RobustZ.M5Quad
import RobustZ.CutoffExplicit
import RobustZ.SharpDerivGen
import RobustZ.FinalConv

/-!
# `RobustZ.EightOverE`：全阶 `(8/e)` 型下界（系数 4，`q!^{1/q}` 形状，无阈值）

目标（对所有 `N ≥ 1`、`0 < φ ≤ π`、任意 admissible 构造，`q = 2N+2`）：

```
4 * (q! * sin(φ/4)^4 / (C * q^4))^(1/q) ≤ cost θ          (C = 10^8)
```

机制（论文 `paper_8e`）：`h(λ) = 1 - ½Re tr(U_1ᴴU_λ)` 在 `λ=1` 处 `q = 2N+2` 阶平坦、
带宽 `τ = T/2`；平坦性允许把常数项换成任何 `deg P < q` 的多项式，代价是带内一致逼近误差
`ε`；取 `P = scaledApprox τ q`（Jacobi–Anger/Chebyshev 截断）与 `B = τ/q²` 的 taper
（`M5Quad` 的 `ε`-无关尺度），乘积界是 `ε` 的**二次式**，于是只需
`ε ≲ (eτ/(2q))^q`；Chebyshev 系数比 Taylor 系数好 `2^{q-1}` 倍，这正是 `4/e ↦ 8/e`。

本文件唯一的新分析成分：用 `δ = log(2q/τ)` 的**围道平移**（`fcoef_bound` +
`exp_sub_approxPoly_band`）给出显式带内误差界 `‖e^{-iμ} - P(μ)‖ ≤ 9 (eτ/(2q))^q`
（`|μ| ≤ τ ≤ q`），它同时给出 collar 衰减假设 `‖c_{q+j}‖ ≤ ε r^j`（`r = τ/(2q)`）。
其余全部复用既有机器（`norm_sum_le_of_moments_gen`、`kernelProd_le_poly_quad`、
`SharpDerivGen` 的一般 `ρ` collar 界、`CutoffExplicit` 的 `K₀ = 21.1`）。
-/

noncomputable section
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

open scoped Matrix Matrix.Norms.L2Operator
open Matrix Filter MeasureTheory
open scoped Topology

namespace RobustZ

/-! ## §1 Stirling 型上界 -/

/-- `1/(n+1) < log (1 + 1/n)`（`n ≥ 1`）：由 `log x < x - 1` 在 `x = n/(n+1)` 处得到。 -/
lemma one_div_succ_lt_log_one_add_inv (n : ℕ) (hn : 1 ≤ n) :
    1 / ((n : ℝ) + 1) < Real.log (1 + (n : ℝ)⁻¹) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hx : (0 : ℝ) < (n : ℝ) / ((n : ℝ) + 1) := by positivity
  have hx1 : (n : ℝ) / ((n : ℝ) + 1) ≠ 1 := by
    have hlt : (n : ℝ) / ((n : ℝ) + 1) < 1 := by
      rw [div_lt_one (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
      linarith
    exact ne_of_lt hlt
  have h := Real.log_lt_sub_one_of_pos hx hx1
  rw [Real.log_div (ne_of_gt hn0) (by positivity : ((n : ℝ) + 1) ≠ 0)] at h
  have hsub : (n : ℝ) / ((n : ℝ) + 1) - 1 = -(1 / ((n : ℝ) + 1)) := by
    field_simp
    try ring
  rw [hsub] at h
  have hlog : Real.log (1 + (n : ℝ)⁻¹) = Real.log ((n : ℝ) + 1) - Real.log (n : ℝ) := by
    have h1 : (1 + (n : ℝ)⁻¹) = ((n : ℝ) + 1) / (n : ℝ) := by
      field_simp
    rw [h1, Real.log_div (by positivity : ((n : ℝ) + 1) ≠ 0) (ne_of_gt hn0)]
  rw [hlog]
  linarith

/-- `e ≤ (1 + 1/n)^{n+1}`（`n ≥ 1`）。 -/
lemma exp_one_le_one_add_inv_pow (n : ℕ) (hn : 1 ≤ n) :
    Real.exp 1 ≤ (1 + (n : ℝ)⁻¹) ^ (n + 1) := by
  have hlog := one_div_succ_lt_log_one_add_inv n hn
  have h1 : (1 : ℝ) ≤ ((n : ℝ) + 1) * Real.log (1 + (n : ℝ)⁻¹) := by
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hlt := mul_lt_mul_of_pos_left hlog hpos
    have hL : ((n : ℝ) + 1) * (1 / ((n : ℝ) + 1)) = 1 := by
      field_simp
    rw [hL] at hlt
    linarith
  have h2 : Real.log ((1 + (n : ℝ)⁻¹) ^ (n + 1))
      = (((n + 1 : ℕ)) : ℝ) * Real.log (1 + (n : ℝ)⁻¹) := by
    rw [Real.log_pow]
  have h3 : (0 : ℝ) < (1 + (n : ℝ)⁻¹) ^ (n + 1) := by positivity
  calc Real.exp 1 ≤ Real.exp (Real.log ((1 + (n : ℝ)⁻¹) ^ (n + 1))) :=
        Real.exp_le_exp.mpr (by simpa [h2] using h1)
    _ = (1 + (n : ℝ)⁻¹) ^ (n + 1) := Real.exp_log h3

/-- `e ≤ (1 + 1/(n+1))^{n+2}`。 -/
lemma exp_one_le_one_add_inv_pow_succ (n : ℕ) :
    Real.exp 1 ≤ (1 + ((n : ℝ) + 1)⁻¹) ^ (n + 2) := by
  have h := exp_one_le_one_add_inv_pow (n + 1) (Nat.le_add_left 1 n)
  have h1 : (((n + 1 : ℕ)) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  rw [h1] at h
  have h2 : n + 1 + 1 = n + 2 := by omega
  rwa [h2] at h

/-- `(1 + 1/q)^q ≤ e`（`q ≥ 1`）。 -/
lemma one_add_inv_pow_le_exp (q : ℕ) (hq : 1 ≤ q) :
    (1 + (q : ℝ)⁻¹) ^ q ≤ Real.exp 1 := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hpos : (0 : ℝ) < 1 + (q : ℝ)⁻¹ := by positivity
  have h1 : Real.log (1 + (q : ℝ)⁻¹) ≤ (q : ℝ)⁻¹ := by
    have h := Real.log_le_sub_one_of_pos hpos
    linarith
  have h2 : (0 : ℝ) < (1 + (q : ℝ)⁻¹) ^ q := by positivity
  have h3 : Real.log ((1 + (q : ℝ)⁻¹) ^ q) = (q : ℝ) * Real.log (1 + (q : ℝ)⁻¹) := by
    rw [Real.log_pow]
  have h4 : Real.log ((1 + (q : ℝ)⁻¹) ^ q) ≤ 1 := by
    rw [h3]
    calc (q : ℝ) * Real.log (1 + (q : ℝ)⁻¹) ≤ (q : ℝ) * (q : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_left h1 hq0.le
      _ = 1 := mul_inv_cancel₀ (ne_of_gt hq0)
  calc (1 + (q : ℝ)⁻¹) ^ q = Real.exp (Real.log ((1 + (q : ℝ)⁻¹) ^ q)) :=
        (Real.exp_log h2).symm
    _ ≤ Real.exp 1 := Real.exp_le_exp.mpr h4

/-- **Stirling 型上界**：`q! · e^q ≤ (q+1)^{q+1}`（乘法归纳 + `e ≤ (1+1/n)^{n+1}`）。 -/
lemma factorial_mul_exp_le (q : ℕ) :
    (q.factorial : ℝ) * Real.exp (q : ℝ) ≤ ((q : ℝ) + 1) ^ (q + 1) := by
  induction q with
  | zero => norm_num
  | succ n ih =>
      have hexpn : Real.exp ((n : ℝ) + 1) = Real.exp (n : ℝ) * Real.exp 1 := by
        rw [Real.exp_add]
      have hstep : ((Nat.factorial (n + 1)) : ℝ) * Real.exp (((n + 1 : ℕ)) : ℝ)
          = ((n : ℝ) + 1) * ((Nat.factorial n : ℝ) * Real.exp (n : ℝ)) * Real.exp 1 := by
        rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, hexpn]
        ring
      rw [hstep]
      have hle1 : ((n : ℝ) + 1) * ((Nat.factorial n : ℝ) * Real.exp (n : ℝ)) * Real.exp 1
          ≤ ((n : ℝ) + 1) * ((n : ℝ) + 1) ^ (n + 1) * Real.exp 1 := by
        have h1 : ((Nat.factorial n : ℝ) * Real.exp (n : ℝ)) ≤ ((n : ℝ) + 1) ^ (n + 1) := ih
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left h1 (by positivity)) (Real.exp_pos 1).le
      refine hle1.trans ?_
      have heq : ((n : ℝ) + 1) * ((n : ℝ) + 1) ^ (n + 1) * Real.exp 1
          = ((n : ℝ) + 1) ^ (n + 2) * Real.exp 1 := by
        rw [pow_succ]
        ring
      rw [heq]
      have h2 : Real.exp 1 ≤ (1 + ((n : ℝ) + 1)⁻¹) ^ (n + 2) :=
        exp_one_le_one_add_inv_pow_succ n
      have h3 : ((n : ℝ) + 1) ^ (n + 2) * Real.exp 1
          ≤ ((n : ℝ) + 1) ^ (n + 2) * (1 + ((n : ℝ) + 1)⁻¹) ^ (n + 2) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
      refine h3.trans ?_
      have h4 : ((n : ℝ) + 1) ^ (n + 2) * (1 + ((n : ℝ) + 1)⁻¹) ^ (n + 2)
          = ((n : ℝ) + 2) ^ (n + 2) := by
        rw [← mul_pow]
        congr 1
        field_simp
        try ring
      have hgoal : ((↑(n + 1) : ℝ) + 1) ^ (n + 1 + 1) = ((n : ℝ) + 2) ^ (n + 2) := by
        have ha : (↑(n + 1) : ℝ) + 1 = (n : ℝ) + 2 := by push_cast; ring
        have hb : n + 1 + 1 = n + 2 := by omega
        rw [ha, hb]
      rw [hgoal]
      exact le_of_eq h4

/-- **推论 A**：`q! e^q / q^q ≤ 2 e q`（`q ≥ 1`）——多项式界（Case I 比较用）。 -/
lemma factorial_mul_exp_div_pow_le (q : ℕ) (hq : 1 ≤ q) :
    (q.factorial : ℝ) * Real.exp (q : ℝ) / (q : ℝ) ^ q ≤ 2 * Real.exp 1 * (q : ℝ) := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hmain := factorial_mul_exp_le q
  rw [div_le_iff₀ (pow_pos hq0 q)]
  refine hmain.trans ?_
  have hsplit : ((q : ℝ) + 1) ^ (q + 1) = ((q : ℝ) + 1) * ((q : ℝ) + 1) ^ q := by
    rw [pow_succ]
    ring
  rw [hsplit]
  have h2 : ((q : ℝ) + 1) ^ q ≤ Real.exp 1 * (q : ℝ) ^ q := by
    have h3 : (1 + (q : ℝ)⁻¹) ^ q ≤ Real.exp 1 := one_add_inv_pow_le_exp q hq
    have h4 : ((q : ℝ) + 1) ^ q = (q : ℝ) ^ q * (1 + (q : ℝ)⁻¹) ^ q := by
      rw [← mul_pow]
      congr 1
      field_simp
    rw [h4]
    calc (q : ℝ) ^ q * (1 + (q : ℝ)⁻¹) ^ q ≤ (q : ℝ) ^ q * Real.exp 1 :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = Real.exp 1 * (q : ℝ) ^ q := by ring
  have h5 : ((q : ℝ) + 1) * ((q : ℝ) + 1) ^ q
      ≤ ((q : ℝ) + 1) * (Real.exp 1 * (q : ℝ) ^ q) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  refine h5.trans ?_
  have hqr : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have h6 : ((q : ℝ) + 1) ≤ 2 * (q : ℝ) := by linarith
  calc ((q : ℝ) + 1) * (Real.exp 1 * (q : ℝ) ^ q)
      ≤ (2 * (q : ℝ)) * (Real.exp 1 * (q : ℝ) ^ q) :=
        mul_le_mul_of_nonneg_right h6 (by positivity)
    _ = 2 * Real.exp 1 * (q : ℝ) * (q : ℝ) ^ q := by ring

/-- **推论 B**：`q! ≤ 2 e q (q/2)^q`（`q ≥ 1`）——Case II 的平凡分支用。 -/
lemma factorial_le_two_mul_exp_mul (q : ℕ) (hq : 1 ≤ q) :
    (q.factorial : ℝ) ≤ 2 * Real.exp 1 * (q : ℝ) * ((q : ℝ) / 2) ^ q := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hmain := factorial_mul_exp_le q
  have hexpq : Real.exp (q : ℝ) = (Real.exp 1) ^ q := by
    simpa using Real.exp_nat_mul (1 : ℝ) q
  have heq1 : ((q : ℝ) + 1) ^ (q + 1) / Real.exp (q : ℝ)
      = ((q : ℝ) + 1) * (((q : ℝ) + 1) / Real.exp 1) ^ q := by
    rw [pow_succ, hexpq, div_pow]
    field_simp
    try ring
  have h1 : (q.factorial : ℝ) ≤ ((q : ℝ) + 1) * (((q : ℝ) + 1) / Real.exp 1) ^ q := by
    rw [← heq1, le_div_iff₀ (Real.exp_pos (q : ℝ))]
    exact hmain
  refine h1.trans ?_
  have h2 : (((q : ℝ) + 1) / Real.exp 1) ^ q ≤ Real.exp 1 * ((q : ℝ) / 2) ^ q := by
    have h3 : ((q : ℝ) + 1) / Real.exp 1
        = ((q : ℝ) / 2) * ((2 * ((q : ℝ) + 1)) / ((q : ℝ) * Real.exp 1)) := by
      field_simp
      try ring
    rw [h3, mul_pow]
    have h4 : ((2 * ((q : ℝ) + 1)) / ((q : ℝ) * Real.exp 1)) ^ q ≤ Real.exp 1 := by
      have h5 : (2 * ((q : ℝ) + 1)) / ((q : ℝ) * Real.exp 1)
          = (2 / Real.exp 1) * (1 + (q : ℝ)⁻¹) := by
        field_simp
        try ring
      rw [h5, mul_pow]
      have h6 : (1 + (q : ℝ)⁻¹) ^ q ≤ Real.exp 1 := one_add_inv_pow_le_exp q hq
      have h7 : (2 / Real.exp 1) ^ q ≤ 1 := by
        have h8 : (2 : ℝ) / Real.exp 1 ≤ 1 := by
          rw [div_le_one (Real.exp_pos 1)]
          have := Real.exp_one_gt_d9
          linarith
        have h9 : (0 : ℝ) ≤ 2 / Real.exp 1 := by positivity
        calc (2 / Real.exp 1) ^ q ≤ 1 ^ q := pow_le_pow_left₀ h9 h8 q
          _ = 1 := one_pow q
      calc (2 / Real.exp 1) ^ q * (1 + (q : ℝ)⁻¹) ^ q
          ≤ 1 * Real.exp 1 := mul_le_mul h7 h6 (by positivity) (by norm_num)
        _ = Real.exp 1 := one_mul _
    calc ((q : ℝ) / 2) ^ q * ((2 * ((q : ℝ) + 1)) / ((q : ℝ) * Real.exp 1)) ^ q
        ≤ ((q : ℝ) / 2) ^ q * Real.exp 1 := mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = Real.exp 1 * ((q : ℝ) / 2) ^ q := by ring
  have h8 : ((q : ℝ) + 1) * (((q : ℝ) + 1) / Real.exp 1) ^ q
      ≤ ((q : ℝ) + 1) * (Real.exp 1 * ((q : ℝ) / 2) ^ q) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  refine h8.trans ?_
  have hqr : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have h9 : ((q : ℝ) + 1) ≤ 2 * (q : ℝ) := by linarith
  calc ((q : ℝ) + 1) * (Real.exp 1 * ((q : ℝ) / 2) ^ q)
      ≤ (2 * (q : ℝ)) * (Real.exp 1 * ((q : ℝ) / 2) ^ q) :=
        mul_le_mul_of_nonneg_right h9 (by positivity)
    _ = 2 * Real.exp 1 * (q : ℝ) * ((q : ℝ) / 2) ^ q := by ring

/-! ## §2 `e^2` 与 `e^{1/2}` 的显式常数 -/

lemma exp_two_le : Real.exp 2 ≤ 7.4 := by
  have h : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]
    norm_num
  have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  nlinarith [Real.exp_pos 1, h, h1]

lemma two_mul_exp_two_le : 2 * Real.exp 2 ≤ 14.8 := by
  linarith [exp_two_le]

lemma exp_half_le : Real.exp (1 / 2) ≤ 5 / 3 := by
  have h1 : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
    rw [← Real.exp_add]
    norm_num
  have h2 : Real.exp 1 < 25 / 9 := by
    have h := Real.exp_one_lt_d9
    norm_num at h ⊢
    linarith
  nlinarith [Real.exp_pos (1 / 2), h1, h2]

/-! ## §3 带内逼近误差（`δ = log(2q/τ)` 的围道平移） -/

/-- `τ · sinh (log (2q/τ)) = q - τ²/(4q)`。 -/
lemma tau_mul_sinh_log (τ : ℝ) (hτ : 0 < τ) {q : ℝ} (hq : 0 < q) :
    τ * Real.sinh (Real.log (2 * q / τ)) = q - τ ^ 2 / (4 * q) := by
  have hy : (0 : ℝ) < 2 * q / τ := by positivity
  rw [Real.sinh_log hy]
  field_simp
  try ring

/-- `exp (-log (2q/τ)) = τ/(2q)`。 -/
lemma exp_neg_log_div (τ : ℝ) (hτ : 0 < τ) {q : ℝ} (hq : 0 < q) :
    Real.exp (-(Real.log (2 * q / τ))) = τ / (2 * q) := by
  have hy : (0 : ℝ) < 2 * q / τ := by positivity
  rw [Real.exp_neg, Real.exp_log hy]
  field_simp

/-- **核心指数恒等式**（`δ = log(2q/τ)`）：

`exp (τ sinh δ - (q+j) δ) = (e τ/(2q))^q · (τ/(2q))^j · e^{-τ²/(4q)}`。 -/
lemma exp_sinh_sub_log (τ : ℝ) (hτ : 0 < τ) (q : ℕ) (hq : 0 < q) (j : ℕ) :
    Real.exp (τ * Real.sinh (Real.log (2 * (q : ℝ) / τ))
        - (((q + j : ℕ)) : ℝ) * Real.log (2 * (q : ℝ) / τ))
      = (Real.exp 1 * τ / (2 * (q : ℝ))) ^ q * (τ / (2 * (q : ℝ))) ^ j
        * Real.exp (-(τ ^ 2 / (4 * (q : ℝ)))) := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hcast : (((q + j : ℕ)) : ℝ) = (q : ℝ) + (j : ℝ) := by push_cast; ring
  have hexp1 : τ * Real.sinh (Real.log (2 * (q : ℝ) / τ))
      = (q : ℝ) - τ ^ 2 / (4 * (q : ℝ)) := tau_mul_sinh_log τ hτ hq0
  have hlogq : Real.exp (-((q : ℝ) * Real.log (2 * (q : ℝ) / τ)))
      = (τ / (2 * (q : ℝ))) ^ q := by
    rw [show -((q : ℝ) * Real.log (2 * (q : ℝ) / τ))
        = (q : ℕ) * (-(Real.log (2 * (q : ℝ) / τ))) by push_cast; ring,
      Real.exp_nat_mul, exp_neg_log_div τ hτ hq0]
  have hlogj : Real.exp (-((j : ℝ) * Real.log (2 * (q : ℝ) / τ)))
      = (τ / (2 * (q : ℝ))) ^ j := by
    rw [show -((j : ℝ) * Real.log (2 * (q : ℝ) / τ))
        = j * (-(Real.log (2 * (q : ℝ) / τ))) by ring,
      Real.exp_nat_mul, exp_neg_log_div τ hτ hq0]
  have hexpq : Real.exp ((q : ℝ) - τ ^ 2 / (4 * (q : ℝ)))
      = (Real.exp 1) ^ q * Real.exp (-(τ ^ 2 / (4 * (q : ℝ)))) := by
    rw [Real.exp_sub, show (q : ℝ) = (q : ℕ) * 1 by push_cast; ring, Real.exp_nat_mul, mul_one,
      div_eq_mul_inv, Real.exp_neg]
  rw [hcast, show τ * Real.sinh (Real.log (2 * (q : ℝ) / τ))
        - ((q : ℝ) + (j : ℝ)) * Real.log (2 * (q : ℝ) / τ)
      = ((q : ℝ) - τ ^ 2 / (4 * (q : ℝ))) + (-((q : ℝ) * Real.log (2 * (q : ℝ) / τ)))
        + (-((j : ℝ) * Real.log (2 * (q : ℝ) / τ))) by rw [hexp1]; ring]
  rw [Real.exp_add, Real.exp_add, hlogq, hlogj, hexpq]
  rw [show Real.exp 1 * τ / (2 * (q : ℝ)) = Real.exp 1 * (τ / (2 * (q : ℝ))) by ring, mul_pow]
  ring

/-- **带内逼近误差**（`|μ| ≤ τ ≤ q`、`τ > 0`）：

`‖e^{-iμ} - scaledApprox τ q (μ)‖ ≤ 9 (e τ/(2q))^q`。 -/
lemma band_error_scaledApprox (τ : ℝ) (hτ : 0 < τ) {q : ℕ} (hq1 : 1 ≤ q)
    (hτq : τ ≤ (q : ℝ)) :
    ∀ μ : ℝ, |μ| ≤ τ →
      ‖Complex.exp (-(μ : ℂ) * Complex.I) - (scaledApprox τ q).eval ((μ : ℂ))‖
        ≤ 9 * (Real.exp 1 * τ / (2 * (q : ℝ))) ^ q := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq1
  set δ : ℝ := Real.log (2 * (q : ℝ) / τ) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    exact Real.log_pos (by rw [lt_div_iff₀ hτ]; linarith)
  have hrval : Real.exp (-δ) = τ / (2 * (q : ℝ)) := by
    rw [hδdef]; exact exp_neg_log_div τ hτ hq0
  have hrle : Real.exp (-δ) ≤ 1 / 2 := by
    rw [hrval, div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (q : ℝ))]
    linarith
  have hden_pos : (0 : ℝ) < 1 - Real.exp (-δ) := by linarith
  have hden : (1 : ℝ) / (1 - Real.exp (-δ)) ≤ 2 := by
    rw [div_le_iff₀ hden_pos]
    linarith
  have hexpq : Real.exp (τ * Real.sinh δ - (q : ℝ) * δ)
      ≤ (Real.exp 1 * τ / (2 * (q : ℝ))) ^ q := by
    have h := exp_sinh_sub_log τ hτ q hq1 0
    rw [← hδdef] at h
    have h2 : (Real.exp 1 * τ / (2 * (q : ℝ))) ^ q * (τ / (2 * (q : ℝ))) ^ 0
        * Real.exp (-(τ ^ 2 / (4 * (q : ℝ))))
        = (Real.exp 1 * τ / (2 * (q : ℝ))) ^ q
          * Real.exp (-(τ ^ 2 / (4 * (q : ℝ)))) := by ring
    rw [h2] at h
    have h3 : Real.exp (-(τ ^ 2 / (4 * (q : ℝ)))) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : (0 : ℝ) ≤ τ ^ 2 / (4 * (q : ℝ)) := by positivity
      linarith
    calc Real.exp (τ * Real.sinh δ - (q : ℝ) * δ)
        = (Real.exp 1 * τ / (2 * (q : ℝ))) ^ q
          * Real.exp (-(τ ^ 2 / (4 * (q : ℝ)))) := h
      _ ≤ (Real.exp 1 * τ / (2 * (q : ℝ))) ^ q * 1 :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = (Real.exp 1 * τ / (2 * (q : ℝ))) ^ q := mul_one _
  have hexpq' : Real.exp (τ * Real.sinh δ - ((q : ℤ)) * δ)
      ≤ (Real.exp 1 * τ / (2 * (q : ℝ))) ^ q := by
    have hcast : ((q : ℤ) : ℝ) = (q : ℝ) := by push_cast; ring
    rw [hcast]
    exact hexpq
  intro μ hμ
  have hband := exp_sub_approxPoly_band τ hτ hδpos hq1 μ hμ
  have hf := fcoef_bound τ hτ.le hδpos (q : ℤ) (by exact_mod_cast hq1)
  have htail : 4 * Real.exp (τ * Real.sinh δ) * Real.exp (-δ) ^ q / (1 - Real.exp (-δ))
      ≤ 8 * (Real.exp 1 * τ / (2 * (q : ℝ))) ^ q := by
    have hnum : Real.exp (τ * Real.sinh δ) * Real.exp (-δ) ^ q
        = Real.exp (τ * Real.sinh δ - (q : ℝ) * δ) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      push_cast
      ring
    have h4nn : (0 : ℝ) ≤ 4 * (Real.exp (τ * Real.sinh δ) * Real.exp (-δ) ^ q) := by
      positivity
    have hrewrite : 4 * Real.exp (τ * Real.sinh δ) * Real.exp (-δ) ^ q
        = 4 * (Real.exp (τ * Real.sinh δ) * Real.exp (-δ) ^ q) := by ring
    rw [hrewrite, hnum]
    have hstep : 4 * Real.exp (τ * Real.sinh δ - (q : ℝ) * δ)
        / (1 - Real.exp (-δ)) ≤ 8 * (Real.exp 1 * τ / (2 * (q : ℝ))) ^ q := by
      rw [div_le_iff₀ hden_pos]
      have h8 : 8 * (Real.exp 1 * τ / (2 * (q : ℝ))) ^ q * (1 - Real.exp (-δ))
          ≥ 4 * Real.exp (τ * Real.sinh δ - (q : ℝ) * δ) := by
        have h9 : 2 * (1 - Real.exp (-δ)) ≥ 1 := by linarith
        have h10 : 8 * (Real.exp 1 * τ / (2 * (q : ℝ))) ^ q * (1 - Real.exp (-δ))
            = 4 * (Real.exp 1 * τ / (2 * (q : ℝ))) ^ q * (2 * (1 - Real.exp (-δ))) := by ring
        rw [h10]
        have h11 : 4 * (Real.exp 1 * τ / (2 * (q : ℝ))) ^ q * 1
            ≤ 4 * (Real.exp 1 * τ / (2 * (q : ℝ))) ^ q * (2 * (1 - Real.exp (-δ))) :=
          mul_le_mul_of_nonneg_left h9 (by positivity)
        have h12 : 4 * Real.exp (τ * Real.sinh δ - (q : ℝ) * δ)
            ≤ 4 * (Real.exp 1 * τ / (2 * (q : ℝ))) ^ q := by linarith [hexpq]
        linarith [h11, h12]
      linarith [h8]
    exact hstep
  rw [scaledApprox_eval τ (ne_of_gt hτ) q μ]
  linarith [hband, hf, hexpq', htail]

/-! ## §4 collar 显式常数（`k := q`、`B := τ/q²`、`r := e^{-δ}`） -/

/-- **collar 常数**：`B = τ/q²`、`r = e^{-δ}`、`ε = 9 (eτ/(2q))^q` 时，`M₁, M₂`
可分别用 `1200 q²ε`、`10^7 q⁴ε` 控制。 -/
lemma collar_bounds_explicit (τ : ℝ) (hτ : 0 < τ) {q : ℕ} (hq4 : 4 ≤ q) (hτq : τ ≤ (q : ℝ)) :
    ∃ M₁ M₂ : ℝ, 0 ≤ M₁ ∧ 0 ≤ M₂ ∧
      (∀ μ : ℝ, |μ| ≤ τ + τ / (q : ℝ) ^ 2 →
        ‖deriv (fun x : ℝ => psiA (scaledApprox τ q) x) μ‖ ≤ M₁) ∧
      (∀ μ : ℝ, |μ| ≤ τ + τ / (q : ℝ) ^ 2 →
        ‖deriv (deriv (fun x : ℝ => psiA (scaledApprox τ q) x)) μ‖ ≤ M₂) ∧
      τ * M₁ ≤ 1200 * (q : ℝ) ^ 2 * (9 * (Real.exp 1 * τ / (2 * (q : ℝ))) ^ q) ∧
      τ ^ 2 * M₂ ≤ 10 ^ 7 * (q : ℝ) ^ 4 * (9 * (Real.exp 1 * τ / (2 * (q : ℝ))) ^ q) := by
  have hq1 : 1 ≤ q := by omega
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq1
  have hq4' : (4 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq4
  have hq1r : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
  set δ : ℝ := Real.log (2 * (q : ℝ) / τ) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    exact Real.log_pos (by rw [lt_div_iff₀ hτ]; linarith)
  set r : ℝ := Real.exp (-δ) with hrdef
  set B : ℝ := τ / (q : ℝ) ^ 2 with hBdef
  have hrpos : 0 < r := Real.exp_pos _
  have hBpos : 0 < B := by rw [hBdef]; positivity
  have hrval : r = τ / (2 * (q : ℝ)) := by
    rw [hrdef, hδdef]; exact exp_neg_log_div τ hτ hq0
  have hεpos : 0 < 9 * (Real.exp 1 * τ / (2 * (q : ℝ))) ^ q := by positivity
  have hεnn : (0 : ℝ) ≤ 9 * (Real.exp 1 * τ / (2 * (q : ℝ))) ^ q := hεpos.le
  have hdec : ∀ j : ℕ, ‖fcoef τ (((q + j : ℕ)) : ℤ)‖
      ≤ (9 * (Real.exp 1 * τ / (2 * (q : ℝ))) ^ q) * r ^ j := by
    intro j
    have hb := fcoef_bound τ hτ.le hδpos (((q + j : ℕ)) : ℤ) (by positivity)
    have hcast : (((q + j : ℕ)) : ℤ) = (q : ℤ) + (j : ℤ) := by push_cast; ring
    have hcast' : (((q + j : ℕ)) : ℝ) = (q : ℝ) + (j : ℝ) := by push_cast; ring
    have hsplit : τ * Real.sinh δ - (((q + j : ℕ)) : ℤ) * δ
        = (τ * Real.sinh δ - ((q : ℤ)) * δ) + (-((j : ℤ) * δ)) := by
      rw [hcast]
      push_cast
      ring
    rw [hsplit, Real.exp_add] at hb
    have h1 : Real.exp (τ * Real.sinh δ - ((q : ℤ)) * δ)
        ≤ (Real.exp 1 * τ / (2 * (q : ℝ))) ^ q := by
      have hqcast : ((q : ℤ) : ℝ) = (q : ℝ) := by push_cast; ring
      rw [hqcast]
      have h2 : Real.exp (τ * Real.sinh δ - (q : ℝ) * δ) ≤ (Real.exp 1 * τ / (2 * (q : ℝ))) ^ q := by
        rw [hδdef]
        have h := exp_sinh_sub_log τ hτ q hq1 0
        have h3 : (Real.exp 1 * τ / (2 * (q : ℝ))) ^ q * (τ / (2 * (q : ℝ))) ^ 0
            * Real.exp (-(τ ^ 2 / (4 * (q : ℝ))))
            = (Real.exp 1 * τ / (2 * (q : ℝ))) ^ q
              * Real.exp (-(τ ^ 2 / (4 * (q : ℝ)))) := by ring
        rw [h3] at h
        have h4 : Real.exp (-(τ ^ 2 / (4 * (q : ℝ)))) ≤ 1 := by
          rw [Real.exp_le_one_iff]
          have : (0 : ℝ) ≤ τ ^ 2 / (4 * (q : ℝ)) := by positivity
          linarith
        calc Real.exp (τ * Real.sinh (Real.log (2 * (q : ℝ) / τ))
              - (q : ℝ) * Real.log (2 * (q : ℝ) / τ))
            = (Real.exp 1 * τ / (2 * (q : ℝ))) ^ q
              * Real.exp (-(τ ^ 2 / (4 * (q : ℝ)))) := h
          _ ≤ (Real.exp 1 * τ / (2 * (q : ℝ))) ^ q * 1 :=
              mul_le_mul_of_nonneg_left h4 (by positivity)
          _ = (Real.exp 1 * τ / (2 * (q : ℝ))) ^ q := mul_one _
      exact h2
    have h2 : Real.exp (-((j : ℤ) * δ)) = r ^ j := by
      rw [show -((j : ℤ) * δ) = (j : ℝ) * (-δ) by push_cast; ring, Real.exp_nat_mul]
    rw [h2] at hb
    have h3 : (0 : ℝ) ≤ r ^ j := by positivity
    have h4 : Real.exp (τ * Real.sinh δ - ((q : ℤ)) * δ) * r ^ j
        ≤ (Real.exp 1 * τ / (2 * (q : ℝ))) ^ q * r ^ j :=
      mul_le_mul_of_nonneg_right h1 h3
    have h5 : (Real.exp 1 * τ / (2 * (q : ℝ))) ^ q * r ^ j
        ≤ (9 * (Real.exp 1 * τ / (2 * (q : ℝ))) ^ q) * r ^ j := by
      have h6 : (0 : ℝ) ≤ (Real.exp 1 * τ / (2 * (q : ℝ))) ^ q := by positivity
      nlinarith [h6, h3]
    linarith [hb, h4, h5]
  have hBdivτ : B / τ = (1 / (q : ℝ)) ^ 2 := by
    rw [hBdef]
    field_simp
  have hsqrtB : Real.sqrt (B / τ) = 1 / (q : ℝ) := by
    rw [hBdivτ, Real.sqrt_sq_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 1 / (q : ℝ))]
  have hexp_q : Real.exp (2 * (1 / (q : ℝ))) ≤ Real.exp (1 / 2) := by
    refine Real.exp_le_exp.mpr ?_
    rw [show (2 : ℝ) * (1 / (q : ℝ)) = 2 / (q : ℝ) by ring,
      div_le_iff₀ (by positivity : (0 : ℝ) < (q : ℝ))]
    linarith
  have hrval' : r ≤ 1 / 2 := by
    rw [hrval, div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (q : ℝ))]
    linarith
  have htR : tailR B τ r ≤ 5 / 6 := by
    rw [tailR, hsqrtB]
    have h1 : r * Real.exp (2 * (1 / (q : ℝ))) ≤ (1 / 2) * (5 / 3) :=
      mul_le_mul hrval' (hexp_q.trans exp_half_le) (Real.exp_pos _).le (by norm_num)
    have h2 : Real.exp (1 / 2) ≤ 5 / 3 := exp_half_le
    calc r * Real.exp (2 * (1 / (q : ℝ))) ≤ (1 / 2) * (5 / 3) := h1
      _ = 5 / 6 := by norm_num
  have htR1 : tailR B τ r < 1 := lt_of_le_of_lt htR (by norm_num)
  have hone : (1 : ℝ) / 6 ≤ 1 - tailR B τ r := by linarith
  have hden_pos : (0 : ℝ) < 1 - tailR B τ r := by linarith
  have h6 : (1 : ℝ) ≤ 6 * (1 - tailR B τ r) := by linarith
  have h216 : (1 : ℝ) ≤ 216 * (1 - tailR B τ r) ^ 3 := by
    have h1 : (1 / 6 : ℝ) ^ 3 ≤ (1 - tailR B τ r) ^ 3 :=
      pow_le_pow_left₀ (by norm_num) hone 3
    norm_num at h1 ⊢
    linarith
  have h7776 : (1 : ℝ) ≤ 7776 * (1 - tailR B τ r) ^ 5 := by
    have h1 : (1 / 6 : ℝ) ^ 5 ≤ (1 - tailR B τ r) ^ 5 :=
      pow_le_pow_left₀ (by norm_num) hone 5
    norm_num at h1 ⊢
    linarith
  have hexp2 : Real.exp ((q : ℝ) * (2 * Real.sqrt (B / τ))) = Real.exp 2 := by
    rw [hsqrtB]
    congr 1
    field_simp
  have hBτ2 : B / τ ≤ 1 / 2 := by
    rw [hBdivτ, div_pow, one_pow, div_le_iff₀ (by positivity : (0 : ℝ) < (q : ℝ) ^ 2)]
    nlinarith [hq4']
  set M₁ : ℝ := 2 * Real.exp 2 *
      (2 * (q : ℝ) ^ 2 / (1 - tailR B τ r) + 4 / (1 - tailR B τ r) ^ 3
        + τ / (1 - tailR B τ r)) * (9 * (Real.exp 1 * τ / (2 * (q : ℝ))) ^ q) / τ with hM₁def
  set M₂ : ℝ := 2 * Real.exp 2 *
      (256 * (q : ℝ) ^ 4 / (1 - tailR B τ r) + 19200 / (1 - tailR B τ r) ^ 5
        + 4 * τ * (q : ℝ) ^ 2 / (1 - tailR B τ r) + 8 * τ / (1 - tailR B τ r) ^ 3
        + τ ^ 2 / (1 - tailR B τ r)) * (9 * (Real.exp 1 * τ / (2 * (q : ℝ))) ^ q) / τ ^ 2
      with hM₂def
  have hcol1 := norm_deriv_psiA_scaled_collar_gen τ B hτ hBpos (k := q) hq1 hεnn hrpos.le htR1 hdec
  have hcol2 := norm_deriv2_psiA_scaled_collar_gen τ B hτ hBpos (k := q) hq1 hεnn hrpos.le htR1 hdec hBτ2
  have hA1 : ∀ μ : ℝ, |μ| ≤ τ + τ / (q : ℝ) ^ 2 →
      ‖deriv (fun x : ℝ => psiA (scaledApprox τ q) x) μ‖ ≤ M₁ := by
    intro μ hμ
    have hμ' : |μ| ≤ τ + B := by rw [hBdef]; exact hμ
    have h := hcol1 μ hμ'
    rw [hexp2] at h
    rw [hM₁def]
    exact h
  have hA2 : ∀ μ : ℝ, |μ| ≤ τ + τ / (q : ℝ) ^ 2 →
      ‖deriv (deriv (fun x : ℝ => psiA (scaledApprox τ q) x)) μ‖ ≤ M₂ := by
    intro μ hμ
    have hμ' : |μ| ≤ τ + B := by rw [hBdef]; exact hμ
    have h := hcol2 μ hμ'
    rw [hexp2] at h
    rw [hM₂def]
    exact h

  refine ⟨M₁, M₂, ?_, ?_, hA1, hA2, ?_, ?_⟩
  · rw [hM₁def]; positivity
  · rw [hM₂def]; positivity
  · -- τ · M₁ ≤ 1200 q² ε
    set u : ℝ := 1 - tailR B τ r with hu
    set E : ℝ := 9 * (Real.exp 1 * τ / (2 * (q : ℝ))) ^ q with hE
    have hu_pos : 0 < u := by rw [hu]; exact hden_pos
    have hu6 : (1 : ℝ) ≤ 6 * u := h6
    have hu216 : (1 : ℝ) ≤ 216 * u ^ 3 := h216
    have hEpos : 0 < E := by rw [hE]; positivity
    rw [hM₁def]
    have hA : τ * (2 * Real.exp 2 * (2 * (q : ℝ) ^ 2 / u + 4 / u ^ 3 + τ / u) * E / τ)
        = 2 * Real.exp 2 * (2 * (q : ℝ) ^ 2 / u + 4 / u ^ 3 + τ / u) * E := by
      field_simp
    rw [hA]
    have h2 : 2 * (q : ℝ) ^ 2 / u ≤ 2 * (q : ℝ) ^ 2 * 6 := by
      rw [div_le_iff₀ hu_pos]
      calc 2 * (q : ℝ) ^ 2 = 2 * (q : ℝ) ^ 2 * 1 := by ring
        _ ≤ 2 * (q : ℝ) ^ 2 * (6 * u) := mul_le_mul_of_nonneg_left hu6 (by positivity)
        _ = 2 * (q : ℝ) ^ 2 * 6 * u := by ring
    have h3 : 4 / u ^ 3 ≤ 4 * 216 := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < u ^ 3)]
      calc (4 : ℝ) = 4 * 1 := by ring
        _ ≤ 4 * (216 * u ^ 3) := mul_le_mul_of_nonneg_left hu216 (by norm_num)
        _ = 4 * 216 * u ^ 3 := by ring
    have h4 : τ / u ≤ (q : ℝ) * 6 := by
      rw [div_le_iff₀ hu_pos]
      calc τ ≤ (q : ℝ) := hτq
        _ = (q : ℝ) * 1 := by ring
        _ ≤ (q : ℝ) * (6 * u) := mul_le_mul_of_nonneg_left hu6 hq0.le
        _ = (q : ℝ) * 6 * u := by ring
    have hsum : 2 * (q : ℝ) ^ 2 / u + 4 / u ^ 3 + τ / u
        ≤ 12 * (q : ℝ) ^ 2 + 864 + 6 * (q : ℝ) := by linarith [h2, h3, h4]
    have hsum2 : 12 * (q : ℝ) ^ 2 + 864 + 6 * (q : ℝ) ≤ 67.5 * (q : ℝ) ^ 2 := by
      nlinarith [hq4', sq_nonneg ((q : ℝ) - 4)]
    calc 2 * Real.exp 2 * (2 * (q : ℝ) ^ 2 / u + 4 / u ^ 3 + τ / u) * E
        ≤ 2 * Real.exp 2 * (67.5 * (q : ℝ) ^ 2) * E :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hsum.trans hsum2) (by positivity)) hEpos.le
      _ ≤ 1200 * (q : ℝ) ^ 2 * E := by
          have hcoef : 2 * Real.exp 2 * (67.5 * (q : ℝ) ^ 2) ≤ 1200 * (q : ℝ) ^ 2 := by
            nlinarith [two_mul_exp_two_le, sq_nonneg (q : ℝ)]
          exact mul_le_mul_of_nonneg_right hcoef hEpos.le
  · -- τ² · M₂ ≤ 10^7 q⁴ ε
    set u : ℝ := 1 - tailR B τ r with hu
    set E : ℝ := 9 * (Real.exp 1 * τ / (2 * (q : ℝ))) ^ q with hE
    have hu_pos : 0 < u := by rw [hu]; exact hden_pos
    have hu6 : (1 : ℝ) ≤ 6 * u := h6
    have hu216 : (1 : ℝ) ≤ 216 * u ^ 3 := h216
    have hu7776 : (1 : ℝ) ≤ 7776 * u ^ 5 := h7776
    have hEpos : 0 < E := by rw [hE]; positivity
    have hq4pow : (256 : ℝ) ≤ (q : ℝ) ^ 4 := by
      have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) hq4' 4
      norm_num at h
      exact h
    rw [hM₂def]
    have hA : τ ^ 2 * (2 * Real.exp 2 *
        (256 * (q : ℝ) ^ 4 / u + 19200 / u ^ 5 + 4 * τ * (q : ℝ) ^ 2 / u + 8 * τ / u ^ 3
          + τ ^ 2 / u) * E / τ ^ 2)
        = 2 * Real.exp 2 * (256 * (q : ℝ) ^ 4 / u + 19200 / u ^ 5 + 4 * τ * (q : ℝ) ^ 2 / u
          + 8 * τ / u ^ 3 + τ ^ 2 / u) * E := by
      field_simp
    rw [hA]
    have h2 : 256 * (q : ℝ) ^ 4 / u ≤ 1536 * (q : ℝ) ^ 4 := by
      rw [div_le_iff₀ hu_pos]
      calc 256 * (q : ℝ) ^ 4 = 256 * (q : ℝ) ^ 4 * 1 := by ring
        _ ≤ 256 * (q : ℝ) ^ 4 * (6 * u) := mul_le_mul_of_nonneg_left hu6 (by positivity)
        _ = 1536 * (q : ℝ) ^ 4 * u := by ring
    have h3 : 19200 / u ^ 5 ≤ 583200 * (q : ℝ) ^ 4 := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < u ^ 5)]
      have h4 : (149299200 : ℝ) ≤ 583200 * (q : ℝ) ^ 4 := by nlinarith [hq4pow]
      calc (19200 : ℝ) = 19200 * 1 := by ring
        _ ≤ 19200 * (7776 * u ^ 5) := mul_le_mul_of_nonneg_left hu7776 (by norm_num)
        _ = 149299200 * u ^ 5 := by ring
        _ ≤ 583200 * (q : ℝ) ^ 4 * u ^ 5 := mul_le_mul_of_nonneg_right h4 (by positivity)
    have h4a : 4 * τ * (q : ℝ) ^ 2 / u ≤ 24 * (q : ℝ) ^ 4 := by
      rw [div_le_iff₀ hu_pos]
      have h7 : τ * (q : ℝ) ^ 2 ≤ (q : ℝ) ^ 3 := by nlinarith [hτq, sq_nonneg (q : ℝ)]
      have h8 : (q : ℝ) ^ 3 ≤ (q : ℝ) ^ 4 := by
        have h := pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ (q : ℝ)) (by norm_num : 3 ≤ 4)
        simpa using h
      have h10 : (1 : ℝ) ≤ 6 * (q : ℝ) * u := by
        have h11 : (6 : ℝ) * u * 1 ≤ 6 * u * (q : ℝ) :=
          mul_le_mul_of_nonneg_left hq1r (by linarith [hu6])
        linarith [hu6, h11]
      have h13 : (q : ℝ) ^ 3 ≤ 6 * (q : ℝ) ^ 4 * u := by
        calc (q : ℝ) ^ 3 = (q : ℝ) ^ 3 * 1 := by ring
          _ ≤ (q : ℝ) ^ 3 * (6 * (q : ℝ) * u) :=
              mul_le_mul_of_nonneg_left h10 (by positivity)
          _ = 6 * (q : ℝ) ^ 4 * u := by ring
      calc 4 * τ * (q : ℝ) ^ 2 = 4 * (τ * (q : ℝ) ^ 2) := by ring
        _ ≤ 4 * (q : ℝ) ^ 3 := by linarith [h7]
        _ ≤ 4 * (6 * (q : ℝ) ^ 4 * u) := by linarith [h13]
        _ = 24 * (q : ℝ) ^ 4 * u := by ring
    have h5 : 8 * τ / u ^ 3 ≤ 1728 * (q : ℝ) ^ 4 := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < u ^ 3)]
      have h8 : τ ≤ (q : ℝ) ^ 4 := by
        have h := pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ (q : ℝ)) (by norm_num : 1 ≤ 4)
        linarith [hτq, h]
      calc 8 * τ = 8 * τ * 1 := by ring
        _ ≤ 8 * τ * (216 * u ^ 3) := mul_le_mul_of_nonneg_left hu216 (by positivity)
        _ ≤ 8 * (q : ℝ) ^ 4 * (216 * u ^ 3) :=
            mul_le_mul_of_nonneg_right (by linarith [h8] : 8 * τ ≤ 8 * (q : ℝ) ^ 4)
              (by positivity)
        _ = 1728 * (q : ℝ) ^ 4 * u ^ 3 := by ring
    have h6'' : τ ^ 2 / u ≤ 6 * (q : ℝ) ^ 4 := by
      rw [div_le_iff₀ hu_pos]
      have h9 : τ ^ 2 ≤ (q : ℝ) ^ 4 := by
        have h10 : τ ^ 2 ≤ (q : ℝ) ^ 2 := by nlinarith [hτq, sq_nonneg τ, hq0.le]
        have h11 : (q : ℝ) ^ 2 ≤ (q : ℝ) ^ 4 :=
          pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ (q : ℝ)) (by norm_num : 2 ≤ 4)
        linarith [h10, h11]
      calc τ ^ 2 = τ ^ 2 * 1 := by ring
        _ ≤ τ ^ 2 * (6 * u) := mul_le_mul_of_nonneg_left hu6 (by positivity)
        _ ≤ (q : ℝ) ^ 4 * (6 * u) := mul_le_mul_of_nonneg_right h9 (by positivity)
        _ = 6 * (q : ℝ) ^ 4 * u := by ring
    have hsum : 256 * (q : ℝ) ^ 4 / u + 19200 / u ^ 5 + 4 * τ * (q : ℝ) ^ 2 / u
        + 8 * τ / u ^ 3 + τ ^ 2 / u
        ≤ (1536 + 583200 + 24 + 1728 + 6) * (q : ℝ) ^ 4 := by
      linarith [h2, h3, h4a, h5, h6'']
    have hfin : 2 * Real.exp 2 * ((1536 + 583200 + 24 + 1728 + 6) * (q : ℝ) ^ 4)
        ≤ 10 ^ 7 * (q : ℝ) ^ 4 := by
      nlinarith [two_mul_exp_two_le, pow_pos hq0 4]
    calc 2 * Real.exp 2 * (256 * (q : ℝ) ^ 4 / u + 19200 / u ^ 5 + 4 * τ * (q : ℝ) ^ 2 / u
          + 8 * τ / u ^ 3 + τ ^ 2 / u) * E
        ≤ 2 * Real.exp 2 * ((1536 + 583200 + 24 + 1728 + 6) * (q : ℝ) ^ 4) * E :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum (by positivity)) hEpos.le
      _ ≤ 10 ^ 7 * (q : ℝ) ^ 4 * E := mul_le_mul_of_nonneg_right hfin hEpos.le


/-! ## §5 M3（自由 taper 宽度 `B`）作用于 `h(0)` -/

/-- **装配引理**：`h(0) ≤ 8√(kernelA τ B P · kernelC τ B P)`，`P = scaledApprox τ (2N+2)`
（次数 `≤ 2N+1 < 2N+2`，矩条件可用），`B` 自由。 -/
lemma h_zero_le_of_kernel {N : ℕ} {φ : ℝ} {L : ℕ} {α θ : Fin L → ℝ}
    (hAdm : Admissible N φ L α θ) {B ε : ℝ}
    (hτ : 0 < (∑ j, θ j) / 2) (hε : 0 < ε) (hB : 0 < B)
    (hPε : ∀ μ : ℝ, |μ| ≤ (∑ j, θ j) / 2 →
      ‖Complex.exp (-(μ : ℂ) * Complex.I)
        - (scaledApprox ((∑ j, θ j) / 2) (2 * N + 2)).eval ((μ : ℂ))‖ ≤ ε) :
    h L α θ 0 ≤ 8 * Real.sqrt
      (kernelA ((∑ j, θ j) / 2) B (scaledApprox ((∑ j, θ j) / 2) (2 * N + 2))
        * kernelC ((∑ j, θ j) / 2) B (scaledApprox ((∑ j, θ j) / 2) (2 * N + 2))) := by
  obtain ⟨ι, hι, c, ν, hν, hf, hmom, h0⟩ := exists_expSum_data N φ L α θ hAdm
  letI : Fintype ι := hι
  have hPdeg : (scaledApprox ((∑ j, θ j) / 2) (2 * N + 2)).natDegree < 2 * N + 2 := by
    have h := scaledApprox_natDegree_le ((∑ j, θ j) / 2) (2 * N + 2)
    omega
  have hmom' : ∑ i, Complex.exp ((ν i : ℂ) * Complex.I)
      * (scaledApprox ((∑ j, θ j) / 2) (2 * N + 2)).eval ((ν i : ℂ)) * c i = 0 :=
    hmom _ hPdeg
  have hbdd : ∀ lam : ℝ,
      ‖∑ i, Complex.exp ((((ν i * lam : ℝ)) : ℂ) * Complex.I) * c i‖ ≤ 2 := by
    intro lam
    rw [← (hf lam).2]
    exact (hf lam).1
  have hint : Integrable (fun t : ℝ =>
      kernel ((∑ j, θ j) / 2) B (scaledApprox ((∑ j, θ j) / 2) (2 * N + 2)) t) :=
    integrable_kernel _ _ hτ hB _
  have hmain := norm_sum_le_of_moments_gen c ν hτ hε hB hν
    (scaledApprox ((∑ j, θ j) / 2) (2 * N + 2)) hPε hmom' hbdd hint
  have hnorm : ‖∑ i, c i‖ = h L α θ 0 := by
    rw [← h0, Complex.norm_def, Complex.normSq_ofReal,
      Real.sqrt_mul_self (h_bounds L α θ 0).1]
  simp only [kernelA, kernelC]
  rw [hnorm] at hmain
  exact hmain

/-! ## §6 最终比较（`ε = 9 (eτ/(2q))^q` 与乘积界 ⇒ 目标形状） -/

lemma final_compare {τ : ℝ} {q : ℕ} {s : ℝ} (hτ : 0 < τ) (hq4 : 4 ≤ q)
    (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hkey : 2 * s ^ 2 ≤ 8 * Real.sqrt (6 * 10 ^ 9 * (q : ℝ) ^ 5
      * (9 * (Real.exp 1 * τ / (2 * (q : ℝ))) ^ q) ^ 2)) :
    (Nat.factorial q : ℝ) * s ^ 4 / (10 ^ 8 * (q : ℝ) ^ 4) ≤ (τ / 2) ^ q := by
  have hq1 : 1 ≤ q := by omega
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq1
  set E : ℝ := 9 * (Real.exp 1 * τ / (2 * (q : ℝ))) ^ q with hEdef
  set w : ℝ := (τ / 2) ^ q with hwdef
  have hEpos : 0 < E := by rw [hEdef]; positivity
  have hwpos : 0 < w := by rw [hwdef]; positivity
  have hsqrtX : Real.sqrt (6 * 10 ^ 9 * (q : ℝ) ^ 5 * E ^ 2)
      ≤ 77500 * ((q : ℝ) ^ 2 * Real.sqrt (q : ℝ) * E) := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have h2 : (77500 * ((q : ℝ) ^ 2 * Real.sqrt (q : ℝ) * E)) ^ 2
        = 77500 ^ 2 * ((q : ℝ) ^ 5 * E ^ 2) := by
      rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hq0.le]
      ring
    rw [h2]
    have h3 : (6 : ℝ) * 10 ^ 9 ≤ 77500 ^ 2 := by norm_num
    nlinarith [h3, pow_pos hq0 5, pow_pos hEpos 2]
  have h620 : 2 * s ^ 2 ≤ 620000 * ((q : ℝ) ^ 2 * Real.sqrt (q : ℝ) * E) := by
    have hb : 8 * Real.sqrt (6 * 10 ^ 9 * (q : ℝ) ^ 5 * E ^ 2)
        ≤ 8 * (77500 * ((q : ℝ) ^ 2 * Real.sqrt (q : ℝ) * E)) :=
      mul_le_mul_of_nonneg_left hsqrtX (by norm_num)
    linarith [hkey, hb]
  have hEeq : E = 9 * (Real.exp 1) ^ q * w / (q : ℝ) ^ q := by
    rw [hEdef, hwdef]
    rw [show Real.exp 1 * τ / (2 * (q : ℝ)) = Real.exp 1 * (τ / (2 * (q : ℝ))) by ring,
      mul_pow]
    rw [show (τ / (2 * (q : ℝ))) ^ q = (τ / 2) ^ q / (q : ℝ) ^ q by
      rw [show τ / (2 * (q : ℝ)) = (τ / 2) / (q : ℝ) by ring, div_pow]]
    ring
  have hpow : (q : ℝ) ^ q = (q : ℝ) ^ 2 * (q : ℝ) ^ (q - 2) := by
    rw [← pow_add]
    congr 1
    omega
  have hw_low : s ^ 2 * (q : ℝ) ^ (q - 2)
      ≤ 2790000 * Real.sqrt (q : ℝ) * (Real.exp 1) ^ q * w := by
    have hA : 2 * s ^ 2
        ≤ 5580000 * Real.sqrt (q : ℝ) * (Real.exp 1) ^ q * w / (q : ℝ) ^ (q - 2) := by
      calc 2 * s ^ 2 ≤ 620000 * ((q : ℝ) ^ 2 * Real.sqrt (q : ℝ) * E) := h620
        _ = 5580000 * Real.sqrt (q : ℝ) * (Real.exp 1) ^ q * w / (q : ℝ) ^ (q - 2) := by
            rw [hEeq, hpow]
            field_simp
            ring
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < (q : ℝ) ^ (q - 2))] at hA
    linarith [hA]
  have hfac : (Nat.factorial q : ℝ) * (2790000 * Real.sqrt (q : ℝ) * (Real.exp 1) ^ q)
      ≤ 10 ^ 8 * (q : ℝ) ^ (q + 2) := by
    have h1 : (Nat.factorial q : ℝ) * (Real.exp 1) ^ q
        ≤ 2 * Real.exp 1 * (q : ℝ) * (q : ℝ) ^ q := by
      have h := factorial_mul_exp_div_pow_le q hq1
      rw [div_le_iff₀ (pow_pos hq0 q)] at h
      rwa [show Real.exp (q : ℝ) = (Real.exp 1) ^ q by
        simpa using Real.exp_nat_mul (1 : ℝ) q] at h
    have hq1r : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
    have hsq : Real.sqrt (q : ℝ) ≤ (q : ℝ) := by
      rw [Real.sqrt_le_iff]
      exact ⟨hq0.le, by nlinarith [hq1r]⟩
    calc (Nat.factorial q : ℝ) * (2790000 * Real.sqrt (q : ℝ) * (Real.exp 1) ^ q)
        = 2790000 * ((Nat.factorial q : ℝ) * (Real.exp 1) ^ q) * Real.sqrt (q : ℝ) := by ring
      _ ≤ 2790000 * (2 * Real.exp 1 * (q : ℝ) * (q : ℝ) ^ q) * (q : ℝ) :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1 (by norm_num)) hsq
            (Real.sqrt_nonneg _) (by positivity)
      _ = 5580000 * Real.exp 1 * (q : ℝ) ^ (q + 2) := by rw [pow_add]; ring
      _ ≤ 10 ^ 8 * (q : ℝ) ^ (q + 2) := by
          have h4 : 5580000 * Real.exp 1 ≤ 10 ^ 8 := by
            have h5 := Real.exp_one_lt_d9
            norm_num at h5 ⊢
            linarith
          exact mul_le_mul_of_nonneg_right h4 (by positivity)
  have hscalar : (Nat.factorial q : ℝ) / (10 ^ 8 * (q : ℝ) ^ 4)
      ≤ (q : ℝ) ^ (q - 2) / (2790000 * Real.sqrt (q : ℝ) * (Real.exp 1) ^ q) := by
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 10 ^ 8 * (q : ℝ) ^ 4)
      (by positivity : (0 : ℝ) < 2790000 * Real.sqrt (q : ℝ) * (Real.exp 1) ^ q)]
    have hpow2 : (q : ℝ) ^ (q - 2) * (q : ℝ) ^ 4 = (q : ℝ) ^ (q + 2) := by
      rw [← pow_add]
      congr 1
      omega
    calc (Nat.factorial q : ℝ) * (2790000 * Real.sqrt (q : ℝ) * (Real.exp 1) ^ q)
        ≤ 10 ^ 8 * (q : ℝ) ^ (q + 2) := hfac
      _ = (q : ℝ) ^ (q - 2) * (10 ^ 8 * (q : ℝ) ^ 4) := by
          rw [show (q : ℝ) ^ (q - 2) * (10 ^ 8 * (q : ℝ) ^ 4)
            = 10 ^ 8 * ((q : ℝ) ^ (q - 2) * (q : ℝ) ^ 4) by ring, hpow2]
  have hs2le1 : s ^ 2 ≤ 1 := by nlinarith [hs, hs1]
  have hs4 : s ^ 4 ≤ s ^ 2 := by nlinarith [hs2le1, sq_nonneg s]
  calc (Nat.factorial q : ℝ) * s ^ 4 / (10 ^ 8 * (q : ℝ) ^ 4)
      = s ^ 4 * ((Nat.factorial q : ℝ) / (10 ^ 8 * (q : ℝ) ^ 4)) := by ring
    _ ≤ s ^ 2 * ((q : ℝ) ^ (q - 2) / (2790000 * Real.sqrt (q : ℝ) * (Real.exp 1) ^ q)) := by
        have h1 : (0 : ℝ) ≤ (Nat.factorial q : ℝ) / (10 ^ 8 * (q : ℝ) ^ 4) := by positivity
        calc s ^ 4 * ((Nat.factorial q : ℝ) / (10 ^ 8 * (q : ℝ) ^ 4))
            ≤ s ^ 2 * ((Nat.factorial q : ℝ) / (10 ^ 8 * (q : ℝ) ^ 4)) :=
              mul_le_mul_of_nonneg_right hs4 h1
          _ ≤ s ^ 2 * ((q : ℝ) ^ (q - 2) / (2790000 * Real.sqrt (q : ℝ) * (Real.exp 1) ^ q)) :=
              mul_le_mul_of_nonneg_left hscalar (by positivity)
    _ = s ^ 2 * (q : ℝ) ^ (q - 2)
          / (2790000 * Real.sqrt (q : ℝ) * (Real.exp 1) ^ q) := by ring
    _ ≤ w := by
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2790000 * Real.sqrt (q : ℝ) * (Real.exp 1) ^ q)]
        linarith [hw_low]
    _ = (τ / 2) ^ q := by rw [hwdef]

/-! ## §7 主定理 -/

/-- **全阶 `8/e` 型下界（系数 4，无阈值）**：`q = 2N+2` 时

`4 (q! sin⁴(φ/4) / (10⁸ q⁴))^{1/q} ≤ cost θ`

对一切 `N ≥ 0`、`0 < φ ≤ π` 与任意 admissible 构造成立。 -/
theorem eight_over_e_bound {L : ℕ} {α θ : Fin L → ℝ} {N : ℕ} {φ : ℝ}
    (hφ0 : 0 < φ) (hφπ : φ ≤ Real.pi) (hAdm : Admissible N φ L α θ) :
    4 * ((Nat.factorial (2 * N + 2) : ℝ) * Real.sin (φ / 4) ^ 4
          / (10 ^ 8 * (((2 * N + 2 : ℕ)) : ℝ) ^ 4))
        ^ (1 / (((2 * N + 2 : ℕ)) : ℝ)) ≤ cost θ := by
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · subst hN0
    show 4 * ((Nat.factorial 2 : ℝ) * Real.sin (φ / 4) ^ 4
          / (10 ^ 8 * (((2 : ℕ)) : ℝ) ^ 4)) ^ (1 / ((2 : ℕ) : ℝ)) ≤ cost θ
    have h1 := elementary_bound (N := 0) hφ0 hφπ hAdm
    have hsnn : 0 ≤ Real.sin (φ / 4) :=
      le_of_lt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [hφπ]))
    have hs1 : Real.sin (φ / 4) ≤ 1 := Real.sin_le_one _
    have hbase : (2 : ℝ) * (2 * (Nat.factorial 2 : ℝ) * Real.sin (φ / 4) ^ 2)
          ^ (1 / ((2 : ℕ) : ℝ)) = 4 * Real.sin (φ / 4) := by
      have hf : (Nat.factorial 2 : ℝ) = 2 := by norm_num
      rw [hf]
      rw [show (2 : ℝ) * 2 * Real.sin (φ / 4) ^ 2 = (2 * Real.sin (φ / 4)) ^ 2 by ring]
      rw [show (1 : ℝ) / ((2 : ℕ) : ℝ) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow,
        Real.sqrt_sq (by positivity)]
      ring
    rw [hbase] at h1
    have htarget : 4 * ((Nat.factorial 2 : ℝ) * Real.sin (φ / 4) ^ 4
          / (10 ^ 8 * (((2 : ℕ)) : ℝ) ^ 4)) ^ (1 / ((2 : ℕ) : ℝ))
        ≤ 4 * Real.sin (φ / 4) := by
      have hf : (Nat.factorial 2 : ℝ) = 2 := by norm_num
      have hq2 : ((((2 : ℕ)) : ℝ)) ^ 4 = 16 := by norm_num
      rw [hf, hq2]
      rw [show (1 : ℝ) / ((2 : ℕ) : ℝ) = 1 / 2 by norm_num]
      have hle : 2 * Real.sin (φ / 4) ^ 4 / (10 ^ 8 * 16) ≤ Real.sin (φ / 4) ^ 2 := by
        have h2 : Real.sin (φ / 4) ^ 2 ≤ 1 := by nlinarith [hsnn, hs1]
        rw [show Real.sin (φ / 4) ^ 4 = (Real.sin (φ / 4) ^ 2) ^ 2 by ring]
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 8 * 16)]
        nlinarith [h2, sq_nonneg (Real.sin (φ / 4) ^ 2)]
      have h3 : (0 : ℝ) ≤ 2 * Real.sin (φ / 4) ^ 4 / (10 ^ 8 * 16) := by positivity
      calc 4 * (2 * Real.sin (φ / 4) ^ 4 / (10 ^ 8 * 16)) ^ (1 / 2 : ℝ)
          ≤ 4 * (Real.sin (φ / 4) ^ 2) ^ (1 / 2 : ℝ) := by
            have h4 := Real.rpow_le_rpow h3 hle (by norm_num : (0 : ℝ) ≤ (1 / 2 : ℝ))
            linarith
        _ = 4 * Real.sin (φ / 4) := by
            rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hsnn]
    linarith [h1, htarget]
  · set q : ℕ := 2 * N + 2 with hqdef
    set τ : ℝ := (∑ j, θ j) / 2 with hτdef
    set s : ℝ := Real.sin (φ / 4) with hsdef
    have hcost : cost θ = 2 * τ := by rw [cost, hτdef]; ring
    have hq4 : 4 ≤ q := by rw [hqdef]; omega
    have hq1 : 1 ≤ q := by omega
    have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq1
    have hq4r : (4 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq4
    have hq1r : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
    have hsnn : 0 ≤ s := by
      rw [hsdef]
      exact le_of_lt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [hφπ]))
    have hs1 : s ≤ 1 := by rw [hsdef]; exact Real.sin_le_one _
    have hs2le1 : s ^ 2 ≤ 1 := by nlinarith [hsnn, hs1]
    by_cases hτ0 : τ = 0
    · exfalso
      have hsum0 : ∑ j, θ j = 0 := by rw [hτdef] at hτ0; linarith
      have hz := h_zero_of_admissible_of_cost_eq_zero hAdm hsum0
      have hge := two_mul_sin_sq_le_h_zero N L α θ hφ0 hφπ hAdm
      rw [← hsdef] at hge
      have hspos : 0 < Real.sin (φ / 4) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [hφπ])
      rw [hz] at hge
      nlinarith [hspos]
    have hτnonneg : 0 ≤ τ := by
      rw [hτdef]
      exact div_nonneg (Finset.sum_nonneg fun j _ => hAdm.1 j) (by norm_num)
    have hτpos : 0 < τ := lt_of_le_of_ne hτnonneg (Ne.symm hτ0)
    have hX : (Nat.factorial q : ℝ) * s ^ 4 / (10 ^ 8 * (q : ℝ) ^ 4) ≤ (τ / 2) ^ q := by
      by_cases hcase : τ ≤ (q : ℝ)
      · -- Case I：τ ≤ q
        set B : ℝ := τ / (q : ℝ) ^ 2 with hBdef
        set E : ℝ := 9 * (Real.exp 1 * τ / (2 * (q : ℝ))) ^ q with hEdef
        have hBpos : 0 < B := by rw [hBdef]; exact div_pos hτpos (pow_pos hq0 2)
        have hEpos : 0 < E := by rw [hEdef]; positivity
        have hEnn : 0 ≤ E := hEpos.le
        have hkey : 2 * s ^ 2 ≤ 8 * Real.sqrt (6 * 10 ^ 9 * (q : ℝ) ^ 5 * E ^ 2) := by
          obtain ⟨M₁, M₂, hM₁nn, hM₂nn, hMA1, hMA2, hM1sh, hM2sh⟩ :=
            collar_bounds_explicit τ hτpos hq4 hcase
          -- 带内逼近
          have hPε : ∀ μ : ℝ, |μ| ≤ τ →
              ‖Complex.exp (-(μ : ℂ) * Complex.I) - (scaledApprox τ q).eval ((μ : ℂ))‖ ≤ E := by
            intro μ hμ
            rw [hEdef]
            exact band_error_scaledApprox τ hτpos hq1 hcase μ hμ
          -- collar（`tau + B` 形式）
          have hMA1' : ∀ μ : ℝ, |μ| ≤ τ + B →
              ‖deriv (fun x : ℝ => psiA (scaledApprox τ q) x) μ‖ ≤ M₁ := by
            intro μ hμ
            have hμ' : |μ| ≤ τ + τ / (q : ℝ) ^ 2 := by simpa [hBdef] using hμ
            exact hMA1 μ hμ'
          have hMA2' : ∀ μ : ℝ, |μ| ≤ τ + B →
              ‖deriv (deriv (fun x : ℝ => psiA (scaledApprox τ q) x)) μ‖ ≤ M₂ := by
            intro μ hμ
            have hμ' : |μ| ≤ τ + τ / (q : ℝ) ^ 2 := by simpa [hBdef] using hμ
            exact hMA2 μ hμ'
          have hψ : ∀ μ : ℝ, ‖psi τ B (scaledApprox τ q) μ‖ ≤ E + B * M₁ :=
            norm_psi_le_band_add_collar hτpos.le hBpos _ hM₁nn hPε hMA1'
          have hcut := deriv_cutoff_le_explicit hτpos hBpos
          have hKnn : (0 : ℝ) ≤ K₀ := K₀_pos.le
          have hK1 : ∀ μ : ℝ, ‖deriv (fun x : ℝ => ((cutoff τ B x : ℝ) : ℂ)) μ‖ ≤ K₀ / B := by
            intro μ
            rw [deriv_coe_cutoff τ B hτpos hBpos, Complex.norm_real, Real.norm_eq_abs]
            exact hcut.1 μ
          have hK2 : ∀ μ : ℝ,
              ‖deriv (deriv (fun x : ℝ => ((cutoff τ B x : ℝ) : ℂ))) μ‖ ≤ K₀ / B ^ 2 := by
            intro μ
            rw [deriv_deriv_coe_cutoff τ B hτpos hBpos, Complex.norm_real, Real.norm_eq_abs]
            exact hcut.2 μ
          -- 乘积界
          have hCd1nn : (0 : ℝ) ≤ 1200 * (q : ℝ) := by positivity
          have hCd2nn : (0 : ℝ) ≤ 10 ^ 7 * (q : ℝ) ^ 2 := by positivity
          have hM1' : τ * M₁ ≤ (1200 * (q : ℝ)) * (q : ℝ) * E := by
            have h := hM1sh
            have heq : (1200 : ℝ) * (q : ℝ) ^ 2 * E = (1200 * (q : ℝ)) * (q : ℝ) * E := by ring
            rw [heq] at h
            exact h
          have hM2' : τ ^ 2 * M₂ ≤ (10 ^ 7 * (q : ℝ) ^ 2) * (q : ℝ) ^ 2 * E := by
            have h := hM2sh
            have heq : (10 ^ 7 : ℝ) * (q : ℝ) ^ 4 * E
                = (10 ^ 7 * (q : ℝ) ^ 2) * (q : ℝ) ^ 2 * E := by ring
            rw [heq] at h
            exact h
          have hBτ : B ≤ τ := by
            rw [hBdef, div_le_iff₀ (by positivity : (0 : ℝ) < (q : ℝ) ^ 2)]
            have h1 : (1 : ℝ) ≤ (q : ℝ) ^ 2 := by nlinarith [hq4r]
            nlinarith [h1, hτpos]
          have hprod := kernelProd_le_poly_quad (q := (q : ℝ)) (k := q)
            (scaledApprox τ q) hτpos hBpos hEnn hKnn hCd1nn hCd2nn hM₁nn hM₂nn
            hq1r (le_refl (q : ℝ)) hBτ (by rw [hBdef]) hM1' hM2' hψ hPε hMA1' hMA2' hK1 hK2
          have hcoef : (1 / 36) * (1 + 1200 * (q : ℝ))
                * (16 * (10 ^ 7 * (q : ℝ) ^ 2) + 32 * (1200 * (q : ℝ)) * K₀ + 16 * K₀)
                * (q : ℝ) ^ 2 ≤ 6 * 10 ^ 9 * (q : ℝ) ^ 5 := by
            have hK0 : K₀ = 21.1 := rfl
            rw [hK0]
            have ha : 810240 * (q : ℝ) ≤ 202560 * (q : ℝ) ^ 2 := by nlinarith [hq4r]
            have hb : (337.6 : ℝ) ≤ 21.1 * (q : ℝ) ^ 2 := by nlinarith [hq4r]
            have hc : (1 : ℝ) + 1200 * (q : ℝ) ≤ 1201 * (q : ℝ) := by nlinarith [hq4r]
            nlinarith [ha, hb, hc, hq4r, sq_nonneg (q : ℝ), pow_pos hq0 2, pow_pos hq0 5]
          have h2 : kernelA τ B (scaledApprox τ q) * kernelC τ B (scaledApprox τ q)
              ≤ 6 * 10 ^ 9 * (q : ℝ) ^ 5 * E ^ 2 := by
            refine hprod.trans ?_
            have hcoef' : (1 / 36) * (1 + 1200 * (q : ℝ))
                  * (16 * (10 ^ 7 * (q : ℝ) ^ 2) + 32 * (1200 * (q : ℝ)) * K₀ + 16 * K₀)
                  * (q : ℝ) ^ 2 * E ^ 2 ≤ 6 * 10 ^ 9 * (q : ℝ) ^ 5 * E ^ 2 :=
              mul_le_mul_of_nonneg_right hcoef (by positivity)
            linarith [hcoef']
          -- 装配
          have hmain : h L α θ 0 ≤ 8 * Real.sqrt
              (kernelA τ B (scaledApprox τ q) * kernelC τ B (scaledApprox τ q)) := by
            have h0 := h_zero_le_of_kernel (N := N) (φ := φ) (L := L) (α := α) (θ := θ) hAdm
              (B := B) (ε := E) (by rw [← hτdef]; exact hτpos) hEpos hBpos (by
                intro μ hμ
                rw [← hτdef] at hμ
                have h := hPε μ hμ
                simpa [hτdef, hqdef] using h)
            simpa [hτdef, hqdef] using h0
          have h3 : 2 * s ^ 2 ≤ h L α θ 0 := by
            have h := two_mul_sin_sq_le_h_zero N L α θ hφ0 hφπ hAdm
            rw [← hsdef] at h
            exact h
          calc 2 * s ^ 2 ≤ h L α θ 0 := h3
            _ ≤ 8 * Real.sqrt (kernelA τ B (scaledApprox τ q) * kernelC τ B (scaledApprox τ q)) :=
                hmain
            _ ≤ 8 * Real.sqrt (6 * 10 ^ 9 * (q : ℝ) ^ 5 * E ^ 2) :=
                mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h2) (by norm_num)
        exact final_compare hτpos hq4 hsnn hs1 (by simpa [hEdef] using hkey)
      · -- Case II：τ > q（平凡分支）
        have hτq' : (q : ℝ) < τ := by
          have h := hcase
          push_neg at h
          exact h
        have hfac := factorial_le_two_mul_exp_mul q hq1
        have hs4le : s ^ 4 ≤ 1 := by nlinarith [hs2le1]
        have hstep1 : (Nat.factorial q : ℝ) * s ^ 4 ≤ (Nat.factorial q : ℝ) := by
          have h1 : (0 : ℝ) ≤ (Nat.factorial q : ℝ) := by positivity
          nlinarith [hs4le, h1]
        have h4 : 2 * Real.exp 1 * (q : ℝ) ≤ 10 ^ 8 * (q : ℝ) ^ 4 := by
          have h5 : 2 * Real.exp 1 ≤ 10 ^ 8 * (q : ℝ) ^ 3 := by
            have h6 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
            have h7 : (4 : ℝ) ^ 3 ≤ (q : ℝ) ^ 3 :=
              pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) hq4r 3
            norm_num at h7
            nlinarith [h6, h7]
          nlinarith [h5, hq0]
        have hstep2 : 2 * Real.exp 1 * (q : ℝ) * ((q : ℝ) / 2) ^ q
            ≤ ((q : ℝ) / 2) ^ q * (10 ^ 8 * (q : ℝ) ^ 4) := by
          calc 2 * Real.exp 1 * (q : ℝ) * ((q : ℝ) / 2) ^ q
              ≤ (10 ^ 8 * (q : ℝ) ^ 4) * ((q : ℝ) / 2) ^ q :=
                mul_le_mul_of_nonneg_right h4 (by positivity)
            _ = ((q : ℝ) / 2) ^ q * (10 ^ 8 * (q : ℝ) ^ 4) := by ring
        have h3 : (Nat.factorial q : ℝ) * s ^ 4 / (10 ^ 8 * (q : ℝ) ^ 4) ≤ ((q : ℝ) / 2) ^ q := by
          rw [div_le_iff₀ (by positivity : (0 : ℝ) < 10 ^ 8 * (q : ℝ) ^ 4)]
          linarith [hstep1, hfac, hstep2]
        have h2 : ((q : ℝ) / 2) ^ q ≤ (τ / 2) ^ q :=
          pow_le_pow_left₀ (by positivity) (by linarith) q
        linarith [h2, h3]
    have hXnn : 0 ≤ (Nat.factorial q : ℝ) * s ^ 4 / (10 ^ 8 * (q : ℝ) ^ 4) := by positivity
    have hroot : ((Nat.factorial q : ℝ) * s ^ 4 / (10 ^ 8 * (q : ℝ) ^ 4)) ^ (1 / (q : ℝ))
        ≤ τ / 2 := by
      calc ((Nat.factorial q : ℝ) * s ^ 4 / (10 ^ 8 * (q : ℝ) ^ 4)) ^ (1 / (q : ℝ))
          ≤ (((τ / 2) ^ q)) ^ (1 / (q : ℝ)) := Real.rpow_le_rpow hXnn hX (by positivity)
        _ = τ / 2 := by
            rw [← Real.rpow_natCast (τ / 2) q,
              ← Real.rpow_mul (div_nonneg hτpos.le (by norm_num) : (0 : ℝ) ≤ τ / 2),
              mul_one_div, div_self (by positivity : (q : ℝ) ≠ 0), Real.rpow_one]
    calc 4 * ((Nat.factorial q : ℝ) * s ^ 4 / (10 ^ 8 * (q : ℝ) ^ 4)) ^ (1 / (q : ℝ))
        ≤ 4 * (τ / 2) := by linarith
      _ = cost θ := by rw [hcost]; ring

end RobustZ
