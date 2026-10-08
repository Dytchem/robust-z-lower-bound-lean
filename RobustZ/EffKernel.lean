import RobustZ.M5Sqrt

/-!
# `EffKernel`：参数化指数（`k²` / `k^b`）的 `B = √ε` 乘积界

`M5Sqrt.kernelProd_le_poly_sqrt` 用的两条锐化输入是

```
τ·M₁ ≤ Cd1·k·ε,      τ²·M₂ ≤ Cd2·k²·ε
```

（`ε`-线性，系数是 `k` 的一次/二次）。**并行推进的 workstream A** 产出的 sharp collar 界
形状略有不同：

```
sup‖Q'‖  ≤ Cd1·(k²/τ)·ε,      sup‖Q''‖ ≤ Cd2·(k^b/τ²)·ε
```

即 `τ·M₁ ≤ Cd1·k²·ε`、`τ²·M₂ ≤ Cd2·k^b·ε`（`b = 2` 或 `4`）。本文件把 `M5Sqrt` 的代数
**逐字重做**一遍：

**(0)** `B·M₁ ≤ Cd1·k²·ε·(B/τ) = Cd1·ε·(k²B/τ) ≤ Cd1·ε`（用侧条件 `hkB : k²B ≤ τ`）。
于是 `S := ε + B·M₁ ≤ (1+Cd1)·ε`。

**(1)** `kernelA_le_support` + `B ≤ τ`：`C₁ ≤ (2π)⁻¹·4τ·(1+Cd1)·ε`。

**(2)** `kernelC_le_support` 的三项：`2(τ+B)M₂ ≤ 4τM₂ ≤ 4·Cd2·k^b·ε/τ`、
`4K·M₁ ≤ 4·K·Cd1·k²·ε/τ`（出现两次）、`(ε+B·M₁)(4K/B) = 4K·B + 4K·M₁`。

**(3)** 相乘、`ε = B²` 展开：

```
(2π)²·C₁C₂ ≤ (1+Cd1)·(16·Cd2·k^b·B⁴ + 32·K·Cd1·k²·B⁴ + 16·K·τ·B³).
```

**(4)** 两条收尾路线：

* **有侧条件**（`hkB : k²B ≤ τ`、`hk2B : k^b·B ≤ τ`）：把 `B⁴` 拉平成 `τ·B³`，得
  `kernelA·kernelC ≤ sqrtC0 Cd1 Cd2 K · τ · ε^{3/2}`，
  `sqrtC0 Cd1 Cd2 K = (1/36)(1+Cd1)(16Cd2 + 32Cd1K + 16K)` —— 与 `M5Sqrt` 逐字相同。
* **无侧条件**（只有 `hkB`，不要求 `k^b·B ≤ τ`）：保留 `ε²` 项，
  `kernelA·kernelC ≤ (1/36)(1+Cd1)(16Cd2·k^b·ε² + 32KCd1·k²·ε² + 16K·τ·ε^{3/2})`。
  这条在应用里是**主力**：`k^b·B ≤ τ` 等价于 `(47/50)a^{3/2} ≥ b`，`b = 4` 时要求 `a ≥ 3.5`，
  代价太大；而 `ε²` 项配 `k^b ≤ q^b` 直接可用（见 `RobustZ/Effective.lean`）。

## 与 `M5Sqrt` 的关系

* `kernelProd_sqrt_param`：指数 `(k², k⁴)`、侧条件 `k²B ≤ τ`、`k⁴B ≤ τ`（题目要求的形状）。
* `kernelProd_sqrt_param_k2`：若 A 只给出 `τ²M₂ ≤ Cd2·k²·ε`（**更弱**的假设，故更好），
  在 `k ≥ 1` 时它蕴含 `k⁴` 版本，于是同一常数可用。
* `kernelProd_sqrt_param_nolift`：一般指数 `b`、**不要**第二条侧条件。
-/

set_option maxHeartbeats 1000000

noncomputable section

namespace RobustZ

open Filter MeasureTheory
open scoped Real

/-! ## §1 `C₂` 的公共上界（指数 `k²` / `k^b`） -/

/-- **`C₂` 的上界（`k²`/`k^b` 版）**：

```
C₂ ≤ (2π)⁻¹·(4·Cd2·k^b·ε/τ + 8·K·Cd1·k²·ε/τ + 4·K·B).
```

只用 `B ≤ τ`、`B = √ε`（给 `ε/B = B`）与两条锐化输入 `τM₁ ≤ Cd1k²ε`、`τ²M₂ ≤ Cd2k^bε`。 -/
lemma kernelC_le_sqrt_param_aux (α β : ℕ) {τ B ε M₁ M₂ K Cd1 Cd2 : ℝ} {k : ℕ}
    (P : Polynomial ℂ)
    (hτ : 0 < τ) (hB : 0 < B) (hε : 0 ≤ ε) (hK : 0 ≤ K)
    (_hCd1 : 0 ≤ Cd1) (_hCd2 : 0 ≤ Cd2) (hM₂nn : 0 ≤ M₂)
    (hBτ : B ≤ τ) (hBval : B = Real.sqrt ε)
    (hM1sharp : τ * M₁ ≤ Cd1 * (k : ℝ) ^ α * ε)
    (hM2sharp : τ ^ 2 * M₂ ≤ Cd2 * (k : ℝ) ^ β * ε)
    (hPε : ∀ μ : ℝ, |μ| ≤ τ →
      ‖Complex.exp (-(μ : ℂ) * Complex.I) - P.eval ((μ : ℂ))‖ ≤ ε)
    (hA1 : ∀ μ : ℝ, |μ| ≤ τ + B → ‖deriv (fun x : ℝ => psiA P x) μ‖ ≤ M₁)
    (hA2 : ∀ μ : ℝ, |μ| ≤ τ + B → ‖deriv (deriv (fun x : ℝ => psiA P x)) μ‖ ≤ M₂)
    (hK1 : ∀ μ : ℝ, ‖deriv (fun x : ℝ => ((cutoff τ B x : ℝ) : ℂ)) μ‖ ≤ K / B)
    (hK2 : ∀ μ : ℝ, ‖deriv (deriv (fun x : ℝ => ((cutoff τ B x : ℝ) : ℂ))) μ‖ ≤ K / B ^ 2) :
    kernelC τ B P ≤ (2 * Real.pi)⁻¹ *
      (4 * Cd2 * (k : ℝ) ^ β * ε / τ + 8 * K * Cd1 * (k : ℝ) ^ α * ε / τ + 4 * K * B) := by
  have hBB : B * B = ε := by
    rw [hBval]
    simpa [pow_two] using Real.sq_sqrt hε
  have hεB : ε / B = B := by
    rw [div_eq_iff hB.ne']
    exact hBB.symm
  have hM1le : M₁ ≤ Cd1 * (k : ℝ) ^ α * ε / τ := by
    rw [le_div_iff₀ hτ]
    calc M₁ * τ = τ * M₁ := by ring
      _ ≤ Cd1 * (k : ℝ) ^ α * ε := hM1sharp
  have hM2le : M₂ ≤ Cd2 * (k : ℝ) ^ β * ε / τ ^ 2 := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < τ ^ 2)]
    calc M₂ * τ ^ 2 = τ ^ 2 * M₂ := by ring
      _ ≤ Cd2 * (k : ℝ) ^ β * ε := hM2sharp
  refine (kernelC_le_support hτ hB P hε hPε hA1 hA2 hK1 hK2).trans ?_
  have hcoef : (0 : ℝ) < (2 * Real.pi)⁻¹ := by positivity
  have h1 : 2 * (τ + B) * M₂ ≤ 4 * Cd2 * (k : ℝ) ^ β * ε / τ := by
    have ha : 2 * (τ + B) * M₂ ≤ 4 * τ * M₂ := by nlinarith [hBτ, hM₂nn, hτ]
    have hb : 4 * τ * M₂ ≤ 4 * τ * (Cd2 * (k : ℝ) ^ β * ε / τ ^ 2) :=
      mul_le_mul_of_nonneg_left hM2le (by linarith)
    have hc : 4 * τ * (Cd2 * (k : ℝ) ^ β * ε / τ ^ 2) = 4 * Cd2 * (k : ℝ) ^ β * ε / τ := by
      field_simp
    linarith [ha, hb, hc]
  have hM1' : 4 * K * M₁ ≤ 4 * K * Cd1 * (k : ℝ) ^ α * ε / τ := by
    have h4K : (0 : ℝ) ≤ 4 * K := mul_nonneg (by norm_num) hK
    have h := mul_le_mul_of_nonneg_left hM1le h4K
    calc 4 * K * M₁ ≤ 4 * K * (Cd1 * (k : ℝ) ^ α * ε / τ) := h
      _ = 4 * K * Cd1 * (k : ℝ) ^ α * ε / τ := by ring
  have h3 : (ε + B * M₁) * (4 * K / B) = 4 * K * B + 4 * K * M₁ := by
    have h4 : (ε + B * M₁) * (4 * K / B) = ε * (4 * K / B) + B * M₁ * (4 * K / B) := by
      ring
    have h5 : ε * (4 * K / B) = 4 * K * (ε / B) := by ring
    have h6 : B * M₁ * (4 * K / B) = 4 * K * M₁ := by field_simp
    have h7 : 4 * K * (ε / B) = 4 * K * B := by rw [hεB]
    linarith [h4, h5, h6, h7]
  have h2 : 2 * (M₁ * (2 * K)) = 4 * K * M₁ := by ring
  have hsum : 2 * (τ + B) * M₂ + 2 * (M₁ * (2 * K)) + (ε + B * M₁) * (4 * K / B)
      ≤ 4 * Cd2 * (k : ℝ) ^ β * ε / τ + 8 * K * Cd1 * (k : ℝ) ^ α * ε / τ + 4 * K * B := by
    have h9 : 4 * K * Cd1 * (k : ℝ) ^ α * ε / τ + 4 * K * Cd1 * (k : ℝ) ^ α * ε / τ
        = 8 * K * Cd1 * (k : ℝ) ^ α * ε / τ := by ring
    linarith [h1, h2, h3, hM1', h9]
  exact mul_le_mul_of_nonneg_left hsum hcoef.le

/-! ## §2 有侧条件的主引理（指数 `k²` / `k^b`，常数与 `k` 无关） -/

/-- **核心（有侧条件）**：`B = √ε`、锐化输入 `τM₁ ≤ Cd1·k²·ε`、`τ²M₂ ≤ Cd2·k^b·ε`、
侧条件 `hkB : k²·B ≤ τ`、`hk2B : k^b·B ≤ τ` 时的乘积界。

结论与 `M5Sqrt.kernelProd_le_poly_sqrt` **逐字相同**（常数 `sqrtC0 Cd1 Cd2 K` 不含 `k`）。 -/
lemma kernelProd_sqrt_param_gen (α β : ℕ) {τ B ε M₁ M₂ K Cd1 Cd2 : ℝ} {k : ℕ}
    (P : Polynomial ℂ)
    (hτ : 0 < τ) (hB : 0 < B) (hε : 0 ≤ ε) (hK : 0 ≤ K)
    (hCd1 : 0 ≤ Cd1) (hCd2 : 0 ≤ Cd2)
    (hM₁nn : 0 ≤ M₁) (hM₂nn : 0 ≤ M₂)
    (hBτ : B ≤ τ) (hkB : (k : ℝ) ^ α * B ≤ τ) (hk2B : (k : ℝ) ^ β * B ≤ τ)
    (hBval : B = Real.sqrt ε)
    (hM1sharp : τ * M₁ ≤ Cd1 * (k : ℝ) ^ α * ε)
    (hM2sharp : τ ^ 2 * M₂ ≤ Cd2 * (k : ℝ) ^ β * ε)
    (hψ : ∀ μ : ℝ, ‖psi τ B P μ‖ ≤ ε + B * M₁)
    (hPε : ∀ μ : ℝ, |μ| ≤ τ →
      ‖Complex.exp (-(μ : ℂ) * Complex.I) - P.eval ((μ : ℂ))‖ ≤ ε)
    (hA1 : ∀ μ : ℝ, |μ| ≤ τ + B → ‖deriv (fun x : ℝ => psiA P x) μ‖ ≤ M₁)
    (hA2 : ∀ μ : ℝ, |μ| ≤ τ + B → ‖deriv (deriv (fun x : ℝ => psiA P x)) μ‖ ≤ M₂)
    (hK1 : ∀ μ : ℝ, ‖deriv (fun x : ℝ => ((cutoff τ B x : ℝ) : ℂ)) μ‖ ≤ K / B)
    (hK2 : ∀ μ : ℝ, ‖deriv (deriv (fun x : ℝ => ((cutoff τ B x : ℝ) : ℂ))) μ‖ ≤ K / B ^ 2) :
    kernelA τ B P * kernelC τ B P ≤ sqrtC0 Cd1 Cd2 K * τ * ε ^ (3 / 2 : ℝ) := by
  -- ### (0) `B·B = ε`、`B³ = ε^{3/2}`、`ε/B = B`、`B·M₁ ≤ Cd1·ε`
  have hBB : B * B = ε := by
    rw [hBval]
    simpa [pow_two] using Real.sq_sqrt hε
  have hB3 : B ^ 3 = ε ^ (3 / 2 : ℝ) := by
    rw [rpow_three_halves_eq_sqrt_cube hε, ← hBval]
  have hεB : ε / B = B := by
    rw [div_eq_iff hB.ne']
    exact hBB.symm
  have hM1le : M₁ ≤ Cd1 * (k : ℝ) ^ α * ε / τ := by
    rw [le_div_iff₀ hτ]
    calc M₁ * τ = τ * M₁ := by ring
      _ ≤ Cd1 * (k : ℝ) ^ α * ε := hM1sharp
  have hBM1 : B * M₁ ≤ Cd1 * ε := by
    have h1 : B * M₁ ≤ B * (Cd1 * (k : ℝ) ^ α * ε / τ) := mul_le_mul_of_nonneg_left hM1le hB.le
    have h2 : B * (Cd1 * (k : ℝ) ^ α * ε / τ) = Cd1 * ε * ((k : ℝ) ^ α * B / τ) := by
      field_simp
    have h3 : (k : ℝ) ^ α * B / τ ≤ 1 := by
      rw [div_le_one hτ]
      exact hkB
    have h4 : Cd1 * ε * ((k : ℝ) ^ α * B / τ) ≤ Cd1 * ε * 1 :=
      mul_le_mul_of_nonneg_left h3 (mul_nonneg hCd1 hε)
    linarith [h1, h2, h4]
  have hS : ε + B * M₁ ≤ (1 + Cd1) * ε := by linarith [hBM1, hε]
  have hSnn : 0 ≤ ε + B * M₁ := by
    have h := mul_nonneg hB.le hM₁nn
    linarith [hε]
  -- ### (1) `C₁ ≤ (2π)⁻¹·4τ·(1+Cd1)·ε`
  have hC1 : kernelA τ B P ≤ (2 * Real.pi)⁻¹ * (4 * τ * ((1 + Cd1) * ε)) := by
    refine (kernelA_le_support hτ hB P hψ).trans ?_
    have hcoef : (0 : ℝ) < (2 * Real.pi)⁻¹ := by positivity
    have h1 : 2 * (τ + B) ≤ 4 * τ := by linarith
    have h3 : 2 * (τ + B) * (ε + B * M₁) ≤ 4 * τ * (ε + B * M₁) :=
      mul_le_mul_of_nonneg_right h1 hSnn
    have h4 : 4 * τ * (ε + B * M₁) ≤ 4 * τ * ((1 + Cd1) * ε) :=
      mul_le_mul_of_nonneg_left hS (by linarith)
    have h5 : 2 * (τ + B) * (ε + B * M₁) ≤ 4 * τ * ((1 + Cd1) * ε) := by linarith [h3, h4]
    calc (2 * Real.pi)⁻¹ * (2 * (τ + B)) * (ε + B * M₁)
        = (2 * Real.pi)⁻¹ * (2 * (τ + B) * (ε + B * M₁)) := by ring
      _ ≤ (2 * Real.pi)⁻¹ * (4 * τ * ((1 + Cd1) * ε)) := mul_le_mul_of_nonneg_left h5 hcoef.le
  -- ### (2) `C₂`（公共引理）
  have hC2 := kernelC_le_sqrt_param_aux α β P hτ hB hε hK hCd1 hCd2 hM₂nn hBτ hBval hM1sharp
    hM2sharp hPε hA1 hA2 hK1 hK2
  -- ### (3) 相乘、展开
  have hC2nn : 0 ≤ kernelC τ B P := kernelC_nonneg hτ hB P
  have hC1rhs : 0 ≤ (2 * Real.pi)⁻¹ * (4 * τ * ((1 + Cd1) * ε)) :=
    mul_nonneg (by positivity)
      (mul_nonneg (mul_nonneg (by norm_num) hτ.le) (mul_nonneg (by linarith) hε))
  have hprod : kernelA τ B P * kernelC τ B P
      ≤ (2 * Real.pi)⁻¹ * (4 * τ * ((1 + Cd1) * ε))
        * ((2 * Real.pi)⁻¹ *
          (4 * Cd2 * (k : ℝ) ^ β * ε / τ + 8 * K * Cd1 * (k : ℝ) ^ α * ε / τ + 4 * K * B)) :=
    mul_le_mul hC1 hC2 hC2nn hC1rhs
  refine hprod.trans ?_
  have hstep1 : (2 * Real.pi)⁻¹ * (4 * τ * ((1 + Cd1) * ε))
        * ((2 * Real.pi)⁻¹ *
          (4 * Cd2 * (k : ℝ) ^ β * ε / τ + 8 * K * Cd1 * (k : ℝ) ^ α * ε / τ + 4 * K * B))
      = (2 * Real.pi)⁻¹ * (2 * Real.pi)⁻¹
        * ((4 * τ * ((1 + Cd1) * ε))
          * (4 * Cd2 * (k : ℝ) ^ β * ε / τ + 8 * K * Cd1 * (k : ℝ) ^ α * ε / τ
            + 4 * K * B)) := by
    ring
  rw [hstep1]
  have hstep2 : (4 * τ * ((1 + Cd1) * ε))
        * (4 * Cd2 * (k : ℝ) ^ β * ε / τ + 8 * K * Cd1 * (k : ℝ) ^ α * ε / τ + 4 * K * B)
      = (1 + Cd1) * (16 * Cd2 * (k : ℝ) ^ β * B ^ 4 + 32 * K * Cd1 * (k : ℝ) ^ α * B ^ 4
          + 16 * K * τ * B ^ 3) := by
    rw [← hBB]
    field_simp
    try ring
  rw [hstep2]
  -- ### (4) 拉平 `B⁴ → τB³`（用 `hkB`、`hk2B`）
  have hkey : 16 * Cd2 * (k : ℝ) ^ β * B ^ 4 + 32 * K * Cd1 * (k : ℝ) ^ α * B ^ 4
        + 16 * K * τ * B ^ 3
      ≤ (16 * Cd2 + 32 * Cd1 * K + 16 * K) * (τ * B ^ 3) := by
    have hB3nn : (0 : ℝ) ≤ B ^ 3 := pow_nonneg hB.le 3
    have hk2 : (k : ℝ) ^ β * B ^ 4 ≤ τ * B ^ 3 := by
      have h := mul_le_mul_of_nonneg_right hk2B hB3nn
      calc (k : ℝ) ^ β * B ^ 4 = ((k : ℝ) ^ β * B) * B ^ 3 := by ring
        _ ≤ τ * B ^ 3 := h
    have hk1 : (k : ℝ) ^ α * B ^ 4 ≤ τ * B ^ 3 := by
      have h := mul_le_mul_of_nonneg_right hkB hB3nn
      calc (k : ℝ) ^ α * B ^ 4 = ((k : ℝ) ^ α * B) * B ^ 3 := by ring
        _ ≤ τ * B ^ 3 := h
    have hA : 16 * Cd2 * (k : ℝ) ^ β * B ^ 4 ≤ 16 * Cd2 * (τ * B ^ 3) := by
      calc 16 * Cd2 * (k : ℝ) ^ β * B ^ 4 = (16 * Cd2) * ((k : ℝ) ^ β * B ^ 4) := by ring
        _ ≤ (16 * Cd2) * (τ * B ^ 3) :=
            mul_le_mul_of_nonneg_left hk2 (mul_nonneg (by norm_num) hCd2)
    have hB' : 32 * K * Cd1 * (k : ℝ) ^ α * B ^ 4 ≤ 32 * K * Cd1 * (τ * B ^ 3) := by
      calc 32 * K * Cd1 * (k : ℝ) ^ α * B ^ 4 = (32 * K * Cd1) * ((k : ℝ) ^ α * B ^ 4) := by ring
        _ ≤ (32 * K * Cd1) * (τ * B ^ 3) :=
            mul_le_mul_of_nonneg_left hk1 (mul_nonneg (mul_nonneg (by norm_num) hK) hCd1)
    have hC' : 16 * K * τ * B ^ 3 = 16 * K * (τ * B ^ 3) := by ring
    have hsum := add_le_add (add_le_add hA hB') (le_of_eq hC')
    calc 16 * Cd2 * (k : ℝ) ^ β * B ^ 4 + 32 * K * Cd1 * (k : ℝ) ^ α * B ^ 4
          + 16 * K * τ * B ^ 3
        = (16 * Cd2 * (k : ℝ) ^ β * B ^ 4 + 32 * K * Cd1 * (k : ℝ) ^ α * B ^ 4)
          + 16 * K * τ * B ^ 3 := by ring
      _ ≤ (16 * Cd2 * (τ * B ^ 3) + 32 * K * Cd1 * (τ * B ^ 3)) + 16 * K * (τ * B ^ 3) := hsum
      _ = (16 * Cd2 + 32 * Cd1 * K + 16 * K) * (τ * B ^ 3) := by ring
  have hX1nn : (0 : ℝ) ≤ 16 * Cd2 * (k : ℝ) ^ β * B ^ 4 + 32 * K * Cd1 * (k : ℝ) ^ α * B ^ 4
      + 16 * K * τ * B ^ 3 := by
    have h1 : (0 : ℝ) ≤ 16 * Cd2 * (k : ℝ) ^ β * B ^ 4 := by positivity
    have h2 : (0 : ℝ) ≤ 32 * K * Cd1 * (k : ℝ) ^ α * B ^ 4 := by positivity
    have h3 : (0 : ℝ) ≤ 16 * K * τ * B ^ 3 := by positivity
    linarith
  -- ### (5) 取 `(2π)⁻² ≤ 1/36`
  have hfinal : (2 * Real.pi)⁻¹ * (2 * Real.pi)⁻¹
        * ((1 + Cd1) * (16 * Cd2 * (k : ℝ) ^ β * B ^ 4 + 32 * K * Cd1 * (k : ℝ) ^ α * B ^ 4
          + 16 * K * τ * B ^ 3))
      ≤ (1 / 36 : ℝ) * (1 + Cd1) * (16 * Cd2 + 32 * Cd1 * K + 16 * K) * τ * ε ^ (3 / 2 : ℝ) := by
    have hcoef : (2 * Real.pi)⁻¹ * (2 * Real.pi)⁻¹ ≤ 1 / 36 := inv_two_pi_sq_le
    calc ((2 * Real.pi)⁻¹ * (2 * Real.pi)⁻¹)
          * ((1 + Cd1) * (16 * Cd2 * (k : ℝ) ^ β * B ^ 4 + 32 * K * Cd1 * (k : ℝ) ^ α * B ^ 4
            + 16 * K * τ * B ^ 3))
        ≤ (1 / 36) * ((1 + Cd1) * (16 * Cd2 * (k : ℝ) ^ β * B ^ 4
            + 32 * K * Cd1 * (k : ℝ) ^ α * B ^ 4 + 16 * K * τ * B ^ 3)) :=
          mul_le_mul_of_nonneg_right hcoef (mul_nonneg (by linarith) hX1nn)
      _ ≤ (1 / 36) * ((1 + Cd1) * ((16 * Cd2 + 32 * Cd1 * K + 16 * K) * (τ * B ^ 3))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hkey (by linarith)) (by norm_num)
      _ = (1 / 36 : ℝ) * (1 + Cd1) * (16 * Cd2 + 32 * Cd1 * K + 16 * K) * τ
            * ε ^ (3 / 2 : ℝ) := by
          rw [hB3]
          ring
  simpa only [sqrtC0] using hfinal

/-- **题目要求的形状**：指数 `(k², k⁴)`，侧条件 `k²B ≤ τ`、`k⁴B ≤ τ`。 -/
lemma kernelProd_sqrt_param {τ B ε M₁ M₂ K Cd1 Cd2 : ℝ} {k : ℕ} (P : Polynomial ℂ)
    (hτ : 0 < τ) (hB : 0 < B) (hε : 0 ≤ ε) (hK : 0 ≤ K)
    (hCd1 : 0 ≤ Cd1) (hCd2 : 0 ≤ Cd2)
    (hM₁nn : 0 ≤ M₁) (hM₂nn : 0 ≤ M₂)
    (hBτ : B ≤ τ) (hkB : (k : ℝ) ^ 2 * B ≤ τ) (hk2B : (k : ℝ) ^ 4 * B ≤ τ)
    (hBval : B = Real.sqrt ε)
    (hM1sharp : τ * M₁ ≤ Cd1 * (k : ℝ) ^ 2 * ε)
    (hM2sharp : τ ^ 2 * M₂ ≤ Cd2 * (k : ℝ) ^ 4 * ε)
    (hψ : ∀ μ : ℝ, ‖psi τ B P μ‖ ≤ ε + B * M₁)
    (hPε : ∀ μ : ℝ, |μ| ≤ τ →
      ‖Complex.exp (-(μ : ℂ) * Complex.I) - P.eval ((μ : ℂ))‖ ≤ ε)
    (hA1 : ∀ μ : ℝ, |μ| ≤ τ + B → ‖deriv (fun x : ℝ => psiA P x) μ‖ ≤ M₁)
    (hA2 : ∀ μ : ℝ, |μ| ≤ τ + B → ‖deriv (deriv (fun x : ℝ => psiA P x)) μ‖ ≤ M₂)
    (hK1 : ∀ μ : ℝ, ‖deriv (fun x : ℝ => ((cutoff τ B x : ℝ) : ℂ)) μ‖ ≤ K / B)
    (hK2 : ∀ μ : ℝ, ‖deriv (deriv (fun x : ℝ => ((cutoff τ B x : ℝ) : ℂ))) μ‖ ≤ K / B ^ 2) :
    kernelA τ B P * kernelC τ B P ≤ sqrtC0 Cd1 Cd2 K * τ * ε ^ (3 / 2 : ℝ) :=
  kernelProd_sqrt_param_gen 2 4 P hτ hB hε hK hCd1 hCd2 hM₁nn hM₂nn hBτ hkB hk2B hBval
    hM1sharp hM2sharp hψ hPε hA1 hA2 hK1 hK2

/-! ## §3 备用形状：A 只给出 `τ²M₂ ≤ Cd2·k²·ε`（更弱的假设） -/

/-- **`τ²M₂ ≤ Cd2·k²·ε` 版本**（指数 `(α, β) = (2, 2)`）：`k ≥ 1` 时 `k²ε ≤ k⁴ε`，
故它是 `kernelProd_sqrt_param` 的 `k⁴` 假设的**充分条件**，同一常数直接可用。 -/
lemma kernelProd_sqrt_param_k2 {τ B ε M₁ M₂ K Cd1 Cd2 : ℝ} {k : ℕ} (P : Polynomial ℂ)
    (hτ : 0 < τ) (hB : 0 < B) (hε : 0 ≤ ε) (hK : 0 ≤ K)
    (hCd1 : 0 ≤ Cd1) (hCd2 : 0 ≤ Cd2)
    (hM₁nn : 0 ≤ M₁) (hM₂nn : 0 ≤ M₂) (hk1 : 1 ≤ k)
    (hBτ : B ≤ τ) (hkB : (k : ℝ) ^ 2 * B ≤ τ) (hk2B : (k : ℝ) ^ 4 * B ≤ τ)
    (hBval : B = Real.sqrt ε)
    (hM1sharp : τ * M₁ ≤ Cd1 * (k : ℝ) ^ 2 * ε)
    (hM2sharp : τ ^ 2 * M₂ ≤ Cd2 * (k : ℝ) ^ 2 * ε)
    (hψ : ∀ μ : ℝ, ‖psi τ B P μ‖ ≤ ε + B * M₁)
    (hPε : ∀ μ : ℝ, |μ| ≤ τ →
      ‖Complex.exp (-(μ : ℂ) * Complex.I) - P.eval ((μ : ℂ))‖ ≤ ε)
    (hA1 : ∀ μ : ℝ, |μ| ≤ τ + B → ‖deriv (fun x : ℝ => psiA P x) μ‖ ≤ M₁)
    (hA2 : ∀ μ : ℝ, |μ| ≤ τ + B → ‖deriv (deriv (fun x : ℝ => psiA P x)) μ‖ ≤ M₂)
    (hK1 : ∀ μ : ℝ, ‖deriv (fun x : ℝ => ((cutoff τ B x : ℝ) : ℂ)) μ‖ ≤ K / B)
    (hK2 : ∀ μ : ℝ, ‖deriv (deriv (fun x : ℝ => ((cutoff τ B x : ℝ) : ℂ))) μ‖ ≤ K / B ^ 2) :
    kernelA τ B P * kernelC τ B P ≤ sqrtC0 Cd1 Cd2 K * τ * ε ^ (3 / 2 : ℝ) := by
  have hk1' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
  have h24 : (k : ℝ) ^ 2 ≤ (k : ℝ) ^ 4 := pow_le_pow_right₀ hk1' (by norm_num)
  have hmono : (k : ℝ) ^ 2 * ε ≤ (k : ℝ) ^ 4 * ε :=
    mul_le_mul_of_nonneg_right h24 hε
  refine kernelProd_sqrt_param P hτ hB hε hK hCd1 hCd2 hM₁nn hM₂nn hBτ hkB hk2B hBval
    hM1sharp ?_ hψ hPε hA1 hA2 hK1 hK2
  calc τ ^ 2 * M₂ ≤ Cd2 * (k : ℝ) ^ 2 * ε := hM2sharp
    _ = Cd2 * ((k : ℝ) ^ 2 * ε) := by ring
    _ ≤ Cd2 * ((k : ℝ) ^ 4 * ε) := mul_le_mul_of_nonneg_left hmono hCd2
    _ = Cd2 * (k : ℝ) ^ 4 * ε := by ring

/-! ## §4 无侧条件的主引理（保留 `ε²` 项；应用里的主力） -/

/-- **核心（无侧条件）**：只有 `hkB : k²·B ≤ τ`，**不要** `k^b·B ≤ τ`。代价是保留 `ε²` 项：

```
C₁C₂ ≤ (1/36)(1+Cd1)(16·Cd2·k^b·ε² + 32·K·Cd1·k²·ε² + 16·K·τ·ε^{3/2}).
```

推导：`(2π)²C₁C₂ ≤ (1+Cd1)(16Cd2k^b B⁴ + 32KCd1k²B⁴ + 16KτB³)`，再用
`B⁴ = ε²`、`B³ = ε^{3/2}`（`B = √ε`）即可，**无需**任何把 `B⁴` 拉平成 `τB³` 的假设。

应用（`RobustZ/Effective.lean`）：`k ≤ q`、`τ ≤ q` 后三项分别是
`q^{b+2/3-2s}`、`q^{8/3-2s}`、`q^{3/2-3s/2}`（`s = (47/50)a^{3/2}`），
只有第一项在 `b = 4` 时需要 `s > 7/3`（即 `a > 1.834`），比侧条件 `k⁴B ≤ τ`
（等价于 `s ≥ 6`，即 `a ≥ 3.44`）宽松得多。 -/
lemma kernelProd_sqrt_param_nolift (α β : ℕ) {τ B ε M₁ M₂ K Cd1 Cd2 : ℝ} {k : ℕ}
    (P : Polynomial ℂ)
    (hτ : 0 < τ) (hB : 0 < B) (hε : 0 ≤ ε) (hK : 0 ≤ K)
    (hCd1 : 0 ≤ Cd1) (hCd2 : 0 ≤ Cd2)
    (hM₁nn : 0 ≤ M₁) (hM₂nn : 0 ≤ M₂)
    (hBτ : B ≤ τ) (hkB : (k : ℝ) ^ α * B ≤ τ)
    (hBval : B = Real.sqrt ε)
    (hM1sharp : τ * M₁ ≤ Cd1 * (k : ℝ) ^ α * ε)
    (hM2sharp : τ ^ 2 * M₂ ≤ Cd2 * (k : ℝ) ^ β * ε)
    (hψ : ∀ μ : ℝ, ‖psi τ B P μ‖ ≤ ε + B * M₁)
    (hPε : ∀ μ : ℝ, |μ| ≤ τ →
      ‖Complex.exp (-(μ : ℂ) * Complex.I) - P.eval ((μ : ℂ))‖ ≤ ε)
    (hA1 : ∀ μ : ℝ, |μ| ≤ τ + B → ‖deriv (fun x : ℝ => psiA P x) μ‖ ≤ M₁)
    (hA2 : ∀ μ : ℝ, |μ| ≤ τ + B → ‖deriv (deriv (fun x : ℝ => psiA P x)) μ‖ ≤ M₂)
    (hK1 : ∀ μ : ℝ, ‖deriv (fun x : ℝ => ((cutoff τ B x : ℝ) : ℂ)) μ‖ ≤ K / B)
    (hK2 : ∀ μ : ℝ, ‖deriv (deriv (fun x : ℝ => ((cutoff τ B x : ℝ) : ℂ))) μ‖ ≤ K / B ^ 2) :
    kernelA τ B P * kernelC τ B P ≤ (1 / 36) * (1 + Cd1)
      * (16 * Cd2 * (k : ℝ) ^ β * ε ^ 2 + 32 * K * Cd1 * (k : ℝ) ^ α * ε ^ 2
        + 16 * K * τ * ε ^ (3 / 2 : ℝ)) := by
  have hBB : B * B = ε := by
    rw [hBval]
    simpa [pow_two] using Real.sq_sqrt hε
  have hB3 : B ^ 3 = ε ^ (3 / 2 : ℝ) := by
    rw [rpow_three_halves_eq_sqrt_cube hε, ← hBval]
  have hB4 : B ^ 4 = ε ^ 2 := by
    calc B ^ 4 = (B * B) ^ 2 := by ring
      _ = ε ^ 2 := by rw [hBB]
  have hεB : ε / B = B := by
    rw [div_eq_iff hB.ne']
    exact hBB.symm
  have hM1le : M₁ ≤ Cd1 * (k : ℝ) ^ α * ε / τ := by
    rw [le_div_iff₀ hτ]
    calc M₁ * τ = τ * M₁ := by ring
      _ ≤ Cd1 * (k : ℝ) ^ α * ε := hM1sharp
  have hBM1 : B * M₁ ≤ Cd1 * ε := by
    have h1 : B * M₁ ≤ B * (Cd1 * (k : ℝ) ^ α * ε / τ) := mul_le_mul_of_nonneg_left hM1le hB.le
    have h2 : B * (Cd1 * (k : ℝ) ^ α * ε / τ) = Cd1 * ε * ((k : ℝ) ^ α * B / τ) := by
      field_simp
    have h3 : (k : ℝ) ^ α * B / τ ≤ 1 := by
      rw [div_le_one hτ]
      exact hkB
    have h4 : Cd1 * ε * ((k : ℝ) ^ α * B / τ) ≤ Cd1 * ε * 1 :=
      mul_le_mul_of_nonneg_left h3 (mul_nonneg hCd1 hε)
    linarith [h1, h2, h4]
  have hS : ε + B * M₁ ≤ (1 + Cd1) * ε := by linarith [hBM1, hε]
  have hSnn : 0 ≤ ε + B * M₁ := by
    have h := mul_nonneg hB.le hM₁nn
    linarith [hε]
  have hC1 : kernelA τ B P ≤ (2 * Real.pi)⁻¹ * (4 * τ * ((1 + Cd1) * ε)) := by
    refine (kernelA_le_support hτ hB P hψ).trans ?_
    have hcoef : (0 : ℝ) < (2 * Real.pi)⁻¹ := by positivity
    have h1 : 2 * (τ + B) ≤ 4 * τ := by linarith
    have h3 : 2 * (τ + B) * (ε + B * M₁) ≤ 4 * τ * (ε + B * M₁) :=
      mul_le_mul_of_nonneg_right h1 hSnn
    have h4 : 4 * τ * (ε + B * M₁) ≤ 4 * τ * ((1 + Cd1) * ε) :=
      mul_le_mul_of_nonneg_left hS (by linarith)
    have h5 : 2 * (τ + B) * (ε + B * M₁) ≤ 4 * τ * ((1 + Cd1) * ε) := by linarith [h3, h4]
    calc (2 * Real.pi)⁻¹ * (2 * (τ + B)) * (ε + B * M₁)
        = (2 * Real.pi)⁻¹ * (2 * (τ + B) * (ε + B * M₁)) := by ring
      _ ≤ (2 * Real.pi)⁻¹ * (4 * τ * ((1 + Cd1) * ε)) := mul_le_mul_of_nonneg_left h5 hcoef.le
  have hC2 := kernelC_le_sqrt_param_aux α β P hτ hB hε hK hCd1 hCd2 hM₂nn hBτ hBval hM1sharp
    hM2sharp hPε hA1 hA2 hK1 hK2
  have hC2nn : 0 ≤ kernelC τ B P := kernelC_nonneg hτ hB P
  have hC1rhs : 0 ≤ (2 * Real.pi)⁻¹ * (4 * τ * ((1 + Cd1) * ε)) :=
    mul_nonneg (by positivity)
      (mul_nonneg (mul_nonneg (by norm_num) hτ.le) (mul_nonneg (by linarith) hε))
  have hprod : kernelA τ B P * kernelC τ B P
      ≤ (2 * Real.pi)⁻¹ * (4 * τ * ((1 + Cd1) * ε))
        * ((2 * Real.pi)⁻¹ *
          (4 * Cd2 * (k : ℝ) ^ β * ε / τ + 8 * K * Cd1 * (k : ℝ) ^ α * ε / τ + 4 * K * B)) :=
    mul_le_mul hC1 hC2 hC2nn hC1rhs
  refine hprod.trans ?_
  have hstep1 : (2 * Real.pi)⁻¹ * (4 * τ * ((1 + Cd1) * ε))
        * ((2 * Real.pi)⁻¹ *
          (4 * Cd2 * (k : ℝ) ^ β * ε / τ + 8 * K * Cd1 * (k : ℝ) ^ α * ε / τ + 4 * K * B))
      = (2 * Real.pi)⁻¹ * (2 * Real.pi)⁻¹
        * ((4 * τ * ((1 + Cd1) * ε))
          * (4 * Cd2 * (k : ℝ) ^ β * ε / τ + 8 * K * Cd1 * (k : ℝ) ^ α * ε / τ
            + 4 * K * B)) := by
    ring
  rw [hstep1]
  have hstep2 : (4 * τ * ((1 + Cd1) * ε))
        * (4 * Cd2 * (k : ℝ) ^ β * ε / τ + 8 * K * Cd1 * (k : ℝ) ^ α * ε / τ + 4 * K * B)
      = (1 + Cd1) * (16 * Cd2 * (k : ℝ) ^ β * B ^ 4 + 32 * K * Cd1 * (k : ℝ) ^ α * B ^ 4
          + 16 * K * τ * B ^ 3) := by
    rw [← hBB]
    field_simp
    try ring
  rw [hstep2, hB4, hB3]
  have hcoef : (2 * Real.pi)⁻¹ * (2 * Real.pi)⁻¹ ≤ 1 / 36 := inv_two_pi_sq_le
  have hXnn : (0 : ℝ) ≤ 16 * Cd2 * (k : ℝ) ^ β * ε ^ 2 + 32 * K * Cd1 * (k : ℝ) ^ α * ε ^ 2
      + 16 * K * τ * ε ^ (3 / 2 : ℝ) := by
    have h1 : (0 : ℝ) ≤ 16 * Cd2 * (k : ℝ) ^ β * ε ^ 2 := by positivity
    have h2 : (0 : ℝ) ≤ 32 * K * Cd1 * (k : ℝ) ^ α * ε ^ 2 := by positivity
    have h3 : (0 : ℝ) ≤ 16 * K * τ * ε ^ (3 / 2 : ℝ) := by positivity
    linarith
  calc ((2 * Real.pi)⁻¹ * (2 * Real.pi)⁻¹)
        * ((1 + Cd1) * (16 * Cd2 * (k : ℝ) ^ β * ε ^ 2 + 32 * K * Cd1 * (k : ℝ) ^ α * ε ^ 2
          + 16 * K * τ * ε ^ (3 / 2 : ℝ)))
      ≤ (1 / 36) * ((1 + Cd1) * (16 * Cd2 * (k : ℝ) ^ β * ε ^ 2
          + 32 * K * Cd1 * (k : ℝ) ^ α * ε ^ 2 + 16 * K * τ * ε ^ (3 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_right hcoef (mul_nonneg (by linarith) hXnn)
    _ = (1 / 36) * (1 + Cd1) * (16 * Cd2 * (k : ℝ) ^ β * ε ^ 2
          + 32 * K * Cd1 * (k : ℝ) ^ α * ε ^ 2 + 16 * K * τ * ε ^ (3 / 2 : ℝ)) := by ring

end RobustZ
