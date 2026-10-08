import RobustZ.M5Sharp

/-!
# M5‴（`M5Quad`）：**`ε`-无关**的截断尺度 ⟹ 核常数乘积的**二次**（`ε²`）界

## 与 `M5Sharp` 的唯一差别

`M5Sharp.kernelProd_le_poly_sharp_param` 用截断尺度

```
B = ε·τ/q²   （`hBval : B = ε * τ / q ^ 2`）
```

得到的是 **`ε`-线性**的结论 `C₁C₂ ≤ (1/36)(1+Cd1)(16Cd2 + 32Cd1K + 16K)·q²·ε`。
该文件自己指出：线性的来源是 `C₂` 里

```
(ε + B·M₁)·(4K/B) = 4K·ε/B + 4K·M₁ ,        4K·ε/B = 4K·q²/τ
```

那一项**与 `ε` 无关**（`ε` 与 `1/B = q²/(ετ)` 精确相消），乘上 `C₁ ∝ ε` 后仍是 `∝ ε`。

本文件把截断尺度换成**与 `ε` 无关**的

```
B = τ/q²      （`hBval : B = τ / q ^ 2`）
```

于是 `ε/B = ε·q²/τ` 变成 **`ε` 的一次**，`C₂` 的每一项都 `∝ ε`，乘积整体升到 `ε²`：

```
kernelA τ B P · kernelC τ B P ≤ (1/36)·(1+Cd1)·(16·Cd2 + 32·Cd1·K + 16·K)·q²·ε².
```

**常数与 `M5Sharp` 逐字相同**——锐化的收益全部体现在 `ε → ε²`（常数没有变大，
唯一变化是 `B ≤ τ` 的验证从 `q ≥ 1` 与 `ε ≤ 1` 变成了只用 `q ≥ 1`）。

## 代数（逐步，标明每一处损失）

记 `S := ε + B·M₁`。由 `hM1sharp`（§1 `mul_B_M1_le_quad`）：

```
B·M₁ = (τ·M₁)/q² ≤ Cd1·k·ε/q² ≤ Cd1·ε,        (i)
```

最后一步只要 `k/q² ≤ 1`，即 `k ≤ q²`；由 `k ≤ q` 与 `q ≥ 1` 得 `k ≤ q ≤ q²`。
**关键：这里不再需要 `ε ≤ 1`**（对比 `M5Sharp`：那里 `B·M₁ = (ε/q²)(τM₁)`
要 `kε ≤ q²`）。

**(1) `C₁`。** `kernelA_le_support` 给 `C₁ ≤ (2π)⁻¹·2(τ+B)·S`；用 `B ≤ τ`
（即 `2(τ+B) ≤ 4τ`，由 `q ≥ 1` 得 `B = τ/q² ≤ τ`）与 (i)：

```
C₁ ≤ (2π)⁻¹·4τ·(1+Cd1)·ε.                                        (★)
```

**(2) `C₂`。** `kernelC_le_support` 的右端是
`2(τ+B)M₂ + 2(M₁(2K)) + (ε+B·M₁)(4K/B)`；最后一项精确拆成
`(ε+B·M₁)(4K/B) = 4K·ε/B + 4K·M₁`。于是四项：

| `C₂` 的项 | 处理 | 依据 |
|---|---|---|
| `2(τ+B)·M₂` | `≤ 4τ·M₂` | `B ≤ τ` |
| `2(M₁·(2K))` | `= 4K·M₁`（精确） | `ring` |
| `4K·ε/B` | `= 4K·q²·ε/τ`（**精确，零损失**） | `ε/B = εq²/τ`（由 `B = τ/q²`） |
| `4K·B·M₁/B` | `= 4K·M₁`（精确） | `field_simp` |

```
C₂ ≤ (2π)⁻¹·(4τ·M₂ + 8K·M₁ + 4K·q²·ε/τ).                        (★★)
```

`8K·M₁` 是 `4K·M₁`（第二项）加 `4K·M₁`（第四项）**两份**，这是 `Cd1`
系数为 `32` 而不是 `16` 的唯一原因（与 `M5Sharp` 一致）。

**(3) 相乘，(★)×(★★)。** `4τ` 的 `τ` 与 `4Kq²ε/τ` 的 `1/τ` **精确相消**：

```
(2π)²·C₁C₂ ≤ 4τ(1+Cd1)ε·(4τM₂ + 8KM₁ + 4Kq²ε/τ)
           = (1+Cd1)·(16·ε·(τ²M₂) + 32·K·ε·(τM₁) + 16·K·q²·ε²).   (♦)
```

对 (♦) 的三块分别用锐化界（唯一的损失在这里：`k ≤ q`、`k² ≤ q²`）：

```
ε·(τ²M₂) ≤ ε·Cd2·k²·ε = Cd2·k²ε²  ≤ Cd2·q²ε²     (k² ≤ q²)
Kε·(τM₁) ≤ Kε·Cd1·k·ε = Cd1·K·kε²  ≤ Cd1·K·q²ε²   (k ≤ q，再 qε² ≤ q²ε² 由 q ≥ 1)
K·q²·ε²  = K·q²·ε²                                 (精确)
```

```
(2π)²·C₁C₂ ≤ (1+Cd1)·(16·Cd2 + 32·Cd1·K + 16·K)·q²·ε².           (♦♦)
```

**(4) `(2π)⁻² ≤ 1/36`**（`π > 3`，`M5Sharp.inv_two_pi_sq_le`）即得主结论。

## `ε ≤ 1` 到底还要不要？

**不要。** 主引理 `kernelProd_le_poly_quad` 的签名里**没有** `hε1 : ε ≤ 1`，
也没有 `hτq : τ ≤ q`。逐一核对 `M5Sharp` 用到 `ε ≤ 1` 的两处：

1. `M5Sharp` 的 `B·M₁ ≤ Cd1ε` 需要 `kε ≤ q ≤ q²`（用 `ε ≤ 1`）。
   本文件 `B·M₁ = (τM₁)/q² ≤ Cd1·kε/q²`，只需 `k ≤ q²`（用 `q ≥ 1`）。
   **`ε` 完全不出现在这一步。**
2. `M5Sharp` 的 `ε·(τ²M₂) ≤ Cd2·q²ε` 需要 `ε² ≤ ε`（即 `ε ≤ 1`）。
   本文件对应的是 `ε·(τ²M₂) ≤ ε·Cd2·q²·ε = Cd2·q²·ε²`，**是等式方向的重写，无损失**。

第三块 `Kε(τM₁) ≤ Cd1K·qε² ≤ Cd1K·q²ε²` 用的也是 `q ≥ 1`（`qε² ≤ q²ε²`），
与 `ε` 的大小无关。因此 `ε ≤ 1` 在本文件中**在任何地方都不需要**。
（仍提供签名兼容版 `kernelProd_le_poly_quad_legacy`：多收 `hε1` 与 `hτq` 但不用，
方便从 `M5Sharp` 的调用点逐字替换。）

## 判据（下游 `FinalSmall.h_zero_lt_of_kernel_decay` 的阈值）

`h_zero_lt_of_kernel_decay` 要的是 `C₁C₂ < ((1-cos(φ/2))/8)²`；本文件给出两条
通往 `< (1/8)²` 的判据（两者都只是 `Csharp·q²ε² < 1/64` 的改写）：

* `kernelProd_quad_lt`（**最紧**）：`ε < 1/(√Csharp·8·q)`。
  该式**不能**换成「`q ≥ q₁`」而无 `ε` 的条件：`ε` 只有下界 `0`，
  `Csharp q²ε²` 对大的 `ε` 必然爆掉，所以任何纯 `q` 判据都必须是假的。
* `kernelProd_quad_criterion`（**显式 `q₁` 形**）：在 `ε ≤ Ec·e^{-δ'q}`（`δ' > 0`，
  这正是 `epsOf τ δ' (2N+1)` 的形状，`q = 2N+2`，`e^{δ'}` 与几何因子吸收进 `Ec`）下，

  ```
  q ≥ q₁ := 32·√Csharp·Ec/δ'²   ⟹   C₁C₂ < (1/8)².
  ```

  推导只用初等界 `e^t ≥ t²/2`（`t = δ'q > 0`）：`8√Csharp·Ec·q·e^{-δ'q} ≤ 2·8√Csharp·Ec/(δ'²q) ≤ 1/2`。

## 常数

```
Csharp(Cd1,Cd2,K) = (1/36)·(1+Cd1)·(16·Cd2 + 32·Cd1·K + 16·K)      （`quadC`）
```

* `Cd1 = 32, Cd2 = 512, K = 1`：`Csharp = 304656/36 = 101552/12 = 8462.666…`
  （`≤ 8463`）；`q₁ = 32·√(101552/12)·Ec/δ'² = 2943.77…·Ec/δ'²`。
* `Cd1 = 4, Cd2 = 16, K = 1`：`Csharp = 2000/36 = 500/9 = 55.555…`（`≤ 56`）；
  `q₁ = 32·√(500/9)·Ec/δ'² = 238.51…·Ec/δ'²`。
-/

set_option maxHeartbeats 1000000

noncomputable section

namespace RobustZ

open Filter MeasureTheory
open scoped Real

/-! ## §1 判据常数 `Csharp` 与 `ε`-无关截断尺度的直接推论 -/

/-- **本文件的显式常数**

```
Csharp(Cd1,Cd2,K) = (1/36)·(1+Cd1)·(16·Cd2 + 32·Cd1·K + 16·K).
```

它**与 `M5Sharp` 的常数逐字相同**：`ε → ε²` 的升级是免费的。 -/
def quadC (Cd1 Cd2 K : ℝ) : ℝ :=
  (1 / 36) * (1 + Cd1) * (16 * Cd2 + 32 * Cd1 * K + 16 * K)

/-- `quadC` 的展开式（`rfl`）。 -/
lemma quadC_def (Cd1 Cd2 K : ℝ) :
    quadC Cd1 Cd2 K = (1 / 36) * (1 + Cd1) * (16 * Cd2 + 32 * Cd1 * K + 16 * K) := rfl

/-- `Cd1, Cd2, K ≥ 0` 时 `quadC ≥ 0`。 -/
lemma quadC_nonneg {Cd1 Cd2 K : ℝ} (hCd1 : 0 ≤ Cd1) (hCd2 : 0 ≤ Cd2) (hK : 0 ≤ K) :
    0 ≤ quadC Cd1 Cd2 K := by
  rw [quadC_def]
  refine mul_nonneg (mul_nonneg (by norm_num) (by linarith)) ?_
  nlinarith [hCd1, hCd2, hK, mul_nonneg hCd1 hK]

/-- **判据阈值 `q₁`**（见 `kernelProd_quad_criterion`）：

```
q₁ = 32·√Csharp·Ec/δ'².
```

在 `ε ≤ Ec·e^{-δ'q}`（`δ' > 0`）下，`q ≥ q₁` 把 `Csharp·q²ε²` 压到 `1/64` 以下。 -/
def quadQ1 (Cd1 Cd2 K δ' Ec : ℝ) : ℝ :=
  32 * Real.sqrt (quadC Cd1 Cd2 K) * Ec / δ' ^ 2

/-- `B = τ/q²` 且 `q ≥ 1` ⟹ `B ≤ τ`（本文件里 `hBτ` 其实可由 `hBval` 推出，
保留它是为了与 `M5Sharp` 的签名对齐）。 -/
lemma B_le_tau_of_Bval {τ B q : ℝ} (hτ : 0 < τ) (hq1 : 1 ≤ q) (hBval : B = τ / q ^ 2) :
    B ≤ τ := by
  have hq2 : (1 : ℝ) ≤ q ^ 2 := by nlinarith [hq1]
  have h1 := mul_le_mul_of_nonneg_left hq2 hτ.le
  rw [hBval, div_le_iff₀ (by positivity : (0 : ℝ) < q ^ 2)]
  linarith [h1]

/-- **`B·M₁ ≤ Cd1·ε`（`ε`-无关版）**：`B = τ/q²` 时

```
B·M₁ = (τ·M₁)/q² ≤ Cd1·k·ε/q² ≤ Cd1·ε,
```

最后一步只需 `k ≤ q²`（由 `k ≤ q`、`q ≥ 1`）。

**对比 `M5Sharp.mul_B_M1_le_sharp`**：那里 `B = ετ/q²`，`B·M₁ = (ε/q²)(τM₁) ≤ Cd1·kε²/q²`
需要 `kε ≤ q²`（用 `ε ≤ 1`）；这里 `ε` 根本不出现。 -/
lemma mul_B_M1_le_quad {τ B ε M₁ Cd1 : ℝ} {k : ℕ} {q : ℝ}
    (hq1 : 1 ≤ q) (hε : 0 ≤ ε) (hCd1 : 0 ≤ Cd1)
    (hkq : (k : ℝ) ≤ q) (hBval : B = τ / q ^ 2)
    (hM1sharp : τ * M₁ ≤ Cd1 * (k : ℝ) * ε) :
    B * M₁ ≤ Cd1 * ε := by
  have hB1 : B * M₁ = (1 / q ^ 2) * (τ * M₁) := by
    rw [hBval]
    ring
  have h2 : (1 / q ^ 2) * (τ * M₁) ≤ (1 / q ^ 2) * (Cd1 * (k : ℝ) * ε) :=
    mul_le_mul_of_nonneg_left hM1sharp (by positivity)
  have h3 : (1 / q ^ 2) * (Cd1 * (k : ℝ) * ε) = Cd1 * ε * ((k : ℝ) / q ^ 2) := by ring
  have h4 : (k : ℝ) / q ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity : (0 : ℝ) < q ^ 2)]
    nlinarith [hkq, hq1]
  have h5 : Cd1 * ε * ((k : ℝ) / q ^ 2) ≤ Cd1 * ε * 1 :=
    mul_le_mul_of_nonneg_left h4 (mul_nonneg hCd1 hε)
  linarith [hB1, h2, h3, h5]

/-! ## §2 主引理 -/

/-- **核心（参数版）：`ε`-无关截断尺度 `B = τ/q²` ⟹ 乘积界是 `ε` 的二次式。**

把 `M`-侧锐化界（`τM₁ ≤ Cd1·k·ε`、`τ²M₂ ≤ Cd2·k²·ε`）代入 `C₁`、`C₂`
的支撑感知界，`B = τ/q²`：

```
kernelA τ B P · kernelC τ B P ≤ (1/36)·(1+Cd1)·(16·Cd2 + 32·Cd1·K + 16·K)·q²·ε².
```

与 `M5Sharp.kernelProd_le_poly_sharp_param` 相比：

* 结论从 `q²·ε` 升级到 `q²·ε²`（**二次**），**常数一字未改**；
* **不再需要** `hε1 : ε ≤ 1`（也不需要 `hτq : τ ≤ q`）——见文件头「`ε ≤ 1` 到底还要不要」；
* `4K·ε/B` 这一项现在是 `4K·q²·ε/τ`（**`ε` 的一次**），被 `C₁` 的 `2(τ+B) ≍ 4τ`
  精确吃掉 `1/τ`，留下 `16K·q²ε²`。

逐步代数与每一处损失见文件头。 -/
lemma kernelProd_le_poly_quad {τ B ε M₁ M₂ K Cd1 Cd2 : ℝ} {k : ℕ} {q : ℝ}
    (P : Polynomial ℂ)
    (hτ : 0 < τ) (hB : 0 < B) (hε : 0 ≤ ε) (hK : 0 ≤ K)
    (hCd1 : 0 ≤ Cd1) (hCd2 : 0 ≤ Cd2)
    (hM₁nn : 0 ≤ M₁) (hM₂nn : 0 ≤ M₂)
    (hq1 : 1 ≤ q) (hkq : (k : ℝ) ≤ q) (hBτ : B ≤ τ)
    (hBval : B = τ / q ^ 2)
    (hM1sharp : τ * M₁ ≤ Cd1 * (k : ℝ) * ε)
    (hM2sharp : τ ^ 2 * M₂ ≤ Cd2 * (k : ℝ) ^ 2 * ε)
    (hψ : ∀ μ : ℝ, ‖psi τ B P μ‖ ≤ ε + B * M₁)
    (hPε : ∀ μ : ℝ, |μ| ≤ τ →
      ‖Complex.exp (-(μ : ℂ) * Complex.I) - P.eval ((μ : ℂ))‖ ≤ ε)
    (hA1 : ∀ μ : ℝ, |μ| ≤ τ + B → ‖deriv (fun x : ℝ => psiA P x) μ‖ ≤ M₁)
    (hA2 : ∀ μ : ℝ, |μ| ≤ τ + B → ‖deriv (deriv (fun x : ℝ => psiA P x)) μ‖ ≤ M₂)
    (hK1 : ∀ μ : ℝ, ‖deriv (fun x : ℝ => ((cutoff τ B x : ℝ) : ℂ)) μ‖ ≤ K / B)
    (hK2 : ∀ μ : ℝ, ‖deriv (deriv (fun x : ℝ => ((cutoff τ B x : ℝ) : ℂ))) μ‖ ≤ K / B ^ 2) :
    kernelA τ B P * kernelC τ B P
      ≤ (1 / 36 : ℝ) * (1 + Cd1) * (16 * Cd2 + 32 * Cd1 * K + 16 * K) * q ^ 2 * ε ^ 2 := by
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le one_pos hq1
  have hεB : ε / B = ε * q ^ 2 / τ := by
    rw [hBval]
    field_simp
  have hk2 : (k : ℝ) ^ 2 ≤ q ^ 2 := pow_le_pow_left₀ (by positivity) hkq 2
  have hqq : q ≤ q ^ 2 := by nlinarith [hq1]
  -- ### (a) 锐化输入的推论：`B·M₁ ≤ Cd1ε`、`S = ε + B·M₁ ≤ (1+Cd1)ε`
  have hBM1 : B * M₁ ≤ Cd1 * ε :=
    mul_B_M1_le_quad hq1 hε hCd1 hkq hBval hM1sharp
  have hSle : ε + B * M₁ ≤ (1 + Cd1) * ε := by linarith [hBM1, hε]
  have hSnn : 0 ≤ ε + B * M₁ := by
    have h := mul_nonneg hB.le hM₁nn
    linarith
  -- ### (b) `C₁ ≤ (2π)⁻¹·4τ·(1+Cd1)ε`
  have hC1 : kernelA τ B P ≤ (2 * Real.pi)⁻¹ * (4 * τ) * ((1 + Cd1) * ε) := by
    refine (kernelA_le_support hτ hB P hψ).trans ?_
    have hcoef : (0 : ℝ) < (2 * Real.pi)⁻¹ := by positivity
    have h1 : 2 * (τ + B) ≤ 4 * τ := by linarith
    have h5 : (2 * Real.pi)⁻¹ * (2 * (τ + B)) ≤ (2 * Real.pi)⁻¹ * (4 * τ) :=
      mul_le_mul_of_nonneg_left h1 hcoef.le
    have h4 : (0 : ℝ) ≤ (2 * Real.pi)⁻¹ * (4 * τ) := mul_nonneg hcoef.le (by linarith)
    exact mul_le_mul h5 hSle hSnn h4
  -- ### (c) `C₂ ≤ (2π)⁻¹·(4τM₂ + 8KM₁ + 4Kq²ε/τ)`
  have hC2 : kernelC τ B P ≤ (2 * Real.pi)⁻¹ *
      (4 * τ * M₂ + 8 * K * M₁ + 4 * K * q ^ 2 * ε / τ) := by
    refine (kernelC_le_support hτ hB P hε hPε hA1 hA2 hK1 hK2).trans ?_
    have hcoef : (0 : ℝ) < (2 * Real.pi)⁻¹ := by positivity
    have h1 : 2 * (τ + B) * M₂ ≤ 4 * τ * M₂ := by nlinarith [hBτ, hM₂nn, hτ]
    have h2 : 2 * (M₁ * (2 * K)) = 4 * K * M₁ := by ring
    have h3 : (ε + B * M₁) * (4 * K / B) ≤ 4 * K * q ^ 2 * ε / τ + 4 * K * M₁ := by
      have h4 : (ε + B * M₁) * (4 * K / B) = ε * (4 * K / B) + B * M₁ * (4 * K / B) := by
        ring
      have h5 : ε * (4 * K / B) = 4 * K * (ε / B) := by ring
      have h6 : B * M₁ * (4 * K / B) = 4 * K * M₁ := by field_simp
      have h7 : 4 * K * (ε / B) = 4 * K * (ε * q ^ 2 / τ) := by rw [hεB]
      have h8 : 4 * K * q ^ 2 * ε / τ = 4 * K * (ε * q ^ 2 / τ) := by ring
      linarith [h4, h5, h6, h7, h8]
    have hsum : 2 * (τ + B) * M₂ + 2 * (M₁ * (2 * K)) + (ε + B * M₁) * (4 * K / B)
        ≤ 4 * τ * M₂ + 8 * K * M₁ + 4 * K * q ^ 2 * ε / τ := by linarith [h1, h2, h3]
    exact mul_le_mul_of_nonneg_left hsum hcoef.le
  -- ### (d) 相乘
  have hC2nn : 0 ≤ kernelC τ B P := kernelC_nonneg hτ hB P
  have hC1rhs : 0 ≤ (2 * Real.pi)⁻¹ * (4 * τ) * ((1 + Cd1) * ε) :=
    mul_nonneg (mul_nonneg (by positivity) (by linarith)) (mul_nonneg (by linarith) hε)
  have hprod : kernelA τ B P * kernelC τ B P
      ≤ (2 * Real.pi)⁻¹ * (4 * τ) * ((1 + Cd1) * ε)
        * ((2 * Real.pi)⁻¹ * (4 * τ * M₂ + 8 * K * M₁ + 4 * K * q ^ 2 * ε / τ)) :=
    mul_le_mul hC1 hC2 hC2nn hC1rhs
  refine hprod.trans ?_
  -- ### (e) 展开：`τ` 与 `1/τ` 精确相消
  have hstep1 : (2 * Real.pi)⁻¹ * (4 * τ) * ((1 + Cd1) * ε)
        * ((2 * Real.pi)⁻¹ * (4 * τ * M₂ + 8 * K * M₁ + 4 * K * q ^ 2 * ε / τ))
      = (2 * Real.pi)⁻¹ * (2 * Real.pi)⁻¹
        * ((4 * τ * ((1 + Cd1) * ε))
          * (4 * τ * M₂ + 8 * K * M₁ + 4 * K * q ^ 2 * ε / τ)) := by ring
  rw [hstep1]
  have hstep2 : (4 * τ * ((1 + Cd1) * ε)) * (4 * τ * M₂ + 8 * K * M₁ + 4 * K * q ^ 2 * ε / τ)
      = (1 + Cd1) * (16 * ε * (τ ^ 2 * M₂) + 32 * K * ε * (τ * M₁)
          + 16 * K * q ^ 2 * ε ^ 2) := by
    field_simp
    ring
  rw [hstep2]
  -- ### (f) 三块归约到 `(16Cd2 + 32Cd1K + 16K)(q²ε²)`
  have hτ2M₂ : τ ^ 2 * M₂ ≤ Cd2 * q ^ 2 * ε := by
    have h1 : Cd2 * (k : ℝ) ^ 2 * ε ≤ Cd2 * q ^ 2 * ε :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk2 hCd2) hε
    linarith [hM2sharp, h1]
  have hτM₁ : τ * M₁ ≤ Cd1 * q * ε := by
    have h1 : Cd1 * (k : ℝ) * ε ≤ Cd1 * q * ε :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkq hCd1) hε
    linarith [hM1sharp, h1]
  have hinner : 16 * ε * (τ ^ 2 * M₂) + 32 * K * ε * (τ * M₁) + 16 * K * q ^ 2 * ε ^ 2
      ≤ (16 * Cd2 + 32 * Cd1 * K + 16 * K) * (q ^ 2 * ε ^ 2) := by
    have hA : 16 * ε * (τ ^ 2 * M₂) ≤ 16 * Cd2 * (q ^ 2 * ε ^ 2) := by
      calc 16 * ε * (τ ^ 2 * M₂) ≤ 16 * ε * (Cd2 * q ^ 2 * ε) :=
            mul_le_mul_of_nonneg_left hτ2M₂ (mul_nonneg (by norm_num) hε)
        _ = 16 * Cd2 * (q ^ 2 * ε ^ 2) := by ring
    have hB' : 32 * K * ε * (τ * M₁) ≤ 32 * Cd1 * K * (q ^ 2 * ε ^ 2) := by
      have hqe : q * ε ^ 2 ≤ q ^ 2 * ε ^ 2 :=
        mul_le_mul_of_nonneg_right hqq (sq_nonneg ε)
      have h0 : (0 : ℝ) ≤ 32 * Cd1 * K := mul_nonneg (mul_nonneg (by norm_num) hCd1) hK
      have h3 : 32 * Cd1 * K * q * ε ^ 2 ≤ 32 * Cd1 * K * q ^ 2 * ε ^ 2 := by
        calc 32 * Cd1 * K * q * ε ^ 2 = (32 * Cd1 * K) * (q * ε ^ 2) := by ring
          _ ≤ (32 * Cd1 * K) * (q ^ 2 * ε ^ 2) := mul_le_mul_of_nonneg_left hqe h0
          _ = 32 * Cd1 * K * q ^ 2 * ε ^ 2 := by ring
      calc 32 * K * ε * (τ * M₁) ≤ 32 * K * ε * (Cd1 * q * ε) :=
            mul_le_mul_of_nonneg_left hτM₁ (mul_nonneg (mul_nonneg (by norm_num) hK) hε)
        _ = 32 * Cd1 * K * q * ε ^ 2 := by ring
        _ ≤ 32 * Cd1 * K * q ^ 2 * ε ^ 2 := h3
        _ = 32 * Cd1 * K * (q ^ 2 * ε ^ 2) := by ring
    have hC' : 16 * K * q ^ 2 * ε ^ 2 ≤ 16 * K * (q ^ 2 * ε ^ 2) := le_of_eq (by ring)
    have hsum := add_le_add (add_le_add hA hB') hC'
    calc (16 * ε * (τ ^ 2 * M₂) + 32 * K * ε * (τ * M₁)) + 16 * K * q ^ 2 * ε ^ 2
        ≤ (16 * Cd2 * (q ^ 2 * ε ^ 2) + 32 * Cd1 * K * (q ^ 2 * ε ^ 2))
          + 16 * K * (q ^ 2 * ε ^ 2) := hsum
      _ = (16 * Cd2 + 32 * Cd1 * K + 16 * K) * (q ^ 2 * ε ^ 2) := by ring
  -- ### (g) 取 `(2π)⁻² ≤ 1/36`
  have hXnn : (0 : ℝ) ≤ 16 * ε * (τ ^ 2 * M₂) + 32 * K * ε * (τ * M₁)
      + 16 * K * q ^ 2 * ε ^ 2 := by
    have h1 : (0 : ℝ) ≤ 16 * ε * (τ ^ 2 * M₂) :=
      mul_nonneg (mul_nonneg (by norm_num) hε) (mul_nonneg (sq_nonneg τ) hM₂nn)
    have h2 : (0 : ℝ) ≤ 32 * K * ε * (τ * M₁) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hK) hε) (mul_nonneg hτ.le hM₁nn)
    have h3 : (0 : ℝ) ≤ 16 * K * q ^ 2 * ε ^ 2 :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hK) (sq_nonneg q)) (sq_nonneg ε)
    linarith [h1, h2, h3]
  have hcoef : (2 * Real.pi)⁻¹ * (2 * Real.pi)⁻¹ ≤ 1 / 36 := inv_two_pi_sq_le
  calc (2 * Real.pi)⁻¹ * (2 * Real.pi)⁻¹
        * ((1 + Cd1) * (16 * ε * (τ ^ 2 * M₂) + 32 * K * ε * (τ * M₁)
          + 16 * K * q ^ 2 * ε ^ 2))
      ≤ (1 / 36) * ((1 + Cd1) * (16 * ε * (τ ^ 2 * M₂) + 32 * K * ε * (τ * M₁)
          + 16 * K * q ^ 2 * ε ^ 2)) :=
        mul_le_mul_of_nonneg_right hcoef (mul_nonneg (by linarith) hXnn)
    _ ≤ (1 / 36) * ((1 + Cd1) * ((16 * Cd2 + 32 * Cd1 * K + 16 * K) * (q ^ 2 * ε ^ 2))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hinner (by linarith : (0 : ℝ) ≤ 1 + Cd1))
          (by norm_num : (0 : ℝ) ≤ 1 / 36)
    _ = (1 / 36 : ℝ) * (1 + Cd1) * (16 * Cd2 + 32 * Cd1 * K + 16 * K) * q ^ 2 * ε ^ 2 := by
        ring

/-- **签名兼容版**：与 `kernelProd_le_poly_quad` 结论相同，但多收 `M5Sharp` 的
`hτq : τ ≤ q` 与 `hε1 : ε ≤ 1`（**两者都不使用**）。

存在的理由：下游若已按 `M5Sharp.kernelProd_le_poly_sharp_param` 的签名写好调用，
可以逐字换成这一条而不必删参数。 -/
lemma kernelProd_le_poly_quad_legacy {τ B ε M₁ M₂ K Cd1 Cd2 : ℝ} {k : ℕ} {q : ℝ}
    (P : Polynomial ℂ)
    (hτ : 0 < τ) (hB : 0 < B) (hε : 0 ≤ ε) (hK : 0 ≤ K)
    (hCd1 : 0 ≤ Cd1) (hCd2 : 0 ≤ Cd2)
    (hM₁nn : 0 ≤ M₁) (hM₂nn : 0 ≤ M₂)
    (hq1 : 1 ≤ q) (hkq : (k : ℝ) ≤ q) (_hτq : τ ≤ q) (hBτ : B ≤ τ) (_hε1 : ε ≤ 1)
    (hBval : B = τ / q ^ 2)
    (hM1sharp : τ * M₁ ≤ Cd1 * (k : ℝ) * ε)
    (hM2sharp : τ ^ 2 * M₂ ≤ Cd2 * (k : ℝ) ^ 2 * ε)
    (hψ : ∀ μ : ℝ, ‖psi τ B P μ‖ ≤ ε + B * M₁)
    (hPε : ∀ μ : ℝ, |μ| ≤ τ →
      ‖Complex.exp (-(μ : ℂ) * Complex.I) - P.eval ((μ : ℂ))‖ ≤ ε)
    (hA1 : ∀ μ : ℝ, |μ| ≤ τ + B → ‖deriv (fun x : ℝ => psiA P x) μ‖ ≤ M₁)
    (hA2 : ∀ μ : ℝ, |μ| ≤ τ + B → ‖deriv (deriv (fun x : ℝ => psiA P x)) μ‖ ≤ M₂)
    (hK1 : ∀ μ : ℝ, ‖deriv (fun x : ℝ => ((cutoff τ B x : ℝ) : ℂ)) μ‖ ≤ K / B)
    (hK2 : ∀ μ : ℝ, ‖deriv (deriv (fun x : ℝ => ((cutoff τ B x : ℝ) : ℂ))) μ‖ ≤ K / B ^ 2) :
    kernelA τ B P * kernelC τ B P
      ≤ (1 / 36 : ℝ) * (1 + Cd1) * (16 * Cd2 + 32 * Cd1 * K + 16 * K) * q ^ 2 * ε ^ 2 :=
  kernelProd_le_poly_quad P hτ hB hε hK hCd1 hCd2 hM₁nn hM₂nn hq1 hkq hBτ hBval
    hM1sharp hM2sharp hψ hPε hA1 hA2 hK1 hK2

/-- **参数版的 `(1+K)` 形状**（与 `M5Scaled.kernelProd_le_poly` 的输出形状一致）：
用 `16Cd2 + 32Cd1K + 16K ≤ (16Cd2 + 32Cd1 + 16)(1+K)`，代价是把 `16Cd2` 也乘上 `K`。
除非下游接口硬要 `(1+K)`，优先用 `kernelProd_le_poly_quad`。 -/
lemma kernelProd_le_poly_quad_one_add_K {τ B ε M₁ M₂ K Cd1 Cd2 : ℝ} {k : ℕ} {q : ℝ}
    (P : Polynomial ℂ)
    (hτ : 0 < τ) (hB : 0 < B) (hε : 0 ≤ ε) (hK : 0 ≤ K)
    (hCd1 : 0 ≤ Cd1) (hCd2 : 0 ≤ Cd2)
    (hM₁nn : 0 ≤ M₁) (hM₂nn : 0 ≤ M₂)
    (hq1 : 1 ≤ q) (hkq : (k : ℝ) ≤ q) (hBτ : B ≤ τ)
    (hBval : B = τ / q ^ 2)
    (hM1sharp : τ * M₁ ≤ Cd1 * (k : ℝ) * ε)
    (hM2sharp : τ ^ 2 * M₂ ≤ Cd2 * (k : ℝ) ^ 2 * ε)
    (hψ : ∀ μ : ℝ, ‖psi τ B P μ‖ ≤ ε + B * M₁)
    (hPε : ∀ μ : ℝ, |μ| ≤ τ →
      ‖Complex.exp (-(μ : ℂ) * Complex.I) - P.eval ((μ : ℂ))‖ ≤ ε)
    (hA1 : ∀ μ : ℝ, |μ| ≤ τ + B → ‖deriv (fun x : ℝ => psiA P x) μ‖ ≤ M₁)
    (hA2 : ∀ μ : ℝ, |μ| ≤ τ + B → ‖deriv (deriv (fun x : ℝ => psiA P x)) μ‖ ≤ M₂)
    (hK1 : ∀ μ : ℝ, ‖deriv (fun x : ℝ => ((cutoff τ B x : ℝ) : ℂ)) μ‖ ≤ K / B)
    (hK2 : ∀ μ : ℝ, ‖deriv (deriv (fun x : ℝ => ((cutoff τ B x : ℝ) : ℂ))) μ‖ ≤ K / B ^ 2) :
    kernelA τ B P * kernelC τ B P
      ≤ (1 / 36 : ℝ) * (1 + Cd1) * (16 * Cd2 + 32 * Cd1 + 16) * (1 + K) * q ^ 2 * ε ^ 2 := by
  have hmain := kernelProd_le_poly_quad P hτ hB hε hK hCd1 hCd2 hM₁nn hM₂nn
    hq1 hkq hBτ hBval hM1sharp hM2sharp hψ hPε hA1 hA2 hK1 hK2
  refine hmain.trans ?_
  have h0 : (0 : ℝ) ≤ q ^ 2 * ε ^ 2 := mul_nonneg (sq_nonneg q) (sq_nonneg ε)
  have h01 : (0 : ℝ) ≤ (1 / 36 : ℝ) * (1 + Cd1) :=
    mul_nonneg (by norm_num) (by linarith)
  have hc : 16 * Cd2 + 32 * Cd1 * K + 16 * K ≤ (16 * Cd2 + 32 * Cd1 + 16) * (1 + K) := by
    nlinarith [mul_nonneg hCd2 hK, mul_nonneg hCd1 hK, hK, hCd1, hCd2]
  calc (1 / 36 : ℝ) * (1 + Cd1) * (16 * Cd2 + 32 * Cd1 * K + 16 * K) * q ^ 2 * ε ^ 2
      = ((1 / 36 : ℝ) * (1 + Cd1))
        * ((16 * Cd2 + 32 * Cd1 * K + 16 * K) * (q ^ 2 * ε ^ 2)) := by ring
    _ ≤ ((1 / 36 : ℝ) * (1 + Cd1))
        * (((16 * Cd2 + 32 * Cd1 + 16) * (1 + K)) * (q ^ 2 * ε ^ 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc h0) h01
    _ = (1 / 36 : ℝ) * (1 + Cd1) * (16 * Cd2 + 32 * Cd1 + 16) * (1 + K) * q ^ 2 * ε ^ 2 := by
        ring

/-! ## §3 数值实例（把 `Cd1, Cd2, K` 钉死） -/

/-- **`(Cd1, Cd2, K) = (32, 512, 1)`**：`Csharp = (1/36)·33·9232 = 304656/36 = 101552/12 = 8462.66…`。 -/
lemma kernelProd_le_poly_quad_inst_32_512 {τ B ε M₁ M₂ : ℝ} {k : ℕ} {q : ℝ}
    (P : Polynomial ℂ)
    (hτ : 0 < τ) (hB : 0 < B) (hε : 0 ≤ ε)
    (hM₁nn : 0 ≤ M₁) (hM₂nn : 0 ≤ M₂)
    (hq1 : 1 ≤ q) (hkq : (k : ℝ) ≤ q) (hBτ : B ≤ τ)
    (hBval : B = τ / q ^ 2)
    (hM1sharp : τ * M₁ ≤ 32 * (k : ℝ) * ε)
    (hM2sharp : τ ^ 2 * M₂ ≤ 512 * (k : ℝ) ^ 2 * ε)
    (hψ : ∀ μ : ℝ, ‖psi τ B P μ‖ ≤ ε + B * M₁)
    (hPε : ∀ μ : ℝ, |μ| ≤ τ →
      ‖Complex.exp (-(μ : ℂ) * Complex.I) - P.eval ((μ : ℂ))‖ ≤ ε)
    (hA1 : ∀ μ : ℝ, |μ| ≤ τ + B → ‖deriv (fun x : ℝ => psiA P x) μ‖ ≤ M₁)
    (hA2 : ∀ μ : ℝ, |μ| ≤ τ + B → ‖deriv (deriv (fun x : ℝ => psiA P x)) μ‖ ≤ M₂)
    (hK1 : ∀ μ : ℝ, ‖deriv (fun x : ℝ => ((cutoff τ B x : ℝ) : ℂ)) μ‖ ≤ 1 / B)
    (hK2 : ∀ μ : ℝ, ‖deriv (deriv (fun x : ℝ => ((cutoff τ B x : ℝ) : ℂ))) μ‖ ≤ 1 / B ^ 2) :
    kernelA τ B P * kernelC τ B P ≤ (101552 / 12 : ℝ) * q ^ 2 * ε ^ 2 := by
  have hmain := kernelProd_le_poly_quad (Cd1 := 32) (Cd2 := 512) (K := 1) P hτ hB hε
    (by norm_num) (by norm_num) (by norm_num) hM₁nn hM₂nn hq1 hkq hBτ hBval
    hM1sharp hM2sharp hψ hPε hA1 hA2 hK1 hK2
  have hc : (1 / 36 : ℝ) * (1 + 32) * (16 * 512 + 32 * 32 * 1 + 16 * 1) = 101552 / 12 := by
    norm_num
  calc kernelA τ B P * kernelC τ B P
      ≤ (1 / 36 : ℝ) * (1 + 32) * (16 * 512 + 32 * 32 * 1 + 16 * 1) * q ^ 2 * ε ^ 2 := hmain
    _ = (101552 / 12 : ℝ) * q ^ 2 * ε ^ 2 := by rw [hc]

/-- **`(Cd1, Cd2, K) = (4, 16, 1)`**：`Csharp = (1/36)·5·400 = 2000/36 = 500/9 = 55.55…`。 -/
lemma kernelProd_le_poly_quad_inst_4_16 {τ B ε M₁ M₂ : ℝ} {k : ℕ} {q : ℝ}
    (P : Polynomial ℂ)
    (hτ : 0 < τ) (hB : 0 < B) (hε : 0 ≤ ε)
    (hM₁nn : 0 ≤ M₁) (hM₂nn : 0 ≤ M₂)
    (hq1 : 1 ≤ q) (hkq : (k : ℝ) ≤ q) (hBτ : B ≤ τ)
    (hBval : B = τ / q ^ 2)
    (hM1sharp : τ * M₁ ≤ 4 * (k : ℝ) * ε)
    (hM2sharp : τ ^ 2 * M₂ ≤ 16 * (k : ℝ) ^ 2 * ε)
    (hψ : ∀ μ : ℝ, ‖psi τ B P μ‖ ≤ ε + B * M₁)
    (hPε : ∀ μ : ℝ, |μ| ≤ τ →
      ‖Complex.exp (-(μ : ℂ) * Complex.I) - P.eval ((μ : ℂ))‖ ≤ ε)
    (hA1 : ∀ μ : ℝ, |μ| ≤ τ + B → ‖deriv (fun x : ℝ => psiA P x) μ‖ ≤ M₁)
    (hA2 : ∀ μ : ℝ, |μ| ≤ τ + B → ‖deriv (deriv (fun x : ℝ => psiA P x)) μ‖ ≤ M₂)
    (hK1 : ∀ μ : ℝ, ‖deriv (fun x : ℝ => ((cutoff τ B x : ℝ) : ℂ)) μ‖ ≤ 1 / B)
    (hK2 : ∀ μ : ℝ, ‖deriv (deriv (fun x : ℝ => ((cutoff τ B x : ℝ) : ℂ))) μ‖ ≤ 1 / B ^ 2) :
    kernelA τ B P * kernelC τ B P ≤ (500 / 9 : ℝ) * q ^ 2 * ε ^ 2 := by
  have hmain := kernelProd_le_poly_quad (Cd1 := 4) (Cd2 := 16) (K := 1) P hτ hB hε
    (by norm_num) (by norm_num) (by norm_num) hM₁nn hM₂nn hq1 hkq hBτ hBval
    hM1sharp hM2sharp hψ hPε hA1 hA2 hK1 hK2
  have hc : (1 / 36 : ℝ) * (1 + 4) * (16 * 16 + 32 * 4 * 1 + 16 * 1) = 500 / 9 := by
    norm_num
  calc kernelA τ B P * kernelC τ B P
      ≤ (1 / 36 : ℝ) * (1 + 4) * (16 * 16 + 32 * 4 * 1 + 16 * 1) * q ^ 2 * ε ^ 2 := hmain
    _ = (500 / 9 : ℝ) * q ^ 2 * ε ^ 2 := by rw [hc]

/-- 两个实例常数的算术自检（含上取整形式 `8463`、`56`）。 -/
lemma quad_const_check :
    (1 / 36 : ℝ) * (1 + 32) * (16 * 512 + 32 * 32 + 16) = 101552 / 12
      ∧ (1 / 36 : ℝ) * (1 + 32) * (16 * 512 + 32 * 32 + 16) ≤ 8463
      ∧ (1 / 36 : ℝ) * (1 + 4) * (16 * 16 + 32 * 4 + 16) = 500 / 9
      ∧ (1 / 36 : ℝ) * (1 + 4) * (16 * 16 + 32 * 4 + 16) ≤ 56 :=
  ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

/-! ## §4 判据：通往 `(1/8)²` 的两条路 -/

/-- **初等引理**：`t > 0` 时 `t·e^{-t} ≤ 2/t`（由 `e^t ≥ t²/2`，即 `sum_le_exp_of_nonneg` 取 `n = 3`）。 -/
lemma mul_exp_neg_le_two_div {t : ℝ} (ht : 0 < t) : t * Real.exp (-t) ≤ 2 / t := by
  have h1 : t ^ 2 / 2 ≤ Real.exp t := by
    have h2 := Real.sum_le_exp_of_nonneg (x := t) ht.le 3
    have h2' : (∑ i ∈ Finset.range 3, t ^ i / ((i.factorial : ℕ) : ℝ)) = 1 + t + t ^ 2 / 2 := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial_zero,
        Nat.factorial_one, Nat.factorial_two, Nat.cast_one, Nat.cast_ofNat, pow_zero, pow_one,
        zero_add]
      ring
    rw [h2'] at h2
    linarith
  have h3 : t ^ 2 ≤ 2 * Real.exp t := by linarith [Real.exp_pos t]
  have h4 : t ^ 2 * (Real.exp t)⁻¹ ≤ 2 := by
    show t ^ 2 / Real.exp t ≤ 2
    exact (div_le_iff₀ (Real.exp_pos t)).mpr h3
  rw [Real.exp_neg, le_div_iff₀ ht]
  calc t * (Real.exp t)⁻¹ * t = t ^ 2 * (Real.exp t)⁻¹ := by ring
    _ ≤ 2 := h4

/-- **最紧的判据**：`ε < 1/(√Csharp·8·q)` ⟹ `C₁C₂ < (1/8)²`。

（`(1/8)²` 就是 `FinalSmall.h_zero_lt_of_kernel_decay` 用的矛盾阈值量级；
取下界 `1/64` 是因为那里右端再乘 `(1-cos(φ/2))² ≤ 1`。）

**为什么不能没有 `ε` 的条件、只写 `q ≥ q₁`**：`ε` 只有下界 `0`，
`Csharp·q²ε²` 对大的 `ε` 必然 `≥ 1/64`，纯 `q` 判据必假。
带几何衰减假设 `ε ≤ Ec·e^{-δ'q}` 的 `q₁` 形见 `kernelProd_quad_criterion`。 -/
lemma kernelProd_quad_lt {τ B ε M₁ M₂ K Cd1 Cd2 : ℝ} {k : ℕ} {q : ℝ}
    (P : Polynomial ℂ)
    (hτ : 0 < τ) (hB : 0 < B) (hε : 0 ≤ ε) (hK : 0 ≤ K)
    (hCd1 : 0 ≤ Cd1) (hCd2 : 0 ≤ Cd2)
    (hM₁nn : 0 ≤ M₁) (hM₂nn : 0 ≤ M₂)
    (hq1 : 1 ≤ q) (hkq : (k : ℝ) ≤ q) (hBτ : B ≤ τ)
    (hBval : B = τ / q ^ 2)
    (hM1sharp : τ * M₁ ≤ Cd1 * (k : ℝ) * ε)
    (hM2sharp : τ ^ 2 * M₂ ≤ Cd2 * (k : ℝ) ^ 2 * ε)
    (hψ : ∀ μ : ℝ, ‖psi τ B P μ‖ ≤ ε + B * M₁)
    (hPε : ∀ μ : ℝ, |μ| ≤ τ →
      ‖Complex.exp (-(μ : ℂ) * Complex.I) - P.eval ((μ : ℂ))‖ ≤ ε)
    (hA1 : ∀ μ : ℝ, |μ| ≤ τ + B → ‖deriv (fun x : ℝ => psiA P x) μ‖ ≤ M₁)
    (hA2 : ∀ μ : ℝ, |μ| ≤ τ + B → ‖deriv (deriv (fun x : ℝ => psiA P x)) μ‖ ≤ M₂)
    (hK1 : ∀ μ : ℝ, ‖deriv (fun x : ℝ => ((cutoff τ B x : ℝ) : ℂ)) μ‖ ≤ K / B)
    (hK2 : ∀ μ : ℝ, ‖deriv (deriv (fun x : ℝ => ((cutoff τ B x : ℝ) : ℂ))) μ‖ ≤ K / B ^ 2)
    (hεsmall : ε < 1 / (Real.sqrt (quadC Cd1 Cd2 K) * 8 * q)) :
    kernelA τ B P * kernelC τ B P < (1 / 8) ^ 2 := by
  have hmain := kernelProd_le_poly_quad P hτ hB hε hK hCd1 hCd2 hM₁nn hM₂nn hq1 hkq hBτ hBval
    hM1sharp hM2sharp hψ hPε hA1 hA2 hK1 hK2
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le one_pos hq1
  have hCnn : (0 : ℝ) ≤ quadC Cd1 Cd2 K := quadC_nonneg hCd1 hCd2 hK
  have hsq : (Real.sqrt (quadC Cd1 Cd2 K) * q * ε) ^ 2 < (1 / 8 : ℝ) ^ 2 := by
    by_cases hC0 : quadC Cd1 Cd2 K = 0
    · rw [hC0, Real.sqrt_zero, zero_mul, zero_mul, div_zero] at hεsmall
      exact absurd hεsmall (not_lt.mpr hε)
    · have hCpos : 0 < quadC Cd1 Cd2 K := lt_of_le_of_ne hCnn (Ne.symm hC0)
      have hs : 0 < Real.sqrt (quadC Cd1 Cd2 K) := Real.sqrt_pos_of_pos hCpos
      have hden : 0 < Real.sqrt (quadC Cd1 Cd2 K) * 8 * q :=
        mul_pos (mul_pos hs (by norm_num)) hq0
      have h1 : ε * (Real.sqrt (quadC Cd1 Cd2 K) * 8 * q) < 1 := (lt_div_iff₀ hden).mp hεsmall
      have h2 : Real.sqrt (quadC Cd1 Cd2 K) * q * ε < 1 / 8 := by linarith
      have h3 : 0 ≤ Real.sqrt (quadC Cd1 Cd2 K) * q * ε :=
        mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hq0.le) hε
      have h4 : (Real.sqrt (quadC Cd1 Cd2 K) * q * ε) * (Real.sqrt (quadC Cd1 Cd2 K) * q * ε)
          < (1 / 8) * (1 / 8) := mul_self_lt_mul_self h3 h2
      calc (Real.sqrt (quadC Cd1 Cd2 K) * q * ε) ^ 2
          = (Real.sqrt (quadC Cd1 Cd2 K) * q * ε) * (Real.sqrt (quadC Cd1 Cd2 K) * q * ε) := by
            ring
        _ < (1 / 8) * (1 / 8) := h4
        _ = (1 / 8 : ℝ) ^ 2 := by ring
  have hCsq : quadC Cd1 Cd2 K * q ^ 2 * ε ^ 2
      = (Real.sqrt (quadC Cd1 Cd2 K) * q * ε) ^ 2 := by
    rw [show (Real.sqrt (quadC Cd1 Cd2 K) * q * ε) ^ 2
        = (Real.sqrt (quadC Cd1 Cd2 K)) ^ 2 * q ^ 2 * ε ^ 2 by ring,
      Real.sq_sqrt hCnn]
  have hlt : quadC Cd1 Cd2 K * q ^ 2 * ε ^ 2 < (1 / 8 : ℝ) ^ 2 := by
    rw [hCsq]
    exact hsq
  exact lt_of_le_of_lt hmain (by simpa only [quadC] using hlt)

/-- **显式 `q₁` 判据**：在几何衰减假设 `ε ≤ Ec·e^{-δ'q}`（`δ' > 0`）下，

```
q ≥ q₁ := 32·√Csharp·Ec/δ'²   ⟹   C₁C₂ < (1/8)².
```

（`ε ≤ Ec·e^{-δ'q}` 正是下游的形状：`M5Apply` 里 `ε = epsOf τ δ' (2N+1)`、
`q = 2N+2`，把 `e^{τ sinh δ'}(1+4/(1-e^{-δ'}))·e^{δ'}` 吸收进 `Ec` 即可。）

推导（只用 `e^t ≥ t²/2`）：记 `t = δ'q > 0`、`A = 8√Csharp·Ec ≥ 0`，

```
8√Csharp·Ec·q·ε ≤ A·q·e^{-t} = (A/δ')·t·e^{-t} ≤ (A/δ')·(2/t) = 2A/(δ'²q) ≤ 1/2 < 1,
```

最后一步用 `4A = 32√Csharp·Ec ≤ δ'²q`（即 `q ≥ q₁`）。 -/
lemma kernelProd_quad_criterion {τ B ε M₁ M₂ K Cd1 Cd2 δ' Ec : ℝ} {k : ℕ} {q : ℝ}
    (P : Polynomial ℂ)
    (hτ : 0 < τ) (hB : 0 < B) (hε : 0 ≤ ε) (hK : 0 ≤ K)
    (hCd1 : 0 ≤ Cd1) (hCd2 : 0 ≤ Cd2)
    (hM₁nn : 0 ≤ M₁) (hM₂nn : 0 ≤ M₂)
    (hq1 : 1 ≤ q) (hkq : (k : ℝ) ≤ q) (hBτ : B ≤ τ)
    (hBval : B = τ / q ^ 2)
    (hM1sharp : τ * M₁ ≤ Cd1 * (k : ℝ) * ε)
    (hM2sharp : τ ^ 2 * M₂ ≤ Cd2 * (k : ℝ) ^ 2 * ε)
    (hψ : ∀ μ : ℝ, ‖psi τ B P μ‖ ≤ ε + B * M₁)
    (hPε : ∀ μ : ℝ, |μ| ≤ τ →
      ‖Complex.exp (-(μ : ℂ) * Complex.I) - P.eval ((μ : ℂ))‖ ≤ ε)
    (hA1 : ∀ μ : ℝ, |μ| ≤ τ + B → ‖deriv (fun x : ℝ => psiA P x) μ‖ ≤ M₁)
    (hA2 : ∀ μ : ℝ, |μ| ≤ τ + B → ‖deriv (deriv (fun x : ℝ => psiA P x)) μ‖ ≤ M₂)
    (hK1 : ∀ μ : ℝ, ‖deriv (fun x : ℝ => ((cutoff τ B x : ℝ) : ℂ)) μ‖ ≤ K / B)
    (hK2 : ∀ μ : ℝ, ‖deriv (deriv (fun x : ℝ => ((cutoff τ B x : ℝ) : ℂ))) μ‖ ≤ K / B ^ 2)
    (hδ' : 0 < δ') (hEc : 0 ≤ Ec)
    (hεdec : ε ≤ Ec * Real.exp (-(δ' * q)))
    (hqbig : quadQ1 Cd1 Cd2 K δ' Ec ≤ q) :
    kernelA τ B P * kernelC τ B P < (1 / 8) ^ 2 := by
  have hmain := kernelProd_le_poly_quad P hτ hB hε hK hCd1 hCd2 hM₁nn hM₂nn hq1 hkq hBτ hBval
    hM1sharp hM2sharp hψ hPε hA1 hA2 hK1 hK2
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le one_pos hq1
  have hCnn : (0 : ℝ) ≤ quadC Cd1 Cd2 K := quadC_nonneg hCd1 hCd2 hK
  -- ### (a) `q ≥ q₁` 给出 `4A ≤ δ'²q`（`A = 8√Csharp·Ec`）
  have hA4 : 32 * Real.sqrt (quadC Cd1 Cd2 K) * Ec ≤ δ' ^ 2 * q := by
    have h1 := hqbig
    rw [quadQ1, div_le_iff₀ (by positivity : (0 : ℝ) < δ' ^ 2)] at h1
    nlinarith [h1]
  -- ### (b) `8√Csharp·Ec·q·e^{-δ'q} ≤ 1/2`
  have hAt : 8 * Real.sqrt (quadC Cd1 Cd2 K) * Ec * q * Real.exp (-(δ' * q)) ≤ 1 / 2 := by
    have hA0 : (0 : ℝ) ≤ 8 * Real.sqrt (quadC Cd1 Cd2 K) * Ec :=
      mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) hEc
    have ht : 0 < δ' * q := mul_pos hδ' hq0
    have hb := mul_exp_neg_le_two_div ht
    have hcoef : (0 : ℝ) ≤ 8 * Real.sqrt (quadC Cd1 Cd2 K) * Ec / δ' := div_nonneg hA0 hδ'.le
    have h1 : 8 * Real.sqrt (quadC Cd1 Cd2 K) * Ec / δ' * ((δ' * q) * Real.exp (-(δ' * q)))
        ≤ 8 * Real.sqrt (quadC Cd1 Cd2 K) * Ec / δ' * (2 / (δ' * q)) :=
      mul_le_mul_of_nonneg_left hb hcoef
    have h2 : 8 * Real.sqrt (quadC Cd1 Cd2 K) * Ec / δ' * (2 / (δ' * q))
        = 2 * (8 * Real.sqrt (quadC Cd1 Cd2 K) * Ec) / (δ' ^ 2 * q) := by
      field_simp
    have h3 : 2 * (8 * Real.sqrt (quadC Cd1 Cd2 K) * Ec) / (δ' ^ 2 * q) ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < δ' ^ 2 * q)]
      linarith [hA4]
    have h4 : 8 * Real.sqrt (quadC Cd1 Cd2 K) * Ec / δ' * ((δ' * q) * Real.exp (-(δ' * q)))
        = 8 * Real.sqrt (quadC Cd1 Cd2 K) * Ec * q * Real.exp (-(δ' * q)) := by
      field_simp
    linarith [h1, h2, h3, h4]
  -- ### (c) `8√Csharp·q·ε < 1`
  have hkey : 8 * Real.sqrt (quadC Cd1 Cd2 K) * q * ε < 1 := by
    have h1 : 8 * Real.sqrt (quadC Cd1 Cd2 K) * q * ε
        ≤ 8 * Real.sqrt (quadC Cd1 Cd2 K) * q * (Ec * Real.exp (-(δ' * q))) :=
      mul_le_mul_of_nonneg_left hεdec
        (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) hq0.le)
    have h2 : 8 * Real.sqrt (quadC Cd1 Cd2 K) * q * (Ec * Real.exp (-(δ' * q)))
        = 8 * Real.sqrt (quadC Cd1 Cd2 K) * Ec * q * Real.exp (-(δ' * q)) := by ring
    linarith [h1, h2, hAt]
  -- ### (d) 平方并接上主引理
  have hsq : (Real.sqrt (quadC Cd1 Cd2 K) * q * ε) ^ 2 < (1 / 8 : ℝ) ^ 2 := by
    have h2 : Real.sqrt (quadC Cd1 Cd2 K) * q * ε < 1 / 8 := by linarith
    have h3 : 0 ≤ Real.sqrt (quadC Cd1 Cd2 K) * q * ε :=
      mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hq0.le) hε
    have h4 : (Real.sqrt (quadC Cd1 Cd2 K) * q * ε) * (Real.sqrt (quadC Cd1 Cd2 K) * q * ε)
        < (1 / 8) * (1 / 8) := mul_self_lt_mul_self h3 h2
    calc (Real.sqrt (quadC Cd1 Cd2 K) * q * ε) ^ 2
        = (Real.sqrt (quadC Cd1 Cd2 K) * q * ε) * (Real.sqrt (quadC Cd1 Cd2 K) * q * ε) := by
          ring
      _ < (1 / 8) * (1 / 8) := h4
      _ = (1 / 8 : ℝ) ^ 2 := by ring
  have hCsq : quadC Cd1 Cd2 K * q ^ 2 * ε ^ 2
      = (Real.sqrt (quadC Cd1 Cd2 K) * q * ε) ^ 2 := by
    rw [show (Real.sqrt (quadC Cd1 Cd2 K) * q * ε) ^ 2
        = (Real.sqrt (quadC Cd1 Cd2 K)) ^ 2 * q ^ 2 * ε ^ 2 by ring,
      Real.sq_sqrt hCnn]
  have hlt : quadC Cd1 Cd2 K * q ^ 2 * ε ^ 2 < (1 / 8 : ℝ) ^ 2 := by
    rw [hCsq]
    exact hsq
  exact lt_of_le_of_lt hmain (by simpa only [quadC] using hlt)

/-! ## §5 假设清单与说明

除 `M5Sharp.kernelProd_le_poly_sharp_param` 的全部 side condition（`hτ hB hε hK hCd1 hCd2
hM₁nn hM₂nn hq1 hkq hBτ hψ hPε hA1 hA2 hK1 hK2`）外：

* `hBval` 从 `B = ε·τ/q²` **换成** `B = τ/q²`（本文件的全部要点）。
* **去掉** `hε1 : ε ≤ 1`（`M5Sharp` 用它的两处在本文件里都不再出现，见文件头）。
* **去掉** `hτq : τ ≤ q`（`M5Sharp` 里它也未被实质使用）。若下游签名需要，
  用 `kernelProd_le_poly_quad_legacy`（多收 `hε1`、`hτq` 但不用）。
* `hBτ : B ≤ τ` 保留（`M5Sharp` 用它证 `2(τ+B) ≤ 4τ`）。由 `hBval`、`hq1`、`hτ`
  可推出（`B_le_tau_of_Bval`），保留只为签名对齐。
* `mul_B_M1_le_quad` 是本文件唯一「新」的输入引理，**不含 `ε`**。
* 判据部分额外需要 `hδ' : 0 < δ'`、`hEc : 0 ≤ Ec`、`hεdec : ε ≤ Ec·e^{-δ'q}`
  与 `hqbig : quadQ1 … ≤ q`；这些只出现在 `kernelProd_quad_criterion` 里，
  主引理与 `kernelProd_quad_lt` 都不需要。 -/

end RobustZ
