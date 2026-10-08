import RobustZ.M5Scaled

/-!
# M5″（`M5Sharp`）：**锐化**（`ε`-线性）的核常数乘积界

## 这个文件做什么

`M5Scaled.kernelProd_le_poly` 从**与 `ε` 无关**的粗 collar 界

```
τ·M₁ ≤ 4k³ + τ + 4kτ,      τ²·M₂ ≤ 128k⁵ + 8k³τ + τ² + 4kτ²
```

推出 `C₁C₂ = kernelA τ B P · kernelC τ B P ≤ 3000(1+K)εq⁸`。`q⁸` 的来源是把
`τM₁ ≲ q³`、`τ²M₂ ≲ q⁵` 直接代入（粗界的 `k` 幂次太高）。

本文件把这两个输入换成**锐化**（`ε`-线性）的版本

```
τ·M₁ ≤ Cd1·k·ε,            τ²·M₂ ≤ Cd2·k²·ε
```

（这正是并行 collar 分析在证的两条；这里把它们当**假设**，故本文件与那份工作完全解耦。）
结论里 `q⁸` 掉到 `q²`，常数是 `Cd1, Cd2, K` 的**显式表达式**：

```
kernelA τ B P · kernelC τ B P ≤ (1/36)·(1+Cd1)·(16·Cd2 + 32·Cd1·K + 16·K)·q²·ε.
```

主引理 `kernelProd_le_poly_sharp_param` 里 `Cd1`、`Cd2` 是**变量**（不是数值），
所以最终常数就是锐化导数分析实际能证的 `Cd1, Cd2` 的函数；两个数值实例
（`Cd1 = 64, Cd2 = 4096` 与 `Cd1 = 10³, Cd2 = 10⁶`）见 §2.2。

## 代数（逐步，标明每一处损失）

记 `S := ε + B·M₁`。由 `hM1sharp`（§1 `mul_B_M1_le_sharp`）：

```
B·M₁ = (ε/q²)·(τ·M₁) ≤ Cd1·k·ε²/q² = Cd1·ε·(kε/q²) ≤ Cd1·ε,     (i)
```
最后一步 `k·ε ≤ q·1 = q ≤ q²`（用 `k ≤ q`、`ε ≤ 1`、`q ≥ 1`）。

**(1) `C₁`。** `kernelA_le_support` 给 `C₁ ≤ (2π)⁻¹·2(τ+B)·S`；用 `B ≤ τ`
（即 `2(τ+B) ≤ 4τ`）与 (i)：

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
| `4K·ε/B` | `= 4K·q²/τ`（**精确，零损失**） | `ε/B = q²/τ`（由 `B = ετ/q²`） |
| `4K·B·M₁/B` | `= 4K·M₁`（精确） | `field_simp` |

```
C₂ ≤ (2π)⁻¹·(4τ·M₂ + 8K·M₁ + 4K·q²/τ).                          (★★)
```
`8K·M₁` 是 `4K·M₁`（第二项）加 `4K·M₁`（第四项）**两份**，这是 `Cd1`
系数为 `32` 而不是 `16` 的唯一原因。

**(3) 相乘，(★)×(★★)。** `4τ` 的 `τ` 与 `4Kq²/τ` 的 `1/τ` **精确相消**：

```
(2π)²·C₁C₂ ≤ 4τ(1+Cd1)ε·(4τM₂ + 8KM₁ + 4Kq²/τ)
           = (1+Cd1)·(16·ε·(τ²M₂) + 32·K·ε·(τM₁) + 16·K·q²·ε).   (♦)
```

对 (♦) 的三块分别用锐化界（唯一的损失在这里：`k ≤ q`、`ε ≤ 1`）：

```
ε·(τ²M₂) ≤ ε·Cd2·k²·ε = Cd2·k²ε² ≤ Cd2·q²ε     (k² ≤ q², ε² ≤ ε)
Kε·(τM₁) ≤ Kε·Cd1·k·ε = Cd1·K·kε² ≤ Cd1·K·q²ε   (k ≤ q,  ε² ≤ ε)
K·q²·ε   = K·q²·ε                                 (精确)
```

```
(2π)²·C₁C₂ ≤ (1+Cd1)·(16·Cd2 + 32·Cd1·K + 16·K)·q²·ε.           (♦♦)
```

**(4) `(2π)⁻² ≤ 1/36`**（`π > 3`，§1 `inv_two_pi_sq_le`）即得主结论。

## 哪一项主导、`ε` 的线性从哪来、`4K/B` 有没有被放缩

* 三块的常数系数是 `16·Cd2`（来自 `2(τ+B)M₂`）、`32·Cd1·K`（来自两份 `4K·M₁`）、
  `16·K`（来自 `4K·ε/B`）。以 `Cd1 = 64, Cd2 = 4096` 为例：
  `16·4096 = 65536`、`32·64 = 2048`、`16` —— **`τ²M₂` 项主导**；
  想让常数变小，唯一有意义的动作是把 `Cd2` 压小（`Csharp ≈ 0.44·Cd1·Cd2`）。
* **`4K/B` 这一项没有被放缩成幂次**：`4K·ε/B = 4K·q²/τ` 是**等式**，
  乘上 `C₁` 里的 `2(τ+B)` 后 `τ` 与 `1/τ` 精确相消，只剩
  `8K(1+Cd1)(q²ε + ε²) ≤ 16K(1+Cd1)q²ε`。它贡献的 `16K` 是三块里**最小**的一块。
  （因此 `≤ 4Kq/ρ` 型的担心不适用：`τ` 已经被 `C₁` 的 `2τ` 吃掉。）
* **`ε` 的线性**由 `4K·ε/B` 这块「`ε`-自由」项与 `C₁ ∝ S ≈ ε` 相乘钉住
  （即 (♦) 里的 `16Kq²ε`）；另两块因为 `M₁, M₂` 的界本身 `∝ ε`，
  给出的是 `ε²`，再用 `ε ≤ 1`（`ε² ≤ q²ε`）降到 `ε`。
  所以结论确实是**一次** `ε`，不是 `ε²`。
* 结构性损失只有 `(1+B/τ) ≤ 2` 与 `k ≤ q`、`k² ≤ q²`。在 `q²` 形状下
  它们等价于 `(1+ε/q²)² ≤ 4` 与 `(q+ε/q)² ≤ 4q²`，无法再改进。

## 假设与代价（详见 §4）

* **多出** `hε1 : ε ≤ 1`：两处 —— (a) `B·M₁ ≤ Cd1ε` 需要 `kε ≤ q²`
  （这一处只需较弱的 `ε ≤ q`）；(b) `ε² ≤ ε`（等价 `k²ε² ≤ q²ε`，
  这一处需要 `ε ≤ 1`）。在应用里 `ε = epsOf τ δ' (2N+1)` 最终 `≤ 1`。
* 参数版另需 `hCd1 : 0 ≤ Cd1`、`hCd2 : 0 ≤ Cd2`（符号参数的单调性）。
* `hτq : τ ≤ q` 未被实质使用，保留是为了与 `kernelProd_le_poly` 签名逐字对齐。
-/

set_option maxHeartbeats 1000000

noncomputable section

namespace RobustZ

open Filter MeasureTheory
open scoped Real

/-! ## §1 锐化输入的直接推论（含 `(2π)⁻²` 的初等界） -/

/-- `(2π)⁻² ≤ 1/36`（由 `π > 3`）。 -/
lemma inv_two_pi_sq_le : (2 * Real.pi)⁻¹ * (2 * Real.pi)⁻¹ ≤ (1 / 36 : ℝ) := by
  have hpi : (6 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have h1 : (2 * Real.pi)⁻¹ ≤ (6 : ℝ)⁻¹ := by
    rw [inv_le_inv₀ (by positivity : (0 : ℝ) < 2 * Real.pi) (by norm_num : (0 : ℝ) < 6)]
    exact hpi
  calc (2 * Real.pi)⁻¹ * (2 * Real.pi)⁻¹ ≤ (6 : ℝ)⁻¹ * (6 : ℝ)⁻¹ :=
        mul_le_mul h1 h1 (by positivity) (by positivity)
    _ = 1 / 36 := by norm_num

/-- **`B·M₁ ≤ Cd1·ε`**（主引理的核心输入，单独成条便于复用与调参）。

`B·M₁ = (ε/q²)·(τM₁) ≤ Cd1·k·ε²/q² = Cd1·ε·(kε/q²) ≤ Cd1·ε`，
最后一步 `k·ε ≤ q·1 = q ≤ q²`（`k ≤ q`、`ε ≤ 1`、`q ≥ 1`）。
（只需较弱的 `ε ≤ q` 即可做这一步；`ε ≤ 1` 是为 `k²ε² ≤ q²ε` 那一处。） -/
lemma mul_B_M1_le_sharp {τ B ε M₁ Cd1 : ℝ} {k : ℕ} {q : ℝ}
    (hτ : 0 < τ) (hq1 : 1 ≤ q) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hCd1 : 0 ≤ Cd1)
    (hkq : (k : ℝ) ≤ q) (hBval : B = ε * τ / q ^ 2)
    (hM1sharp : τ * M₁ ≤ Cd1 * (k : ℝ) * ε) :
    B * M₁ ≤ Cd1 * ε := by
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le one_pos hq1
  have hB1 : B * M₁ = (ε / q ^ 2) * (τ * M₁) := by
    rw [hBval]
    field_simp
  have h2 : (ε / q ^ 2) * (τ * M₁) ≤ (ε / q ^ 2) * (Cd1 * (k : ℝ) * ε) :=
    mul_le_mul_of_nonneg_left hM1sharp (by positivity)
  have hkε : (k : ℝ) * ε ≤ q ^ 2 := by
    have h1 : (k : ℝ) * ε ≤ q * 1 := mul_le_mul hkq hε1 hε hq0.le
    have h3 : q * 1 ≤ q ^ 2 := by nlinarith [hq1]
    linarith [h1, h3]
  have h3 : (ε / q ^ 2) * (Cd1 * (k : ℝ) * ε) = Cd1 * ε * ((k : ℝ) * ε / q ^ 2) := by
    ring
  have h4 : (k : ℝ) * ε / q ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity : (0 : ℝ) < q ^ 2)]
    exact hkε
  have h5 : Cd1 * ε * ((k : ℝ) * ε / q ^ 2) ≤ Cd1 * ε * 1 :=
    mul_le_mul_of_nonneg_left h4 (mul_nonneg hCd1 hε)
  linarith [hB1, h2, h3, h5]

/-! ## §2 主引理 -/

/-! ### §2.1 参数版（`Cd1`、`Cd2` 是变量，常数是它们的显式表达式） -/

/-- **锐化核心（参数版）**：把 `M₁`、`M₂` 的**`ε`-线性** collar 界代入 `C₁`、`C₂`
的支撑感知界，`q⁸ → q²`。

与 `M5Scaled.kernelProd_le_poly` 逐字同构，只把两条粗界
（`τM₁ ≤ 4k³+τ+4kτ`、`τ²M₂ ≤ 128k⁵+8k³τ+τ²+4kτ²`）换成锐化版本

* `τM₁ ≤ Cd1·k·ε`
* `τ²M₂ ≤ Cd2·k²·ε`，

结论常数为 **`Cd1, Cd2, K` 的显式表达式**（通路里最紧的形状，
不含把 `Cd2` 乘上 `(1+K)` 之类的保险放缩）：

```
kernelA τ B P · kernelC τ B P ≤ (1/36)·(1+Cd1)·(16·Cd2 + 32·Cd1·K + 16·K)·q²·ε.
```

三项系数依次来自 `2(τ+B)M₂`（`16Cd2`）、两份 `4K·M₁`（`32Cd1K`）、
`4K·ε/B = 4Kq²/τ`（`16K`）。逐步代数见文件头。 -/
lemma kernelProd_le_poly_sharp_param {τ B ε M₁ M₂ K Cd1 Cd2 : ℝ} {k : ℕ} {q : ℝ}
    (P : Polynomial ℂ)
    (hτ : 0 < τ) (hB : 0 < B) (hε : 0 ≤ ε) (hK : 0 ≤ K)
    (hCd1 : 0 ≤ Cd1) (hCd2 : 0 ≤ Cd2)
    (hM₁nn : 0 ≤ M₁) (hM₂nn : 0 ≤ M₂)
    (hq1 : 1 ≤ q) (hkq : (k : ℝ) ≤ q) (hτq : τ ≤ q) (hBτ : B ≤ τ)
    (hε1 : ε ≤ 1)
    (hBval : B = ε * τ / q ^ 2)
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
      ≤ (1 / 36 : ℝ) * (1 + Cd1) * (16 * Cd2 + 32 * Cd1 * K + 16 * K) * q ^ 2 * ε := by
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le one_pos hq1
  have hεpos : 0 < ε := by
    rcases lt_or_eq_of_le hε with h | h
    · exact h
    · exfalso
      rw [← h, zero_mul, zero_div] at hBval
      rw [hBval] at hB
      exact lt_irrefl 0 hB
  have hεB : ε / B = q ^ 2 / τ := by
    rw [hBval]
    field_simp
  have hk2 : (k : ℝ) ^ 2 ≤ q ^ 2 := pow_le_pow_left₀ (by positivity) hkq 2
  have hqq : q ≤ q ^ 2 := by nlinarith [hq1]
  have hε2 : ε ^ 2 ≤ ε := by nlinarith [hε, hε1]
  -- ### (a) 锐化输入的推论：`B·M₁ ≤ Cd1ε`、`S = ε + B·M₁ ≤ (1+Cd1)ε`
  have hBM1 : B * M₁ ≤ Cd1 * ε :=
    mul_B_M1_le_sharp hτ hq1 hε hε1 hCd1 hkq hBval hM1sharp
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
  -- ### (c) `C₂ ≤ (2π)⁻¹·(4τM₂ + 8KM₁ + 4Kq²/τ)`
  have hC2 : kernelC τ B P ≤ (2 * Real.pi)⁻¹ *
      (4 * τ * M₂ + 8 * K * M₁ + 4 * K * q ^ 2 / τ) := by
    refine (kernelC_le_support hτ hB P hε hPε hA1 hA2 hK1 hK2).trans ?_
    have hcoef : (0 : ℝ) < (2 * Real.pi)⁻¹ := by positivity
    have h1 : 2 * (τ + B) * M₂ ≤ 4 * τ * M₂ := by nlinarith [hBτ, hM₂nn, hτ]
    have h2 : 2 * (M₁ * (2 * K)) = 4 * K * M₁ := by ring
    have h3 : (ε + B * M₁) * (4 * K / B) ≤ 4 * K * q ^ 2 / τ + 4 * K * M₁ := by
      have h4 : (ε + B * M₁) * (4 * K / B) = ε * (4 * K / B) + B * M₁ * (4 * K / B) := by
        ring
      have h5 : ε * (4 * K / B) = 4 * K * (ε / B) := by ring
      have h6 : B * M₁ * (4 * K / B) = 4 * K * M₁ := by field_simp
      have h7 : 4 * K * (ε / B) = 4 * K * (q ^ 2 / τ) := by rw [hεB]
      have h8 : 4 * K * q ^ 2 / τ = 4 * K * (q ^ 2 / τ) := by ring
      linarith [h4, h5, h6, h7, h8]
    have hsum : 2 * (τ + B) * M₂ + 2 * (M₁ * (2 * K)) + (ε + B * M₁) * (4 * K / B)
        ≤ 4 * τ * M₂ + 8 * K * M₁ + 4 * K * q ^ 2 / τ := by linarith [h1, h2, h3]
    exact mul_le_mul_of_nonneg_left hsum hcoef.le
  -- ### (d) 相乘
  have hC2nn : 0 ≤ kernelC τ B P := kernelC_nonneg hτ hB P
  have hC1rhs : 0 ≤ (2 * Real.pi)⁻¹ * (4 * τ) * ((1 + Cd1) * ε) :=
    mul_nonneg (mul_nonneg (by positivity) (by linarith)) (mul_nonneg (by linarith) hε)
  have hprod : kernelA τ B P * kernelC τ B P
      ≤ (2 * Real.pi)⁻¹ * (4 * τ) * ((1 + Cd1) * ε)
        * ((2 * Real.pi)⁻¹ * (4 * τ * M₂ + 8 * K * M₁ + 4 * K * q ^ 2 / τ)) :=
    mul_le_mul hC1 hC2 hC2nn hC1rhs
  refine hprod.trans ?_
  -- ### (e) 展开：`τ` 与 `1/τ` 精确相消
  have hstep1 : (2 * Real.pi)⁻¹ * (4 * τ) * ((1 + Cd1) * ε)
        * ((2 * Real.pi)⁻¹ * (4 * τ * M₂ + 8 * K * M₁ + 4 * K * q ^ 2 / τ))
      = (2 * Real.pi)⁻¹ * (2 * Real.pi)⁻¹
        * ((4 * τ * ((1 + Cd1) * ε))
          * (4 * τ * M₂ + 8 * K * M₁ + 4 * K * q ^ 2 / τ)) := by ring
  rw [hstep1]
  have hstep2 : (4 * τ * ((1 + Cd1) * ε)) * (4 * τ * M₂ + 8 * K * M₁ + 4 * K * q ^ 2 / τ)
      = (1 + Cd1) * (16 * ε * (τ ^ 2 * M₂) + 32 * K * ε * (τ * M₁)
          + 16 * K * q ^ 2 * ε) := by
    field_simp
    ring
  rw [hstep2]
  -- ### (f) 三块归约到 `(16Cd2 + 32Cd1K + 16K)(q²ε)`
  have hτ2M₂ : τ ^ 2 * M₂ ≤ Cd2 * q ^ 2 * ε := by
    have h1 : Cd2 * (k : ℝ) ^ 2 * ε ≤ Cd2 * q ^ 2 * ε :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk2 hCd2) hε
    linarith [hM2sharp, h1]
  have hτM₁ : τ * M₁ ≤ Cd1 * q * ε := by
    have h1 : Cd1 * (k : ℝ) * ε ≤ Cd1 * q * ε :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkq hCd1) hε
    linarith [hM1sharp, h1]
  have hinner : 16 * ε * (τ ^ 2 * M₂) + 32 * K * ε * (τ * M₁) + 16 * K * q ^ 2 * ε
      ≤ (16 * Cd2 + 32 * Cd1 * K + 16 * K) * (q ^ 2 * ε) := by
    have hA : 16 * ε * (τ ^ 2 * M₂) ≤ 16 * Cd2 * (q ^ 2 * ε) := by
      have h3 : 16 * Cd2 * q ^ 2 * ε ^ 2 ≤ 16 * Cd2 * q ^ 2 * ε := by
        have h0 : (0 : ℝ) ≤ 16 * Cd2 * q ^ 2 :=
          mul_nonneg (mul_nonneg (by norm_num) hCd2) (sq_nonneg q)
        calc 16 * Cd2 * q ^ 2 * ε ^ 2 = (16 * Cd2 * q ^ 2) * ε ^ 2 := by ring
          _ ≤ (16 * Cd2 * q ^ 2) * ε := mul_le_mul_of_nonneg_left hε2 h0
          _ = 16 * Cd2 * q ^ 2 * ε := by ring
      calc 16 * ε * (τ ^ 2 * M₂) ≤ 16 * ε * (Cd2 * q ^ 2 * ε) :=
            mul_le_mul_of_nonneg_left hτ2M₂ (mul_nonneg (by norm_num) hε)
        _ = 16 * Cd2 * q ^ 2 * ε ^ 2 := by ring
        _ ≤ 16 * Cd2 * q ^ 2 * ε := h3
        _ = 16 * Cd2 * (q ^ 2 * ε) := by ring
    have hB' : 32 * K * ε * (τ * M₁) ≤ 32 * Cd1 * K * (q ^ 2 * ε) := by
      have hqe : q * ε ^ 2 ≤ q ^ 2 * ε := by
        have e1 : q * ε ^ 2 ≤ q * ε := mul_le_mul_of_nonneg_left hε2 hq0.le
        have e2 : q * ε ≤ q ^ 2 * ε := mul_le_mul_of_nonneg_right hqq hε
        linarith [e1, e2]
      have h0 : (0 : ℝ) ≤ 32 * Cd1 * K :=
        mul_nonneg (mul_nonneg (by norm_num) hCd1) hK
      have h3 : 32 * Cd1 * K * q * ε ^ 2 ≤ 32 * Cd1 * K * q ^ 2 * ε := by
        calc 32 * Cd1 * K * q * ε ^ 2 = (32 * Cd1 * K) * (q * ε ^ 2) := by ring
          _ ≤ (32 * Cd1 * K) * (q ^ 2 * ε) := mul_le_mul_of_nonneg_left hqe h0
          _ = 32 * Cd1 * K * q ^ 2 * ε := by ring
      calc 32 * K * ε * (τ * M₁) ≤ 32 * K * ε * (Cd1 * q * ε) :=
            mul_le_mul_of_nonneg_left hτM₁ (mul_nonneg (mul_nonneg (by norm_num) hK) hε)
        _ = 32 * Cd1 * K * q * ε ^ 2 := by ring
        _ ≤ 32 * Cd1 * K * q ^ 2 * ε := h3
        _ = 32 * Cd1 * K * (q ^ 2 * ε) := by ring
    have hC' : 16 * K * q ^ 2 * ε ≤ 16 * K * (q ^ 2 * ε) := le_of_eq (by ring)
    have hsum := add_le_add (add_le_add hA hB') hC'
    calc (16 * ε * (τ ^ 2 * M₂) + 32 * K * ε * (τ * M₁)) + 16 * K * q ^ 2 * ε
        ≤ (16 * Cd2 * (q ^ 2 * ε) + 32 * Cd1 * K * (q ^ 2 * ε)) + 16 * K * (q ^ 2 * ε) :=
          hsum
      _ = (16 * Cd2 + 32 * Cd1 * K + 16 * K) * (q ^ 2 * ε) := by ring
  -- ### (g) 取 `(2π)⁻² ≤ 1/36`
  have hXnn : (0 : ℝ) ≤ 16 * ε * (τ ^ 2 * M₂) + 32 * K * ε * (τ * M₁)
      + 16 * K * q ^ 2 * ε := by
    have h1 : (0 : ℝ) ≤ 16 * ε * (τ ^ 2 * M₂) :=
      mul_nonneg (mul_nonneg (by norm_num) hε) (mul_nonneg (sq_nonneg τ) hM₂nn)
    have h2 : (0 : ℝ) ≤ 32 * K * ε * (τ * M₁) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hK) hε) (mul_nonneg hτ.le hM₁nn)
    have h3 : (0 : ℝ) ≤ 16 * K * q ^ 2 * ε :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hK) (sq_nonneg q)) hε
    linarith [h1, h2, h3]
  have hcoef : (2 * Real.pi)⁻¹ * (2 * Real.pi)⁻¹ ≤ 1 / 36 := inv_two_pi_sq_le
  calc (2 * Real.pi)⁻¹ * (2 * Real.pi)⁻¹
        * ((1 + Cd1) * (16 * ε * (τ ^ 2 * M₂) + 32 * K * ε * (τ * M₁)
          + 16 * K * q ^ 2 * ε))
      ≤ (1 / 36) * ((1 + Cd1) * (16 * ε * (τ ^ 2 * M₂) + 32 * K * ε * (τ * M₁)
          + 16 * K * q ^ 2 * ε)) :=
        mul_le_mul_of_nonneg_right hcoef (mul_nonneg (by linarith) hXnn)
    _ ≤ (1 / 36) * ((1 + Cd1) * ((16 * Cd2 + 32 * Cd1 * K + 16 * K) * (q ^ 2 * ε))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hinner (by linarith : (0 : ℝ) ≤ 1 + Cd1))
          (by norm_num : (0 : ℝ) ≤ 1 / 36)
    _ = (1 / 36 : ℝ) * (1 + Cd1) * (16 * Cd2 + 32 * Cd1 * K + 16 * K) * q ^ 2 * ε := by
        ring

/-- **参数版的 `(1+K)` 形状**（与 `kernelProd_le_poly` 的输出形状一致）：
用 `16Cd2 + 32Cd1K + 16K ≤ (16Cd2 + 32Cd1 + 16)(1+K)`，代价是把 `16Cd2`
也乘上了 `K`。除非下游接口硬要 `(1+K)`，优先用 `kernelProd_le_poly_sharp_param`。 -/
lemma kernelProd_le_poly_sharp_param_one_add_K {τ B ε M₁ M₂ K Cd1 Cd2 : ℝ} {k : ℕ} {q : ℝ}
    (P : Polynomial ℂ)
    (hτ : 0 < τ) (hB : 0 < B) (hε : 0 ≤ ε) (hK : 0 ≤ K)
    (hCd1 : 0 ≤ Cd1) (hCd2 : 0 ≤ Cd2)
    (hM₁nn : 0 ≤ M₁) (hM₂nn : 0 ≤ M₂)
    (hq1 : 1 ≤ q) (hkq : (k : ℝ) ≤ q) (hτq : τ ≤ q) (hBτ : B ≤ τ)
    (hε1 : ε ≤ 1)
    (hBval : B = ε * τ / q ^ 2)
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
      ≤ (1 / 36 : ℝ) * (1 + Cd1) * (16 * Cd2 + 32 * Cd1 + 16) * (1 + K) * q ^ 2 * ε := by
  have hmain := kernelProd_le_poly_sharp_param P hτ hB hε hK hCd1 hCd2 hM₁nn hM₂nn
    hq1 hkq hτq hBτ hε1 hBval hM1sharp hM2sharp hψ hPε hA1 hA2 hK1 hK2
  refine hmain.trans ?_
  have h0 : (0 : ℝ) ≤ q ^ 2 * ε := mul_nonneg (sq_nonneg q) hε
  have h01 : (0 : ℝ) ≤ (1 / 36 : ℝ) * (1 + Cd1) :=
    mul_nonneg (by norm_num) (by linarith)
  have hc : 16 * Cd2 + 32 * Cd1 * K + 16 * K ≤ (16 * Cd2 + 32 * Cd1 + 16) * (1 + K) := by
    nlinarith [mul_nonneg hCd2 hK, mul_nonneg hCd1 hK, hK, hCd1, hCd2]
  calc (1 / 36 : ℝ) * (1 + Cd1) * (16 * Cd2 + 32 * Cd1 * K + 16 * K) * q ^ 2 * ε
      = ((1 / 36 : ℝ) * (1 + Cd1))
        * ((16 * Cd2 + 32 * Cd1 * K + 16 * K) * (q ^ 2 * ε)) := by ring
    _ ≤ ((1 / 36 : ℝ) * (1 + Cd1))
        * (((16 * Cd2 + 32 * Cd1 + 16) * (1 + K)) * (q ^ 2 * ε)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc h0) h01
    _ = (1 / 36 : ℝ) * (1 + Cd1) * (16 * Cd2 + 32 * Cd1 + 16) * (1 + K) * q ^ 2 * ε := by
        ring

/-! ### §2.2 数值实例 -/

/-- **锐化主引理（`Cd1 = 64`、`Cd2 = 4096` 实例）**：常数
`(1/36)·65·(16·4096 + 32·64 + 16) = 4394000/36 = 122055.55…`，故取 `122056`。

紧形式为 `(1/36)·65·(65536 + 2064K) = 118328.9 + 3726.7K`（见参数版）；
`(1+K)` 形状多出的 `118329K` 完全来自把 `16·Cd2 = 65536` 也乘上 `K`。 -/
lemma kernelProd_le_poly_sharp_small {τ B ε M₁ M₂ K : ℝ} {k : ℕ} {q : ℝ} (P : Polynomial ℂ)
    (hτ : 0 < τ) (hB : 0 < B) (hε : 0 ≤ ε) (hK : 0 ≤ K)
    (hM₁nn : 0 ≤ M₁) (hM₂nn : 0 ≤ M₂)
    (hq1 : 1 ≤ q) (hkq : (k : ℝ) ≤ q) (hτq : τ ≤ q) (hBτ : B ≤ τ)
    (hε1 : ε ≤ 1)
    (hBval : B = ε * τ / q ^ 2)
    (hM1sharp : τ * M₁ ≤ 64 * (k : ℝ) * ε)
    (hM2sharp : τ ^ 2 * M₂ ≤ 4096 * (k : ℝ) ^ 2 * ε)
    (hψ : ∀ μ : ℝ, ‖psi τ B P μ‖ ≤ ε + B * M₁)
    (hPε : ∀ μ : ℝ, |μ| ≤ τ →
      ‖Complex.exp (-(μ : ℂ) * Complex.I) - P.eval ((μ : ℂ))‖ ≤ ε)
    (hA1 : ∀ μ : ℝ, |μ| ≤ τ + B → ‖deriv (fun x : ℝ => psiA P x) μ‖ ≤ M₁)
    (hA2 : ∀ μ : ℝ, |μ| ≤ τ + B → ‖deriv (deriv (fun x : ℝ => psiA P x)) μ‖ ≤ M₂)
    (hK1 : ∀ μ : ℝ, ‖deriv (fun x : ℝ => ((cutoff τ B x : ℝ) : ℂ)) μ‖ ≤ K / B)
    (hK2 : ∀ μ : ℝ, ‖deriv (deriv (fun x : ℝ => ((cutoff τ B x : ℝ) : ℂ))) μ‖ ≤ K / B ^ 2) :
    kernelA τ B P * kernelC τ B P ≤ 122056 * (1 + K) * q ^ 2 * ε := by
  have hmain := kernelProd_le_poly_sharp_param (Cd1 := 64) (Cd2 := 4096) P hτ hB hε hK
    (by norm_num) (by norm_num) hM₁nn hM₂nn hq1 hkq hτq hBτ hε1 hBval hM1sharp hM2sharp
    hψ hPε hA1 hA2 hK1 hK2
  refine hmain.trans ?_
  have h0 : (0 : ℝ) ≤ q ^ 2 * ε := mul_nonneg (sq_nonneg q) hε
  have hc : (1 / 36 : ℝ) * (1 + 64) * (16 * 4096 + 32 * 64 * K + 16 * K)
      ≤ 122056 * (1 + K) := by nlinarith [hK]
  calc (1 / 36 : ℝ) * (1 + 64) * (16 * 4096 + 32 * 64 * K + 16 * K) * q ^ 2 * ε
      = ((1 / 36 : ℝ) * (1 + 64) * (16 * 4096 + 32 * 64 * K + 16 * K)) * (q ^ 2 * ε) := by
        ring
    _ ≤ (122056 * (1 + K)) * (q ^ 2 * ε) := mul_le_mul_of_nonneg_right hc h0
    _ = 122056 * (1 + K) * q ^ 2 * ε := by ring

/-- **锐化主引理（`Cd1 = 10³`、`Cd2 = 10⁶` 实例）**：常数
`(1/36)·1001·(16·10⁶ + 32·10³ + 16) = 16048048016/36 = 445779111.56…`，取 `445779112`。

⚠ `~4.5·10⁸` 完全来自假设 `Cd2 = 10⁶`（`16·Cd2` 项）。`Cd1, Cd2` 是**占位符**时
请用参数版 `kernelProd_le_poly_sharp_param`，那里常数是
`(1/36)(1+Cd1)(16Cd2 + 32Cd1K + 16K)`。 -/
lemma kernelProd_le_poly_sharp {τ B ε M₁ M₂ K : ℝ} {k : ℕ} {q : ℝ} (P : Polynomial ℂ)
    (hτ : 0 < τ) (hB : 0 < B) (hε : 0 ≤ ε) (hK : 0 ≤ K)
    (hM₁nn : 0 ≤ M₁) (hM₂nn : 0 ≤ M₂)
    (hq1 : 1 ≤ q) (hkq : (k : ℝ) ≤ q) (hτq : τ ≤ q) (hBτ : B ≤ τ)
    (hε1 : ε ≤ 1)
    (hBval : B = ε * τ / q ^ 2)
    (hM1sharp : τ * M₁ ≤ 1000 * (k : ℝ) * ε)
    (hM2sharp : τ ^ 2 * M₂ ≤ 1000000 * (k : ℝ) ^ 2 * ε)
    (hψ : ∀ μ : ℝ, ‖psi τ B P μ‖ ≤ ε + B * M₁)
    (hPε : ∀ μ : ℝ, |μ| ≤ τ →
      ‖Complex.exp (-(μ : ℂ) * Complex.I) - P.eval ((μ : ℂ))‖ ≤ ε)
    (hA1 : ∀ μ : ℝ, |μ| ≤ τ + B → ‖deriv (fun x : ℝ => psiA P x) μ‖ ≤ M₁)
    (hA2 : ∀ μ : ℝ, |μ| ≤ τ + B → ‖deriv (deriv (fun x : ℝ => psiA P x)) μ‖ ≤ M₂)
    (hK1 : ∀ μ : ℝ, ‖deriv (fun x : ℝ => ((cutoff τ B x : ℝ) : ℂ)) μ‖ ≤ K / B)
    (hK2 : ∀ μ : ℝ, ‖deriv (deriv (fun x : ℝ => ((cutoff τ B x : ℝ) : ℂ))) μ‖ ≤ K / B ^ 2) :
    kernelA τ B P * kernelC τ B P ≤ 445779112 * (1 + K) * q ^ 2 * ε := by
  have hmain := kernelProd_le_poly_sharp_param (Cd1 := 1000) (Cd2 := 1000000) P hτ hB hε hK
    (by norm_num) (by norm_num) hM₁nn hM₂nn hq1 hkq hτq hBτ hε1 hBval hM1sharp hM2sharp
    hψ hPε hA1 hA2 hK1 hK2
  refine hmain.trans ?_
  have h0 : (0 : ℝ) ≤ q ^ 2 * ε := mul_nonneg (sq_nonneg q) hε
  have hc : (1 / 36 : ℝ) * (1 + 1000) * (16 * 1000000 + 32 * 1000 * K + 16 * K)
      ≤ 445779112 * (1 + K) := by nlinarith [hK]
  calc (1 / 36 : ℝ) * (1 + 1000) * (16 * 1000000 + 32 * 1000 * K + 16 * K) * q ^ 2 * ε
      = ((1 / 36 : ℝ) * (1 + 1000) * (16 * 1000000 + 32 * 1000 * K + 16 * K))
        * (q ^ 2 * ε) := by ring
    _ ≤ (445779112 * (1 + K)) * (q ^ 2 * ε) := mul_le_mul_of_nonneg_right hc h0
    _ = 445779112 * (1 + K) * q ^ 2 * ε := by ring

/-! ## §3 常数与形状的自检 -/

/-- `(1+K)` 形状的两个数值常数的算术自检。 -/
lemma sharp_const_check :
    (1 / 36 : ℝ) * (1 + 64) * (16 * 4096 + 32 * 64 + 16) ≤ 122056
      ∧ (1 / 36 : ℝ) * (1 + 1000) * (16 * 1000000 + 32 * 1000 + 16) ≤ 445779112 :=
  ⟨by norm_num, by norm_num⟩

/-- 常数对 `Cd1, Cd2` 单调不减（`16Cd2 + 32Cd1K + 16K`，`K ≥ 0`）。 -/
lemma sharp_const_mono {Cd1 Cd2 Cd1' Cd2' K : ℝ} (hK : 0 ≤ K)
    (h1 : Cd1 ≤ Cd1') (h2 : Cd2 ≤ Cd2') :
    16 * Cd2 + 32 * Cd1 * K + 16 * K ≤ 16 * Cd2' + 32 * Cd1' * K + 16 * K := by
  nlinarith [h1, h2, hK]

/-! ## §4 假设清单与说明

除 `kernelProd_le_poly` 的全部 side condition（`hτ hB hε hK hM₁nn hM₂nn hq1 hkq hτq hBτ
hBval hψ hPε hA1 hA2 hK1 hK2`）外，本文件：

* **多出** `hε1 : ε ≤ 1`。它用在两处：
  1. `B·M₁ ≤ Cd1·ε` 需要 `kε ≤ q²`；由 `k ≤ q` 与 `ε ≤ 1` 得 `kε ≤ q`，
     再由 `q ≤ q²` 得结论。**这一处只需较弱的 `ε ≤ q`**。
  2. `ε·(τ²M₂) ≤ Cd2·q²ε` 需要 `ε² ≤ ε`（等价于 `k²ε² ≤ q²ε`）。
     这是真正用到 `ε ≤ 1` 的地方；替代品是 `k²ε ≤ q²`。
  在应用里 `ε = epsOf τ δ' (2N+1)` 对 `N` 最终 `≤ 1`，故无实质代价。
* 参数版 `kernelProd_le_poly_sharp_param` 另加 `hCd1 : 0 ≤ Cd1`、`hCd2 : 0 ≤ Cd2`
  （`Cd1, Cd2` 是符号参数，单调性需要非负）。
* **把** `hM1 : τM₁ ≤ 4k³ + τ + 4kτ`、`hM2 : τ²M₂ ≤ 128k⁵ + 8k³τ + τ² + 4kτ²`
  **换成** `hM1sharp : τM₁ ≤ Cd1·k·ε`、`hM2sharp : τ²M₂ ≤ Cd2·k²·ε`。
  这正是并行 collar 分析要证的两条（本文件因此与它解耦）。
* 其余（`hψ hPε hA1 hA2 hK1 hK2 hBτ hε hK` 等）逐字保留。
  其中 `hτq : τ ≤ q` 在证明里**未被实质使用**（锐化后 `τ` 只在 `2(τ+B) ≤ 4τ`
  与 `τ·(1/τ) = 1` 处出现），保留是为了与 `kernelProd_le_poly` 的签名逐字对齐。
* `hM₁nn` 在 §2.1(g) 的 `hXnn` 里用到；`hM₂nn` 在 §2.1(c) 的
  `2(τ+B)M₂ ≤ 4τM₂` 处实质使用。两条都是 `M₁, M₂` 作为上确界的自然性质，
  与 `kernelProd_le_poly` 一致。
-/

end RobustZ
