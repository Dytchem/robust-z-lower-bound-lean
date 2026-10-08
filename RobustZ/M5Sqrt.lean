import RobustZ.M5Quad

/-!
# M5⁗（`M5Sqrt`）：截断尺度 `B = √ε` 的核常数乘积界（`ε^{3/2}` 形状）

## 为什么是 `B = √ε`

`M5Apply.h_zero_le_of_admissible{,_pos}` 与 `FinalSmall.h_zero_lt_of_kernel_decay`
用的是**同一个**截断尺度

```
B = Real.sqrt (epsOf τ δ' (2N+1))     （记 ε := epsOf τ δ' (2N+1)，即 B = √ε）
```

后者（`FinalSmall.lean`）的假设逐字是

```
kernelA τ B (scaledApprox τ (2N+1)) * kernelC τ B (scaledApprox τ (2N+1))
  ≤ ((1 - Real.cos (φ/2))/8)^2 * Real.exp (-η * (2N+2)),
```

所以**只要**把乘积界证成 `B = √ε` 的形状，就能直接接进那条**已经全绿**的链
（不需要动 M3、也不需要改 `FinalSmall`）。本文件给出的就是这条界，以及它的判据。

`M5Quad`（`B = τ/q²`）保留作为备选：它的判据与 `q` 挂钩（`ε ≲ 1/(C q)`），
本文件的判据是 `ε^{3/2} < δ²/(64·Csharp·τ)`，即 `ε ≲ (δ²/(Csharp τ))^{2/3}`。

## 代数（逐步，标明每一处损失）

记 `r := √ε = B`（故 `ε = B²`）。由两条**锐化**（`ε`-线性）collar 输入：

```
M₁ ≤ Cd1·k·ε/τ,        M₂ ≤ Cd2·k²·ε/τ².
```

**(0) `B·M₁ ≤ Cd1·ε`。** `B·M₁ ≤ B·Cd1k·B²/τ = Cd1·ε·(kB/τ) ≤ Cd1·ε`，
最后一步用**额外假设** `hkB : k·B ≤ τ`（即 `kB/τ ≤ 1`）。于是

```
S := ε + B·M₁ ≤ (1 + Cd1)·ε.
```

**(1) `C₁`。** `kernelA_le_support` 给 `C₁ ≤ (2π)⁻¹·2(τ+B)·S`；由 `hBτ : B ≤ τ`
得 `2(τ+B) ≤ 4τ`，再由 (0)：

```
C₁ ≤ (2π)⁻¹·4τ·(1+Cd1)·ε.                                       (★)
```

**(2) `C₂`。** `kernelC_le_support` 的右端是
`2(τ+B)M₂ + 2(M₁(2K)) + (ε+B·M₁)(4K/B)`。第三项精确拆开，且 `ε/B = B`（因 `B² = ε`）：

```
(ε+B·M₁)(4K/B) = 4K·(ε/B) + 4K·M₁ = 4K·B + 4K·M₁.
```

四项（`B ≤ τ`、`M₁ ≤ Cd1kε/τ`、`M₂ ≤ Cd2k²ε/τ²`）：

```
2(τ+B)M₂ ≤ 4τ·M₂ ≤ 4·Cd2·k²·ε/τ,
2(M₁·2K) = 4K·M₁ ≤ 4·K·Cd1·k·ε/τ,
4K·B      = 4K·B,
4K·M₁     ≤ 4·K·Cd1·k·ε/τ,
```

```
C₂ ≤ (2π)⁻¹·(4·Cd2·k²·ε/τ + 8·K·Cd1·k·ε/τ + 4·K·B).            (★★)
```

**(3) 相乘。** `(★)×(★★)`，`4τ` 与 `1/τ` 精确相消，`ε = B²`：

```
(2π)²·C₁C₂ ≤ (1+Cd1)·(16·Cd2·k²·B⁴ + 32·K·Cd1·k·B⁴ + 16·K·τ·B³).  (♦)
```

再用两条**额外假设**把 `B⁴` 拉平成 `τ·B³`：

```
hkB  : k·B ≤ τ    ⟹  k·B⁴   = (kB)·B³  ≤ τ·B³,
hk2B : k²·B ≤ τ   ⟹  k²·B⁴  = (k²B)·B³ ≤ τ·B³,
```

```
(2π)²·C₁C₂ ≤ (1+Cd1)·(16·Cd2 + 32·Cd1·K + 16·K)·τ·B³.            (♦♦)
```

**(4) `(2π)⁻² ≤ 1/36`**（`π > 3`，`M5Sharp.inv_two_pi_sq_le`）与 `B³ = ε^{3/2}` 即得

```
kernelA τ B P · kernelC τ B P ≤ Csharp·τ·ε^{3/2},
Csharp(Cd1,Cd2,K) = (1/36)·(1+Cd1)·(16·Cd2 + 32·Cd1·K + 16·K)     （`sqrtC0`）
```

**常数与 `k` 无关**，并且与 `M5Sharp`（`B = ετ/q²`）的常数**逐字相同**：
`ε` 的次数从 1 升到 `3/2`，代价是三条只涉及 `B` 的侧条件（`B ≤ τ`、`kB ≤ τ`、`k²B ≤ τ`），
它们都与 `ε` 的大小无关，且比 `M5Sharp` 的 `ε ≤ 1` 更容易满足。

## 判据

```
ε^{3/2} < (1/8)²/(Csharp·τ)   ⟹   C₁C₂ < (1/8)²,
ε^{3/2} < δ²/(64·Csharp·τ)    ⟹   C₁C₂ < (δ/8)²   （δ = 1-cos(φ/2)，`FinalSmall` 的阈值）
```

## 侧条件清单（相对 `M5Sharp.kernelProd_le_poly_sharp_param`）

* `hBval` 从 `B = ε·τ/q²` **换成** `B = Real.sqrt ε`（本文件全部要点）。
* **去掉** `hε1 : ε ≤ 1`、`hτq : τ ≤ q`、参数 `q`（`B = √ε` 下它们都不需要）。
* **多出** `hkB : (k:ℝ)·B ≤ τ` 与 `hk2B : (k:ℝ)²·B ≤ τ`（都只涉及 `B`）。
  应用里 `k = 2N+1`、`B = √(epsOf τ δ' (2N+1)) ≈ e^{-δ'(2N+1)/2}`，
  两条都是「指数压倒多项式」型的显然事实；`hkB` 也可由 `hk2B` 与 `k ≥ 1` 推出
  （见 `kernelProd_le_poly_sqrt_of_k2B`）。
* 备用：`kernelProd_le_poly_sqrt_kdep` 用常数 `sqrtC`（含 `k², k`）换取**更弱**的侧条件
  （只要 `Cd1·k·B ≤ τ`，不要 `hk2B`）；`kernelProd_le_poly_sqrt_general`
  连 `hkB` 都不要，代价是常数里出现 `k³` 项。
-/

set_option maxHeartbeats 1000000

noncomputable section

namespace RobustZ

open Filter MeasureTheory
open scoped Real

/-! ## §1 常数与 `ε^{3/2}` 的换算 -/

/-- **`B = √ε` 版的显式常数（与 `k` 无关）**

```
Csharp(Cd1,Cd2,K) = (1/36)·(1+Cd1)·(16·Cd2 + 32·Cd1·K + 16·K).
```

三项系数依次来自 `2(τ+B)M₂`（`16Cd2`）、两份 `4K·M₁`（`32Cd1K`）、
`4K·ε/B = 4K·B`（`16K`）——与 `M5Sharp` 的 `q²ε` 版**逐字相同**。 -/
def sqrtC0 (Cd1 Cd2 K : ℝ) : ℝ :=
  (1 / 36) * (1 + Cd1) * (16 * Cd2 + 32 * Cd1 * K + 16 * K)

/-- `sqrtC0` 的展开式（`rfl`）。 -/
lemma sqrtC0_def (Cd1 Cd2 K : ℝ) :
    sqrtC0 Cd1 Cd2 K = (1 / 36) * (1 + Cd1) * (16 * Cd2 + 32 * Cd1 * K + 16 * K) := rfl

/-- `Cd1, Cd2, K ≥ 0` 时 `sqrtC0 ≥ 0`。 -/
lemma sqrtC0_nonneg {Cd1 Cd2 K : ℝ} (hCd1 : 0 ≤ Cd1) (hCd2 : 0 ≤ Cd2) (hK : 0 ≤ K) :
    0 ≤ sqrtC0 Cd1 Cd2 K := by
  rw [sqrtC0_def]
  have h1 : (0 : ℝ) ≤ 1 + Cd1 := by linarith
  have h2 : (0 : ℝ) ≤ 16 * Cd2 + 32 * Cd1 * K + 16 * K := by
    have ha : (0 : ℝ) ≤ 16 * Cd2 := by linarith
    have hb : (0 : ℝ) ≤ 32 * Cd1 * K := by positivity
    have hc : (0 : ℝ) ≤ 16 * K := by linarith
    linarith
  exact mul_nonneg (mul_nonneg (by norm_num) h1) h2

/-- **`B = √ε` 版的显式常数（含 `k`）**

```
Csharp(Cd1,Cd2,K,k) = (1/36)·(32·Cd2·k² + 64·K·Cd1·k + 32·K).
```

这是「只有 `Cd1·k·B ≤ τ`、不要 `k²·B ≤ τ`」的代价（见 `kernelProd_le_poly_sqrt_kdep`）。 -/
def sqrtC (Cd1 Cd2 K : ℝ) (k : ℕ) : ℝ :=
  (1 / 36) * (32 * Cd2 * (k : ℝ) ^ 2 + 64 * K * Cd1 * (k : ℝ) + 32 * K)

/-- `sqrtC` 的展开式（`rfl`）。 -/
lemma sqrtC_def (Cd1 Cd2 K : ℝ) (k : ℕ) :
    sqrtC Cd1 Cd2 K k
      = (1 / 36) * (32 * Cd2 * (k : ℝ) ^ 2 + 64 * K * Cd1 * (k : ℝ) + 32 * K) := rfl

/-- `Cd1, Cd2, K ≥ 0` 时 `sqrtC ≥ 0`。 -/
lemma sqrtC_nonneg {Cd1 Cd2 K : ℝ} (hCd1 : 0 ≤ Cd1) (hCd2 : 0 ≤ Cd2) (hK : 0 ≤ K)
    (k : ℕ) : 0 ≤ sqrtC Cd1 Cd2 K k := by
  rw [sqrtC_def]
  refine mul_nonneg (by norm_num) ?_
  have h1 : (0 : ℝ) ≤ 32 * Cd2 * (k : ℝ) ^ 2 := by positivity
  have h2 : (0 : ℝ) ≤ 64 * K * Cd1 * (k : ℝ) := by positivity
  have h3 : (0 : ℝ) ≤ 32 * K := by linarith
  linarith

/-- **`ε ≥ 0` 时 `ε^{3/2} = (√ε)³`**（`Real.rpow` 与自然数幂之间的换算）。 -/
lemma rpow_three_halves_eq_sqrt_cube {ε : ℝ} (hε : 0 ≤ ε) :
    ε ^ (3 / 2 : ℝ) = Real.sqrt ε ^ 3 := by
  have h1 : (Real.sqrt ε) ^ (3 : ℝ) = Real.sqrt ε ^ 3 := Real.rpow_natCast _ 3
  rw [← h1, Real.sqrt_eq_rpow, ← Real.rpow_mul (x := ε) hε (1 / 2) (3 : ℝ)]
  norm_num

/-! ## §2 主引理（`B = √ε`，常数与 `k` 无关） -/

/-- **`C₂` 的公共上界**（三个主引理共用；与 `B = √ε` 的代数无关的部分）：

```
C₂ ≤ (2π)⁻¹·(4·Cd2·k²·ε/τ + 8·K·Cd1·k·ε/τ + 4·K·B).
```

只用 `B ≤ τ`、`B = √ε`（后者给 `ε/B = B`）与两条锐化输入。 -/
lemma kernelC_le_sqrt_aux {τ B ε M₁ M₂ K Cd1 Cd2 : ℝ} {k : ℕ} (P : Polynomial ℂ)
    (hτ : 0 < τ) (hB : 0 < B) (hε : 0 ≤ ε) (hK : 0 ≤ K)
    (hCd1 : 0 ≤ Cd1) (hCd2 : 0 ≤ Cd2) (hM₂nn : 0 ≤ M₂)
    (hBτ : B ≤ τ) (hBval : B = Real.sqrt ε)
    (hM1sharp : τ * M₁ ≤ Cd1 * (k : ℝ) * ε)
    (hM2sharp : τ ^ 2 * M₂ ≤ Cd2 * (k : ℝ) ^ 2 * ε)
    (hPε : ∀ μ : ℝ, |μ| ≤ τ →
      ‖Complex.exp (-(μ : ℂ) * Complex.I) - P.eval ((μ : ℂ))‖ ≤ ε)
    (hA1 : ∀ μ : ℝ, |μ| ≤ τ + B → ‖deriv (fun x : ℝ => psiA P x) μ‖ ≤ M₁)
    (hA2 : ∀ μ : ℝ, |μ| ≤ τ + B → ‖deriv (deriv (fun x : ℝ => psiA P x)) μ‖ ≤ M₂)
    (hK1 : ∀ μ : ℝ, ‖deriv (fun x : ℝ => ((cutoff τ B x : ℝ) : ℂ)) μ‖ ≤ K / B)
    (hK2 : ∀ μ : ℝ, ‖deriv (deriv (fun x : ℝ => ((cutoff τ B x : ℝ) : ℂ))) μ‖ ≤ K / B ^ 2) :
    kernelC τ B P ≤ (2 * Real.pi)⁻¹ *
      (4 * Cd2 * (k : ℝ) ^ 2 * ε / τ + 8 * K * Cd1 * (k : ℝ) * ε / τ + 4 * K * B) := by
  have hBB : B * B = ε := by
    rw [hBval]
    simpa [pow_two] using Real.sq_sqrt hε
  have hεB : ε / B = B := by
    rw [div_eq_iff hB.ne']
    exact hBB.symm
  have hM1le : M₁ ≤ Cd1 * (k : ℝ) * ε / τ := by
    rw [le_div_iff₀ hτ]
    calc M₁ * τ = τ * M₁ := by ring
      _ ≤ Cd1 * (k : ℝ) * ε := hM1sharp
  have hM2le : M₂ ≤ Cd2 * (k : ℝ) ^ 2 * ε / τ ^ 2 := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < τ ^ 2)]
    calc M₂ * τ ^ 2 = τ ^ 2 * M₂ := by ring
      _ ≤ Cd2 * (k : ℝ) ^ 2 * ε := hM2sharp
  refine (kernelC_le_support hτ hB P hε hPε hA1 hA2 hK1 hK2).trans ?_
  have hcoef : (0 : ℝ) < (2 * Real.pi)⁻¹ := by positivity
  have h1 : 2 * (τ + B) * M₂ ≤ 4 * Cd2 * (k : ℝ) ^ 2 * ε / τ := by
    have ha : 2 * (τ + B) * M₂ ≤ 4 * τ * M₂ := by nlinarith [hBτ, hM₂nn, hτ]
    have hb : 4 * τ * M₂ ≤ 4 * τ * (Cd2 * (k : ℝ) ^ 2 * ε / τ ^ 2) :=
      mul_le_mul_of_nonneg_left hM2le (by linarith)
    have hc : 4 * τ * (Cd2 * (k : ℝ) ^ 2 * ε / τ ^ 2) = 4 * Cd2 * (k : ℝ) ^ 2 * ε / τ := by
      field_simp
    linarith [ha, hb, hc]
  have hM1' : 4 * K * M₁ ≤ 4 * K * Cd1 * (k : ℝ) * ε / τ := by
    have h4K : (0 : ℝ) ≤ 4 * K := mul_nonneg (by norm_num) hK
    have h := mul_le_mul_of_nonneg_left hM1le h4K
    calc 4 * K * M₁ ≤ 4 * K * (Cd1 * (k : ℝ) * ε / τ) := h
      _ = 4 * K * Cd1 * (k : ℝ) * ε / τ := by ring
  have h3 : (ε + B * M₁) * (4 * K / B) = 4 * K * B + 4 * K * M₁ := by
    have h4 : (ε + B * M₁) * (4 * K / B) = ε * (4 * K / B) + B * M₁ * (4 * K / B) := by
      ring
    have h5 : ε * (4 * K / B) = 4 * K * (ε / B) := by ring
    have h6 : B * M₁ * (4 * K / B) = 4 * K * M₁ := by field_simp
    have h7 : 4 * K * (ε / B) = 4 * K * B := by rw [hεB]
    linarith [h4, h5, h6, h7]
  have h2 : 2 * (M₁ * (2 * K)) = 4 * K * M₁ := by ring
  have hsum : 2 * (τ + B) * M₂ + 2 * (M₁ * (2 * K)) + (ε + B * M₁) * (4 * K / B)
      ≤ 4 * Cd2 * (k : ℝ) ^ 2 * ε / τ + 8 * K * Cd1 * (k : ℝ) * ε / τ + 4 * K * B := by
    have h9 : 4 * K * Cd1 * (k : ℝ) * ε / τ + 4 * K * Cd1 * (k : ℝ) * ε / τ
        = 8 * K * Cd1 * (k : ℝ) * ε / τ := by ring
    linarith [h1, h2, h3, hM1', h9]
  exact mul_le_mul_of_nonneg_left hsum hcoef.le

/-- **核心：截断尺度 `B = √ε` 时的乘积界（`ε^{3/2}` 形状，`Csharp = sqrtC0 Cd1 Cd2 K`）。**

与 `M5Sharp.kernelProd_le_poly_sharp_param`（`B = ετ/q²`，结论 `q²ε`）相比：

* `hBval` 换成 `B = Real.sqrt ε`，结论换成 `sqrtC0·τ·ε^{3/2}`；
* 常数**不含 `k`**、也不含 `q`（三项系数与 `M5Sharp` 逐字相同）；
* 侧条件去掉 `ε ≤ 1`、`τ ≤ q`，多出两条**只涉及 `B`** 的：
  `hkB : k·B ≤ τ`（⟹ `B·M₁ ≤ Cd1ε`）与 `hk2B : k²·B ≤ τ`（⟹ `k²B⁴ ≤ τB³`）。

不需要 `q`、不需要 `ε ≤ 1`。若只有 `hkB` 而没有 `hk2B`，用
`kernelProd_le_poly_sqrt_kdep`（常数 `sqrtC` 含 `k²,k`）。 -/
lemma kernelProd_le_poly_sqrt {τ B ε M₁ M₂ K Cd1 Cd2 : ℝ} {k : ℕ} (P : Polynomial ℂ)
    (hτ : 0 < τ) (hB : 0 < B) (hε : 0 ≤ ε) (hK : 0 ≤ K)
    (hCd1 : 0 ≤ Cd1) (hCd2 : 0 ≤ Cd2)
    (hM₁nn : 0 ≤ M₁) (hM₂nn : 0 ≤ M₂)
    (hBτ : B ≤ τ) (hkB : (k : ℝ) * B ≤ τ) (hk2B : (k : ℝ) ^ 2 * B ≤ τ)
    (hBval : B = Real.sqrt ε)
    (hM1sharp : τ * M₁ ≤ Cd1 * (k : ℝ) * ε)
    (hM2sharp : τ ^ 2 * M₂ ≤ Cd2 * (k : ℝ) ^ 2 * ε)
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
  have hM1le : M₁ ≤ Cd1 * (k : ℝ) * ε / τ := by
    rw [le_div_iff₀ hτ]
    calc M₁ * τ = τ * M₁ := by ring
      _ ≤ Cd1 * (k : ℝ) * ε := hM1sharp
  have hBM1 : B * M₁ ≤ Cd1 * ε := by
    have h1 : B * M₁ ≤ B * (Cd1 * (k : ℝ) * ε / τ) := mul_le_mul_of_nonneg_left hM1le hB.le
    have h2 : B * (Cd1 * (k : ℝ) * ε / τ) = Cd1 * ε * ((k : ℝ) * B / τ) := by
      field_simp
    have h3 : (k : ℝ) * B / τ ≤ 1 := by
      rw [div_le_one hτ]
      exact hkB
    have h4 : Cd1 * ε * ((k : ℝ) * B / τ) ≤ Cd1 * ε * 1 :=
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
  -- ### (2) `C₂ ≤ (2π)⁻¹·(4Cd2k²ε/τ + 8KCd1kε/τ + 4KB)`（公共引理 `kernelC_le_sqrt_aux`）
  have hC2 := kernelC_le_sqrt_aux P hτ hB hε hK hCd1 hCd2 hM₂nn hBτ hBval hM1sharp hM2sharp
    hPε hA1 hA2 hK1 hK2
  -- ### (3) 相乘、展开
  have hC2nn : 0 ≤ kernelC τ B P := kernelC_nonneg hτ hB P
  have hC1rhs : 0 ≤ (2 * Real.pi)⁻¹ * (4 * τ * ((1 + Cd1) * ε)) :=
    mul_nonneg (by positivity)
      (mul_nonneg (mul_nonneg (by norm_num) hτ.le) (mul_nonneg (by linarith) hε))
  have hprod : kernelA τ B P * kernelC τ B P
      ≤ (2 * Real.pi)⁻¹ * (4 * τ * ((1 + Cd1) * ε))
        * ((2 * Real.pi)⁻¹ *
          (4 * Cd2 * (k : ℝ) ^ 2 * ε / τ + 8 * K * Cd1 * (k : ℝ) * ε / τ + 4 * K * B)) :=
    mul_le_mul hC1 hC2 hC2nn hC1rhs
  refine hprod.trans ?_
  have hstep1 : (2 * Real.pi)⁻¹ * (4 * τ * ((1 + Cd1) * ε))
        * ((2 * Real.pi)⁻¹ *
          (4 * Cd2 * (k : ℝ) ^ 2 * ε / τ + 8 * K * Cd1 * (k : ℝ) * ε / τ + 4 * K * B))
      = (2 * Real.pi)⁻¹ * (2 * Real.pi)⁻¹
        * ((4 * τ * ((1 + Cd1) * ε))
          * (4 * Cd2 * (k : ℝ) ^ 2 * ε / τ + 8 * K * Cd1 * (k : ℝ) * ε / τ + 4 * K * B)) := by
    ring
  rw [hstep1]
  have hstep2 : (4 * τ * ((1 + Cd1) * ε))
        * (4 * Cd2 * (k : ℝ) ^ 2 * ε / τ + 8 * K * Cd1 * (k : ℝ) * ε / τ + 4 * K * B)
      = (1 + Cd1) * (16 * Cd2 * (k : ℝ) ^ 2 * B ^ 4 + 32 * K * Cd1 * (k : ℝ) * B ^ 4
          + 16 * K * τ * B ^ 3) := by
    rw [← hBB]
    field_simp
    try ring
  rw [hstep2]
  -- ### (4) 拉平 `B⁴ → τB³`（用 `hkB`、`hk2B`、`hBτ`）
  have hkey : 16 * Cd2 * (k : ℝ) ^ 2 * B ^ 4 + 32 * K * Cd1 * (k : ℝ) * B ^ 4
        + 16 * K * τ * B ^ 3
      ≤ (16 * Cd2 + 32 * Cd1 * K + 16 * K) * (τ * B ^ 3) := by
    have hB3nn : (0 : ℝ) ≤ B ^ 3 := pow_nonneg hB.le 3
    have hB4 : B ^ 4 ≤ τ * B ^ 3 := by
      have h := mul_le_mul_of_nonneg_right hBτ hB3nn
      calc B ^ 4 = B * B ^ 3 := by ring
        _ ≤ τ * B ^ 3 := h
    have hk2 : (k : ℝ) ^ 2 * B ^ 4 ≤ τ * B ^ 3 := by
      have h := mul_le_mul_of_nonneg_right hk2B hB3nn
      calc (k : ℝ) ^ 2 * B ^ 4 = ((k : ℝ) ^ 2 * B) * B ^ 3 := by ring
        _ ≤ τ * B ^ 3 := h
    have hk1 : (k : ℝ) * B ^ 4 ≤ τ * B ^ 3 := by
      have h := mul_le_mul_of_nonneg_right hkB hB3nn
      calc (k : ℝ) * B ^ 4 = ((k : ℝ) * B) * B ^ 3 := by ring
        _ ≤ τ * B ^ 3 := h
    have hA : 16 * Cd2 * (k : ℝ) ^ 2 * B ^ 4 ≤ 16 * Cd2 * (τ * B ^ 3) := by
      calc 16 * Cd2 * (k : ℝ) ^ 2 * B ^ 4 = (16 * Cd2) * ((k : ℝ) ^ 2 * B ^ 4) := by ring
        _ ≤ (16 * Cd2) * (τ * B ^ 3) :=
            mul_le_mul_of_nonneg_left hk2 (mul_nonneg (by norm_num) hCd2)
    have hB' : 32 * K * Cd1 * (k : ℝ) * B ^ 4 ≤ 32 * K * Cd1 * (τ * B ^ 3) := by
      calc 32 * K * Cd1 * (k : ℝ) * B ^ 4 = (32 * K * Cd1) * ((k : ℝ) * B ^ 4) := by ring
        _ ≤ (32 * K * Cd1) * (τ * B ^ 3) :=
            mul_le_mul_of_nonneg_left hk1 (mul_nonneg (mul_nonneg (by norm_num) hK) hCd1)
    have hC' : 16 * K * τ * B ^ 3 = 16 * K * (τ * B ^ 3) := by ring
    have hsum := add_le_add (add_le_add hA hB') (le_of_eq hC')
    calc 16 * Cd2 * (k : ℝ) ^ 2 * B ^ 4 + 32 * K * Cd1 * (k : ℝ) * B ^ 4
          + 16 * K * τ * B ^ 3
        = (16 * Cd2 * (k : ℝ) ^ 2 * B ^ 4 + 32 * K * Cd1 * (k : ℝ) * B ^ 4)
          + 16 * K * τ * B ^ 3 := by ring
      _ ≤ (16 * Cd2 * (τ * B ^ 3) + 32 * K * Cd1 * (τ * B ^ 3)) + 16 * K * (τ * B ^ 3) := hsum
      _ = (16 * Cd2 + 32 * Cd1 * K + 16 * K) * (τ * B ^ 3) := by ring
  have hX1nn : (0 : ℝ) ≤ 16 * Cd2 * (k : ℝ) ^ 2 * B ^ 4 + 32 * K * Cd1 * (k : ℝ) * B ^ 4
      + 16 * K * τ * B ^ 3 := by
    have h1 : (0 : ℝ) ≤ 16 * Cd2 * (k : ℝ) ^ 2 * B ^ 4 := by positivity
    have h2 : (0 : ℝ) ≤ 32 * K * Cd1 * (k : ℝ) * B ^ 4 := by positivity
    have h3 : (0 : ℝ) ≤ 16 * K * τ * B ^ 3 := by positivity
    linarith
  -- ### (5) 取 `(2π)⁻² ≤ 1/36`
  have hfinal : (2 * Real.pi)⁻¹ * (2 * Real.pi)⁻¹
        * ((1 + Cd1) * (16 * Cd2 * (k : ℝ) ^ 2 * B ^ 4 + 32 * K * Cd1 * (k : ℝ) * B ^ 4
          + 16 * K * τ * B ^ 3))
      ≤ (1 / 36 : ℝ) * (1 + Cd1) * (16 * Cd2 + 32 * Cd1 * K + 16 * K) * τ * ε ^ (3 / 2 : ℝ) := by
    have hcoef : (2 * Real.pi)⁻¹ * (2 * Real.pi)⁻¹ ≤ 1 / 36 := inv_two_pi_sq_le
    calc ((2 * Real.pi)⁻¹ * (2 * Real.pi)⁻¹)
          * ((1 + Cd1) * (16 * Cd2 * (k : ℝ) ^ 2 * B ^ 4 + 32 * K * Cd1 * (k : ℝ) * B ^ 4
            + 16 * K * τ * B ^ 3))
        ≤ (1 / 36) * ((1 + Cd1) * (16 * Cd2 * (k : ℝ) ^ 2 * B ^ 4
            + 32 * K * Cd1 * (k : ℝ) * B ^ 4 + 16 * K * τ * B ^ 3)) :=
          mul_le_mul_of_nonneg_right hcoef (mul_nonneg (by linarith) hX1nn)
      _ ≤ (1 / 36) * ((1 + Cd1) * ((16 * Cd2 + 32 * Cd1 * K + 16 * K) * (τ * B ^ 3))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hkey (by linarith)) (by norm_num)
      _ = (1 / 36 : ℝ) * (1 + Cd1) * (16 * Cd2 + 32 * Cd1 * K + 16 * K) * τ
            * ε ^ (3 / 2 : ℝ) := by
          rw [hB3]
          ring
  simpa only [sqrtC0] using hfinal

/-! ### §2.1 替代形状：常数含 `k`（侧条件更弱，只要 `Cd1·k·B ≤ τ`） -/

/-- **`B = √ε` 的「常数含 `k`」形状**：只要 `Cd1·k·B ≤ τ`（**不要** `hk2B`），
代价是常数 `sqrtC Cd1 Cd2 K k = (1/36)·(32·Cd2·k² + 64·K·Cd1·k + 32·K)`。

`hBk` 的唯一作用是由 `Cd1kB³/τ ≤ ε` 得 `B·M₁ ≤ ε`（即 `S ≤ 2ε`）；
不用 `hkB`，只需 `B ≤ τ` 就能把 `B⁴` 拉平成 `τB³`（这一步现在带上了 `k²`、`k`）。 -/
lemma kernelProd_le_poly_sqrt_kdep {τ B ε M₁ M₂ K Cd1 Cd2 : ℝ} {k : ℕ} (P : Polynomial ℂ)
    (hτ : 0 < τ) (hB : 0 < B) (hε : 0 ≤ ε) (hK : 0 ≤ K)
    (hCd1 : 0 ≤ Cd1) (hCd2 : 0 ≤ Cd2)
    (hM₁nn : 0 ≤ M₁) (hM₂nn : 0 ≤ M₂)
    (hBτ : B ≤ τ) (hBk : Cd1 * (k : ℝ) * B ≤ τ)
    (hBval : B = Real.sqrt ε)
    (hM1sharp : τ * M₁ ≤ Cd1 * (k : ℝ) * ε)
    (hM2sharp : τ ^ 2 * M₂ ≤ Cd2 * (k : ℝ) ^ 2 * ε)
    (hψ : ∀ μ : ℝ, ‖psi τ B P μ‖ ≤ ε + B * M₁)
    (hPε : ∀ μ : ℝ, |μ| ≤ τ →
      ‖Complex.exp (-(μ : ℂ) * Complex.I) - P.eval ((μ : ℂ))‖ ≤ ε)
    (hA1 : ∀ μ : ℝ, |μ| ≤ τ + B → ‖deriv (fun x : ℝ => psiA P x) μ‖ ≤ M₁)
    (hA2 : ∀ μ : ℝ, |μ| ≤ τ + B → ‖deriv (deriv (fun x : ℝ => psiA P x)) μ‖ ≤ M₂)
    (hK1 : ∀ μ : ℝ, ‖deriv (fun x : ℝ => ((cutoff τ B x : ℝ) : ℂ)) μ‖ ≤ K / B)
    (hK2 : ∀ μ : ℝ, ‖deriv (deriv (fun x : ℝ => ((cutoff τ B x : ℝ) : ℂ))) μ‖ ≤ K / B ^ 2) :
    kernelA τ B P * kernelC τ B P ≤ sqrtC Cd1 Cd2 K k * τ * ε ^ (3 / 2 : ℝ) := by
  have hBB : B * B = ε := by
    rw [hBval]
    simpa [pow_two] using Real.sq_sqrt hε
  have hB3 : B ^ 3 = ε ^ (3 / 2 : ℝ) := by
    rw [rpow_three_halves_eq_sqrt_cube hε, ← hBval]
  have hM1le : M₁ ≤ Cd1 * (k : ℝ) * ε / τ := by
    rw [le_div_iff₀ hτ]
    calc M₁ * τ = τ * M₁ := by ring
      _ ≤ Cd1 * (k : ℝ) * ε := hM1sharp
  have hBM1 : B * M₁ ≤ Cd1 * (k : ℝ) * B ^ 3 / τ := by
    have h1 : B * M₁ ≤ B * (Cd1 * (k : ℝ) * ε / τ) := mul_le_mul_of_nonneg_left hM1le hB.le
    have h2 : B * (Cd1 * (k : ℝ) * ε / τ) = Cd1 * (k : ℝ) * B ^ 3 / τ := by
      rw [← hBB]
      ring
    linarith [h1, h2]
  have hBM1ε : B * M₁ ≤ ε := by
    have h2 : Cd1 * (k : ℝ) * B ^ 3 / τ ≤ B * B := by
      rw [div_le_iff₀ hτ]
      have h3 : (Cd1 * (k : ℝ) * B) * (B * B) ≤ τ * (B * B) :=
        mul_le_mul_of_nonneg_right hBk (mul_nonneg hB.le hB.le)
      have h4 : (Cd1 * (k : ℝ) * B) * (B * B) = Cd1 * (k : ℝ) * B ^ 3 := by ring
      have h5 : τ * (B * B) = (B * B) * τ := by ring
      linarith [h3, h4, h5]
    have h6 := le_trans hBM1 h2
    rwa [hBB] at h6
  have hS : ε + B * M₁ ≤ 2 * ε := by linarith [hBM1ε, hε]
  have hSnn : 0 ≤ ε + B * M₁ := by
    have h := mul_nonneg hB.le hM₁nn
    linarith [hε]
  have hC1 : kernelA τ B P ≤ (2 * Real.pi)⁻¹ * (8 * τ * ε) := by
    refine (kernelA_le_support hτ hB P hψ).trans ?_
    have hcoef : (0 : ℝ) < (2 * Real.pi)⁻¹ := by positivity
    have h1 : 2 * (τ + B) ≤ 4 * τ := by linarith
    have h3 : 2 * (τ + B) * (ε + B * M₁) ≤ 4 * τ * (ε + B * M₁) :=
      mul_le_mul_of_nonneg_right h1 hSnn
    have h4 : 4 * τ * (ε + B * M₁) ≤ 4 * τ * (2 * ε) :=
      mul_le_mul_of_nonneg_left hS (by linarith)
    have h5 : 2 * (τ + B) * (ε + B * M₁) ≤ 8 * τ * ε := by linarith [h3, h4]
    calc (2 * Real.pi)⁻¹ * (2 * (τ + B)) * (ε + B * M₁)
        = (2 * Real.pi)⁻¹ * (2 * (τ + B) * (ε + B * M₁)) := by ring
      _ ≤ (2 * Real.pi)⁻¹ * (8 * τ * ε) := mul_le_mul_of_nonneg_left h5 hcoef.le
  have hC2 := kernelC_le_sqrt_aux P hτ hB hε hK hCd1 hCd2 hM₂nn hBτ hBval hM1sharp hM2sharp
    hPε hA1 hA2 hK1 hK2
  have hC2nn : 0 ≤ kernelC τ B P := kernelC_nonneg hτ hB P
  have hC1rhs : 0 ≤ (2 * Real.pi)⁻¹ * (8 * τ * ε) :=
    mul_nonneg (by positivity) (mul_nonneg (mul_nonneg (by norm_num) hτ.le) hε)
  have hprod : kernelA τ B P * kernelC τ B P
      ≤ (2 * Real.pi)⁻¹ * (8 * τ * ε)
        * ((2 * Real.pi)⁻¹ *
          (4 * Cd2 * (k : ℝ) ^ 2 * ε / τ + 8 * K * Cd1 * (k : ℝ) * ε / τ + 4 * K * B)) :=
    mul_le_mul hC1 hC2 hC2nn hC1rhs
  refine hprod.trans ?_
  have hstep1 : (2 * Real.pi)⁻¹ * (8 * τ * ε)
        * ((2 * Real.pi)⁻¹ *
          (4 * Cd2 * (k : ℝ) ^ 2 * ε / τ + 8 * K * Cd1 * (k : ℝ) * ε / τ + 4 * K * B))
      = (2 * Real.pi)⁻¹ * (2 * Real.pi)⁻¹
        * ((8 * τ * ε)
          * (4 * Cd2 * (k : ℝ) ^ 2 * ε / τ + 8 * K * Cd1 * (k : ℝ) * ε / τ + 4 * K * B)) := by
    ring
  rw [hstep1]
  have hstep2 : (8 * τ * ε)
        * (4 * Cd2 * (k : ℝ) ^ 2 * ε / τ + 8 * K * Cd1 * (k : ℝ) * ε / τ + 4 * K * B)
      = 32 * Cd2 * (k : ℝ) ^ 2 * B ^ 4 + 64 * K * Cd1 * (k : ℝ) * B ^ 4
        + 32 * K * τ * B ^ 3 := by
    rw [← hBB]
    field_simp
    try ring
  rw [hstep2]
  have hkey : 32 * Cd2 * (k : ℝ) ^ 2 * B ^ 4 + 64 * K * Cd1 * (k : ℝ) * B ^ 4
        + 32 * K * τ * B ^ 3
      ≤ (32 * Cd2 * (k : ℝ) ^ 2 + 64 * K * Cd1 * (k : ℝ) + 32 * K) * (τ * B ^ 3) := by
    have hB3nn : (0 : ℝ) ≤ B ^ 3 := pow_nonneg hB.le 3
    have hB4 : B ^ 4 ≤ τ * B ^ 3 := by
      have h := mul_le_mul_of_nonneg_right hBτ hB3nn
      calc B ^ 4 = B * B ^ 3 := by ring
        _ ≤ τ * B ^ 3 := h
    have h1 : 32 * Cd2 * (k : ℝ) ^ 2 * B ^ 4 ≤ 32 * Cd2 * (k : ℝ) ^ 2 * (τ * B ^ 3) := by
      calc 32 * Cd2 * (k : ℝ) ^ 2 * B ^ 4 = (32 * Cd2 * (k : ℝ) ^ 2) * B ^ 4 := by ring
        _ ≤ (32 * Cd2 * (k : ℝ) ^ 2) * (τ * B ^ 3) :=
            mul_le_mul_of_nonneg_left hB4 (by positivity)
    have h2 : 64 * K * Cd1 * (k : ℝ) * B ^ 4 ≤ 64 * K * Cd1 * (k : ℝ) * (τ * B ^ 3) := by
      calc 64 * K * Cd1 * (k : ℝ) * B ^ 4 = (64 * K * Cd1 * (k : ℝ)) * B ^ 4 := by ring
        _ ≤ (64 * K * Cd1 * (k : ℝ)) * (τ * B ^ 3) :=
            mul_le_mul_of_nonneg_left hB4 (by positivity)
    have h3 : 32 * K * τ * B ^ 3 = 32 * K * (τ * B ^ 3) := by ring
    have hsum : 32 * Cd2 * (k : ℝ) ^ 2 * B ^ 4 + 64 * K * Cd1 * (k : ℝ) * B ^ 4
          + 32 * K * τ * B ^ 3
        ≤ (32 * Cd2 * (k : ℝ) ^ 2 * (τ * B ^ 3) + 64 * K * Cd1 * (k : ℝ) * (τ * B ^ 3))
          + 32 * K * (τ * B ^ 3) := by linarith [h1, h2, h3]
    calc 32 * Cd2 * (k : ℝ) ^ 2 * B ^ 4 + 64 * K * Cd1 * (k : ℝ) * B ^ 4
          + 32 * K * τ * B ^ 3
        = (32 * Cd2 * (k : ℝ) ^ 2 * B ^ 4 + 64 * K * Cd1 * (k : ℝ) * B ^ 4)
          + 32 * K * τ * B ^ 3 := by ring
      _ ≤ (32 * Cd2 * (k : ℝ) ^ 2 * (τ * B ^ 3) + 64 * K * Cd1 * (k : ℝ) * (τ * B ^ 3))
            + 32 * K * (τ * B ^ 3) := hsum
      _ = (32 * Cd2 * (k : ℝ) ^ 2 + 64 * K * Cd1 * (k : ℝ) + 32 * K) * (τ * B ^ 3) := by ring
  have hX1nn : (0 : ℝ) ≤ 32 * Cd2 * (k : ℝ) ^ 2 * B ^ 4 + 64 * K * Cd1 * (k : ℝ) * B ^ 4
      + 32 * K * τ * B ^ 3 := by
    have h1 : (0 : ℝ) ≤ 32 * Cd2 * (k : ℝ) ^ 2 * B ^ 4 := by positivity
    have h2 : (0 : ℝ) ≤ 64 * K * Cd1 * (k : ℝ) * B ^ 4 := by positivity
    have h3 : (0 : ℝ) ≤ 32 * K * τ * B ^ 3 := by positivity
    linarith
  have hfinal : (2 * Real.pi)⁻¹ * (2 * Real.pi)⁻¹
        * (32 * Cd2 * (k : ℝ) ^ 2 * B ^ 4 + 64 * K * Cd1 * (k : ℝ) * B ^ 4
          + 32 * K * τ * B ^ 3)
      ≤ (1 / 36 : ℝ) * (32 * Cd2 * (k : ℝ) ^ 2 + 64 * K * Cd1 * (k : ℝ) + 32 * K)
        * τ * ε ^ (3 / 2 : ℝ) := by
    have hcoef : (2 * Real.pi)⁻¹ * (2 * Real.pi)⁻¹ ≤ 1 / 36 := inv_two_pi_sq_le
    calc ((2 * Real.pi)⁻¹ * (2 * Real.pi)⁻¹)
          * (32 * Cd2 * (k : ℝ) ^ 2 * B ^ 4 + 64 * K * Cd1 * (k : ℝ) * B ^ 4
            + 32 * K * τ * B ^ 3)
        ≤ (1 / 36) * (32 * Cd2 * (k : ℝ) ^ 2 * B ^ 4 + 64 * K * Cd1 * (k : ℝ) * B ^ 4
            + 32 * K * τ * B ^ 3) := mul_le_mul_of_nonneg_right hcoef hX1nn
      _ ≤ (1 / 36) * ((32 * Cd2 * (k : ℝ) ^ 2 + 64 * K * Cd1 * (k : ℝ) + 32 * K)
            * (τ * B ^ 3)) := mul_le_mul_of_nonneg_left hkey (by norm_num)
      _ = (1 / 36 : ℝ) * (32 * Cd2 * (k : ℝ) ^ 2 + 64 * K * Cd1 * (k : ℝ) + 32 * K)
            * τ * ε ^ (3 / 2 : ℝ) := by
          rw [hB3]
          ring
  simpa only [sqrtC] using hfinal

/-! ### §2.2 替代形状：连 `hBk` 都不要（常数含 `k³`） -/

/-- **`B = √ε` 的「无条件」形状**：侧条件只有 `B ≤ τ`（**不需要任何 `k` 与 `B` 的关系**），
代价是常数多出三个 `k`-高次项：

```
Csharp_gen = (1/36)·(16·Cd2·k² + 48·K·Cd1·k + 16·K + 16·Cd1·Cd2·k³ + 32·K·Cd1²·k²).
```

`ε^{3/2}` 的形状不变；拉平只用 `B⁴ ≤ τB³` 与 `B⁵/τ ≤ τB³`（后者由 `B² ≤ τ²`）。 -/
lemma kernelProd_le_poly_sqrt_general {τ B ε M₁ M₂ K Cd1 Cd2 : ℝ} {k : ℕ} (P : Polynomial ℂ)
    (hτ : 0 < τ) (hB : 0 < B) (hε : 0 ≤ ε) (hK : 0 ≤ K)
    (hCd1 : 0 ≤ Cd1) (hCd2 : 0 ≤ Cd2)
    (hM₁nn : 0 ≤ M₁) (hM₂nn : 0 ≤ M₂)
    (hBτ : B ≤ τ)
    (hBval : B = Real.sqrt ε)
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
      ≤ (1 / 36 : ℝ) * (16 * Cd2 * (k : ℝ) ^ 2 + 48 * K * Cd1 * (k : ℝ) + 16 * K
          + 16 * Cd1 * Cd2 * (k : ℝ) ^ 3 + 32 * K * Cd1 ^ 2 * (k : ℝ) ^ 2)
        * τ * ε ^ (3 / 2 : ℝ) := by
  have hBB : B * B = ε := by
    rw [hBval]
    simpa [pow_two] using Real.sq_sqrt hε
  have hB3 : B ^ 3 = ε ^ (3 / 2 : ℝ) := by
    rw [rpow_three_halves_eq_sqrt_cube hε, ← hBval]
  have hM1le : M₁ ≤ Cd1 * (k : ℝ) * ε / τ := by
    rw [le_div_iff₀ hτ]
    calc M₁ * τ = τ * M₁ := by ring
      _ ≤ Cd1 * (k : ℝ) * ε := hM1sharp
  have hBM1 : B * M₁ ≤ Cd1 * (k : ℝ) * B ^ 3 / τ := by
    have h1 : B * M₁ ≤ B * (Cd1 * (k : ℝ) * ε / τ) := mul_le_mul_of_nonneg_left hM1le hB.le
    have h2 : B * (Cd1 * (k : ℝ) * ε / τ) = Cd1 * (k : ℝ) * B ^ 3 / τ := by
      rw [← hBB]
      ring
    linarith [h1, h2]
  have hSnn : 0 ≤ ε + B * M₁ := by
    have h := mul_nonneg hB.le hM₁nn
    linarith [hε]
  have hC1 : kernelA τ B P ≤ (2 * Real.pi)⁻¹ * (4 * τ * ε + 4 * Cd1 * (k : ℝ) * B ^ 3) := by
    refine (kernelA_le_support hτ hB P hψ).trans ?_
    have hcoef : (0 : ℝ) < (2 * Real.pi)⁻¹ := by positivity
    have h1 : 2 * (τ + B) ≤ 4 * τ := by linarith
    have h3 : 2 * (τ + B) * (ε + B * M₁) ≤ 4 * τ * (ε + B * M₁) :=
      mul_le_mul_of_nonneg_right h1 hSnn
    have h4 : 4 * τ * (ε + B * M₁) = 4 * τ * ε + 4 * τ * (B * M₁) := by ring
    have h5 : 4 * τ * (B * M₁) ≤ 4 * τ * (Cd1 * (k : ℝ) * B ^ 3 / τ) :=
      mul_le_mul_of_nonneg_left hBM1 (by linarith)
    have h6 : 4 * τ * (Cd1 * (k : ℝ) * B ^ 3 / τ) = 4 * Cd1 * (k : ℝ) * B ^ 3 := by
      field_simp
      try ring
    have h7 : 2 * (τ + B) * (ε + B * M₁) ≤ 4 * τ * ε + 4 * Cd1 * (k : ℝ) * B ^ 3 := by
      linarith [h3, h4, h5, h6]
    calc (2 * Real.pi)⁻¹ * (2 * (τ + B)) * (ε + B * M₁)
        = (2 * Real.pi)⁻¹ * (2 * (τ + B) * (ε + B * M₁)) := by ring
      _ ≤ (2 * Real.pi)⁻¹ * (4 * τ * ε + 4 * Cd1 * (k : ℝ) * B ^ 3) :=
          mul_le_mul_of_nonneg_left h7 hcoef.le
  have hC2 := kernelC_le_sqrt_aux P hτ hB hε hK hCd1 hCd2 hM₂nn hBτ hBval hM1sharp hM2sharp
    hPε hA1 hA2 hK1 hK2
  have hC2nn : 0 ≤ kernelC τ B P := kernelC_nonneg hτ hB P
  have hC1rhs : 0 ≤ (2 * Real.pi)⁻¹ * (4 * τ * ε + 4 * Cd1 * (k : ℝ) * B ^ 3) :=
    mul_nonneg (by positivity)
      (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hτ.le) hε)
        (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCd1) (Nat.cast_nonneg k))
          (pow_nonneg hB.le 3)))
  have hprod : kernelA τ B P * kernelC τ B P
      ≤ (2 * Real.pi)⁻¹ * (4 * τ * ε + 4 * Cd1 * (k : ℝ) * B ^ 3)
        * ((2 * Real.pi)⁻¹ *
          (4 * Cd2 * (k : ℝ) ^ 2 * ε / τ + 8 * K * Cd1 * (k : ℝ) * ε / τ + 4 * K * B)) :=
    mul_le_mul hC1 hC2 hC2nn hC1rhs
  refine hprod.trans ?_
  have hstep1 : (2 * Real.pi)⁻¹ * (4 * τ * ε + 4 * Cd1 * (k : ℝ) * B ^ 3)
        * ((2 * Real.pi)⁻¹ *
          (4 * Cd2 * (k : ℝ) ^ 2 * ε / τ + 8 * K * Cd1 * (k : ℝ) * ε / τ + 4 * K * B))
      = (2 * Real.pi)⁻¹ * (2 * Real.pi)⁻¹
        * ((4 * τ * ε + 4 * Cd1 * (k : ℝ) * B ^ 3)
          * (4 * Cd2 * (k : ℝ) ^ 2 * ε / τ + 8 * K * Cd1 * (k : ℝ) * ε / τ + 4 * K * B)) := by
    ring
  rw [hstep1]
  have hstep2 : (4 * τ * ε + 4 * Cd1 * (k : ℝ) * B ^ 3)
        * (4 * Cd2 * (k : ℝ) ^ 2 * ε / τ + 8 * K * Cd1 * (k : ℝ) * ε / τ + 4 * K * B)
      = 16 * Cd2 * (k : ℝ) ^ 2 * B ^ 4 + 32 * K * Cd1 * (k : ℝ) * B ^ 4
        + 16 * K * τ * B ^ 3 + 16 * Cd1 * Cd2 * (k : ℝ) ^ 3 * B ^ 5 / τ
        + 32 * K * Cd1 ^ 2 * (k : ℝ) ^ 2 * B ^ 5 / τ + 16 * K * Cd1 * (k : ℝ) * B ^ 4 := by
    rw [← hBB]
    field_simp
    try ring
  rw [hstep2]
  have hkey : 16 * Cd2 * (k : ℝ) ^ 2 * B ^ 4 + 32 * K * Cd1 * (k : ℝ) * B ^ 4
        + 16 * K * τ * B ^ 3 + 16 * Cd1 * Cd2 * (k : ℝ) ^ 3 * B ^ 5 / τ
        + 32 * K * Cd1 ^ 2 * (k : ℝ) ^ 2 * B ^ 5 / τ + 16 * K * Cd1 * (k : ℝ) * B ^ 4
      ≤ (16 * Cd2 * (k : ℝ) ^ 2 + 48 * K * Cd1 * (k : ℝ) + 16 * K
          + 16 * Cd1 * Cd2 * (k : ℝ) ^ 3 + 32 * K * Cd1 ^ 2 * (k : ℝ) ^ 2)
        * (τ * B ^ 3) := by
    have hB3nn : (0 : ℝ) ≤ B ^ 3 := pow_nonneg hB.le 3
    have hB4 : B ^ 4 ≤ τ * B ^ 3 := by
      have h := mul_le_mul_of_nonneg_right hBτ hB3nn
      calc B ^ 4 = B * B ^ 3 := by ring
        _ ≤ τ * B ^ 3 := h
    have hB2 : B ^ 2 ≤ τ ^ 2 := by nlinarith [hBτ, hB.le, hτ]
    have hB5 : B ^ 5 / τ ≤ τ * B ^ 3 := by
      rw [div_le_iff₀ hτ]
      calc B ^ 5 = B ^ 2 * B ^ 3 := by ring
        _ ≤ τ ^ 2 * B ^ 3 := mul_le_mul_of_nonneg_right hB2 hB3nn
        _ = (τ * B ^ 3) * τ := by ring
    have h1 : 16 * Cd2 * (k : ℝ) ^ 2 * B ^ 4 ≤ 16 * Cd2 * (k : ℝ) ^ 2 * (τ * B ^ 3) := by
      calc 16 * Cd2 * (k : ℝ) ^ 2 * B ^ 4 = (16 * Cd2 * (k : ℝ) ^ 2) * B ^ 4 := by ring
        _ ≤ (16 * Cd2 * (k : ℝ) ^ 2) * (τ * B ^ 3) :=
            mul_le_mul_of_nonneg_left hB4 (by positivity)
    have h2 : 32 * K * Cd1 * (k : ℝ) * B ^ 4 ≤ 32 * K * Cd1 * (k : ℝ) * (τ * B ^ 3) := by
      calc 32 * K * Cd1 * (k : ℝ) * B ^ 4 = (32 * K * Cd1 * (k : ℝ)) * B ^ 4 := by ring
        _ ≤ (32 * K * Cd1 * (k : ℝ)) * (τ * B ^ 3) :=
            mul_le_mul_of_nonneg_left hB4 (by positivity)
    have h3 : 16 * K * Cd1 * (k : ℝ) * B ^ 4 ≤ 16 * K * Cd1 * (k : ℝ) * (τ * B ^ 3) := by
      calc 16 * K * Cd1 * (k : ℝ) * B ^ 4 = (16 * K * Cd1 * (k : ℝ)) * B ^ 4 := by ring
        _ ≤ (16 * K * Cd1 * (k : ℝ)) * (τ * B ^ 3) :=
            mul_le_mul_of_nonneg_left hB4 (by positivity)
    have h4 : 16 * Cd1 * Cd2 * (k : ℝ) ^ 3 * B ^ 5 / τ
        ≤ 16 * Cd1 * Cd2 * (k : ℝ) ^ 3 * (τ * B ^ 3) := by
      calc 16 * Cd1 * Cd2 * (k : ℝ) ^ 3 * B ^ 5 / τ
          = (16 * Cd1 * Cd2 * (k : ℝ) ^ 3) * (B ^ 5 / τ) := by ring
        _ ≤ (16 * Cd1 * Cd2 * (k : ℝ) ^ 3) * (τ * B ^ 3) :=
            mul_le_mul_of_nonneg_left hB5 (by positivity)
    have h5 : 32 * K * Cd1 ^ 2 * (k : ℝ) ^ 2 * B ^ 5 / τ
        ≤ 32 * K * Cd1 ^ 2 * (k : ℝ) ^ 2 * (τ * B ^ 3) := by
      calc 32 * K * Cd1 ^ 2 * (k : ℝ) ^ 2 * B ^ 5 / τ
          = (32 * K * Cd1 ^ 2 * (k : ℝ) ^ 2) * (B ^ 5 / τ) := by ring
        _ ≤ (32 * K * Cd1 ^ 2 * (k : ℝ) ^ 2) * (τ * B ^ 3) :=
            mul_le_mul_of_nonneg_left hB5 (by positivity)
    have h6 : 16 * K * τ * B ^ 3 = 16 * K * (τ * B ^ 3) := by ring
    have hsum : 16 * Cd2 * (k : ℝ) ^ 2 * B ^ 4 + 32 * K * Cd1 * (k : ℝ) * B ^ 4
          + 16 * K * τ * B ^ 3 + 16 * Cd1 * Cd2 * (k : ℝ) ^ 3 * B ^ 5 / τ
          + 32 * K * Cd1 ^ 2 * (k : ℝ) ^ 2 * B ^ 5 / τ + 16 * K * Cd1 * (k : ℝ) * B ^ 4
        ≤ ((((16 * Cd2 * (k : ℝ) ^ 2 * (τ * B ^ 3) + 32 * K * Cd1 * (k : ℝ) * (τ * B ^ 3))
            + 16 * K * (τ * B ^ 3)) + 16 * Cd1 * Cd2 * (k : ℝ) ^ 3 * (τ * B ^ 3))
            + 32 * K * Cd1 ^ 2 * (k : ℝ) ^ 2 * (τ * B ^ 3))
          + 16 * K * Cd1 * (k : ℝ) * (τ * B ^ 3) := by linarith [h1, h2, h3, h4, h5, h6]
    refine hsum.trans (le_of_eq ?_)
    ring
  have hX1nn : (0 : ℝ) ≤ 16 * Cd2 * (k : ℝ) ^ 2 * B ^ 4 + 32 * K * Cd1 * (k : ℝ) * B ^ 4
      + 16 * K * τ * B ^ 3 + 16 * Cd1 * Cd2 * (k : ℝ) ^ 3 * B ^ 5 / τ
      + 32 * K * Cd1 ^ 2 * (k : ℝ) ^ 2 * B ^ 5 / τ + 16 * K * Cd1 * (k : ℝ) * B ^ 4 := by
    have h1 : (0 : ℝ) ≤ 16 * Cd2 * (k : ℝ) ^ 2 * B ^ 4 := by positivity
    have h2 : (0 : ℝ) ≤ 32 * K * Cd1 * (k : ℝ) * B ^ 4 := by positivity
    have h3 : (0 : ℝ) ≤ 16 * K * τ * B ^ 3 := by positivity
    have h4 : (0 : ℝ) ≤ 16 * Cd1 * Cd2 * (k : ℝ) ^ 3 * B ^ 5 / τ := by positivity
    have h5 : (0 : ℝ) ≤ 32 * K * Cd1 ^ 2 * (k : ℝ) ^ 2 * B ^ 5 / τ := by positivity
    have h6 : (0 : ℝ) ≤ 16 * K * Cd1 * (k : ℝ) * B ^ 4 := by positivity
    linarith
  have hcoef : (2 * Real.pi)⁻¹ * (2 * Real.pi)⁻¹ ≤ 1 / 36 := inv_two_pi_sq_le
  calc (2 * Real.pi)⁻¹ * (2 * Real.pi)⁻¹
        * (16 * Cd2 * (k : ℝ) ^ 2 * B ^ 4 + 32 * K * Cd1 * (k : ℝ) * B ^ 4
          + 16 * K * τ * B ^ 3 + 16 * Cd1 * Cd2 * (k : ℝ) ^ 3 * B ^ 5 / τ
          + 32 * K * Cd1 ^ 2 * (k : ℝ) ^ 2 * B ^ 5 / τ
          + 16 * K * Cd1 * (k : ℝ) * B ^ 4)
      ≤ (1 / 36) * (16 * Cd2 * (k : ℝ) ^ 2 * B ^ 4 + 32 * K * Cd1 * (k : ℝ) * B ^ 4
          + 16 * K * τ * B ^ 3 + 16 * Cd1 * Cd2 * (k : ℝ) ^ 3 * B ^ 5 / τ
          + 32 * K * Cd1 ^ 2 * (k : ℝ) ^ 2 * B ^ 5 / τ
          + 16 * K * Cd1 * (k : ℝ) * B ^ 4) :=
        mul_le_mul_of_nonneg_right hcoef hX1nn
    _ ≤ (1 / 36) * ((16 * Cd2 * (k : ℝ) ^ 2 + 48 * K * Cd1 * (k : ℝ) + 16 * K
          + 16 * Cd1 * Cd2 * (k : ℝ) ^ 3 + 32 * K * Cd1 ^ 2 * (k : ℝ) ^ 2)
          * (τ * B ^ 3)) :=
        mul_le_mul_of_nonneg_left hkey (by norm_num)
    _ = (1 / 36 : ℝ) * (16 * Cd2 * (k : ℝ) ^ 2 + 48 * K * Cd1 * (k : ℝ) + 16 * K
          + 16 * Cd1 * Cd2 * (k : ℝ) ^ 3 + 32 * K * Cd1 ^ 2 * (k : ℝ) ^ 2)
        * τ * ε ^ (3 / 2 : ℝ) := by
        rw [hB3]
        ring

/-! ## §3 数值实例（`K = 1`） -/

/-- **`(Cd1, Cd2, K) = (32, 512, 1)`**：
`sqrtC0 = (1/36)·33·(16·512 + 32·32 + 16) = 304656/36 = 8462.66…`，取 `8463`。 -/
lemma kernelProd_le_poly_sqrt_inst_32_512 {τ B ε M₁ M₂ : ℝ} {k : ℕ} (P : Polynomial ℂ)
    (hτ : 0 < τ) (hB : 0 < B) (hε : 0 ≤ ε)
    (hM₁nn : 0 ≤ M₁) (hM₂nn : 0 ≤ M₂)
    (hBτ : B ≤ τ) (hkB : (k : ℝ) * B ≤ τ) (hk2B : (k : ℝ) ^ 2 * B ≤ τ)
    (hBval : B = Real.sqrt ε)
    (hM1sharp : τ * M₁ ≤ 32 * (k : ℝ) * ε)
    (hM2sharp : τ ^ 2 * M₂ ≤ 512 * (k : ℝ) ^ 2 * ε)
    (hψ : ∀ μ : ℝ, ‖psi τ B P μ‖ ≤ ε + B * M₁)
    (hPε : ∀ μ : ℝ, |μ| ≤ τ →
      ‖Complex.exp (-(μ : ℂ) * Complex.I) - P.eval ((μ : ℂ))‖ ≤ ε)
    (hA1 : ∀ μ : ℝ, |μ| ≤ τ + B → ‖deriv (fun x : ℝ => psiA P x) μ‖ ≤ M₁)
    (hA2 : ∀ μ : ℝ, |μ| ≤ τ + B → ‖deriv (deriv (fun x : ℝ => psiA P x)) μ‖ ≤ M₂)
    (hK1 : ∀ μ : ℝ, ‖deriv (fun x : ℝ => ((cutoff τ B x : ℝ) : ℂ)) μ‖ ≤ 1 / B)
    (hK2 : ∀ μ : ℝ, ‖deriv (deriv (fun x : ℝ => ((cutoff τ B x : ℝ) : ℂ))) μ‖ ≤ 1 / B ^ 2) :
    kernelA τ B P * kernelC τ B P ≤ 8463 * τ * ε ^ (3 / 2 : ℝ) := by
  have hmain := kernelProd_le_poly_sqrt (Cd1 := 32) (Cd2 := 512) (K := 1) P hτ hB hε
    (by norm_num) (by norm_num) (by norm_num) hM₁nn hM₂nn hBτ hkB hk2B hBval
    hM1sharp hM2sharp hψ hPε hA1 hA2 hK1 hK2
  refine hmain.trans ?_
  have h0 : (0 : ℝ) ≤ τ * ε ^ (3 / 2 : ℝ) :=
    mul_nonneg hτ.le (Real.rpow_nonneg hε _)
  have hc : sqrtC0 32 512 1 ≤ 8463 := by
    rw [sqrtC0_def]
    norm_num
  calc sqrtC0 32 512 1 * τ * ε ^ (3 / 2 : ℝ)
      = sqrtC0 32 512 1 * (τ * ε ^ (3 / 2 : ℝ)) := by ring
    _ ≤ 8463 * (τ * ε ^ (3 / 2 : ℝ)) := mul_le_mul_of_nonneg_right hc h0
    _ = 8463 * τ * ε ^ (3 / 2 : ℝ) := by ring

/-- **`(Cd1, Cd2, K) = (4, 16, 1)`**：
`sqrtC0 = (1/36)·5·(16·16 + 32·4 + 16) = 2000/36 = 55.55…`，取 `56`。 -/
lemma kernelProd_le_poly_sqrt_inst_4_16 {τ B ε M₁ M₂ : ℝ} {k : ℕ} (P : Polynomial ℂ)
    (hτ : 0 < τ) (hB : 0 < B) (hε : 0 ≤ ε)
    (hM₁nn : 0 ≤ M₁) (hM₂nn : 0 ≤ M₂)
    (hBτ : B ≤ τ) (hkB : (k : ℝ) * B ≤ τ) (hk2B : (k : ℝ) ^ 2 * B ≤ τ)
    (hBval : B = Real.sqrt ε)
    (hM1sharp : τ * M₁ ≤ 4 * (k : ℝ) * ε)
    (hM2sharp : τ ^ 2 * M₂ ≤ 16 * (k : ℝ) ^ 2 * ε)
    (hψ : ∀ μ : ℝ, ‖psi τ B P μ‖ ≤ ε + B * M₁)
    (hPε : ∀ μ : ℝ, |μ| ≤ τ →
      ‖Complex.exp (-(μ : ℂ) * Complex.I) - P.eval ((μ : ℂ))‖ ≤ ε)
    (hA1 : ∀ μ : ℝ, |μ| ≤ τ + B → ‖deriv (fun x : ℝ => psiA P x) μ‖ ≤ M₁)
    (hA2 : ∀ μ : ℝ, |μ| ≤ τ + B → ‖deriv (deriv (fun x : ℝ => psiA P x)) μ‖ ≤ M₂)
    (hK1 : ∀ μ : ℝ, ‖deriv (fun x : ℝ => ((cutoff τ B x : ℝ) : ℂ)) μ‖ ≤ 1 / B)
    (hK2 : ∀ μ : ℝ, ‖deriv (deriv (fun x : ℝ => ((cutoff τ B x : ℝ) : ℂ))) μ‖ ≤ 1 / B ^ 2) :
    kernelA τ B P * kernelC τ B P ≤ 56 * τ * ε ^ (3 / 2 : ℝ) := by
  have hmain := kernelProd_le_poly_sqrt (Cd1 := 4) (Cd2 := 16) (K := 1) P hτ hB hε
    (by norm_num) (by norm_num) (by norm_num) hM₁nn hM₂nn hBτ hkB hk2B hBval
    hM1sharp hM2sharp hψ hPε hA1 hA2 hK1 hK2
  refine hmain.trans ?_
  have h0 : (0 : ℝ) ≤ τ * ε ^ (3 / 2 : ℝ) :=
    mul_nonneg hτ.le (Real.rpow_nonneg hε _)
  have hc : sqrtC0 4 16 1 ≤ 56 := by
    rw [sqrtC0_def]
    norm_num
  calc sqrtC0 4 16 1 * τ * ε ^ (3 / 2 : ℝ)
      = sqrtC0 4 16 1 * (τ * ε ^ (3 / 2 : ℝ)) := by ring
    _ ≤ 56 * (τ * ε ^ (3 / 2 : ℝ)) := mul_le_mul_of_nonneg_right hc h0
    _ = 56 * τ * ε ^ (3 / 2 : ℝ) := by ring

/-! ## §4 判据 -/

/-- **判据（`(1/8)²` 形）**：`ε^{3/2} < (1/8)²/(Csharp·τ)` ⟹ `C₁C₂ < (1/8)²`。

（`hC : 0 < sqrtC0 Cd1 Cd2 K` 在 `K > 0`，或 `Cd2 > 0` 时自动成立；
见 `sqrtC0_pos_of_K_pos`、`sqrtC0_pos_of_Cd2_pos`。） -/
lemma kernelProd_sqrt_lt {τ B ε M₁ M₂ K Cd1 Cd2 : ℝ} {k : ℕ} (P : Polynomial ℂ)
    (hτ : 0 < τ) (hB : 0 < B) (hε : 0 ≤ ε) (hK : 0 ≤ K)
    (hCd1 : 0 ≤ Cd1) (hCd2 : 0 ≤ Cd2)
    (hM₁nn : 0 ≤ M₁) (hM₂nn : 0 ≤ M₂)
    (hBτ : B ≤ τ) (hkB : (k : ℝ) * B ≤ τ) (hk2B : (k : ℝ) ^ 2 * B ≤ τ)
    (hBval : B = Real.sqrt ε)
    (hM1sharp : τ * M₁ ≤ Cd1 * (k : ℝ) * ε)
    (hM2sharp : τ ^ 2 * M₂ ≤ Cd2 * (k : ℝ) ^ 2 * ε)
    (hψ : ∀ μ : ℝ, ‖psi τ B P μ‖ ≤ ε + B * M₁)
    (hPε : ∀ μ : ℝ, |μ| ≤ τ →
      ‖Complex.exp (-(μ : ℂ) * Complex.I) - P.eval ((μ : ℂ))‖ ≤ ε)
    (hA1 : ∀ μ : ℝ, |μ| ≤ τ + B → ‖deriv (fun x : ℝ => psiA P x) μ‖ ≤ M₁)
    (hA2 : ∀ μ : ℝ, |μ| ≤ τ + B → ‖deriv (deriv (fun x : ℝ => psiA P x)) μ‖ ≤ M₂)
    (hK1 : ∀ μ : ℝ, ‖deriv (fun x : ℝ => ((cutoff τ B x : ℝ) : ℂ)) μ‖ ≤ K / B)
    (hK2 : ∀ μ : ℝ, ‖deriv (deriv (fun x : ℝ => ((cutoff τ B x : ℝ) : ℂ))) μ‖ ≤ K / B ^ 2)
    (hC : 0 < sqrtC0 Cd1 Cd2 K)
    (hsmall : ε ^ (3 / 2 : ℝ) < (1 / 8) ^ 2 / (sqrtC0 Cd1 Cd2 K * τ)) :
    kernelA τ B P * kernelC τ B P < (1 / 8 : ℝ) ^ 2 := by
  have hmain := kernelProd_le_poly_sqrt P hτ hB hε hK hCd1 hCd2 hM₁nn hM₂nn hBτ hkB hk2B
    hBval hM1sharp hM2sharp hψ hPε hA1 hA2 hK1 hK2
  have hden : 0 < sqrtC0 Cd1 Cd2 K * τ := mul_pos hC hτ
  have h1 : ε ^ (3 / 2 : ℝ) * (sqrtC0 Cd1 Cd2 K * τ) < (1 / 8 : ℝ) ^ 2 :=
    (lt_div_iff₀ hden).mp hsmall
  have h2 : sqrtC0 Cd1 Cd2 K * τ * ε ^ (3 / 2 : ℝ) < (1 / 8 : ℝ) ^ 2 := by
    rw [show sqrtC0 Cd1 Cd2 K * τ * ε ^ (3 / 2 : ℝ)
        = ε ^ (3 / 2 : ℝ) * (sqrtC0 Cd1 Cd2 K * τ) by ring]
    exact h1
  exact lt_of_le_of_lt hmain h2

/-- **判据（`(δ/8)²` 形，接 `FinalSmall.h_zero_lt_of_kernel_decay` 的阈值）**：
取 `δ = 1 - Real.cos (φ/2)`，则 `ε^{3/2} < δ²/(64·Csharp·τ)` ⟹ `C₁C₂ < (δ/8)²`，
即 `8·√(C₁C₂) < δ`。 -/
lemma kernelProd_sqrt_criterion {τ B ε M₁ M₂ K Cd1 Cd2 δ : ℝ} {k : ℕ} (P : Polynomial ℂ)
    (hτ : 0 < τ) (hB : 0 < B) (hε : 0 ≤ ε) (hK : 0 ≤ K)
    (hCd1 : 0 ≤ Cd1) (hCd2 : 0 ≤ Cd2)
    (hM₁nn : 0 ≤ M₁) (hM₂nn : 0 ≤ M₂)
    (hBτ : B ≤ τ) (hkB : (k : ℝ) * B ≤ τ) (hk2B : (k : ℝ) ^ 2 * B ≤ τ)
    (hBval : B = Real.sqrt ε)
    (hM1sharp : τ * M₁ ≤ Cd1 * (k : ℝ) * ε)
    (hM2sharp : τ ^ 2 * M₂ ≤ Cd2 * (k : ℝ) ^ 2 * ε)
    (hψ : ∀ μ : ℝ, ‖psi τ B P μ‖ ≤ ε + B * M₁)
    (hPε : ∀ μ : ℝ, |μ| ≤ τ →
      ‖Complex.exp (-(μ : ℂ) * Complex.I) - P.eval ((μ : ℂ))‖ ≤ ε)
    (hA1 : ∀ μ : ℝ, |μ| ≤ τ + B → ‖deriv (fun x : ℝ => psiA P x) μ‖ ≤ M₁)
    (hA2 : ∀ μ : ℝ, |μ| ≤ τ + B → ‖deriv (deriv (fun x : ℝ => psiA P x)) μ‖ ≤ M₂)
    (hK1 : ∀ μ : ℝ, ‖deriv (fun x : ℝ => ((cutoff τ B x : ℝ) : ℂ)) μ‖ ≤ K / B)
    (hK2 : ∀ μ : ℝ, ‖deriv (deriv (fun x : ℝ => ((cutoff τ B x : ℝ) : ℂ))) μ‖ ≤ K / B ^ 2)
    (hC : 0 < sqrtC0 Cd1 Cd2 K)
    (hεsmall : ε ^ (3 / 2 : ℝ) < δ ^ 2 / (64 * sqrtC0 Cd1 Cd2 K * τ)) :
    kernelA τ B P * kernelC τ B P < (δ / 8) ^ 2 := by
  have hmain := kernelProd_le_poly_sqrt P hτ hB hε hK hCd1 hCd2 hM₁nn hM₂nn hBτ hkB hk2B
    hBval hM1sharp hM2sharp hψ hPε hA1 hA2 hK1 hK2
  have hden : 0 < 64 * sqrtC0 Cd1 Cd2 K * τ := by
    have h1 : (0 : ℝ) < 64 * sqrtC0 Cd1 Cd2 K := mul_pos (by norm_num) hC
    exact mul_pos h1 hτ
  have h1 : ε ^ (3 / 2 : ℝ) * (64 * sqrtC0 Cd1 Cd2 K * τ) < δ ^ 2 :=
    (lt_div_iff₀ hden).mp hεsmall
  have h2 : sqrtC0 Cd1 Cd2 K * τ * ε ^ (3 / 2 : ℝ) < δ ^ 2 / 64 := by linarith
  have h3 : (δ / 8) ^ 2 = δ ^ 2 / 64 := by ring
  exact lt_of_le_of_lt hmain (by rw [h3]; exact h2)

/-! ## §5 常数自检 -/

/-- 两个数值实例的算术自检。 -/
lemma sqrtC0_inst_check :
    sqrtC0 32 512 1 ≤ 8463 ∧ sqrtC0 4 16 1 ≤ 56 := by
  rw [sqrtC0_def, sqrtC0_def]
  norm_num

/-- `K > 0` 时 `sqrtC0 > 0`（`hC` 的充分条件）。 -/
lemma sqrtC0_pos_of_K_pos {Cd1 Cd2 K : ℝ} (hCd1 : 0 ≤ Cd1) (hCd2 : 0 ≤ Cd2) (hK : 0 < K) :
    0 < sqrtC0 Cd1 Cd2 K := by
  rw [sqrtC0_def]
  have h1 : (0 : ℝ) < 1 + Cd1 := by linarith
  have h2 : (0 : ℝ) < 16 * Cd2 + 32 * Cd1 * K + 16 * K := by
    have ha : (0 : ℝ) ≤ 16 * Cd2 := by linarith
    have hb : (0 : ℝ) ≤ 32 * Cd1 * K := by positivity
    have hc : (0 : ℝ) < 16 * K := by linarith
    linarith
  exact mul_pos (mul_pos (by norm_num) h1) h2

/-- `Cd2 > 0` 时 `sqrtC0 > 0`（`hC` 的另一充分条件）。 -/
lemma sqrtC0_pos_of_Cd2_pos {Cd1 Cd2 K : ℝ} (hCd1 : 0 ≤ Cd1) (hCd2 : 0 < Cd2) (hK : 0 ≤ K) :
    0 < sqrtC0 Cd1 Cd2 K := by
  rw [sqrtC0_def]
  have h1 : (0 : ℝ) < 1 + Cd1 := by linarith
  have h2 : (0 : ℝ) < 16 * Cd2 + 32 * Cd1 * K + 16 * K := by
    have ha : (0 : ℝ) < 16 * Cd2 := by linarith
    have hb : (0 : ℝ) ≤ 32 * Cd1 * K := by positivity
    have hc : (0 : ℝ) ≤ 16 * K := by linarith
    linarith
  exact mul_pos (mul_pos (by norm_num) h1) h2

end RobustZ
