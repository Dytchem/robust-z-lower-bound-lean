import RobustZ.Inversion
import RobustZ.L1Bound
import RobustZ.KernelIntegrable

/-!
# M3：smearing 引理的主组装

主结论（`B = √ε`）

`‖∑ᵢ cᵢ‖ ≤ 8 · √(C₁ · C₂)`，其中
`C₁ = (2π)⁻¹ ∫_{-A}^{A} ‖Ψ‖`、`C₂ = (2π)⁻¹ ∫_{-A}^{A} ‖Ψ''‖`、`A = τ + √ε + 1`。

证明路线：

1. `sum_c_eq_sum_c_psi`（矩条件 + 带内 `Ψ = 1 − Pe^{iμ}`）把 `∑ᵢcᵢ` 换成 `∑ᵢcᵢΨ(νᵢ)`；
2. `sum_mul_psi_eq_integral`（`integral_exp_mul_kernel`，逐项）把它写成
   `∫ (∑ᵢ cᵢe^{iνᵢt})·κ(t) dt`；
3. `norm_integral_le_two_mul`（指数和的一致界 `≤ 2`）给出 `≤ 2∫‖κ‖`；
4. `integral_norm_le_sqrt`（`norm_kernel_le` + `norm_kernel_le_deriv`）给出 `≤ 4√(C₁C₂)`。

合计即 `8√(C₁C₂)`。

注：`hbdd`（指数和的一致界）必须作用在**同一组频率** `ν` 上、形如
`‖∑ᵢ e^{i(νᵢλ)}cᵢ‖ ≤ 2`——这是第 3 步逐点界的来源。
-/

noncomputable section

namespace RobustZ

open scoped Real
open Filter MeasureTheory

/-- **第 1 步（表示）**：`∑ᵢ cᵢΨ(νᵢ) = ∫ (∑ᵢ cᵢe^{iνᵢt})κ(t)dt`。

逐项用反演恒等式 `integral_exp_mul_kernel`：`∫ e^{iνᵢt}κ(t)dt = Ψ(νᵢ)`。 -/
lemma sum_mul_psi_eq_integral {ι : Type} [Fintype ι] (c : ι → ℂ) (ν : ι → ℝ)
    {τ B : ℝ} (hτ : 0 < τ) (hB : 0 < B) (P : Polynomial ℂ)
    (hint : Integrable (fun t : ℝ => kernel τ B P t)) :
    ∑ i, c i * psi τ B P (ν i)
      = ∫ t : ℝ, (∑ i, c i * Complex.exp (((ν i : ℂ) * Complex.I) * (t : ℂ)))
          * kernel τ B P t := by
  have hexp : ∀ i : ι, psi τ B P (ν i)
      = ∫ t : ℝ, Complex.exp (((ν i : ℂ) * Complex.I) * (t : ℂ)) * kernel τ B P t :=
    fun i => (integral_exp_mul_kernel τ B hτ hB P (ν i) hint).symm
  have hcont : ∀ i : ι,
      Continuous (fun t : ℝ => Complex.exp (((ν i : ℂ) * Complex.I) * (t : ℂ))) := by
    intro i
    exact Complex.continuous_exp.comp (by fun_prop)
  have hnorm : ∀ i : ι, ∀ t : ℝ,
      ‖Complex.exp (((ν i : ℂ) * Complex.I) * (t : ℂ))‖ = 1 := by
    intro i t
    rw [Complex.norm_exp]
    have hre : (((ν i : ℂ) * Complex.I) * (t : ℂ)).re = 0 := by
      simp [Complex.mul_re]
    rw [hre, Real.exp_zero]
  -- 常数 `cᵢ` 与积分互换
  have hstep : ∀ i : ι, c i * (∫ t : ℝ,
        Complex.exp (((ν i : ℂ) * Complex.I) * (t : ℂ)) * kernel τ B P t)
      = ∫ t : ℝ,
          c i * (Complex.exp (((ν i : ℂ) * Complex.I) * (t : ℂ)) * kernel τ B P t) := by
    intro i
    rw [← MeasureTheory.integral_const_mul]
  have hint_i : ∀ i : ι, Integrable (fun t : ℝ =>
      c i * (Complex.exp (((ν i : ℂ) * Complex.I) * (t : ℂ)) * kernel τ B P t)) := by
    intro i
    exact (hint.bdd_mul (hcont i).aestronglyMeasurable
      (Eventually.of_forall fun t => (hnorm i t).le)).const_mul (c i)
  rw [Finset.sum_congr rfl (fun i _ => by rw [hexp i, hstep i])]
  rw [← MeasureTheory.integral_finsetSum Finset.univ (f := fun (i : ι) (t : ℝ) =>
    c i * (Complex.exp (((ν i : ℂ) * Complex.I) * (t : ℂ)) * kernel τ B P t))
    (fun i _ => hint_i i)]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  have hdist : (∑ i, c i *
        (Complex.exp (((ν i : ℂ) * Complex.I) * (t : ℂ)) * kernel τ B P t))
      = (∑ i, c i * Complex.exp (((ν i : ℂ) * Complex.I) * (t : ℂ))) * kernel τ B P t := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  exact hdist

/-- **第 2 步（模估计）**：指数和一致有界于 `2` 时，积分范数被 `2∫‖κ‖` 控制。 -/
lemma norm_integral_le_two_mul {ι : Type} [Fintype ι] (c : ι → ℂ) (ν : ι → ℝ)
    {τ B : ℝ} (hB : 0 < B) (P : Polynomial ℂ)
    (hbdd : ∀ lam : ℝ,
      ‖∑ i, Complex.exp ((((ν i * lam : ℝ)) : ℂ) * Complex.I) * c i‖ ≤ 2)
    (hint : Integrable (fun t : ℝ => kernel τ B P t)) :
    ‖∫ t : ℝ, (∑ i, c i * Complex.exp (((ν i : ℂ) * Complex.I) * (t : ℂ)))
        * kernel τ B P t‖
      ≤ 2 * ∫ t : ℝ, ‖kernel τ B P t‖ := by
  have hsum : ∀ t : ℝ,
      ‖∑ i, c i * Complex.exp (((ν i : ℂ) * Complex.I) * (t : ℂ))‖ ≤ 2 := by
    intro t
    have heq : (∑ i, c i * Complex.exp (((ν i : ℂ) * Complex.I) * (t : ℂ)))
        = ∑ i, Complex.exp ((((ν i * t : ℝ)) : ℂ) * Complex.I) * c i := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have harg : ((ν i : ℂ) * Complex.I) * (t : ℂ)
          = (((ν i * t : ℝ)) : ℂ) * Complex.I := by
        push_cast
        ring
      rw [harg, mul_comm]
    rw [heq]
    exact hbdd t
  have hpt : ∀ t : ℝ,
      ‖(∑ i, c i * Complex.exp (((ν i : ℂ) * Complex.I) * (t : ℂ)))
        * kernel τ B P t‖ ≤ 2 * ‖kernel τ B P t‖ := by
    intro t
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hsum t) (norm_nonneg _)
  have hg : Integrable (fun t : ℝ => 2 * ‖kernel τ B P t‖) := by
    simpa using hint.norm.const_mul (2 : ℝ)
  calc ‖∫ t : ℝ, (∑ i, c i * Complex.exp (((ν i : ℂ) * Complex.I) * (t : ℂ)))
        * kernel τ B P t‖
      ≤ ∫ t : ℝ, 2 * ‖kernel τ B P t‖ :=
        MeasureTheory.norm_integral_le_of_norm_le hg (Eventually.of_forall hpt)
    _ = 2 * ∫ t : ℝ, ‖kernel τ B P t‖ := MeasureTheory.integral_const_mul 2 _

/-- **M3 smearing 主定理**：`‖∑ᵢcᵢ‖ ≤ 8√(C₁C₂)`。 -/
theorem norm_sum_le_of_moments {ι : Type} [Fintype ι] (c : ι → ℂ) (ν : ι → ℝ)
    {τ ε : ℝ} (hτ : 0 < τ) (hε : 0 < ε) (hν : ∀ i, |ν i| ≤ τ)
    (P : Polynomial ℂ)
    (hPε : ∀ μ : ℝ, |μ| ≤ τ → ‖Complex.exp (-(μ : ℂ) * Complex.I) - P.eval ((μ : ℂ))‖ ≤ ε)
    (hmom : ∑ i, Complex.exp ((ν i : ℂ) * Complex.I) * P.eval ((ν i : ℂ)) * c i = 0)
    (hbdd : ∀ lam : ℝ,
      ‖∑ i, Complex.exp ((((ν i * lam : ℝ)) : ℂ) * Complex.I) * c i‖ ≤ 2)
    (hint : Integrable (fun t : ℝ => kernel τ (Real.sqrt ε) P t)) :
    ‖∑ i, c i‖ ≤ 8 * Real.sqrt
      (((2 * Real.pi)⁻¹ * ∫ μ in (-(τ + Real.sqrt ε + 1))..(τ + Real.sqrt ε + 1),
          ‖psi τ (Real.sqrt ε) P μ‖)
       * ((2 * Real.pi)⁻¹ * ∫ μ in (-(τ + Real.sqrt ε + 1))..(τ + Real.sqrt ε + 1),
            ‖deriv (deriv (psi τ (Real.sqrt ε) P)) μ‖)) := by
  have hB : 0 < Real.sqrt ε := Real.sqrt_pos_of_pos hε
  have hA : -(τ + Real.sqrt ε + 1) ≤ τ + Real.sqrt ε + 1 := by
    linarith [Real.sqrt_nonneg ε]
  set C1 : ℝ := (2 * Real.pi)⁻¹ * ∫ μ in (-(τ + Real.sqrt ε + 1))..(τ + Real.sqrt ε + 1),
      ‖psi τ (Real.sqrt ε) P μ‖ with hC1
  set C2 : ℝ := (2 * Real.pi)⁻¹ * ∫ μ in (-(τ + Real.sqrt ε + 1))..(τ + Real.sqrt ε + 1),
      ‖deriv (deriv (psi τ (Real.sqrt ε) P)) μ‖ with hC2
  have hC1nn : 0 ≤ C1 := by
    rw [hC1]
    exact mul_nonneg (by positivity)
      (intervalIntegral.integral_nonneg_of_forall hA (fun μ => norm_nonneg _))
  have hC2nn : 0 ≤ C2 := by
    rw [hC2]
    exact mul_nonneg (by positivity)
      (intervalIntegral.integral_nonneg_of_forall hA (fun μ => norm_nonneg _))
  have hb1 : ∀ t : ℝ, ‖kernel τ (Real.sqrt ε) P t‖ ≤ C1 := by
    intro t
    rw [hC1]
    exact norm_kernel_le τ (Real.sqrt ε) hτ.le hB P t
  have hb2 : ∀ t : ℝ, t ≠ 0 → ‖kernel τ (Real.sqrt ε) P t‖ ≤ C2 / t ^ 2 := by
    intro t ht
    calc ‖kernel τ (Real.sqrt ε) P t‖
        ≤ ((2 * Real.pi * t ^ 2)⁻¹) *
            ∫ μ in (-(τ + Real.sqrt ε + 1))..(τ + Real.sqrt ε + 1),
              ‖deriv (deriv (psi τ (Real.sqrt ε) P)) μ‖ :=
          norm_kernel_le_deriv τ (Real.sqrt ε) hτ hB P ht
      _ = C2 / t ^ 2 := by rw [hC2, div_eq_mul_inv, mul_inv]; ring
  have hkappa : ∫ t : ℝ, ‖kernel τ (Real.sqrt ε) P t‖ ≤ 4 * Real.sqrt (C1 * C2) :=
    integral_norm_le_sqrt (κ := fun t : ℝ => kernel τ (Real.sqrt ε) P t) hb1 hb2 hC1nn hC2nn
  have hrep := sum_mul_psi_eq_integral (τ := τ) (B := Real.sqrt ε) c ν hτ hB P hint
  have hred := sum_c_eq_sum_c_psi c ν hν hB P hmom
  have hbd := norm_integral_le_two_mul (τ := τ) (B := Real.sqrt ε) c ν hB P hbdd hint
  calc ‖∑ i, c i‖
      = ‖∑ i, c i * psi τ (Real.sqrt ε) P (ν i)‖ := by rw [hred]
    _ = ‖∫ t : ℝ, (∑ i, c i * Complex.exp (((ν i : ℂ) * Complex.I) * (t : ℂ)))
          * kernel τ (Real.sqrt ε) P t‖ := by rw [hrep]
    _ ≤ 2 * ∫ t : ℝ, ‖kernel τ (Real.sqrt ε) P t‖ := hbd
    _ ≤ 2 * (4 * Real.sqrt (C1 * C2)) :=
        mul_le_mul_of_nonneg_left hkappa (by norm_num)
    _ = 8 * Real.sqrt (C1 * C2) := by ring

/-!
## M3′：taper 宽度 `B` 参数化版本

`norm_sum_le_of_moments` 把 taper 宽度写死为 `B = √ε`，这与 `τ` **无关**：当 `τ → 0`
时 collar 相对宽度 `√ε/τ → ∞`，Chebyshev 界在 collar 上指数增长，`C₁ ~ k²/τ`、
`∫‖Ψ''‖` 中的项发散。论文用的是与 `τ` 成正比的 `B = ετ/q²`（由 `∫|κ̂| ≲ ετ`
与 `∫|κ̂''| ≲ k⁴/τ` 相乘把 `τ` 精确抵消）。

下面把 `B` 完全解放出来。底层零件（`norm_kernel_le`、`norm_kernel_le_deriv`、
`integral_norm_le_sqrt`、`integral_exp_mul_kernel`、`sum_c_eq_sum_c_psi`）本来就以
`B` 为自由变量，故证明与 `norm_sum_le_of_moments` 逐行相同，只是全程用 `hB : 0 < B`
代替 `Real.sqrt_pos_of_pos hε`。

（原 `norm_sum_le_of_moments` 保持原样未动；`norm_sum_le_of_moments_of_gen` 给出
机器验证的兼容性证书：本引理在 `B := √ε` 处的特化与它**逐字**同型。）
-/

set_option linter.unusedVariables false in
/-- **M3′ smearing 主定理（自由 taper 宽度 `B`）**：`‖∑ᵢcᵢ‖ ≤ 8√(C₁C₂)`，
其中 `C₁ = (2π)⁻¹∫_{-A}^{A}‖Ψ‖`、`C₂ = (2π)⁻¹∫_{-A}^{A}‖Ψ''‖`、`A = τ + B + 1`。

注：`hε`（矩的精度）在本引理中不出现——`B` 是自由的，正确用法是把它取成与 `τ`
成正比的量（论文：`B = ετ/q²`）。`hε` 保留只为与原引理签名对齐、便于下游切换。 -/
theorem norm_sum_le_of_moments_gen {ι : Type} [Fintype ι] (c : ι → ℂ) (ν : ι → ℝ)
    {τ ε B : ℝ} (hτ : 0 < τ) (hε : 0 < ε) (hB : 0 < B) (hν : ∀ i, |ν i| ≤ τ)
    (P : Polynomial ℂ)
    (hPε : ∀ μ : ℝ, |μ| ≤ τ → ‖Complex.exp (-(μ : ℂ) * Complex.I) - P.eval ((μ : ℂ))‖ ≤ ε)
    (hmom : ∑ i, Complex.exp ((ν i : ℂ) * Complex.I) * P.eval ((ν i : ℂ)) * c i = 0)
    (hbdd : ∀ lam : ℝ,
      ‖∑ i, Complex.exp ((((ν i * lam : ℝ)) : ℂ) * Complex.I) * c i‖ ≤ 2)
    (hint : Integrable (fun t : ℝ => kernel τ B P t)) :
    ‖∑ i, c i‖ ≤ 8 * Real.sqrt
      (((2 * Real.pi)⁻¹ * ∫ μ in (-(τ + B + 1))..(τ + B + 1), ‖psi τ B P μ‖)
       * ((2 * Real.pi)⁻¹ * ∫ μ in (-(τ + B + 1))..(τ + B + 1),
            ‖deriv (deriv (psi τ B P)) μ‖)) := by
  have hA : -(τ + B + 1) ≤ τ + B + 1 := by linarith [hB.le]
  set C1 : ℝ := (2 * Real.pi)⁻¹ * ∫ μ in (-(τ + B + 1))..(τ + B + 1),
      ‖psi τ B P μ‖ with hC1
  set C2 : ℝ := (2 * Real.pi)⁻¹ * ∫ μ in (-(τ + B + 1))..(τ + B + 1),
      ‖deriv (deriv (psi τ B P)) μ‖ with hC2
  have hC1nn : 0 ≤ C1 := by
    rw [hC1]
    exact mul_nonneg (by positivity)
      (intervalIntegral.integral_nonneg_of_forall hA (fun μ => norm_nonneg _))
  have hC2nn : 0 ≤ C2 := by
    rw [hC2]
    exact mul_nonneg (by positivity)
      (intervalIntegral.integral_nonneg_of_forall hA (fun μ => norm_nonneg _))
  have hb1 : ∀ t : ℝ, ‖kernel τ B P t‖ ≤ C1 := by
    intro t
    rw [hC1]
    exact norm_kernel_le τ B hτ.le hB P t
  have hb2 : ∀ t : ℝ, t ≠ 0 → ‖kernel τ B P t‖ ≤ C2 / t ^ 2 := by
    intro t ht
    calc ‖kernel τ B P t‖
        ≤ ((2 * Real.pi * t ^ 2)⁻¹) *
            ∫ μ in (-(τ + B + 1))..(τ + B + 1),
              ‖deriv (deriv (psi τ B P)) μ‖ :=
          norm_kernel_le_deriv τ B hτ hB P ht
      _ = C2 / t ^ 2 := by rw [hC2, div_eq_mul_inv, mul_inv]; ring
  have hkappa : ∫ t : ℝ, ‖kernel τ B P t‖ ≤ 4 * Real.sqrt (C1 * C2) :=
    integral_norm_le_sqrt (κ := fun t : ℝ => kernel τ B P t) hb1 hb2 hC1nn hC2nn
  have hrep := sum_mul_psi_eq_integral (τ := τ) (B := B) c ν hτ hB P hint
  have hred := sum_c_eq_sum_c_psi c ν hν hB P hmom
  have hbd := norm_integral_le_two_mul (τ := τ) (B := B) c ν hB P hbdd hint
  calc ‖∑ i, c i‖
      = ‖∑ i, c i * psi τ B P (ν i)‖ := by rw [hred]
    _ = ‖∫ t : ℝ, (∑ i, c i * Complex.exp (((ν i : ℂ) * Complex.I) * (t : ℂ)))
          * kernel τ B P t‖ := by rw [hrep]
    _ ≤ 2 * ∫ t : ℝ, ‖kernel τ B P t‖ := hbd
    _ ≤ 2 * (4 * Real.sqrt (C1 * C2)) :=
        mul_le_mul_of_nonneg_left hkappa (by norm_num)
    _ = 8 * Real.sqrt (C1 * C2) := by ring

set_option linter.unusedVariables false in
/-- **M3″（论文的 taper 尺度 `B = ετ/q²`）**：`_gen` 在 `B := ε·τ/q²` 处的直接特化。

这是本文件存在的理由：`B` 与 `τ` 成正比，于是 collar 相对宽度 `B/τ = ε/q²` 与 `τ`
无关，`C₁ ~ ετ/q²` 型界与 `C₂ ~ k⁴/τ` 型界相乘时 `τ` 精确抵消（对照写死的 `B = √ε`
给出的 `√ε/τ → ∞`）。`hint` 由 `integrable_kernel` 自动消解，调用方无需提供。

主线的切换点：
`exact norm_sum_le_of_moments_tau_scaled c ν hτ hεpos hq hν P hPε hmom hbdd`。 -/
theorem norm_sum_le_of_moments_tau_scaled {ι : Type} [Fintype ι] (c : ι → ℂ) (ν : ι → ℝ)
    {τ ε q : ℝ} (hτ : 0 < τ) (hε : 0 < ε) (hq : 0 < q) (hν : ∀ i, |ν i| ≤ τ)
    (P : Polynomial ℂ)
    (hPε : ∀ μ : ℝ, |μ| ≤ τ → ‖Complex.exp (-(μ : ℂ) * Complex.I) - P.eval ((μ : ℂ))‖ ≤ ε)
    (hmom : ∑ i, Complex.exp ((ν i : ℂ) * Complex.I) * P.eval ((ν i : ℂ)) * c i = 0)
    (hbdd : ∀ lam : ℝ,
      ‖∑ i, Complex.exp ((((ν i * lam : ℝ)) : ℂ) * Complex.I) * c i‖ ≤ 2) :
    ‖∑ i, c i‖ ≤ 8 * Real.sqrt
      (((2 * Real.pi)⁻¹ * ∫ μ in (-(τ + ε * τ / q ^ 2 + 1))..(τ + ε * τ / q ^ 2 + 1),
          ‖psi τ (ε * τ / q ^ 2) P μ‖)
       * ((2 * Real.pi)⁻¹ * ∫ μ in (-(τ + ε * τ / q ^ 2 + 1))..(τ + ε * τ / q ^ 2 + 1),
            ‖deriv (deriv (psi τ (ε * τ / q ^ 2) P)) μ‖)) :=
  norm_sum_le_of_moments_gen c ν hτ hε
    (div_pos (mul_pos hε hτ) (pow_pos hq 2)) hν P hPε hmom hbdd
    (integrable_kernel τ (ε * τ / q ^ 2) hτ (div_pos (mul_pos hε hτ) (pow_pos hq 2)) P)

/-- **兼容性证书**：`norm_sum_le_of_moments_gen` 在 `B := √ε` 处的特化就是
`norm_sum_le_of_moments` 的陈述（区间 `-(τ+√ε+1)..(τ+√ε+1)`、核 `kernel τ (√ε) P`
逐字相同）。此引理的证明体是对 `_gen` 的一次 `exact` 应用，因此它的**编译通过**
即机器验证了"原引理可以零风险地改写为 `_gen` 的推论、下游零改动"。

（本文件出于"不得改动已有 `norm_sum_le_of_moments`"的约束，未真的做这步改写；
主线若想消除重复证明，把原引理证明体换成 `exact norm_sum_le_of_moments_of_gen …`
即可——那个 `exact` 已在此处被验证过。） -/
theorem norm_sum_le_of_moments_of_gen {ι : Type} [Fintype ι] (c : ι → ℂ) (ν : ι → ℝ)
    {τ ε : ℝ} (hτ : 0 < τ) (hε : 0 < ε) (hν : ∀ i, |ν i| ≤ τ)
    (P : Polynomial ℂ)
    (hPε : ∀ μ : ℝ, |μ| ≤ τ → ‖Complex.exp (-(μ : ℂ) * Complex.I) - P.eval ((μ : ℂ))‖ ≤ ε)
    (hmom : ∑ i, Complex.exp ((ν i : ℂ) * Complex.I) * P.eval ((ν i : ℂ)) * c i = 0)
    (hbdd : ∀ lam : ℝ,
      ‖∑ i, Complex.exp ((((ν i * lam : ℝ)) : ℂ) * Complex.I) * c i‖ ≤ 2)
    (hint : Integrable (fun t : ℝ => kernel τ (Real.sqrt ε) P t)) :
    ‖∑ i, c i‖ ≤ 8 * Real.sqrt
      (((2 * Real.pi)⁻¹ * ∫ μ in (-(τ + Real.sqrt ε + 1))..(τ + Real.sqrt ε + 1),
          ‖psi τ (Real.sqrt ε) P μ‖)
       * ((2 * Real.pi)⁻¹ * ∫ μ in (-(τ + Real.sqrt ε + 1))..(τ + Real.sqrt ε + 1),
            ‖deriv (deriv (psi τ (Real.sqrt ε) P)) μ‖)) :=
  norm_sum_le_of_moments_gen c ν hτ hε (Real.sqrt_pos_of_pos hε) hν P hPε hmom hbdd hint

end RobustZ
