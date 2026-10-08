import RobustZ.KernelBound
import RobustZ.L1Bound

/-!
# M3：核的 L¹ 可积性

`κ(t) = (2π)⁻¹∫ Ψ(μ)e^{−iμt}dμ`，其中 `Ψ = (1 − Pe^{iμ})χ` 是紧支 `C²` 函数。

由 `norm_kernel_le`（一致界 `A`）和 `norm_kernel_le_deriv`（`C / t²` 衰减）拼出
`κ` 在 `ℝ` 上（Bochner）可积：

* `κ` 是参数积分，因而是**连续**的，于是 `AEStronglyMeasurable`；
* 在 `Ioc (-1) 1` 上被常数 `A` 支配，测度有限；
* 在两条尾 `Iic (-1)`、`Ioi 1` 上被 `C · t⁻²` 支配。

三段用 `IntegrableOn.union` 合并，`Ioc (-1) 1 ∪ (Iic (-1) ∪ Ioi 1) = univ`。
-/

noncomputable section

namespace RobustZ

open scoped Real
open Filter MeasureTheory

/-- 一致界常数 `A = (2π)⁻¹ ∫ ‖Ψ‖`。 -/
noncomputable def kernelA (τ B : ℝ) (P : Polynomial ℂ) : ℝ :=
  (2 * Real.pi)⁻¹ * ∫ μ in (-(τ + B + 1))..(τ + B + 1), ‖psi τ B P μ‖

/-- 衰减常数 `C = (2π)⁻¹ ∫ ‖Ψ''‖`。 -/
noncomputable def kernelC (τ B : ℝ) (P : Polynomial ℂ) : ℝ :=
  (2 * Real.pi)⁻¹ * ∫ μ in (-(τ + B + 1))..(τ + B + 1), ‖deriv (deriv (psi τ B P)) μ‖

/-- 一致界：`∀ t, ‖κ t‖ ≤ A`。 -/
lemma norm_kernel_le_A (τ B : ℝ) (hτ : 0 ≤ τ) (hB : 0 < B) (P : Polynomial ℂ) (t : ℝ) :
    ‖kernel τ B P t‖ ≤ kernelA τ B P :=
  norm_kernel_le τ B hτ hB P t

/-- 二次衰减：`∀ t ≠ 0, ‖κ t‖ ≤ C / t²`。 -/
lemma norm_kernel_le_C (τ B : ℝ) (hτ : 0 < τ) (hB : 0 < B) (P : Polynomial ℂ) {t : ℝ}
    (ht : t ≠ 0) : ‖kernel τ B P t‖ ≤ kernelC τ B P / t ^ 2 := by
  have h := norm_kernel_le_deriv τ B hτ hB P ht
  rw [kernelC, div_eq_mul_inv]
  calc ‖kernel τ B P t‖
      ≤ (2 * Real.pi * t ^ 2)⁻¹ * ∫ μ in (-(τ + B + 1))..(τ + B + 1),
          ‖deriv (deriv (psi τ B P)) μ‖ := h
    _ = ((2 * Real.pi)⁻¹ * ∫ μ in (-(τ + B + 1))..(τ + B + 1),
          ‖deriv (deriv (psi τ B P)) μ‖) * (t ^ 2)⁻¹ := by
        rw [mul_inv]
        ring

/-- `κ` 作为 `t` 的函数连续（`Ψ` 连续紧支，参数积分由控制收敛定理连续）。 -/
lemma continuous_kernel (τ B : ℝ) (hτ : 0 < τ) (hB : 0 < B) (P : Polynomial ℂ) :
    Continuous fun t : ℝ => kernel τ B P t := by
  have hΨ : ContDiff ℝ 2 (psi τ B P) := contDiff_psi τ B hτ hB P
  have hpsi : Continuous (psi τ B P) := hΨ.continuous
  have hmain : Continuous fun x : ℝ => ∫ μ in (-(τ + B + 1))..(τ + B + 1),
      psi τ B P μ * Complex.exp (-((μ : ℂ) * Complex.I * (x : ℂ))) := by
    refine intervalIntegral.continuous_of_dominated_interval (X := ℝ)
      (F := fun x μ => psi τ B P μ * Complex.exp (-((μ : ℂ) * Complex.I * (x : ℂ))))
      (bound := fun μ => ‖psi τ B P μ‖) (μ := volume) ?_ ?_ ?_ ?_
    · -- `F x` 连续，故 a.e. 强可测
      intro x
      exact (hpsi.mul (Complex.continuous_exp.comp
        (((Complex.continuous_ofReal.mul continuous_const).mul continuous_const).neg))).aestronglyMeasurable
    · -- 被 `‖Ψ‖` 一致支配
      intro x
      refine Eventually.of_forall fun μ _ => ?_
      rw [norm_mul, Complex.norm_exp]
      have hre : (-((μ : ℂ) * Complex.I * (x : ℂ))).re = 0 := by
        simp [Complex.mul_re]
      rw [hre, Real.exp_zero, mul_one]
    · -- `‖Ψ‖` 在区间上可积
      exact (continuous_norm.comp hpsi).intervalIntegrable _ _
    · -- 对每个 `μ`，`x ↦ Ψ(μ)e^{−iμx}` 连续
      refine Eventually.of_forall fun μ _ => ?_
      exact continuous_const.mul (Complex.continuous_exp.comp
        (((continuous_const : Continuous fun _ : ℝ => (μ : ℂ) * Complex.I).mul
          Complex.continuous_ofReal).neg))
  have hc : Continuous fun _ : ℝ => ((2 * Real.pi)⁻¹ : ℝ) := continuous_const
  have hsm : Continuous fun x : ℝ => ((2 * Real.pi)⁻¹ : ℝ) •
      ∫ μ in (-(τ + B + 1))..(τ + B + 1),
        psi τ B P μ * Complex.exp (-((μ : ℂ) * Complex.I * (x : ℂ))) :=
    hc.smul hmain
  simpa only [kernel] using hsm

lemma aestronglyMeasurable_kernel (τ B : ℝ) (hτ : 0 < τ) (hB : 0 < B) (P : Polynomial ℂ) :
    AEStronglyMeasurable (fun t : ℝ => kernel τ B P t) volume :=
  (continuous_kernel τ B hτ hB P).aestronglyMeasurable

/-- **目标**：核 `κ(t) = (2π)⁻¹∫ Ψ(μ)e^{−iμt}dμ` 在 `ℝ` 上可积。 -/
lemma integrable_kernel (τ B : ℝ) (hτ : 0 < τ) (hB : 0 < B) (P : Polynomial ℂ) :
    Integrable (fun t : ℝ => kernel τ B P t) := by
  have hmeas : AEStronglyMeasurable (fun t : ℝ => kernel τ B P t) volume :=
    aestronglyMeasurable_kernel τ B hτ hB P
  have hmeas' : ∀ s : Set ℝ,
      AEStronglyMeasurable (fun t : ℝ => kernel τ B P t) (volume.restrict s) :=
    fun s => hmeas.mono_measure (Measure.restrict_le_self)
  have hboundA : ∀ t : ℝ, ‖kernel τ B P t‖ ≤ kernelA τ B P :=
    fun t => norm_kernel_le_A τ B hτ.le hB P t
  have hboundC : ∀ t : ℝ, t ≠ 0 → ‖kernel τ B P t‖ ≤ kernelC τ B P / t ^ 2 :=
    fun t ht => norm_kernel_le_C τ B hτ hB P ht
  -- 中段 `Ioc (-1) 1`：有限测度 + 一致界 `A`
  have hmid : IntegrableOn (fun t : ℝ => kernel τ B P t) (Set.Ioc (-1) 1) volume :=
    IntegrableOn.of_bound (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top)
      (hmeas' _) (kernelA τ B P) (Eventually.of_forall hboundA)
  -- 右尾 `Ioi 1`：被 `C · t⁻²` 支配
  have hright : IntegrableOn (fun t : ℝ => kernel τ B P t) (Set.Ioi 1) volume := by
    refine Integrable.mono' (μ := volume.restrict (Set.Ioi 1))
      (f := fun t : ℝ => kernel τ B P t)
      (g := fun t : ℝ => kernelC τ B P * (t ^ 2)⁻¹)
      ((integrableOn_inv_sq_Ioi (R := 1) one_pos).const_mul (kernelC τ B P))
      (hmeas' _) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : t ≠ 0 := by
      rintro rfl
      linarith [Set.mem_Ioi.mp ht]
    rw [← div_eq_mul_inv]
    exact hboundC t ht0
  -- 左尾 `Iic (-1)`：被 `C · t⁻²` 支配
  have hleft : IntegrableOn (fun t : ℝ => kernel τ B P t) (Set.Iic (-1)) volume := by
    refine Integrable.mono' (μ := volume.restrict (Set.Iic (-1)))
      (f := fun t : ℝ => kernel τ B P t)
      (g := fun t : ℝ => kernelC τ B P * (t ^ 2)⁻¹)
      ((integrableOn_inv_sq_Iic (R := 1) one_pos).const_mul (kernelC τ B P))
      (hmeas' _) ?_
    filter_upwards [ae_restrict_mem measurableSet_Iic] with t ht
    have ht0 : t ≠ 0 := by
      rintro rfl
      linarith [Set.mem_Iic.mp ht]
    rw [← div_eq_mul_inv]
    exact hboundC t ht0
  -- 合并三段
  have huniv : (Set.Ioc (-1) 1 ∪ (Set.Iic (-1) ∪ Set.Ioi 1) : Set ℝ) = Set.univ := by
    rw [← Set.compl_Ioc (a := (-1)) (b := 1), Set.union_compl_self]
  rw [← integrableOn_univ, ← huniv]
  exact hmid.union (hleft.union hright)

end RobustZ
