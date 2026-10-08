import RobustZ.M5Apply
import RobustZ.Final
import RobustZ.CollarBound
import RobustZ.PsiBounds

/-!
# M5 收尾：把 `8√(C₁C₂)` 压到端点常数以下

`C₁ = kernelA τ (√ε) P`、`C₂ = kernelC τ (√ε) P`（`τ = (Σθ)/2`、`ε = epsOf τ δ' k`、`P = scaledApprox τ k`）。
本文件给出把这两个常数用小 `ε` 控制的显式界。
-/

noncomputable section

namespace RobustZ

open Filter MeasureTheory

/-- `Ψ` 在整条实轴上被 `ε + B·M₁` 一致控制（带内用逼近界，collar 用中值定理，带外为零）。 -/
lemma norm_psi_le_band_add_collar {τ B : ℝ} (hτ : 0 ≤ τ) (hB : 0 < B) (P : Polynomial ℂ)
    {ε M₁ : ℝ} (hM₁ : 0 ≤ M₁)
    (hPε : ∀ μ : ℝ, |μ| ≤ τ →
      ‖Complex.exp (-(μ : ℂ) * Complex.I) - P.eval ((μ : ℂ))‖ ≤ ε)
    (hM : ∀ μ : ℝ, |μ| ≤ τ + B → ‖deriv (fun x : ℝ => psiA P x) μ‖ ≤ M₁) :
    ∀ μ : ℝ, ‖psi τ B P μ‖ ≤ ε + B * M₁ := by
  intro μ
  have hnonneg : (0:ℝ) ≤ ε + B * M₁ := by
    have := norm_nonneg (Complex.exp (-((0:ℝ) : ℂ) * Complex.I) - P.eval (((0:ℝ) : ℂ)))
    have h0 : (0:ℝ) ≤ ε := le_trans this (hPε 0 (by simp [abs_zero]; exact hτ))
    nlinarith [mul_nonneg hB.le hM₁]
  by_cases hband : |μ| ≤ τ
  · refine le_trans (norm_psi_le_band τ B hB P hPε μ hband) ?_
    nlinarith [mul_nonneg hB.le hM₁]
  · by_cases hcol : |μ| ≤ τ + B
    · have hA : ‖psiA P μ‖ ≤ ε + B * M₁ := norm_psiA_le τ B hτ hB P hPε hM μ hcol
      have hcut : ‖psi τ B P μ‖ ≤ ‖psiA P μ‖ := by
        have hnorm : ‖(((cutoff τ B μ : ℝ)) : ℂ)‖ = |cutoff τ B μ| :=
          RCLike.norm_ofReal _
        have h1 : |cutoff τ B μ| ≤ 1 := by
          rw [abs_of_nonneg (cutoff_nonneg τ B μ)]
          exact cutoff_le_one τ B μ
        rw [psi, norm_mul, hnorm]
        calc ‖psiA P μ‖ * |cutoff τ B μ| ≤ ‖psiA P μ‖ * 1 :=
              mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
          _ = ‖psiA P μ‖ := mul_one _
      exact le_trans hcut hA
    · have hout : τ + B ≤ |μ| := le_of_lt (lt_of_not_ge hcol)
      rw [psi_eq_zero P hB hout, norm_zero]
      exact hnonneg

/-- `‖Ψ‖` 在积分区间上可积。 -/
lemma intervalIntegrable_norm_psi {τ B : ℝ} (hτ : 0 < τ) (hB : 0 < B) (P : Polynomial ℂ) :
    IntervalIntegrable (fun μ : ℝ => ‖psi τ B P μ‖) (MeasureTheory.volume)
      (-(τ + B + 1)) (τ + B + 1) :=
  (((contDiff_psi τ B hτ hB P).continuous).norm).intervalIntegrable
    (-(τ + B + 1)) (τ + B + 1) (μ := MeasureTheory.volume)

/-- **`C₁` 的显式界**：`kernelA τ B P ≤ (2π)⁻¹·2(τ+B+1)·(ε + B·M₁)`。 -/
lemma kernelA_le {τ B : ℝ} (hτ : 0 < τ) (hB : 0 < B) (P : Polynomial ℂ) {ε M₁ : ℝ}
    (hψ : ∀ μ : ℝ, ‖psi τ B P μ‖ ≤ ε + B * M₁) :
    kernelA τ B P ≤ (2 * Real.pi)⁻¹ * (2 * (τ + B + 1)) * (ε + B * M₁) := by
  rw [kernelA]
  have hfac : (0:ℝ) ≤ (2 * Real.pi)⁻¹ := by positivity
  have hA : -(τ + B + 1) ≤ τ + B + 1 := by linarith
  have hmain : ∫ μ in (-(τ + B + 1))..(τ + B + 1), ‖psi τ B P μ‖
      ≤ (2 * (τ + B + 1)) * (ε + B * M₁) := by
    calc ∫ μ in (-(τ + B + 1))..(τ + B + 1), ‖psi τ B P μ‖
        ≤ ∫ μ in (-(τ + B + 1))..(τ + B + 1), (ε + B * M₁) :=
          intervalIntegral.integral_mono_on (f := fun μ : ℝ => ‖psi τ B P μ‖)
            (g := fun _ : ℝ => ε + B * M₁) hA (intervalIntegrable_norm_psi hτ hB P)
            (intervalIntegrable_const (μ := (MeasureTheory.volume : Measure ℝ))
              (c := ε + B * M₁)) (fun μ _ => hψ μ)
      _ = (τ + B + 1 - (-(τ + B + 1))) * (ε + B * M₁) := by
          rw [intervalIntegral.integral_const]; simp [smul_eq_mul]
      _ = 2 * (τ + B + 1) * (ε + B * M₁) := by ring
  calc (2 * Real.pi)⁻¹ * ∫ μ in (-(τ + B + 1))..(τ + B + 1), ‖psi τ B P μ‖
      ≤ (2 * Real.pi)⁻¹ * (2 * (τ + B + 1) * (ε + B * M₁)) :=
        mul_le_mul_of_nonneg_left hmain hfac
    _ = (2 * Real.pi)⁻¹ * (2 * (τ + B + 1)) * (ε + B * M₁) := by ring

/-- **`C₂` 的显式界**（支撑感知的 `∫‖Ψ''‖` 界，`B = √ε`）。 -/
lemma kernelC_le {τ B : ℝ} (hτ : 0 < τ) (hB : 0 < B) (P : Polynomial ℂ) {ε M₁ M₂ K : ℝ}
    (hε : 0 ≤ ε)
    (hPε : ∀ μ : ℝ, |μ| ≤ τ →
      ‖Complex.exp (-(μ : ℂ) * Complex.I) - P.eval ((μ : ℂ))‖ ≤ ε)
    (hA1 : ∀ μ : ℝ, |μ| ≤ τ + B → ‖deriv (fun x : ℝ => psiA P x) μ‖ ≤ M₁)
    (hA2 : ∀ μ : ℝ, |μ| ≤ τ + B → ‖deriv (deriv (fun x : ℝ => psiA P x)) μ‖ ≤ M₂)
    (hK1 : ∀ μ : ℝ, ‖deriv (fun x : ℝ => ((cutoff τ B x : ℝ) : ℂ)) μ‖ ≤ K / B)
    (hK2 : ∀ μ : ℝ, ‖deriv (deriv (fun x : ℝ => ((cutoff τ B x : ℝ) : ℂ))) μ‖ ≤ K / B ^ 2) :
    kernelC τ B P ≤ (2 * Real.pi)⁻¹ *
      (2 * (τ + B + 1) * M₂ + 2 * (M₁ * (2 * K)) + (ε + B * M₁) * (4 * K / B)) := by
  rw [kernelC]
  have hfac : (0:ℝ) ≤ (2 * Real.pi)⁻¹ := by positivity
  exact mul_le_mul_of_nonneg_left
    (integral_norm_deriv2_psi_le_sharp τ B hτ hB P hε hPε hA1 hA2 hK1 hK2) hfac

end RobustZ
