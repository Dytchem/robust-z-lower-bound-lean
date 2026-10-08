import RobustZ.Approx
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# M3：smearing 核的截断函数

`cutoff τ B μ = σ((τ + B − |μ|)/B)`，其中 `σ = Real.smoothTransition`：
在 `|μ| ≤ τ` 上等于 1，在 `|μ| ≥ τ + B` 上等于 0，取值在 `[0,1]`，光滑。
`B > 0` 是 taper 宽度。
-/

noncomputable section

namespace RobustZ

open scoped Real
open Filter MeasureTheory

/-- 光滑截断：`|μ| ≤ τ` 处为 1，`|μ| ≥ τ + B` 处为 0。 -/
noncomputable def cutoff (τ B : ℝ) (μ : ℝ) : ℝ :=
  Real.smoothTransition ((τ + B - |μ|) / B)

lemma cutoff_eq_one {τ B μ : ℝ} (hB : 0 < B) (h : |μ| ≤ τ) : cutoff τ B μ = 1 := by
  refine Real.smoothTransition.one_of_one_le ?_
  rw [le_div_iff₀ hB]
  linarith [neg_abs_le μ]

lemma cutoff_eq_zero {τ B μ : ℝ} (hB : 0 < B) (h : τ + B ≤ |μ|) : cutoff τ B μ = 0 := by
  exact Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hB.le)

lemma cutoff_nonneg (τ B μ : ℝ) : 0 ≤ cutoff τ B μ :=
  Real.smoothTransition.nonneg _

lemma cutoff_le_one (τ B μ : ℝ) : cutoff τ B μ ≤ 1 :=
  Real.smoothTransition.le_one _

/-- `cutoff` 在 `τ > 0` 时是 `C²` 的（`μ = 0` 附近恒等于 1）。 -/
lemma contDiff_cutoff (τ B : ℝ) (hτ : 0 < τ) (hB : 0 < B) :
    ContDiff ℝ 2 (cutoff τ B) := by
  rw [contDiff_iff_contDiffAt]
  intro μ
  rcases eq_or_ne μ 0 with rfl | hne
  · refine (contDiffAt_const (c := (1 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hτ] with x hx
    refine cutoff_eq_one hB ?_
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hx
    exact le_of_lt (by simpa using hx)
  · have hBne : B ≠ 0 := ne_of_gt hB
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · have hev : (fun x : ℝ => (τ + B - |x|) / B) =ᶠ[nhds μ] (fun x : ℝ => (τ + B + x) / B) := by
        filter_upwards [isOpen_Iio.mem_nhds hneg] with x hx
        rw [abs_of_neg hx]
        ring
      have h1 : ContDiffAt ℝ 2 (fun x : ℝ => (τ + B + x) / B) μ := by fun_prop
      exact (Real.smoothTransition.contDiff.contDiffAt.comp μ (h1.congr_of_eventuallyEq hev))
    · have hev : (fun x : ℝ => (τ + B - |x|) / B) =ᶠ[nhds μ] (fun x : ℝ => (τ + B - x) / B) := by
        filter_upwards [isOpen_Ioi.mem_nhds hpos] with x hx
        rw [abs_of_pos hx]
      have h1 : ContDiffAt ℝ 2 (fun x : ℝ => (τ + B - x) / B) μ := by fun_prop
      exact (Real.smoothTransition.contDiff.contDiffAt.comp μ (h1.congr_of_eventuallyEq hev))

/-- `A(μ) = 1 − P(μ)e^{iμ}`。 -/
noncomputable def psiA (P : Polynomial ℂ) (μ : ℝ) : ℂ :=
  1 - P.eval ((μ : ℂ)) * Complex.exp ((μ : ℂ) * Complex.I)

/-- `Ψ(μ) = (1 − P(μ)e^{iμ})·χ(μ)`（光滑紧支，支撑含于 `[−(τ+B), τ+B]`）。 -/
noncomputable def psi (τ B : ℝ) (P : Polynomial ℂ) (μ : ℝ) : ℂ :=
  psiA P μ * (cutoff τ B μ : ℂ)

-- 积分区间取 `±(τ+B+1)`，严格大于 `Ψ` 的支撑 `±(τ+B)`，
-- 这样分部积分的边界项自动为零（`Ψ` 在端点附近恒为零）。
/-- 核 `κ(t) = (2π)⁻¹∫ Ψ(μ)e^{−iμt}dμ`。 -/
noncomputable def kernel (τ B : ℝ) (P : Polynomial ℂ) (t : ℝ) : ℂ :=
  ((2 * Real.pi)⁻¹ : ℝ) • ∫ μ in (-(τ + B + 1))..(τ + B + 1),
    psi τ B P μ * Complex.exp (-((μ : ℂ) * Complex.I * (t : ℂ)))

/-- 带内 `Ψ = 1 − Pe^{iμ}`（`χ ≡ 1`）。 -/
lemma psi_eq_psiA (P : Polynomial ℂ) {τ B : ℝ} (hB : 0 < B) {μ : ℝ} (h : |μ| ≤ τ) :
    psi τ B P μ = psiA P μ := by
  rw [psi, cutoff_eq_one hB h, Complex.ofReal_one, mul_one]

/-- 支撑外 `Ψ = 0`。 -/
lemma psi_eq_zero (P : Polynomial ℂ) {τ B : ℝ} (hB : 0 < B) {μ : ℝ} (h : τ + B ≤ |μ|) :
    psi τ B P μ = 0 := by
  rw [psi, cutoff_eq_zero hB h, Complex.ofReal_zero, mul_zero]

/-- 带内 `Ψ` 的一致界：`|μ| ≤ τ` 时 `‖Ψ(μ)‖ ≤ ε`。 -/
lemma norm_psi_le_band (τ B : ℝ) (hB : 0 < B) (P : Polynomial ℂ) {ε : ℝ}
    (hPε : ∀ μ : ℝ, |μ| ≤ τ → ‖Complex.exp (-(μ : ℂ) * Complex.I) - P.eval ((μ : ℂ))‖ ≤ ε) :
    ∀ μ : ℝ, |μ| ≤ τ → ‖psi τ B P μ‖ ≤ ε := by
  intro μ hμ
  rw [psi, cutoff_eq_one hB hμ, Complex.ofReal_one, mul_one, psiA]
  have hfac : 1 - P.eval ((μ : ℂ)) * Complex.exp ((μ : ℂ) * Complex.I)
      = Complex.exp ((μ : ℂ) * Complex.I)
        * (Complex.exp (-((μ : ℂ) * Complex.I)) - P.eval ((μ : ℂ))) := by
    have h1 : Complex.exp ((μ : ℂ) * Complex.I) * Complex.exp (-((μ : ℂ) * Complex.I)) = 1 := by
      rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
    rw [mul_sub, h1]
    ring
  have hexp : ‖Complex.exp ((μ : ℂ) * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp]
    have hre : ((μ : ℂ) * Complex.I).re = 0 := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [hre, Real.exp_zero]
  rw [hfac, norm_mul, hexp, one_mul]
  simpa only [neg_mul] using hPε μ hμ

/-- 核的平凡界：`‖κ(t)‖ ≤ (2π)⁻¹∫‖Ψ‖`。 -/
lemma norm_kernel_le (τ B : ℝ) (hτ : 0 ≤ τ) (hB : 0 < B) (P : Polynomial ℂ) (t : ℝ) :
    ‖kernel τ B P t‖ ≤ ((2 * Real.pi)⁻¹) *
      ∫ μ in (-(τ + B + 1))..(τ + B + 1), ‖psi τ B P μ‖ := by
  rw [kernel, norm_smul, Real.norm_of_nonneg (by positivity)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hle := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
    (f := fun μ : ℝ => psi τ B P μ * Complex.exp (-((μ : ℂ) * Complex.I * (t : ℂ))))
    (show -(τ + B + 1) ≤ τ + B + 1 by linarith)
  refine hle.trans (le_of_eq ?_)
  refine intervalIntegral.integral_congr (f := fun μ : ℝ =>
    ‖psi τ B P μ * Complex.exp (-((μ : ℂ) * Complex.I * (t : ℂ)))‖)
    (g := fun μ : ℝ => ‖psi τ B P μ‖) fun μ _ => ?_
  dsimp only
  rw [norm_mul, Complex.norm_exp]
  have hre : (-((μ : ℂ) * Complex.I * (t : ℂ))).re = 0 := by
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.neg_re, Complex.neg_im, mul_zero, zero_mul, sub_zero, add_zero,
      neg_zero]
  rw [hre, Real.exp_zero, mul_one]

/-- **M3 代数归约**：由矩条件，`Σᵢcᵢ = ΣᵢcᵢΨ(νᵢ)`（`Ψ` 在带内等于 `1 − Pe^{iμ}`）。 -/
lemma sum_c_eq_sum_c_psi {ι : Type} [Fintype ι] (c : ι → ℂ) (ν : ι → ℝ) {τ B : ℝ}
    (hν : ∀ i, |ν i| ≤ τ) (hB : 0 < B) (P : Polynomial ℂ)
    (hmom : ∑ i, Complex.exp ((ν i : ℂ) * Complex.I) * P.eval ((ν i : ℂ)) * c i = 0) :
    ∑ i, c i = ∑ i, c i * psi τ B P (ν i) := by
  have h1 : ∀ i, c i * psi τ B P (ν i)
      = c i - c i * (P.eval ((ν i : ℂ)) * Complex.exp ((ν i : ℂ) * Complex.I)) := by
    intro i
    rw [psi_eq_psiA P hB (hν i), psiA]
    ring
  rw [Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_sub_distrib]
  have h2 : ∑ i, c i * (P.eval ((ν i : ℂ)) * Complex.exp ((ν i : ℂ) * Complex.I)) = 0 := by
    rw [← hmom]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h2, sub_zero]

end RobustZ
