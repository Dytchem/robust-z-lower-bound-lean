import RobustZ.KernelBound
import Mathlib.Analysis.Fourier.Inversion

/-!
# M3：反演恒等式

Mathlib 的 Fourier 归一化是
`𝓕 f w = ∫ v, 𝐞(-⟪v,w⟫) • f v = ∫ v, f v · e^{−2πivw} dv`（**没有** `(2π)⁻¹` 因子），
而 `kernel τ B P t = (2π)⁻¹ ∫ Ψ(μ)e^{−iμt}dμ`。做代换 `μ = 2πν` 即得

`kernel τ B P t = 𝓕 (fun ν : ℝ => psi τ B P (2πν)) t`（**正变换** `𝓕`，不是 `𝓕⁻`）。

由此配合 Fourier 反演公式 `𝓕⁻ (𝓕 Φ) = Φ` 得到主定理（M3 反演恒等式）

`∫ t, e^{iλt} κ(t) dt = Ψ(λ)`。
-/

noncomputable section

namespace RobustZ

open scoped Real FourierTransform RealInnerProductSpace
open Filter MeasureTheory

/-- `Ψ` 的支撑含于 `[−(τ+B), τ+B]`。 -/
lemma support_psi_subset (τ B : ℝ) (hB : 0 < B) (P : Polynomial ℂ) :
    Function.support (psi τ B P) ⊆ Set.Icc (-(τ + B)) (τ + B) := by
  intro μ hμ
  rw [Set.mem_Icc]
  have h : ¬ (τ + B ≤ |μ|) := fun hc => hμ (psi_eq_zero P hB hc)
  have h' : |μ| < τ + B := lt_of_not_ge h
  exact ⟨by linarith [h', neg_abs_le μ], by linarith [h', le_abs_self μ]⟩

/-- `Ψ` 紧支。 -/
lemma hasCompactSupport_psi (τ B : ℝ) (hB : 0 < B) (P : Polynomial ℂ) :
    HasCompactSupport (psi τ B P) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc (support_psi_subset τ B hB P)

/-- **(2) 可积性**：`ν ↦ Ψ(2πν)` 紧支且连续，故可积。 -/
lemma integrable_psi_comp (τ B : ℝ) (hτ : 0 < τ) (hB : 0 < B) (P : Polynomial ℂ) :
    Integrable (fun ν : ℝ => psi τ B P (2 * Real.pi * ν)) := by
  have hcont : Continuous (fun ν : ℝ => psi τ B P (2 * Real.pi * ν)) :=
    (contDiff_psi τ B hτ hB P).continuous.comp (by fun_prop)
  have hpos : (0 : ℝ) < 2 * Real.pi := by positivity
  have hsupp : Function.support (fun ν : ℝ => psi τ B P (2 * Real.pi * ν))
      ⊆ Set.Icc (-(τ + B) / (2 * Real.pi)) ((τ + B) / (2 * Real.pi)) := by
    intro ν hν
    rw [Function.mem_support] at hν
    have hlt : |2 * Real.pi * ν| < τ + B := lt_of_not_ge fun hc => hν (psi_eq_zero P hB hc)
    rw [abs_mul, abs_of_pos hpos] at hlt
    have hlt' : |ν| * (2 * Real.pi) < τ + B := by linarith [hlt]
    rw [Set.mem_Icc]
    constructor
    · rw [div_le_iff₀ hpos]
      have h1 : -|ν| * (2 * Real.pi) ≤ ν * (2 * Real.pi) :=
        mul_le_mul_of_nonneg_right (neg_abs_le ν) hpos.le
      linarith [h1, hlt']
    · rw [le_div_iff₀ hpos]
      have h1 : ν * (2 * Real.pi) ≤ |ν| * (2 * Real.pi) :=
        mul_le_mul_of_nonneg_right (le_abs_self ν) hpos.le
      linarith [h1, hlt']
  exact hcont.integrable_of_hasCompactSupport
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupp)

/-- `Ψ` 在 `[−(τ+B+1), τ+B+1]` 之外为零，故全直线积分等于该区间上的积分。 -/
lemma integral_eq_intervalIntegral_psi (τ B : ℝ) (hτ : 0 < τ) (hB : 0 < B)
    (P : Polynomial ℂ) (t : ℝ) :
    (∫ μ : ℝ, psi τ B P μ * Complex.exp (-((μ : ℂ) * Complex.I * (t : ℂ))))
      = ∫ μ in (-(τ + B + 1))..(τ + B + 1),
          psi τ B P μ * Complex.exp (-((μ : ℂ) * Complex.I * (t : ℂ))) := by
  set A : ℝ := τ + B + 1 with hA
  have hzero : ∀ μ ∉ Set.Icc (-A) A,
      psi τ B P μ * Complex.exp (-((μ : ℂ) * Complex.I * (t : ℂ))) = 0 := by
    intro μ hμ
    have habs : τ + B ≤ |μ| := by
      by_contra hcon
      have hcon' : |μ| < τ + B := lt_of_not_ge hcon
      exact hμ (by
        rw [Set.mem_Icc]
        constructor <;> linarith [hA, neg_abs_le μ, le_abs_self μ])
    rw [psi_eq_zero P hB habs, zero_mul]
  calc (∫ μ : ℝ, psi τ B P μ * Complex.exp (-((μ : ℂ) * Complex.I * (t : ℂ))))
      = ∫ μ in Set.Icc (-A) A,
          psi τ B P μ * Complex.exp (-((μ : ℂ) * Complex.I * (t : ℂ))) :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero
          (s := Set.Icc (-A) A)
          (f := fun μ : ℝ => psi τ B P μ * Complex.exp (-((μ : ℂ) * Complex.I * (t : ℂ))))
          hzero).symm
    _ = ∫ μ in Set.Ioc (-A) A,
          psi τ B P μ * Complex.exp (-((μ : ℂ) * Complex.I * (t : ℂ))) :=
        MeasureTheory.integral_Icc_eq_integral_Ioc
    _ = ∫ μ in (-A)..A,
          psi τ B P μ * Complex.exp (-((μ : ℂ) * Complex.I * (t : ℂ))) :=
        (intervalIntegral.integral_of_le (show -A ≤ A by linarith)).symm
    _ = ∫ μ in (-(τ + B + 1))..(τ + B + 1),
          psi τ B P μ * Complex.exp (-((μ : ℂ) * Complex.I * (t : ℂ))) := by rw [hA]

/-- **(1) 桥接**：`kernel` 是 `ν ↦ Ψ(2πν)` 的 Fourier 变换（`𝓕`，非 `𝓕⁻`）。 -/
lemma kernel_eq_fourier (τ B : ℝ) (hτ : 0 < τ) (hB : 0 < B) (P : Polynomial ℂ) :
    (fun t : ℝ => kernel τ B P t)
      = 𝓕 (fun ν : ℝ => psi τ B P (2 * Real.pi * ν)) := by
  funext t
  have h2pi : (2 * Real.pi) ≠ 0 := by positivity
  -- 代换 `μ = 2πν` 后的被积函数：`g ((2π)⁻¹x) = Ψ(x)·e^{−ixt}`
  have hg : ∀ x : ℝ,
      (fun ν : ℝ => Complex.exp (↑(-2 * Real.pi * (ν * t)) * Complex.I)
        • psi τ B P (2 * Real.pi * ν)) ((2 * Real.pi)⁻¹ * x)
      = psi τ B P x * Complex.exp (-((x : ℂ) * Complex.I * (t : ℂ))) := by
    intro x
    have h2 : 2 * Real.pi * ((2 * Real.pi)⁻¹ * x) = x := by
      rw [← mul_assoc, mul_inv_cancel₀ h2pi, one_mul]
    have hexp : -2 * Real.pi * (((2 * Real.pi)⁻¹ * x) * t) = -(x * t) := by
      calc -2 * Real.pi * (((2 * Real.pi)⁻¹ * x) * t)
          = -((2 * Real.pi * ((2 * Real.pi)⁻¹ * x)) * t) := by ring
        _ = -(x * t) := by rw [h2]
    have harg : ((↑(-(x * t)) : ℂ)) * Complex.I = -((x : ℂ) * Complex.I * (t : ℂ)) := by
      push_cast
      ring
    simp only [smul_eq_mul]
    rw [hexp, h2, harg,
      mul_comm (Complex.exp (-((x : ℂ) * Complex.I * (t : ℂ)))) (psi τ B P x)]
  have hleft : (∫ x : ℝ, (fun ν : ℝ => Complex.exp (↑(-2 * Real.pi * (ν * t)) * Complex.I)
        • psi τ B P (2 * Real.pi * ν)) ((2 * Real.pi)⁻¹ * x))
      = ∫ x : ℝ, psi τ B P x * Complex.exp (-((x : ℂ) * Complex.I * (t : ℂ))) :=
    integral_congr_ae (Filter.Eventually.of_forall hg)
  -- 变量替换 `MeasureTheory.Measure.integral_comp_mul_left`
  have hscale : (∫ x : ℝ, (fun ν : ℝ => Complex.exp (↑(-2 * Real.pi * (ν * t)) * Complex.I)
        • psi τ B P (2 * Real.pi * ν)) ((2 * Real.pi)⁻¹ * x))
      = (2 * Real.pi) • ∫ y : ℝ, Complex.exp (↑(-2 * Real.pi * (y * t)) * Complex.I)
        • psi τ B P (2 * Real.pi * y) := by
    have h := MeasureTheory.Measure.integral_comp_mul_left
      (g := fun ν : ℝ => Complex.exp (↑(-2 * Real.pi * (ν * t)) * Complex.I)
        • psi τ B P (2 * Real.pi * ν)) ((2 * Real.pi)⁻¹)
    rwa [inv_inv, abs_of_pos (show (0 : ℝ) < 2 * Real.pi by positivity)] at h
  have hB' : (∫ y : ℝ, Complex.exp (↑(-2 * Real.pi * (y * t)) * Complex.I)
        • psi τ B P (2 * Real.pi * y))
      = ((2 * Real.pi)⁻¹ : ℝ) • ∫ x : ℝ,
          (fun ν : ℝ => Complex.exp (↑(-2 * Real.pi * (ν * t)) * Complex.I)
            • psi τ B P (2 * Real.pi * ν)) ((2 * Real.pi)⁻¹ * x) := by
    rw [hscale, smul_smul, inv_mul_cancel₀ h2pi, one_smul]
  rw [Real.fourier_eq']
  simp only [Real.inner_apply]
  rw [hB', hleft, integral_eq_intervalIntegral_psi τ B hτ hB P t, kernel]

/-- **(3) M3 反演恒等式**：`∫ e^{iλt}κ(t)dt = Ψ(λ)`。

（`λ` 不能作 Lean 标识符——它是 `fun` 的记号——故参数名为 `lam`。） -/
lemma integral_exp_mul_kernel (τ B : ℝ) (hτ : 0 < τ) (hB : 0 < B) (P : Polynomial ℂ) (lam : ℝ)
    (hint : Integrable (fun t : ℝ => kernel τ B P t)) :
    ∫ t : ℝ, Complex.exp ((lam : ℂ) * Complex.I * (t : ℂ)) * kernel τ B P t
      = psi τ B P lam := by
  have h2pi : (2 * Real.pi) ≠ 0 := by positivity
  have h2lam : 2 * Real.pi * (lam / (2 * Real.pi)) = lam := by
    rw [mul_comm (2 * Real.pi) (lam / (2 * Real.pi))]
    exact div_mul_cancel₀ lam h2pi
  have hcont : Continuous (fun ν : ℝ => psi τ B P (2 * Real.pi * ν)) :=
    (contDiff_psi τ B hτ hB P).continuous.comp (by fun_prop)
  have hintΦ : Integrable (fun ν : ℝ => psi τ B P (2 * Real.pi * ν)) :=
    integrable_psi_comp τ B hτ hB P
  have hintF : Integrable (𝓕 (fun ν : ℝ => psi τ B P (2 * Real.pi * ν))) := by
    rw [← kernel_eq_fourier τ B hτ hB P]
    exact hint
  -- Fourier 反演：`𝓕⁻ (𝓕 Φ) = Φ`
  have hInv : 𝓕⁻ (𝓕 (fun ν : ℝ => psi τ B P (2 * Real.pi * ν)))
      = (fun ν : ℝ => psi τ B P (2 * Real.pi * ν)) :=
    Continuous.fourierInv_fourier_eq hcont hintΦ hintF
  have hpt := congrFun hInv (lam / (2 * Real.pi))
  rw [Real.fourierInv_eq'] at hpt
  simp only [Real.inner_apply] at hpt
  -- 把 `𝓕 Φ` 换回 `kernel`，并把 `2π·(v·(λ/2π))` 对齐成 `v·λ`
  have hgoal : (∫ t : ℝ, Complex.exp ((lam : ℂ) * Complex.I * (t : ℂ)) * kernel τ B P t)
      = ∫ v : ℝ, Complex.exp (↑(2 * Real.pi * (v * (lam / (2 * Real.pi)))) * Complex.I)
          • 𝓕 (fun ν : ℝ => psi τ B P (2 * Real.pi * ν)) v := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    have hF : 𝓕 (fun ν : ℝ => psi τ B P (2 * Real.pi * ν)) v = kernel τ B P v :=
      (congrFun (kernel_eq_fourier τ B hτ hB P) v).symm
    have h2 : 2 * Real.pi * (v * (lam / (2 * Real.pi))) = v * lam := by
      calc 2 * Real.pi * (v * (lam / (2 * Real.pi)))
          = v * (2 * Real.pi * (lam / (2 * Real.pi))) := by ring
        _ = v * lam := by rw [h2lam]
    have harg : (((2 * Real.pi * (v * (lam / (2 * Real.pi))) : ℝ)) : ℂ) * Complex.I
        = (lam : ℂ) * Complex.I * (v : ℂ) := by
      have h3 : (((2 * Real.pi * (v * (lam / (2 * Real.pi)))) : ℝ) : ℂ)
          = ((v * lam : ℝ) : ℂ) := by
        rw [h2]
      rw [h3]
      push_cast
      ring
    dsimp only
    rw [hF, harg, smul_eq_mul]
  rw [hgoal, hpt, h2lam]

end RobustZ
