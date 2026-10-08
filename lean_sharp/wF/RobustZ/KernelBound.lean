import RobustZ.Smearing

/-!
# M3：两次分部积分 ⇒ 核的点态衰减界

对 `κ(t) = (2π)⁻¹∫ Ψ(μ)e^{−iμt}dμ`（`Ψ` 紧支光滑）用两次分部积分（每次把一个
`e^{−iμt}` 的导数转成因子 `it`，边界项因 `Ψ` 在 `±(τ+B+1)` 附近恒为零而消失）：

`∫ Ψ e^{−iμt} = (it)⁻² ∫ Ψ'' e^{−iμt}`，

取模并逐点估计 `|e^{−iμt}| = 1` 即得 `‖κ(t)‖ ≤ (2πt²)⁻¹∫‖Ψ''‖`。
-/


noncomputable section

namespace RobustZ

open scoped Real
open Filter MeasureTheory

/-- `μ ↦ 1 − P(μ)e^{iμ}` 光滑。 -/
lemma contDiff_psiA (P : Polynomial ℂ) : ContDiff ℝ 2 (psiA P) := by
  have hpoly : ContDiff ℝ 2 (fun z : ℂ => P.eval z) := by
    induction P using Polynomial.induction_on' with
    | add p q hp hq => simpa only [Polynomial.eval_add] using hp.add hq
    | monomial n a =>
      have h : (fun z : ℂ => (Polynomial.monomial n a).eval z) = fun z : ℂ => a * z ^ n := by
        funext z
        rw [Polynomial.eval_monomial]
      rw [h]
      exact contDiff_const.mul ((contDiff_id : ContDiff ℝ 2 (id : ℂ → ℂ)).pow n)
  have h1 : ContDiff ℝ 2 (fun μ : ℝ => P.eval ((μ : ℂ))) := by
    have h := hpoly.comp (Complex.ofRealCLM.contDiff)
    simpa only [Function.comp_def, id_eq, Complex.ofRealCLM_apply] using h
  have h2 : ContDiff ℝ 2 (fun μ : ℝ => Complex.exp ((μ : ℂ) * Complex.I)) := by
    have h3 : ContDiff ℝ 2 (fun z : ℂ => z * Complex.I) :=
      (contDiff_id : ContDiff ℝ 2 (id : ℂ → ℂ)).mul contDiff_const
    have h4 : ContDiff ℝ 2 (fun μ : ℝ => (μ : ℂ) * Complex.I) := by
      have h := h3.comp (Complex.ofRealCLM.contDiff)
      simpa only [Function.comp_def, id_eq, Complex.ofRealCLM_apply] using h
    have h5 := Complex.contDiff_exp.comp h4
    simpa only [Function.comp_def] using h5
  have h6 : ContDiff ℝ 2 (fun μ : ℝ => (1 : ℂ) - P.eval ((μ : ℂ)) * Complex.exp ((μ : ℂ) * Complex.I)) :=
    contDiff_const.sub (h1.mul h2)
  change ContDiff ℝ 2 (fun μ : ℝ => 1 - P.eval ((μ : ℂ)) * Complex.exp ((μ : ℂ) * Complex.I))
  exact h6

/-- `Ψ = (1 − Pe^{iμ})·χ` 是 `C²` 的。 -/
lemma contDiff_psi (τ B : ℝ) (hτ : 0 < τ) (hB : 0 < B) (P : Polynomial ℂ) :
    ContDiff ℝ 2 (psi τ B P) := by
  have h1 : ContDiff ℝ 2 (fun μ : ℝ => ((cutoff τ B μ : ℝ) : ℂ)) := by
    have h := (Complex.ofRealCLM.contDiff).comp (contDiff_cutoff τ B hτ hB)
    simpa only [Function.comp_def, Complex.ofRealCLM_apply] using h
  have h2 := (contDiff_psiA P).mul h1
  change ContDiff ℝ 2 (fun μ : ℝ => psiA P μ * ((cutoff τ B μ : ℝ) : ℂ))
  exact h2

/-- 分部积分（指数权）：`f` 在 `±A` 处为 `0` 时，
`∫_{-A}^{A} f'(μ)e^{-iμt}dμ = it·∫_{-A}^{A} f(μ)e^{-iμt}dμ`。 -/
lemma integral_deriv_mul_exp_eq (f : ℝ → ℂ) (A t : ℝ) (hf : Differentiable ℝ f)
    (hf' : Continuous (deriv f)) (hA : f A = 0) (hA' : f (-A) = 0) :
    ∫ μ in -A..A, deriv f μ * Complex.exp (-((μ : ℂ) * Complex.I * (t : ℂ)))
      = ((t : ℂ) * Complex.I) *
        ∫ μ in -A..A, f μ * Complex.exp (-((μ : ℂ) * Complex.I * (t : ℂ))) := by
  have he_cont : Continuous fun μ : ℝ => Complex.exp (-((μ : ℂ) * Complex.I * (t : ℂ))) := by
    refine Complex.continuous_exp.comp ?_
    fun_prop
  have he_hd : ∀ μ : ℝ, HasDerivAt (fun ν : ℝ => Complex.exp (-((ν : ℂ) * Complex.I * (t : ℂ))))
      (Complex.exp (-((μ : ℂ) * Complex.I * (t : ℂ))) * (-(Complex.I * (t : ℂ)))) μ := by
    intro μ
    have h1 : HasDerivAt (fun ν : ℝ => (ν : ℂ) * Complex.I * (t : ℂ)) (Complex.I * (t : ℂ)) μ := by
      have h0 : HasDerivAt (fun ν : ℝ => (ν : ℂ)) (1 : ℂ) μ := by
        simpa using HasDerivAt.ofReal_comp (hasDerivAt_id μ)
      simpa only [mul_assoc, one_mul] using h0.mul_const (Complex.I * (t : ℂ))
    exact h1.neg.cexp
  have he_deriv : ∀ μ : ℝ, deriv (fun ν : ℝ => Complex.exp (-((ν : ℂ) * Complex.I * (t : ℂ)))) μ
      = -((t : ℂ) * Complex.I) * Complex.exp (-((μ : ℂ) * Complex.I * (t : ℂ))) := by
    intro μ
    rw [(he_hd μ).deriv]
    ring
  have hhd : ∀ x ∈ Set.uIcc (-A) A, HasDerivAt (fun μ : ℝ => f μ * Complex.exp (-((μ : ℂ) * Complex.I * (t : ℂ))))
      (deriv f x * Complex.exp (-((x : ℂ) * Complex.I * (t : ℂ)))
        + f x * deriv (fun ν : ℝ => Complex.exp (-((ν : ℂ) * Complex.I * (t : ℂ)))) x) x :=
    fun x _ => (hf.differentiableAt.hasDerivAt).mul ((he_hd x).differentiableAt.hasDerivAt)
  have hint1 : IntervalIntegrable
      (fun x : ℝ => deriv f x * Complex.exp (-((x : ℂ) * Complex.I * (t : ℂ)))) volume (-A) A :=
    (hf'.mul he_cont).intervalIntegrable _ _
  have hint2 : IntervalIntegrable
      (fun x : ℝ => f x * deriv (fun ν : ℝ => Complex.exp (-((ν : ℂ) * Complex.I * (t : ℂ)))) x)
      volume (-A) A := by
    have hde : deriv (fun ν : ℝ => Complex.exp (-((ν : ℂ) * Complex.I * (t : ℂ))))
        = fun x : ℝ => -((t : ℂ) * Complex.I) * Complex.exp (-((x : ℂ) * Complex.I * (t : ℂ))) :=
      funext he_deriv
    have hcont : Continuous fun x : ℝ =>
        -((t : ℂ) * Complex.I) * Complex.exp (-((x : ℂ) * Complex.I * (t : ℂ))) :=
      (continuous_const (y := -((t : ℂ) * Complex.I))).mul he_cont
    rw [hde]
    exact (hf.continuous.mul hcont).intervalIntegrable (-A) A (μ := volume)
  have hFT := intervalIntegral.integral_eq_sub_of_hasDerivAt hhd (hint1.add hint2)
  rw [hA, hA', zero_mul, zero_mul, sub_zero] at hFT
  have hsplit : ∫ x in -A..A, (deriv f x * Complex.exp (-((x : ℂ) * Complex.I * (t : ℂ)))
        + f x * deriv (fun ν : ℝ => Complex.exp (-((ν : ℂ) * Complex.I * (t : ℂ)))) x)
      = (∫ x in -A..A, deriv f x * Complex.exp (-((x : ℂ) * Complex.I * (t : ℂ))))
        + ∫ x in -A..A, f x * deriv (fun ν : ℝ => Complex.exp (-((ν : ℂ) * Complex.I * (t : ℂ)))) x :=
    intervalIntegral.integral_add hint1 hint2
  rw [hsplit] at hFT
  have h2 : ∫ x in -A..A, f x * deriv (fun ν : ℝ => Complex.exp (-((ν : ℂ) * Complex.I * (t : ℂ)))) x
      = -((t : ℂ) * Complex.I) * ∫ x in -A..A, f x * Complex.exp (-((x : ℂ) * Complex.I * (t : ℂ))) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [he_deriv x]
    ring
  rw [h2] at hFT
  rw [neg_mul, ← sub_eq_add_neg, sub_eq_zero] at hFT
  exact hFT

/-- **两次分部积分**：核的点态衰减界 `‖κ(t)‖ ≤ (2πt²)⁻¹∫‖Ψ''‖`。 -/
lemma norm_kernel_le_deriv (τ B : ℝ) (hτ : 0 < τ) (hB : 0 < B) (P : Polynomial ℂ) {t : ℝ}
    (ht : t ≠ 0) :
    ‖kernel τ B P t‖ ≤ ((2 * Real.pi * t ^ 2)⁻¹) *
      ∫ μ in (-(τ + B + 1))..(τ + B + 1), ‖deriv (deriv (psi τ B P)) μ‖ := by
  set A : ℝ := τ + B + 1 with hA
  have hApos : 0 < A := by rw [hA]; linarith
  have hAlt : τ + B < A := by rw [hA]; linarith
  set k : ℂ := ((t : ℂ) * Complex.I)⁻¹ with hk
  have htC : (t : ℂ) ≠ 0 := fun h => ht (Complex.ofReal_injective (by simpa using h))
  have hc_ne : ((t : ℂ) * Complex.I) ≠ 0 := mul_ne_zero htC Complex.I_ne_zero
  -- smoothness of `Ψ`
  have hΨ : ContDiff ℝ 2 (psi τ B P) := contDiff_psi τ B hτ hB P
  have hdΨ : Differentiable ℝ (psi τ B P) := hΨ.differentiable (by norm_num)
  have hd1 : Differentiable ℝ (deriv (psi τ B P)) := hΨ.differentiable_deriv_two
  have hc1 : Continuous (deriv (psi τ B P)) := hΨ.continuous_deriv (by norm_num)
  have hc2 : Continuous (deriv (deriv (psi τ B P))) := by
    have h1 : ContDiff ℝ 1 (deriv (psi τ B P)) := by simpa using hΨ.deriv'
    exact h1.continuous_deriv (by norm_num)
  -- weight norms
  have he_norm : ∀ μ : ℝ, ‖Complex.exp (-((μ : ℂ) * Complex.I * (t : ℂ)))‖ = 1 := by
    intro μ
    rw [Complex.norm_exp]
    have hre : (-((μ : ℂ) * Complex.I * (t : ℂ))).re = 0 := by
      simp [Complex.mul_re]
    rw [hre, Real.exp_zero]
  have hnormC : ‖(t : ℂ)‖ = |t| := by
    have h2 : ‖(t : ℂ)‖ ^ 2 = t ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
      ring
    calc ‖(t : ℂ)‖ = Real.sqrt (‖(t : ℂ)‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ = Real.sqrt (t ^ 2) := by rw [h2]
      _ = |t| := Real.sqrt_sq_eq_abs t
  -- end point vanishing of `Ψ` and `Ψ'`
  have hΨA : psi τ B P A = 0 := psi_eq_zero P hB (by rw [abs_of_pos hApos]; linarith)
  have hΨA' : psi τ B P (-A) = 0 :=
    psi_eq_zero P hB (by rw [abs_neg, abs_of_pos hApos]; linarith)
  have hderiv_zero : ∀ x : ℝ, τ + B < |x| → deriv (psi τ B P) x = 0 := by
    intro x hx
    have hnb : ∀ᶠ y in nhds x, τ + B < |y| :=
      (isOpen_lt continuous_const continuous_abs).mem_nhds (by simpa using hx)
    have hev : psi τ B P =ᶠ[nhds x] fun _ => (0 : ℂ) := by
      filter_upwards [hnb] with y hy
      exact psi_eq_zero P hB hy.le
    rw [hev.deriv_eq, deriv_const]
  have hdΨA : deriv (psi τ B P) A = 0 := hderiv_zero A (by rw [abs_of_pos hApos]; exact hAlt)
  have hdΨA' : deriv (psi τ B P) (-A) = 0 :=
    hderiv_zero (-A) (by rw [abs_neg, abs_of_pos hApos]; exact hAlt)
  -- two integrations by parts
  have hIBP1 := integral_deriv_mul_exp_eq (psi τ B P) A t hdΨ hc1 hΨA hΨA'
  have hIBP2 := integral_deriv_mul_exp_eq (deriv (psi τ B P)) A t hd1 hc2 hdΨA hdΨA'
  have hB1 : ∫ μ in -A..A, deriv (psi τ B P) μ * Complex.exp (-((μ : ℂ) * Complex.I * (t : ℂ)))
      = k * ∫ μ in -A..A,
          deriv (deriv (psi τ B P)) μ * Complex.exp (-((μ : ℂ) * Complex.I * (t : ℂ))) := by
    rw [hIBP2, hk, inv_mul_cancel_left₀ hc_ne]
  have hB0 : ∫ μ in -A..A, psi τ B P μ * Complex.exp (-((μ : ℂ) * Complex.I * (t : ℂ)))
      = k * (k * ∫ μ in -A..A,
          deriv (deriv (psi τ B P)) μ * Complex.exp (-((μ : ℂ) * Complex.I * (t : ℂ)))) := by
    have h2 : ((t : ℂ) * Complex.I) * (∫ μ in -A..A,
          psi τ B P μ * Complex.exp (-((μ : ℂ) * Complex.I * (t : ℂ))))
        = k * ∫ μ in -A..A,
          deriv (deriv (psi τ B P)) μ * Complex.exp (-((μ : ℂ) * Complex.I * (t : ℂ))) := by
      rw [← hIBP1, hB1]
    calc ∫ μ in -A..A, psi τ B P μ * Complex.exp (-((μ : ℂ) * Complex.I * (t : ℂ)))
        = k * (((t : ℂ) * Complex.I) * ∫ μ in -A..A,
            psi τ B P μ * Complex.exp (-((μ : ℂ) * Complex.I * (t : ℂ)))) := by
          rw [hk, inv_mul_cancel_left₀ hc_ne]
      _ = k * (k * ∫ μ in -A..A,
            deriv (deriv (psi τ B P)) μ * Complex.exp (-((μ : ℂ) * Complex.I * (t : ℂ)))) := by
          rw [h2]
  -- norm bound
  have hk_sq : ‖k‖ ^ 2 = (t ^ 2)⁻¹ := by
    have h2 : ‖k‖ = (|t|)⁻¹ := by
      rw [hk, norm_inv, norm_mul, Complex.norm_I, mul_one, hnormC]
    rw [h2, inv_pow, sq_abs]
  have hmain : ‖∫ μ in -A..A, psi τ B P μ * Complex.exp (-((μ : ℂ) * Complex.I * (t : ℂ)))‖
      ≤ (t ^ 2)⁻¹ * ∫ μ in -A..A, ‖deriv (deriv (psi τ B P)) μ‖ := by
    rw [hB0]
    calc ‖k * (k * ∫ μ in -A..A,
          deriv (deriv (psi τ B P)) μ * Complex.exp (-((μ : ℂ) * Complex.I * (t : ℂ))))‖
        ≤ ‖k‖ * ‖k * ∫ μ in -A..A,
            deriv (deriv (psi τ B P)) μ * Complex.exp (-((μ : ℂ) * Complex.I * (t : ℂ)))‖ :=
          norm_mul_le _ _
      _ = ‖k‖ * (‖k‖ * ‖∫ μ in -A..A,
            deriv (deriv (psi τ B P)) μ * Complex.exp (-((μ : ℂ) * Complex.I * (t : ℂ)))‖) := by
          rw [norm_mul]
      _ = ‖k‖ ^ 2 * ‖∫ μ in -A..A,
            deriv (deriv (psi τ B P)) μ * Complex.exp (-((μ : ℂ) * Complex.I * (t : ℂ)))‖ := by
          ring
      _ ≤ ‖k‖ ^ 2 * ∫ μ in -A..A, ‖deriv (deriv (psi τ B P)) μ‖ := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          calc ‖∫ μ in -A..A,
                deriv (deriv (psi τ B P)) μ * Complex.exp (-((μ : ℂ) * Complex.I * (t : ℂ)))‖
              ≤ ∫ μ in -A..A,
                  ‖deriv (deriv (psi τ B P)) μ * Complex.exp (-((μ : ℂ) * Complex.I * (t : ℂ)))‖ :=
                intervalIntegral.norm_integral_le_integral_norm (by linarith)
            _ = ∫ μ in -A..A, ‖deriv (deriv (psi τ B P)) μ‖ := by
                refine intervalIntegral.integral_congr fun μ _ => ?_
                rw [norm_mul, he_norm μ, mul_one]
      _ = (t ^ 2)⁻¹ * ∫ μ in -A..A, ‖deriv (deriv (psi τ B P)) μ‖ := by rw [hk_sq]
  calc ‖kernel τ B P t‖
      = (2 * Real.pi)⁻¹ * ‖∫ μ in -A..A,
          psi τ B P μ * Complex.exp (-((μ : ℂ) * Complex.I * (t : ℂ)))‖ := by
        rw [kernel, norm_smul, Real.norm_of_nonneg (by positivity)]
    _ ≤ (2 * Real.pi)⁻¹ * ((t ^ 2)⁻¹ * ∫ μ in -A..A, ‖deriv (deriv (psi τ B P)) μ‖) :=
        mul_le_mul_of_nonneg_left hmain (by positivity)
    _ = ((2 * Real.pi * t ^ 2)⁻¹) * ∫ μ in -A..A, ‖deriv (deriv (psi τ B P)) μ‖ := by
        rw [mul_inv]
        ring

end RobustZ
