import RobustZ.ExpSum
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic

/-!
# M4：逼近引理（圆上 Fourier 系数 + 围道平移界）

对 `F(θ) = e^{-iτ cos θ}`（`2π` 周期、整函数），其 Fourier 系数
`cₙ = (1/2π)∫₀^{2π} e^{-inθ}e^{-iτcos θ}dθ` 满足**围道平移界**
`|cₙ| ≤ exp(τ·sinh δ − n·δ)`（`δ > 0`, `n > 0`）：
把积分沿虚轴下移 `δ`（矩形 Cauchy 定理 + 周期性 ⇒ 两条竖边相消），
再估计模长即可。
-/

noncomputable section

open Complex

namespace RobustZ

open scoped Real

/-- `F` 的整函数版本：`z ↦ e^{-inz}e^{-iτcos z}`。 -/
def fz (τ : ℝ) (n : ℤ) (z : ℂ) : ℂ :=
  Complex.exp (-(n : ℂ) * Complex.I * z) * Complex.exp (-(τ : ℂ) * Complex.I * Complex.cos z)

/-- `2π` 周期性。 -/
lemma fz_periodic (τ : ℝ) (n : ℤ) (z : ℂ) :
    fz τ n (z + 2 * Real.pi) = fz τ n z := by
  simp only [fz, Complex.cos_add_two_pi]
  have harg : -↑n * Complex.I * (z + 2 * ↑Real.pi)
      = -↑n * Complex.I * z - ↑n * (2 * ↑Real.pi * Complex.I) := by ring
  rw [harg, Complex.exp_sub, Complex.exp_int_mul_two_pi_mul_I, div_one]

/-- `fz` 是整函数。 -/
lemma differentiable_fz (τ : ℝ) (n : ℤ) : Differentiable ℂ (fz τ n) := by
  unfold fz
  refine Differentiable.mul ?_ ?_
  · exact ((differentiable_const (c := -(n : ℂ) * Complex.I)).mul
      (differentiable_id (𝕜 := ℂ))).cexp
  · exact ((differentiable_const (c := -(τ : ℂ) * Complex.I)).mul
      (Complex.differentiable_cos)).cexp

lemma continuous_fz (τ : ℝ) (n : ℤ) : Continuous (fz τ n) :=
  (differentiable_fz τ n).continuous

/-- Fourier 系数：`cₙ = (1/2π)∫₀^{2π} e^{-inθ}e^{-iτcos θ}dθ`。 -/
def fcoef (τ : ℝ) (n : ℤ) : ℂ :=
  ((2 * Real.pi)⁻¹ : ℝ) • ∫ θ in (0 : ℝ)..(2 * Real.pi), fz τ n (θ : ℂ)

/-- 围道平移：把积分沿虚轴下移 `δ` 不改变值。 -/
lemma integral_shift (τ : ℝ) (n : ℤ) {δ : ℝ} (hδ : 0 < δ) :
    (∫ x in (0 : ℝ)..(2 * Real.pi), fz τ n ((x : ℂ) + (0 : ℂ) * Complex.I))
      = ∫ x in (0 : ℝ)..(2 * Real.pi), fz τ n ((x : ℂ) + (-δ : ℂ) * Complex.I) := by
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn (fz τ n) 0
    (Complex.mk (2 * Real.pi) (-δ)) (differentiable_fz τ n).differentiableOn
  dsimp only at h
  simp only [Complex.zero_re, Complex.zero_im, Complex.ofReal_zero, Complex.ofReal_neg,
    Complex.ofReal_ofNat, mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add, sub_zero,
    zero_sub, neg_zero, neg_mul] at h
  have hvert : (∫ y in (0 : ℝ)..(-δ), fz τ n (((2 * Real.pi : ℝ) : ℂ) + (y : ℂ) * Complex.I))
      = ∫ y in (0 : ℝ)..(-δ), fz τ n ((0 : ℂ) + (y : ℂ) * Complex.I) := by
    refine intervalIntegral.integral_congr fun y _ => ?_
    have hper := fz_periodic τ n ((y : ℂ) * Complex.I)
    rw [add_comm] at hper
    simpa using hper
  rw [hvert] at h
  have h2 : (∫ x in (0 : ℝ)..(2 * Real.pi), fz τ n ((x : ℂ) + (0 : ℂ) * Complex.I))
      - (∫ x in (0 : ℝ)..(2 * Real.pi), fz τ n ((x : ℂ) + (-δ : ℂ) * Complex.I)) = 0 := by
    have h3 : (∫ x in (0 : ℝ)..(2 * Real.pi), fz τ n ((x : ℂ) + (0 : ℂ) * Complex.I))
          - (∫ x in (0 : ℝ)..(2 * Real.pi), fz τ n ((x : ℂ) + (-δ : ℂ) * Complex.I))
          + Complex.I • (∫ y in (0 : ℝ)..(-δ), fz τ n ((0 : ℂ) + (y : ℂ) * Complex.I))
        = 0 + Complex.I • (∫ y in (0 : ℝ)..(-δ), fz τ n ((0 : ℂ) + (y : ℂ) * Complex.I)) := by
      simpa using sub_eq_zero.mp h
    exact add_right_cancel h3
  exact sub_eq_zero.mp h2

/-- 平移后单点模长：`‖fz τ n (θ − δI)‖ = exp(τ·sinθ·sinhδ − nδ)`。 -/
lemma norm_fz_shift (τ : ℝ) (n : ℤ) (θ δ : ℝ) :
    ‖fz τ n ((θ : ℂ) - (δ : ℂ) * Complex.I)‖
      = Real.exp (τ * Real.sin θ * Real.sinh δ - n * δ) := by
  have hz : (θ : ℂ) - (δ : ℂ) * Complex.I = (θ : ℂ) + ((-δ : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  have hcos : Complex.cos ((θ : ℂ) + ((-δ : ℝ) : ℂ) * Complex.I)
      = Complex.cos (θ : ℂ) * Complex.cosh ((-δ : ℝ) : ℂ)
        - Complex.sin (θ : ℂ) * Complex.sinh ((-δ : ℝ) : ℂ) * Complex.I :=
    Complex.cos_add_mul_I _ _
  have hn : (n : ℂ) = ((n : ℝ) : ℂ) := by norm_num
  have h1 : (-(n : ℂ) * Complex.I * ((θ : ℂ) + ((-δ : ℝ) : ℂ) * Complex.I)).re
      = -(n : ℝ) * δ := by
    rw [hn]
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_I_re, Complex.mul_I_im, Complex.I_re, Complex.I_im,
      Complex.neg_re, Complex.neg_im, mul_zero, zero_mul, add_zero, sub_zero, neg_zero]
    push_cast
    ring
  have h2 : (-(τ : ℂ) * Complex.I * Complex.cos ((θ : ℂ) + ((-δ : ℝ) : ℂ) * Complex.I)).re
      = τ * Real.sin θ * Real.sinh δ := by
    rw [hcos]
    simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_I_re, Complex.mul_I_im,
      Complex.I_re, Complex.I_im, Complex.cos_ofReal_re, Complex.cos_ofReal_im,
      Complex.sin_ofReal_re, Complex.sin_ofReal_im, Complex.cosh_ofReal_re, Complex.cosh_ofReal_im,
      Complex.sinh_ofReal_re, Complex.sinh_ofReal_im, Complex.ofReal_neg, Complex.cosh_neg,
      Complex.sinh_neg, Complex.neg_re, Complex.neg_im, mul_zero, zero_mul, add_zero, sub_zero,
      neg_zero, mul_one, one_mul]
    push_cast
    ring
  rw [fz, hz, norm_mul, Complex.norm_exp, Complex.norm_exp, ← Real.exp_add]
  congr 1
  rw [h1, h2]
  ring

/-- **围道平移界**：`|cₙ| ≤ exp(τ·sinh δ − n·δ)`（`δ > 0`, `n > 0`）。 -/
theorem fcoef_bound (τ : ℝ) (hτ : 0 ≤ τ) {δ : ℝ} (hδ : 0 < δ) (n : ℤ) (hn : 0 < n) :
    ‖fcoef τ n‖ ≤ Real.exp (τ * Real.sinh δ - n * δ) := by
  have hscal : ‖((2 * Real.pi)⁻¹ : ℝ)‖ = (2 * Real.pi)⁻¹ :=
    Real.norm_of_nonneg (by positivity)
  rw [fcoef, norm_smul, hscal]
  have hshift := integral_shift (τ := τ) (n := n) hδ
  have hnorm : ‖∫ θ in (0 : ℝ)..(2 * Real.pi),
      fz τ n ((θ : ℂ) + (-δ : ℂ) * Complex.I)‖
      ≤ 2 * Real.pi * Real.exp (τ * Real.sinh δ - n * δ) := by
    have hle : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
        ‖fz τ n ((θ : ℂ) + (-δ : ℂ) * Complex.I)‖
        ≤ Real.exp (τ * Real.sinh δ - n * δ) := by
      intro θ _
      rw [show (θ : ℂ) + (-δ : ℂ) * Complex.I = (θ : ℂ) - (δ : ℂ) * Complex.I by ring,
        norm_fz_shift]
      refine Real.exp_le_exp.mpr ?_
      have hsinh : 0 ≤ Real.sinh δ := le_of_lt ((Real.sinh_pos_iff (x := δ)).mpr hδ)
      have h1 : τ * Real.sin θ ≤ τ * 1 := mul_le_mul_of_nonneg_left (Real.sin_le_one θ) hτ
      have h2 : τ * Real.sin θ * Real.sinh δ ≤ τ * 1 * Real.sinh δ :=
        mul_le_mul_of_nonneg_right h1 hsinh
      linarith
    calc ‖∫ θ in (0 : ℝ)..(2 * Real.pi), fz τ n ((θ : ℂ) + (-δ : ℂ) * Complex.I)‖
        ≤ ∫ θ in (0 : ℝ)..(2 * Real.pi), ‖fz τ n ((θ : ℂ) + (-δ : ℂ) * Complex.I)‖ :=
          intervalIntegral.norm_integral_le_integral_norm (by positivity)
      _ ≤ ∫ θ in (0 : ℝ)..(2 * Real.pi), Real.exp (τ * Real.sinh δ - n * δ) :=
          intervalIntegral.integral_mono_on (by positivity)
            (((continuous_fz τ n).comp (by fun_prop :
              Continuous fun θ : ℝ => (θ : ℂ) + (-δ : ℂ) * Complex.I)).norm.intervalIntegrable
              _ _) intervalIntegrable_const hle
      _ = 2 * Real.pi * Real.exp (τ * Real.sinh δ - n * δ) := by
          rw [intervalIntegral.integral_const]
          ring
  have h1 : ‖∫ θ in (0 : ℝ)..(2 * Real.pi), fz τ n (θ : ℂ)‖
      = ‖∫ θ in (0 : ℝ)..(2 * Real.pi), fz τ n ((θ : ℂ) + (0 : ℂ) * Complex.I)‖ := by
    congr 2 with θ
    simp
  rw [h1, hshift]
  have hpos : (0:ℝ) < 2 * Real.pi := by positivity
  calc (2 * Real.pi)⁻¹ * ‖∫ θ in (0 : ℝ)..(2 * Real.pi),
        fz τ n ((θ : ℂ) + (-δ : ℂ) * Complex.I)‖
      ≤ (2 * Real.pi)⁻¹ * (2 * Real.pi * Real.exp (τ * Real.sinh δ - n * δ)) := by
        exact mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = Real.exp (τ * Real.sinh δ - n * δ) := by
        field_simp


instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- `F(θ) = e^{-iτcos θ}` 提升到圆 `AddCircle (2π)`。 -/
def Fcirc (τ : ℝ) (x : AddCircle (2 * Real.pi)) : ℂ :=
  AddCircle.liftIoc (2 * Real.pi) 0
    (fun θ => Complex.exp (-(τ : ℂ) * Complex.I * Complex.cos θ)) x

/-- 圆上 Fourier 系数就是 `fcoef`。 -/
lemma fourierCoeff_Fcirc (τ : ℝ) (n : ℤ) : fourierCoeff (Fcirc τ) n = fcoef τ n := by
  have hF : Fcirc τ = fun x => AddCircle.liftIoc (2 * Real.pi) 0
      (fun θ => Complex.exp (-(τ : ℂ) * Complex.I * Complex.cos θ)) x := rfl
  rw [hF, fourierCoeff_liftIoc_eq, fourierCoeffOn_eq_integral, sub_zero, zero_add, fcoef]
  congr 1
  · rw [one_div]
  · refine intervalIntegral.integral_congr fun x _ => ?_
    have hexp : 2 * (Real.pi : ℂ) * Complex.I * ↑(-n) * (x : ℂ) / ↑(2 * Real.pi)
        = -(n : ℂ) * Complex.I * (x : ℂ) := by
      have hpi : (Real.pi : ℂ) ≠ 0 := by
        simpa using Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      push_cast
      field_simp
    rw [fourier_coe_apply, hexp, fz, smul_eq_mul]

/-- 偶性：`c₋ₙ = cₙ`。 -/
lemma fcoef_neg (τ : ℝ) (n : ℤ) : fcoef τ (-n) = fcoef τ n := by
  rw [fcoef, fcoef]
  congr 1
  have h1 : (∫ θ in (0 : ℝ)..(2 * Real.pi), fz τ (-n) (θ : ℂ))
      = ∫ s in (0 : ℝ)..(2 * Real.pi), fz τ (-n) ((2 * Real.pi - s : ℝ) : ℂ) := by
    rw [intervalIntegral.integral_comp_sub_left (fun s : ℝ => fz τ (-n) (s : ℂ)) (2 * Real.pi)]
    norm_num
  rw [h1]
  refine intervalIntegral.integral_congr fun s _ => ?_
  have hcos : Complex.cos (((2 * Real.pi - s : ℝ)) : ℂ) = Complex.cos ((s : ℝ) : ℂ) := by
    rw [Complex.ofReal_sub, Complex.cos_sub, ← Complex.ofReal_cos, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin, ← Complex.ofReal_sin, Real.cos_two_pi, Real.sin_two_pi]
    push_cast
    ring
  rw [fz, fz, hcos]
  have hsplit : -↑(-n) * Complex.I * (((2 * Real.pi - s : ℝ)) : ℂ)
      = ↑n * (2 * ↑Real.pi * Complex.I) + (↑(-n) * Complex.I * (s : ℂ)) := by
    push_cast
    ring
  rw [hsplit, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul]
  have hs : ↑(-n) * Complex.I * (s : ℂ) = -↑n * Complex.I * (s : ℂ) := by
    push_cast
    ring
  rw [hs]

/-- 零频：`‖c₀‖ ≤ exp(τ sinh δ)`。 -/
lemma norm_fcoef_zero (τ : ℝ) (hτ : 0 ≤ τ) {δ : ℝ} (hδ : 0 < δ) :
    ‖fcoef τ 0‖ ≤ Real.exp (τ * Real.sinh δ) := by
  have h0 : ‖fcoef τ 0‖ ≤ 1 := by
    rw [fcoef, norm_smul, Real.norm_of_nonneg (by positivity)]
    have hnorm : ∀ θ : ℝ, ‖fz τ 0 (θ : ℂ)‖ = 1 := by
      intro θ
      rw [fz, norm_mul, Complex.norm_exp, Complex.norm_exp]
      simp only [Int.cast_zero, neg_zero, zero_mul, Complex.zero_re, Real.exp_zero, one_mul]
      have h2 : (-(τ : ℂ) * Complex.I * Complex.cos (θ : ℂ)).re = 0 := by
        simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re,
          Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.cos_ofReal_re,
          Complex.cos_ofReal_im, mul_zero, zero_mul, sub_zero, zero_sub, neg_zero]
      rw [h2, Real.exp_zero]
    have h2 : ‖∫ θ in (0 : ℝ)..(2 * Real.pi), fz τ 0 (θ : ℂ)‖ ≤ 2 * Real.pi := by
      refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := (1 : ℝ)) ?_).trans_eq ?_
      · intro θ _
        rw [hnorm θ]
      · rw [sub_zero, abs_of_pos (by positivity), one_mul]
    calc (2 * Real.pi)⁻¹ * ‖∫ θ in (0 : ℝ)..(2 * Real.pi), fz τ 0 (θ : ℂ)‖
        ≤ (2 * Real.pi)⁻¹ * (2 * Real.pi) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 1 := by field_simp
  exact h0.trans (Real.one_le_exp (mul_nonneg hτ (le_of_lt ((Real.sinh_pos_iff (x := δ)).mpr hδ))))

/-- 正频衰减。 -/
lemma norm_fcoef_pos (τ : ℝ) (hτ : 0 ≤ τ) {δ : ℝ} (hδ : 0 < δ) {n : ℤ} (hn : 0 < n) :
    ‖fcoef τ n‖ ≤ Real.exp (τ * Real.sinh δ - n * δ) :=
  fcoef_bound τ hτ hδ n hn

/-- 负频衰减（用偶性）。 -/
lemma norm_fcoef_neg (τ : ℝ) (hτ : 0 ≤ τ) {δ : ℝ} (hδ : 0 < δ) {n : ℤ} (hn : n < 0) :
    ‖fcoef τ n‖ ≤ Real.exp (τ * Real.sinh δ + n * δ) := by
  have hpos : 0 < -n := neg_pos.mpr hn
  have hb := fcoef_bound τ hτ hδ (-n) hpos
  rw [fcoef_neg] at hb
  refine hb.trans (le_of_eq ?_)
  congr 1
  push_cast
  ring

/-- 系数族可和。 -/
lemma summable_fourierCoeff_Fcirc (τ : ℝ) (hτ : 0 ≤ τ) {δ : ℝ} (hδ : 0 < δ) :
    Summable (fourierCoeff (Fcirc τ)) := by
  have hr0 : 0 ≤ Real.exp (-δ) := Real.exp_nonneg _
  have hr1 : Real.exp (-δ) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hg : Summable (fun n : ℕ => Real.exp (τ * Real.sinh δ) * Real.exp (-δ) ^ n) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hexp : ∀ n : ℕ, Real.exp (τ * Real.sinh δ) * Real.exp (-δ) ^ n
      = Real.exp (τ * Real.sinh δ - n * δ) := by
    intro n
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  refine Summable.of_nat_of_neg_add_one ?_ ?_
  · refine Summable.of_norm_bounded hg fun n => ?_
    rw [fourierCoeff_Fcirc, hexp n]
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      simpa using norm_fcoef_zero τ hτ hδ
    · refine norm_fcoef_pos τ hτ hδ (by exact_mod_cast h)
  · refine Summable.of_norm_bounded ((summable_nat_add_iff 1).mpr hg) fun n => ?_
    rw [fourierCoeff_Fcirc, hexp (n + 1)]
    refine (norm_fcoef_neg τ hτ hδ ?_).trans (le_of_eq ?_)
    · push_cast
      omega
    · congr 1
      push_cast
      ring


/-- `Fcirc` 连续。 -/
lemma continuous_Fcirc (τ : ℝ) : Continuous (Fcirc τ) := by
  have hF : Fcirc τ = AddCircle.liftIoc (2 * Real.pi) 0
      (fun θ => Complex.exp (-(τ : ℂ) * Complex.I * Complex.cos θ)) := rfl
  rw [hF]
  refine AddCircle.liftIoc_zero_continuous ?_ ?_
  · simp [Real.cos_zero, Real.cos_two_pi]
  · have h1 : Continuous fun θ : ℝ =>
        Complex.exp (-(τ : ℂ) * Complex.I * ((Real.cos θ : ℝ) : ℂ)) := by
      fun_prop
    have h2 : (fun θ : ℝ => Complex.exp (-(τ : ℂ) * Complex.I * Complex.cos (θ : ℂ)))
        = fun θ : ℝ => Complex.exp (-(τ : ℂ) * Complex.I * ((Real.cos θ : ℝ) : ℂ)) := by
      funext θ
      rw [Complex.ofReal_cos]
    rw [h2]
    exact h1.continuousOn

/-- 作为连续映射的 `Fcirc`（供 Fourier 收敛定理使用）。 -/
def Fcont (τ : ℝ) : C(AddCircle (2 * Real.pi), ℂ) where
  toFun := Fcirc τ
  continuous_toFun := continuous_Fcirc τ

lemma fourierCoeff_Fcont (τ : ℝ) (n : ℤ) : fourierCoeff (Fcont τ) n = fcoef τ n := by
  rw [show fourierCoeff (Fcont τ) n = fourierCoeff (Fcirc τ) n from rfl, fourierCoeff_Fcirc]

lemma summable_fourierCoeff_Fcont (τ : ℝ) (hτ : 0 ≤ τ) {δ : ℝ} (hδ : 0 < δ) :
    Summable (fourierCoeff (Fcont τ)) := by
  rw [show fourierCoeff (Fcont τ) = fourierCoeff (Fcirc τ) from rfl]
  exact summable_fourierCoeff_Fcirc τ hτ hδ


/-- 逐点 Fourier 展开（连续映射版）。 -/
lemma hasSum_fourier_Fcont (τ : ℝ) (hτ : 0 ≤ τ) {δ : ℝ} (hδ : 0 < δ)
    (x : AddCircle (2 * Real.pi)) :
    HasSum (fun n : ℤ => fourierCoeff (Fcont τ) n • fourier n x) (Fcont τ x) :=
  has_pointwise_sum_fourier_series_of_summable (summable_fourierCoeff_Fcont τ hτ hδ) x


/-- 圆上 `F` 在实参数 `θ ∈ (0, 2π]` 处的值。 -/
lemma Fcont_coe_of_mem (τ : ℝ) {θ : ℝ} (hθ : θ ∈ Set.Ioc 0 (2 * Real.pi)) :
    Fcont τ (θ : AddCircle (2 * Real.pi))
      = Complex.exp (-(τ : ℂ) * Complex.I * Complex.cos (θ : ℂ)) := by
  have hF : (Fcont τ : AddCircle (2 * Real.pi) → ℂ)
      = AddCircle.liftIoc (2 * Real.pi) 0
        (fun θ => Complex.exp (-(τ : ℂ) * Complex.I * Complex.cos θ)) := rfl
  rw [hF]
  exact AddCircle.liftIoc_zero_coe_apply hθ

/-- 实参数处的 Fourier 级数（`HasSum` 形式，系数换成 `fcoef`）。 -/
lemma hasSum_exp_fcoef (τ : ℝ) (hτ : 0 ≤ τ) {δ : ℝ} (hδ : 0 < δ) {θ : ℝ}
    (hθ : θ ∈ Set.Ioc 0 (2 * Real.pi)) :
    HasSum (fun n : ℤ => fcoef τ n * Complex.exp ((n : ℂ) * Complex.I * (θ : ℂ)))
      (Complex.exp (-(τ : ℂ) * Complex.I * Complex.cos (θ : ℂ))) := by
  have h := hasSum_fourier_Fcont τ hτ hδ (θ : AddCircle (2 * Real.pi))
  have hf : (fun n : ℤ => fourierCoeff (Fcont τ) n • fourier n (θ : AddCircle (2 * Real.pi)))
      = fun n : ℤ => fcoef τ n * Complex.exp ((n : ℂ) * Complex.I * (θ : ℂ)) := by
    funext n
    have hexp : 2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (θ : ℂ) / (((2 * Real.pi : ℝ)) : ℂ)
        = (n : ℂ) * Complex.I * (θ : ℂ) := by
      have hpi : (((2 * Real.pi : ℝ)) : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (by positivity : (2 * Real.pi : ℝ) ≠ 0)
      rw [div_eq_iff hpi]
      push_cast
      ring
    rw [fourierCoeff_Fcont, fourier_coe_apply, smul_eq_mul, hexp]
  rw [hf] at h
  rw [Fcont_coe_of_mem τ hθ] at h
  exact h


/-- 统一形式的系数衰减界：`‖cₙ‖ ≤ exp(τ sinh δ − |n|δ)`。 -/
lemma norm_fcoef_le (τ : ℝ) (hτ : 0 ≤ τ) {δ : ℝ} (hδ : 0 < δ) (n : ℤ) :
    ‖fcoef τ n‖ ≤ Real.exp (τ * Real.sinh δ - |((n : ℤ) : ℝ)| * δ) := by
  rcases lt_trichotomy n 0 with h | h | h
  · have hb := norm_fcoef_neg τ hτ hδ h
    refine hb.trans (le_of_eq ?_)
    congr 1
    rw [abs_of_neg (by exact_mod_cast h : ((n : ℤ) : ℝ) < 0)]
    ring
  · subst h
    simpa using norm_fcoef_zero τ hτ hδ
  · have hb := norm_fcoef_pos τ hτ hδ h
    refine hb.trans (le_of_eq ?_)
    congr 1
    rw [abs_of_pos (by exact_mod_cast h : (0 : ℝ) < ((n : ℤ) : ℝ))]

/-- 带 Fourier 因子的衰减界（因子的模为 1）。 -/
lemma norm_fcoef_mul_exp_le (τ : ℝ) (hτ : 0 ≤ τ) {δ : ℝ} (hδ : 0 < δ) (m : ℤ) (θ : ℝ) :
    ‖fcoef τ m * Complex.exp ((m : ℂ) * Complex.I * (θ : ℂ))‖
      ≤ Real.exp (τ * Real.sinh δ - |((m : ℤ) : ℝ)| * δ) := by
  rw [norm_mul, Complex.norm_exp]
  have hm : (m : ℂ) = ((m : ℝ) : ℂ) := by norm_num
  have hre : ((m : ℂ) * Complex.I * (θ : ℂ)).re = 0 := by
    rw [hm]
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
  rw [hre, Real.exp_zero, mul_one]
  exact norm_fcoef_le τ hτ hδ m


/-- 第 `n` 个 Fourier 项（`cₙe^{inθ}`）。 -/
def fterm (τ : ℝ) (θ : ℝ) (n : ℤ) : ℂ :=
  fcoef τ n * Complex.exp ((n : ℂ) * Complex.I * (θ : ℂ))

lemma norm_fterm_le (τ : ℝ) (hτ : 0 ≤ τ) {δ : ℝ} (hδ : 0 < δ) (θ : ℝ) (n : ℤ) :
    ‖fterm τ θ n‖ ≤ Real.exp (τ * Real.sinh δ) * Real.exp (-δ) ^ n.natAbs := by
  have habs : |((n : ℤ) : ℝ)| = (n.natAbs : ℝ) := by
    rcases Int.eq_nat_or_neg n with ⟨k, rfl⟩ | ⟨k, rfl⟩ <;> simp
  refine (norm_fcoef_mul_exp_le τ hτ hδ n θ).trans (le_of_eq ?_)
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  rw [habs]
  ring

/-- 尾部（`k` 之后的 ℤ 和）的界。 -/
lemma norm_tail_le (τ : ℝ) (hτ : 0 ≤ τ) {δ : ℝ} (hδ : 0 < δ) (θ : ℝ) (k : ℕ) :
    ‖∑' n : ℕ, (fterm τ θ (((n + k : ℕ)) : ℤ) + fterm τ θ (-(((n + k : ℕ)) : ℤ) - 1))‖
      ≤ 4 * Real.exp (τ * Real.sinh δ) * Real.exp (-δ) ^ k / (1 - Real.exp (-δ)) := by
  set r : ℝ := Real.exp (-δ) with hr
  have hr0 : 0 ≤ r := Real.exp_nonneg _
  have hr1 : r < 1 := by
    rw [hr, Real.exp_lt_one_iff]
    linarith
  have hden : 0 < 1 - r := by linarith
  have hterm : ∀ n : ℕ, ‖fterm τ θ (((n + k : ℕ)) : ℤ) + fterm τ θ (-(((n + k : ℕ)) : ℤ) - 1)‖
      ≤ (2 * Real.exp (τ * Real.sinh δ) * r ^ k) * r ^ n := by
    intro n
    have h1 : ‖fterm τ θ (((n + k : ℕ)) : ℤ)‖ ≤ Real.exp (τ * Real.sinh δ) * r ^ k * r ^ n := by
      refine (norm_fterm_le τ hτ hδ θ _).trans (le_of_eq ?_)
      rw [Int.natAbs_natCast, hr, pow_add,
        mul_comm (Real.exp (-δ) ^ n) (Real.exp (-δ) ^ k)]
      ring
    have h2 : ‖fterm τ θ (-(((n + k : ℕ)) : ℤ) - 1)‖
        ≤ Real.exp (τ * Real.sinh δ) * r ^ k * r ^ n := by
      have hidx2 : -(((n + k : ℕ)) : ℤ) - 1 = -(((n + k + 1 : ℕ)) : ℤ) := by push_cast; ring
      have hb := norm_fterm_le τ hτ hδ θ (-(((n + k + 1 : ℕ)) : ℤ))
      rw [Int.natAbs_neg, Int.natAbs_natCast] at hb
      rw [← hidx2] at hb
      refine hb.trans ?_
      have hle : Real.exp (-δ) ^ (n + k + 1) ≤ Real.exp (-δ) ^ (n + k) := by
        rw [pow_succ]
        nlinarith [pow_nonneg (Real.exp_nonneg (-δ)) (n + k), hr1]
      calc Real.exp (τ * Real.sinh δ) * Real.exp (-δ) ^ (n + k + 1)
          ≤ Real.exp (τ * Real.sinh δ) * Real.exp (-δ) ^ (n + k) :=
            mul_le_mul_of_nonneg_left hle (Real.exp_nonneg _)
        _ = Real.exp (τ * Real.sinh δ) * r ^ k * r ^ n := by
            rw [hr, pow_add, mul_comm (Real.exp (-δ) ^ n) (Real.exp (-δ) ^ k)]
            ring
    calc ‖fterm τ θ (((n + k : ℕ)) : ℤ) + fterm τ θ (-(((n + k : ℕ)) : ℤ) - 1)‖
        ≤ ‖fterm τ θ (((n + k : ℕ)) : ℤ)‖ + ‖fterm τ θ (-(((n + k : ℕ)) : ℤ) - 1)‖ :=
          norm_add_le _ _
      _ ≤ Real.exp (τ * Real.sinh δ) * r ^ k * r ^ n
            + Real.exp (τ * Real.sinh δ) * r ^ k * r ^ n := add_le_add h1 h2
      _ = (2 * Real.exp (τ * Real.sinh δ) * r ^ k) * r ^ n := by ring
  have hsum : Summable fun n : ℕ => (2 * Real.exp (τ * Real.sinh δ) * r ^ k) * r ^ n :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hnorm_sum : Summable fun n : ℕ =>
      ‖fterm τ θ (((n + k : ℕ)) : ℤ) + fterm τ θ (-(((n + k : ℕ)) : ℤ) - 1)‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm hsum
  refine (norm_tsum_le_tsum_norm hnorm_sum).trans ?_
  refine (Summable.tsum_le_tsum hterm hnorm_sum hsum).trans ?_
  rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1, div_eq_mul_inv]
  have hE : 0 ≤ Real.exp (τ * Real.sinh δ) := Real.exp_nonneg _
  have hrk : 0 ≤ r ^ k := pow_nonneg hr0 k
  have hinv : 0 ≤ (1 - r)⁻¹ := inv_nonneg.mpr (le_of_lt hden)
  nlinarith [mul_nonneg (mul_nonneg hE hrk) hinv]


/-- 级数拆分：`L = 有限部分 + 尾部`（有限部分含频率 `{0..k-1} ∪ {-1..-k}`）。 -/
lemma exp_eq_sum_add_tail (τ : ℝ) (hτ : 0 ≤ τ) {δ : ℝ} (hδ : 0 < δ) {θ : ℝ}
    (hθ : θ ∈ Set.Ioc 0 (2 * Real.pi)) (k : ℕ) :
    Complex.exp (-(τ : ℂ) * Complex.I * Complex.cos (θ : ℂ))
      = (∑ n ∈ Finset.range k, (fterm τ θ (n : ℤ) + fterm τ θ (-(n : ℤ) - 1)))
        + ∑' n : ℕ, (fterm τ θ (((n + k : ℕ)) : ℤ) + fterm τ θ (-(((n + k : ℕ)) : ℤ) - 1)) := by
  have h := hasSum_exp_fcoef τ hτ hδ hθ
  have hs : Summable (fun n : ℤ => fterm τ θ n) := h.summable
  have hs_nat : Summable (fun n : ℕ => fterm τ θ (n : ℤ)) :=
    hs.comp_injective (fun a b hab => Nat.cast_injective hab)
  have hs_neg : Summable (fun n : ℕ => fterm τ θ (-(n : ℤ) - 1)) :=
    hs.comp_injective (fun a b hab => by
      have h2 : -((a : ℤ)) - 1 = -((b : ℤ)) - 1 := hab
      omega)
  have hg : Summable (fun n : ℕ => (fterm τ θ (n : ℤ) + fterm τ θ (-(n : ℤ) - 1))) :=
    hs_nat.add hs_neg
  have h1 : ∑' n : ℕ, (fterm τ θ (n : ℤ) + fterm τ θ (-(n : ℤ) - 1)) = ∑' n : ℤ, fterm τ θ n := by
    rw [← tsum_nat_add_neg_add_one hs]
    refine tsum_congr fun n => ?_
    congr 1
    push_cast
    ring
  have h2 : (∑ n ∈ Finset.range k, (fterm τ θ (n : ℤ) + fterm τ θ (-(n : ℤ) - 1)))
      + ∑' n : ℕ, (fterm τ θ (((n + k : ℕ)) : ℤ) + fterm τ θ (-(((n + k : ℕ)) : ℤ) - 1))
      = ∑' n : ℕ, (fterm τ θ (n : ℤ) + fterm τ θ (-(n : ℤ) - 1)) := by
    exact hg.sum_add_tsum_nat_add k
  have hbridge : (∑' n : ℤ, fcoef τ n * Complex.exp ((n : ℂ) * Complex.I * (θ : ℂ)))
      = ∑' n : ℤ, fterm τ θ n := tsum_congr fun n => rfl
  rw [← h.tsum_eq, hbridge, ← h1, ← h2]


/-- 逼近多项式 `P(u) = c₀ + Σ_{m=1}^{k-1} 2cₘTₘ(u)`（`Chebyshev.T`）。 -/
noncomputable def approxPoly (τ : ℝ) (k : ℕ) : Polynomial ℂ :=
  Polynomial.C (fcoef τ 0)
    + ∑ m ∈ Finset.range (k - 1), Polynomial.C (2 * fcoef τ ((m : ℤ) + 1))
        * Polynomial.Chebyshev.T ℂ ((m : ℤ) + 1)

/-- 多项式在 `cos θ` 处的值。 -/
lemma approxPoly_eval (τ : ℝ) (k : ℕ) (θ : ℝ) :
    (approxPoly τ k).eval ((Real.cos θ : ℝ) : ℂ)
      = fcoef τ 0 + ∑ m ∈ Finset.range (k - 1),
          2 * fcoef τ ((m : ℤ) + 1) * ((Real.cos (((m : ℤ) + 1) * θ) : ℝ) : ℂ) := by
  rw [approxPoly, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_finsetSum]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C]
  congr 1
  have hcos : ((Real.cos θ : ℝ) : ℂ) = Complex.cos (θ : ℂ) := Complex.ofReal_cos θ
  rw [hcos, Polynomial.Chebyshev.T_complex_cos]
  have harg : (((m : ℤ) + 1 : ℤ) : ℂ) * (θ : ℂ) = (((((m : ℤ) + 1) * θ : ℝ)) : ℂ) := by
    push_cast
    ring
  rw [harg, Complex.ofReal_cos]


/-- `e^{ix} + e^{-ix} = 2cos x`。 -/
lemma exp_add_exp_neg_mul_I (x : ℝ) :
    Complex.exp ((x : ℂ) * Complex.I) + Complex.exp (-(x : ℂ) * Complex.I)
      = 2 * ((Real.cos x : ℝ) : ℂ) := by
  have h1 : Complex.exp ((x : ℂ) * Complex.I)
      = ((Real.cos x : ℝ) : ℂ) + ((Real.sin x : ℝ) : ℂ) * Complex.I := by
    rw [← Complex.cos_add_sin_I (x : ℂ), Complex.ofReal_cos, Complex.ofReal_sin]
  have h2 : Complex.exp (-(x : ℂ) * Complex.I)
      = ((Real.cos x : ℝ) : ℂ) - ((Real.sin x : ℝ) : ℂ) * Complex.I := by
    rw [← Complex.cos_sub_sin_I (x : ℂ), Complex.ofReal_cos, Complex.ofReal_sin]
  rw [h1, h2]
  ring

/-- `∑_{n<k} f n = f 0 + ∑_{m<k-1} f (m+1)`（`k ≥ 1`）。 -/
lemma sum_range_split {M : Type*} [AddCommMonoid M] (f : ℕ → M) {k : ℕ} (hk : 1 ≤ k) :
    ∑ n ∈ Finset.range k, f n = f 0 + ∑ m ∈ Finset.range (k - 1), f (m + 1) := by
  nth_rewrite 1 [← Nat.succ_pred_eq_of_pos hk]
  rw [Finset.sum_range_succ']
  exact add_comm _ _

/-- `∑_{n<k} f n = (∑_{m<k-1} f m) + f (k-1)`（`k ≥ 1`）。 -/
lemma sum_range_split_last {M : Type*} [AddCommMonoid M] (f : ℕ → M) {k : ℕ} (hk : 1 ≤ k) :
    ∑ n ∈ Finset.range k, f n = (∑ m ∈ Finset.range (k - 1), f m) + f (k - 1) := by
  nth_rewrite 1 [← Nat.succ_pred_eq_of_pos hk]
  rw [Finset.sum_range_succ]
  simp [Nat.pred_eq_sub_one]

/-- 有限部分 = 多项式 `+` 残余单项。 -/
lemma sum_fterm_eq_approxPoly (τ : ℝ) {k : ℕ} (hk : 1 ≤ k) (θ : ℝ) :
    ∑ n ∈ Finset.range k, (fterm τ θ (n : ℤ) + fterm τ θ (-(n : ℤ) - 1))
      = (approxPoly τ k).eval ((Real.cos θ : ℝ) : ℂ)
        + fcoef τ (k : ℤ) * Complex.exp (-((k : ℤ) : ℂ) * Complex.I * (θ : ℂ)) := by
  have hA : ∑ n ∈ Finset.range k, fterm τ θ (n : ℤ)
      = fcoef τ 0 + ∑ m ∈ Finset.range (k - 1),
          fcoef τ ((m : ℤ) + 1) * Complex.exp ((((m : ℤ) + 1 : ℤ)) * Complex.I * (θ : ℂ)) := by
    rw [sum_range_split (fun n : ℕ => fterm τ θ (n : ℤ)) hk]
    have h0 : fterm τ θ (((0 : ℕ)) : ℤ) = fcoef τ 0 := by simp [fterm]
    have hs : ∀ m : ℕ, fterm τ θ (((m + 1 : ℕ)) : ℤ)
        = fcoef τ ((m : ℤ) + 1) * Complex.exp ((((m : ℤ) + 1 : ℤ)) * Complex.I * (θ : ℂ)) := by
      intro m
      rw [fterm, show (((m + 1 : ℕ)) : ℤ) = (m : ℤ) + 1 by push_cast; ring]
    rw [h0, Finset.sum_congr rfl fun m _ => hs m]
  have hB : ∑ n ∈ Finset.range k, fterm τ θ (-(n : ℤ) - 1)
      = (∑ m ∈ Finset.range (k - 1),
          fcoef τ ((m : ℤ) + 1) * Complex.exp (-(((m : ℤ) + 1 : ℤ)) * Complex.I * (θ : ℂ)))
        + fcoef τ (k : ℤ) * Complex.exp (-((k : ℤ) : ℂ) * Complex.I * (θ : ℂ)) := by
    have hstep : ∀ n : ℕ, fterm τ θ (-(n : ℤ) - 1)
        = fcoef τ ((n : ℤ) + 1) * Complex.exp (-(((n : ℤ) + 1 : ℤ)) * Complex.I * (θ : ℂ)) := by
      intro n
      rw [fterm, show -(n : ℤ) - 1 = -((n : ℤ) + 1) by ring, fcoef_neg]
      congr 1
      push_cast
      ring
    rw [Finset.sum_congr rfl fun n _ => hstep n]
    rw [sum_range_split_last (fun n : ℕ => fcoef τ ((n : ℤ) + 1)
      * Complex.exp (-(((n : ℤ) + 1 : ℤ)) * Complex.I * (θ : ℂ))) hk]
    congr 1
    rw [show (((k - 1 : ℕ)) : ℤ) + 1 = (k : ℤ) by push_cast; omega]
  rw [Finset.sum_add_distrib, hA, hB, approxPoly_eval]
  have hpair : (∑ m ∈ Finset.range (k - 1), fcoef τ ((m : ℤ) + 1)
        * Complex.exp ((((m : ℤ) + 1 : ℤ)) * Complex.I * (θ : ℂ)))
      + (∑ m ∈ Finset.range (k - 1), fcoef τ ((m : ℤ) + 1)
        * Complex.exp (-(((m : ℤ) + 1 : ℤ)) * Complex.I * (θ : ℂ)))
      = ∑ m ∈ Finset.range (k - 1), 2 * fcoef τ ((m : ℤ) + 1)
        * ((Real.cos (((m : ℤ) + 1) * θ) : ℝ) : ℂ) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    have hstep2 : Complex.exp ((((m : ℤ) + 1 : ℤ) : ℂ) * Complex.I * (θ : ℂ))
          + Complex.exp (-(((m : ℤ) + 1 : ℤ) : ℂ) * Complex.I * (θ : ℂ))
        = 2 * ((Real.cos (((m : ℤ) + 1) * θ) : ℝ) : ℂ) := by
      have h1 : (((m : ℤ) + 1 : ℤ) : ℂ) * Complex.I * (θ : ℂ)
          = (((((m : ℤ) + 1) * θ : ℝ)) : ℂ) * Complex.I := by push_cast; ring
      have h2 : -(((m : ℤ) + 1 : ℤ) : ℂ) * Complex.I * (θ : ℂ)
          = -(((((m : ℤ) + 1) * θ : ℝ)) : ℂ) * Complex.I := by push_cast; ring
      rw [h1, h2, exp_add_exp_neg_mul_I]
    rw [← mul_add, hstep2]
    ring
  linear_combination hpair

/-- **逼近误差界**：`‖e^{-iτcos θ} − P(cos θ)‖ ≤ |c_k| + 4e^{τ sinh δ}e^{-δk}/(1−e^{−δ})`。 -/
lemma exp_sub_approxPoly_le (τ : ℝ) (hτ : 0 ≤ τ) {δ : ℝ} (hδ : 0 < δ) {θ : ℝ}
    (hθ : θ ∈ Set.Ioc 0 (2 * Real.pi)) {k : ℕ} (hk : 1 ≤ k) :
    ‖Complex.exp (-(τ : ℂ) * Complex.I * Complex.cos (θ : ℂ))
        - (approxPoly τ k).eval ((Real.cos θ : ℝ) : ℂ)‖
      ≤ ‖fcoef τ (k : ℤ)‖
        + 4 * Real.exp (τ * Real.sinh δ) * Real.exp (-δ) ^ k / (1 - Real.exp (-δ)) := by
  set T : ℂ := ∑' n : ℕ, (fterm τ θ (((n + k : ℕ)) : ℤ) + fterm τ θ (-(((n + k : ℕ)) : ℤ) - 1))
    with hT
  have htail : ‖T‖ ≤ 4 * Real.exp (τ * Real.sinh δ) * Real.exp (-δ) ^ k / (1 - Real.exp (-δ)) :=
    norm_tail_le τ hτ hδ θ k
  rw [exp_eq_sum_add_tail τ hτ hδ hθ k, sum_fterm_eq_approxPoly τ hk θ]
  have hkey : (approxPoly τ k).eval ((Real.cos θ : ℝ) : ℂ)
        + fcoef τ (k : ℤ) * Complex.exp (-((k : ℤ) : ℂ) * Complex.I * (θ : ℂ)) + T
        - (approxPoly τ k).eval ((Real.cos θ : ℝ) : ℂ)
      = fcoef τ (k : ℤ) * Complex.exp (-((k : ℤ) : ℂ) * Complex.I * (θ : ℂ)) + T := by ring
  rw [hkey]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_exp]
  have hkcast : ((k : ℤ) : ℂ) = ((k : ℝ) : ℂ) := by norm_num
  have hexp1 : (-((k : ℤ) : ℂ) * Complex.I * (θ : ℂ)).re = 0 := by
    rw [hkcast]
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.neg_re, Complex.neg_im, mul_zero, zero_mul, sub_zero, add_zero,
      neg_zero]
  rw [hexp1, Real.exp_zero, mul_one]
  linarith [htail]


end RobustZ
