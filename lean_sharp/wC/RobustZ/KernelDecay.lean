import RobustZ.FinalSmall
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.Complex.Trigonometric

/-!
# `KernelDecay`：`FinalSmall` 缺口的定位与可证部分

（详细文档见文件末尾 §6。）
-/

noncomputable section

namespace RobustZ

open Filter MeasureTheory
open scoped Real Topology

/-! ## 1. 记号 -/

/-- `hkernel` 的核常数积（`τ = (Σθ)/2`、`ε = epsOf τ δ' (2N+1)`、`P = scaledApprox τ (2N+1)`）。 -/
noncomputable def kernelProd (δ' : ℝ) (N : ℕ) (L : ℕ) (θ : Fin L → ℝ) : ℝ :=
  kernelA ((∑ j, θ j) / 2) (Real.sqrt (epsOf ((∑ j, θ j) / 2) δ' (2 * N + 1)))
      (scaledApprox ((∑ j, θ j) / 2) (2 * N + 1))
    * kernelC ((∑ j, θ j) / 2) (Real.sqrt (epsOf ((∑ j, θ j) / 2) δ' (2 * N + 1)))
      (scaledApprox ((∑ j, θ j) / 2) (2 * N + 1))

/-- `FinalSmall.h_zero_small_of_tau_le` 里那个 `hkernel` 假设。 -/
def HKernel (φ ρ δ' : ℝ) : Prop :=
  ∀ᶠ N : ℕ in Filter.atTop, ∀ {L : ℕ} {α θ : Fin L → ℝ}, Admissible N φ L α θ →
    (∑ j, θ j) / 2 ≤ ρ * (2 * (N : ℝ) + 2) →
    kernelProd δ' N L θ ≤ ((1 - Real.cos (φ / 2)) / 8) ^ 2
      * Real.exp (-(δ' - ρ * Real.sinh δ') * (2 * (N : ℝ) + 2))

/-! ## 2. 结构定理：`hkernel` 就是主定理的核心 -/

/-- **结构定理**：`hkernel` 蕴含「最终不存在满足 `τ ≤ ρ(2N+2)` 的 admissible 构造」。

证明：若有这样的构造，`M5Apply.h_zero_le_of_admissible_twoN_add_one` 给 `h(0) ≤ 8√(C₁C₂)`，
配上 `hkernel` 得 `8√(C₁C₂) ≤ (1-cos(φ/2))·e^{-η(2N+2)/2} < 1-cos(φ/2)`，即 `h(0) < 1-cos(φ/2)`；
而 `HTraceLower.h_zero_ge` 给 `1-cos(φ/2) ≤ h(0)`。矛盾。 -/
theorem no_admissible_of_kernel_decay {φ : ℝ} (hφ0 : 0 < φ) (hφπ : φ ≤ Real.pi)
    {ρ δ' : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hδ' : 0 < δ')
    (hη : 0 < δ' - ρ * Real.sinh δ') (hk : HKernel φ ρ δ') :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ {L : ℕ} {α θ : Fin L → ℝ}, Admissible N φ L α θ →
      ¬ ((∑ j, θ j) / 2 ≤ ρ * (2 * (N : ℝ) + 2)) := by
  filter_upwards [h_zero_small_of_tau_le hφ0 hφπ hρ0 hρ1 hδ' hη hk] with N hN L α θ hAdm hτρ
  have h1 := hN hAdm hτρ
  have h2 := h_zero_ge φ hφ0.le hφπ L α θ hAdm.2.1
  linarith

/-- 反向（空真性）：若最终没有满足 `τ ≤ ρ(2N+2)` 的 admissible 构造，则 `hkernel` 自动成立。 -/
theorem hkernel_of_no_admissible {φ ρ δ' : ℝ}
    (h : ∀ᶠ N : ℕ in Filter.atTop, ∀ {L : ℕ} {α θ : Fin L → ℝ}, Admissible N φ L α θ →
      ¬ ((∑ j, θ j) / 2 ≤ ρ * (2 * (N : ℝ) + 2))) :
    HKernel φ ρ δ' := by
  filter_upwards [h] with N hN L α θ hAdm hτρ
  exact absurd hτρ (hN hAdm)

/-! ## 3. 修正版收尾：只需「`C₁·C₂ → 0`」 -/

/-- **修正版收尾**：若 `C₁·C₂ ≤ A` 且 `8√A < 1-cos(φ/2)`，则端点小性成立。 -/
lemma h_zero_lt_of_kernel_le {N : ℕ} {φ : ℝ} {L : ℕ} {α θ : Fin L → ℝ}
    (hAdm : Admissible N φ L α θ) {δ' : ℝ} (hδ' : 0 < δ')
    {A : ℝ} (hker : kernelA ((∑ j, θ j) / 2) (Real.sqrt (epsOf ((∑ j, θ j) / 2) δ' (2 * N + 1)))
          (scaledApprox ((∑ j, θ j) / 2) (2 * N + 1))
        * kernelC ((∑ j, θ j) / 2) (Real.sqrt (epsOf ((∑ j, θ j) / 2) δ' (2 * N + 1)))
          (scaledApprox ((∑ j, θ j) / 2) (2 * N + 1)) ≤ A)
    (hA : 8 * Real.sqrt A < 1 - Real.cos (φ / 2)) :
    h L α θ 0 < 1 - Real.cos (φ / 2) := by
  have h8 : 8 * Real.sqrt
      (kernelA ((∑ j, θ j) / 2) (Real.sqrt (epsOf ((∑ j, θ j) / 2) δ' (2 * N + 1)))
          (scaledApprox ((∑ j, θ j) / 2) (2 * N + 1))
        * kernelC ((∑ j, θ j) / 2) (Real.sqrt (epsOf ((∑ j, θ j) / 2) δ' (2 * N + 1)))
          (scaledApprox ((∑ j, θ j) / 2) (2 * N + 1)))
      ≤ 8 * Real.sqrt A :=
    mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hker) (by norm_num : (0 : ℝ) ≤ 8)
  exact lt_of_le_of_lt ((h_zero_le_of_admissible_twoN_add_one hAdm hδ').trans h8) hA

/-- **修正版收尾（最终形式）**：`hkernel` 的结论只需要「`C₁C₂ ≤ A N` 且 `A N → 0`」。 -/
theorem h_zero_small_of_tau_le_tendsto {φ : ℝ} (hφ0 : 0 < φ) (hφπ : φ ≤ Real.pi)
    {ρ : ℝ} (_hρ0 : 0 < ρ) (_hρ1 : ρ < 1) {δ' : ℝ} (hδ' : 0 < δ')
    {A : ℕ → ℝ} (hA0 : Tendsto A atTop (𝓝 0))
    (hkernel : ∀ᶠ N : ℕ in Filter.atTop, ∀ {L : ℕ} {α θ : Fin L → ℝ},
      Admissible N φ L α θ → (∑ j, θ j) / 2 ≤ ρ * (2 * (N : ℝ) + 2) →
      kernelA ((∑ j, θ j) / 2) (Real.sqrt (epsOf ((∑ j, θ j) / 2) δ' (2 * N + 1)))
          (scaledApprox ((∑ j, θ j) / 2) (2 * N + 1))
        * kernelC ((∑ j, θ j) / 2) (Real.sqrt (epsOf ((∑ j, θ j) / 2) δ' (2 * N + 1)))
          (scaledApprox ((∑ j, θ j) / 2) (2 * N + 1)) ≤ A N) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ {L : ℕ} {α θ : Fin L → ℝ},
      Admissible N φ L α θ → (∑ j, θ j) / 2 ≤ ρ * (2 * (N : ℝ) + 2) →
      h L α θ 0 < 1 - Real.cos (φ / 2) := by
  have hc : 0 < 1 - Real.cos (φ / 2) := one_sub_cos_half_pos hφ0 hφπ
  have hc8 : 0 < (1 - Real.cos (φ / 2)) / 8 := by linarith
  have hev : ∀ᶠ N : ℕ in Filter.atTop, A N < ((1 - Real.cos (φ / 2)) / 8) ^ 2 :=
    hA0.eventually (eventually_lt_nhds (by positivity))
  filter_upwards [hkernel, hev] with N hN hAN L α θ hAdm hτρ
  refine h_zero_lt_of_kernel_le hAdm hδ' (hN hAdm hτρ) ?_
  have hsqrt : Real.sqrt (A N) < (1 - Real.cos (φ / 2)) / 8 := by
    rw [Real.sqrt_lt' hc8]
    exact hAN
  linarith

/-- `HKernel` 蕴含 `h_zero_small_of_tau_le` 所需要的那个 `hkernel` 假设（逐字形式）。 -/
theorem hkernel_form {φ ρ δ' : ℝ} (hk : HKernel φ ρ δ') :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ {L : ℕ} {α θ : Fin L → ℝ},
      Admissible N φ L α θ → (∑ j, θ j) / 2 ≤ ρ * (2 * (N : ℝ) + 2) →
      kernelA ((∑ j, θ j) / 2) (Real.sqrt (epsOf ((∑ j, θ j) / 2) δ' (2 * N + 1)))
          (scaledApprox ((∑ j, θ j) / 2) (2 * N + 1))
        * kernelC ((∑ j, θ j) / 2) (Real.sqrt (epsOf ((∑ j, θ j) / 2) δ' (2 * N + 1)))
          (scaledApprox ((∑ j, θ j) / 2) (2 * N + 1))
        ≤ ((1 - Real.cos (φ / 2)) / 8) ^ 2
          * Real.exp (-(δ' - ρ * Real.sinh δ') * (2 * (N : ℝ) + 2)) :=
  hk

/-! ## 4. 缺口的关键砖：collar 上的 Jacobi–Anger 尾部恒等式

带内（`|μ| ≤ τ`）的逼近误差由 `Approx.exp_sub_approxPoly_le` 给出，那里 `T_m(cos θ) = cos(mθ)`，
`|T_m| ≤ 1`。**collar 上（`|μ| ≤ τ+B`）必须换成 `u = μ/τ`、`T_m(u)`**；`u ≥ 1` 时
`T_m(u) = cosh(m·arcosh u)` 指数增长，于是"无抵消"的界（`CollarBound` 那一套：`Σ|c_m||T_m|`）
必然带出多余的 `e^{τ sinh δ'}`，这也正是 `hkernel` 卡住的根源。

真正的抵消来自级数恒等式（`w > 0`）：

`e^{-iτ cosh w} = Σ_{n∈ℤ} c_n e^{-nw}`（`c_n = fcoef τ n`，Jacobi–Anger 的解析延拓）。

它**不需要**任何解析延拓：把 `integral_shift`（围道下移）反过来用（围道上移 `w`），
得到 `c_n e^{-nw}` 是移位函数 `θ ↦ e^{-iτcos(θ+iw)}` 的第 `n` 个 Fourier 系数，
再用 Mathlib 的 `has_pointwise_sum_fourier_series_of_summable` 在 `θ = 0` 处取值即可。 -/

/-- `fz` 的复平移仍是 `2π` 周期的。 -/
lemma fz_periodic_shift (τ : ℝ) (n : ℤ) (w : ℝ) (z : ℂ) :
    fz τ n (z + 2 * (Real.pi : ℂ) + (w : ℂ) * Complex.I)
      = fz τ n (z + (w : ℂ) * Complex.I) := by
  have h := fz_periodic τ n (z + (w : ℂ) * Complex.I)
  rw [show z + (w : ℂ) * Complex.I + 2 * (Real.pi : ℂ)
      = z + 2 * (Real.pi : ℂ) + (w : ℂ) * Complex.I from by ring] at h
  exact h

/-- **一般围道平移**（下移 `lam > 0`）：`2π` 周期的整函数在两条水平线上的积分相等。
（`Approx.integral_shift` 是 `F = fz τ n` 的特例。） -/
lemma integral_shift_gen (F : ℂ → ℂ) (hF : Differentiable ℂ F)
    (hper : ∀ z : ℂ, F (z + 2 * (Real.pi : ℂ)) = F z) {lam : ℝ} (_hlam : 0 < lam) :
    (∫ x in (0 : ℝ)..(2 * Real.pi), F ((x : ℂ) + (0 : ℂ) * Complex.I))
      = ∫ x in (0 : ℝ)..(2 * Real.pi), F ((x : ℂ) + (-lam : ℂ) * Complex.I) := by
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn F 0
    (Complex.mk (2 * Real.pi) (-lam)) hF.differentiableOn
  simp only [Complex.zero_re, Complex.zero_im, Complex.ofReal_zero, Complex.ofReal_neg,
    zero_mul, one_mul, zero_add, add_zero] at h
  have hvert : (∫ y in (0 : ℝ)..(-lam), F (((2 * Real.pi : ℝ) : ℂ) + (y : ℂ) * Complex.I))
      = ∫ y in (0 : ℝ)..(-lam), F ((0 : ℂ) + (y : ℂ) * Complex.I) := by
    refine intervalIntegral.integral_congr fun y _ => ?_
    rw [show ((2 * Real.pi : ℝ) : ℂ) + (y : ℂ) * Complex.I
        = (y : ℂ) * Complex.I + 2 * (Real.pi : ℂ) from by push_cast; ring]
    rw [hper]
    ring_nf
  rw [hvert] at h
  have h2 : (∫ x in (0 : ℝ)..(2 * Real.pi), F ((x : ℂ) + (0 : ℂ) * Complex.I))
      - (∫ x in (0 : ℝ)..(2 * Real.pi), F ((x : ℂ) + (-lam : ℂ) * Complex.I)) = 0 := by
    simpa only [add_sub_cancel_right, zero_add, zero_mul, add_zero] using h
  exact sub_eq_zero.mp h2

/-- **围道上移**：`∫ fz(θ + iw) = ∫ fz(θ)`（`w > 0`，`fz(τ,n)(z) = e^{-inz}e^{-iτcos z}`）。 -/
lemma integral_shift_up (τ : ℝ) (n : ℤ) {w : ℝ} (hw : 0 < w) :
    (∫ x in (0 : ℝ)..(2 * Real.pi), fz τ n ((x : ℂ) + (w : ℂ) * Complex.I))
      = ∫ x in (0 : ℝ)..(2 * Real.pi), fz τ n ((x : ℂ) + (0 : ℂ) * Complex.I) := by
  have hdiff : Differentiable ℂ (fun z : ℂ => fz τ n (z + (w : ℂ) * Complex.I)) :=
    (differentiable_fz τ n).comp (differentiable_id.add_const _)
  have hper : ∀ z : ℂ, (fun z : ℂ => fz τ n (z + (w : ℂ) * Complex.I))
      (z + 2 * (Real.pi : ℂ)) = (fun z : ℂ => fz τ n (z + (w : ℂ) * Complex.I)) z := by
    intro z
    exact fz_periodic_shift τ n w z
  have h := integral_shift_gen (fun z : ℂ => fz τ n (z + (w : ℂ) * Complex.I)) hdiff hper hw
  have hL : (∫ x in (0 : ℝ)..(2 * Real.pi),
        fz τ n ((x : ℂ) + (0 : ℂ) * Complex.I + (w : ℂ) * Complex.I))
      = ∫ x in (0 : ℝ)..(2 * Real.pi), fz τ n ((x : ℂ) + (w : ℂ) * Complex.I) :=
    intervalIntegral.integral_congr fun x _ => by
      congr 1
      ring
  have hR : (∫ x in (0 : ℝ)..(2 * Real.pi),
        fz τ n ((x : ℂ) + (-w : ℂ) * Complex.I + (w : ℂ) * Complex.I))
      = ∫ x in (0 : ℝ)..(2 * Real.pi), fz τ n ((x : ℂ) + (0 : ℂ) * Complex.I) :=
    intervalIntegral.integral_congr fun x _ => by
      congr 1
      ring
  rw [hL, hR] at h
  exact h

/-- **移位函数的积分**：`∫ e^{-inθ}e^{-iτcos(θ+iw)}dθ = e^{-nw}·∫fz(τ,n)`。 -/
lemma integral_exp_shift_eq (τ : ℝ) (n : ℤ) {w : ℝ} (hw : 0 < w) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
        Complex.exp (-(n : ℂ) * Complex.I * (θ : ℂ))
          * Complex.exp (-(τ : ℂ) * Complex.I * Complex.cos ((θ : ℂ) + (w : ℂ) * Complex.I)))
      = Complex.exp (-(n : ℂ) * (w : ℂ))
        * ∫ θ in (0 : ℝ)..(2 * Real.pi), fz τ n ((θ : ℂ) + (0 : ℂ) * Complex.I) := by
  have hshift := integral_shift_up τ n hw
  have h1 : (∫ θ in (0 : ℝ)..(2 * Real.pi), fz τ n ((θ : ℂ) + (w : ℂ) * Complex.I))
      = Complex.exp ((n : ℂ) * (w : ℂ))
        * ∫ θ in (0 : ℝ)..(2 * Real.pi),
            Complex.exp (-(n : ℂ) * Complex.I * (θ : ℂ))
              * Complex.exp (-(τ : ℂ) * Complex.I
                  * Complex.cos ((θ : ℂ) + (w : ℂ) * Complex.I)) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    have h1a : -(n : ℂ) * Complex.I * ((w : ℂ) * Complex.I) = (n : ℂ) * (w : ℂ) := by
      have hh : -(n : ℂ) * Complex.I * ((w : ℂ) * Complex.I)
          = -((n : ℂ) * (w : ℂ)) * (Complex.I * Complex.I) := by ring
      rw [hh, Complex.I_mul_I]
      ring
    have harg : -(n : ℂ) * Complex.I * ((θ : ℂ) + (w : ℂ) * Complex.I)
        = (n : ℂ) * (w : ℂ) + -(n : ℂ) * Complex.I * (θ : ℂ) := by
      rw [mul_add, h1a]
      ring
    rw [fz, harg, Complex.exp_add]
    ring
  rw [hshift] at h1
  have h2 : Complex.exp (-(n : ℂ) * (w : ℂ)) * Complex.exp ((n : ℂ) * (w : ℂ)) = 1 := by
    rw [← Complex.exp_add]
    simp
  rw [h1, ← mul_assoc, h2, one_mul]

/-- 移位后的函数提升到圆 `AddCircle (2π)`。 -/
def Fcsh (τ w : ℝ) : AddCircle (2 * Real.pi) → ℂ :=
  AddCircle.liftIoc (2 * Real.pi) 0
    (fun θ => Complex.exp (-(τ : ℂ) * Complex.I * Complex.cos ((θ : ℂ) + (w : ℂ) * Complex.I)))

/-- 移位函数的 Fourier 系数 = `c_n·e^{-nw}`（`w > 0`）。 -/
lemma fourierCoeff_Fcsh (τ w : ℝ) (hw : 0 < w) (n : ℤ) :
    fourierCoeff (Fcsh τ w) n = fcoef τ n * Complex.exp (-(n : ℂ) * (w : ℂ)) := by
  have hF : Fcsh τ w = fun x => AddCircle.liftIoc (2 * Real.pi) 0
      (fun θ => Complex.exp (-(τ : ℂ) * Complex.I
        * Complex.cos ((θ : ℂ) + (w : ℂ) * Complex.I))) x := rfl
  rw [hF, fourierCoeff_liftIoc_eq, fourierCoeffOn_eq_integral, sub_zero, zero_add]
  have hkey := integral_exp_shift_eq τ n hw
  have hInt : (∫ x in (0 : ℝ)..(2 * Real.pi),
        (fourier (-n)) (x : AddCircle (2 * Real.pi))
          • Complex.exp (-(τ : ℂ) * Complex.I * Complex.cos ((x : ℂ) + (w : ℂ) * Complex.I)))
      = ∫ x in (0 : ℝ)..(2 * Real.pi),
          Complex.exp (-(n : ℂ) * Complex.I * (x : ℂ))
            * Complex.exp (-(τ : ℂ) * Complex.I
                * Complex.cos ((x : ℂ) + (w : ℂ) * Complex.I)) := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    have hexp : 2 * (Real.pi : ℂ) * Complex.I * ↑(-n) * (x : ℂ) / ↑(2 * Real.pi)
        = -(n : ℂ) * Complex.I * (x : ℂ) := by
      have hpi : (Real.pi : ℂ) ≠ 0 := by
        simpa using Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      push_cast
      field_simp
    rw [fourier_coe_apply, hexp, smul_eq_mul]
  rw [hInt, hkey, fcoef, one_div, Complex.real_smul, Complex.real_smul]
  ring

/-- `approxPoly` 在 `cosh w` 处的值（collar 版 `Approx.approxPoly_eval`）。 -/
lemma approxPoly_eval_cosh (τ : ℝ) (k : ℕ) (w : ℝ) :
    (approxPoly τ k).eval ((Real.cosh w : ℝ) : ℂ)
      = fcoef τ 0 + ∑ m ∈ Finset.range (k - 1),
          2 * fcoef τ ((m : ℤ) + 1) * ((Real.cosh (((m : ℤ) + 1) * w) : ℝ) : ℂ) := by
  rw [approxPoly, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_finsetSum]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C]
  congr 1
  have h1 : ((Real.cosh w : ℝ) : ℂ) = Complex.cosh (w : ℂ) := Complex.ofReal_cosh w
  rw [h1, Polynomial.Chebyshev.T_complex_cosh]
  have harg : (((m : ℤ) + 1 : ℤ) : ℂ) * (w : ℂ) = (((((m : ℤ) + 1) * w : ℝ)) : ℂ) := by
    push_cast
    ring
  rw [harg, Complex.ofReal_cosh]

/-- `Fcsh τ w` 连续。 -/
lemma continuous_Fcsh (τ w : ℝ) : Continuous (Fcsh τ w) := by
  have hF : Fcsh τ w = AddCircle.liftIoc (2 * Real.pi) 0
      (fun θ => Complex.exp (-(τ : ℂ) * Complex.I
        * Complex.cos ((θ : ℂ) + (w : ℂ) * Complex.I))) := rfl
  rw [hF]
  refine AddCircle.liftIoc_zero_continuous ?_ ?_
  · have hc : Complex.cos (((0 : ℝ) : ℂ) + (w : ℂ) * Complex.I)
        = Complex.cos ((((2 * Real.pi : ℝ)) : ℂ) + (w : ℂ) * Complex.I) := by
      have h2pi : ((((2 * Real.pi : ℝ)) : ℂ)) = (0 : ℂ) + 2 * (Real.pi : ℂ) := by
        push_cast
        ring
      rw [h2pi]
      rw [show (0 : ℂ) + 2 * (Real.pi : ℂ) + (w : ℂ) * Complex.I
          = (((0 : ℝ) : ℂ) + (w : ℂ) * Complex.I) + 2 * (Real.pi : ℂ) from by
        rw [Complex.ofReal_zero]
        ring,
        Complex.cos_add_two_pi]
    rw [hc]
  · have hcont : Continuous fun θ : ℝ => Complex.exp (-(τ : ℂ) * Complex.I
        * Complex.cos ((θ : ℂ) + (w : ℂ) * Complex.I)) := by fun_prop
    exact hcont.continuousOn

/-- 作为连续映射的 `Fcsh τ w`。 -/
def FcshCont (τ w : ℝ) : C(AddCircle (2 * Real.pi), ℂ) where
  toFun := Fcsh τ w
  continuous_toFun := continuous_Fcsh τ w

lemma fourierCoeff_FcshCont (τ w : ℝ) (hw : 0 < w) (n : ℤ) :
    fourierCoeff (FcshCont τ w) n = fcoef τ n * Complex.exp (-(n : ℂ) * (w : ℂ)) :=
  fourierCoeff_Fcsh τ w hw n

/-- 移位函数的系数族可和（需 `w < δ`）。 -/
lemma summable_fourierCoeff_Fcsh (τ : ℝ) (hτ : 0 ≤ τ) {δ w : ℝ} (hδ : 0 < δ) (hw : 0 < w)
    (hwδ : w < δ) : Summable (fourierCoeff (FcshCont τ w)) := by
  set F : ℤ → ℂ := fun n => fcoef τ n * Complex.exp (-(n : ℂ) * (w : ℂ)) with hFdef
  have hcoe : fourierCoeff (FcshCont τ w) = F := funext fun n => fourierCoeff_FcshCont τ w hw n
  rw [hcoe]
  have hr0 : 0 ≤ Real.exp (-(δ - w)) := Real.exp_nonneg _
  have hr1 : Real.exp (-(δ - w)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hg : Summable (fun n : ℕ => Real.exp (τ * Real.sinh δ) * Real.exp (-(δ - w)) ^ n) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hnorm : ∀ n : ℤ, ‖F n‖
      ≤ Real.exp (τ * Real.sinh δ) * Real.exp (-(δ - w)) ^ n.natAbs := by
    intro n
    have h1 : ‖Complex.exp (-(n : ℂ) * (w : ℂ))‖
        = Real.exp (-(n : ℝ) * w) := by
      rw [Complex.norm_exp]
      congr 1
      simp [Complex.mul_re]
    have h2 : ‖fcoef τ n‖ ≤ Real.exp (τ * Real.sinh δ - |((n : ℤ) : ℝ)| * δ) :=
      norm_fcoef_le τ hτ hδ n
    have habs : |((n : ℤ) : ℝ)| = (n.natAbs : ℝ) := by
      rcases Int.eq_nat_or_neg n with ⟨k, rfl⟩ | ⟨k, rfl⟩ <;> simp
    have hkey : -(n : ℝ) * w ≤ (n.natAbs : ℝ) * w := by
      have h1 : -(n : ℝ) ≤ |((n : ℤ) : ℝ)| := neg_le_abs _
      rw [habs] at h1
      nlinarith [hw]
    have hexp : Real.exp (τ * Real.sinh δ - (n.natAbs : ℝ) * δ) * Real.exp (-(n : ℝ) * w)
        ≤ Real.exp (τ * Real.sinh δ) * Real.exp (-(δ - w)) ^ n.natAbs := by
      have hL : Real.exp (τ * Real.sinh δ - (n.natAbs : ℝ) * δ) * Real.exp (-(n : ℝ) * w)
          = Real.exp (τ * Real.sinh δ - (n.natAbs : ℝ) * δ + (-(n : ℝ) * w)) :=
        (Real.exp_add _ _).symm
      have hR : Real.exp (τ * Real.sinh δ) * Real.exp (-(δ - w)) ^ n.natAbs
          = Real.exp (τ * Real.sinh δ + (n.natAbs : ℝ) * (-(δ - w))) := by
        rw [← Real.exp_nat_mul, Real.exp_add]
      rw [hL, hR]
      exact Real.exp_le_exp.mpr (by nlinarith [hkey])
    rw [hFdef]
    simp only
    rw [norm_mul, h1]
    rw [habs] at h2
    exact (mul_le_mul_of_nonneg_right h2 (Real.exp_nonneg _)).trans hexp
  refine Summable.of_nat_of_neg_add_one ?_ ?_
  · refine Summable.of_norm_bounded hg fun n => ?_
    have := hnorm (n : ℤ)
    rw [Int.natAbs_natCast] at this
    exact this
  · refine Summable.of_norm_bounded ((summable_nat_add_iff 1).mpr hg) fun n => ?_
    have h := hnorm (-((n : ℤ)) - 1)
    rw [show (-((n : ℤ)) - 1) = -(((n : ℤ)) + 1) from by ring, Int.natAbs_neg] at h
    have hidx2 : ((((n : ℤ)) + 1)) = ((n + 1 : ℕ) : ℤ) := by push_cast; ring
    have hidx : ((((n : ℤ)) + 1)).natAbs = n + 1 := by rw [hidx2, Int.natAbs_natCast]
    rw [hidx] at h
    exact h

/-- **Fourier 反演给出的 collar 恒等式**：`0 < w < δ` 时
`e^{-iτcosh w} = Σ_{n∈ℤ} c_n e^{-nw}`。 -/
theorem hasSum_fcoef_cosh (τ : ℝ) (hτ : 0 ≤ τ) {δ w : ℝ} (hδ : 0 < δ) (hw : 0 < w)
    (hwδ : w < δ) :
    HasSum (fun n : ℤ => fcoef τ n * Complex.exp (-(n : ℂ) * (w : ℂ)))
      (Complex.exp (-(τ : ℂ) * Complex.I * ((Real.cosh w : ℝ) : ℂ))) := by
  have h := has_pointwise_sum_fourier_series_of_summable (summable_fourierCoeff_Fcsh τ hτ hδ hw hwδ)
    (0 : AddCircle (2 * Real.pi))
  have hf : (fun n : ℤ => fourierCoeff (FcshCont τ w) n • fourier n (0 : AddCircle (2 * Real.pi)))
      = fun n : ℤ => fcoef τ n * Complex.exp (-(n : ℂ) * (w : ℂ)) := by
    funext n
    rw [fourierCoeff_FcshCont τ w hw n]
    simp
  rw [hf] at h
  have hval : FcshCont τ w (0 : AddCircle (2 * Real.pi))
      = Complex.exp (-(τ : ℂ) * Complex.I * ((Real.cosh w : ℝ) : ℂ)) := by
    have hcoe : ((2 * Real.pi : ℝ) : AddCircle (2 * Real.pi)) = (0 : AddCircle (2 * Real.pi)) := by
      have hp := AddCircle.coe_add_period (2 * Real.pi) (0 : ℝ)
      simpa using hp
    rw [← hcoe]
    have hF : (FcshCont τ w : AddCircle (2 * Real.pi) → ℂ) = Fcsh τ w := rfl
    rw [hF, Fcsh]
    rw [AddCircle.liftIoc_zero_coe_apply
      (show (2 * Real.pi : ℝ) ∈ Set.Ioc 0 (2 * Real.pi) from
        ⟨by linarith [Real.pi_pos], le_refl _⟩)]
    rw [show (((2 * Real.pi : ℝ)) : ℂ) + (w : ℂ) * Complex.I
        = ((0 : ℝ) : ℂ) + (w : ℂ) * Complex.I + 2 * (Real.pi : ℂ) from by push_cast; ring,
      Complex.cos_add_two_pi]
    rw [show ((0 : ℝ) : ℂ) + (w : ℂ) * Complex.I = (w : ℂ) * Complex.I from by
        rw [Complex.ofReal_zero]
        ring,
      Complex.cos_mul_I, Complex.ofReal_cosh]
  rw [hval] at h
  exact h



/-- 有限和恒等式（collar 误差的来源）：`Σ_{n<k}(c_n e^{-nw} + c_{n+1}e^{(n+1)w})
= P_k(cosh w) + c_k e^{kw}`。 -/
lemma sum_range_pairs (τ w : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    ∑ n ∈ Finset.range k, (fcoef τ (n : ℤ) * Complex.exp (-((n : ℤ) : ℂ) * (w : ℂ))
        + fcoef τ ((n : ℤ) + 1) * Complex.exp ((((n : ℤ) + 1 : ℤ) : ℂ) * (w : ℂ)))
      = (approxPoly τ k).eval ((Real.cosh w : ℝ) : ℂ)
        + fcoef τ (k : ℤ) * Complex.exp (((k : ℤ) : ℂ) * (w : ℂ)) := by
  rw [Finset.sum_add_distrib]
  have h1 : ∑ n ∈ Finset.range k, fcoef τ (n : ℤ) * Complex.exp (-((n : ℤ) : ℂ) * (w : ℂ))
      = fcoef τ 0 + ∑ m ∈ Finset.range (k - 1),
          fcoef τ ((m : ℤ) + 1) * Complex.exp (-((((m : ℤ) + 1 : ℤ)) : ℂ) * (w : ℂ)) := by
    rw [sum_range_split (fun n : ℕ => fcoef τ (n : ℤ)
      * Complex.exp (-((n : ℤ) : ℂ) * (w : ℂ))) hk]
    have h0 : fcoef τ (((0 : ℕ)) : ℤ)
        * Complex.exp (-((((0 : ℕ)) : ℤ) : ℂ) * (w : ℂ)) = fcoef τ 0 := by simp
    have hsum : (∑ m ∈ Finset.range (k - 1),
          fcoef τ ((((m + 1 : ℕ)) : ℤ)) * Complex.exp (-(((((m + 1 : ℕ)) : ℤ)) : ℂ) * (w : ℂ)))
        = ∑ m ∈ Finset.range (k - 1),
          fcoef τ ((m : ℤ) + 1) * Complex.exp (-((((m : ℤ) + 1 : ℤ)) : ℂ) * (w : ℂ)) :=
      Finset.sum_congr rfl fun m _ => by
        rw [show (((m + 1 : ℕ)) : ℤ) = (m : ℤ) + 1 by push_cast; ring]
    rw [h0, hsum]
  have h2 : ∑ n ∈ Finset.range k,
        fcoef τ ((n : ℤ) + 1) * Complex.exp ((((n : ℤ) + 1 : ℤ) : ℂ) * (w : ℂ))
      = (∑ m ∈ Finset.range (k - 1),
          fcoef τ ((m : ℤ) + 1) * Complex.exp ((((m : ℤ) + 1 : ℤ) : ℂ) * (w : ℂ)))
        + fcoef τ (k : ℤ) * Complex.exp (((k : ℤ) : ℂ) * (w : ℂ)) := by
    rw [sum_range_split_last (fun n : ℕ => fcoef τ ((n : ℤ) + 1)
      * Complex.exp ((((n : ℤ) + 1 : ℤ) : ℂ) * (w : ℂ))) hk]
    congr 1
    rw [show (((k - 1 : ℕ)) : ℤ) + 1 = (k : ℤ) by push_cast; omega]
  rw [h1, h2, approxPoly_eval_cosh]
  have hcosh : ∀ m : ℕ,
      fcoef τ ((m : ℤ) + 1) * Complex.exp (-((((m : ℤ) + 1 : ℤ)) : ℂ) * (w : ℂ))
        + fcoef τ ((m : ℤ) + 1) * Complex.exp ((((m : ℤ) + 1 : ℤ) : ℂ) * (w : ℂ))
      = 2 * fcoef τ ((m : ℤ) + 1) * ((Real.cosh (((m : ℤ) + 1) * w) : ℝ) : ℂ) := by
    intro m
    have harg : ((((m : ℤ) + 1 : ℤ)) : ℂ) * (w : ℂ) = ((((m : ℤ) + 1) * w : ℝ) : ℂ) := by
      push_cast
      ring
    have hreal : Complex.exp (((((m : ℤ) + 1) * w : ℝ)) : ℂ)
        + Complex.exp (-(((((m : ℤ) + 1) * w : ℝ)) : ℂ))
        = 2 * ((Real.cosh (((m : ℤ) + 1) * w) : ℝ) : ℂ) := by
      rw [Real.cosh_eq]
      simp only [Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_ofNat,
        Complex.ofReal_exp, Complex.ofReal_neg]
      ring
    rw [neg_mul, harg]
    linear_combination (fcoef τ ((m : ℤ) + 1)) * hreal
  have hS : (∑ m ∈ Finset.range (k - 1),
        fcoef τ ((m : ℤ) + 1) * Complex.exp (-((((m : ℤ) + 1 : ℤ)) : ℂ) * (w : ℂ)))
      + (∑ m ∈ Finset.range (k - 1),
        fcoef τ ((m : ℤ) + 1) * Complex.exp ((((m : ℤ) + 1 : ℤ) : ℂ) * (w : ℂ)))
      = ∑ m ∈ Finset.range (k - 1),
          2 * fcoef τ ((m : ℤ) + 1) * ((Real.cosh (((m : ℤ) + 1) * w) : ℝ) : ℂ) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun m _ => hcosh m
  rw [← hS]
  ring

/-! ## 5. 诊断与「还差什么」（供后续接手）

### 5.1 已证内容

* §2：`hkernel` ⟺「最终不存在 `τ ≤ ρ(2N+2)` 的 admissible 构造」。
* §3：修正后的收尾（只需 `C₁C₂ ≤ A N`、`A N → 0`）。
* §4：**collar 上的 Jacobi–Anger 尾部恒等式**（本题真正缺的那块砖）：

  `hasSum_fcoef_cosh : 0 < w < δ → HasSum (fun n : ℤ => fcoef τ n * e^{-nw}) (e^{-iτ cosh w})`

  证明链条（全部已证，无占位符、无解析延拓）：
  `integral_shift_gen`（一般 `2π` 周期整函数的围道平移）→ `integral_shift_up`
  （`∫ fz(θ+iw) = ∫ fz(θ)`）→ `integral_exp_shift_eq` / `fourierCoeff_Fcsh`
  （移位函数的第 `n` 个 Fourier 系数是 `c_n e^{-nw}`）→ `summable_fourierCoeff_Fcsh`
  → Mathlib `has_pointwise_sum_fourier_series_of_summable` 在 `θ = 0` 取值。

### 5.2 为什么必须走这条路（`CollarBound` 路线为何注定失败）

`CollarBound.norm_{,deriv_}approxPoly_le_collar` 对**整个** Chebyshev 和用同一个椭圆参数 `δ'`，
于是界里带 `E := e^{τ·sinh δ'}`（`τ ≤ ρ(2N+2)` 时 `E = e^{Θ(N)}`）。代入
`h_zero_le_of_admissible_twoN_add_one` 的链条（`B = √ε`、`k = 2N+1`、`q = 2N+2`）：

* `M₁ ≥ E·k²/τ` ⇒ `kernelA_le` 里的 `(ε + B·M₁)` 含 `√ε·E k²/τ`；
* `kernelC_le` 含 `4K·M₁ ≥ 4K·E k²/τ`（此项**不含** `√ε`，量级 `e^{ρq sinh δ'}`）。

而 `hkernel` 要求 `C₁C₂ ≤ ((1-cos(φ/2))/8)²·e^{-ηq}`（`η = δ' - ρ sinh δ'`）。两者相差
`e^{E 量级}`，**指数级**不可能对齐。所以这不是"界不够紧"，而是这批界的方向不对：
它们对 `Σ_m |c_m||T_m(u)|` 作估计，而 collar 上真正小的是**带抵消的和** `Σ_m c_m T_m(u)`
（`|T_m(cosh w)| = cosh(mw)` 增长，但系数 `c_m` 的相位使其和对消到 `e^{-δ'k}` 量级）。

### 5.3 还差什么（精确清单）

1. **collar 误差本身**：由 §4 的恒等式 + `tsum_nat_add_neg_add_one` / `Summable.sum_add_tsum_nat_add`
   把 `Σ_{n:ℤ} c_n e^{-nw}` 拆成 `P_k(cosh w)` + 尾部，得（`k ≥ 1`、`δ > w > 0`）
   `‖e^{-iτ cosh w} - P_k(cosh w)‖ ≤ e^{τ sinh δ}·(e^{-k(δ-w)} + e^{-k(δ+w)}/(1-e^{-(δ+w)})
     + e^{-(k+1)(δ-w)}/(1-e^{-(δ-w)}))`。
   这一步是**纯级数整理**（无新数学）：本文件的 `sum_range_pairs` 已经证掉了它的
   **有限和一半**（`Σ_{n<k}(c_n e^{-nw} + c_{n+1}e^{(n+1)w}) = P_k(cosh w) + c_k e^{kw}`），
   剩下的只是把 `Σ'_{n:ℤ} c_n e^{-nw}` 按 `tsum_nat_add_neg_add_one` +
   `Summable.sum_add_tsum_nat_add k` 劈开、再用 `norm_tsum_le_tsum_norm` + 几何级数
   （照抄 `Approx.norm_tail_le` 的模板）估尾部，约 80–120 行。
2. **导数版**：对 `E = e^{-iμ} - P(μ)` 求导（`P^{(j)}(μ) = τ^{-j}(approxPoly)^{(j)}(μ/τ)`），
   需要 `|T_m^{(j)}(u)| ≤ m^{2j}e^{mw}`（`m²`、`m⁴` 因子）——同样的尾部整理，但多出
   `k²/τ`、`k⁴/τ²` 因子；配合 collar 条件（`w ≤ δ'/2`，即 `2√(B/τ) ≤ δ'/2`）与 `1/τ ≤ 1/(16B/δ'²)`
   即可（这些因子是**多项式**，被 `e^{-ηq}` 压掉）。
3. **装配**：`kernelA_mul_kernelC_le`（`FinalSmall`）+ `norm_psi_le_band_add_collar`，
   取 `A N = poly(N)·C(δ',ρ)·e^{-η(2N+2)}`，用 §3 的 `h_zero_small_of_tau_le_tendsto` 收尾。
4. **小 `τ` 分歧**：`τ → 0` 时 `1/τ` 因子发散；但 collar 条件 `2√(B/τ) ≤ δ'/2` 逼出
   `τ ≥ 16B/δ'²`，即 `1/τ ≤ δ'²/(16√ε)`，正好抵消 `√ε`；`τ = 0` 的退化情形由
   `h_zero_of_admissible_of_cost_eq_zero` 处理（`M5Apply` 里已如此）。

### 5.4 结论（给调用方）

**不要把 `hkernel` 当作独立的"技术引理"来证**：§2 说明它与主定理核心等价
（在 §3 的收尾 + `HTraceLower.h_zero_ge` 之下），因此它**只在「小成本构造不存在」时为真**
（空真），而这正是主定理的内容。可行的两种收尾方式：

* (A) 上面 1–4 的完整路线（本文件已铺好 §4 的关键砖）；
* (B) 照论文 `app:smear` 的做法：换 taper 宽度 `B = ετ/q²`（而不是 `√ε`）与 Markov 不等式，
  直接得 `h(0) ≤ 2c₀q²√ε → 0`，再与常数 `1-cos(φ/2)` 比较 —— 但那要求改动 `kernelA/kernelC`
  的定义层（`SmearingMain`/`M3`），改动面比 (A) 大。 -/


end RobustZ
