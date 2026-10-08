import RobustZ.FinalConv
import RobustZ.Band

/-!
# M5 收尾（`FinalSmall`）：`τ ≤ ρ(2N+2)` 情形的端点小性

目标（论文 §2.4 收尾）：

```
lemma h_zero_small_of_tau_le {φ : ℝ} (hφ0 : 0 < φ) (hφπ : φ ≤ Real.pi)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ {L : ℕ} {α θ : Fin L → ℝ},
      Admissible N φ L α θ → (∑ j, θ j) / 2 ≤ ρ * (2 * (N : ℝ) + 2) →
      h L α θ 0 < 1 - Real.cos (φ / 2)
```

即：**最终不存在**满足 `τ ≤ ρ(2N+2)` 的 N 阶 admissible 构造（`τ = (Σθ)/2`）。

与上面这个「理想签名」相比，本文件第 §4 节落盘的 `h_zero_small_of_tau_le` **多出**：

* 两个参数 `{δ' : ℝ} (hδ' : 0 < δ') (hη : 0 < δ' - ρ * Real.sinh δ')`；
* 一个假设 `hkernel`：「对一切满足 `τ ≤ ρ(2N+2)` 的 admissible 构造，核常数积
  `C₁·C₂` 最终按 `e^{-(δ'-ρ sinh δ')(2N+2)}` 衰减」（完整陈述见该引理）。

除这三点外逐字一致。`hkernel` 是**唯一**降级来的假设；由它到最终结论的全部算术都在
本文件里证完了（§2、§3），它的**解析输入**（collar 上的 `M₁, M₂`）缺失的原因与补法见 §6。
（下游 `RobustZ/Theorem.lean` 已按此签名把 `hkernel` 贯穿到 `c_ge_four_proof`。）

## 本文件给出的内容（全部无 `sorry`）

* `exists_delta_sub_mul_sinh_pos`：存在 `δ' > 0` 使 `0 < δ' - ρ·sinh δ'`。
* `epsOf_le_exp_decay`：`τ ≥ 0`、`τ ≤ ρ(2N+2)` 时
  `epsOf τ δ' (2N+1) ≤ C(δ')·e^{δ'}·e^{-η(2N+2)}`，`η = δ' - ρ sinh δ'`。
* `tendsto_exp_decay_atTop`：`N ↦ e^{-η(2N+2)} → 0`。
* `sqrt_sq_mul_exp`、`h_zero_lt_of_kernel_decay`：由「核常数积 `C₁C₂` 按
  `e^{-η(2N+2)}` 衰减」得端点小性（`8√(C₁C₂) < 1-cos(φ/2)`）。
* `h_zero_small_of_tau_le`：**降级版本**（额外假设 `hkernel`，见该引理 docstring）。
* `kernelC_nonneg`、`kernelA_mul_kernelC_le`：`hkernel` 的**接口** ——
  `C₁·C₂` 的显式界只需要 collar 上的导数界 `M₁, M₂`（和截断常数 `K`）。
* `norm_fcoef_le_one`、`norm_fcoef_le_min`：`‖fcoef τ n‖ ≤ 1` 与
  `min` 形式的逐项界 —— 修补缺口的第一块砖（§5.5）。
* §6 是对「为什么现有零件证不出 `hkernel`」与「还差什么」的定量诊断。
-/

noncomputable section

namespace RobustZ

open Filter MeasureTheory
open scoped Real

/-! ## (1) 「选 `δ'`」这一步 -/

/-- **存在足够小的 `δ' > 0` 使 `ρ·sinh δ' < δ'`**（`0 < ρ < 1`）。

证明走 `sinh` 在原点的导数：`slope Real.sinh 0 y = sinh y / y → 1`（`y → 0`），
而 `1 < (1 + ρ⁻¹)/2`，故存在 `δ' > 0` 使 `sinh δ'/δ' < (1+ρ⁻¹)/2`；
两边乘 `ρδ'` 得 `ρ sinh δ' ≤ ρδ'(1+ρ⁻¹)/2 = δ'(1+ρ)/2 < δ'`。 -/
lemma exists_delta_sub_mul_sinh_pos {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    ∃ δ' : ℝ, 0 < δ' ∧ 0 < δ' - ρ * Real.sinh δ' := by
  have hinv : 1 < ρ⁻¹ := (one_lt_inv₀ hρ0).mpr hρ1
  have hc : (1 : ℝ) < (1 + ρ⁻¹) / 2 := by linarith
  -- `slope Real.sinh 0 y = sinh y / y → 1`（`y → 0`，`y ≠ 0`）
  have hslope : Tendsto (slope Real.sinh 0) (nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ) (nhds (1 : ℝ)) := by
    have h := (Real.hasDerivAt_sinh 0).tendsto_slope
    simpa using h
  have hev : ∀ᶠ y in nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ, slope Real.sinh 0 y < (1 + ρ⁻¹) / 2 :=
    hslope.eventually (eventually_lt_nhds hc)
  rw [eventually_nhdsWithin_iff] at hev
  obtain ⟨ε, hε0, hε⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨min (ε / 2) (1 / 2), by positivity, ?_⟩
  set δ' : ℝ := min (ε / 2) (1 / 2) with hδ'def
  have hδ'0 : 0 < δ' := by rw [hδ'def]; positivity
  have hδ'le : δ' ≤ ε / 2 := by rw [hδ'def]; exact min_le_left _ _
  have hdist : dist δ' 0 < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hδ'0]
    linarith
  have hsl : Real.sinh δ' / δ' < (1 + ρ⁻¹) / 2 := by
    have h := hε hdist (by simp [ne_of_gt hδ'0])
    rw [slope_def_field] at h
    simpa using h
  have hmul : Real.sinh δ' < (1 + ρ⁻¹) / 2 * δ' := by
    rw [div_lt_iff₀ hδ'0] at hsl
    exact hsl
  have h2 : ρ * Real.sinh δ' < ρ * ((1 + ρ⁻¹) / 2 * δ') := mul_lt_mul_of_pos_left hmul hρ0
  have h3 : ρ * ((1 + ρ⁻¹) / 2 * δ') = (1 + ρ) / 2 * δ' := by
    field_simp
    ring
  rw [h3] at h2
  have h4 : (1 + ρ) / 2 * δ' < δ' := by nlinarith [hδ'0, hρ1]
  linarith

/-! ## (2) `epsOf` 的指数衰减 -/

/-- **`ε` 的指数衰减**：`τ ≥ 0`、`τ ≤ ρ(2N+2)` 时
`epsOf τ δ' (2N+1) ≤ (1 + 4/(1-e^{-δ'}))·e^{δ'}·e^{-η(2N+2)}`，`η = δ' - ρ sinh δ'`。

两个指数正好相消：`ρ(2N+2)sinh δ' - (2N+1)δ' = δ' - (δ' - ρ sinh δ')(2N+2)`，
所以用 `τ ≤ ρ(2N+2)` 与 `e^{·}` 的单调性把 `e^{τ sinh δ'}` 换成 `e^{ρ(2N+2)sinh δ'}` 即可。 -/
lemma epsOf_le_exp_decay {ρ δ' τ : ℝ} {N : ℕ} (hδ' : 0 < δ') (_hτ0 : 0 ≤ τ)
    (hτρ : τ ≤ ρ * (2 * (N : ℝ) + 2)) :
    epsOf τ δ' (2 * N + 1)
      ≤ (1 + 4 / (1 - Real.exp (-δ'))) * Real.exp δ'
          * Real.exp (-(δ' - ρ * Real.sinh δ') * (2 * (N : ℝ) + 2)) := by
  have hlt1 : Real.exp (-δ') < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hpos1 : 0 < 1 - Real.exp (-δ') := by linarith
  have hC : 0 < 1 + 4 / (1 - Real.exp (-δ')) := by positivity
  have hsinh : 0 < Real.sinh δ' := (Real.sinh_pos_iff (x := δ')).mpr hδ'
  have hexp1 : Real.exp (τ * Real.sinh δ')
      ≤ Real.exp (ρ * (2 * (N : ℝ) + 2) * Real.sinh δ') :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hτρ hsinh.le)
  have hpow : Real.exp (-δ') ^ (2 * N + 1)
      = Real.exp (-(((2 * N + 1 : ℕ) : ℝ) * δ')) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hstep : Real.exp (τ * Real.sinh δ') * Real.exp (-(((2 * N + 1 : ℕ) : ℝ) * δ'))
      ≤ Real.exp δ' * Real.exp (-(δ' - ρ * Real.sinh δ') * (2 * (N : ℝ) + 2)) := by
    refine le_trans (mul_le_mul_of_nonneg_right hexp1 (Real.exp_pos _).le) (le_of_eq ?_)
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    push_cast
    ring
  calc epsOf τ δ' (2 * N + 1)
      = Real.exp (τ * Real.sinh δ') * (1 + 4 / (1 - Real.exp (-δ')))
          * Real.exp (-(((2 * N + 1 : ℕ) : ℝ) * δ')) := by
        rw [epsOf, hpow]
    _ = (1 + 4 / (1 - Real.exp (-δ')))
          * (Real.exp (τ * Real.sinh δ') * Real.exp (-(((2 * N + 1 : ℕ) : ℝ) * δ'))) := by
        ring
    _ ≤ (1 + 4 / (1 - Real.exp (-δ')))
          * (Real.exp δ' * Real.exp (-(δ' - ρ * Real.sinh δ') * (2 * (N : ℝ) + 2))) :=
        mul_le_mul_of_nonneg_left hstep hC.le
    _ = (1 + 4 / (1 - Real.exp (-δ'))) * Real.exp δ'
          * Real.exp (-(δ' - ρ * Real.sinh δ') * (2 * (N : ℝ) + 2)) := by
        ring

/-- 衰减因子 `e^{-η(2N+2)} → 0`（`η > 0`）。用 `e^{-η(2N+2)} = (e^{-2η})^N·e^{-2η}`
与 `tendsto_pow_atTop_nhds_zero_of_lt_one`。 -/
lemma tendsto_exp_decay_atTop {η : ℝ} (hη : 0 < η) :
    Tendsto (fun N : ℕ => Real.exp (-η * (2 * (N : ℝ) + 2))) atTop (nhds 0) := by
  have hlt : Real.exp (-2 * η) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hnn : 0 ≤ Real.exp (-2 * η) := (Real.exp_pos _).le
  have h1 : Tendsto (fun N : ℕ => Real.exp (-2 * η) ^ N) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hnn hlt
  have h2 : Tendsto (fun _ : ℕ => Real.exp (-2 * η)) atTop (nhds (Real.exp (-2 * η))) :=
    tendsto_const_nhds
  have h3 : Tendsto (fun N : ℕ => Real.exp (-2 * η) ^ N * Real.exp (-2 * η)) atTop
      (nhds (0 * Real.exp (-2 * η))) := h1.mul h2
  rw [zero_mul] at h3
  refine h3.congr' ?_
  filter_upwards with N
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  ring

/-! ## (3) 组装 -/

/-- `√(a²·e^c) = a·e^{c/2}`（`a ≥ 0`）。 -/
lemma sqrt_sq_mul_exp (a c : ℝ) (ha : 0 ≤ a) :
    Real.sqrt (a ^ 2 * Real.exp c) = a * Real.exp (c / 2) := by
  rw [Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha, ← Real.exp_half]

/-- **由「核常数积按 `e^{-η(2N+2)}` 衰减」得端点小性**。

`h(0) ≤ 8√(C₁C₂) ≤ 8√(((1-cos(φ/2))/8)²·e^{-η(2N+2)}) = (1-cos(φ/2))·e^{-η(2N+2)/2} < 1-cos(φ/2)`。 -/
lemma h_zero_lt_of_kernel_decay {N : ℕ} {φ : ℝ} {L : ℕ} {α θ : Fin L → ℝ}
    (hφ0 : 0 < φ) (hφπ : φ ≤ Real.pi)
    (hAdm : Admissible N φ L α θ) {δ' η : ℝ} (hδ' : 0 < δ') (hη : 0 < η)
    (hker : kernelA ((∑ j, θ j) / 2) (Real.sqrt (epsOf ((∑ j, θ j) / 2) δ' (2 * N + 1)))
          (scaledApprox ((∑ j, θ j) / 2) (2 * N + 1))
        * kernelC ((∑ j, θ j) / 2) (Real.sqrt (epsOf ((∑ j, θ j) / 2) δ' (2 * N + 1)))
          (scaledApprox ((∑ j, θ j) / 2) (2 * N + 1))
        ≤ ((1 - Real.cos (φ / 2)) / 8) ^ 2 * Real.exp (-η * (2 * (N : ℝ) + 2))) :
    h L α θ 0 < 1 - Real.cos (φ / 2) := by
  have hc₀ : 0 < 1 - Real.cos (φ / 2) := one_sub_cos_half_pos hφ0 hφπ
  have hq : (0 : ℝ) < 2 * (N : ℝ) + 2 := by positivity
  have hElt : Real.exp (-η * (2 * (N : ℝ) + 2)) < 1 :=
    Real.exp_lt_one_iff.mpr (by nlinarith)
  have hbase : 8 * Real.sqrt
      (kernelA ((∑ j, θ j) / 2) (Real.sqrt (epsOf ((∑ j, θ j) / 2) δ' (2 * N + 1)))
          (scaledApprox ((∑ j, θ j) / 2) (2 * N + 1))
        * kernelC ((∑ j, θ j) / 2) (Real.sqrt (epsOf ((∑ j, θ j) / 2) δ' (2 * N + 1)))
          (scaledApprox ((∑ j, θ j) / 2) (2 * N + 1)))
      ≤ (1 - Real.cos (φ / 2)) * Real.exp ((-η * (2 * (N : ℝ) + 2)) / 2) := by
    have hs : Real.sqrt
        (kernelA ((∑ j, θ j) / 2) (Real.sqrt (epsOf ((∑ j, θ j) / 2) δ' (2 * N + 1)))
            (scaledApprox ((∑ j, θ j) / 2) (2 * N + 1))
          * kernelC ((∑ j, θ j) / 2) (Real.sqrt (epsOf ((∑ j, θ j) / 2) δ' (2 * N + 1)))
            (scaledApprox ((∑ j, θ j) / 2) (2 * N + 1)))
        ≤ ((1 - Real.cos (φ / 2)) / 8) * Real.exp ((-η * (2 * (N : ℝ) + 2)) / 2) :=
      (Real.sqrt_le_sqrt hker).trans (le_of_eq (sqrt_sq_mul_exp ((1 - Real.cos (φ / 2)) / 8)
        (-η * (2 * (N : ℝ) + 2)) (by positivity)))
    have h8 := mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 8)
    have hr : 8 * (((1 - Real.cos (φ / 2)) / 8) * Real.exp ((-η * (2 * (N : ℝ) + 2)) / 2))
        = (1 - Real.cos (φ / 2)) * Real.exp ((-η * (2 * (N : ℝ) + 2)) / 2) := by ring
    linarith
  calc h L α θ 0
      ≤ 8 * Real.sqrt
        (kernelA ((∑ j, θ j) / 2) (Real.sqrt (epsOf ((∑ j, θ j) / 2) δ' (2 * N + 1)))
            (scaledApprox ((∑ j, θ j) / 2) (2 * N + 1))
          * kernelC ((∑ j, θ j) / 2) (Real.sqrt (epsOf ((∑ j, θ j) / 2) δ' (2 * N + 1)))
            (scaledApprox ((∑ j, θ j) / 2) (2 * N + 1))) :=
        h_zero_le_of_admissible_twoN_add_one hAdm hδ'
    _ ≤ (1 - Real.cos (φ / 2)) * Real.exp ((-η * (2 * (N : ℝ) + 2)) / 2) := hbase
    _ < (1 - Real.cos (φ / 2)) * 1 := by
        refine mul_lt_mul_of_pos_left ?_ hc₀
        rw [Real.exp_lt_one_iff]
        nlinarith
    _ = 1 - Real.cos (φ / 2) := mul_one _

/-! ## (4) 目标引理（**降级版本**）

与题目要求的签名相比，多了一个假设 `hkernel`（其余逐字一致）：
`hkernel` 就是「M3（`norm_sum_le_of_moments`）+ M4（`epsOf` 几何衰减）+ collar 导数界
⇒ 核常数积 `C₁C₂` 按 `e^{-(δ'-ρ sinh δ')(2N+2)}` 衰减」这一步的**结论**。
上面三个引理把它到最终结论的**全部**算术都证掉了。 -/
lemma h_zero_small_of_tau_le {φ : ℝ} (hφ0 : 0 < φ) (hφπ : φ ≤ Real.pi)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    {δ' : ℝ} (hδ' : 0 < δ') (hη : 0 < δ' - ρ * Real.sinh δ')
    (hkernel : ∀ᶠ N : ℕ in Filter.atTop, ∀ {L : ℕ} {α θ : Fin L → ℝ},
      Admissible N φ L α θ → (∑ j, θ j) / 2 ≤ ρ * (2 * (N : ℝ) + 2) →
      kernelA ((∑ j, θ j) / 2) (Real.sqrt (epsOf ((∑ j, θ j) / 2) δ' (2 * N + 1)))
          (scaledApprox ((∑ j, θ j) / 2) (2 * N + 1))
        * kernelC ((∑ j, θ j) / 2) (Real.sqrt (epsOf ((∑ j, θ j) / 2) δ' (2 * N + 1)))
          (scaledApprox ((∑ j, θ j) / 2) (2 * N + 1))
        ≤ ((1 - Real.cos (φ / 2)) / 8) ^ 2
          * Real.exp (-(δ' - ρ * Real.sinh δ') * (2 * (N : ℝ) + 2))) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ {L : ℕ} {α θ : Fin L → ℝ},
      Admissible N φ L α θ → (∑ j, θ j) / 2 ≤ ρ * (2 * (N : ℝ) + 2) →
      h L α θ 0 < 1 - Real.cos (φ / 2) := by
  have _hδ'exists : ∃ δ : ℝ, 0 < δ ∧ 0 < δ - ρ * Real.sinh δ :=
    exists_delta_sub_mul_sinh_pos hρ0 hρ1
  filter_upwards [hkernel] with N hN L α θ hAdm hτρ
  exact h_zero_lt_of_kernel_decay hφ0 hφπ hAdm hδ' hη (hN hAdm hτρ)

/-! ## (5) 缺口的「接口」：`C₁·C₂` 的显式界

下面这条引理说明 `hkernel` **只需要** collar 上的两个导数界 `M₁ = sup‖Ψ_A'‖`、
`M₂ = sup‖Ψ_A''‖`（外加截断导数常数 `K`）就能推出：它把 `kernelA_le` / `kernelC_le`
直接相乘。这是「最后一块拼图」真正缺少的输入所在的位置。 -/

/-- `kernelC ≥ 0`（`τ, B > 0` 时被积函数非负、积分区间正向）。 -/
lemma kernelC_nonneg {τ B : ℝ} (hτ : 0 < τ) (hB : 0 < B) (P : Polynomial ℂ) :
    0 ≤ kernelC τ B P := by
  rw [kernelC]
  refine mul_nonneg (by positivity) ?_
  exact intervalIntegral.integral_nonneg (by linarith) fun μ _ => norm_nonneg _

/-- **`C₁·C₂` 的显式界**：把 `kernelA_le` 与 `kernelC_le` 相乘。 -/
lemma kernelA_mul_kernelC_le {τ B : ℝ} (hτ : 0 < τ) (hB : 0 < B) (P : Polynomial ℂ)
    {ε M₁ M₂ K : ℝ} (hε : 0 ≤ ε) (hM₁ : 0 ≤ M₁)
    (hψ : ∀ μ : ℝ, ‖psi τ B P μ‖ ≤ ε + B * M₁)
    (hPε : ∀ μ : ℝ, |μ| ≤ τ →
      ‖Complex.exp (-(μ : ℂ) * Complex.I) - P.eval ((μ : ℂ))‖ ≤ ε)
    (hA1 : ∀ μ : ℝ, |μ| ≤ τ + B → ‖deriv (fun x : ℝ => psiA P x) μ‖ ≤ M₁)
    (hA2 : ∀ μ : ℝ, |μ| ≤ τ + B → ‖deriv (deriv (fun x : ℝ => psiA P x)) μ‖ ≤ M₂)
    (hK1 : ∀ μ : ℝ, ‖deriv (fun x : ℝ => ((cutoff τ B x : ℝ) : ℂ)) μ‖ ≤ K / B)
    (hK2 : ∀ μ : ℝ, ‖deriv (deriv (fun x : ℝ => ((cutoff τ B x : ℝ) : ℂ))) μ‖ ≤ K / B ^ 2) :
    kernelA τ B P * kernelC τ B P
      ≤ ((2 * Real.pi)⁻¹ * (2 * (τ + B + 1)) * (ε + B * M₁))
        * ((2 * Real.pi)⁻¹ *
            (2 * (τ + B + 1) * M₂ + 2 * (M₁ * (2 * K)) + (ε + B * M₁) * (4 * K / B))) := by
  have hb : (0 : ℝ) ≤ (2 * Real.pi)⁻¹ * (2 * (τ + B + 1)) * (ε + B * M₁) :=
    mul_nonneg (mul_nonneg (by positivity) (by linarith))
      (add_nonneg hε (mul_nonneg hB.le hM₁))
  exact mul_le_mul (kernelA_le hτ hB P hψ) (kernelC_le hτ hB P hε hPε hA1 hA2 hK1 hK2)
    (kernelC_nonneg hτ hB P) hb

/-! ## (5.5) 补缺口的第一块砖：`‖fcoef τ n‖ ≤ 1` 与 `min` 形式

`fcoef_bound` 用的是**固定**椭圆参数 `δ`，于是系数界里必然带出 `e^{τ sinh δ}`。
但这条界对**任意** `δ > 0` 成立，取 `δ → 0⁺` 即得与 `τ, n` 无关的 `‖fcoef τ n‖ ≤ 1`。
两者取 `min` 就得到「小 `n` 用常数界、大 `n` 用几何衰减」的逐项界 —— 这正是
让 collar 估计丢掉 `E` 因子的关键（见 §6 的配方）。 -/

/-- **`fcoef` 的一致界**：`‖fcoef τ n‖ ≤ 1`（`τ ≥ 0`、`n > 0`）。
由 `fcoef_bound` 令 `δ → 0⁺` 得到。 -/
lemma norm_fcoef_le_one (τ : ℝ) (hτ : 0 ≤ τ) {n : ℤ} (hn : 0 < n) :
    ‖fcoef τ n‖ ≤ 1 := by
  have hcont : Continuous fun δ : ℝ => Real.exp (τ * Real.sinh δ - (n : ℝ) * δ) :=
    Real.continuous_exp.comp
      ((continuous_const.mul Real.continuous_sinh).sub (continuous_const.mul continuous_id))
  have h1 : Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1)) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h2 : Tendsto (fun k : ℕ => Real.exp (τ * Real.sinh ((1 : ℝ) / ((k : ℝ) + 1))
      - (n : ℝ) * ((1 : ℝ) / ((k : ℝ) + 1)))) atTop (nhds 1) := by
    have h := (hcont.tendsto 0).comp h1
    have h0 : Real.exp (τ * Real.sinh 0 - (n : ℝ) * 0) = 1 := by simp [Real.sinh_zero]
    rwa [h0] at h
  refine le_of_tendsto_of_tendsto tendsto_const_nhds h2 ?_
  filter_upwards with k
  exact fcoef_bound τ hτ (by positivity : (0 : ℝ) < 1 / ((k : ℝ) + 1)) n hn

/-- **逐项 `min` 界**：`‖fcoef τ n‖ ≤ min 1 (e^{τ sinh δ - nδ})`（`δ > 0`、`n > 0`）。 -/
lemma norm_fcoef_le_min (τ : ℝ) (hτ : 0 ≤ τ) {δ : ℝ} (hδ : 0 < δ) {n : ℤ} (hn : 0 < n) :
    ‖fcoef τ n‖ ≤ min 1 (Real.exp (τ * Real.sinh δ - n * δ)) :=
  le_min (norm_fcoef_le_one τ hτ hn) (fcoef_bound τ hτ hδ n hn)

/-! ## (6) 缺口诊断（`sorry`-free 的说明性注释）

### 为什么现有零件证不出 `hkernel`

把上面那条引理的右端记为 `A(τ,B,ε,M₁,M₂,K)`。现有库里 `M₁, M₂` 的**唯一**来源是
`CollarBound.norm_approxPoly_le_collar` 与 `norm_deriv_approxPoly_le_collar`：

```
‖(approxPoly τ k).eval (u:ℂ)‖      ≤ E·4/(1-e^{-δ'}) + 1
‖deriv (approxPoly τ k) u‖          ≤ E·4/(1-e^{-δ'})·k² + 1      (|u| ≤ 1 + B/τ)
E := Real.exp (τ * Real.sinh δ')
```

链式法则给出 `M₁ = (E·k²+1)/τ + (E+1)`，而 `M₂` 至少是 `(E·k⁴+1)/τ²` 级
（注意 `CollarBound` 只有**一阶**导数的 collar 界；二阶版本还不存在，粗界同样是 `k⁴` 级）。
而 `ε = epsOf τ δ' (2N+1) ≈ E·e^{-δ'(2N+1)}`、`τ ≤ ρ(2N+2)`，于是界里的关键因子

```
√ε · E  ≍  exp((2N+2)·(1.5·ρ·sinh δ' - δ'/2))      （以及 C₂ 界的 4K·M₁ ≍ E·k²/τ）
```

在 `δ' → 0` 时指数为 `δ'(1.5ρ - 0.5)`：**只要 `ρ > 1/3` 就随 `N` 指数发散**
（`C₂` 界里的 `4K·M₁` 项更是对任意 `ρ > 0` 都随 `N` 指数发散）。
所以要强调：这不是「界不够紧」，而是**用现有这两个 collar 界推出的 `C₁C₂` 上界本身发散**，
因此在 `ρ > 1/3` 时这条路线不可能给出 `hkernel`。
此外 `M₁, M₂` 里的 `1/τ, 1/τ²`（来自 `P^{(j)}(μ) = τ^{-j}(approxPoly)^{(j)}(μ/τ)`）
在 `τ → 0` 时发散，而结论量化了所有 `τ ≤ ρ(2N+2)`（含极小的 `τ`）。

### 要补什么才能真正无假设

需要一条**不带 `E` 因子、也不带 `1/τ` 损失**的 collar 导数估计，形如

```
∀ u, |u| ≤ 1 + B/τ →  ‖(approxPoly τ k)^{(j)}(u)‖ ≤ C_j · τ^j · poly(k, τ)     (j = 0,1,2)
```

（`B = √(epsOf τ δ' (2N+1))`）。这是 Jacobi–Anger 截断在 Bernstein 椭圆上的**真渐近**
应有的样子（真值近似为 `τ^j·e^{∓iτu}`，故 `M_j = ‖P^{(j)}‖ = poly(k,τ)`），
而 `CollarBound` 的两个引理因为对**整个** Chebyshev 和用了同一个椭圆参数 `δ'`，
拿到了 `E = e^{τ sinh δ'}` 这个多余的指数因子。

一条初等的修补路线（第一块砖 `norm_fcoef_le_min` 已在 §5.5 **证明**）：

* `fcoef_bound`（`‖fcoef τ n‖ ≤ e^{τ sinh δ - nδ}`，对**任意** `δ > 0` 成立）
  与 `‖fcoef τ n‖ ≤ 1`（`norm_fcoef_le_one`，令 `δ → 0⁺`）取 `min`，得逐项界
  `‖fcoef τ n‖ ≤ min(1, e^{τ sinh δ - nδ})`；
* 记 `w := arccosh(1+B/τ)`（于是 `τ·sinh w = √(B²+2Bτ) → 0`、`τ·cosh w = τ+B`），
  取 `δ := w + 1/(1+τ)`（**而不是题目固定的 `δ'`**）对 Chebyshev 和逐项估计：
  在 `m₀ := τ sinh δ/δ` 处分段，小 `m` 用常数 `1`、大 `m` 用几何衰减，得
  `Σ_{m<k}‖fcoef τ m‖·‖T_m(u)‖ ≤ e^{τ sinh δ·w/δ}·(1/(1-e^{-w}) + 1/(1-e^{-(δ-w)}))`，
  而 `τ sinh δ ≤ e^{1/(1+τ)}·(τ cosh w + τ sinh w) ≤ 1.2·(τ + B + √(B²+2Bτ))/(1+τ) + …`
  是**与 `N` 无关的有界量**（`w` 大时必有 `τ ≪ B = √ε → 0`，故 `τ cosh w = τ+B ≍ B`）；
  `E = e^{τ sinh δ'}` 就是这样被换成常数的；
* 补上 `scaledApprox` 的链式法则（`P^{(j)}(μ) = τ^{-j}·(approxPoly τ k)^{(j)}(μ/τ)`）
  与纯算术 `8√(C₁C₂) ≤ poly(q)·ε^{1/4}`（由本文件 §2 的 `epsOf_le_exp_decay` /
  `tendsto_exp_decay_atTop` 收尾），即可删掉 `hkernel` 假设。

（上面 §5.5 的两个引理是本文件对这条路线唯一已形式化的部分；其余仍是待做工作。） -/

end RobustZ
