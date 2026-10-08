import RobustZ.Smearing

/-!
# M3：截断函数导数的标度界

对 `cutoff τ B μ = σ((τ + B - |μ|) / B)`（其中 `σ = Real.smoothTransition`）证明：存在常数
`K > 0`，使得对任意 `B > 0` 与任意 `μ`

* `|deriv (cutoff τ B) μ| ≤ K / B`
* `|deriv (deriv (cutoff τ B)) μ| ≤ K / B ^ 2`

证明思路：

* `σ` 在 `(-∞, 0]` 上恒为 `0`、在 `[1, ∞)` 上恒为 `1`，故 `deriv σ` 与 `deriv (deriv σ)`
  在 `(0,1)` 之外恒为零；它们连续，于是由 `[0,1]` 的紧性得到全局界 `K₁`、`K₂`。
* 链式法则：`μ > 0` 时 `cutoff τ B =ᶠ[𝓝 μ] σ ∘ ((τ + B - ·)/B)`，`μ < 0` 时
  `cutoff τ B =ᶠ[𝓝 μ] σ ∘ ((τ + B + ·)/B)`；仿射内层的导数绝对值为 `1/B`、二阶导为 `0`。
* `μ = 0` 时 `cutoff τ B` 在 `0` 的邻域（半径 `τ` 的球）内恒等于 `1`，故各阶导数在 `0` 处为 `0`。

-/

noncomputable section

namespace RobustZ

open scoped Real
open Filter

/-! ### 光滑过渡函数导数的全局界 -/

private lemma deriv_smoothTransition_eq_zero_of_neg {y : ℝ} (hy : y < 0) :
    deriv Real.smoothTransition y = 0 := by
  have hev : Real.smoothTransition =ᶠ[nhds y] fun _ : ℝ => (0 : ℝ) := by
    filter_upwards [isOpen_Iio.mem_nhds hy] with z hz
    exact Real.smoothTransition.zero_of_nonpos hz.le
  rw [hev.deriv_eq]
  exact deriv_const y 0

private lemma deriv_smoothTransition_eq_zero_of_one_lt {y : ℝ} (hy : 1 < y) :
    deriv Real.smoothTransition y = 0 := by
  have hev : Real.smoothTransition =ᶠ[nhds y] fun _ : ℝ => (1 : ℝ) := by
    filter_upwards [isOpen_Ioi.mem_nhds hy] with z hz
    exact Real.smoothTransition.one_of_one_le hz.le
  rw [hev.deriv_eq]
  exact deriv_const y 1

private lemma continuous_deriv_smoothTransition : Continuous (deriv Real.smoothTransition) :=
  (Real.smoothTransition.contDiff (n := 2)).continuous_deriv (by norm_num)

private lemma continuous_deriv2_smoothTransition :
    Continuous (deriv (deriv Real.smoothTransition)) :=
  (ContDiff.deriv' (n := 1) (Real.smoothTransition.contDiff (n := 2))).continuous_deriv
    (le_refl 1)

private lemma differentiable_smoothTransition : Differentiable ℝ Real.smoothTransition :=
  (Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num)

private lemma differentiable_deriv_smoothTransition :
    Differentiable ℝ (deriv Real.smoothTransition) :=
  ContDiff.differentiable_deriv_two (Real.smoothTransition.contDiff (n := 2))

private lemma exists_bound_deriv_smoothTransition :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y : ℝ, |deriv Real.smoothTransition y| ≤ K := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    continuous_deriv_smoothTransition.continuousOn
  refine ⟨max C 0, le_max_right C 0, fun y => ?_⟩
  by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
  · have h1 : |deriv Real.smoothTransition y| ≤ C := by simpa using hC y hy
    exact h1.trans (le_max_left C 0)
  · rw [Set.mem_Icc] at hy
    rcases lt_or_ge y 0 with hy0 | hy0
    · rw [deriv_smoothTransition_eq_zero_of_neg hy0, abs_zero]
      exact le_max_right C 0
    · have hy1 : 1 < y := lt_of_not_ge fun h1 => hy ⟨hy0, h1⟩
      rw [deriv_smoothTransition_eq_zero_of_one_lt hy1, abs_zero]
      exact le_max_right C 0

private lemma exists_bound_deriv2_smoothTransition :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y : ℝ, |deriv (deriv Real.smoothTransition) y| ≤ K := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    continuous_deriv2_smoothTransition.continuousOn
  refine ⟨max C 0, le_max_right C 0, fun y => ?_⟩
  by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
  · have h1 : |deriv (deriv Real.smoothTransition) y| ≤ C := by simpa using hC y hy
    exact h1.trans (le_max_left C 0)
  · have hz : deriv Real.smoothTransition =ᶠ[nhds y] fun _ : ℝ => (0 : ℝ) := by
      rw [Set.mem_Icc] at hy
      rcases lt_or_ge y 0 with hy0 | hy0
      · filter_upwards [isOpen_Iio.mem_nhds hy0] with w hw
        exact deriv_smoothTransition_eq_zero_of_neg hw
      · have hy1 : 1 < y := lt_of_not_ge fun h1 => hy ⟨hy0, h1⟩
        filter_upwards [isOpen_Ioi.mem_nhds hy1] with w hw
        exact deriv_smoothTransition_eq_zero_of_one_lt hw
    rw [hz.deriv_eq, deriv_const y 0, abs_zero]
    exact le_max_right C 0

/-! ### 仿射内层的链式法则 -/

private lemma deriv_comp_sub_div {F : ℝ → ℝ} (dF : Differentiable ℝ F) (c B x : ℝ) :
    deriv (fun y : ℝ => F ((c - y) / B)) x = deriv F ((c - x) / B) * (-(1 / B)) := by
  have h1 : deriv (fun y : ℝ => (c - y) / B) x = -(1 / B) := by
    rw [deriv_div_const B, deriv_const_sub c, deriv_id'']
    ring
  have h4 : DifferentiableAt ℝ (fun y : ℝ => (c - y) / B) x := by fun_prop
  have h5 : deriv (fun y : ℝ => F ((c - y) / B)) x
      = deriv F ((c - x) / B) * deriv (fun y : ℝ => (c - y) / B) x := by
    simpa only [Function.comp_def] using deriv_comp x (dF.differentiableAt) h4
  rw [h5, h1]

private lemma deriv_comp_add_div {F : ℝ → ℝ} (dF : Differentiable ℝ F) (c B x : ℝ) :
    deriv (fun y : ℝ => F ((c + y) / B)) x = deriv F ((c + x) / B) * (1 / B) := by
  have h1 : deriv (fun y : ℝ => (c + y) / B) x = (1 / B) := by
    rw [deriv_div_const B, deriv_const_add c, deriv_id'']
  have h4 : DifferentiableAt ℝ (fun y : ℝ => (c + y) / B) x := by fun_prop
  have h5 : deriv (fun y : ℝ => F ((c + y) / B)) x
      = deriv F ((c + x) / B) * deriv (fun y : ℝ => (c + y) / B) x := by
    simpa only [Function.comp_def] using deriv_comp x (dF.differentiableAt) h4
  rw [h5, h1]

/-! ### `cutoff` 在 `μ ≠ 0` 处的导数公式 -/

private lemma deriv_cutoff_of_pos {τ B μ : ℝ} (hμ : 0 < μ) :
    deriv (cutoff τ B) μ
      = deriv Real.smoothTransition ((τ + B - μ) / B) * (-(1 / B)) := by
  have hev : cutoff τ B =ᶠ[nhds μ] fun y : ℝ => Real.smoothTransition ((τ + B - y) / B) := by
    filter_upwards [isOpen_Ioi.mem_nhds hμ] with y hy
    simp only [cutoff]
    rw [abs_of_pos hy]
  rw [hev.deriv_eq]
  exact deriv_comp_sub_div differentiable_smoothTransition (τ + B) B μ

private lemma deriv_cutoff_of_neg {τ B μ : ℝ} (hμ : μ < 0) :
    deriv (cutoff τ B) μ
      = deriv Real.smoothTransition ((τ + B + μ) / B) * (1 / B) := by
  have hev : cutoff τ B =ᶠ[nhds μ] fun y : ℝ => Real.smoothTransition ((τ + B + y) / B) := by
    filter_upwards [isOpen_Iio.mem_nhds hμ] with y hy
    simp only [cutoff]
    rw [abs_of_neg hy]
    ring_nf
  rw [hev.deriv_eq]
  exact deriv_comp_add_div differentiable_smoothTransition (τ + B) B μ

private lemma deriv2_cutoff_of_pos {τ B μ : ℝ} (hμ : 0 < μ) :
    deriv (deriv (cutoff τ B)) μ
      = deriv (deriv Real.smoothTransition) ((τ + B - μ) / B) * ((1 / B) * (1 / B)) := by
  have hpt : deriv (cutoff τ B) =ᶠ[nhds μ]
      fun x : ℝ => deriv Real.smoothTransition ((τ + B - x) / B) * (-(1 / B)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hμ] with x hx
    exact deriv_cutoff_of_pos hx
  rw [hpt.deriv_eq]
  have hdiff : DifferentiableAt ℝ (fun x : ℝ => deriv Real.smoothTransition ((τ + B - x) / B))
      μ := differentiable_deriv_smoothTransition.differentiableAt.comp μ (by fun_prop)
  rw [deriv_mul_const hdiff (-(1 / B)),
    deriv_comp_sub_div differentiable_deriv_smoothTransition (τ + B) B μ]
  ring

private lemma deriv2_cutoff_of_neg {τ B μ : ℝ} (hμ : μ < 0) :
    deriv (deriv (cutoff τ B)) μ
      = deriv (deriv Real.smoothTransition) ((τ + B + μ) / B) * ((1 / B) * (1 / B)) := by
  have hpt : deriv (cutoff τ B) =ᶠ[nhds μ]
      fun x : ℝ => deriv Real.smoothTransition ((τ + B + x) / B) * (1 / B) := by
    filter_upwards [isOpen_Iio.mem_nhds hμ] with x hx
    exact deriv_cutoff_of_neg hx
  rw [hpt.deriv_eq]
  have hdiff : DifferentiableAt ℝ (fun x : ℝ => deriv Real.smoothTransition ((τ + B + x) / B))
      μ := differentiable_deriv_smoothTransition.differentiableAt.comp μ (by fun_prop)
  rw [deriv_mul_const hdiff (1 / B),
    deriv_comp_add_div differentiable_deriv_smoothTransition (τ + B) B μ]
  ring

/-! ### 主定理 -/

/-- 截断函数的一阶、二阶导数都被 `K / B`、`K / B ^ 2` 控制（`K` 只依赖 `τ`）。 -/
lemma exists_deriv_cutoff_bound (τ : ℝ) (hτ : 0 < τ) :
    ∃ K : ℝ, 0 < K ∧ ∀ B : ℝ, 0 < B →
      (∀ μ : ℝ, |deriv (cutoff τ B) μ| ≤ K / B) ∧
      (∀ μ : ℝ, |deriv (deriv (cutoff τ B)) μ| ≤ K / B ^ 2) := by
  obtain ⟨K₁, hK₁0, hK₁⟩ := exists_bound_deriv_smoothTransition
  obtain ⟨K₂, hK₂0, hK₂⟩ := exists_bound_deriv2_smoothTransition
  have hK₁le : K₁ ≤ max K₁ K₂ + 1 :=
    le_trans (le_max_left K₁ K₂) (le_add_of_nonneg_right zero_le_one)
  have hK₂le : K₂ ≤ max K₁ K₂ + 1 :=
    le_trans (le_max_right K₁ K₂) (le_add_of_nonneg_right zero_le_one)
  have hKpos : (0 : ℝ) < max K₁ K₂ + 1 := by
    have h : (0 : ℝ) ≤ max K₁ K₂ := le_trans hK₁0 (le_max_left K₁ K₂)
    linarith
  refine ⟨max K₁ K₂ + 1, hKpos, fun B hB => ⟨?_, ?_⟩⟩
  · intro μ
    rcases eq_or_ne μ 0 with rfl | hne
    · have hev : cutoff τ B =ᶠ[nhds (0 : ℝ)] fun _ : ℝ => (1 : ℝ) := by
        filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hτ] with x hx
        refine cutoff_eq_one hB ?_
        rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hx
        exact le_of_lt (by simpa using hx)
      rw [hev.deriv_eq, deriv_const (0 : ℝ) 1, abs_zero]
      exact div_nonneg (by linarith [le_max_left K₁ K₂]) hB.le
    · rcases lt_or_gt_of_ne hne with hneg | hpos
      · rw [deriv_cutoff_of_neg hneg, abs_mul, abs_of_pos (one_div_pos.mpr hB)]
        calc |deriv Real.smoothTransition ((τ + B + μ) / B)| * (1 / B)
            ≤ K₁ * (1 / B) := mul_le_mul_of_nonneg_right (hK₁ _) (by positivity)
          _ = K₁ / B := by ring
          _ ≤ (max K₁ K₂ + 1) / B := by
              rw [div_eq_mul_inv, div_eq_mul_inv]
              exact mul_le_mul_of_nonneg_right hK₁le (by positivity)
      · rw [deriv_cutoff_of_pos hpos, abs_mul, abs_neg, abs_of_pos (one_div_pos.mpr hB)]
        calc |deriv Real.smoothTransition ((τ + B - μ) / B)| * (1 / B)
            ≤ K₁ * (1 / B) := mul_le_mul_of_nonneg_right (hK₁ _) (by positivity)
          _ = K₁ / B := by ring
          _ ≤ (max K₁ K₂ + 1) / B := by
              rw [div_eq_mul_inv, div_eq_mul_inv]
              exact mul_le_mul_of_nonneg_right hK₁le (by positivity)
  · intro μ
    rcases eq_or_ne μ 0 with rfl | hne
    · have hball : ∀ x ∈ Metric.ball (0 : ℝ) τ, cutoff τ B x = 1 := fun x hx => by
        refine cutoff_eq_one hB ?_
        rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hx
        exact le_of_lt (by simpa using hx)
      have hz : deriv (cutoff τ B) =ᶠ[nhds (0 : ℝ)] fun _ : ℝ => (0 : ℝ) := by
        filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hτ] with x hx
        have hx' : cutoff τ B =ᶠ[nhds x] fun _ : ℝ => (1 : ℝ) := by
          filter_upwards [Metric.isOpen_ball.mem_nhds hx] with y hy
          exact hball y hy
        rw [hx'.deriv_eq, deriv_const x 1]
      rw [hz.deriv_eq, deriv_const (0 : ℝ) 0, abs_zero]
      exact div_nonneg hKpos.le (by positivity)
    · rcases lt_or_gt_of_ne hne with hneg | hpos
      · rw [deriv2_cutoff_of_neg hneg, abs_mul,
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 / B) * (1 / B))]
        calc |deriv (deriv Real.smoothTransition) ((τ + B + μ) / B)| * ((1 / B) * (1 / B))
            ≤ K₂ * ((1 / B) * (1 / B)) :=
              mul_le_mul_of_nonneg_right (hK₂ _) (by positivity)
          _ = K₂ / B ^ 2 := by rw [one_div_mul_one_div, pow_two]; ring
          _ ≤ (max K₁ K₂ + 1) / B ^ 2 := by
              rw [div_eq_mul_inv, div_eq_mul_inv]
              exact mul_le_mul_of_nonneg_right hK₂le (by positivity)
      · rw [deriv2_cutoff_of_pos hpos, abs_mul,
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 / B) * (1 / B))]
        calc |deriv (deriv Real.smoothTransition) ((τ + B - μ) / B)| * ((1 / B) * (1 / B))
            ≤ K₂ * ((1 / B) * (1 / B)) :=
              mul_le_mul_of_nonneg_right (hK₂ _) (by positivity)
          _ = K₂ / B ^ 2 := by rw [one_div_mul_one_div, pow_two]; ring
          _ ≤ (max K₁ K₂ + 1) / B ^ 2 := by
              rw [div_eq_mul_inv, div_eq_mul_inv]
              exact mul_le_mul_of_nonneg_right hK₂le (by positivity)

end RobustZ
