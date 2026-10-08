import RobustZ.Approx

/-!
# M4b：逼近误差界的**频带形式**

`RobustZ.exp_sub_approxPoly_le` 给出的是「`θ` 形式」的界：
`‖e^{-iτcos θ} − P(cos θ)‖ ≤ |c_k| + 4e^{τ sinh δ}e^{-δk}/(1−e^{−δ})`。

本文件把它搬到**频带形式**（`μ ∈ [−τ, τ]`）：对 `|μ| ≤ τ` 有
`‖e^{−iμ} − P(μ/τ)‖ ≤ |c_k| + 4e^{τ sinh δ}e^{-δk}/(1−e^{−δ})`。

做法：令 `u = μ/τ ∈ [−1,1]`、`θ = arccos u`，则 `cos θ = u`、`μ = τ cos θ`；
若 `θ = 0`（即 `u = 1`，`μ = τ`），改用 `θ = 2π`（`cos 2π = 1`）。
-/

noncomputable section

open Complex

namespace RobustZ

open scoped Real

/-- 辅助形式：只要 `μ = τ cos θ`（`θ ∈ (0, 2π]`），误差界即成立。 -/
lemma exp_sub_approxPoly_band_of_eq_cos (τ : ℝ) (hτ : 0 < τ) {δ : ℝ} (hδ : 0 < δ)
    {k : ℕ} (hk : 1 ≤ k) {μ θ : ℝ} (hθ : θ ∈ Set.Ioc 0 (2 * Real.pi))
    (hμθ : μ = τ * Real.cos θ) :
    ‖Complex.exp (-(μ : ℂ) * Complex.I) - (approxPoly τ k).eval ((μ / τ : ℝ) : ℂ)‖
      ≤ ‖fcoef τ (k : ℤ)‖
        + 4 * Real.exp (τ * Real.sinh δ) * Real.exp (-δ) ^ k / (1 - Real.exp (-δ)) := by
  have hmain := exp_sub_approxPoly_le τ hτ.le hδ hθ hk
  have hdiv : (μ / τ : ℝ) = Real.cos θ := by
    rw [hμθ, mul_div_cancel_left₀ _ (ne_of_gt hτ)]
  have hexp : -((μ : ℂ)) * Complex.I = -(τ : ℂ) * Complex.I * Complex.cos (θ : ℂ) := by
    rw [hμθ, ← Complex.ofReal_cos]
    push_cast
    ring
  rw [hdiv, hexp]
  exact hmain

/-- **逼近误差界（频带形式）**：对 `|μ| ≤ τ`，
`‖e^{−iμ} − P(μ/τ)‖ ≤ |c_k| + 4e^{τ sinh δ}e^{-δk}/(1−e^{−δ})`。 -/
lemma exp_sub_approxPoly_band (τ : ℝ) (hτ : 0 < τ) {δ : ℝ} (hδ : 0 < δ) {k : ℕ}
    (hk : 1 ≤ k) :
    ∀ μ : ℝ, |μ| ≤ τ →
      ‖Complex.exp (-(μ : ℂ) * Complex.I) - (approxPoly τ k).eval ((μ / τ : ℝ) : ℂ)‖
        ≤ ‖fcoef τ (k : ℤ)‖
          + 4 * Real.exp (τ * Real.sinh δ) * Real.exp (-δ) ^ k / (1 - Real.exp (-δ)) := by
  intro μ hμ
  have hμ_ge : -τ ≤ μ := (abs_le.mp hμ).1
  have hμ_le : μ ≤ τ := (abs_le.mp hμ).2
  set u : ℝ := μ / τ with hu
  have hu_le : u ≤ 1 := by
    rw [hu, div_le_one hτ]
    exact hμ_le
  have hu_ge : -1 ≤ u := by
    rw [hu, le_div_iff₀ hτ]
    linarith
  have hcos : Real.cos (Real.arccos u) = u := Real.cos_arccos hu_ge hu_le
  have hμu : μ = τ * u := by
    rw [hu]
    field_simp
  rcases eq_or_lt_of_le (Real.arccos_nonneg u) with h0 | hpos
  · -- 端点 `μ = τ`：`u = 1`，改用 `θ = 2π`
    have hu1 : u = 1 := by rw [← hcos, ← h0, Real.cos_zero]
    refine exp_sub_approxPoly_band_of_eq_cos τ hτ hδ hk (θ := 2 * Real.pi)
      ⟨by positivity, le_refl _⟩ ?_
    rw [hμu, hu1, Real.cos_two_pi, mul_one]
  · -- 内部：直接用 `θ = arccos u`
    have hπ : Real.arccos u ≤ 2 * Real.pi := by
      have h := Real.arccos_le_pi u
      linarith [Real.pi_pos]
    exact exp_sub_approxPoly_band_of_eq_cos τ hτ hδ hk (θ := Real.arccos u)
      ⟨hpos, hπ⟩ (by rw [hμu, hcos])

/-- **显式可调用的频带逼近接口**：存在与 `k` 无关的常数 `ε > 0`，使得对每个 `k ≥ 1`
与每个 `|μ| ≤ τ` 都有
`‖e^{−iμ} − P_k(μ/τ)‖ ≤ ε·(e^{−δk}/(1−e^{−δ})) + |c_k|`。 -/
lemma exists_approx_band (τ : ℝ) (hτ : 0 < τ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ k ≥ 1, ∀ μ : ℝ, |μ| ≤ τ →
      ‖Complex.exp (-(μ : ℂ) * Complex.I) - (approxPoly τ k).eval ((μ / τ : ℝ) : ℂ)‖
        ≤ ε * (Real.exp (-δ) ^ k * (1 / (1 - Real.exp (-δ))))
          + ‖fcoef τ (k : ℤ)‖ := by
  refine ⟨4 * Real.exp (τ * Real.sinh δ), by positivity, ?_⟩
  intro k hk μ hμ
  have h1 := exp_sub_approxPoly_band τ hτ hδ hk μ hμ
  have hlt1 : Real.exp (-δ) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hne : 1 - Real.exp (-δ) ≠ 0 := sub_ne_zero.mpr (ne_of_gt hlt1)
  have hEq : 4 * Real.exp (τ * Real.sinh δ) * Real.exp (-δ) ^ k / (1 - Real.exp (-δ))
      = 4 * Real.exp (τ * Real.sinh δ)
        * (Real.exp (-δ) ^ k * (1 / (1 - Real.exp (-δ)))) := by
    field_simp
  rw [hEq] at h1
  linarith [h1]

/-- 频带形式 + 系数界 `|c_k| ≤ e^{τ sinh δ − kδ}` 的**完全显式**版本（`k ≥ 1`）。 -/
lemma exp_sub_approxPoly_band_explicit (τ : ℝ) (hτ : 0 < τ) {δ : ℝ} (hδ : 0 < δ)
    {k : ℕ} (hk : 1 ≤ k) :
    ∀ μ : ℝ, |μ| ≤ τ →
      ‖Complex.exp (-(μ : ℂ) * Complex.I) - (approxPoly τ k).eval ((μ / τ : ℝ) : ℂ)‖
        ≤ Real.exp (τ * Real.sinh δ - (k : ℤ) * δ)
          + 4 * Real.exp (τ * Real.sinh δ) * Real.exp (-δ) ^ k / (1 - Real.exp (-δ)) := by
  intro μ hμ
  have h1 := exp_sub_approxPoly_band τ hτ hδ hk μ hμ
  have h2 := fcoef_bound τ hτ.le hδ (k : ℤ) (by exact_mod_cast hk)
  linarith [h1, h2]

/-- **最终干净接口（几何衰减）**：存在与 `k`、`μ` 无关的常数 `ε > 0`，使对每个 `k ≥ 1`
与每个 `|μ| ≤ τ` 都有 `‖e^{−iμ} − P_k(μ/τ)‖ ≤ ε·e^{−δk}`。
（取 `ε = e^{τ sinh δ}·(1 + 4/(1−e^{−δ}))`：该项把 `|c_k| ≤ e^{τ sinh δ − kδ}` 也吸收了。） -/
lemma exists_approx_band_geometric (τ : ℝ) (hτ : 0 < τ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ k ≥ 1, ∀ μ : ℝ, |μ| ≤ τ →
      ‖Complex.exp (-(μ : ℂ) * Complex.I) - (approxPoly τ k).eval ((μ / τ : ℝ) : ℂ)‖
        ≤ ε * Real.exp (-δ) ^ k := by
  have hlt1 : Real.exp (-δ) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hpos1 : 0 < 1 - Real.exp (-δ) := by linarith
  refine ⟨Real.exp (τ * Real.sinh δ) * (1 + 4 / (1 - Real.exp (-δ))), ?_, ?_⟩
  · have h2 : 0 < 4 / (1 - Real.exp (-δ)) := div_pos (by norm_num) hpos1
    exact mul_pos (Real.exp_pos _) (by linarith)
  · intro k hk μ hμ
    have h1 := exp_sub_approxPoly_band_explicit τ hτ hδ hk μ hμ
    have hexp_neg : Real.exp (-((k : ℤ) * δ)) = Real.exp (-δ) ^ k := by
      have hcast : -((k : ℤ) * δ) = (k : ℝ) * (-δ) := by
        push_cast
        ring
      rw [hcast, Real.exp_nat_mul]
    have hkδ : Real.exp (τ * Real.sinh δ - (k : ℤ) * δ)
        = Real.exp (τ * Real.sinh δ) * Real.exp (-δ) ^ k := by
      rw [sub_eq_add_neg, Real.exp_add, hexp_neg]
    rw [hkδ] at h1
    have hEq : Real.exp (τ * Real.sinh δ) * (1 + 4 / (1 - Real.exp (-δ)))
          * Real.exp (-δ) ^ k
        = Real.exp (τ * Real.sinh δ) * Real.exp (-δ) ^ k
          + 4 * Real.exp (τ * Real.sinh δ) * Real.exp (-δ) ^ k
            / (1 - Real.exp (-δ)) := by
      field_simp
    rw [hEq]
    exact h1

end RobustZ
