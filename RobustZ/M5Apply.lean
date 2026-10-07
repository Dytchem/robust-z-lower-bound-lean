import RobustZ.Final
import RobustZ.CollarBound
import RobustZ.M5Bridge
import RobustZ.SmearingMain

/-!
# M5 组装第一步：把 M3 + M4 应用到 `h(0)`

本文件把两条已冻结的主线接起来。

* **M4**（`Band.exists_approx_band_geometric`）给出带内逼近误差的**显式几何衰减**常数
  `ε_k = e^{τ·sinh δ'}·(1 + 4/(1 − e^{−δ'}))·e^{−δ'k}`，此处记为局部记号 `epsOf τ δ' k`
  （与 `Band.lean` 的证明里取的常数逐字一致，只是多带了 `e^{−δ'k}` 因子）。
* **M3**（`SmearingMain.norm_sum_le_of_moments`）对**任意** `ε > 0` 给出
  `‖Σᵢ cᵢ‖ ≤ 8√(C₁·C₂)`，其中 `C₁ = kernelA τ (√ε) P`、`C₂ = kernelC τ (√ε) P`
  （`kernelA` / `kernelC` 的定义就是那两个显式区间积分）。

取 `τ = (Σⱼθⱼ)/2`、`P = scaledApprox τ k`（`M5Bridge` 的复合多项式）、`ε = epsOf τ δ' k`，
并把左端的 `‖Σᵢcᵢ‖` 换回 `h(0)`（`exists_expSum_data` 的第 4 条 + `h_bounds` 的 `0 ≤ h`），
即得主引理

`h L α θ 0 ≤ 8√( kernelA τ (√(epsOf τ δ' k)) P · kernelC τ (√(epsOf τ δ' k)) P )`。

`τ = 0` 的退化情形由 `h_zero_of_admissible_of_cost_eq_zero` 处理（此时 `h(0) = 0`，
右端非负），故主引理**不含** `τ > 0` 假设；带假设的版本是 `h_zero_le_of_admissible_pos`。
-/

noncomputable section

namespace RobustZ

open scoped Real
open Filter MeasureTheory

/-! ## (1) M4 的显式常数 `epsOf` -/

/-- M4（`Band.exists_approx_band_geometric`）中那个"与 `k`、`μ` 无关"的常数，
乘上几何因子 `e^{−δ'k}` 之后的显式值：

`epsOf τ δ' k = e^{τ·sinh δ'}·(1 + 4/(1 − e^{−δ'}))·e^{−δ'k}`。 -/
noncomputable def epsOf (τ δ' : ℝ) (k : ℕ) : ℝ :=
  Real.exp (τ * Real.sinh δ') * (1 + 4 / (1 - Real.exp (-δ'))) * Real.exp (-δ') ^ k

/-- `epsOf τ δ' k > 0`（`δ' > 0`，`τ` 任意）。 -/
lemma epsOf_pos {δ' : ℝ} (hδ' : 0 < δ') (τ : ℝ) (k : ℕ) : 0 < epsOf τ δ' k := by
  have hlt1 : Real.exp (-δ') < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hpos1 : 0 < 1 - Real.exp (-δ') := by linarith
  have h4 : 0 < 4 / (1 - Real.exp (-δ')) := div_pos (by norm_num) hpos1
  rw [epsOf]
  exact mul_pos (mul_pos (Real.exp_pos _) (by linarith)) (pow_pos (Real.exp_pos _) k)

/-- **M4（显式常数版）**：`k ≥ 1`、`|μ| ≤ τ` 时
`‖e^{−iμ} − P_k(μ/τ)‖ ≤ epsOf τ δ' k`。

证明与 `Band.exists_approx_band_geometric` 相同（用
`Band.exp_sub_approxPoly_band_explicit`），只是把常数写成 `epsOf` 的形式。 -/
lemma approx_band_epsOf (τ : ℝ) (hτ : 0 < τ) {δ' : ℝ} (hδ' : 0 < δ')
    {k : ℕ} (hk : 1 ≤ k) {μ : ℝ} (hμ : |μ| ≤ τ) :
    ‖Complex.exp (-(μ : ℂ) * Complex.I) - (approxPoly τ k).eval ((μ / τ : ℝ) : ℂ)‖
      ≤ epsOf τ δ' k := by
  have h1 := exp_sub_approxPoly_band_explicit τ hτ hδ' hk μ hμ
  have hlt1 : Real.exp (-δ') < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hpos1 : 0 < 1 - Real.exp (-δ') := by linarith
  have hexp_neg : Real.exp (-((k : ℤ) * δ')) = Real.exp (-δ') ^ k := by
    have hcast : -((k : ℤ) * δ') = (k : ℝ) * (-δ') := by
      push_cast
      ring
    rw [hcast, Real.exp_nat_mul]
  have hkδ : Real.exp (τ * Real.sinh δ' - (k : ℤ) * δ')
      = Real.exp (τ * Real.sinh δ') * Real.exp (-δ') ^ k := by
    rw [sub_eq_add_neg, Real.exp_add, hexp_neg]
  rw [hkδ] at h1
  have hEq : epsOf τ δ' k
      = Real.exp (τ * Real.sinh δ') * Real.exp (-δ') ^ k
        + 4 * Real.exp (τ * Real.sinh δ') * Real.exp (-δ') ^ k / (1 - Real.exp (-δ')) := by
    rw [epsOf]
    field_simp
  rw [hEq]
  exact h1

/-- **M4（显式常数版，`scaledApprox` 形式）**：M3 需要的是 `μ` 处的多项式，故把
`M5Bridge.scaledApprox_eval` 接在 `approx_band_epsOf` 前面。 -/
lemma scaledApprox_band_epsOf (τ : ℝ) (hτ : 0 < τ) {δ' : ℝ} (hδ' : 0 < δ')
    {k : ℕ} (hk : 1 ≤ k) {μ : ℝ} (hμ : |μ| ≤ τ) :
    ‖Complex.exp (-(μ : ℂ) * Complex.I) - (scaledApprox τ k).eval ((μ : ℂ))‖
      ≤ epsOf τ δ' k := by
  rw [scaledApprox_eval τ (ne_of_gt hτ) k μ]
  exact approx_band_epsOf τ hτ hδ' hk hμ

/-! ## (2) 主引理（非退化情形 `τ > 0`） -/

set_option linter.style.haveILetI false in
/-- **M3 + M4 应用到 `h(0)`（`τ = (Σθ)/2 > 0` 情形）**。 -/
lemma h_zero_le_of_admissible_pos {N : ℕ} {φ : ℝ} {L : ℕ} {α θ : Fin L → ℝ}
    (hAdm : Admissible N φ L α θ) {δ' : ℝ} (hδ' : 0 < δ')
    {k : ℕ} (hk : 1 ≤ k) (hdeg : k + 1 ≤ 2 * N + 2)
    (hτ : 0 < (∑ j, θ j) / 2) :
    h L α θ 0 ≤ 8 * Real.sqrt
      (kernelA ((∑ j, θ j) / 2) (Real.sqrt (epsOf ((∑ j, θ j) / 2) δ' k))
          (scaledApprox ((∑ j, θ j) / 2) k)
        * kernelC ((∑ j, θ j) / 2) (Real.sqrt (epsOf ((∑ j, θ j) / 2) δ' k))
          (scaledApprox ((∑ j, θ j) / 2) k)) := by
  obtain ⟨ι, hι, c, ν, hν, hf, hmom, h0⟩ := exists_expSum_data N φ L α θ hAdm
  letI : Fintype ι := hι
  have hεpos : 0 < epsOf ((∑ j, θ j) / 2) δ' k := epsOf_pos hδ' _ k
  -- 多项式的次数条件（`hdeg` + `scaledApprox_natDegree_lt`）
  have hPdeg : (scaledApprox ((∑ j, θ j) / 2) k).natDegree < 2 * N + 2 :=
    lt_of_lt_of_le (scaledApprox_natDegree_lt _ k) hdeg
  -- 矩条件
  have hmom' : ∑ i, Complex.exp ((ν i : ℂ) * Complex.I)
      * (scaledApprox ((∑ j, θ j) / 2) k).eval ((ν i : ℂ)) * c i = 0 :=
    hmom (scaledApprox ((∑ j, θ j) / 2) k) hPdeg
  -- 带内逼近（M4）
  have hPε : ∀ μ : ℝ, |μ| ≤ (∑ j, θ j) / 2 →
      ‖Complex.exp (-(μ : ℂ) * Complex.I)
          - (scaledApprox ((∑ j, θ j) / 2) k).eval ((μ : ℂ))‖
        ≤ epsOf ((∑ j, θ j) / 2) δ' k :=
    fun μ hμ => scaledApprox_band_epsOf _ hτ hδ' hk hμ
  -- 指数和的一致界（由 `‖h‖ ≤ 2` 反推）
  have hbdd : ∀ lam : ℝ,
      ‖∑ i, Complex.exp ((((ν i * lam : ℝ)) : ℂ) * Complex.I) * c i‖ ≤ 2 := by
    intro lam
    rw [← (hf lam).2]
    exact (hf lam).1
  -- 核可积性
  have hint : Integrable (fun t : ℝ => kernel ((∑ j, θ j) / 2)
      (Real.sqrt (epsOf ((∑ j, θ j) / 2) δ' k))
      (scaledApprox ((∑ j, θ j) / 2) k) t) :=
    integrable_kernel _ _ hτ (Real.sqrt_pos_of_pos hεpos) _
  -- M3
  have hmain := norm_sum_le_of_moments (τ := (∑ j, θ j) / 2)
    (ε := epsOf ((∑ j, θ j) / 2) δ' k) c ν hτ hεpos hν
    (scaledApprox ((∑ j, θ j) / 2) k) hPε hmom' hbdd hint
  -- 左端换算 `‖Σᵢcᵢ‖ = h(0)`
  have hnorm : ‖∑ i, c i‖ = h L α θ 0 := by
    rw [← h0, Complex.norm_def, Complex.normSq_ofReal,
      Real.sqrt_mul_self (h_bounds L α θ 0).1]
  -- 结论里的 `kernelA` / `kernelC` 就是 M3 结论中的两个积分
  simp only [kernelA, kernelC]
  rw [hnorm] at hmain
  exact hmain

/-! ## (3) 主引理（含 `τ = 0` 退化情形） -/

/-- **M3 + M4 应用到 `h(0)`**：对 admissible 构造、任意 `δ' > 0` 与 `1 ≤ k`、`k+1 ≤ 2N+2`，

`h(0) ≤ 8√( kernelA τ (√(epsOf τ δ' k)) (scaledApprox τ k)
             · kernelC τ (√(epsOf τ δ' k)) (scaledApprox τ k) )`，`τ = (Σⱼθⱼ)/2`。

`τ = 0` 时由 `h_zero_of_admissible_of_cost_eq_zero` 得 `h(0) = 0`，右端非负，故无需 `τ > 0`。 -/
lemma h_zero_le_of_admissible {N : ℕ} {φ : ℝ} {L : ℕ} {α θ : Fin L → ℝ}
    (hAdm : Admissible N φ L α θ) {δ' : ℝ} (hδ' : 0 < δ')
    {k : ℕ} (hk : 1 ≤ k) (hdeg : k + 1 ≤ 2 * N + 2) :
    h L α θ 0 ≤ 8 * Real.sqrt
      (kernelA ((∑ j, θ j) / 2) (Real.sqrt (epsOf ((∑ j, θ j) / 2) δ' k))
          (scaledApprox ((∑ j, θ j) / 2) k)
        * kernelC ((∑ j, θ j) / 2) (Real.sqrt (epsOf ((∑ j, θ j) / 2) δ' k))
          (scaledApprox ((∑ j, θ j) / 2) k)) := by
  by_cases hτ0 : (∑ j, θ j) / 2 = 0
  · -- 退化情形：`Σθ = 0`（`Admissible` 给 `θ ≥ 0`）⟹ `θ ≡ 0` ⟹ `h(0) = 0`
    have hsum0 : ∑ j, θ j = 0 := by linarith
    rw [h_zero_of_admissible_of_cost_eq_zero hAdm hsum0]
    exact mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  · refine h_zero_le_of_admissible_pos hAdm hδ' hk hdeg ?_
    exact lt_of_le_of_ne
      (div_nonneg (Finset.sum_nonneg fun j _ => hAdm.1 j) (by norm_num)) (Ne.symm hτ0)

/-! ## (4) 论文参数 `q = 2N+2` 的特化（`k = 2N+1`） -/

/-- **主引理的 `k = 2N+1` 特化**：取多项式次数上限的最后一档（`k+1 = 2N+2`，即论文的
`q = 2N+2`），两个侧条件 `1 ≤ k` 与 `k+1 ≤ 2N+2` 自动满足，逼近误差衰减到
`epsOf τ δ' (2N+1) ≍ e^{τ·sinh δ'}·e^{−δ'(2N+1)}`。 -/
lemma h_zero_le_of_admissible_twoN_add_one {N : ℕ} {φ : ℝ} {L : ℕ} {α θ : Fin L → ℝ}
    (hAdm : Admissible N φ L α θ) {δ' : ℝ} (hδ' : 0 < δ') :
    h L α θ 0 ≤ 8 * Real.sqrt
      (kernelA ((∑ j, θ j) / 2) (Real.sqrt (epsOf ((∑ j, θ j) / 2) δ' (2 * N + 1)))
          (scaledApprox ((∑ j, θ j) / 2) (2 * N + 1))
        * kernelC ((∑ j, θ j) / 2) (Real.sqrt (epsOf ((∑ j, θ j) / 2) δ' (2 * N + 1)))
          (scaledApprox ((∑ j, θ j) / 2) (2 * N + 1))) :=
  h_zero_le_of_admissible hAdm hδ' (by omega) (by omega)

end RobustZ
