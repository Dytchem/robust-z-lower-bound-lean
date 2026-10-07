import RobustZ.CollarBound
import RobustZ.M5Prelim
import RobustZ.M5Bridge
import RobustZ.SmearingMain
import RobustZ.Liminf

/-!
# M5：定理 `c ≥ 4` 的组装

论文 §2.4 Assembly 的形式化。证明链：

* 反证：固定 `ρ = 1 - δ < 1`，若某 `N` 阶 admissible 构造有 `τ ≤ ρ q`（`q = 2N+2`、`τ = (Σθ)/2`），
  则 M4 给带内逼近误差 `ε ≲ e^{η q}`（`η < 0`），M3（`norm_sum_le_of_moments`）给
  `h(0) = ‖Σcᵢ‖ ≤ 8√(C₁C₂) → 0`；
* 而 `h(0) ≥ 1 − cos(φ/2) > 0` 与 `N` 无关（`HTraceLower.h_zero_ge`），矛盾；
* 故最终 `τ > ρ q`，即 `cost θ = 2τ > 4ρ(N+1)`，再由 `Tmin ≤ cost θ`（对每个 admissible 构造）
  反推 `4ρ(N+1) ≤ Tmin N φ`；
* 用 `liminf_ge_of_eventually` + 上界假设 `hbdd` 收尾，最后 `δ → 0`。
-/

noncomputable section

namespace RobustZ

open Filter MeasureTheory

/-- 端点下界是**正常数**：`0 < φ ≤ π` ⟹ `0 < 1 − cos(φ/2)`。 -/
lemma one_sub_cos_half_pos {φ : ℝ} (hφ0 : 0 < φ) (hφπ : φ ≤ Real.pi) :
    0 < 1 - Real.cos (φ / 2) := by
  have h2 : 0 < φ / 2 := by linarith
  have hpi : φ / 2 ≤ Real.pi := by linarith
  have hlt := Real.cos_lt_cos_of_nonneg_of_le_pi (x := (0 : ℝ)) (y := φ / 2) le_rfl hpi h2
  simpa using hlt

/-- `costs` 里所有元素都 `≥ c` 时，`Tmin ≥ c`。 -/
lemma le_Tmin_of_forall {N : ℕ} {φ c : ℝ} (hne : (costs N φ).Nonempty)
    (h : ∀ T ∈ costs N φ, c ≤ T) : c ≤ Tmin N φ :=
  le_csInf hne h

/-- **最后一公里**：若对每个 `δ ∈ (0,1)`，最终所有 admissible 构造的代价 `≥ 4(1−δ)(N+1)`，
则 `4 ≤ liminf (Tmin N φ / N)`（配 `Tmin` 的上界假设 `hbdd`，这是 Lean 侧 `liminf` 取值域所必需）。 -/
lemma liminf_ge_of_cost_bound {φ : ℝ} (hne : ∀ N, (costs N φ).Nonempty)
    (hbdd : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop (fun N : ℕ => Tmin N φ / N))
    (hcost : ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ᶠ N in Filter.atTop,
      ∀ T ∈ costs N φ, 4 * (1 - δ) * ((N : ℝ) + 1) ≤ T) :
    4 ≤ Filter.liminf (fun N : ℕ => Tmin N φ / N) Filter.atTop := by
  refine liminf_ge_of_eventually (a := fun N : ℕ => Tmin N φ) (c := 4) hbdd ?_
  intro δ hδ
  set δ' : ℝ := min (δ / 4) (1 / 2) with hδ'def
  have hδ'pos : 0 < δ' := lt_min (by linarith) (by norm_num)
  have hδ'lt : δ' < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hδ'le : δ' ≤ δ / 4 := min_le_left _ _
  have hδ'nn : (0:ℝ) < 1 - δ' := by linarith
  filter_upwards [hcost δ' hδ'pos hδ'lt, Filter.eventually_ge_atTop 1] with N hN hN1
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN1
  have hle : 4 * (1 - δ') * ((N : ℝ) + 1) ≤ Tmin N φ :=
    le_Tmin_of_forall (hne N) (fun T hT => hN T hT)
  have h4 : 4 * (1 - δ') ≤ Tmin N φ / N := by
    rw [le_div_iff₀ hNpos]
    have hmono : 4 * (1 - δ') * (N : ℝ) ≤ 4 * (1 - δ') * ((N : ℝ) + 1) := by
      have hpos : (0:ℝ) ≤ 4 * (1 - δ') := by linarith
      nlinarith
    linarith
  linarith

end RobustZ
