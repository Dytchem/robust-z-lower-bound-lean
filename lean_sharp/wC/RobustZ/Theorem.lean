import RobustZ.FinalSmall
import RobustZ.M5Scaled
import RobustZ.Final
import RobustZ.Liminf
import RobustZ.HTraceLower

/-!
# 主定理：`c ≥ 4`（论文 Theorem 1）

把 `FinalSmall.h_zero_small_of_tau_le`（带宽低于阈值时 `h(0)` 被压到端点常数以下）
与 `HTraceLower.h_zero_ge`（`h(0)` 有与 `N` 无关的正下界）冲突，得到
「充分大 `N` 时所有 admissible 构造的代价 `≥ 4(1−δ)(N+1)`」，
再由 `Final.liminf_ge_of_cost_bound` 收尾。
-/

noncomputable section

namespace RobustZ

open Filter

/-- **`c ≥ 4`**，证明版本（`Statement.lean` 里的同名定理给出逐字相同的陈述）。 -/
theorem c_ge_four_proof (φ : ℝ) (hφ0 : 0 < φ) (hφπ : φ ≤ Real.pi)
    (hne : ∀ N, (costs N φ).Nonempty)
    (hbdd : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop (fun N : ℕ => Tmin N φ / N)) :
    4 ≤ Filter.liminf (fun N : ℕ => Tmin N φ / N) Filter.atTop := by
  refine liminf_ge_of_cost_bound hne hbdd ?_
  intro δ hδ hδ1
  have hρ0 : (0:ℝ) < 1 - δ := by linarith
  have hρ1 : 1 - δ < 1 := by linarith
  filter_upwards [h_zero_small_of_tau_le_scaled (φ := φ) hφ0 hφπ hρ0 hρ1] with N hN
  intro T hT
  obtain ⟨L, α, θ, hAdm, rfl⟩ := hT
  by_contra hlt
  have hcost : cost θ < 4 * (1 - δ) * ((N : ℝ) + 1) := not_le.mp hlt
  have hcost2 : (∑ j, θ j) < 4 * (1 - δ) * ((N : ℝ) + 1) := hcost
  have hτ : (∑ j, θ j) / 2 ≤ (1 - δ) * (2 * (N : ℝ) + 2) := by linarith
  have hsmall := hN hAdm hτ
  have hge := h_zero_ge φ hφ0.le hφπ L α θ hAdm.2.1
  linarith

/-- **`c ≥ 4`**（论文 Theorem 1 第一条不等式）：与 `Statement.lean` 里的陈述逐字相同。 -/
theorem c_ge_four (φ : ℝ) (hφ0 : 0 < φ) (hφπ : φ ≤ Real.pi)
    (hne : ∀ N, (costs N φ).Nonempty)
    (hbdd : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop (fun N : ℕ => Tmin N φ / N)) :
    4 ≤ Filter.liminf (fun N : ℕ => Tmin N φ / N) Filter.atTop :=
  c_ge_four_proof φ hφ0 hφπ hne hbdd

/-- **无上界假设的二分版本**：要么结论成立，要么 `T_min N φ / N` 发散到 `+∞`。 -/
theorem c_ge_four_or_grows (φ : ℝ) (hφ0 : 0 < φ) (hφπ : φ ≤ Real.pi)
    (hne : ∀ N, (costs N φ).Nonempty) :
    4 ≤ Filter.liminf (fun N : ℕ => Tmin N φ / N) Filter.atTop ∨
      ∀ M : ℝ, ∀ᶠ N in Filter.atTop, M ≤ Tmin N φ / N := by
  refine liminf_ge_or_tendsto_atTop (a := fun N : ℕ => Tmin N φ) (c := 4) ?_
  intro δ hδ
  set δ' : ℝ := min (δ / 4) (1 / 2) with hδ'def
  have hδ'pos : 0 < δ' := lt_min (by linarith) (by norm_num)
  have hδ'lt : δ' < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hδ'le : δ' ≤ δ / 4 := min_le_left _ _
  filter_upwards [h_zero_small_of_tau_le_scaled (φ := φ) (ρ := 1 - δ') hφ0 hφπ
      (by linarith) (by linarith), Filter.eventually_ge_atTop 1] with N hN hN1
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN1
  have hlow : ∀ T ∈ costs N φ, 4 * (1 - δ') * ((N : ℝ) + 1) ≤ T := by
    intro T hT
    obtain ⟨L, α, θ, hAdm, rfl⟩ := hT
    by_contra hlt
    have hcost : (∑ j, θ j) < 4 * (1 - δ') * ((N : ℝ) + 1) := not_le.mp hlt
    have hτ : (∑ j, θ j) / 2 ≤ (1 - δ') * (2 * (N : ℝ) + 2) := by linarith
    have hsmall := hN hAdm hτ
    have hge := h_zero_ge φ hφ0.le hφπ L α θ hAdm.2.1
    linarith
  have hTmin := le_Tmin_of_forall (hne N) hlow
  have hmono : 4 * (1 - δ') * (N : ℝ) ≤ 4 * (1 - δ') * ((N : ℝ) + 1) := by
    have hpos : (0:ℝ) ≤ 4 * (1 - δ') := by linarith
    nlinarith
  have hkey : 4 - δ ≤ 4 * (1 - δ') := by linarith
  rw [le_div_iff₀ hNpos]
  nlinarith [hkey, hmono, hTmin, hNpos]

end RobustZ
