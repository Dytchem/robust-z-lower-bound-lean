import RobustZ.HTraceLower
import RobustZ.ExpSum
import RobustZ.Liminf

/-!
# M5：最终组装的预备引理（`M5Prelim.lean`）

本文件收集 M5（`4 ≤ liminf T_min(N,φ)/N` 的最终组装）需要的 API 引理，
全部自包含、只用已冻结的依赖（`Statement` / `Elementary` / `HTraceLower` / `ExpSum` / `Liminf`）：

* `h_one` —— `h(1) = 0`（`U_1` 酉）；
* `U_eq_Xrot_of_theta_eq_zero` —— 所有 `θⱼ = 0` 时 `U_λ` 与 `λ` 无关（恒为 `X(Σα)`）；
* `h_zero_eq_h_one_of_theta_eq_zero` / `h_zero_of_theta_eq_zero` / `h_zero_of_cost_eq_zero`
  / `h_zero_of_admissible_of_cost_eq_zero` —— `τ = Σθⱼ = 0` 的退化端点 `h(0) = 0`；
* `exists_expSum_data` —— `h_moments` 与 `h_bounds` 重新打包成 M3 需要的形状；
* `Tmin_le_of_admissible` —— `Tmin N φ ≤ cost θ`。

**记号说明（重要）**：mathlib v4.34.1 中旧名 `Complex.abs` 与 `Complex.norm_ofReal`
已不存在（`#check @Complex.abs` 报 unknown constant；复数模已完全并入 `‖·‖`，
实标量嵌入的模由 `RCLike.norm_ofReal`（`Mathlib/Analysis/RCLike/Basic.lean`）给出）。
因此第 (3) 条中"`|h(λ)| ≤ 2`"写作 `‖(h L α θ lam : ℂ)‖ ≤ 2`；
对实数值 `h` 它正是 `|h lam| = h lam`。证明走
`Complex.norm_def` + `Complex.normSq_ofReal` + `Real.sqrt_mul_self`
（`RCLike.norm_ofReal` 与本文件中的 `Complex.ofReal` 强制转换无法在 `rw` 中 key-match）。
-/

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

namespace RobustZ

/-! ## (1) `h(1) = 0` -/

/-- **(1)** `λ = 1` 时 `U_1ᴴ U_1 = 1`，迹为 `2`，故 `h(1) = 1 - ½·2 = 0`。 -/
lemma h_one (L : ℕ) (α θ : Fin L → ℝ) : h L α θ 1 = 0 := by
  rw [h, U_conjTranspose_mul L α θ 1, trace_one_M2]
  norm_num

/-! ## (2) `τ = 0` 的退化情形 -/

/-- **(2) 辅助**：若所有 `θⱼ = 0`，则每个 `Z(λθⱼ) = 1`，故 `U_λ` 与 `λ` 无关：
它退化为单个 `X` 旋转 `X(Σ_j α_j)`。这是 `U_lam_zero` 的一般化
（`U_lam_zero` 只处理 `λ = 0`）。 -/
lemma U_eq_Xrot_of_theta_eq_zero : ∀ (L : ℕ) (α θ : Fin L → ℝ), (∀ j, θ j = 0) →
    ∀ lam : ℝ, U L α θ lam = Xrot (∑ j, α j) := by
  intro L
  induction L with
  | zero =>
      intro α θ _ lam
      simp [Xrot]
  | succ L ih =>
      intro α θ hθ lam
      rw [U_succ, ih (fun j => α j.castSucc) (fun j => θ j.castSucc)
          (fun j => hθ j.castSucc) lam,
        hθ (Fin.last L), mul_zero, Zrot, zero_smul, NormedSpace.exp_zero, Matrix.mul_one,
        Xrot_add, Fin.sum_univ_castSucc]

/-- **(2) 形式一**：`θ ≡ 0` 时 `U_0 = U_1`，故 `h(0) = h(1)`。 -/
lemma h_zero_eq_h_one_of_theta_eq_zero (L : ℕ) (α θ : Fin L → ℝ) (hθ : ∀ j, θ j = 0) :
    h L α θ 0 = h L α θ 1 := by
  have hU : U L α θ 0 = U L α θ 1 := by
    rw [U_eq_Xrot_of_theta_eq_zero L α θ hθ 0, U_eq_Xrot_of_theta_eq_zero L α θ hθ 1]
  rw [h, h, hU]

/-- **(2) 形式二**：`θ ≡ 0` 时 `h(0) = h(1) = 0`。 -/
lemma h_zero_of_theta_eq_zero (L : ℕ) (α θ : Fin L → ℝ) (hθ : ∀ j, θ j = 0) :
    h L α θ 0 = 0 := by
  rw [h_zero_eq_h_one_of_theta_eq_zero L α θ hθ, h_one]

/-- **(2) 形式三**（代价为零）：`Σ_j θ_j = 0` 且所有 `θ_j ≥ 0` 时每个 `θ_j = 0`
（`Fintype.sum_eq_zero_iff_of_nonneg`），于是 `h(0) = 0`。 -/
lemma h_zero_of_cost_eq_zero (L : ℕ) (α θ : Fin L → ℝ) (hθ : ∑ j, θ j = 0)
    (hθnn : ∀ j, 0 ≤ θ j) : h L α θ 0 = 0 := by
  have hθ0 : θ = 0 := (Fintype.sum_eq_zero_iff_of_nonneg hθnn).mp hθ
  exact h_zero_of_theta_eq_zero L α θ fun j => by simp [hθ0]

/-- **(2) 形式四**（直接对接 `Admissible`）：非负性是 `Admissible` 的一部分。 -/
lemma h_zero_of_admissible_of_cost_eq_zero {N : ℕ} {φ : ℝ} {L : ℕ} {α θ : Fin L → ℝ}
    (hAdm : Admissible N φ L α θ) (hθ : ∑ j, θ j = 0) : h L α θ 0 = 0 :=
  h_zero_of_cost_eq_zero L α θ hθ hAdm.1

/-! ## (3) `h_moments` + `h_bounds` 的打包 -/

/-- **(3)** M3（smearing）需要的输入形状：`h` 的复化是带宽 `τ = Σθⱼ/2` 的有限指数和，
且 `|h| ≤ 2`，其系数满足全部低阶矩条件（`deg P < 2N+2`），并且 `h(0) = Σᵢ cᵢ`。

（`h_moments` 给出指数和表示、矩条件与 `h(0) = Σ cᵢ`，`h_bounds` 给出 `0 ≤ h ≤ 2`；
再由 `Complex.norm_def`、`Complex.normSq_ofReal`、`Real.sqrt_mul_self hb.1` 得
`‖(h lam : ℂ)‖ = h lam ≤ 2`。） -/
lemma exists_expSum_data (N : ℕ) (φ : ℝ) (L : ℕ) (α θ : Fin L → ℝ)
    (hAdm : Admissible N φ L α θ) :
    ∃ (ι : Type) (_ : Fintype ι) (c : ι → ℂ) (ν : ι → ℝ),
      (∀ i, |ν i| ≤ (∑ j, θ j) / 2) ∧
      (∀ lam : ℝ, ‖(h L α θ lam : ℂ)‖ ≤ 2 ∧
        (h L α θ lam : ℂ) = ∑ i, Complex.exp (((ν i * lam : ℝ) : ℂ) * Complex.I) * c i) ∧
      (∀ P : Polynomial ℂ, P.natDegree < 2 * N + 2 →
        ∑ i, Complex.exp (((ν i : ℝ) : ℂ) * Complex.I) * P.eval ((ν i : ℂ)) * c i = 0) ∧
      ((h L α θ 0 : ℝ) : ℂ) = ∑ i, c i := by
  obtain ⟨ι, hι, c, ν, hν, hf, hmom, h0⟩ := h_moments N φ L α θ hAdm
  refine ⟨ι, hι, c, ν, hν, fun lam => ⟨?_, hf lam⟩, hmom, h0⟩
  have hb := h_bounds L α θ lam
  rw [Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self hb.1]
  exact hb.2

/-! ## (4) `Tmin` 的上界工具 -/

/-- **(4)** `cost θ` 本身就是可达代价（取同样的 `L, α, θ`），故不超过下确界 `Tmin`；
需要 `costs` 的下有界性 `costs_bddBelow`。 -/
lemma Tmin_le_of_admissible {N : ℕ} {φ : ℝ} {L : ℕ} {α θ : Fin L → ℝ}
    (hAdm : Admissible N φ L α θ) : Tmin N φ ≤ cost θ :=
  csInf_le (costs_bddBelow N φ) ⟨L, α, θ, hAdm, rfl⟩

/-! ## (5) 小算术（按要求 **不写**，仅记录形状）

最终组装需要的唯一"纯算术"步骤是把代价下界 `T ≥ 2(1-δ)(2N+2) = 4(1-δ)(N+1)`
化成 `4(1-δ) ≤ T/N`（再用 `δ → 0` 与 `liminf_ge_of_eventually` 收尾）。
最简形式（`N ≥ 1` 时）：

```lean
lemma four_mul_one_sub_le_div {N : ℕ} {T δ : ℝ} (hN : 1 ≤ N) (hδ1 : δ ≤ 1)
    (h : 2 * ((1 - δ) * (2 * (N : ℝ) + 2)) ≤ T) : 4 * (1 - δ) ≤ T / N
```

证明要点：`2 * ((1-δ) * (2*N+2)) = 4 * (1-δ) * (N+1)`；由 `1 ≤ N` 得 `0 < N`，
`(N+1)/N ≥ 1`，两边除以 `N > 0` 并用 `0 ≤ 1-δ`（`hδ1`）比较即可。
若希望结论直接是 `4 - δ ≤ T/N`（`0 ≤ δ ≤ 1`），把 `4*(1-δ) ≤ 4-δ` 接在后面即可。 -/

end RobustZ
