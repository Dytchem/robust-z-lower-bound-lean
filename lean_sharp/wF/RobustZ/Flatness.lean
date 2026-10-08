import RobustZ.Elementary
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.Analytic.Order

/-!
# M2b：平坦阶数翻倍（`h_flat`）

`W := U_1ᴴ U_λ - 1` 在 `λ = 1` 处有 `N+1` 阶零点（来自 `Admissible` 的 `N` 阶平坦），
而 `h = ¼ tr(WᴴW)`（`Elementary.lean`），故 `h` 在 `1` 处有 `2N+2` 阶零点：

`h = (·-1)^(2N+2) · g`，`g` 解析 ⇒ `analyticOrderAt h 1 ≥ 2N+2` ⇒ 各阶导数在前 `2N+2` 阶为零。

解析性用 `AnalyticAt`；阶数用 `analyticOrderAt`；两者的桥是
`natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero`。
-/

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

namespace RobustZ

/-! ## 1. 解析性 -/

lemma analyticAt_exp_smul (A : M2) (x : ℝ) :
    AnalyticAt ℝ (fun l : ℝ => NormedSpace.exp (l • A)) x := by
  have h1 : AnalyticAt ℝ (fun l : ℝ => l • A) x :=
    (analyticAt_id (𝕜 := ℝ) (E := ℝ) (z := x)).smul
      (analyticAt_const (𝕜 := ℝ) (F := M2) (v := A) (x := x))
  refine AnalyticAt.comp (f := fun l : ℝ => l • A) (x := x) ?_ h1
  exact NormedSpace.analyticAt_exp_of_mem_ball (𝕂 := ℝ) (𝔸 := M2) (x • A)
    (by simp [NormedSpace.expSeries_radius_eq_top, Metric.eball_top])

/-- 连续线性映射保持解析性。 -/
lemma AnalyticAt.comp_clm {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {f : ℝ → F} {x : ℝ} (g : F →L[ℝ] G)
    (hf : AnalyticAt ℝ f x) : AnalyticAt ℝ (fun y => g (f y)) x :=
  (g.comp_analyticOnNhd (s := {x}) (fun y hy => by
    rw [Set.mem_singleton_iff] at hy; rwa [hy])) x (Set.mem_singleton x)

lemma analyticAt_Xrot (x : ℝ) : AnalyticAt ℝ Xrot x := by
  unfold Xrot
  exact analyticAt_exp_smul Jx2 x

lemma analyticAt_Zrot_mul (c : ℝ) (x : ℝ) :
    AnalyticAt ℝ (fun l : ℝ => Zrot (l * c)) x := by
  have h : (fun l : ℝ => Zrot (l * c)) = fun l : ℝ => NormedSpace.exp (l • (c • Jz2)) := by
    funext l
    rw [Zrot, mul_smul]
  rw [h]
  exact analyticAt_exp_smul (c • Jz2) x

lemma analyticAt_U : ∀ (L : ℕ) (α θ : Fin L → ℝ) (x : ℝ),
    AnalyticAt ℝ (fun l : ℝ => U L α θ l) x
  | 0, α, θ, x => by simpa [U] using (analyticAt_const (𝕜 := ℝ) (v := (1 : M2)) (x := x))
  | L + 1, α, θ, x => by
      have h : (fun l : ℝ => U (L + 1) α θ l)
          = fun l : ℝ => U L (fun j => α j.castSucc) (fun j => θ j.castSucc) l
              * (Xrot (α (Fin.last L)) * Zrot (l * θ (Fin.last L))) := by
        funext l; rw [U_succ]
      rw [h]
      exact (analyticAt_U L _ _ x).mul
        ((analyticAt_const (v := Xrot (α (Fin.last L)))).mul
          (analyticAt_Zrot_mul (θ (Fin.last L)) x))

/-! ## 2. `U_· - Z(φ)` 在 1 处的阶 ≥ N+1 -/

/-- `Admissible` ⇒ `U_· - Z(φ)` 的各阶导数在前 `N+1` 阶为零。 -/
lemma iteratedDeriv_U_sub_Ztgt (N : ℕ) (φ : ℝ) (L : ℕ) (α θ : Fin L → ℝ)
    (hAdm : Admissible N φ L α θ) {i : ℕ} (hi : i < N + 1) :
    iteratedDeriv i (fun l : ℝ => U L α θ l - Ztgt φ) 1 = 0 := by
  have hU : ContDiffAt ℝ (i : WithTop ℕ∞) (fun l : ℝ => U L α θ l) 1 :=
    (analyticAt_U L α θ 1).contDiffAt
  have hc : ContDiffAt ℝ (i : WithTop ℕ∞) (fun _ : ℝ => Ztgt φ) 1 := contDiffAt_const
  have hfun : (fun l : ℝ => U L α θ l - Ztgt φ)
      = ((fun l : ℝ => U L α θ l) - fun _ : ℝ => Ztgt φ) := rfl
  rw [hfun, iteratedDeriv_sub hU hc]
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · subst h0
    simp [hAdm.2.1]
  · have hmem : i ∈ Finset.Icc 1 N := by
      simp only [Finset.mem_Icc]; omega
    rw [hAdm.2.2 i hmem]
    simp [iteratedDeriv_const, hpos.ne']

/-- 阶数下界：`N+1 ≤ analyticOrderAt (U_· - Z(φ)) 1`。 -/
lemma le_analyticOrderAt_U_sub_Ztgt (N : ℕ) (φ : ℝ) (L : ℕ) (α θ : Fin L → ℝ)
    (hAdm : Admissible N φ L α θ) :
    ((N + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt (fun l : ℝ => U L α θ l - Ztgt φ) 1 := by
  have hfun : (fun l : ℝ => U L α θ l - Ztgt φ)
      = ((fun l : ℝ => U L α θ l) - fun _ : ℝ => Ztgt φ) := rfl
  rw [hfun, natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
    ((analyticAt_U L α θ 1).sub analyticAt_const)]
  intro i hi
  exact iteratedDeriv_U_sub_Ztgt N φ L α θ hAdm hi

/-! ## 3. 因子分解 -/

/-- `U_· - Z(φ) = (·-1)^(N+1) • G`，`G` 在 1 处解析。 -/
lemma exists_factor_U_sub (N : ℕ) (φ : ℝ) (L : ℕ) (α θ : Fin L → ℝ)
    (hAdm : Admissible N φ L α θ) :
    ∃ G : ℝ → M2, AnalyticAt ℝ G 1 ∧
      ∀ l : ℝ, U L α θ l - Ztgt φ = (l - 1) ^ (N + 1) • G l := by
  set f : ℝ → M2 := fun l => U L α θ l - Ztgt φ with hf
  have hf_an : AnalyticAt ℝ f 1 := (analyticAt_U L α θ 1).sub analyticAt_const
  -- 平移到 0 处用 Taylor（Mathlib 的版本以 0 为中心）
  have hlin : AnalyticAt ℝ (fun z : ℝ => 1 + z) 0 :=
    (analyticAt_const (𝕜 := ℝ) (v := (1 : ℝ)) (x := (0 : ℝ))).add
      (analyticAt_id (𝕜 := ℝ) (E := ℝ) (z := (0 : ℝ)))
  have hf1 : AnalyticAt ℝ f (1 + 0) := by simpa using hf_an
  have hshift : AnalyticAt ℝ (fun z : ℝ => f (1 + z)) 0 :=
    AnalyticAt.comp (g := f) (f := fun z : ℝ => 1 + z) (x := 0) hf1 hlin
  obtain ⟨F, hF_an, hF⟩ := AnalyticAt.exists_eq_sum_add_pow_mul hshift (N + 1)
  have hzero : ∀ i < N + 1, iteratedDeriv i (fun z : ℝ => f (1 + z)) 0 = 0 := by
    intro i hi
    have hcomp : iteratedDeriv i (fun z : ℝ => f (1 + z)) 0 = iteratedDeriv i f 1 := by
      have h := congrFun (iteratedDeriv_comp_const_add i f 1) 0
      simpa using h
    rw [hcomp]
    exact iteratedDeriv_U_sub_Ztgt N φ L α θ hAdm hi
  have hmain : ∀ z : ℝ, f (1 + z) = z ^ (N + 1) • F z := by
    intro z
    rw [hF z]
    have hsum : (∑ i ∈ Finset.range (N + 1),
        (z ^ i / (i.factorial : ℝ)) • iteratedDeriv i (fun z : ℝ => f (1 + z)) 0) = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      rw [hzero i (Finset.mem_range.mp hi), smul_zero]
    rw [hsum, zero_add]
  refine ⟨fun l => F (l - 1), ?_, ?_⟩
  · have hlin : AnalyticAt ℝ (fun l : ℝ => l - 1) 1 :=
      (analyticAt_id (𝕜 := ℝ) (E := ℝ) (z := (1 : ℝ))).sub
        (analyticAt_const (𝕜 := ℝ) (v := (1 : ℝ)) (x := (1 : ℝ)))
    have : (fun l : ℝ => F (l - 1)) = (fun z : ℝ => F z) ∘ (fun l : ℝ => l - 1) := rfl
    rw [this]
    have hF0 : AnalyticAt ℝ F (1 - 1) := by simpa using hF_an
    exact AnalyticAt.comp (g := F) (f := fun l : ℝ => l - 1) (x := 1) hF0 hlin
  · intro l
    have h := hmain (l - 1)
    have harg : 1 + (l - 1) = l := by ring
    rw [harg] at h
    exact h

/-- `W_λ = U_1ᴴ U_λ - 1 = (·-1)^(N+1) • G`。 -/
lemma exists_factor_W (N : ℕ) (φ : ℝ) (L : ℕ) (α θ : Fin L → ℝ)
    (hAdm : Admissible N φ L α θ) :
    ∃ G : ℝ → M2, AnalyticAt ℝ G 1 ∧
      ∀ l : ℝ, (U L α θ 1)ᴴ * U L α θ l - 1 = (l - 1) ^ (N + 1) • G l := by
  obtain ⟨F, hF_an, hF⟩ := exists_factor_U_sub N φ L α θ hAdm
  refine ⟨fun l => (U L α θ 1)ᴴ * F l,
    (analyticAt_const (v := (U L α θ 1)ᴴ)).mul hF_an, fun l => ?_⟩
  have hU1 : (U L α θ 1)ᴴ * Ztgt φ = 1 := by
    rw [← hAdm.2.1]
    exact U_conjTranspose_mul L α θ 1
  have hmul : (U L α θ 1)ᴴ * U L α θ l - 1
      = (U L α θ 1)ᴴ * (U L α θ l - Ztgt φ) := by
    rw [Matrix.mul_sub, hU1]
  rw [hmul, hF l, mul_smul_comm]

/-! ## 4. `h = (·-1)^(2N+2) · g` 与 `h_flat` -/

lemma analyticAt_entry (G : ℝ → M2) (hG : AnalyticAt ℝ G 1) (i j : Fin 2) :
    AnalyticAt ℝ (fun l : ℝ => G l i j) 1 :=
  AnalyticAt.comp_clm (ContinuousLinearMap.proj (R := ℝ) j)
    (AnalyticAt.comp_clm (ContinuousLinearMap.proj (R := ℝ) i) hG)

lemma analyticAt_normSq_entry (G : ℝ → M2) (hG : AnalyticAt ℝ G 1) (i j : Fin 2) :
    AnalyticAt ℝ (fun l : ℝ => Complex.normSq (G l i j)) 1 := by
  have hre : AnalyticAt ℝ (fun l : ℝ => (G l i j).re) 1 :=
    AnalyticAt.comp_clm Complex.reCLM (analyticAt_entry G hG i j)
  have him : AnalyticAt ℝ (fun l : ℝ => (G l i j).im) 1 :=
    AnalyticAt.comp_clm Complex.imCLM (analyticAt_entry G hG i j)
  have hfun : (fun l : ℝ => Complex.normSq (G l i j))
      = fun l : ℝ => (G l i j).re * (G l i j).re + (G l i j).im * (G l i j).im := by
    funext l; rw [Complex.normSq_apply]
  rw [hfun]
  exact (hre.mul hre).add (him.mul him)

lemma analyticAt_quarter_trace (G : ℝ → M2) (hG : AnalyticAt ℝ G 1) :
    AnalyticAt ℝ (fun l : ℝ => (1 / 4) * ((G l)ᴴ * (G l)).trace.re) 1 := by
  have hsum : AnalyticAt ℝ (fun l : ℝ => Complex.normSq (G l 0 0) + Complex.normSq (G l 0 1)
      + Complex.normSq (G l 1 0) + Complex.normSq (G l 1 1)) 1 :=
    (((analyticAt_normSq_entry G hG 0 0).add (analyticAt_normSq_entry G hG 0 1)).add
      (analyticAt_normSq_entry G hG 1 0)).add (analyticAt_normSq_entry G hG 1 1)
  have hfun : (fun l : ℝ => (1 / 4) * ((G l)ᴴ * (G l)).trace.re)
      = fun l : ℝ => (1 / 4) * (Complex.normSq (G l 0 0) + Complex.normSq (G l 0 1)
          + Complex.normSq (G l 1 0) + Complex.normSq (G l 1 1)) := by
    funext l; rw [trace_conjTranspose_mul_self_eq_normSq]
  rw [hfun]
  exact (analyticAt_const (𝕜 := ℝ) (v := (1 / 4 : ℝ)) (x := (1 : ℝ))).mul hsum

/-- `h = (·-1)^(2N+2) · g`，`g` 在 `1` 处解析。 -/
lemma exists_factor_h (N : ℕ) (φ : ℝ) (L : ℕ) (α θ : Fin L → ℝ)
    (hAdm : Admissible N φ L α θ) :
    ∃ g : ℝ → ℝ, AnalyticAt ℝ g 1 ∧
      ∀ l : ℝ, h L α θ l = (l - 1) ^ (2 * N + 2) * g l := by
  obtain ⟨G, hG, hGW⟩ := exists_factor_W N φ L α θ hAdm
  refine ⟨fun l => (1 / 4) * ((G l)ᴴ * (G l)).trace.re,
    analyticAt_quarter_trace G hG, fun l => ?_⟩
  have hV : (((U L α θ 1)ᴴ * U L α θ l)ᴴ) * ((U L α θ 1)ᴴ * U L α θ l) = 1 :=
    V_conjTranspose_mul L α θ l
  rw [h, h_eq_quarter_trace _ hV, hGW l, Matrix.conjTranspose_smul, star_trivial,
    smul_mul_assoc, Matrix.mul_smul, smul_smul, Matrix.trace_smul]
  simp only [Complex.smul_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- **M2b**：`Admissible` ⇒ `h` 在 `1` 处 `2N+2` 阶平（论文的平坦阶数翻倍）。 -/
theorem h_flat (N : ℕ) (φ : ℝ) (L : ℕ) (α θ : Fin L → ℝ) (hAdm : Admissible N φ L α θ) :
    ∀ k < 2 * N + 2, iteratedDeriv k (fun lam => h L α θ lam) 1 = 0 := by
  obtain ⟨g, hg_an, hg_eq⟩ := exists_factor_h N φ L α θ hAdm
  have hid : AnalyticAt ℝ (fun l : ℝ => l - 1) 1 :=
    (analyticAt_id (𝕜 := ℝ) (E := ℝ) (z := (1 : ℝ))).sub
      (analyticAt_const (𝕜 := ℝ) (v := (1 : ℝ)) (x := (1 : ℝ)))
  have hfun : (fun lam : ℝ => h L α θ lam)
      = fun l : ℝ => (l - 1) ^ (2 * N + 2) * g l := funext hg_eq
  have hh_an : AnalyticAt ℝ (fun lam : ℝ => h L α θ lam) 1 := by
    rw [hfun]
    exact (hid.pow _).mul hg_an
  have horder : ((2 * N + 2 : ℕ) : ℕ∞) ≤ analyticOrderAt (fun lam : ℝ => h L α θ lam) 1 := by
    have hprod : (fun l : ℝ => (l - 1) ^ (2 * N + 2) * g l)
        = (((fun l : ℝ => l - 1) ^ (2 * N + 2)) * g) := rfl
    have hcalc : analyticOrderAt (fun lam : ℝ => h L α θ lam) 1
        = ((2 * N + 2 : ℕ) : ℕ∞) + analyticOrderAt g 1 := by
      rw [hfun, hprod, analyticOrderAt_mul (hid.pow _) hg_an, analyticOrderAt_pow hid,
        analyticOrderAt_id_sub_const_self]
      simp
    rw [hcalc]
    exact le_add_right le_rfl
  exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hh_an).mp horder

end RobustZ
