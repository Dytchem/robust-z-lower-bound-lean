import RobustZ.HTraceLower
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# 论文 §4 的初等有限 `N` 下界（`ElementaryBound.lean`）

本文件形式化论文（`paper_num/main.tex`，§"Two elementary bounds"）中给出的
初等下界：对目标角 `φ ∈ (0, π]`，任意 `N` 阶鲁棒序列满足

```
T = cost θ ≥ 2 * (2 * q! * sin(φ/4)^2)^(1/q),   q = 2N + 2,
```

即 `q!` 形式；由 Stirling 可得 `T ≳ 4(N+1)/e`，也就是论文的 `4/e` 系数
（本文件末给出严格不等式 `2(q!)^(1/q) > 4(N+1)/e`）。

证明路线（与论文一致）：

1. **传播子的导数界**：单个 `Z` 因子满足 `‖Z(λθ_j)^{(m)}‖ = (θ_j/2)^m`；
   对乘积用 Leibniz 公式与多项式定理得到 `‖U_λ^{(k)}‖ ≤ τ^k`，`τ = Σθ_j/2`
   （`norm_iteratedDeriv_U_le`）。
2. **载体的导数界**：由 `h = 1 - ½ Re tr(U_1ᴴ U_λ)` 与 `|tr M| ≤ 2‖M‖` 得
   `|h^{(k)}(λ)| ≤ τ^k`（`abs_iteratedDeriv_h_le`）。
3. **平坦阶数翻倍**：`h_flat`（`RobustZ/Flatness.lean`）给出 `h` 在 `1` 处
   `q = 2N+2` 阶平坦；Taylor 定理的 Lagrange 余项写成 `ξ ∈ (0,1)` 处的
   `q` 阶导数，故 `|h(0)| ≤ τ^q/q!`（`abs_h_zero_le`）。
4. **端点几何**：`h(0) ≥ 1 - cos(φ/2) = 2 sin²(φ/4)`（`h_zero_ge`）。
5. 合并得 `τ^q ≥ 2 q! sin²(φ/4)`，开 `q` 次方即得结论。
-/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped Matrix Matrix.Norms.L2Operator
open Matrix Filter
open scoped Topology

namespace RobustZ

/-! ## 1. `2 × 2` 矩阵的范数基础引理 -/

/-- 酉矩阵（`Aᴴ A = 1`）的算子范数为 `1`。 -/
lemma norm_eq_one_of_conjTranspose_mul_eq_one (A : M2) (h : Aᴴ * A = 1) : ‖A‖ = 1 := by
  have h2 : ‖A‖ * ‖A‖ = 1 := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self A, h, CStarRing.norm_one]
  nlinarith [norm_nonneg A]

/-- 矩阵元素的模不超过 L2 算子范数。 -/
lemma norm_entry_le (M : M2) (j i : Fin 2) : ‖M j i‖ ≤ ‖M‖ := by
  have h := M.l2_opNorm_mulVec (EuclideanSpace.single i (1 : ℂ))
  have h1 : ‖EuclideanSpace.single i (1 : ℂ)‖ = 1 := by simp
  rw [h1, mul_one] at h
  have h2 : (EuclideanSpace.single i (1 : ℂ)).ofLp = Pi.single i (1 : ℂ) := rfl
  rw [h2] at h
  have h3 : (M *ᵥ Pi.single i (1 : ℂ)) = fun k => M k i := by
    funext k
    simp [Matrix.mulVec]
  rw [h3] at h
  calc ‖M j i‖ = ‖((EuclideanSpace.equiv (Fin 2) ℂ).symm (fun k => M k i)).ofLp j‖ := by simp
    _ ≤ _ := PiLp.norm_apply_le _ j
    _ ≤ ‖M‖ := h

/-- `|tr M| ≤ 2‖M‖`（`2 × 2`）。 -/
lemma norm_trace_le (M : M2) : ‖M.trace‖ ≤ 2 * ‖M‖ := by
  rw [Matrix.trace_fin_two]
  calc ‖M 0 0 + M 1 1‖ ≤ ‖M 0 0‖ + ‖M 1 1‖ := norm_add_le _ _
    _ ≤ ‖M‖ + ‖M‖ := add_le_add (norm_entry_le M 0 0) (norm_entry_le M 1 1)
    _ = 2 * ‖M‖ := by ring

/-- `‖Jz2‖ = 1/2`（生成元 `-iσz/2` 的算子范数）。 -/
lemma norm_Jz2 : ‖Jz2‖ = (1 / 2 : ℝ) := by
  have hσ : (!![1, 0; 0, -1] : M2)ᴴ * !![1, 0; 0, -1] = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two]
  have h1 : ‖(!![1, 0; 0, -1] : M2)‖ = 1 := norm_eq_one_of_conjTranspose_mul_eq_one _ hσ
  simp only [Jz2, Jz, sigmaZ, norm_smul, h1, mul_one]
  norm_num

lemma norm_smul_Jz2 (c : ℝ) : ‖c • Jz2‖ = |c| / 2 := by
  rw [norm_smul, norm_Jz2, Real.norm_eq_abs]
  ring

/-! ## 2. `Z(λc)` 的导数 -/

/-- `Z(λc) = exp(λ • (c • Jz2))` 的导数。 -/
lemma hasDerivAt_Zrot_mul (c lam : ℝ) :
    HasDerivAt (fun l : ℝ => Zrot (l * c)) (Zrot (lam * c) * (c • Jz2)) lam := by
  have h := hasDerivAt_exp_smul_const_of_mem_ball (𝕂 := ℝ) (𝔸 := M2)
    (x := c • Jz2) (t := lam) (by simp [NormedSpace.expSeries_radius_eq_top, Metric.eball_top])
  simpa [Zrot, mul_smul] using h

/-- `Z(λc)` 的第 `k` 阶导数：`(Z(λc))^{(k)} = Z(λc)(c Jz2)^k`。 -/
lemma iteratedDeriv_Zrot_mul (c : ℝ) (k : ℕ) (lam : ℝ) :
    iteratedDeriv k (fun l : ℝ => Zrot (l * c)) lam = Zrot (lam * c) * (c • Jz2) ^ k := by
  induction k generalizing lam with
  | zero => simp
  | succ k ih =>
      rw [iteratedDeriv_succ]
      have hfun : iteratedDeriv k (fun l : ℝ => Zrot (l * c))
          = fun l => Zrot (l * c) * (c • Jz2) ^ k := funext ih
      rw [hfun]
      rw [(hasDerivAt_Zrot_mul c lam).mul_const ((c • Jz2) ^ k) |>.deriv, mul_assoc, pow_succ']

/-- `‖(Z(λc))^{(k)}‖ ≤ (|c|/2)^k`。 -/
lemma norm_iteratedDeriv_Zrot_mul_le (c : ℝ) (k : ℕ) (lam : ℝ) :
    ‖iteratedDeriv k (fun l : ℝ => Zrot (l * c)) lam‖ ≤ (|c| / 2) ^ k := by
  rw [iteratedDeriv_Zrot_mul]
  calc ‖Zrot (lam * c) * (c • Jz2) ^ k‖
      ≤ ‖Zrot (lam * c)‖ * ‖(c • Jz2) ^ k‖ := norm_mul_le _ _
    _ ≤ 1 * ‖c • Jz2‖ ^ k := by
        refine mul_le_mul (le_of_eq (norm_eq_one_of_conjTranspose_mul_eq_one _
          (Zrot_conjTranspose_mul _))) (norm_pow_le _ _) (by positivity) (by norm_num)
    _ = (|c| / 2) ^ k := by rw [one_mul, norm_smul_Jz2]

/-- 单位 `X` 旋转与 `Z(λc)` 乘积的导数界。 -/
lemma norm_iteratedDeriv_XZ_le (a c : ℝ) (k : ℕ) (lam : ℝ) :
    ‖iteratedDeriv k (fun l : ℝ => Xrot a * Zrot (l * c)) lam‖ ≤ (|c| / 2) ^ k := by
  rw [iteratedDeriv_const_mul (Xrot a) ((analyticAt_Zrot_mul c lam).contDiffAt)]
  calc ‖Xrot a * iteratedDeriv k (fun l : ℝ => Zrot (l * c)) lam‖
      ≤ ‖Xrot a‖ * ‖iteratedDeriv k (fun l : ℝ => Zrot (l * c)) lam‖ := norm_mul_le _ _
    _ ≤ 1 * (|c| / 2) ^ k := by
        refine mul_le_mul (le_of_eq (norm_eq_one_of_conjTranspose_mul_eq_one _
          (Xrot_conjTranspose_mul _))) (norm_iteratedDeriv_Zrot_mul_le c k lam)
          (by positivity) (by norm_num)
    _ = (|c| / 2) ^ k := one_mul _

/-! ## 3. Leibniz + 多项式定理：`‖U^{(k)}‖ ≤ τ^k` -/

/-- 乘积的 `k` 阶导数界（Leibniz 公式 + 二项式定理的实标量形式）。 -/
lemma norm_iteratedDeriv_mul_le {σ ρ : ℝ} (hσ : 0 ≤ σ)
    {A B : ℝ → M2} {k : ℕ} {x : ℝ}
    (hAc : ContDiffAt ℝ ((k : ℕ) : WithTop ℕ∞) A x)
    (hBc : ContDiffAt ℝ ((k : ℕ) : WithTop ℕ∞) B x)
    (hA : ∀ i ≤ k, ‖iteratedDeriv i A x‖ ≤ σ ^ i)
    (hB : ∀ i ≤ k, ‖iteratedDeriv i B x‖ ≤ ρ ^ i) :
    ‖iteratedDeriv k (A * B) x‖ ≤ (σ + ρ) ^ k := by
  rw [iteratedDeriv_mul hAc hBc]
  have hterm : ∀ i, (↑(k.choose i) : M2) * iteratedDeriv i A x * iteratedDeriv (k - i) B x
      = (k.choose i : ℝ) • (iteratedDeriv i A x * iteratedDeriv (k - i) B x) := by
    intro i
    rw [Algebra.smul_def, map_natCast, mul_assoc]
  simp only [hterm]
  have hstep : ∀ i ∈ Finset.range (k + 1),
      ‖(k.choose i : ℝ) • (iteratedDeriv i A x * iteratedDeriv (k - i) B x)‖
        ≤ (k.choose i : ℝ) * (σ ^ i * ρ ^ (k - i)) := by
    intro i hi
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hki : k - i ≤ k := Nat.sub_le _ _
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (k.choose i))]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    exact (norm_mul_le _ _).trans (mul_le_mul (hA i hik) (hB (k - i) hki)
      (by positivity) (pow_nonneg hσ i))
  exact (norm_sum_le _ _).trans ((Finset.sum_le_sum hstep).trans (by
    rw [add_pow]
    exact le_of_eq (Finset.sum_congr rfl fun i _ => by ring)))

/-- **传播子导数界**：`‖d^k/dλ^k U_λ‖ ≤ (Σ_j |θ_j|/2)^k`（对一切 `λ`）。 -/
lemma norm_iteratedDeriv_U_le : ∀ (L : ℕ) (α θ : Fin L → ℝ) (k : ℕ) (x : ℝ),
    ‖iteratedDeriv k (fun l : ℝ => U L α θ l) x‖ ≤ (∑ j, |θ j| / 2) ^ k
  | 0, α, θ, k, x => by
      have h : (fun l : ℝ => U 0 α θ l) = fun _ : ℝ => (1 : M2) := by
        funext l; simp
      rw [h, iteratedDeriv_const]
      split_ifs with hk
      · subst hk; simp
      · rw [norm_zero]; positivity
  | L + 1, α, θ, k, x => by
      have hfun : (fun l : ℝ => U (L + 1) α θ l)
          = (fun l : ℝ => U L (fun j => α j.castSucc) (fun j => θ j.castSucc) l)
            * (fun l : ℝ => Xrot (α (Fin.last L)) * Zrot (l * θ (Fin.last L))) := by
        funext l
        exact U_succ L α θ l
      have hsum : (∑ j : Fin L, |θ j.castSucc| / 2) + |θ (Fin.last L)| / 2
          = ∑ j : Fin (L + 1), |θ j| / 2 := by
        rw [Fin.sum_univ_castSucc]
      rw [hfun, ← hsum]
      refine norm_iteratedDeriv_mul_le (Finset.sum_nonneg fun j _ => by positivity)
        ((analyticAt_U L _ _ x).contDiffAt)
        (((analyticAt_const (v := Xrot (α (Fin.last L)))).mul
          (analyticAt_Zrot_mul (θ (Fin.last L)) x)).contDiffAt)
        (fun i _ => norm_iteratedDeriv_U_le L (fun j => α j.castSucc)
          (fun j => θ j.castSucc) i x)
        (fun i _ => norm_iteratedDeriv_XZ_le _ _ i x)

/-! ### `iteratedDeriv` 与连续线性映射的复合 -/

/-- `deriv (g ∘ f) x = g (deriv f x)`。 -/
lemma deriv_clm_comp {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (g : F →L[ℝ] G) (f : ℝ → F) (x : ℝ)
    (hd : DifferentiableAt ℝ f x) :
    deriv (fun y => g (f y)) x = g (deriv f x) := by
  have h := (g.hasFDerivAt.comp_hasDerivAt x hd.hasDerivAt)
  rw [← h.deriv]
  rfl

/-- `ContDiffAt` 蕴含 `iteratedDeriv` 在一点可微。 -/
lemma differentiableAt_iteratedDeriv_of_contDiffAt {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : ℝ → F} {x : ℝ} {n : ℕ}
    (h : ContDiffAt ℝ ((n + 1 : ℕ) : WithTop ℕ∞) f x) :
    DifferentiableAt ℝ (iteratedDeriv n f) x := by
  have h' : ContDiffWithinAt ℝ ((n + 1 : ℕ) : WithTop ℕ∞) f Set.univ x := h.contDiffWithinAt
  have h2 := h'.differentiableWithinAt_iteratedDerivWithin (s := Set.univ) (m := n)
    (by exact_mod_cast Nat.lt_succ_self n) (by simp)
  rwa [iteratedDerivWithin_univ, differentiableWithinAt_univ] at h2

/-- **`iteratedDeriv` 的复合公式**：`(g ∘ f)^{(n)} = g (f^{(n)})`。 -/
lemma iteratedDeriv_clm_comp {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (g : F →L[ℝ] G) (f : ℝ → F) :
    ∀ (n : ℕ) (x : ℝ), ContDiffAt ℝ (n : WithTop ℕ∞) f x →
      iteratedDeriv n (fun y => g (f y)) x = g (iteratedDeriv n f x) := by
  intro n
  induction n with
  | zero => intro x _; simp
  | succ n ih =>
      intro x hx
      have hev : (fun y => iteratedDeriv n (fun z => g (f z)) y) =ᶠ[𝓝 x]
          fun y => g (iteratedDeriv n f y) := by
        filter_upwards [hx.eventually (by simp)] with y hy
        exact ih y (hy.of_le (by simp))
      have hdiff : DifferentiableAt ℝ (iteratedDeriv n f) x :=
        differentiableAt_iteratedDeriv_of_contDiffAt hx
      rw [iteratedDeriv_succ, hev.deriv_eq, iteratedDeriv_succ]
      exact deriv_clm_comp g (iteratedDeriv n f) x hdiff

/-! ## 4. 标量载体 `h` 的导数界 -/

/-- 迹作为连续线性映射（界为 `2`，见 `norm_trace_le`）。 -/
def traceCLM : M2 →L[ℝ] ℂ :=
  (Matrix.traceLinearMap (Fin 2) ℝ ℂ).mkContinuous 2 (fun M => norm_trace_le M)

/-- `A ↦ ½ Re tr(Aᴴ ·)`：载体 `h = 1 - ½Re tr(U_1ᴴ U_λ)` 中除常数外的实线性部分。 -/
def carrierCLM (A : M2) : M2 →L[ℝ] ℝ :=
  (1 / 2 : ℝ) • (Complex.reCLM.comp (traceCLM.comp ((ContinuousLinearMap.mul ℝ M2) Aᴴ)))

lemma carrierCLM_apply (A M : M2) : carrierCLM A M = (1 / 2) * ((Aᴴ * M).trace).re := rfl

/-- 载体的线性部分在酉 `A` 上范数不超过 `1`。 -/
lemma norm_carrierCLM_le (A M : M2) (hA : Aᴴ * A = 1) : ‖carrierCLM A M‖ ≤ ‖M‖ := by
  have hnorm : ‖A‖ = 1 := norm_eq_one_of_conjTranspose_mul_eq_one A hA
  have h1 : ‖((Aᴴ * M).trace).re‖ ≤ ‖(Aᴴ * M).trace‖ := Complex.abs_re_le_norm _
  rw [carrierCLM_apply]
  calc ‖(1 / 2) * ((Aᴴ * M).trace).re‖ = (1 / 2) * ‖((Aᴴ * M).trace).re‖ := by
        rw [norm_mul, Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 1 / 2)]
    _ ≤ (1 / 2) * ‖(Aᴴ * M).trace‖ := by
        exact mul_le_mul_of_nonneg_left h1 (by norm_num)
    _ ≤ (1 / 2) * (2 * ‖Aᴴ * M‖) := by
        exact mul_le_mul_of_nonneg_left (norm_trace_le _) (by norm_num)
    _ = ‖Aᴴ * M‖ := by ring
    _ ≤ ‖Aᴴ‖ * ‖M‖ := norm_mul_le _ _
    _ = ‖M‖ := by rw [Matrix.l2_opNorm_conjTranspose, hnorm, one_mul]

lemma h_eq_carrierCLM (L : ℕ) (α θ : Fin L → ℝ) (lam : ℝ) :
    h L α θ lam = 1 - carrierCLM (U L α θ 1) (U L α θ lam) := rfl

/-- `h` 在任意点解析。 -/
lemma analyticAt_h (L : ℕ) (α θ : Fin L → ℝ) (x : ℝ) :
    AnalyticAt ℝ (fun l : ℝ => h L α θ l) x := by
  have hfun : (fun l : ℝ => h L α θ l)
      = fun l : ℝ => 1 - carrierCLM (U L α θ 1) (U L α θ l) := funext (h_eq_carrierCLM L α θ)
  have h1 : AnalyticAt ℝ (fun l : ℝ => carrierCLM (U L α θ 1) (U L α θ l)) x :=
    AnalyticAt.comp_clm (carrierCLM (U L α θ 1)) (analyticAt_U L α θ x)
  rw [hfun]
  exact (analyticAt_const (𝕜 := ℝ) (v := (1 : ℝ)) (x := x)).sub h1

/-- **载体导数界**：`|h^{(k)}(λ)| ≤ τ^k`，`τ = Σ_j |θ_j|/2`，`k ≥ 1`。 -/
lemma abs_iteratedDeriv_h_le (L : ℕ) (α θ : Fin L → ℝ) {k : ℕ} (hk : 1 ≤ k) (x : ℝ) :
    |iteratedDeriv k (fun l : ℝ => h L α θ l) x| ≤ (∑ j, |θ j| / 2) ^ k := by
  have hfun : (fun l : ℝ => h L α θ l)
      = fun l : ℝ => 1 - carrierCLM (U L α θ 1) (U L α θ l) := funext (h_eq_carrierCLM L α θ)
  have hsplit : (fun l : ℝ => 1 - carrierCLM (U L α θ 1) (U L α θ l))
      = ((fun _ : ℝ => (1 : ℝ)) - fun l : ℝ => carrierCLM (U L α θ 1) (U L α θ l)) := rfl
  have hc : ContDiffAt ℝ ((k : ℕ) : WithTop ℕ∞)
      (fun l : ℝ => carrierCLM (U L α θ 1) (U L α θ l)) x :=
    ((carrierCLM (U L α θ 1)).contDiff.comp_contDiffAt x
      (analyticAt_U L α θ x).contDiffAt)
  have hk0 : ¬ (k = 0) := by omega
  have hval : iteratedDeriv k (fun l : ℝ => h L α θ l) x
      = - carrierCLM (U L α θ 1) (iteratedDeriv k (fun l : ℝ => U L α θ l) x) := by
    rw [hfun, hsplit, iteratedDeriv_sub contDiffAt_const hc, iteratedDeriv_const,
      iteratedDeriv_clm_comp (carrierCLM (U L α θ 1)) (fun l : ℝ => U L α θ l) k x
        ((analyticAt_U L α θ x).contDiffAt)]
    simp only [hk0, ite_false, zero_sub]
  rw [hval, abs_neg, ← Real.norm_eq_abs]
  calc ‖carrierCLM (U L α θ 1) (iteratedDeriv k (fun l : ℝ => U L α θ l) x)‖
      ≤ ‖iteratedDeriv k (fun l : ℝ => U L α θ l) x‖ :=
        norm_carrierCLM_le _ _ (U_conjTranspose_mul L α θ 1)
    _ ≤ (∑ j, |θ j| / 2) ^ k := norm_iteratedDeriv_U_le L α θ k x

/-! ## 5. Taylor–Lagrange：平坦性给出 `|h(0)| ≤ τ^q/q!` -/

/-- **Taylor 定理（Lagrange 余项）+ 平坦性**：若 `f` 在 `λ = 1` 处前 `q` 阶导数全为零，
则 `f(0)` 由区间内部某点的 `q` 阶导数决定。 -/
lemma abs_zero_le_of_flat (f : ℝ → ℝ) (q : ℕ) (τ : ℝ) (hq : 0 < q)
    (hf : ContDiffOn ℝ ((q : ℕ) : WithTop ℕ∞) f (Set.uIcc 1 0))
    (hcd : ∀ i < q, ContDiffAt ℝ ((i : ℕ) : WithTop ℕ∞) f 1)
    (hflat : ∀ i < q, iteratedDeriv i f 1 = 0)
    (hbd : ∀ ξ ∈ Set.Ioo 0 1, |iteratedDeriv q f ξ| ≤ τ ^ q) :
    |f 0| ≤ τ ^ q / (q.factorial : ℝ) := by
  have hq1 : q - 1 + 1 = q := Nat.sub_add_cancel hq
  have hcont : ContDiffOn ℝ ((((q - 1 : ℕ)) : WithTop ℕ∞) + 1) f (Set.uIcc 1 0) := by
    have hcast : (((q - 1 : ℕ)) : WithTop ℕ∞) + 1 = ((q : ℕ) : WithTop ℕ∞) := by
      exact_mod_cast hq1
    rw [hcast]
    exact hf
  obtain ⟨ξ, hξ, heq⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv (f := f) (x := 0) (x₀ := 1) (n := q - 1)
      (by norm_num) hcont
  have hzero : taylorWithinEval f (q - 1) (Set.uIcc 1 0) 1 0 = 0 := by
    rw [taylor_within_apply, hq1]
    refine Finset.sum_eq_zero fun i hi => ?_
    have hiq : i < q := Finset.mem_range.mp hi
    have h1 : iteratedDerivWithin i f (Set.uIcc 1 0) 1 = 0 := by
      rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc (by norm_num : (1 : ℝ) ≠ 0))
        (hcd i hiq) (by simp)]
      exact hflat i hiq
    rw [h1, smul_zero]
  have hf0 : f 0 = iteratedDeriv q f ξ * (0 - 1) ^ q / (q.factorial : ℝ) := by
    have h' := heq
    rw [hzero, sub_zero, hq1] at h'
    simpa using h'
  have hξI : ξ ∈ Set.Ioo 0 1 := by simpa [Set.uIoo] using hξ
  have hfac : (0 : ℝ) < (q.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos q)
  have h1 : |(0 : ℝ) - 1| = 1 := by norm_num
  have h2 : |(q.factorial : ℝ)| = (q.factorial : ℝ) := abs_of_nonneg hfac.le
  have habs : |f 0| = |iteratedDeriv q f ξ| / (q.factorial : ℝ) := by
    rw [hf0, abs_div, abs_mul, abs_pow, h1, one_pow, mul_one, h2]
  rw [habs, div_le_div_iff_of_pos_right hfac]
  exact hbd ξ hξI

/-! ## 6. 端点几何与最终下界 -/

/-- 端点下界：`h(0) ≥ 1 - cos(φ/2) = 2 sin²(φ/4)`（论文 `eq:endpoint`）。 -/
lemma two_mul_sin_sq_le_h_zero (N : ℕ) (L : ℕ) (α θ : Fin L → ℝ) {φ : ℝ}
    (hφ0 : 0 < φ) (hφπ : φ ≤ Real.pi) (hAdm : Admissible N φ L α θ) :
    2 * Real.sin (φ / 4) ^ 2 ≤ h L α θ 0 := by
  have htri : 1 - Real.cos (φ / 2) = 2 * Real.sin (φ / 4) ^ 2 := by
    have h1 := Real.cos_two_mul (φ / 4)
    have h2 := Real.sin_sq_add_cos_sq (φ / 4)
    have h3 : 2 * (φ / 4) = φ / 2 := by ring
    rw [h3] at h1
    nlinarith
  rw [← htri]
  exact h_zero_ge φ (le_of_lt hφ0) hφπ L α θ hAdm.2.1

/-- **论文 §4 的初等有限 `N` 下界**（`4/e` 估计的 `q!` 精确形式）：

对 `q = 2N + 2`，任意 `N` 阶鲁棒序列满足
`cost θ ≥ 2 (2 q! sin²(φ/4))^(1/q)`；`φ = π` 时即 `cost θ ≥ 2 (q!)^(1/q)`。 -/
theorem elementary_bound {L : ℕ} {α θ : Fin L → ℝ} {N : ℕ} {φ : ℝ}
    (hφ0 : 0 < φ) (hφπ : φ ≤ Real.pi) (hAdm : Admissible N φ L α θ) :
    2 * (2 * (Nat.factorial (2 * N + 2) : ℝ) * Real.sin (φ / 4) ^ 2)
        ^ (1 / ((2 * N + 2 : ℕ) : ℝ)) ≤ cost θ := by
  set q : ℕ := 2 * N + 2 with hqdef
  have hq : 0 < q := by omega
  set T : ℝ := cost θ with hTdef
  have hfac : (0 : ℝ) < (q.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos q)
  have hTnn : 0 ≤ T := by
    rw [hTdef, cost]
    exact Finset.sum_nonneg fun j _ => hAdm.1 j
  have hτ : (∑ j, |θ j| / 2) = T / 2 := by
    have h1 : ∀ j, |θ j| = θ j := fun j => abs_of_nonneg (hAdm.1 j)
    simp only [h1, hTdef, cost, Finset.sum_div]
  -- (1) 导数界 `|h^{(q)}| ≤ (T/2)^q`
  have hbd : ∀ ξ ∈ Set.Ioo 0 1,
      |iteratedDeriv q (fun l : ℝ => h L α θ l) ξ| ≤ (T / 2) ^ q := by
    intro ξ _
    rw [← hτ]
    exact abs_iteratedDeriv_h_le L α θ (by omega) ξ
  -- (2) 平坦性（`h_flat`）
  have hflat : ∀ i < q, iteratedDeriv i (fun l : ℝ => h L α θ l) 1 = 0 := by
    intro i hi
    exact h_flat N φ L α θ hAdm i (by omega)
  have hcd : ∀ i < q, ContDiffAt ℝ ((i : ℕ) : WithTop ℕ∞)
      (fun l : ℝ => h L α θ l) 1 := fun i _ => (analyticAt_h L α θ 1).contDiffAt
  have hcont : ContDiffOn ℝ ((q : ℕ) : WithTop ℕ∞) (fun l : ℝ => h L α θ l)
      (Set.uIcc 1 0) :=
    (contDiff_iff_contDiffAt.mpr fun x => (analyticAt_h L α θ x).contDiffAt).contDiffOn
  -- (3) Taylor–Lagrange
  have hstep1 : h L α θ 0 ≤ (T / 2) ^ q / (q.factorial : ℝ) :=
    (le_abs_self _).trans (abs_zero_le_of_flat _ q (T / 2) hq hcont hcd hflat hbd)
  -- (4) 端点
  have hstep2 : 2 * Real.sin (φ / 4) ^ 2 ≤ h L α θ 0 :=
    two_mul_sin_sq_le_h_zero N L α θ hφ0 hφπ hAdm
  have hmain : 2 * Real.sin (φ / 4) ^ 2 * (q.factorial : ℝ) ≤ (T / 2) ^ q :=
    (le_div_iff₀ hfac).mp (hstep2.trans hstep1)
  -- (5) 开 `q` 次方
  have hroot : (2 * Real.sin (φ / 4) ^ 2 * (q.factorial : ℝ)) ^ (1 / (q : ℝ)) ≤ T / 2 := by
    calc (2 * Real.sin (φ / 4) ^ 2 * (q.factorial : ℝ)) ^ (1 / (q : ℝ))
        ≤ ((T / 2) ^ q) ^ (1 / (q : ℝ)) :=
          Real.rpow_le_rpow (by positivity) hmain (by positivity)
      _ = T / 2 := by
          rw [← Real.rpow_natCast (T / 2) q, ← Real.rpow_mul (by linarith : (0 : ℝ) ≤ T / 2),
            mul_one_div, div_self (by positivity : (q : ℝ) ≠ 0), Real.rpow_one]
  have hbase : 2 * (Nat.factorial q : ℝ) * Real.sin (φ / 4) ^ 2
      = 2 * Real.sin (φ / 4) ^ 2 * (q.factorial : ℝ) := by ring
  rw [hbase]
  calc 2 * (2 * Real.sin (φ / 4) ^ 2 * (q.factorial : ℝ)) ^ (1 / (q : ℝ))
      ≤ 2 * (T / 2) := by linarith
    _ = cost θ := by rw [hTdef]; ring

/-- 论文 `4/e` 估计所用的目标角特例 `φ = π`：`cost θ ≥ 2 (q!)^(1/q)`，`q = 2N+2`。 -/
theorem elementary_bound_pi {L : ℕ} {α θ : Fin L → ℝ} {N : ℕ}
    (hAdm : Admissible N Real.pi L α θ) :
    2 * (Nat.factorial (2 * N + 2) : ℝ) ^ (1 / ((2 * N + 2 : ℕ) : ℝ)) ≤ cost θ := by
  have h := elementary_bound (φ := Real.pi) Real.pi_pos le_rfl hAdm
  have hsin : Real.sin (Real.pi / 4) ^ 2 = 1 / 2 := by
    rw [Real.sin_pi_div_four]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hb : 2 * (Nat.factorial (2 * N + 2) : ℝ) * Real.sin (Real.pi / 4) ^ 2
      = (Nat.factorial (2 * N + 2) : ℝ) := by
    rw [hsin]
    ring
  calc 2 * (Nat.factorial (2 * N + 2) : ℝ) ^ (1 / ((2 * N + 2 : ℕ) : ℝ))
      = 2 * (2 * (Nat.factorial (2 * N + 2) : ℝ) * Real.sin (Real.pi / 4) ^ 2)
          ^ (1 / ((2 * N + 2 : ℕ) : ℝ)) := by rw [hb]
    _ ≤ cost θ := h

/-! ## 7. 与论文 `4(N+1)/e` 公式的比较

`elementary_bound` 给出 `cost θ ≥ 2 (q!)^(1/q)`，`q = 2N+2`；论文把它松弛成
`4(N+1)/e`（用 Stirling）。本节的 `elementary_gt_four_over_e` 证明前者**严格强于**
后者，即 `2 (q!)^(1/q) > 4(N+1)/e`（`= 2q/e`），从而 `elementary_bound` 蕴含论文的
`4/e` 系数结论。

证明不依赖 Stirling：由指数级数 `e^n = Σ_k n^k/k!`，第 `n` 项 `n^n/n!` 与正的
第 `n+1` 项 `n^(n+1)/(n+1)!` 之和不超过 `e^n`，故 `n^n/n! < e^n`，即
`(n/e)^n < n!`；两边开 `n` 次方得 `n/e < (n!)^(1/n)`。 -/

/-- `n! > (n/e)^n`（`n ≥ 1`）。证明用指数级数：`n^n/n!` 与正的
`n^(n+1)/(n+1)!` 都是 `exp n` 的级数项，故 `n^n/n! < exp n`。 -/
lemma factorial_gt_div_exp_pow (n : ℕ) (hn : 1 ≤ n) :
    (((n : ℝ) / Real.exp 1) ^ n) < (Nat.factorial n : ℝ) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hfac : (0 : ℝ) < (n.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos n)
  -- 级数 `Σ_{i<n+2} n^i/i! ≤ exp n`，拆出第 `n` 与第 `n+1` 项
  have hser := Real.sum_le_exp_of_nonneg (Nat.cast_nonneg n) (n + 2)
  have hsplit : (∑ i ∈ Finset.range (n + 2), (n : ℝ) ^ i / (i.factorial : ℝ))
      = ((∑ i ∈ Finset.range n, (n : ℝ) ^ i / (i.factorial : ℝ))
          + (n : ℝ) ^ n / (n.factorial : ℝ))
        + (n : ℝ) ^ (n + 1) / ((n + 1).factorial : ℝ) := by
    simp only [Finset.sum_range_succ]
  rw [hsplit] at hser
  have hpos_term : 0 < (n : ℝ) ^ (n + 1) / ((n + 1).factorial : ℝ) :=
    div_pos (pow_pos hn0 _) (Nat.cast_pos.mpr (Nat.factorial_pos (n + 1)))
  have hsum_nn : 0 ≤ ∑ i ∈ Finset.range n, (n : ℝ) ^ i / (i.factorial : ℝ) :=
    Finset.sum_nonneg fun i _ => by positivity
  have hlt : (n : ℝ) ^ n / (n.factorial : ℝ) < Real.exp (n : ℝ) := by linarith
  have hlt' : (n : ℝ) ^ n < (n.factorial : ℝ) * Real.exp (n : ℝ) := by
    rw [div_lt_iff₀ hfac] at hlt
    linarith
  have hexp_eq : Real.exp (n : ℝ) = (Real.exp 1) ^ n := by
    rw [← Real.exp_nat_mul, mul_one]
  rw [hexp_eq] at hlt'
  rw [div_pow, div_lt_iff₀ (pow_pos (Real.exp_pos 1) n)]
  exact hlt'

/-- `n/e < (n!)^(1/n)`（`n ≥ 1`）：`factorial_gt_div_exp_pow` 两边开 `n` 次方。 -/
lemma div_exp_lt_factorial_rpow (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) / Real.exp 1 < (n.factorial : ℝ) ^ (1 / (n : ℝ)) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnn : 0 ≤ (n : ℝ) / Real.exp 1 := le_of_lt (div_pos hn0 (Real.exp_pos 1))
  have hroot : (((n : ℝ) / Real.exp 1) ^ n) ^ (1 / (n : ℝ)) = (n : ℝ) / Real.exp 1 := by
    rw [← Real.rpow_natCast ((n : ℝ) / Real.exp 1) n,
      ← Real.rpow_mul hnn (n : ℝ) (1 / (n : ℝ)), mul_one_div, div_self (ne_of_gt hn0),
      Real.rpow_one]
  have hz : (0 : ℝ) < 1 / (n : ℝ) := by positivity
  have h := Real.rpow_lt_rpow (pow_nonneg hnn n) (factorial_gt_div_exp_pow n hn) hz
  rwa [hroot] at h

/-- **初等下界强于论文的 `4/e` 公式**：`q = 2N+2` 时
`2 (q!)^(1/q) > 4(N+1)/e = 2q/e`（`elementary_bound` 因此蕴含 `4/e` 系数）。 -/
lemma elementary_gt_four_over_e (N : ℕ) :
    4 * ((N : ℝ) + 1) / Real.exp 1
      < 2 * (((2 * N + 2).factorial : ℝ)) ^ (1 / ((2 * N + 2 : ℕ) : ℝ)) := by
  have hcast : ((2 * N + 2 : ℕ) : ℝ) = 2 * ((N : ℝ) + 1) := by push_cast; ring
  rw [hcast]
  have h := div_exp_lt_factorial_rpow (2 * N + 2) (by omega)
  rw [hcast] at h
  have heq : 4 * ((N : ℝ) + 1) / Real.exp 1
      = 2 * ((2 * ((N : ℝ) + 1)) / Real.exp 1) := by
    rw [mul_div_assoc, mul_div_assoc]
    ring
  rw [heq]
  linarith

end RobustZ
