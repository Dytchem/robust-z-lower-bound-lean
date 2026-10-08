import RobustZ.Flatness
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# M2c：有限指数和表示与矩条件

`Z(λθ)` 的两项指数分解 ⇒ 乘积仍是有限指数和 ⇒ `U_λ`、`h` 都是有限指数和，
频率绝对值不超过 `τ = Σθⱼ/2`；再结合 `h_flat` 得到矩条件
`Σᵢ cᵢ P(νᵢ) e^{iνᵢ} = 0`（`deg P < 2N+2`），这是 M3 smearing 的输入。
-/

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

namespace RobustZ

/-! ## 1. 定义与封闭性 -/

/-- 复值有限指数和，频率绝对值 ≤ τ。 -/
def ExpSumC (f : ℝ → ℂ) (τ : ℝ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (c : ι → ℂ) (ν : ι → ℝ),
    (∀ i, |ν i| ≤ τ) ∧ ∀ lam : ℝ, f lam = ∑ i, Complex.exp (((ν i * lam : ℝ) : ℂ) * Complex.I) * c i

/-- 矩阵值有限指数和，频率绝对值 ≤ τ。 -/
def ExpSumM (f : ℝ → M2) (τ : ℝ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (c : ι → M2) (ν : ι → ℝ),
    (∀ i, |ν i| ≤ τ) ∧ ∀ lam : ℝ, f lam = ∑ i, Complex.exp (((ν i * lam : ℝ) : ℂ) * Complex.I) • c i

lemma ExpSumC.const_mul {f : ℝ → ℂ} {τ : ℝ} (h : ExpSumC f τ) (C : ℂ) :
    ExpSumC (fun lam => f lam * C) τ := by
  obtain ⟨ι, hι, c, ν, hν, hf⟩ := h
  refine ⟨ι, hι, fun i => c i * C, ν, hν, fun lam => ?_⟩
  dsimp only
  rw [hf lam, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma ExpSumC.add {f g : ℝ → ℂ} {τ σ : ℝ} (hf : ExpSumC f τ) (hg : ExpSumC g σ) :
    ExpSumC (fun lam => f lam + g lam) (max τ σ) := by
  obtain ⟨ι, hι, c, ν, hν, hfc⟩ := hf
  obtain ⟨κ, hκ, d, μ, hμ, hgc⟩ := hg
  let F : ι ⊕ κ → ℂ := Sum.elim c d
  let N : ι ⊕ κ → ℝ := Sum.elim ν μ
  refine ⟨ι ⊕ κ, inferInstance, F, N, ?_, fun lam => ?_⟩
  · rintro (i | i)
    · simp only [N, Sum.elim_inl]
      exact le_trans (hν i) (le_max_left _ _)
    · simp only [N, Sum.elim_inr]
      exact le_trans (hμ i) (le_max_right _ _)
  · dsimp only
    rw [hfc lam, hgc lam]
    rw [Fintype.sum_sum_type (fun p : ι ⊕ κ =>
      Complex.exp (((N p * lam : ℝ) : ℂ) * Complex.I) * F p)]
    simp only [F, N, Sum.elim_inl, Sum.elim_inr]

lemma ExpSumC.mul {f g : ℝ → ℂ} {τ σ : ℝ} (hf : ExpSumC f τ) (hg : ExpSumC g σ) :
    ExpSumC (fun lam => f lam * g lam) (τ + σ) := by
  obtain ⟨ι, hι, c, ν, hν, hfc⟩ := hf
  obtain ⟨κ, hκ, d, μ, hμ, hgc⟩ := hg
  let F : ι × κ → ℂ := fun p => c p.1 * d p.2
  let N : ι × κ → ℝ := fun p => ν p.1 + μ p.2
  refine ⟨ι × κ, inferInstance, F, N, ?_, fun lam => ?_⟩
  · rintro ⟨i, j⟩
    simp only [N]
    calc |ν i + μ j| ≤ |ν i| + |μ j| := abs_add_le _ _
      _ ≤ τ + σ := add_le_add (hν i) (hμ j)
  · dsimp only
    rw [hfc lam, hgc lam, Finset.sum_mul_sum]
    rw [← Fintype.sum_prod_type (fun p : ι × κ =>
      Complex.exp (((ν p.1 * lam : ℝ) : ℂ) * Complex.I) * c p.1
        * (Complex.exp (((μ p.2 * lam : ℝ) : ℂ) * Complex.I) * d p.2))]
    refine Finset.sum_congr rfl fun p _ => ?_
    have hexp : Complex.exp (((ν p.1 * lam : ℝ) : ℂ) * Complex.I)
        * Complex.exp (((μ p.2 * lam : ℝ) : ℂ) * Complex.I)
        = Complex.exp ((((ν p.1 + μ p.2) * lam : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    calc Complex.exp (((ν p.1 * lam : ℝ) : ℂ) * Complex.I) * c p.1
          * (Complex.exp (((μ p.2 * lam : ℝ) : ℂ) * Complex.I) * d p.2)
        = (Complex.exp (((ν p.1 * lam : ℝ) : ℂ) * Complex.I)
            * Complex.exp (((μ p.2 * lam : ℝ) : ℂ) * Complex.I)) * (c p.1 * d p.2) := by
          ring
      _ = Complex.exp ((((ν p.1 + μ p.2) * lam : ℝ) : ℂ) * Complex.I) * (c p.1 * d p.2) := by
          rw [hexp]

lemma ExpSumM.const_mul {f : ℝ → M2} {τ : ℝ} (h : ExpSumM f τ) (C : M2) :
    ExpSumM (fun lam => C * f lam) τ := by
  obtain ⟨ι, hι, c, ν, hν, hf⟩ := h
  refine ⟨ι, hι, fun i => C * c i, ν, hν, fun lam => ?_⟩
  dsimp only
  rw [hf lam, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [mul_smul_comm]

lemma ExpSumM.one_smul_expSumC {g : ℝ → ℂ} {σ : ℝ} (hg : ExpSumC g σ) :
    ExpSumM (fun lam => g lam • (1 : M2)) σ := by
  obtain ⟨ι, hι, c, ν, hν, hgc⟩ := hg
  refine ⟨ι, hι, fun i => c i • (1 : M2), ν, hν, fun lam => ?_⟩
  dsimp only
  rw [hgc lam, Finset.sum_smul]
  exact Finset.sum_congr rfl fun i _ => by rw [mul_smul]

lemma ExpSumM.mul {f g : ℝ → M2} {τ σ : ℝ} (hf : ExpSumM f τ) (hg : ExpSumM g σ) :
    ExpSumM (fun lam => f lam * g lam) (τ + σ) := by
  obtain ⟨ι, hι, c, ν, hν, hfc⟩ := hf
  obtain ⟨κ, hκ, d, μ, hμ, hgc⟩ := hg
  let F : ι × κ → M2 := fun p => c p.1 * d p.2
  let N : ι × κ → ℝ := fun p => ν p.1 + μ p.2
  refine ⟨ι × κ, inferInstance, F, N, ?_, fun lam => ?_⟩
  · rintro ⟨i, j⟩
    simp only [N]
    calc |ν i + μ j| ≤ |ν i| + |μ j| := abs_add_le _ _
      _ ≤ τ + σ := add_le_add (hν i) (hμ j)
  · dsimp only
    rw [hfc lam, hgc lam, Finset.sum_mul_sum]
    rw [← Fintype.sum_prod_type (fun p : ι × κ =>
      (Complex.exp (((ν p.1 * lam : ℝ) : ℂ) * Complex.I) • c p.1)
        * (Complex.exp (((μ p.2 * lam : ℝ) : ℂ) * Complex.I) • d p.2))]
    refine Finset.sum_congr rfl fun p _ => ?_
    have hsm : (Complex.exp (((ν p.1 * lam : ℝ) : ℂ) * Complex.I) • c p.1)
          * (Complex.exp (((μ p.2 * lam : ℝ) : ℂ) * Complex.I) • d p.2)
        = (Complex.exp (((ν p.1 * lam : ℝ) : ℂ) * Complex.I)
            * Complex.exp (((μ p.2 * lam : ℝ) : ℂ) * Complex.I)) • (c p.1 * d p.2) := by
      rw [smul_mul_assoc, mul_smul_comm, smul_smul]
    have hexp : Complex.exp (((ν p.1 * lam : ℝ) : ℂ) * Complex.I)
        * Complex.exp (((μ p.2 * lam : ℝ) : ℂ) * Complex.I)
        = Complex.exp ((((ν p.1 + μ p.2) * lam : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hsm, hexp]

lemma ExpSumM.mul_scalar {f : ℝ → M2} {τ : ℝ} (h : ExpSumM f τ) {g : ℝ → ℂ} {σ : ℝ}
    (hg : ExpSumC g σ) : ExpSumM (fun lam => g lam • f lam) (σ + τ) := by
  have h' := (ExpSumM.one_smul_expSumC hg).mul h
  convert h' using 1
  funext lam
  rw [smul_mul_assoc, Matrix.one_mul]

/-! ## 2. `Z` 的基例 -/

lemma Jz2_eq_diagonal : Jz2 = Matrix.diagonal ![-Complex.I / 2, Complex.I / 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Jz2, Jz, sigmaZ, Matrix.diagonal, Matrix.smul_apply] <;> ring

/-- 两项指数分解：`Z(λθ) = e^{-iλθ/2}•E₀₀ + e^{iλθ/2}•E₁₁`。 -/
lemma Zrot_eq_two_terms (t : ℝ) :
    Zrot t = NormedSpace.exp (((-t / 2 : ℝ) : ℂ) * Complex.I) • (!![1, 0; 0, 0] : M2)
      + NormedSpace.exp (((t / 2 : ℝ) : ℂ) * Complex.I) • (!![0, 0; 0, 1] : M2) := by
  have hdiag : t • Jz2 = Matrix.diagonal (fun i : Fin 2 =>
      t * ![-Complex.I / 2, Complex.I / 2] i) := by
    rw [Jz2_eq_diagonal, ← Matrix.diagonal_smul]
    rfl
  rw [Zrot, hdiag, Matrix.exp_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal, Matrix.add_apply, Matrix.smul_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
      Matrix.cons_val_fin_one, Complex.exp_eq_exp_ℂ]
  all_goals first
    | rfl
    | (congr 1; push_cast; ring)

/-- 常数矩阵函数是指数和（带宽 0）。 -/
lemma expSumM_const (C : M2) : ExpSumM (fun _ : ℝ => C) 0 :=
  ⟨PUnit, inferInstance, fun _ => C, fun _ => 0, fun _ => by simp, fun _ => by simp⟩

lemma Xrot_expSumM (α : ℝ) : ExpSumM (fun _ : ℝ => Xrot α) 0 := expSumM_const _

/-- `Zrot (λ * θ)` 的指数和（频率 `±θ/2`）。 -/
lemma Zrot_mul_expSumM (θ : ℝ) : ExpSumM (fun lam : ℝ => Zrot (lam * θ)) (|θ| / 2) := by
  refine ⟨Bool, inferInstance, fun b => if b then !![1, 0; 0, 0] else !![0, 0; 0, 1],
    fun b => if b then -(θ / 2) else θ / 2, ?_, fun lam => ?_⟩
  · intro b
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, abs_neg, abs_div, abs_two]
    exacts [le_rfl, le_rfl]
  · dsimp only
    rw [Fintype.sum_bool, Zrot_eq_two_terms (lam * θ)]
    simp only [Bool.false_eq_true, ↓reduceIte]
    congr 1
    · rw [← Complex.exp_eq_exp_ℂ]
      ring_nf
    · rw [← Complex.exp_eq_exp_ℂ]
      ring_nf

/-- `U` 的指数和，带宽 `Σθⱼ/2`。 -/
lemma U_expSumM : ∀ (L : ℕ) (α θ : Fin L → ℝ),
    ExpSumM (U L α θ) (∑ j, |θ j| / 2)
  | 0, α, θ => by
      change ExpSumM (fun lam : ℝ => U 0 α θ lam) (∑ j, |θ j| / 2)
      have h : (fun lam : ℝ => U 0 α θ lam) = fun _ : ℝ => (1 : M2) := by
        funext lam; simp
      rw [h]
      simpa using expSumM_const (1 : M2)
  | L + 1, α, θ => by
      change ExpSumM (fun lam : ℝ => U (L + 1) α θ lam) (∑ j, |θ j| / 2)
      have hfun : (fun lam : ℝ => U (L + 1) α θ lam)
          = fun lam : ℝ => U L (fun j => α j.castSucc) (fun j => θ j.castSucc) lam
              * (Xrot (α (Fin.last L)) * Zrot (lam * θ (Fin.last L))) := by
        funext lam; rw [U_succ]
      rw [hfun, Fin.sum_univ_castSucc]
      have h1 := U_expSumM L (fun j => α j.castSucc) (fun j => θ j.castSucc)
      have h2 := (Xrot_expSumM (α (Fin.last L))).mul (Zrot_mul_expSumM (θ (Fin.last L)))
      have h3 := h1.mul h2
      convert h3 using 2
      ring

lemma ExpSumC.mono {f : ℝ → ℂ} {τ σ : ℝ} (h : ExpSumC f τ) (hle : τ ≤ σ) : ExpSumC f σ := by
  obtain ⟨ι, hι, c, ν, hν, hf⟩ := h
  exact ⟨ι, hι, c, ν, fun i => le_trans (hν i) hle, hf⟩

lemma ExpSumC.neg {f : ℝ → ℂ} {τ : ℝ} (h : ExpSumC f τ) :
    ExpSumC (fun lam => -f lam) τ := by
  obtain ⟨ι, hι, c, ν, hν, hf⟩ := h
  refine ⟨ι, hι, fun i => -c i, ν, hν, fun lam => ?_⟩
  dsimp only
  rw [hf lam, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma ExpSumC.const (C : ℂ) : ExpSumC (fun _ : ℝ => C) 0 :=
  ⟨PUnit, inferInstance, fun _ => C, fun _ => 0, fun _ => by simp, fun _ => by simp⟩

lemma ExpSumC.starConj {f : ℝ → ℂ} {τ : ℝ} (h : ExpSumC f τ) :
    ExpSumC (fun lam => star (f lam)) τ := by
  obtain ⟨ι, hι, c, ν, hν, hf⟩ := h
  refine ⟨ι, hι, fun i => star (c i), fun i => -ν i, ?_, fun lam => ?_⟩
  · intro i; simpa using hν i
  · dsimp only
    rw [hf lam, star_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hexp : star (Complex.exp (((ν i * lam : ℝ) : ℂ) * Complex.I))
        = Complex.exp ((((-ν i) * lam : ℝ) : ℂ) * Complex.I) := by
      rw [show star (Complex.exp (((ν i * lam : ℝ) : ℂ) * Complex.I))
          = starRingEnd ℂ (Complex.exp (((ν i * lam : ℝ) : ℂ) * Complex.I)) from rfl,
        ← Complex.exp_conj]
      congr 1
      simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, map_neg]
      push_cast
      ring
    rw [star_mul, hexp, mul_comm]

/-- 矩阵指数和的迹是复值指数和。 -/
lemma ExpSumM.trace {f : ℝ → M2} {τ : ℝ} (h : ExpSumM f τ) :
    ExpSumC (fun lam => (f lam).trace) τ := by
  obtain ⟨ι, hι, c, ν, hν, hf⟩ := h
  refine ⟨ι, hι, fun i => (c i).trace, ν, hν, fun lam => ?_⟩
  dsimp only
  rw [hf lam, Matrix.trace_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [Matrix.trace_smul]; ring

/-! ## 3. `h` 的指数和表示 -/

/-- `h` 的复化是指数和，带宽 `Σ|θⱼ|/2`。 -/
lemma h_expSumC (L : ℕ) (α θ : Fin L → ℝ) :
    ExpSumC (fun lam => (h L α θ lam : ℂ)) (∑ j, |θ j| / 2) := by
  set τ : ℝ := ∑ j, |θ j| / 2 with hτ
  have hW : ExpSumM (fun lam : ℝ => (U L α θ 1)ᴴ * U L α θ lam) τ :=
    (U_expSumM L α θ).const_mul _
  have hG : ExpSumC (fun lam : ℝ => ((U L α θ 1)ᴴ * U L α θ lam).trace) τ := hW.trace
  have hcoe : (fun lam : ℝ => (h L α θ lam : ℂ))
      = fun lam : ℝ => 1 + -((((U L α θ 1)ᴴ * U L α θ lam).trace
          + star (((U L α θ 1)ᴴ * U L α θ lam).trace)) * (1 / 4)) := by
    funext lam
    set z : ℂ := ((U L α θ 1)ᴴ * U L α θ lam).trace with hzdef
    rw [h]
    push_cast
    have hz : ((z.re : ℝ) : ℂ) = (z + star z) / 2 := by
      rw [Complex.star_def, Complex.add_conj]
      push_cast
      ring
    rw [hz]
    ring
  rw [hcoe]
  have hinner : ExpSumC (fun lam : ℝ => ((U L α θ 1)ᴴ * U L α θ lam).trace
      + star (((U L α θ 1)ᴴ * U L α θ lam).trace)) (max τ τ) := hG.add hG.starConj
  have hmain := (ExpSumC.const (1 : ℂ)).add (hinner.const_mul (1 / 4)).neg
  refine ExpSumC.mono hmain ?_
  have hτ0 : 0 ≤ τ := Finset.sum_nonneg fun j _ => by positivity
  rw [max_self, max_eq_right hτ0]

/-! ## 4. 矩条件 -/

/-- 实值函数复化的导数。 -/
lemma deriv_ofReal (f : ℝ → ℝ) (x : ℝ) :
    deriv (fun y : ℝ => (f y : ℂ)) x = ((deriv f x : ℝ) : ℂ) := by
  by_cases h : DifferentiableAt ℝ f x
  · have h2 : HasDerivAt (fun y : ℝ => (f y : ℂ)) ((deriv f x : ℝ) : ℂ) x :=
      HasDerivAt.ofReal_comp h.hasDerivAt
    exact HasDerivAt.deriv h2
  · have h' : ¬ DifferentiableAt ℝ (fun y : ℝ => (f y : ℂ)) x := by
      intro hd
      apply h
      have hcomp : f = fun y : ℝ => Complex.reCLM ((fun y : ℝ => (f y : ℂ)) y) := by
        funext y
        simp
      rw [hcomp]
      exact Complex.reCLM.differentiableAt.comp x hd
    rw [deriv_zero_of_not_differentiableAt h', deriv_zero_of_not_differentiableAt h]
    simp

lemma iteratedDeriv_ofReal (n : ℕ) (f : ℝ → ℝ) (x : ℝ) :
    iteratedDeriv n (fun y : ℝ => (f y : ℂ)) x = ((iteratedDeriv n f x : ℝ) : ℂ) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      have hL : iteratedDeriv (n + 1) (fun y : ℝ => (f y : ℂ)) x
          = deriv (fun y : ℝ => ((iteratedDeriv n f y : ℝ) : ℂ)) x := by
        rw [iteratedDeriv_succ]
        congr 1
        funext y
        exact ih y
      rw [hL, deriv_ofReal, iteratedDeriv_succ]

/-- `y ↦ e^{a y}` 的导数。 -/
lemma hasDerivAt_cexp_const_mul (a : ℂ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => Complex.exp (a * y)) (Complex.exp (a * x) * a) x := by
  have h1 : HasDerivAt (fun y : ℝ => a * (y : ℂ)) a x := by
    simpa using HasDerivAt.const_mul a (HasDerivAt.ofReal_comp (hasDerivAt_id x))
  exact HasDerivAt.cexp h1

/-- 单项 `y ↦ e^{iνy}·b` 的导数（形式与指数和定义逐字一致）。 -/
lemma hasDerivAt_expSumTerm (ν : ℝ) (b : ℂ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => Complex.exp (((ν * y : ℝ) : ℂ) * Complex.I) * b)
      (Complex.exp (((ν * x : ℝ) : ℂ) * Complex.I) * ((ν : ℂ) * Complex.I) * b) x := by
  have h0 : HasDerivAt (fun y : ℝ => Complex.exp ((((ν : ℝ) : ℂ) * Complex.I) * (y : ℂ)))
      (Complex.exp ((((ν : ℝ) : ℂ) * Complex.I) * (x : ℂ)) * (((ν : ℝ) : ℂ) * Complex.I)) x :=
    hasDerivAt_cexp_const_mul (((ν : ℝ) : ℂ) * Complex.I) x
  have h1 := HasDerivAt.mul_const h0 b
  have hfun : (fun y : ℝ => Complex.exp ((((ν : ℝ) : ℂ) * Complex.I) * (y : ℂ)) * b)
      = fun y : ℝ => Complex.exp (((ν * y : ℝ) : ℂ) * Complex.I) * b := by
    funext y
    congr 2
    push_cast
    ring
  have hderiv : Complex.exp ((((ν : ℝ) : ℂ) * Complex.I) * (x : ℂ)) * (((ν : ℝ) : ℂ) * Complex.I) * b
      = Complex.exp (((ν * x : ℝ) : ℂ) * Complex.I) * ((ν : ℂ) * Complex.I) * b := by
    congr 2
    push_cast
    ring
  rw [hfun, hderiv] at h1
  exact h1

/-- 指数和的逐项求导公式。 -/
lemma iteratedDeriv_expSum {ι : Type} [Fintype ι] {c : ι → ℂ} {ν : ι → ℝ} {f : ℝ → ℂ}
    (hf : ∀ lam : ℝ, f lam = ∑ i, Complex.exp (((ν i * lam : ℝ) : ℂ) * Complex.I) * c i)
    (n : ℕ) (lam : ℝ) :
    iteratedDeriv n f lam = ∑ i, Complex.exp (((ν i * lam : ℝ) : ℂ) * Complex.I)
      * ((((ν i : ℂ) * Complex.I) ^ n) * c i) := by
  induction n generalizing lam with
  | zero =>
      rw [iteratedDeriv_zero, hf lam]
      exact Finset.sum_congr rfl fun i _ => by ring
  | succ n ih =>
      have hfun : iteratedDeriv n f = fun y : ℝ => ∑ i,
          Complex.exp (((ν i * y : ℝ) : ℂ) * Complex.I) * ((((ν i : ℂ) * Complex.I) ^ n) * c i) := by
        funext y
        exact ih y
      have hfun2 : (fun y : ℝ => ∑ i, Complex.exp (((ν i * y : ℝ) : ℂ) * Complex.I)
            * ((((ν i : ℂ) * Complex.I) ^ n) * c i))
          = ∑ i, (fun y : ℝ => Complex.exp (((ν i * y : ℝ) : ℂ) * Complex.I)
            * ((((ν i : ℂ) * Complex.I) ^ n) * c i)) := by
        funext y
        rw [Finset.sum_apply]
      rw [iteratedDeriv_succ, hfun, hfun2]
      rw [deriv_sum (fun i _ => HasDerivAt.differentiableAt
        (hasDerivAt_expSumTerm (ν i) ((((ν i : ℂ) * Complex.I) ^ n) * c i) lam))]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [HasDerivAt.deriv (hasDerivAt_expSumTerm (ν i) ((((ν i : ℂ) * Complex.I) ^ n) * c i) lam)]
      ring

/-- **矩条件**（M3 的输入）：`h` 的复化是有限指数和，且其系数满足全部低阶矩条件。 -/
theorem h_moments (N : ℕ) (φ : ℝ) (L : ℕ) (α θ : Fin L → ℝ) (hAdm : Admissible N φ L α θ) :
    ∃ (ι : Type) (_ : Fintype ι) (c : ι → ℂ) (ν : ι → ℝ),
      (∀ i, |ν i| ≤ (∑ j, θ j) / 2) ∧
      (∀ lam : ℝ, (h L α θ lam : ℂ)
        = ∑ i, Complex.exp (((ν i * lam : ℝ) : ℂ) * Complex.I) * c i) ∧
      (∀ P : Polynomial ℂ, P.natDegree < 2 * N + 2 →
        ∑ i, Complex.exp (((ν i : ℝ) : ℂ) * Complex.I) * P.eval ((ν i : ℂ)) * c i = 0) ∧
      ((h L α θ 0 : ℝ) : ℂ) = ∑ i, c i := by
  obtain ⟨ι, hι, c, ν, hν, hf⟩ := h_expSumC L α θ
  refine ⟨ι, hι, c, ν, ?_, hf, ?_, ?_⟩
  · intro i
    have h1 : (∑ j, |θ j| / 2) = (∑ j, θ j) / 2 := by
      rw [Finset.sum_div]
      congr 1
      funext j
      rw [abs_of_nonneg (hAdm.1 j)]
    rw [h1] at hν
    exact hν i
  · intro P hP
    have hderiv : ∀ k < 2 * N + 2,
        iteratedDeriv k (fun lam : ℝ => (h L α θ lam : ℂ)) 1 = 0 := by
      intro k hk
      rw [iteratedDeriv_ofReal, h_flat N φ L α θ hAdm k hk]
      simp
    have hmono : ∀ k < 2 * N + 2,
        ∑ i, Complex.exp ((ν i : ℂ) * Complex.I) * (ν i : ℂ) ^ k * c i = 0 := by
      intro k hk
      have hk' := hderiv k hk
      rw [iteratedDeriv_expSum hf k 1] at hk'
      have hterm : ∀ i, Complex.exp (((ν i * 1 : ℝ) : ℂ) * Complex.I)
            * ((((ν i : ℂ) * Complex.I) ^ k) * c i)
          = Complex.I ^ k * (Complex.exp ((ν i : ℂ) * Complex.I) * (ν i : ℂ) ^ k * c i) := by
        intro i
        rw [mul_one, mul_pow]
        ring
      rw [Finset.sum_congr rfl fun i _ => hterm i, ← Finset.mul_sum] at hk'
      exact (mul_eq_zero.mp hk').resolve_left (pow_ne_zero _ Complex.I_ne_zero)
    calc ∑ i, Complex.exp ((ν i : ℂ) * Complex.I) * P.eval ((ν i : ℂ)) * c i
        = ∑ i, ∑ k ∈ Finset.range (P.natDegree + 1),
            Complex.exp ((ν i : ℂ) * Complex.I) * (P.coeff k * (ν i) ^ k) * c i := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Polynomial.eval_eq_sum_range (p := P) (ν i : ℂ), Finset.mul_sum,
            Finset.sum_mul]
      _ = ∑ k ∈ Finset.range (P.natDegree + 1),
            P.coeff k * (∑ i, Complex.exp ((ν i : ℂ) * Complex.I) * (ν i : ℂ) ^ k * c i) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = 0 := by
          refine Finset.sum_eq_zero fun k hk => ?_
          have hk2 : k < 2 * N + 2 :=
            lt_of_le_of_lt (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) hP
          rw [hmono k hk2]
          ring
  · have h0 := hf 0
    dsimp only at h0
    rw [h0]
    exact Finset.sum_congr rfl fun i _ => by simp

end RobustZ
