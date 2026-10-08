import RobustZ.Statement

/-!
# M2：初等结构引理

本文件给出：
* 生成元 `Jx = -i σx`、`Jz = -i σz` 的反厄米性，以及 `Xrot`、`Zrot`、`U`、`V = U_1ᴴ U_λ` 的酉性；
* `h = ¼ tr((V-1)ᴴ(V-1))`，从而 `0 ≤ h ≤ 2`（论文 §2.1）；
* 代价集合的下界（`Tmin` 是真下确界）。
-/

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

namespace RobustZ

/-! ## 1. 生成元与酉性 -/

lemma Jx_conjTranspose : Jxᴴ = -Jx := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Jx, sigmaX, Matrix.conjTranspose_apply]

lemma Jz_conjTranspose : Jzᴴ = -Jz := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Jz, sigmaZ, Matrix.conjTranspose_apply]

/-- 实标量乘反厄米元仍反厄米。 -/
lemma conjTranspose_smul_real (r : ℝ) (J : M2) (hJ : Jᴴ = -J) :
    ((r • J)ᴴ) = -(r • J) := by
  rw [Matrix.conjTranspose_smul, hJ, smul_neg]
  simp

/-- 反厄米元的指数是酉的。 -/
lemma exp_conjTranspose_mul_exp (A : M2) (hA : Aᴴ = -A) :
    (NormedSpace.exp A)ᴴ * NormedSpace.exp A = 1 := by
  rw [← Matrix.exp_conjTranspose, hA]
  rw [← Matrix.exp_add_of_commute (-A) A (Commute.neg_left (Commute.refl A))]
  simp

lemma exp_mul_exp_conjTranspose (A : M2) (hA : Aᴴ = -A) :
    NormedSpace.exp A * (NormedSpace.exp A)ᴴ = 1 := by
  rw [← Matrix.exp_conjTranspose, hA]
  rw [← Matrix.exp_add_of_commute A (-A) (Commute.neg_right (Commute.refl A))]
  simp

lemma Jx2_conjTranspose : Jx2ᴴ = -Jx2 := by
  rw [Jx2, Matrix.conjTranspose_smul, Jx_conjTranspose, smul_neg]
  norm_num

lemma Jz2_conjTranspose : Jz2ᴴ = -Jz2 := by
  rw [Jz2, Matrix.conjTranspose_smul, Jz_conjTranspose, smul_neg]
  norm_num

lemma Xrot_conjTranspose_mul (α : ℝ) : (Xrot α)ᴴ * Xrot α = 1 := by
  rw [Xrot]
  exact exp_conjTranspose_mul_exp _ (conjTranspose_smul_real α Jx2 Jx2_conjTranspose)

lemma Xrot_mul_conjTranspose (α : ℝ) : Xrot α * (Xrot α)ᴴ = 1 := by
  rw [Xrot]
  exact exp_mul_exp_conjTranspose _ (conjTranspose_smul_real α Jx2 Jx2_conjTranspose)

lemma Zrot_conjTranspose_mul (θ : ℝ) : (Zrot θ)ᴴ * Zrot θ = 1 := by
  rw [Zrot]
  exact exp_conjTranspose_mul_exp _ (conjTranspose_smul_real θ Jz2 Jz2_conjTranspose)

lemma Zrot_mul_conjTranspose (θ : ℝ) : Zrot θ * (Zrot θ)ᴴ = 1 := by
  rw [Zrot]
  exact exp_mul_exp_conjTranspose _ (conjTranspose_smul_real θ Jz2 Jz2_conjTranspose)

lemma XZ_conjTranspose_mul (α θ : ℝ) :
    (Xrot α * Zrot θ)ᴴ * (Xrot α * Zrot θ) = 1 := by
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc (Xrot α)ᴴ (Xrot α) (Zrot θ), Xrot_conjTranspose_mul, Matrix.one_mul,
    Zrot_conjTranspose_mul]

lemma XZ_mul_conjTranspose (α θ : ℝ) :
    (Xrot α * Zrot θ) * (Xrot α * Zrot θ)ᴴ = 1 := by
  rw [Matrix.conjTranspose_mul, ← Matrix.mul_assoc,
    Matrix.mul_assoc (Xrot α) (Zrot θ) (Zrot θ)ᴴ, Zrot_mul_conjTranspose, Matrix.mul_one,
    Xrot_mul_conjTranspose]

lemma U_conjTranspose_mul (L : ℕ) (α θ : Fin L → ℝ) (lam : ℝ) :
    (U L α θ lam)ᴴ * U L α θ lam = 1 := by
  induction L with
  | zero => simp
  | succ L ih =>
      rw [U_succ, Matrix.conjTranspose_mul, Matrix.mul_assoc,
        ← Matrix.mul_assoc (U L _ _ lam)ᴴ (U L _ _ lam) (Xrot _ * Zrot _), ih, Matrix.one_mul,
        XZ_conjTranspose_mul]

lemma U_mul_conjTranspose (L : ℕ) (α θ : Fin L → ℝ) (lam : ℝ) :
    U L α θ lam * (U L α θ lam)ᴴ = 1 := by
  induction L with
  | zero => simp
  | succ L ih =>
      rw [U_succ, Matrix.conjTranspose_mul,
        Matrix.mul_assoc (U L _ _ lam) (Xrot _ * Zrot _)
          ((Xrot _ * Zrot _)ᴴ * (U L _ _ lam)ᴴ),
        ← Matrix.mul_assoc (Xrot _ * Zrot _) ((Xrot _ * Zrot _)ᴴ) (U L _ _ lam)ᴴ,
        ← Matrix.mul_assoc (U L _ _ lam) ((Xrot _ * Zrot _) * (Xrot _ * Zrot _)ᴴ) (U L _ _ lam)ᴴ,
        XZ_mul_conjTranspose, Matrix.mul_one, ih]

/-- `V = U_1ᴴ U_λ`（论文 §2.1）是酉矩阵。 -/
lemma V_conjTranspose_mul (L : ℕ) (α θ : Fin L → ℝ) (lam : ℝ) :
    (((U L α θ 1)ᴴ * U L α θ lam)ᴴ) * ((U L α θ 1)ᴴ * U L α θ lam) = 1 := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc,
    ← Matrix.mul_assoc (U L α θ 1) ((U L α θ 1)ᴴ) (U L α θ lam),
    U_mul_conjTranspose, Matrix.one_mul, U_conjTranspose_mul]

/-! ## 2. `h` 的两个界 -/

/-- `(V-1)ᴴ(V-1) = 2·1 - V - Vᴴ`（用 `VᴴV = 1`）。 -/
lemma sub_one_conjTranspose_mul_sub_one (V : M2) (hV : Vᴴ * V = 1) :
    (V - 1)ᴴ * (V - 1) = 2 • (1 : M2) - V - Vᴴ := by
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_one,
    Matrix.one_mul, hV]
  module

/-- `h = ¼ tr((V-1)ᴴ(V-1))`（论文 §2.1 的 `h = ½‖V-I‖²`，归一化 HS 范数）。 -/
lemma h_eq_quarter_trace (V : M2) (hV : Vᴴ * V = 1) :
    1 - (1 / 2) * V.trace.re = (1 / 4) * ((V - 1)ᴴ * (V - 1)).trace.re := by
  rw [sub_one_conjTranspose_mul_sub_one V hV, Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_smul,
    Matrix.trace_one, Matrix.trace_conjTranspose]
  norm_num
  ring

/-- `tr(WᴴW)` 的实部是四个元素模方之和（2×2 情形）。 -/
lemma trace_conjTranspose_mul_self_eq_normSq (W : M2) :
    (Wᴴ * W).trace.re = Complex.normSq (W 0 0) + Complex.normSq (W 0 1)
      + Complex.normSq (W 1 0) + Complex.normSq (W 1 1) := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
    Complex.mul_re, Complex.add_re, Complex.normSq_apply, Complex.conj_re, Complex.conj_im]
  ring

lemma trace_conjTranspose_mul_self_re_nonneg (W : M2) : 0 ≤ (Wᴴ * W).trace.re := by
  rw [trace_conjTranspose_mul_self_eq_normSq]
  linarith [Complex.normSq_nonneg (W 0 0), Complex.normSq_nonneg (W 0 1),
    Complex.normSq_nonneg (W 1 0), Complex.normSq_nonneg (W 1 1)]

lemma normSq_diag_le_one (V : M2) (hV : Vᴴ * V = 1) (i : Fin 2) :
    Complex.normSq (V i i) ≤ 1 := by
  have key : ∀ a : ℂ, (star a * a).re = Complex.normSq a := by
    intro a
    simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im,
      Complex.normSq_apply]
    ring
  have h := congrFun (congrFun hV i) i
  have hre : (V 0 i).re * (V 0 i).re + (V 0 i).im * (V 0 i).im
      + ((V 1 i).re * (V 1 i).re + (V 1 i).im * (V 1 i).im) = 1 := by
    have h' := congrArg Complex.re h
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two, Matrix.one_apply_eq,
      Complex.add_re, Complex.one_re, key] using h'
  have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  rcases hi with h | h
  · subst h
    rw [Complex.normSq_apply]
    nlinarith [sq_nonneg (V 1 0).re, sq_nonneg (V 1 0).im]
  · subst h
    rw [Complex.normSq_apply]
    nlinarith [sq_nonneg (V 0 1).re, sq_nonneg (V 0 1).im]

lemma abs_re_le_one_of_normSq_le_one {z : ℂ} (h : Complex.normSq z ≤ 1) :
    -(1 : ℝ) ≤ z.re ∧ z.re ≤ 1 := by
  rw [Complex.normSq_apply] at h
  have h2 : z.re ^ 2 ≤ 1 := by nlinarith [sq_nonneg z.im]
  exact abs_le.mp ((sq_le_one_iff_abs_le_one z.re).mp h2)

/-- 酉矩阵的迹的实部落在 `[-2,2]`。 -/
lemma trace_re_bounds (V : M2) (hV : Vᴴ * V = 1) :
    -(2 : ℝ) ≤ V.trace.re ∧ V.trace.re ≤ 2 := by
  have h0 := abs_re_le_one_of_normSq_le_one (normSq_diag_le_one V hV 0)
  have h1 := abs_re_le_one_of_normSq_le_one (normSq_diag_le_one V hV 1)
  have ht : V.trace = V 0 0 + V 1 1 := by simp [Matrix.trace, Fin.sum_univ_two]
  rw [ht, Complex.add_re]
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2]

theorem h_bounds (L : ℕ) (α θ : Fin L → ℝ) (lam : ℝ) :
    0 ≤ h L α θ lam ∧ h L α θ lam ≤ 2 := by
  have hV := V_conjTranspose_mul L α θ lam
  have hh : h L α θ lam = (1 / 4) * (((U L α θ 1)ᴴ * U L α θ lam - 1)ᴴ
      * ((U L α θ 1)ᴴ * U L α θ lam - 1)).trace.re := by
    rw [h]
    exact h_eq_quarter_trace _ hV
  have hW := sub_one_conjTranspose_mul_sub_one _ hV
  have htr : ((((U L α θ 1)ᴴ * U L α θ lam - 1)ᴴ
      * ((U L α θ 1)ᴴ * U L α θ lam - 1)).trace).re
      = 4 - 2 * ((U L α θ 1)ᴴ * U L α θ lam).trace.re := by
    rw [hW, Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one,
      Matrix.trace_conjTranspose]
    norm_num
    ring
  have hb := trace_re_bounds _ hV
  rw [hh, htr]
  constructor <;> linarith [hb.1, hb.2]

/-! ## 3. 代价集合的下界 -/

theorem costs_bddBelow (N : ℕ) (φ : ℝ) : BddBelow (costs N φ) := by
  refine ⟨0, ?_⟩
  rintro T ⟨L, α, θ, hAdm, rfl⟩
  exact Finset.sum_nonneg fun j _ => hAdm.1 j

end RobustZ
