import RobustZ.HTrace

/-!
# `h(0)` 的精确值与单侧下界（`HTraceLower.lean`）

论文 §2.1 端点（`paper_final/main.tex`，eq. `eq:endpoint`）：

```
h(0) = 1 - cos(φ/2) * cos(A/2),   A = Σ_j α_j ≥ ...
```

因为 `λ = 0` 时 `Z(0) = 1`，序列退化为单个 `X` 旋转 `U_0 = X(A)`（`HTrace.lean`
中的 `U_lam_zero`），端点值多出因子 `cos(A/2)`。由 `cos ≤ 1` 得论文实际使用的
单侧下界（`0 ≤ φ ≤ π` 时 `cos(φ/2) ≥ 0`）：

```
h(0) ≥ 1 - cos(φ/2) = 2 sin²(φ/4).
```

本文件给出：
* `Had`：Hadamard 共轭 `H Z(t) H⁻¹ = X(t)`（`H = !![1,1;1,-1]`，`H⁻¹ = ½H`）；
* `Xrot_eq_two_terms`：`X(t) = e^{-it/2} P₊ + e^{it/2} P₋`（`P±` 是 `σx` 的谱投影）；
* `trace_conjTranspose_Zrot_mul_Xrot`：`tr(Z(φ)ᴴ X(a)) = 2 cos(φ/2) cos(a/2)`；
* `h_zero_eq` / `h_zero_ge`：精确端点值与下界。
-/

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

namespace RobustZ

/-! ## 1. `2 × 2` 基础计算 -/

/-- 单位矩阵的 `E₀₀ + E₁₁` 分解。 -/
lemma E00_add_E11 : (!![1, 0; 0, 0] : M2) + !![0, 0; 0, 1] = 1 := by
  rw [Matrix.one_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.add_apply]

/-- `σz = E₀₀ - E₁₁`。 -/
lemma E00_sub_E11 : (!![1, 0; 0, 0] : M2) - !![0, 0; 0, 1] = sigmaZ := by
  rw [sigmaZ]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.sub_apply]

lemma trace_one_M2 : (1 : M2).trace = 2 := by
  rw [Matrix.trace_one]
  simp

lemma trace_sigmaX : (sigmaX : M2).trace = 0 := by
  rw [sigmaX, Matrix.trace_fin_two_of]
  norm_num

lemma trace_sigmaZ : (sigmaZ : M2).trace = 0 := by
  rw [sigmaZ, Matrix.trace_fin_two_of]
  norm_num

lemma trace_sigmaZ_mul_sigmaX : (sigmaZ * sigmaX).trace = 0 := by
  rw [sigmaZ, sigmaX, Matrix.mul_fin_two, Matrix.trace_fin_two_of]
  norm_num

/-- `2 × 2` 乘积的迹用元素表示。 -/
lemma trace_mul_fin_two (A B : M2) :
    (A * B).trace = A 0 0 * B 0 0 + A 0 1 * B 1 0 + A 1 0 * B 0 1 + A 1 1 * B 1 1 := by
  simp only [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-! ## 2. Hadamard 共轭：`H Z(t) H⁻¹ = X(t)` -/

/-- 未归一化 Hadamard 矩阵。 -/
def Had : M2 := !![1, 1; 1, -1]

lemma Had_mul_Had : Had * Had = (2 : ℂ) • (1 : M2) := by
  rw [Had, Matrix.mul_fin_two, Matrix.one_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply] <;> norm_num

lemma Had_mul_half : Had * ((1 / 2 : ℂ) • Had) = 1 := by
  rw [Matrix.mul_smul, Had_mul_Had, smul_smul,
    show ((1 / 2 : ℂ) * 2) = 1 by norm_num, one_smul]

lemma half_mul_Had : ((1 / 2 : ℂ) • Had) * Had = 1 := by
  rw [Matrix.smul_mul, Had_mul_Had, smul_smul,
    show ((1 / 2 : ℂ) * 2) = 1 by norm_num, one_smul]

lemma Had_isUnit : IsUnit Had :=
  ⟨⟨Had, (1 / 2 : ℂ) • Had, Had_mul_half, half_mul_Had⟩, rfl⟩

lemma Had_inv : Had⁻¹ = (1 / 2 : ℂ) • Had := Matrix.inv_eq_right_inv Had_mul_half

/-- `H (-i σz/2) H = 2 (-i σx/2)`，即 `H Jz2 H⁻¹ = Jx2`。 -/
lemma Had_Jz2_Had : Had * Jz2 * Had = (2 : ℂ) • Jx2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Had, Jz2, Jz, Jx2, Jx, sigmaZ, sigmaX, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.smul_apply] <;>
    ring

lemma smul_Jx2_eq_conj (t : ℝ) : t • Jx2 = Had * (t • Jz2) * Had⁻¹ := by
  rw [Had_inv, Matrix.mul_smul Had t Jz2, Matrix.smul_mul t (Had * Jz2) ((1 / 2 : ℂ) • Had),
    Matrix.mul_smul (Had * Jz2) (1 / 2 : ℂ) Had, Had_Jz2_Had, smul_smul,
    show ((1 / 2 : ℂ) * 2) = 1 by norm_num, one_smul]

/-- 共轭把 `Z` 旋转变成 `X` 旋转：`X(t) = H Z(t) H⁻¹`。 -/
lemma Xrot_eq_conj (t : ℝ) : Xrot t = Had * Zrot t * Had⁻¹ := by
  rw [Xrot, smul_Jx2_eq_conj t, Zrot, Matrix.exp_conj Had (t • Jz2) Had_isUnit]

/-- `σx` 的谱投影 `P₊ = (1 + σx)/2`（未归一化写法 `½!![1,1;1,1]`）。 -/
def Pplus : M2 := (1 / 2 : ℂ) • !![1, 1; 1, 1]

/-- `σx` 的谱投影 `P₋ = (1 - σx)/2`。 -/
def Pminus : M2 := (1 / 2 : ℂ) • !![1, -1; -1, 1]

lemma Had_E00_Had : Had * (!![1, 0; 0, 0] : M2) * Had = !![1, 1; 1, 1] := by
  rw [Had, Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num

lemma Had_E11_Had : Had * (!![0, 0; 0, 1] : M2) * Had = !![1, -1; -1, 1] := by
  rw [Had, Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num

lemma Had_conj_E00 : Had * (!![1, 0; 0, 0] : M2) * Had⁻¹ = Pplus := by
  rw [Had_inv, Pplus, Matrix.mul_smul, Had_E00_Had]

lemma Had_conj_E11 : Had * (!![0, 0; 0, 1] : M2) * Had⁻¹ = Pminus := by
  rw [Had_inv, Pminus, Matrix.mul_smul, Had_E11_Had]

/-- `X` 旋转的两项指数分解（`σx` 的谱分解）。 -/
lemma Xrot_eq_two_terms (t : ℝ) :
    Xrot t = NormedSpace.exp (((-t / 2 : ℝ) : ℂ) * Complex.I) • Pplus
      + NormedSpace.exp (((t / 2 : ℝ) : ℂ) * Complex.I) • Pminus := by
  rw [Xrot_eq_conj, Zrot_eq_two_terms, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Had_conj_E00, Had_conj_E11]

/-! ## 3. `tr(Z(φ)ᴴ X(a)) = 2 cos(φ/2) cos(a/2)` -/

lemma trace_E00_Pplus : ((!![1, 0; 0, 0] : M2) * Pplus).trace = 1 / 2 := by
  simp only [Pplus, Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_fin_two,
    Matrix.trace_fin_two_of, smul_eq_mul]
  norm_num

lemma trace_E00_Pminus : ((!![1, 0; 0, 0] : M2) * Pminus).trace = 1 / 2 := by
  simp only [Pminus, Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_fin_two,
    Matrix.trace_fin_two_of, smul_eq_mul]
  norm_num

lemma trace_E11_Pplus : ((!![0, 0; 0, 1] : M2) * Pplus).trace = 1 / 2 := by
  simp only [Pplus, Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_fin_two,
    Matrix.trace_fin_two_of, smul_eq_mul]
  norm_num

lemma trace_E11_Pminus : ((!![0, 0; 0, 1] : M2) * Pminus).trace = 1 / 2 := by
  simp only [Pminus, Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_fin_two,
    Matrix.trace_fin_two_of, smul_eq_mul]
  norm_num

/-- **端点迹公式**：`tr(Z(φ)ᴴ X(a)) = 2 cos(φ/2) cos(a/2)`。 -/
lemma trace_conjTranspose_Zrot_mul_Xrot (φ a : ℝ) :
    (((Zrot φ)ᴴ) * Xrot a).trace
      = ((2 * (Real.cos (φ / 2) * Real.cos (a / 2)) : ℝ) : ℂ) := by
  rw [Zrot_conjTranspose_eq, trace_mul_fin_two, Zrot_eq_two_terms, Xrot_eq_two_terms]
  simp only [Matrix.add_apply, Matrix.smul_apply, Pplus, Pminus, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
    Matrix.cons_val_fin_one]
  rw [← Complex.exp_eq_exp_ℂ]
  rw [Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I,
    Complex.exp_ofReal_mul_I]
  simp only [neg_div, neg_neg, Real.cos_neg, Real.sin_neg]
  push_cast
  ring

/-! ## 4. `h(0)` 的精确值与下界 -/

/-- **精确端点值**：`h(0) = 1 - cos(φ/2) cos(A/2)`，`A = Σ_j α_j`。 -/
lemma h_zero_eq (φ : ℝ) (L : ℕ) (α θ : Fin L → ℝ) (hU1 : U L α θ 1 = Ztgt φ) :
    h L α θ 0 = 1 - Real.cos (φ / 2) * Real.cos ((∑ j, α j) / 2) := by
  rw [h_zero_general φ L α θ hU1, U_lam_zero L α θ, Ztgt, trace_conjTranspose_Zrot_mul_Xrot]
  simp only [Complex.ofReal_re]
  ring

/-- **单侧下界**（论文 `eq:endpoint` 实际使用的形式）：`h(0) ≥ 1 - cos(φ/2)`。 -/
lemma h_zero_ge (φ : ℝ) (hφ0 : 0 ≤ φ) (hφπ : φ ≤ Real.pi) (L : ℕ) (α θ : Fin L → ℝ)
    (hU1 : U L α θ 1 = Ztgt φ) : 1 - Real.cos (φ / 2) ≤ h L α θ 0 := by
  rw [h_zero_eq φ L α θ hU1]
  have hcφ : 0 ≤ Real.cos (φ / 2) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith⟩
  have hca : Real.cos ((∑ j, α j) / 2) ≤ 1 := Real.cos_le_one _
  nlinarith

/-- **结构引理**：任何 `X`-旋转的乘积仍是一个 `X`-旋转（这里整体相位 `s = 1`）。 -/
lemma U_lam_zero_exists (L : ℕ) (α θ : Fin L → ℝ) :
    ∃ (a : ℝ) (s : ℂ), ‖s‖ = 1 ∧ U L α θ 0 = s • Xrot a :=
  ⟨∑ j, α j, 1, by simp, by rw [one_smul]; exact U_lam_zero L α θ⟩

/-- 同轴 `X` 旋转两两交换（角度可加），故乘积可合并为单个 `X`。 -/
lemma Xrot_commute (a b : ℝ) : Commute (Xrot a) (Xrot b) := by
  show Xrot a * Xrot b = Xrot b * Xrot a
  rw [Xrot_add, Xrot_add, add_comm]

end RobustZ
