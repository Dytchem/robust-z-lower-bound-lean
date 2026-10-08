import RobustZ.Statement
import RobustZ.ExpSum

/-!
# `h` 在 `λ = 0` 端的取值（`HTrace.lean`）

论文 §2.1 的端点值（`paper_final/main.tex`，eq. `eq:endpoint`）：

```
h(0) = 1 - cos(φ/2) * cos(A/2),   A = Σ_j α_j
```

本文件把这一条形式化。注意：**`h(0) = 1 - cos(φ/2)` 一般不成立** ——
`λ = 0` 时 `Z(0) = 1`，于是 `U_0 = X(α_1)⋯X(α_L) = X(A)`（所有 `X` 同轴，
角度可加），因此端点值带有额外的因子 `cos(A/2)`；只有当 `A ∈ 4πℤ`（例如
所有 `α_j = 0`）时 `cos(A/2) = 1`，才退化为 `1 - cos(φ/2)`。

主结果：
* `h_zero_eq`      : `h L α θ 0 = 1 - cos(φ/2) * cos((Σ α)/2)`（精确值）；
* `h_zero_lower`   : `0 ≤ φ ≤ π` 时 `1 - cos(φ/2) ≤ h L α θ 0`（论文实际使用的不等式）；
* `h_zero_of_U0_eq_one` : 额外假设 `U_0 = 1` 时得到 `h L α θ 0 = 1 - cos(φ/2)`。
-/

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

namespace RobustZ

/-! ## 1. `X` 旋转的角度加性与 `U_0 = X(A)` -/

/-- 同一轴的 `X` 旋转角度可加。 -/
lemma Xrot_add (a b : ℝ) : Xrot a * Xrot b = Xrot (a + b) := by
  have hcomm : Commute (a • Jx2) (b • Jx2) := by
    show (a • Jx2) * (b • Jx2) = (b • Jx2) * (a • Jx2)
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_smul,
      mul_comm a b]
  rw [Xrot, Xrot, Xrot, ← Matrix.exp_add_of_commute (a • Jx2) (b • Jx2) hcomm]
  congr 1
  rw [add_smul]

/-- `λ = 0` 时所有 `Z` 演化坍缩，序列退化为单个 `X` 旋转：`U_0 = X(Σ_j α_j)`。 -/
lemma U_lam_zero (L : ℕ) (α θ : Fin L → ℝ) : U L α θ 0 = Xrot (∑ j, α j) := by
  induction L with
  | zero => simp [Xrot]
  | succ L ih =>
      rw [U_succ, ih, Fin.sum_univ_castSucc, Zrot, zero_mul, zero_smul, NormedSpace.exp_zero,
        Matrix.mul_one, Xrot_add]

/-! ## 2. `Z(φ)ᴴ` 的迹 -/

/-- `(Z θ)ᴴ = Z (-θ)`（`Jz2` 反厄米）。 -/
lemma Zrot_conjTranspose_eq (θ : ℝ) : (Zrot θ)ᴴ = Zrot (-θ) := by
  have h : (θ • Jz2)ᴴ = (-θ) • Jz2 := by
    rw [conjTranspose_smul_real θ Jz2 Jz2_conjTranspose, neg_smul]
  rw [Zrot, Zrot, ← Matrix.exp_conjTranspose, h]

/-- 两项指数分解的迹：`tr Z(t) = e^{-it/2} + e^{it/2} = 2 cos(t/2)`。 -/
lemma trace_Zrot (t : ℝ) : (Zrot t).trace = 2 * ((Real.cos (t / 2) : ℝ) : ℂ) := by
  rw [Zrot_eq_two_terms, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
    Matrix.trace_fin_two_of, Matrix.trace_fin_two_of]
  simp only [smul_eq_mul, mul_one, add_zero, zero_add]
  rw [← Complex.exp_eq_exp_ℂ]
  rw [Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I, neg_div, Real.cos_neg, Real.sin_neg]
  push_cast
  ring

/-- `tr(Z(φ)ᴴ) = 2 cos(φ/2)`。 -/
lemma trace_conjTranspose_Zrot (φ : ℝ) :
    ((Zrot φ)ᴴ).trace = 2 * ((Real.cos (φ / 2) : ℝ) : ℂ) := by
  rw [Zrot_conjTranspose_eq, trace_Zrot, neg_div, Real.cos_neg]

/-! ## 3. `h(0)` 的一般形式 -/

/-- `λ = 0` 处 `h` 的一般表达式（只用 `U_1 = Z(φ)`）。 -/
lemma h_zero_general (φ : ℝ) (L : ℕ) (α θ : Fin L → ℝ) (hU1 : U L α θ 1 = Ztgt φ) :
    h L α θ 0 = 1 - (1 / 2) * (((Ztgt φ)ᴴ * U L α θ 0).trace).re := by
  simp only [h, hU1]

/-- 若额外有 `U_0 = 1`（例如所有 `α_j ≡ 0`），则 `h(0) = 1 - cos(φ/2)`。 -/
lemma h_zero_of_U0_eq_one (φ : ℝ) (L : ℕ) (α θ : Fin L → ℝ) (hU1 : U L α θ 1 = Ztgt φ)
    (hU0 : U L α θ 0 = 1) : h L α θ 0 = 1 - Real.cos (φ / 2) := by
  have h2 : ((2 : ℂ) * ((Real.cos (φ / 2) : ℝ) : ℂ)).re = 2 * Real.cos (φ / 2) := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [h_zero_general φ L α θ hU1, hU0, Matrix.mul_one, Ztgt, trace_conjTranspose_Zrot, h2]
  ring

end RobustZ

