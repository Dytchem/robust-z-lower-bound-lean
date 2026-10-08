import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Tactic

/-!
# Robust composite `Z` rotations: statement layer

Formal counterpart of the main theorem of
*Saturation of the Linear Lower Bound for High-Order Robust Composite `Z` Rotations*
(`paper_final/main.tex`, Theorem 1): `liminf_{N→∞} T_min(N,φ)/N ≥ 4`.

Conventions (paper §2.1):
`Z^ε(θ) = exp(-i(1+ε)θ σ_z/2)`, `X(α) = exp(-i α σ_x/2)`; `X` rotations are free,
the cost is `T = Σ_j θ_j`.

Indexing: the paper writes `U_λ = X(α_L) Z(λθ_L) ⋯ X(α_1) Z(λθ_1)` (index decreasing to
the right); here the pulses are indexed `j : Fin L` increasing from left to right, so
`U_λ = ∏_{j<L} X(α_j) Z(λ θ_j)`. The two differ only by relabelling.
-/

noncomputable section

-- `ᴴ`（共轭转置）与矩阵范数都是 Mathlib 中的作用域记号/实例。
open scoped Matrix Matrix.Norms.L2Operator
open Matrix

namespace RobustZ

/-- `2 × 2` complex matrices. -/
abbrev M2 := Matrix (Fin 2) (Fin 2) ℂ

/-- Pauli `X`. -/
def sigmaX : M2 := !![0, 1; 1, 0]

/-- Pauli `Z`. -/
def sigmaZ : M2 := !![1, 0; 0, -1]

/-- 反厄米生成元 `-i σx`（`X(α) = exp((α/2) Jx)`）。 -/
def Jx : M2 := (-Complex.I) • sigmaX

/-- 反厄米生成元 `-i σz`（`Z(θ) = exp((θ/2) Jz)`）。 -/
def Jz : M2 := (-Complex.I) • sigmaZ

/-- `-i σx / 2`：使 `X(α) = exp(α • Jx2)`。 -/
def Jx2 : M2 := (1 / 2 : ℂ) • Jx

/-- `-i σz / 2`：使 `Z(θ) = exp(θ • Jz2)`。 -/
def Jz2 : M2 := (1 / 2 : ℂ) • Jz

/-- Exact, instantaneous `X` rotation. -/
def Xrot (α : ℝ) : M2 := NormedSpace.exp (α • Jx2)

/-- `Z` evolution of angle `θ` (error-free, i.e. `ε = 0`). -/
def Zrot (θ : ℝ) : M2 := NormedSpace.exp (θ • Jz2)

/-- Target rotation `Z(φ)`. -/
def Ztgt (φ : ℝ) : M2 := Zrot φ

/-- The composite evolution `U_λ = ∏_{j<L} X(α_j) Z(λ θ_j)`，从左到右递归定义。 -/
def U : (L : ℕ) → (Fin L → ℝ) → (Fin L → ℝ) → ℝ → M2
  | 0, _, _, _ => 1
  | L + 1, α, θ, lam =>
      U L (fun j => α j.castSucc) (fun j => θ j.castSucc) lam *
        (Xrot (α (Fin.last L)) * Zrot (lam * θ (Fin.last L)))

@[simp] lemma U_zero (α θ : Fin 0 → ℝ) (lam : ℝ) : U 0 α θ lam = 1 := rfl

lemma U_succ (L : ℕ) (α θ : Fin (L + 1) → ℝ) (lam : ℝ) :
    U (L + 1) α θ lam = U L (fun j => α j.castSucc) (fun j => θ j.castSucc) lam *
      (Xrot (α (Fin.last L)) * Zrot (lam * θ (Fin.last L))) := rfl

/-- Total `Z`-evolution angle. -/
def cost {L : ℕ} (θ : Fin L → ℝ) : ℝ := ∑ j, θ j

/-- Order-`N` robustness for target `φ`: all angles nonnegative, `U_1 = Z(φ)`, and the
first `N` derivatives of `λ ↦ U_λ` vanish at `λ = 1` (paper eq. (2)). -/
def Admissible (N : ℕ) (φ : ℝ) (L : ℕ) (α θ : Fin L → ℝ) : Prop :=
  (∀ j, 0 ≤ θ j) ∧
    U L α θ 1 = Ztgt φ ∧
    ∀ k ∈ Finset.Icc 1 N, iteratedDeriv k (fun lam => U L α θ lam) 1 = 0

/-- Achievable costs. -/
def costs (N : ℕ) (φ : ℝ) : Set ℝ :=
  {T | ∃ (L : ℕ) (α θ : Fin L → ℝ), Admissible N φ L α θ ∧ T = cost θ}

/-- Minimal total `Z`-evolution angle for order-`N` robustness at target `φ`. -/
def Tmin (N : ℕ) (φ : ℝ) : ℝ := sInf (costs N φ)

/-- The scalar error function `h(λ) = 1 - ½ Tr[U_1† U_λ]` (paper §2.1). -/
def h (L : ℕ) (α θ : Fin L → ℝ) (lam : ℝ) : ℝ :=
  1 - (1 / 2) * ((U L α θ 1)ᴴ * U L α θ lam).trace.re

/-! ### Main theorem

`c_ge_four`（论文 Theorem 1 第一条不等式）与它的无上界假设二分版 `c_ge_four_or_grows`
的**证明**放在顶层模块 `RobustZ/Theorem.lean`（本文件是最底层模块，不能反向 import 分析层），
签名与论文陈述逐字对应。审计：`#print axioms RobustZ.c_ge_four`。
-/

end RobustZ
