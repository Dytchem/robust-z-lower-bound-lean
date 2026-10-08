import RobustZ.JensenRung
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Jensen bridges: discharging `jord` and `jgrow` for the Jensen rung

This module discharges the two explicit analytic hypotheses of
`RobustZ.jensen_rung` (`RobustZ/JensenRung.lean`), so that the Jensen rung
becomes unconditional.

## The canonical complexification `Hcanon`

For pulse data `(L, α, θ)` we complexify the propagator directly at matrix
level: with `ZC w = exp (w • Jz2)` (complex-`Z` rotation) and

```
UC L α θ z = ∏ X(αⱼ) · ZC (z · θⱼ),
```

we set `Hcanon L α θ z = 1 - ½ · Tr[U₁ᴴ · UC(z)]`, where `U₁ = U L α θ 1`.
This is entire (finite product of entire matrix exponentials).

## Bridge `jord` (order)

The tree proves real flatness `h_flat`: all real iterated derivatives of
`h` at `1` vanish below order `q = 2N+2`.  Two facts lift this to the
divisor lower bound `((q : ℕ) : ℤ) ≤ divisor Hcanon (closedBall 0 R) 1`:

* `Hcanon ↑lam = ↑(h lam)` on `ℝ` (`Hcanon_real`).  This is the one place
  needing genuine input: `Tr[U₁ᴴ U_λ]` is *real* because every factor is a
  unit quaternion `!![a,b;-conj b,conj a]` (`IsQuat`), and such matrices are
  closed under product and conjugate transpose with real trace.  Hence the
  complex `1 - ½Tr` agrees with the real `1 - ½Re Tr` on `ℝ`.
* complex iterated derivatives at a real point agree with real ones
  (`iteratedDeriv_Hcanon_restrict`, via `HasDerivAt.comp_ofReal`), so the
  vanishing transfers; `natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero`
  gives the order bound.  Infinite order is excluded by the identity theorem
  (`Hcanon 0 = h 0 ≥ s > 0`), converting the order bound into the divisor
  bound through `AnalyticOnNhd.divisor_apply`.

## Bridge `jgrow` (growth)

`‖ZC w‖ ≤ exp(|Im w|/2)` from the diagonal form (the two eigenvalues have
moduli `exp(±Im w/2)`); `‖Xrot‖ = 1` (unitary, C⋆-identity); the product
over pulses gives `‖UC z‖ ≤ exp((Σ|θⱼ|/2)·|Im z|)`, i.e. with
`cost θ / 2` under nonnegativity; `|Tr| ≤ 2‖·‖` (`norm_trace_le_two`)
gives `‖Hcanon z‖ ≤ 1 + exp ≤ 2·exp`.

## Wrappers

`jensen_rung_final` (and `jensen_rung_pi_final`) apply `jensen_rung`
(`jensen_rung_pi`) to `Hcanon`, with no `jord`/`jgrow` hypotheses.
-/

noncomputable section

open Metric Filter MeromorphicOn MeasureTheory
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator

namespace RobustZ

/-! ## 1. Complexified rotations and propagator -/

/-- Complexified `Z` rotation `ZC w = exp (w • Jz2)`.  For real `t`,
`ZC ↑t = Zrot t`. -/
def ZC (w : ℂ) : M2 := NormedSpace.exp (w • Jz2)

/-- Two-term form of `ZC`, mirroring `Zrot_eq_two_terms`. -/
lemma ZC_eq_two_terms (w : ℂ) :
    ZC w = NormedSpace.exp (w • (-Complex.I / 2)) • (!![1, 0; 0, 0] : M2)
      + NormedSpace.exp (w • (Complex.I / 2)) • (!![0, 0; 0, 1] : M2) := by
  have hdiag : w • Jz2 = Matrix.diagonal (w • ![-Complex.I / 2, Complex.I / 2]) := by
    rw [Jz2_eq_diagonal, Matrix.diagonal_smul]
  rw [ZC, hdiag, Matrix.exp_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal, Matrix.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.of_apply, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one]

/-- Diagonal form of `ZC` with scalar exponentials. -/
lemma ZC_eq_diagonal' (w : ℂ) :
    ZC w = Matrix.diagonal ![NormedSpace.exp (w • (-Complex.I / 2)),
      NormedSpace.exp (w • (Complex.I / 2))] := by
  rw [ZC_eq_two_terms]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal, Matrix.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.of_apply, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one]

/-- Single-pulse growth bound `‖ZC w‖ ≤ exp(|Im w|/2)`. -/
lemma norm_ZC_le (w : ℂ) : ‖ZC w‖ ≤ Real.exp (|w.im| / 2) := by
  rw [ZC_eq_diagonal', Matrix.l2_opNorm_diagonal,
    pi_norm_le_iff_of_nonneg (by positivity)]
  refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
  · simp only [Matrix.cons_val_zero, ← Complex.exp_eq_exp_ℂ, Complex.norm_exp]
    have hre : (w • (-Complex.I / 2)).re = w.im / 2 := by
      simp [smul_eq_mul, Complex.mul_re]
      ring
    rw [hre]
    exact Real.exp_le_exp.mpr (by linarith [le_abs_self w.im])
  · simp only [Matrix.cons_val_one, Matrix.cons_val', Matrix.cons_val_fin_one,
      ← Complex.exp_eq_exp_ℂ, Complex.norm_exp]
    have hre : (w • (Complex.I / 2)).re = -(w.im / 2) := by
      simp [smul_eq_mul, Complex.mul_re]
      ring
    rw [hre]
    exact Real.exp_le_exp.mpr (by linarith [neg_le_abs w.im])

/-- `ZC` agrees with `Zrot` on the real axis. -/
lemma ZC_real (t : ℝ) : ZC (t : ℂ) = Zrot t := by
  rw [ZC, Zrot]
  congr 1

/-- `X` rotations are unitary, hence norm one (C⋆-identity). -/
lemma norm_Xrot (t : ℝ) : ‖Xrot t‖ = 1 := by
  have hU : Xrot t ∈ unitary M2 := Unitary.mem_iff.mpr
    ⟨by rw [Matrix.star_eq_conjTranspose]; exact Xrot_conjTranspose_mul t,
     by rw [Matrix.star_eq_conjTranspose]; exact Xrot_mul_conjTranspose t⟩
  exact CStarRing.norm_of_mem_unitary hU

/-- Complexified composite evolution `UC L α θ z = ∏ X(αⱼ)·ZC(z·θⱼ)`. -/
def UC : (L : ℕ) → (Fin L → ℝ) → (Fin L → ℝ) → ℂ → M2
  | 0, _, _, _ => 1
  | L + 1, α, θ, z =>
      UC L (fun j => α j.castSucc) (fun j => θ j.castSucc) z *
        (Xrot (α (Fin.last L)) * ZC (z * ((θ (Fin.last L) : ℝ) : ℂ)))

lemma UC_succ (L : ℕ) (α θ : Fin (L + 1) → ℝ) (z : ℂ) :
    UC (L + 1) α θ z = UC L (fun j => α j.castSucc) (fun j => θ j.castSucc) z *
      (Xrot (α (Fin.last L)) * ZC (z * ((θ (Fin.last L) : ℝ) : ℂ))) := rfl

/-- `UC` agrees with `U` on the real axis. -/
lemma UC_real : ∀ (L : ℕ) (α θ : Fin L → ℝ) (lam : ℝ),
    UC L α θ (lam : ℂ) = U L α θ lam
  | 0, _, _, _ => rfl
  | L + 1, α, θ, lam => by
      have h1 : UC L (fun j => α j.castSucc) (fun j => θ j.castSucc) (lam : ℂ)
          = U L (fun j => α j.castSucc) (fun j => θ j.castSucc) lam :=
        UC_real L _ _ lam
      have h2 : ZC ((lam : ℂ) * ((θ (Fin.last L) : ℝ) : ℂ))
          = Zrot (lam * θ (Fin.last L)) := by
        rw [← Complex.ofReal_mul]
        exact ZC_real _
      rw [UC_succ, U_succ, h1, h2]

/-- Multi-pulse growth bound with `Σ|θⱼ|`. -/
lemma UC_norm_le : ∀ (L : ℕ) (α θ : Fin L → ℝ) (z : ℂ),
    ‖UC L α θ z‖ ≤ Real.exp ((∑ j, |θ j| / 2) * |z.im|)
  | 0, α, θ, z => by
      show ‖(1 : M2)‖ ≤ Real.exp ((∑ j : Fin 0, |θ j| / 2) * |z.im|)
      rw [norm_one]
      have h0 : (∑ j : Fin 0, |θ j| / 2) * |z.im| = 0 := by simp
      rw [h0, Real.exp_zero]
  | L + 1, α, θ, z => by
      have hX : ‖Xrot (α (Fin.last L))‖ = 1 := norm_Xrot _
      have hZ : ‖ZC (z * ((θ (Fin.last L) : ℝ) : ℂ))‖
          ≤ Real.exp (|θ (Fin.last L)| / 2 * |z.im|) := by
        have h := norm_ZC_le (z * ((θ (Fin.last L) : ℝ) : ℂ))
        have him : (z * ((θ (Fin.last L) : ℝ) : ℂ)).im
            = z.im * θ (Fin.last L) := by
          simp [Complex.mul_im]
        have habs : |z.im * θ (Fin.last L)| = |θ (Fin.last L)| * |z.im| := by
          rw [abs_mul, mul_comm]
        have h2 : |(z * ((θ (Fin.last L) : ℝ) : ℂ)).im| / 2
            = |θ (Fin.last L)| / 2 * |z.im| := by
          rw [him, habs]; ring
        rwa [h2] at h
      have h1 := UC_norm_le L (fun j => α j.castSucc) (fun j => θ j.castSucc) z
      have h2' : ‖Xrot (α (Fin.last L))‖ * ‖ZC (z * ((θ (Fin.last L) : ℝ) : ℂ))‖
          ≤ 1 * Real.exp (|θ (Fin.last L)| / 2 * |z.im|) := by
        rw [hX]
        exact mul_le_mul_of_nonneg_left hZ zero_le_one
      calc ‖UC (L + 1) α θ z‖
          ≤ ‖UC L (fun j => α j.castSucc) (fun j => θ j.castSucc) z‖
            * (‖Xrot (α (Fin.last L))‖ * ‖ZC (z * ((θ (Fin.last L) : ℝ) : ℂ))‖) := by
            rw [UC_succ]
            calc ‖_ * _‖ ≤ ‖UC L _ _ _‖ * ‖Xrot _ * ZC _‖ := norm_mul_le _ _
              _ ≤ _ := by
                apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
                exact norm_mul_le _ _
        _ ≤ Real.exp ((∑ j : Fin L, |θ j.castSucc| / 2) * |z.im|)
            * (1 * Real.exp (|θ (Fin.last L)| / 2 * |z.im|)) :=
            mul_le_mul h1 h2'
              (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (Real.exp_pos _).le
        _ = Real.exp ((∑ j, |θ j| / 2) * |z.im|) := by
            have hsum : (∑ j : Fin (L + 1), |θ j| / 2)
                = (∑ j : Fin L, |θ j.castSucc| / 2) + |θ (Fin.last L)| / 2 :=
              Fin.sum_univ_castSucc _
            rw [one_mul, ← Real.exp_add, hsum]
            congr 1
            ring

/-- The canonical complexification `Hcanon = 1 - ½·Tr[U₁ᴴ·UC]`. -/
def Hcanon (L : ℕ) (α θ : Fin L → ℝ) (z : ℂ) : ℂ :=
  1 - ((((U L α θ 1)ᴴ * UC L α θ z).trace) / 2)

/-! ## 2. Analyticity of the complexification -/

/-- Continuous linear maps preserve analyticity (complex base field). -/
lemma AnalyticAt.comp_clmC {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G] {f : ℂ → F} {x : ℂ} (g : F →L[ℂ] G)
    (hf : AnalyticAt ℂ f x) : AnalyticAt ℂ (fun y => g (f y)) x :=
  (g.comp_analyticOnNhd (s := {x}) (fun y hy => by
    rw [Set.mem_singleton_iff] at hy; rwa [hy])) x (Set.mem_singleton x)

/-- Scalar-matrix exponentials are analytic. -/
lemma analyticAt_exp_smulC (A : M2) (x : ℂ) :
    AnalyticAt ℂ (fun w : ℂ => NormedSpace.exp (w • A)) x := by
  have h1 : AnalyticAt ℂ (fun w : ℂ => w • A) x :=
    (analyticAt_id (𝕜 := ℂ) (E := ℂ) (z := x)).smul
      (analyticAt_const (𝕜 := ℂ) (F := M2) (v := A) (x := x))
  refine AnalyticAt.comp (f := fun w : ℂ => w • A) (x := x) ?_ h1
  exact NormedSpace.analyticAt_exp_of_mem_ball (𝕂 := ℂ) (𝔸 := M2) (x • A)
    (by simp [NormedSpace.expSeries_radius_eq_top, Metric.eball_top])

lemma analyticAt_ZC (w : ℂ) : AnalyticAt ℂ ZC w :=
  analyticAt_exp_smulC Jz2 w

/-- The complexified propagator is analytic in `z`. -/
lemma analyticAt_UC : ∀ (L : ℕ) (α θ : Fin L → ℝ) (w : ℂ),
    AnalyticAt ℂ (UC L α θ) w
  | 0, _, _, w => by
      simpa [UC] using (analyticAt_const (𝕜 := ℂ) (F := M2) (v := (1 : M2)) (x := w))
  | L + 1, α, θ, w => by
      have hZ : AnalyticAt ℂ
          (fun z : ℂ => ZC (z * ((θ (Fin.last L) : ℝ) : ℂ))) w :=
        (analyticAt_ZC _).comp
          ((analyticAt_id (𝕜 := ℂ) (E := ℂ) (z := w)).mul analyticAt_const)
      have h : (UC (L + 1) α θ)
          = fun z : ℂ => UC L (fun j => α j.castSucc) (fun j => θ j.castSucc) z
              * (Xrot (α (Fin.last L)) * ZC (z * ((θ (Fin.last L) : ℝ) : ℂ))) :=
        funext (fun z => UC_succ L α θ z)
      rw [h]
      exact (analyticAt_UC L _ _ w).mul
        (analyticAt_const.mul hZ)

/-- Matrix entries of `U₁ᴴ·UC` are analytic. -/
lemma analyticAt_entry_UC (L : ℕ) (α θ : Fin L → ℝ) (i j : Fin 2) (w : ℂ) :
    AnalyticAt ℂ (fun z : ℂ => ((U L α θ 1)ᴴ * UC L α θ z) i j) w :=
  AnalyticAt.comp_clmC (ContinuousLinearMap.proj (R := ℂ) j)
    (AnalyticAt.comp_clmC (ContinuousLinearMap.proj (R := ℂ) i)
      ((analyticAt_const (𝕜 := ℂ) (F := M2) (v := (U L α θ 1)ᴴ) (x := w)).mul
        (analyticAt_UC L α θ w)))

lemma analyticAt_trace_UC (L : ℕ) (α θ : Fin L → ℝ) (w : ℂ) :
    AnalyticAt ℂ (fun z : ℂ => ((U L α θ 1)ᴴ * UC L α θ z).trace) w := by
  have hfun : (fun z : ℂ => ((U L α θ 1)ᴴ * UC L α θ z).trace)
      = fun z : ℂ => ((U L α θ 1)ᴴ * UC L α θ z) 0 0
        + ((U L α θ 1)ᴴ * UC L α θ z) 1 1 := by
    funext z
    rw [Matrix.trace_fin_two]
  rw [hfun]
  exact (analyticAt_entry_UC L α θ 0 0 w).add (analyticAt_entry_UC L α θ 1 1 w)

lemma analyticAt_Hcanon (L : ℕ) (α θ : Fin L → ℝ) (w : ℂ) :
    AnalyticAt ℂ (Hcanon L α θ) w := by
  have hT := analyticAt_trace_UC L α θ w
  have hT2 : AnalyticAt ℂ
      (fun z : ℂ => (((U L α θ 1)ᴴ * UC L α θ z).trace) / 2) w := by
    have hfun : (fun z : ℂ => (((U L α θ 1)ᴴ * UC L α θ z).trace) / 2)
        = (fun z : ℂ => (((U L α θ 1)ᴴ * UC L α θ z).trace) * (2 : ℂ)⁻¹) := by
      funext z
      rw [div_eq_mul_inv]
    rw [hfun]
    exact hT.mul analyticAt_const
  have hfun : Hcanon L α θ
      = fun z : ℂ => 1 - ((((U L α θ 1)ᴴ * UC L α θ z).trace) / 2) := rfl
  rw [hfun]
  exact analyticAt_const.sub hT2

lemma Hcanon_analyticOn (L : ℕ) (α θ : Fin L → ℝ) :
    AnalyticOnNhd ℂ (Hcanon L α θ) Set.univ :=
  fun z _ => analyticAt_Hcanon L α θ z

lemma Hcanon_diff (L : ℕ) (α θ : Fin L → ℝ) :
    Differentiable ℂ (Hcanon L α θ) :=
  differentiableOn_univ.mp (Hcanon_analyticOn L α θ).differentiableOn

/-! ## 3. Quaternionic form: the trace is real on `ℝ` -/

/-- Unit-quaternion form `!![a,b;-conj b,conj a]` of `2 × 2` matrices. -/
def IsQuat (M : M2) : Prop :=
  ∃ a b : ℂ, M = !![a, b; -(star b), star a]

lemma isQuat_one : IsQuat 1 := by
  refine ⟨1, 0, ?_⟩
  rw [Matrix.one_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [star_zero, star_one]

/-- Conjugation swaps the two `X`-rotation exponentials. -/
lemma star_exp_neg_half_mul_I (t : ℝ) :
    star (Complex.exp (((-t / 2 : ℝ) : ℂ) * Complex.I))
      = Complex.exp ((((t / 2 : ℝ) : ℂ)) * Complex.I) := by
  rw [← starRingEnd_apply, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

lemma isQuat_Xrot (t : ℝ) : IsQuat (Xrot t) := by
  set e1 : ℂ := Complex.exp (((-t / 2 : ℝ) : ℂ) * Complex.I) with he1
  set e2 : ℂ := Complex.exp ((((t / 2 : ℝ) : ℂ)) * Complex.I) with he2
  have hstar : star e1 = e2 := star_exp_neg_half_mul_I t
  have hstar2 : star e2 = e1 := by rw [← hstar, star_star]
  have hX : Xrot t = e1 • Pplus + e2 • Pminus := by
    rw [Xrot_eq_two_terms]
    simp only [← Complex.exp_eq_exp_ℂ, he1, he2]
  refine ⟨(e1 + e2) / 2, (e1 - e2) / 2, ?_⟩
  rw [hX]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Pplus, Pminus, hstar, hstar2,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.of_apply,
      Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one,
      star_add, star_mul, star_sub, star_star] <;>
    ring

lemma isQuat_Zrot (t : ℝ) : IsQuat (Zrot t) := by
  set e1 : ℂ := Complex.exp (((-t / 2 : ℝ) : ℂ) * Complex.I) with he1
  set e2 : ℂ := Complex.exp ((((t / 2 : ℝ) : ℂ)) * Complex.I) with he2
  have hstar : star e1 = e2 := star_exp_neg_half_mul_I t
  have hZ : Zrot t = e1 • (!![1, 0; 0, 0] : M2) + e2 • (!![0, 0; 0, 1] : M2) := by
    rw [Zrot_eq_two_terms]
    simp only [← Complex.exp_eq_exp_ℂ, he1, he2]
  refine ⟨e1, 0, ?_⟩
  rw [hZ]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hstar,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.of_apply,
      Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one, star_zero] <;>
    ring

lemma isQuat_mul {M1 M2 : M2} (h1 : IsQuat M1) (h2 : IsQuat M2) :
    IsQuat (M1 * M2) := by
  obtain ⟨a1, b1, rfl⟩ := h1
  obtain ⟨a2, b2, rfl⟩ := h2
  refine ⟨a1 * a2 + b1 * (-(star b2)), a1 * b2 + b1 * star a2, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.of_apply,
      Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one,
      star_add, star_mul, star_neg, star_sub, star_star] <;>
    ring

lemma isQuat_conjTranspose {M : M2} (h : IsQuat M) : IsQuat Mᴴ := by
  obtain ⟨a, b, rfl⟩ := h
  refine ⟨star a, -b, ?_⟩
  rw [← Matrix.star_eq_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.star_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.of_apply,
      Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one,
      star_add, star_mul, star_neg, star_sub, star_star] <;>
    ring

/-- Every propagator value is a unit quaternion. -/
lemma isQuat_U : ∀ (L : ℕ) (α θ : Fin L → ℝ) (lam : ℝ), IsQuat (U L α θ lam)
  | 0, _, _, _ => by
      rw [U_zero]
      exact isQuat_one
  | L + 1, α, θ, lam => by
      rw [U_succ]
      exact isQuat_mul (isQuat_U L _ _ lam)
        (isQuat_mul (isQuat_Xrot _) (isQuat_Zrot _))

/-- Quaternionic matrices have real trace. -/
lemma trace_im_eq_zero_of_isQuat {M : M2} (h : IsQuat M) : M.trace.im = 0 := by
  obtain ⟨a, b, rfl⟩ := h
  rw [Matrix.trace_fin_two_of]
  have hstar : (star a).im = -(a.im) := by
    rw [← starRingEnd_apply]
    exact RCLike.conj_im a
  rw [Complex.add_im, hstar, add_neg_cancel]

/-- `Hcanon` extends `h`: on the real axis the trace is real, so
`1 - ½Tr` agrees with `1 - ½Re Tr`. -/
lemma Hcanon_real (L : ℕ) (α θ : Fin L → ℝ) (lam : ℝ) :
    Hcanon L α θ (lam : ℂ) = (((h L α θ lam : ℝ)) : ℂ) := by
  have hV : IsQuat ((U L α θ 1)ᴴ * U L α θ lam) :=
    isQuat_mul (isQuat_conjTranspose (isQuat_U L α θ 1)) (isQuat_U L α θ lam)
  obtain ⟨a, b, hab⟩ := hV
  have him : (((U L α θ 1)ᴴ * U L α θ lam).trace).im = 0 :=
    trace_im_eq_zero_of_isQuat ⟨a, b, hab⟩
  have hre : (((((U L α θ 1)ᴴ * U L α θ lam).trace.re : ℝ)) : ℂ)
      = ((U L α θ 1)ᴴ * U L α θ lam).trace := by
    have hri := Complex.re_add_im (((U L α θ 1)ᴴ * U L α θ lam).trace)
    rw [him] at hri
    simpa using hri
  show (1 : ℂ) - ((((U L α θ 1)ᴴ * UC L α θ (lam : ℂ)).trace) / 2)
      = ((((h L α θ lam : ℝ))) : ℂ)
  rw [UC_real]
  have hco : ((((h L α θ lam : ℝ))) : ℂ)
      = 1 - ((((((U L α θ 1)ᴴ * U L α θ lam).trace.re : ℝ)) : ℂ) / 2) := by
    have hh : h L α θ lam
        = 1 - (1 / 2) * ((((U L α θ 1)ᴴ * U L α θ lam).trace).re) := rfl
    rw [hh]
    push_cast
    ring
  rw [hco, hre]

/-! ## 4. Growth bound (`jgrow`) -/

/-- Matrix entries are bounded by the L2 operator norm. -/
lemma norm_entry_le_l2Op (A : M2) (i j : Fin 2) : ‖A i j‖ ≤ ‖A‖ := by
  classical
  have hmul := A.l2_opNorm_mulVec (EuclideanSpace.single j (1 : ℂ))
  have hnorm1 : ‖EuclideanSpace.single j (1 : ℂ)‖ = 1 := by
    rw [EuclideanSpace.norm_single, norm_one]
  rw [hnorm1, mul_one] at hmul
  have hentry : ((EuclideanSpace.equiv (Fin 2) ℂ).symm
      (A *ᵥ (EuclideanSpace.single j (1 : ℂ)))) i = A i j := by
    simp [EuclideanSpace.single, Matrix.mulVec_single_one]
  calc ‖A i j‖
      = ‖((EuclideanSpace.equiv (Fin 2) ℂ).symm
          (A *ᵥ (EuclideanSpace.single j (1 : ℂ)))) i‖ := by rw [hentry]
    _ ≤ ‖(EuclideanSpace.equiv (Fin 2) ℂ).symm
          (A *ᵥ (EuclideanSpace.single j (1 : ℂ)))‖ := PiLp.norm_apply_le _ _
    _ ≤ ‖A‖ := hmul

/-- `‖trace A‖ ≤ 2‖A‖` for `2 × 2` matrices. -/
lemma norm_trace_le_two (A : M2) : ‖A.trace‖ ≤ 2 * ‖A‖ := by
  rw [Matrix.trace_fin_two]
  calc ‖A 0 0 + A 1 1‖ ≤ ‖A 0 0‖ + ‖A 1 1‖ := norm_add_le _ _
    _ ≤ ‖A‖ + ‖A‖ := add_le_add (norm_entry_le_l2Op A 0 0) (norm_entry_le_l2Op A 1 1)
    _ = 2 * ‖A‖ := by ring

/-- The reference unitary `U₁ᴴ` has norm one. -/
lemma norm_conjTranspose_U (L : ℕ) (α θ : Fin L → ℝ) (lam : ℝ) :
    ‖(U L α θ lam)ᴴ‖ = 1 := by
  have hU : U L α θ lam ∈ unitary M2 := Unitary.mem_iff.mpr
    ⟨by rw [Matrix.star_eq_conjTranspose]; exact U_conjTranspose_mul L α θ lam,
     by rw [Matrix.star_eq_conjTranspose]; exact U_mul_conjTranspose L α θ lam⟩
  calc ‖(U L α θ lam)ᴴ‖ = ‖U L α θ lam‖ := by
        rw [← Matrix.star_eq_conjTranspose, norm_star]
    _ = 1 := CStarRing.norm_of_mem_unitary hU

/-- Pointwise complex growth bound for `Hcanon`. -/
lemma Hcanon_norm_le {L : ℕ} {α θ : Fin L → ℝ}
    (hθ : ∀ j, 0 ≤ θ j) (z : ℂ) :
    ‖Hcanon L α θ z‖ ≤ 2 * Real.exp ((cost θ / 2) * |z.im|) := by
  have hsum : (∑ j, |θ j| / 2) = cost θ / 2 := by
    show (∑ j, |θ j| / 2) = (∑ j, θ j) / 2
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl (fun j _ => by rw [abs_of_nonneg (hθ j)])
  have hUC : ‖UC L α θ z‖ ≤ Real.exp ((cost θ / 2) * |z.im|) := by
    have h := UC_norm_le L α θ z
    rwa [hsum] at h
  have hU1 : ‖(U L α θ 1)ᴴ‖ = 1 := norm_conjTranspose_U L α θ 1
  have hT : ‖(((U L α θ 1)ᴴ * UC L α θ z).trace)‖
      ≤ 2 * Real.exp ((cost θ / 2) * |z.im|) := by
    calc ‖(((U L α θ 1)ᴴ * UC L α θ z).trace)‖
        ≤ 2 * ‖(U L α θ 1)ᴴ * UC L α θ z‖ := norm_trace_le_two _
      _ ≤ 2 * (‖(U L α θ 1)ᴴ‖ * ‖UC L α θ z‖) :=
          mul_le_mul_of_nonneg_left (norm_mul_le _ _) (by norm_num)
      _ ≤ 2 * (1 * Real.exp ((cost θ / 2) * |z.im|)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          calc ‖(U L α θ 1)ᴴ‖ * ‖UC L α θ z‖
              = 1 * ‖UC L α θ z‖ := by rw [hU1]
            _ ≤ 1 * Real.exp ((cost θ / 2) * |z.im|) :=
                mul_le_mul_of_nonneg_left hUC (by norm_num)
      _ = 2 * Real.exp ((cost θ / 2) * |z.im|) := by ring
  have hexp_nonneg : (0 : ℝ) ≤ (cost θ / 2) * |z.im| := by
    apply mul_nonneg _ (abs_nonneg _)
    apply div_nonneg _ zero_le_two
    exact Finset.sum_nonneg (fun j _ => hθ j)
  have h1exp : (1 : ℝ) ≤ Real.exp ((cost θ / 2) * |z.im|) :=
    Real.one_le_exp hexp_nonneg
  have e1 : ‖Hcanon L α θ z‖
      ≤ 1 + ‖(((U L α θ 1)ᴴ * UC L α θ z).trace)‖ / 2 := by
    have hH : Hcanon L α θ z
        = 1 - ((((U L α θ 1)ᴴ * UC L α θ z).trace) / 2) := rfl
    rw [hH]
    calc ‖(1 : ℂ) - ((((U L α θ 1)ᴴ * UC L α θ z).trace) / 2)‖
        ≤ ‖(1 : ℂ)‖ + ‖((((U L α θ 1)ᴴ * UC L α θ z).trace) / 2)‖ :=
          norm_sub_le _ _
      _ = 1 + ‖(((U L α θ 1)ᴴ * UC L α θ z).trace)‖ / 2 := by
          rw [norm_one, norm_div]
          norm_num
  linarith [e1, hT, h1exp]

/-- Bridge `jgrow`: the exact growth statement `jensen_rung` assumes,
for `H := Hcanon`. -/
theorem bridge_jgrow {L : ℕ} {α θ : Fin L → ℝ}
    (hθ : ∀ j, 0 ≤ θ j) (z : ℂ) :
    ‖Hcanon L α θ z‖ ≤ 2 * Real.exp ((cost θ / 2) * |z.im|) :=
  Hcanon_norm_le hθ z

/-! ## 5. Order bound (`jord`) -/

/-- Complex iterated derivatives at a real point agree with the real
iterated derivatives of the restriction (via `HasDerivAt.comp_ofReal`). -/
lemma iteratedDeriv_Hcanon_restrict (L : ℕ) (α θ : Fin L → ℝ) (k : ℕ) (y : ℝ) :
    iteratedDeriv k (Hcanon L α θ) (↑y)
      = iteratedDeriv k (fun y : ℝ => Hcanon L α θ ↑y) y := by
  induction k generalizing y with
  | zero => simp only [iteratedDeriv_zero]
  | succ k ih =>
      have hana : AnalyticAt ℂ (iteratedDeriv k (Hcanon L α θ)) (↑y) := by
        rw [iteratedDeriv_eq_iterate]
        exact ((Hcanon_analyticOn L α θ).iterated_deriv k) _ (Set.mem_univ _)
      have hFdiff : DifferentiableAt ℂ (iteratedDeriv k (Hcanon L α θ)) (↑y) :=
        hana.differentiableAt
      have hHas : HasDerivAt (iteratedDeriv k (Hcanon L α θ))
          (deriv (iteratedDeriv k (Hcanon L α θ)) (↑y)) (↑y) :=
        hFdiff.hasDerivAt
      have hReal : HasDerivAt (fun y : ℝ => (iteratedDeriv k (Hcanon L α θ)) ↑y)
          (deriv (iteratedDeriv k (Hcanon L α θ)) (↑y)) y :=
        hHas.comp_ofReal
      have hfun : (fun y : ℝ => (iteratedDeriv k (Hcanon L α θ)) ↑y)
          = iteratedDeriv k (fun y : ℝ => Hcanon L α θ ↑y) :=
        funext (fun y => ih y)
      rw [hfun] at hReal
      have hderiv : deriv (iteratedDeriv k (fun y : ℝ => Hcanon L α θ ↑y)) y
          = deriv (iteratedDeriv k (Hcanon L α θ)) (↑y) :=
        hReal.deriv
      simp only [iteratedDeriv_succ]
      exact hderiv.symm

/-- Real flatness transfers to complex vanishing at `1`. -/
lemma complex_vanishing (N : ℕ) {L : ℕ} {α θ : Fin L → ℝ} {φ : ℝ}
    (hAdm : Admissible N φ L α θ) (k : ℕ) (hk : k < 2 * N + 2) :
    iteratedDeriv k (Hcanon L α θ) 1 = 0 := by
  have h1 : (1 : ℂ) = (((1 : ℝ)) : ℂ) := Complex.ofReal_one.symm
  rw [h1, iteratedDeriv_Hcanon_restrict L α θ k 1]
  have hfun : (fun y : ℝ => Hcanon L α θ (↑y))
      = (fun y : ℝ => (((h L α θ y : ℝ)) : ℂ)) :=
    funext (fun y => Hcanon_real L α θ y)
  rw [hfun, iteratedDeriv_ofReal, h_flat N φ L α θ hAdm k hk, Complex.ofReal_zero]

/-- Bridge `jord`: the exact divisor statement `jensen_rung` assumes,
for `H := Hcanon`. -/
theorem bridge_jord (N : ℕ) {L : ℕ} {α θ : Fin L → ℝ} {φ : ℝ}
    (hφ0 : 0 < φ) (hφπ : φ ≤ Real.pi)
    (hAdm : Admissible N φ L α θ) (R : ℝ) (hR : 1 < R) :
    ((2 * N + 2 : ℕ) : ℤ) ≤ divisor (Hcanon L α θ) (closedBall (0 : ℂ) R) 1 := by
  have h1mem : (1 : ℂ) ∈ closedBall (0 : ℂ) R := by
    rw [Metric.mem_closedBall, dist_zero_right, norm_one]
    exact hR.le
  have hHana : AnalyticOnNhd ℂ (Hcanon L α θ) (closedBall (0 : ℂ) R) :=
    (Hcanon_analyticOn L α θ).mono (Set.subset_univ _)
  have hdiv : divisor (Hcanon L α θ) (closedBall (0 : ℂ) R) 1
      = (ENat.map Nat.cast (analyticOrderAt (Hcanon L α θ) 1)).untop₀ :=
    hHana.divisor_apply h1mem
  have horder : ((2 * N + 2 : ℕ) : ℕ∞)
      ≤ analyticOrderAt (Hcanon L α θ) 1 := by
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
      (analyticAt_Hcanon L α θ 1)]
    intro i hi
    exact complex_vanishing N hAdm i hi
  have hfin : analyticOrderAt (Hcanon L α θ) 1 ≠ ⊤ := by
    intro htop
    have hev : Hcanon L α θ =ᶠ[𝓝 (1 : ℂ)] 0 := analyticOrderAt_eq_top.mp htop
    have hglob : Hcanon L α θ = 0 :=
      AnalyticOnNhd.eq_of_eventuallyEq (Hcanon_analyticOn L α θ)
        (fun _ _ => analyticAt_const) hev
    have h0 : Hcanon L α θ 0 = 0 := by rw [hglob]; rfl
    have hH0 : Hcanon L α θ (((0 : ℝ)) : ℂ) = ((((h L α θ 0 : ℝ))) : ℂ) :=
      Hcanon_real L α θ 0
    rw [Complex.ofReal_zero] at hH0
    rw [hH0] at h0
    have h00 : h L α θ 0 = 0 := by exact_mod_cast h0
    have hspos : (0 : ℝ) < 2 * Real.sin (φ / 4) ^ 2 := by
      have hsinpos : (0 : ℝ) < Real.sin (φ / 4) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith [hφ0]) (by linarith [hφπ, Real.pi_pos])
      exact mul_pos (by norm_num) (sq_pos_of_ne_zero (ne_of_gt hsinpos))
    have hge : 1 - Real.cos (φ / 2) ≤ h L α θ 0 :=
      h_zero_ge φ hφ0.le hφπ L α θ hAdm.2.1
    have hs_eq : 1 - Real.cos (φ / 2) = 2 * Real.sin (φ / 4) ^ 2 := by
      rw [Real.sin_sq_eq_half_sub]
      have h2 : 2 * (φ / 4) = φ / 2 := by ring
      rw [h2]
      ring
    linarith [h00, hge, hspos, hs_eq]
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfin
  have hqn : 2 * N + 2 ≤ n := by
    have h' : ((2 * N + 2 : ℕ) : ℕ∞) ≤ ((n : ℕ) : ℕ∞) := by
      rw [hn]
      exact horder
    exact_mod_cast h'
  have hval : divisor (Hcanon L α θ) (closedBall (0 : ℂ) R) 1 = ((n : ℕ) : ℤ) := by
    rw [hdiv, ← hn]
    simp
  rw [hval]
  exact_mod_cast hqn

/-! ## 6. Unconditional Jensen rung -/

/-- **Theorem J (route-K K2), general-φ form, unconditional.** For
`0 < φ ≤ π`, every order-`N` admissible sequence with `q = 2N+2`,
`s = 2 sin²(φ/4)` satisfies `π * q / (e * (2/s)^((1:ℝ)/q)) ≤ T`.
The analytic inputs `jord`/`jgrow` are discharged by `bridge_jord`/
`bridge_jgrow` for the canonical complexification `Hcanon`. -/
theorem jensen_rung_final (N : ℕ) {L : ℕ} {α θ : Fin L → ℝ} {φ : ℝ}
    (hφ0 : 0 < φ) (hφπ : φ ≤ Real.pi)
    (hAdm : Admissible N φ L α θ) :
    Real.pi * ((2 * N + 2 : ℕ):ℝ)
      / (Real.exp 1 * (2 / (2 * Real.sin (φ / 4) ^ 2)) ^ ((1:ℝ) / ((2 * N + 2 : ℕ):ℝ)))
      ≤ cost θ := by
  have hθ : ∀ j, 0 ≤ θ j := hAdm.1
  exact jensen_rung N hφ0 hφπ hAdm (Hcanon L α θ) (Hcanon_diff L α θ)
    (fun lam => Hcanon_real L α θ lam)
    (bridge_jord N hφ0 hφπ hAdm)
    (fun z => bridge_jgrow hθ z)

/-- **Theorem J at `φ = π`, unconditional.** -/
theorem jensen_rung_pi_final (N : ℕ) {L : ℕ} {α θ : Fin L → ℝ}
    (hAdm : Admissible N Real.pi L α θ) :
    Real.pi * ((2 * N + 2 : ℕ):ℝ)
      / (Real.exp 1 * (2:ℝ) ^ ((1:ℝ) / ((2 * N + 2 : ℕ):ℝ))) ≤ cost θ := by
  have hθ : ∀ j, 0 ≤ θ j := hAdm.1
  exact jensen_rung_pi N hAdm (Hcanon L α θ) (Hcanon_diff L α θ)
    (fun lam => Hcanon_real L α θ lam)
    (bridge_jord N Real.pi_pos le_rfl hAdm)
    (fun z => bridge_jgrow hθ z)

end RobustZ
