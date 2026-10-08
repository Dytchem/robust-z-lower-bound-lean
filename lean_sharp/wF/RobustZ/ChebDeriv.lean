/-
Copyright (c) 2025 RobustZ project. All rights reserved.

Chebyshev derivative bounds and derivative bounds for `approxPoly`.

Main results:
* `RobustZ.norm_deriv_chebyshevT_le` : the derivative of `T_n` is bounded by `n ^ 2` on `[-1, 1]`.
* `RobustZ.norm_deriv2_chebyshevT_le` : the second derivative of `T_n` is bounded by `16 n ^ 4`.
* `RobustZ.norm_deriv_approxPoly_le`, `RobustZ.norm_deriv2_approxPoly_le` : explicit bounds.
-/
import RobustZ.Approx
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Real.Pi.Bounds

open Complex
namespace RobustZ
open scoped Real

/-! ## Elementary sine estimates -/

/-- `|sin (k * θ)| ≤ k * |sin θ|` for natural `k`. -/
private lemma abs_sin_nat_mul_le (k : ℕ) (θ : ℝ) :
    |Real.sin ((k : ℝ) * θ)| ≤ (k : ℝ) * |Real.sin θ| := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h : ((k + 1 : ℕ) : ℝ) * θ = (k : ℝ) * θ + θ := by push_cast; ring
    rw [h, Real.sin_add]
    calc |Real.sin ((k : ℝ) * θ) * Real.cos θ + Real.cos ((k : ℝ) * θ) * Real.sin θ|
        ≤ |Real.sin ((k : ℝ) * θ) * Real.cos θ|
          + |Real.cos ((k : ℝ) * θ) * Real.sin θ| := abs_add_le _ _
      _ = |Real.sin ((k : ℝ) * θ)| * |Real.cos θ|
          + |Real.cos ((k : ℝ) * θ)| * |Real.sin θ| := by rw [abs_mul, abs_mul]
      _ ≤ |Real.sin ((k : ℝ) * θ)| * 1 + 1 * |Real.sin θ| := by
            have h1 := Real.abs_cos_le_one θ
            have h2 := Real.abs_cos_le_one ((k : ℝ) * θ)
            have h3 : (0 : ℝ) ≤ |Real.sin ((k : ℝ) * θ)| := abs_nonneg _
            have h4 : (0 : ℝ) ≤ |Real.sin θ| := abs_nonneg _
            nlinarith [h1, h2, h3, h4]
      _ ≤ (k : ℝ) * |Real.sin θ| + |Real.sin θ| := by
            have h1 := ih
            have h2 : (0 : ℝ) ≤ |Real.sin θ| := abs_nonneg _
            nlinarith [h1, h2]
      _ = ((k + 1 : ℕ) : ℝ) * |Real.sin θ| := by push_cast; ring

/-- `|n| = (n.natAbs : ℝ)` for integers. -/
private lemma abs_int_cast_eq (n : ℤ) : |((n : ℤ) : ℝ)| = (n.natAbs : ℝ) := by
  obtain ⟨k, hk | hk⟩ := Int.eq_nat_or_neg n
  · rw [hk]; simp
  · rw [hk]; simp

/-- `|sin (n * θ)| ≤ |n| * |sin θ|`. -/
private lemma abs_sin_int_mul_le (n : ℤ) (θ : ℝ) :
    |Real.sin ((n : ℝ) * θ)| ≤ |((n : ℤ) : ℝ)| * |Real.sin θ| := by
  obtain ⟨k, hk | hk⟩ := Int.eq_nat_or_neg n
  · rw [hk]; simpa using abs_sin_nat_mul_le k θ
  · rw [hk]
    have h : (((-(k : ℤ)) : ℤ) : ℝ) * θ = -((k : ℝ) * θ) := by push_cast; ring
    rw [h, Real.sin_neg, abs_neg]
    simpa using abs_sin_nat_mul_le k θ

/-! ## First derivative of Chebyshev polynomials -/

/-- Chain rule computation: `θ ↦ T_n (cos θ)` has derivative `-n sin (n θ)`. -/
private lemma hasDerivAt_chebT_cos (n : ℤ) (θ : ℝ) :
    HasDerivAt (fun x : ℝ => (Polynomial.Chebyshev.T ℝ n).eval (Real.cos x))
      (-((n : ℝ) * Real.sin ((n : ℝ) * θ))) θ := by
  have hfun : (fun x : ℝ => (Polynomial.Chebyshev.T ℝ n).eval (Real.cos x))
      = fun x : ℝ => Real.cos ((n : ℝ) * x) :=
    funext fun x => Polynomial.Chebyshev.T_real_cos x n
  rw [hfun]
  have h := (Real.hasDerivAt_cos ((n : ℝ) * θ)).comp θ
    ((hasDerivAt_id θ).const_mul (n : ℝ))
  convert h using 1
  · ext x; simp [Function.comp]
  · ring

/-- The key identity `T_n' (cos θ) * sin θ = n * sin (n θ)`. -/
private lemma chebyshevT_deriv_cos_mul_sin (n : ℤ) (θ : ℝ) :
    (Polynomial.Chebyshev.T ℝ n).derivative.eval (Real.cos θ) * Real.sin θ
      = (n : ℝ) * Real.sin ((n : ℝ) * θ) := by
  have hchain : HasDerivAt (fun x : ℝ => (Polynomial.Chebyshev.T ℝ n).eval (Real.cos x))
      ((Polynomial.Chebyshev.T ℝ n).derivative.eval (Real.cos θ) * (-Real.sin θ)) θ :=
    (Polynomial.hasDerivAt (Polynomial.Chebyshev.T ℝ n) (Real.cos θ)).comp θ
      (Real.hasDerivAt_cos θ)
  have h := hchain.unique (hasDerivAt_chebT_cos n θ)
  have key : (Polynomial.Chebyshev.T ℝ n).derivative.eval (Real.cos θ) * Real.sin θ
      = -((Polynomial.Chebyshev.T ℝ n).derivative.eval (Real.cos θ) * (-Real.sin θ)) := by
    ring
  rw [key, h]; ring

/-- On `(-1, 1)` the derivative of `T_n` is bounded by `(natAbs n) ^ 2`. -/
private lemma abs_deriv_chebyshevT_le_aux (n : ℤ) {u : ℝ} (hu : u ∈ Set.Ioo (-1 : ℝ) 1) :
    |(Polynomial.Chebyshev.T ℝ n).derivative.eval u| ≤ ((n.natAbs : ℝ)) ^ 2 := by
  have hcos : Real.cos (Real.arccos u) = u := Real.cos_arccos hu.1.le hu.2.le
  have hsinpos : 0 < Real.sin (Real.arccos u) := by
    rw [Real.sin_arccos]
    exact Real.sqrt_pos.mpr (by nlinarith [hu.1, hu.2])
  have hid : (Polynomial.Chebyshev.T ℝ n).derivative.eval (Real.cos (Real.arccos u))
        * Real.sin (Real.arccos u)
      = (n : ℝ) * Real.sin ((n : ℝ) * Real.arccos u) :=
    chebyshevT_deriv_cos_mul_sin n (Real.arccos u)
  rw [hcos] at hid
  have hN : (0 : ℝ) ≤ (n.natAbs : ℝ) := by positivity
  have hsin : |Real.sin ((n : ℝ) * Real.arccos u)|
      ≤ (n.natAbs : ℝ) * Real.sin (Real.arccos u) := by
    have h := abs_sin_int_mul_le n (Real.arccos u)
    rw [abs_int_cast_eq, abs_of_pos hsinpos] at h
    exact h
  have h1 : |(Polynomial.Chebyshev.T ℝ n).derivative.eval u| * Real.sin (Real.arccos u)
      = |(Polynomial.Chebyshev.T ℝ n).derivative.eval u * Real.sin (Real.arccos u)| := by
    rw [abs_mul, abs_of_pos hsinpos]
  have h2 : |(Polynomial.Chebyshev.T ℝ n).derivative.eval u| * Real.sin (Real.arccos u)
      = (n.natAbs : ℝ) * |Real.sin ((n : ℝ) * Real.arccos u)| := by
    rw [h1, hid, abs_mul, abs_int_cast_eq]
  have h3 : (n.natAbs : ℝ) * |Real.sin ((n : ℝ) * Real.arccos u)|
      ≤ ((n.natAbs : ℝ)) ^ 2 * Real.sin (Real.arccos u) := by
    nlinarith [hsin, hsinpos, hN]
  exact le_of_mul_le_mul_right (h2.trans_le h3) hsinpos

/-- **Item 1.** The derivative of `T_n` is bounded by `n ^ 2` on `[-1, 1]`. -/
lemma abs_deriv_chebyshevT_le (n : ℤ) {u : ℝ} (hu : u ∈ Set.Icc (-1 : ℝ) 1) :
    |(Polynomial.Chebyshev.T ℝ n).derivative.eval u| ≤ ((n.natAbs : ℝ)) ^ 2 := by
  have hclosed : IsClosed {u : ℝ |
      |(Polynomial.Chebyshev.T ℝ n).derivative.eval u| ≤ ((n.natAbs : ℝ)) ^ 2} :=
    isClosed_le (Polynomial.continuous _).abs continuous_const
  have hsub : Set.Ioo (-1 : ℝ) 1 ⊆ {u : ℝ |
      |(Polynomial.Chebyshev.T ℝ n).derivative.eval u| ≤ ((n.natAbs : ℝ)) ^ 2} :=
    fun u hu => abs_deriv_chebyshevT_le_aux n hu
  have hIcc : Set.Icc (-1 : ℝ) 1 ⊆ {u : ℝ |
      |(Polynomial.Chebyshev.T ℝ n).derivative.eval u| ≤ ((n.natAbs : ℝ)) ^ 2} := by
    rw [← closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)]
    exact hclosed.closure_subset_iff.mpr hsub
  exact hIcc hu

/-- **Item 1 (complex form).** -/
lemma norm_deriv_chebyshevT_le (n : ℤ) {u : ℝ} (hu : u ∈ Set.Icc (-1 : ℝ) 1) :
    ‖deriv (fun x : ℝ => (((Polynomial.Chebyshev.T ℝ n).eval x : ℝ) : ℂ)) u‖
      ≤ ((n.natAbs : ℝ)) ^ 2 := by
  have hderiv : deriv (fun x : ℝ => (((Polynomial.Chebyshev.T ℝ n).eval x : ℝ) : ℂ)) u
      = (((Polynomial.Chebyshev.T ℝ n).derivative.eval u : ℝ) : ℂ) :=
    ((Polynomial.hasDerivAt (Polynomial.Chebyshev.T ℝ n) u).ofReal_comp).deriv
  rw [hderiv, Complex.norm_real]
  exact abs_deriv_chebyshevT_le n hu

/-! ## Second derivative of Chebyshev polynomials -/

/-- `θ ↦ T_n' (cos θ)` has derivative `T_n'' (cos θ) * (-sin θ)`. -/
private lemma hasDerivAt_chebT_deriv_cos (n : ℤ) (θ : ℝ) :
    HasDerivAt (fun x : ℝ => (Polynomial.Chebyshev.T ℝ n).derivative.eval (Real.cos x))
      ((Polynomial.Chebyshev.T ℝ n).derivative.derivative.eval (Real.cos θ) * (-Real.sin θ))
      θ :=
  (Polynomial.hasDerivAt (Polynomial.Chebyshev.T ℝ n).derivative (Real.cos θ)).comp θ
    (Real.hasDerivAt_cos θ)

/-- The key identity `T_n'' (cos θ) * sin θ ^ 3 = ψ_n θ`. -/
private lemma chebyshevT_deriv2_cos_mul_sin (n : ℤ) (θ : ℝ) :
    (Polynomial.Chebyshev.T ℝ n).derivative.derivative.eval (Real.cos θ) * Real.sin θ ^ 3
      = (n : ℝ) * Real.sin ((n : ℝ) * θ) * Real.cos θ
        - (n : ℝ) ^ 2 * Real.cos ((n : ℝ) * θ) * Real.sin θ := by
  have hD : HasDerivAt
      (fun x : ℝ => (Polynomial.Chebyshev.T ℝ n).derivative.eval (Real.cos x) * Real.sin x)
      (((Polynomial.Chebyshev.T ℝ n).derivative.derivative.eval (Real.cos θ) * (-Real.sin θ))
        * Real.sin θ
        + (Polynomial.Chebyshev.T ℝ n).derivative.eval (Real.cos θ) * Real.cos θ) θ :=
    (hasDerivAt_chebT_deriv_cos n θ).mul (Real.hasDerivAt_sin θ)
  have hE : HasDerivAt (fun x : ℝ => (n : ℝ) * Real.sin ((n : ℝ) * x))
      ((n : ℝ) * (Real.cos ((n : ℝ) * θ) * (n : ℝ))) θ := by
    have h := ((Real.hasDerivAt_sin ((n : ℝ) * θ)).comp θ
      ((hasDerivAt_id θ).const_mul (n : ℝ))).const_mul (n : ℝ)
    simpa [Function.comp, mul_one] using h
  have hfun : (fun x : ℝ =>
        (Polynomial.Chebyshev.T ℝ n).derivative.eval (Real.cos x) * Real.sin x)
      = fun x : ℝ => (n : ℝ) * Real.sin ((n : ℝ) * x) :=
    funext fun x => chebyshevT_deriv_cos_mul_sin n x
  rw [← hfun] at hE
  have huniq := hD.unique hE
  have hid := chebyshevT_deriv_cos_mul_sin n θ
  linear_combination -Real.sin θ * huniq + Real.cos θ * hid

/-- Derivative of `ψ_n`. -/
private lemma hasDerivAt_psi (n : ℤ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (n : ℝ) * Real.sin ((n : ℝ) * s) * Real.cos s
        - (n : ℝ) ^ 2 * Real.cos ((n : ℝ) * s) * Real.sin s)
      (((n : ℝ) ^ 3 - (n : ℝ)) * Real.sin ((n : ℝ) * t) * Real.sin t) t := by
  have hsin : HasDerivAt (fun s : ℝ => Real.sin ((n : ℝ) * s))
      ((n : ℝ) * Real.cos ((n : ℝ) * t)) t := by
    have h := (Real.hasDerivAt_sin ((n : ℝ) * t)).comp t
      ((hasDerivAt_id t).const_mul (n : ℝ))
    convert h using 1
    · ext x; simp [Function.comp]
    · ring
  have hcosn : HasDerivAt (fun s : ℝ => Real.cos ((n : ℝ) * s))
      (-((n : ℝ) * Real.sin ((n : ℝ) * t))) t := by
    have h := (Real.hasDerivAt_cos ((n : ℝ) * t)).comp t
      ((hasDerivAt_id t).const_mul (n : ℝ))
    convert h using 1
    · ext x; simp [Function.comp]
    · ring
  have hA := (hsin.const_mul (n : ℝ)).mul (Real.hasDerivAt_cos t)
  have hB := (hcosn.const_mul ((n : ℝ) ^ 2)).mul (Real.hasDerivAt_sin t)
  convert hA.sub hB using 1
  ring

/-- MVT bound for `ψ_n` on `[0, θ]`. -/
private lemma abs_psi_le (n : ℤ) {θ : ℝ} (hθ0 : 0 ≤ θ) :
    |(n : ℝ) * Real.sin ((n : ℝ) * θ) * Real.cos θ
        - (n : ℝ) ^ 2 * Real.cos ((n : ℝ) * θ) * Real.sin θ|
      ≤ 2 * ((n.natAbs : ℝ)) ^ 4 * θ ^ 3 := by
  set N : ℝ := (n.natAbs : ℝ) with hN
  have hN0 : 0 ≤ N := by positivity
  have hkey : (N ^ 3 + N) * N ≤ 2 * N ^ 4 := by
    rcases eq_or_ne n 0 with hn | hn
    · subst hn; simp [hN]
    · have h2 : 0 < n.natAbs := Int.natAbs_pos.mpr hn
      have h1 : (1 : ℝ) ≤ N := by
        rw [hN]; exact_mod_cast h2
      have h4 : (1 : ℝ) ≤ N ^ 2 := by nlinarith [h1]
      nlinarith [h4, hN0, sq_nonneg (N ^ 2)]
  have hderiv : ∀ x ∈ Set.Icc (0 : ℝ) θ,
      ‖deriv (fun s : ℝ => (n : ℝ) * Real.sin ((n : ℝ) * s) * Real.cos s
        - (n : ℝ) ^ 2 * Real.cos ((n : ℝ) * s) * Real.sin s) x‖ ≤ 2 * N ^ 4 * θ ^ 2 := by
    intro x hx
    have hx0 : 0 ≤ x := hx.1
    have hxθ : x ≤ θ := hx.2
    have hd : deriv (fun s : ℝ => (n : ℝ) * Real.sin ((n : ℝ) * s) * Real.cos s
        - (n : ℝ) ^ 2 * Real.cos ((n : ℝ) * s) * Real.sin s) x
        = ((n : ℝ) ^ 3 - (n : ℝ)) * Real.sin ((n : ℝ) * x) * Real.sin x :=
      (hasDerivAt_psi n x).deriv
    have hNabs : |(n : ℝ)| = N := by rw [hN]; exact abs_int_cast_eq n
    have hs1 : |Real.sin ((n : ℝ) * x)| ≤ N * |Real.sin x| := by
      have h := abs_sin_int_mul_le n x
      rwa [hNabs] at h
    have hs2 : |Real.sin x| ≤ x := by
      have h := Real.abs_sin_le_abs (x := x)
      rwa [abs_of_nonneg hx0] at h
    have hN3 : |((n : ℝ) ^ 3 - (n : ℝ))| ≤ N ^ 3 + N := by
      calc |((n : ℝ) ^ 3 - (n : ℝ))|
          = |((n : ℝ) ^ 3 + -(n : ℝ))| := by ring_nf
        _ ≤ |((n : ℝ) ^ 3)| + |(-(n : ℝ))| := abs_add_le _ _
        _ = |(n : ℝ)| ^ 3 + |(n : ℝ)| := by rw [abs_pow, abs_neg]
        _ = N ^ 3 + N := by rw [hNabs]
    have hA : |((n : ℝ) ^ 3 - (n : ℝ)) * Real.sin ((n : ℝ) * x)| ≤ (N ^ 3 + N) * (N * x) := by
      rw [abs_mul]
      have hb : |Real.sin ((n : ℝ) * x)| ≤ N * x := by
        have h0 : (0 : ℝ) ≤ |Real.sin x| := abs_nonneg _
        nlinarith [hs1, hs2, hN0, hx0]
      exact mul_le_mul hN3 hb (abs_nonneg _) (by positivity)
    have hψ : |((n : ℝ) ^ 3 - (n : ℝ)) * Real.sin ((n : ℝ) * x) * Real.sin x|
        ≤ 2 * N ^ 4 * θ ^ 2 := by
      calc |((n : ℝ) ^ 3 - (n : ℝ)) * Real.sin ((n : ℝ) * x) * Real.sin x|
          = |((n : ℝ) ^ 3 - (n : ℝ)) * Real.sin ((n : ℝ) * x)| * |Real.sin x| := by
            rw [abs_mul]
        _ ≤ ((N ^ 3 + N) * (N * x)) * x :=
            mul_le_mul hA hs2 (abs_nonneg _) (by positivity)
        _ = (N ^ 3 + N) * N * x ^ 2 := by ring
        _ ≤ (2 * N ^ 4) * θ ^ 2 := by
            have hx2 : x ^ 2 ≤ θ ^ 2 := by nlinarith [hx0, hxθ, hθ0]
            have h1 : (0 : ℝ) ≤ (N ^ 3 + N) * N := by positivity
            have h2 : (0 : ℝ) ≤ 2 * N ^ 4 := by positivity
            have h3 : (0 : ℝ) ≤ x ^ 2 := by positivity
            have h4 : (0 : ℝ) ≤ θ ^ 2 := by positivity
            nlinarith [hkey, hx2, h1, h2, h3, h4]
        _ = 2 * N ^ 4 * θ ^ 2 := by ring
    rw [hd, Real.norm_eq_abs]
    exact hψ
  have hmain := Convex.norm_image_sub_le_of_norm_deriv_le
    (f := fun s : ℝ => (n : ℝ) * Real.sin ((n : ℝ) * s) * Real.cos s
      - (n : ℝ) ^ 2 * Real.cos ((n : ℝ) * s) * Real.sin s)
    (s := Set.Icc (0 : ℝ) θ) (x := 0) (y := θ) (C := 2 * N ^ 4 * θ ^ 2)
    (fun x _ => (hasDerivAt_psi n x).differentiableAt) hderiv (convex_Icc _ _)
    (Set.left_mem_Icc.mpr hθ0) (Set.right_mem_Icc.mpr hθ0)
  have hzero : (n : ℝ) * Real.sin ((n : ℝ) * 0) * Real.cos 0
      - (n : ℝ) ^ 2 * Real.cos ((n : ℝ) * 0) * Real.sin 0 = 0 := by simp
  have hmain' : |(n : ℝ) * Real.sin ((n : ℝ) * θ) * Real.cos θ
      - (n : ℝ) ^ 2 * Real.cos ((n : ℝ) * θ) * Real.sin θ|
      ≤ (2 * N ^ 4 * θ ^ 2) * θ := by
    simpa [hzero, Real.norm_eq_abs, abs_of_nonneg hθ0, sub_zero, mul_one] using hmain
  calc |(n : ℝ) * Real.sin ((n : ℝ) * θ) * Real.cos θ
        - (n : ℝ) ^ 2 * Real.cos ((n : ℝ) * θ) * Real.sin θ|
      ≤ (2 * N ^ 4 * θ ^ 2) * θ := hmain'
    _ = 2 * N ^ 4 * θ ^ 3 := by ring

/-- Bound for `T_n''` at `cos θ`, `θ ∈ (0, π/2]`. -/
private lemma abs_deriv2_chebyshevT_cos_le (n : ℤ) {θ : ℝ} (hθ0 : 0 < θ)
    (hθπ : θ ≤ Real.pi / 2) :
    |(Polynomial.Chebyshev.T ℝ n).derivative.derivative.eval (Real.cos θ)|
      ≤ 16 * ((n.natAbs : ℝ)) ^ 4 := by
  set N : ℝ := (n.natAbs : ℝ) with hN
  have hN0 : 0 ≤ N := by positivity
  have hθ0' : 0 ≤ θ := le_of_lt hθ0
  have hsinpos : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos, hθπ])
  have hid : |(Polynomial.Chebyshev.T ℝ n).derivative.derivative.eval (Real.cos θ)|
        * Real.sin θ ^ 3
      = |(n : ℝ) * Real.sin ((n : ℝ) * θ) * Real.cos θ
        - (n : ℝ) ^ 2 * Real.cos ((n : ℝ) * θ) * Real.sin θ| := by
    rw [← abs_of_pos (pow_pos hsinpos 3), ← abs_mul, chebyshevT_deriv2_cos_mul_sin n θ]
  have hψ := abs_psi_le n hθ0'
  have hjordan : 2 / Real.pi * θ ≤ Real.sin θ := Real.mul_le_sin hθ0' hθπ
  have hsin3 : 8 * θ ^ 3 / Real.pi ^ 3 ≤ Real.sin θ ^ 3 := by
    have h0 : (0 : ℝ) ≤ 2 / Real.pi * θ := by positivity
    have h := pow_le_pow_left₀ h0 hjordan 3
    have h2 : (2 / Real.pi * θ) ^ 3 = 8 * θ ^ 3 / Real.pi ^ 3 := by
      field_simp
      ring
    rwa [h2] at h
  have hchain : |(Polynomial.Chebyshev.T ℝ n).derivative.derivative.eval (Real.cos θ)|
        * (8 * θ ^ 3 / Real.pi ^ 3) ≤ 2 * N ^ 4 * θ ^ 3 := by
    have h1 : |(Polynomial.Chebyshev.T ℝ n).derivative.derivative.eval (Real.cos θ)|
          * (8 * θ ^ 3 / Real.pi ^ 3)
        ≤ |(Polynomial.Chebyshev.T ℝ n).derivative.derivative.eval (Real.cos θ)|
          * Real.sin θ ^ 3 :=
      mul_le_mul_of_nonneg_left hsin3 (abs_nonneg _)
    rw [hid] at h1
    exact h1.trans (by simpa [hN] using hψ)
  have hπ3 : Real.pi ^ 3 ≤ 64 := by
    have h := pow_le_pow_left₀ (le_of_lt Real.pi_pos) (le_of_lt Real.pi_lt_four) 3
    norm_num at h
    exact h
  have hnum : 2 * N ^ 4 * θ ^ 3 ≤ 16 * N ^ 4 * (8 * θ ^ 3 / Real.pi ^ 3) := by
    have hN4 : (0 : ℝ) ≤ N ^ 4 := by positivity
    have hθ3 : (0 : ℝ) ≤ θ ^ 3 := by positivity
    have hπ3pos : (0 : ℝ) < Real.pi ^ 3 := by positivity
    rw [show (16 : ℝ) * N ^ 4 * (8 * θ ^ 3 / Real.pi ^ 3)
        = (128 * N ^ 4 * θ ^ 3) / Real.pi ^ 3 by ring]
    rw [le_div_iff₀ hπ3pos]
    have hc : (0 : ℝ) ≤ 2 * N ^ 4 * θ ^ 3 := by positivity
    calc 2 * N ^ 4 * θ ^ 3 * Real.pi ^ 3 ≤ 2 * N ^ 4 * θ ^ 3 * 64 :=
          mul_le_mul_of_nonneg_left hπ3 hc
      _ = 128 * N ^ 4 * θ ^ 3 := by ring
  have hB : (0 : ℝ) < 8 * θ ^ 3 / Real.pi ^ 3 := by positivity
  have hfinal : |(Polynomial.Chebyshev.T ℝ n).derivative.derivative.eval (Real.cos θ)|
        * (8 * θ ^ 3 / Real.pi ^ 3) ≤ 16 * N ^ 4 * (8 * θ ^ 3 / Real.pi ^ 3) :=
    hchain.trans hnum
  exact le_of_mul_le_mul_right hfinal hB

/-- If `p (-x) = c * p x` pointwise then `p' (-x) = -(c * p' x)`. -/
private lemma deriv_eval_neg_of_eval_neg {p : Polynomial ℝ} {c : ℝ}
    (h : ∀ y : ℝ, p.eval (-y) = c * p.eval y) (x : ℝ) :
    p.derivative.eval (-x) = -(c * p.derivative.eval x) := by
  have hcomp : p.comp (-Polynomial.X) = Polynomial.C c * p := by
    apply Polynomial.funext
    intro y
    rw [Polynomial.eval_comp, Polynomial.eval_neg, Polynomial.eval_X, Polynomial.eval_mul,
      Polynomial.eval_C]
    exact h y
  have hder := congrArg Polynomial.derivative hcomp
  rw [Polynomial.derivative_comp, Polynomial.derivative_C_mul] at hder
  have hdX : Polynomial.derivative (-Polynomial.X : Polynomial ℝ) = -1 := by
    rw [show (-Polynomial.X : Polynomial ℝ) = Polynomial.C (-1) * Polynomial.X by simp,
      Polynomial.derivative_C_mul, Polynomial.derivative_X]
    simp
  rw [hdX] at hder
  have hval := congrArg (fun q : Polynomial ℝ => q.eval x) hder
  simp only [Polynomial.eval_mul, Polynomial.eval_neg, Polynomial.eval_one, Polynomial.eval_C,
    Polynomial.eval_comp, Polynomial.eval_X] at hval
  linarith [hval]

/-- Second derivative of `T_n` is even in absolute value. -/
private lemma abs_deriv2_chebyshevT_neg (n : ℤ) (x : ℝ) :
    |(Polynomial.Chebyshev.T ℝ n).derivative.derivative.eval (-x)|
      = |(Polynomial.Chebyshev.T ℝ n).derivative.derivative.eval x| := by
  have hc : |(((n.negOnePow : ℤ) : ℝ))| = 1 := by
    rw [← Int.cast_abs, Int.abs_negOnePow]
    norm_num
  have hT : ∀ y : ℝ, (Polynomial.Chebyshev.T ℝ n).eval (-y)
      = (((n.negOnePow : ℤ) : ℝ)) * (Polynomial.Chebyshev.T ℝ n).eval y :=
    fun y => Polynomial.Chebyshev.T_eval_neg ℝ n y
  have hp : ∀ y : ℝ, (Polynomial.Chebyshev.T ℝ n).derivative.eval (-y)
      = (-(((n.negOnePow : ℤ) : ℝ))) * (Polynomial.Chebyshev.T ℝ n).derivative.eval y := by
    intro y
    rw [deriv_eval_neg_of_eval_neg hT y]
    ring
  rw [deriv_eval_neg_of_eval_neg hp x, abs_neg, abs_mul, abs_neg, hc, one_mul]

/-- **Item 2 (Chebyshev part).** `|T_n''| ≤ 16 * n ^ 4` on `[-1, 1]`. -/
lemma abs_deriv2_chebyshevT_le (n : ℤ) {u : ℝ} (hu : u ∈ Set.Icc (-1 : ℝ) 1) :
    |(Polynomial.Chebyshev.T ℝ n).derivative.derivative.eval u|
      ≤ 16 * ((n.natAbs : ℝ)) ^ 4 := by
  have hclosed : IsClosed {u : ℝ |
      |(Polynomial.Chebyshev.T ℝ n).derivative.derivative.eval u|
        ≤ 16 * ((n.natAbs : ℝ)) ^ 4} :=
    isClosed_le (Polynomial.continuous _).abs continuous_const
  have hIcc : Set.Icc (0 : ℝ) 1 ⊆ {u : ℝ |
      |(Polynomial.Chebyshev.T ℝ n).derivative.derivative.eval u|
        ≤ 16 * ((n.natAbs : ℝ)) ^ 4} := by
    rw [← closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    refine hclosed.closure_subset_iff.mpr fun u hu => ?_
    have hcos : Real.cos (Real.arccos u) = u :=
      Real.cos_arccos (by linarith [hu.1]) hu.2.le
    rw [← hcos]
    exact abs_deriv2_chebyshevT_cos_le n (Real.arccos_pos.mpr hu.2)
      (le_of_lt (Real.arccos_lt_pi_div_two.mpr hu.1))
  by_cases h : 0 ≤ u
  · exact hIcc ⟨h, hu.2⟩
  · have hlt : u < 0 := not_le.mp h
    have h2 : -u ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith [hu.1]⟩
    exact (abs_deriv2_chebyshevT_neg n u) ▸ hIcc h2

/-! ## Complex forms of the Chebyshev bounds -/

/-- `T_n` has the same derivative over `ℂ` and over `ℝ` on the real axis. -/
private lemma chebyshevT_complex_derivative_eval (n : ℤ) (u : ℝ) :
    (Polynomial.Chebyshev.T ℂ n).derivative.eval (u : ℂ)
      = (((Polynomial.Chebyshev.T ℝ n).derivative.eval u : ℝ) : ℂ) := by
  have hA : HasDerivAt (fun y : ℝ => (Polynomial.Chebyshev.T ℂ n).eval (y : ℂ))
      ((Polynomial.Chebyshev.T ℂ n).derivative.eval (u : ℂ)) u :=
    (Polynomial.hasDerivAt (Polynomial.Chebyshev.T ℂ n) (u : ℂ)).comp_ofReal
  have hB : HasDerivAt (fun y : ℝ => (((Polynomial.Chebyshev.T ℝ n).eval y : ℝ) : ℂ))
      (((Polynomial.Chebyshev.T ℝ n).derivative.eval u : ℝ) : ℂ) u :=
    (Polynomial.hasDerivAt (Polynomial.Chebyshev.T ℝ n) u).ofReal_comp
  have hfun : (fun y : ℝ => (((Polynomial.Chebyshev.T ℝ n).eval y : ℝ) : ℂ))
      = fun y : ℝ => (Polynomial.Chebyshev.T ℂ n).eval (y : ℂ) :=
    funext fun y => Polynomial.Chebyshev.complex_ofReal_eval_T y n
  rw [hfun] at hB
  exact hA.unique hB

/-- `T_n''` has the same value over `ℂ` and over `ℝ` on the real axis. -/
private lemma chebyshevT_complex_derivative2_eval (n : ℤ) (u : ℝ) :
    (Polynomial.Chebyshev.T ℂ n).derivative.derivative.eval (u : ℂ)
      = (((Polynomial.Chebyshev.T ℝ n).derivative.derivative.eval u : ℝ) : ℂ) := by
  have hA : HasDerivAt (fun y : ℝ => (Polynomial.Chebyshev.T ℂ n).derivative.eval (y : ℂ))
      ((Polynomial.Chebyshev.T ℂ n).derivative.derivative.eval (u : ℂ)) u :=
    (Polynomial.hasDerivAt (Polynomial.Chebyshev.T ℂ n).derivative (u : ℂ)).comp_ofReal
  have hB : HasDerivAt
      (fun y : ℝ => (((Polynomial.Chebyshev.T ℝ n).derivative.eval y : ℝ) : ℂ))
      (((Polynomial.Chebyshev.T ℝ n).derivative.derivative.eval u : ℝ) : ℂ) u :=
    (Polynomial.hasDerivAt (Polynomial.Chebyshev.T ℝ n).derivative u).ofReal_comp
  have hfun : (fun y : ℝ => (((Polynomial.Chebyshev.T ℝ n).derivative.eval y : ℝ) : ℂ))
      = fun y : ℝ => (Polynomial.Chebyshev.T ℂ n).derivative.eval (y : ℂ) :=
    funext fun y => (chebyshevT_complex_derivative_eval n y).symm
  rw [hfun] at hB
  exact hA.unique hB

/-- Complex form of the first derivative bound. -/
lemma norm_deriv_chebyshevT_complex_le (n : ℤ) {u : ℝ} (hu : u ∈ Set.Icc (-1 : ℝ) 1) :
    ‖(Polynomial.Chebyshev.T ℂ n).derivative.eval (u : ℂ)‖ ≤ ((n.natAbs : ℝ)) ^ 2 := by
  rw [chebyshevT_complex_derivative_eval n u, Complex.norm_real]
  exact abs_deriv_chebyshevT_le n hu

/-- Complex form of the second derivative bound. -/
lemma norm_deriv2_chebyshevT_complex_le (n : ℤ) {u : ℝ} (hu : u ∈ Set.Icc (-1 : ℝ) 1) :
    ‖(Polynomial.Chebyshev.T ℂ n).derivative.derivative.eval (u : ℂ)‖
      ≤ 16 * ((n.natAbs : ℝ)) ^ 4 := by
  rw [chebyshevT_complex_derivative2_eval n u, Complex.norm_real]
  exact abs_deriv2_chebyshevT_le n hu

/-! ## The approximation polynomial `approxPoly` -/

/-- First `deriv` of a complex polynomial along the real axis. -/
lemma deriv_poly_ofReal (p : Polynomial ℂ) (u : ℝ) :
    deriv (fun x : ℝ => p.eval (x : ℂ)) u = p.derivative.eval (u : ℂ) :=
  ((Polynomial.hasDerivAt p (u : ℂ)).comp_ofReal).deriv

/-- Second `deriv` of a complex polynomial along the real axis. -/
lemma deriv2_poly_ofReal (p : Polynomial ℂ) (u : ℝ) :
    deriv (fun x : ℝ => deriv (fun y : ℝ => p.eval (y : ℂ)) x) u
      = p.derivative.derivative.eval (u : ℂ) := by
  rw [show (fun x : ℝ => deriv (fun y : ℝ => p.eval (y : ℂ)) x)
      = fun x : ℝ => p.derivative.eval (x : ℂ) from funext fun x => deriv_poly_ofReal p x]
  exact deriv_poly_ofReal p.derivative u

/-- The algebraic derivative of `approxPoly`. -/
lemma derivative_approxPoly (τ : ℝ) (k : ℕ) :
    (approxPoly τ k).derivative
      = ∑ m ∈ Finset.range (k - 1), Polynomial.C (2 * fcoef τ ((m : ℤ) + 1))
          * (Polynomial.Chebyshev.T ℂ ((m : ℤ) + 1)).derivative := by
  rw [approxPoly, map_add, Polynomial.derivative_C, zero_add, Polynomial.derivative_sum]
  exact Finset.sum_congr rfl fun m _ => Polynomial.derivative_C_mul _ _

/-- Evaluation of the derivative of `approxPoly`. -/
lemma eval_derivative_approxPoly (τ : ℝ) (k : ℕ) (u : ℝ) :
    (approxPoly τ k).derivative.eval (u : ℂ)
      = ∑ m ∈ Finset.range (k - 1), 2 * fcoef τ ((m : ℤ) + 1)
          * (Polynomial.Chebyshev.T ℂ ((m : ℤ) + 1)).derivative.eval (u : ℂ) := by
  rw [derivative_approxPoly, Polynomial.eval_finsetSum]
  exact Finset.sum_congr rfl fun m _ => by rw [Polynomial.eval_mul, Polynomial.eval_C]

/-- The algebraic second derivative of `approxPoly`. -/
lemma derivative2_approxPoly (τ : ℝ) (k : ℕ) :
    (approxPoly τ k).derivative.derivative
      = ∑ m ∈ Finset.range (k - 1), Polynomial.C (2 * fcoef τ ((m : ℤ) + 1))
          * (Polynomial.Chebyshev.T ℂ ((m : ℤ) + 1)).derivative.derivative := by
  rw [derivative_approxPoly, Polynomial.derivative_sum]
  exact Finset.sum_congr rfl fun m _ => Polynomial.derivative_C_mul _ _

/-- Evaluation of the second derivative of `approxPoly`. -/
lemma eval_derivative2_approxPoly (τ : ℝ) (k : ℕ) (u : ℝ) :
    (approxPoly τ k).derivative.derivative.eval (u : ℂ)
      = ∑ m ∈ Finset.range (k - 1), 2 * fcoef τ ((m : ℤ) + 1)
          * (Polynomial.Chebyshev.T ℂ ((m : ℤ) + 1)).derivative.derivative.eval (u : ℂ) := by
  rw [derivative2_approxPoly, Polynomial.eval_finsetSum]
  exact Finset.sum_congr rfl fun m _ => by rw [Polynomial.eval_mul, Polynomial.eval_C]

/-- **Item 2 (explicit constant).** `‖(approxPoly τ k)'‖ ≤ 2 e^{τ sinh δ} k³ e^{-δ} + 1`
on `[-1, 1]`. -/
lemma norm_deriv_approxPoly_le' (τ : ℝ) (hτ : 0 ≤ τ) {δ : ℝ} (hδ : 0 < δ) (k : ℕ)
    {u : ℝ} (hu : u ∈ Set.Icc (-1 : ℝ) 1) :
    ‖deriv (fun x : ℝ => (approxPoly τ k).eval (x : ℂ)) u‖
      ≤ 2 * Real.exp (τ * Real.sinh δ) * (k : ℝ) ^ 3 * Real.exp (-δ) + 1 := by
  set E : ℝ := Real.exp (τ * Real.sinh δ) with hE
  set r : ℝ := Real.exp (-δ) with hr
  have hE0 : 0 ≤ E := by positivity
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r ≤ 1 := by
    rw [hr]
    exact le_of_lt (Real.exp_lt_one_iff.mpr (by linarith))
  rw [deriv_poly_ofReal, eval_derivative_approxPoly]
  refine (norm_sum_le (Finset.range (k - 1)) _).trans ?_
  have hterm : ∀ m ∈ Finset.range (k - 1),
      ‖2 * fcoef τ ((m : ℤ) + 1)
        * (Polynomial.Chebyshev.T ℂ ((m : ℤ) + 1)).derivative.eval (u : ℂ)‖
        ≤ 2 * E * r ^ (m + 1) * (k : ℝ) ^ 2 := by
    intro m hm
    have hmk : m < k - 1 := Finset.mem_range.mp hm
    have hcastZ : ((m : ℤ) + 1 : ℤ) = ((m + 1 : ℕ) : ℤ) := by push_cast; ring
    have hcastR : ((((m : ℤ) + 1 : ℤ)) : ℝ) * δ = ((m + 1 : ℕ) : ℝ) * δ := by
      push_cast; ring
    have hjpos : (0 : ℝ) < (((m : ℤ) + 1 : ℤ) : ℝ) := by
      have : (0 : ℤ) < (m : ℤ) + 1 := by omega
      exact_mod_cast this
    have hjk : ((m + 1 : ℕ) : ℝ) ≤ (k : ℝ) := by
      have h1 : m + 1 ≤ k := by omega
      exact_mod_cast h1
    have hf : ‖fcoef τ ((m : ℤ) + 1)‖ ≤ E * r ^ (m + 1) := by
      have h1 := norm_fcoef_le τ hτ hδ ((m : ℤ) + 1)
      rw [abs_of_pos hjpos] at h1
      have hexp : Real.exp (τ * Real.sinh δ - (((m : ℤ) + 1 : ℤ) : ℝ) * δ)
          = E * r ^ (m + 1) := by
        rw [hE, hr, hcastR, Real.exp_sub, Real.exp_nat_mul, Real.exp_neg, div_eq_mul_inv,
          inv_pow]
      rwa [hexp] at h1
    have hD : ‖(Polynomial.Chebyshev.T ℂ ((m : ℤ) + 1)).derivative.eval (u : ℂ)‖
        ≤ (k : ℝ) ^ 2 := by
      refine (norm_deriv_chebyshevT_complex_le _ hu).trans ?_
      rw [hcastZ, Int.natAbs_natCast]
      exact pow_le_pow_left₀ (by positivity) hjk 2
    calc ‖2 * fcoef τ ((m : ℤ) + 1)
          * (Polynomial.Chebyshev.T ℂ ((m : ℤ) + 1)).derivative.eval (u : ℂ)‖
        = 2 * ‖fcoef τ ((m : ℤ) + 1)‖
          * ‖(Polynomial.Chebyshev.T ℂ ((m : ℤ) + 1)).derivative.eval (u : ℂ)‖ := by
          rw [norm_mul, norm_mul]
          norm_num
      _ ≤ 2 * (E * r ^ (m + 1)) * (k : ℝ) ^ 2 := by
          have h1 : (0 : ℝ) ≤ ‖fcoef τ ((m : ℤ) + 1)‖ := norm_nonneg _
          have h2 : (0 : ℝ) ≤
            ‖(Polynomial.Chebyshev.T ℂ ((m : ℤ) + 1)).derivative.eval (u : ℂ)‖ :=
            norm_nonneg _
          nlinarith [hf, hD, h1, h2]
      _ = 2 * E * r ^ (m + 1) * (k : ℝ) ^ 2 := by ring
  have hsum : ∑ m ∈ Finset.range (k - 1), r ^ (m + 1) ≤ (k : ℝ) * r := by
    calc ∑ m ∈ Finset.range (k - 1), r ^ (m + 1)
        ≤ ∑ _m ∈ Finset.range (k - 1), r :=
          Finset.sum_le_sum fun m _ => by
            rw [pow_succ]
            have h1 : r ^ m ≤ 1 := pow_le_one₀ hr0 hr1
            nlinarith [h1, hr0]
      _ = ((k - 1 : ℕ) : ℝ) * r := by simp
      _ ≤ (k : ℝ) * r := by
          refine mul_le_mul_of_nonneg_right ?_ hr0
          exact_mod_cast Nat.sub_le k 1
  calc ∑ m ∈ Finset.range (k - 1),
        ‖2 * fcoef τ ((m : ℤ) + 1)
          * (Polynomial.Chebyshev.T ℂ ((m : ℤ) + 1)).derivative.eval (u : ℂ)‖
      ≤ ∑ m ∈ Finset.range (k - 1), 2 * E * r ^ (m + 1) * (k : ℝ) ^ 2 :=
        Finset.sum_le_sum hterm
    _ = 2 * E * (k : ℝ) ^ 2 * ∑ m ∈ Finset.range (k - 1), r ^ (m + 1) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun m _ => by ring
    _ ≤ 2 * E * (k : ℝ) ^ 2 * ((k : ℝ) * r) := by
        refine mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ 2 * E * (k : ℝ) ^ 3 * r + 1 := by
        have : 2 * E * (k : ℝ) ^ 2 * ((k : ℝ) * r) = 2 * E * (k : ℝ) ^ 3 * r := by ring
        rw [this]
        linarith

/-- **Item 2 (explicit constant).** Second derivative bound for `approxPoly`. -/
lemma norm_deriv2_approxPoly_le' (τ : ℝ) (hτ : 0 ≤ τ) {δ : ℝ} (hδ : 0 < δ) (k : ℕ)
    {u : ℝ} (hu : u ∈ Set.Icc (-1 : ℝ) 1) :
    ‖deriv (fun x : ℝ => deriv (fun y : ℝ => (approxPoly τ k).eval (y : ℂ)) x) u‖
      ≤ 32 * Real.exp (τ * Real.sinh δ) * (k : ℝ) ^ 5 * Real.exp (-δ) + 1 := by
  set E : ℝ := Real.exp (τ * Real.sinh δ) with hE
  set r : ℝ := Real.exp (-δ) with hr
  have hE0 : 0 ≤ E := by positivity
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r ≤ 1 := by
    rw [hr]
    exact le_of_lt (Real.exp_lt_one_iff.mpr (by linarith))
  rw [deriv2_poly_ofReal, eval_derivative2_approxPoly]
  refine (norm_sum_le (Finset.range (k - 1)) _).trans ?_
  have hterm : ∀ m ∈ Finset.range (k - 1),
      ‖2 * fcoef τ ((m : ℤ) + 1)
        * (Polynomial.Chebyshev.T ℂ ((m : ℤ) + 1)).derivative.derivative.eval (u : ℂ)‖
        ≤ 2 * E * r ^ (m + 1) * (16 * (k : ℝ) ^ 4) := by
    intro m hm
    have hmk : m < k - 1 := Finset.mem_range.mp hm
    have hcastZ : ((m : ℤ) + 1 : ℤ) = ((m + 1 : ℕ) : ℤ) := by push_cast; ring
    have hcastR : ((((m : ℤ) + 1 : ℤ)) : ℝ) * δ = ((m + 1 : ℕ) : ℝ) * δ := by
      push_cast; ring
    have hjpos : (0 : ℝ) < (((m : ℤ) + 1 : ℤ) : ℝ) := by
      have : (0 : ℤ) < (m : ℤ) + 1 := by omega
      exact_mod_cast this
    have hjk : ((m + 1 : ℕ) : ℝ) ≤ (k : ℝ) := by
      have h1 : m + 1 ≤ k := by omega
      exact_mod_cast h1
    have hf : ‖fcoef τ ((m : ℤ) + 1)‖ ≤ E * r ^ (m + 1) := by
      have h1 := norm_fcoef_le τ hτ hδ ((m : ℤ) + 1)
      rw [abs_of_pos hjpos] at h1
      have hexp : Real.exp (τ * Real.sinh δ - (((m : ℤ) + 1 : ℤ) : ℝ) * δ)
          = E * r ^ (m + 1) := by
        rw [hE, hr, hcastR, Real.exp_sub, Real.exp_nat_mul, Real.exp_neg, div_eq_mul_inv,
          inv_pow]
      rwa [hexp] at h1
    have hD : ‖(Polynomial.Chebyshev.T ℂ ((m : ℤ) + 1)).derivative.derivative.eval (u : ℂ)‖
        ≤ 16 * (k : ℝ) ^ 4 := by
      refine (norm_deriv2_chebyshevT_complex_le _ hu).trans ?_
      rw [hcastZ, Int.natAbs_natCast]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hjk 4) (by norm_num)
    calc ‖2 * fcoef τ ((m : ℤ) + 1)
          * (Polynomial.Chebyshev.T ℂ ((m : ℤ) + 1)).derivative.derivative.eval (u : ℂ)‖
        = 2 * ‖fcoef τ ((m : ℤ) + 1)‖
          * ‖(Polynomial.Chebyshev.T ℂ ((m : ℤ) + 1)).derivative.derivative.eval (u : ℂ)‖ := by
          rw [norm_mul, norm_mul]
          norm_num
      _ ≤ 2 * (E * r ^ (m + 1)) * (16 * (k : ℝ) ^ 4) := by
          have h1 : (0 : ℝ) ≤ ‖fcoef τ ((m : ℤ) + 1)‖ := norm_nonneg _
          have h2 : (0 : ℝ) ≤
            ‖(Polynomial.Chebyshev.T ℂ ((m : ℤ) + 1)).derivative.derivative.eval (u : ℂ)‖ :=
            norm_nonneg _
          nlinarith [hf, hD, h1, h2]
      _ = 2 * E * r ^ (m + 1) * (16 * (k : ℝ) ^ 4) := by ring
  have hsum : ∑ m ∈ Finset.range (k - 1), r ^ (m + 1) ≤ (k : ℝ) * r := by
    calc ∑ m ∈ Finset.range (k - 1), r ^ (m + 1)
        ≤ ∑ _m ∈ Finset.range (k - 1), r :=
          Finset.sum_le_sum fun m _ => by
            rw [pow_succ]
            have h1 : r ^ m ≤ 1 := pow_le_one₀ hr0 hr1
            nlinarith [h1, hr0]
      _ = ((k - 1 : ℕ) : ℝ) * r := by simp
      _ ≤ (k : ℝ) * r := by
          refine mul_le_mul_of_nonneg_right ?_ hr0
          exact_mod_cast Nat.sub_le k 1
  calc ∑ m ∈ Finset.range (k - 1),
        ‖2 * fcoef τ ((m : ℤ) + 1)
          * (Polynomial.Chebyshev.T ℂ ((m : ℤ) + 1)).derivative.derivative.eval (u : ℂ)‖
      ≤ ∑ m ∈ Finset.range (k - 1), 2 * E * r ^ (m + 1) * (16 * (k : ℝ) ^ 4) :=
        Finset.sum_le_sum hterm
    _ = 2 * E * (16 * (k : ℝ) ^ 4) * ∑ m ∈ Finset.range (k - 1), r ^ (m + 1) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun m _ => by ring
    _ ≤ 2 * E * (16 * (k : ℝ) ^ 4) * ((k : ℝ) * r) := by
        refine mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ 32 * E * (k : ℝ) ^ 5 * r + 1 := by
        have : 2 * E * (16 * (k : ℝ) ^ 4) * ((k : ℝ) * r) = 32 * E * (k : ℝ) ^ 5 * r := by
          ring
        rw [this]
        linarith

/-- **Item 2.** Existence of an explicit constant bounding `‖(approxPoly τ k)'‖` on `[-1, 1]`. -/
lemma norm_deriv_approxPoly_le (τ : ℝ) (hτ : 0 ≤ τ) {δ : ℝ} (hδ : 0 < δ) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ u ∈ Set.Icc (-1 : ℝ) 1,
      ‖deriv (fun x : ℝ => (approxPoly τ k).eval (x : ℂ)) u‖ ≤ C :=
  ⟨2 * Real.exp (τ * Real.sinh δ) * (k : ℝ) ^ 3 * Real.exp (-δ) + 1,
    by positivity,
    fun u hu => norm_deriv_approxPoly_le' τ hτ hδ k hu⟩

/-- **Item 2 (second derivative).** Existence of an explicit constant bounding
`‖(approxPoly τ k)''‖` on `[-1, 1]`. -/
lemma norm_deriv2_approxPoly_le (τ : ℝ) (hτ : 0 ≤ τ) {δ : ℝ} (hδ : 0 < δ) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ u ∈ Set.Icc (-1 : ℝ) 1,
      ‖deriv (fun x : ℝ => deriv (fun y : ℝ => (approxPoly τ k).eval (y : ℂ)) x) u‖ ≤ C :=
  ⟨32 * Real.exp (τ * Real.sinh δ) * (k : ℝ) ^ 5 * Real.exp (-δ) + 1,
    by positivity,
    fun u hu => norm_deriv2_approxPoly_le' τ hτ hδ k hu⟩

end RobustZ
