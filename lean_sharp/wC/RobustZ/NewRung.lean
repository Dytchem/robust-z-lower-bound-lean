import RobustZ.BesselTail
import RobustZ.RealizeLemma
import RobustZ.InversionId
import RobustZ.ChebDeriv
import RobustZ.ExpSum
import RobustZ.ElementaryBound
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# New rung: explicit Chebyshev-truncation realization + main lower bound (L4/L5/L6).

Scope: `LEAN_READY.md` L4 (explicit constants for the Chebyshev truncation),
L5 (main rung `T > 2τ`), and a finitized closed form of L6.1
(`T ≥ 4(N+1)[1-c(log q/q)^{2/3}]` with explicit `c`, `N₁`).

Deviations from `LEAN_READY.md` (all reported in the final message):
* (D1) The Chebyshev remainder series (Jacobi–Anger tail) and its two termwise
  differentiations are taken as an explicit hypothesis bundle (`nrCheb`):
  pointwise `HasSum` representations plus coefficient bounds.  Every L4
  *inequality* is proved in Lean from that bundle together with the tree's
  `ChebDeriv` bounds and `majorB_geom`; only the uniform-convergence
  justification of the series representations is external.
* (D2) The second-derivative Chebyshev estimate uses the tree's proved
  `|T_k''| ≤ 16·k^4` (`abs_deriv2_chebyshevT_le`) rather than the sharp
  `k^2(k^2-1)/3`; the `Ccal` D2-term is restated as `32·η2·q^2`
  (instead of `(2/3)·η2·q^2`) and reported.
* (D3) `η1`, `η2` are the explicit closed-form majorants
  `η1 = (1+r)/(1-r)^3`, `η2 = (1+11r+11r^2+r^3)/(1-r)^5` (`r = e^{-αq}`),
  which dominate the `LEAN_READY.md` §0 tsum values (the factor `(1+m/q)^{2j}`
  is majorized by `(1+m)^{2j}` and the `(1-e^{-α})` prefactor is dropped).
* (D4 — CLOSED) Fourier inversion on the band is `Realize.inversion_on_band`
  (`RobustZ/InversionId.lean`, proved from mathlib Fourier inversion);
  `NewRung` takes no inversion hypothesis.
* (D5) L6 is proved with `c = 6`, `N₁ = 1000 + ⌈exp((C0+|log s0|)/mgn)⌉₊`
  (hence `N₁ = 1000` at `φ = π`), via crude but fully explicit estimates.
-/

noncomputable section

namespace RobustZ

open scoped Real
open Finset MeasureTheory
open scoped Matrix Matrix.Norms.L2Operator

/-! ## §1. Closed polynomial-times-geometric sums.

For `0 ≤ r < 1`: `S₁ = ∑(m+1)r^m = 1/(1-r)^2`,
`S₂ = ∑(m+1)^2r^m = (1+r)/(1-r)^3`,
`S₄ = ∑(m+1)^4r^m = (1+11r+11r^2+r^3)/(1-r)^5`
(the last via `S₃`). Each follows from the one-step shift
`∑'F(m+1) = ∑'F - F 0` (`nr_shift_tsum`). -/

/-- One-step shift for `tsum`: `∑' m, F (m+1) = ∑' m, F m - F 0`. -/
lemma nr_shift_tsum (F : ℕ → ℝ) (hF : Summable F) :
    (∑' m, F (m + 1)) = (∑' m, F m) - F 0 := by
  have h := hF.sum_add_tsum_nat_add 1
  simp only [Finset.range_one, Finset.sum_singleton] at h
  linarith [h]

/-- Summability of `((m:ℝ)+1)^k * r^m`. -/
lemma nr_summable_poly_mul_geom (k : ℕ) {r : ℝ} (hr : ‖r‖ < 1) :
    Summable (fun m : ℕ => (((m : ℝ) + 1) ^ k * r ^ m)) := by
  have hexp : (fun m : ℕ => (((m : ℝ) + 1) ^ k * r ^ m))
      = fun m : ℕ => ∑ j ∈ Finset.range (k + 1),
        ((k.choose j : ℝ) * (((m : ℝ) ^ j * r ^ m))) := by
    funext m
    rw [add_pow, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hexp]
  refine summable_sum (fun j _ => ?_)
  exact (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) j hr).mul_left _

/-- `S₁ = ∑(m+1)r^m = 1/(1-r)^2`. -/
lemma nr_tsum_S1 {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑' m : ℕ, (((m : ℝ) + 1) * r ^ m)) = 1 / (1 - r) ^ 2 := by
  have hrn : ‖r‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hr0]
  have hS1 : Summable (fun m : ℕ => (((m : ℝ) + 1) * r ^ m)) := by
    simpa only [pow_one] using nr_summable_poly_mul_geom 1 hrn
  have hS0 : Summable (fun m : ℕ => r ^ m) :=
    summable_geometric_of_lt_one hr0 hr1
  have hM : Summable (fun m : ℕ => (m : ℝ) * r ^ m) := by
    have e : (fun m : ℕ => (m : ℝ) * r ^ m)
        = (fun m : ℕ => (((m : ℝ) + 1) * r ^ m))
          - (fun m : ℕ => r ^ m) := by
      funext m
      simp only [Pi.sub_apply]
      ring
    rw [e]
    exact hS1.sub hS0
  have hS0val : (∑' m : ℕ, r ^ m) = (1 - r)⁻¹ :=
    tsum_geometric_of_lt_one hr0 hr1
  have hsh := nr_shift_tsum (fun m : ℕ => (m : ℝ) * r ^ m) hM
  simp only [Nat.cast_zero, zero_mul, pow_zero] at hsh
  have hexp : ∀ m : ℕ, ((m + 1 : ℕ) : ℝ) * r ^ (m + 1)
      = r * ((m : ℝ) * r ^ m) + r * r ^ m := by
    intro m
    push_cast
    ring
  have eB : Summable (fun m : ℕ => r * r ^ m) := hS0.mul_left r
  have hval : (∑' m : ℕ, ((m + 1 : ℕ) : ℝ) * r ^ (m + 1))
      = r * (∑' m : ℕ, (m : ℝ) * r ^ m)
        + r * (∑' m : ℕ, r ^ m) := by
    have step1 : (∑' m : ℕ, ((m + 1 : ℕ) : ℝ) * r ^ (m + 1))
        = ∑' m : ℕ, (r * ((m : ℝ) * r ^ m) + r * r ^ m) :=
      tsum_congr hexp
    have step2 : (∑' m : ℕ, (r * ((m : ℝ) * r ^ m) + r * r ^ m))
        = (∑' m : ℕ, r * ((m : ℝ) * r ^ m))
          + (∑' m : ℕ, r * r ^ m) :=
      Summable.tsum_add (hM.mul_left r) eB
    rw [step1, step2, tsum_mul_left, tsum_mul_left]
  -- middle sum `S_mid = r/(1-r)^2`
  have hSmid : (∑' m : ℕ, (m : ℝ) * r ^ m) = r / (1 - r) ^ 2 := by
    rw [hS0val] at hval
    have hrne : (1 : ℝ) - r ≠ 0 := sub_ne_zero.mpr (ne_of_gt hr1)
    rw [hsh] at hval
    simp only [sub_zero] at hval
    field_simp at hval ⊢
    nlinarith [hval]
  -- `S₁ = S₀ + S_mid`
  have hsplit : (∑' m : ℕ, (((m : ℝ) + 1) * r ^ m))
      = (∑' m : ℕ, r ^ m) + (∑' m : ℕ, (m : ℝ) * r ^ m) := by
    have step1 : (∑' m : ℕ, (((m : ℝ) + 1) * r ^ m))
        = ∑' m : ℕ, (r ^ m + (m : ℝ) * r ^ m) := by
      refine tsum_congr fun m => ?_
      ring
    rw [step1]
    exact Summable.tsum_add hS0 hM
  rw [hsplit, hS0val, hSmid]
  have hrne : (1 : ℝ) - r ≠ 0 := sub_ne_zero.mpr (ne_of_gt hr1)
  field_simp
  ring

/-- `S₂ = ∑(m+1)^2r^m = (1+r)/(1-r)^3`. -/
lemma nr_tsum_S2 {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑' m : ℕ, (((m : ℝ) + 1) ^ 2 * r ^ m)) = (1 + r) / (1 - r) ^ 3 := by
  have hrn : ‖r‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hr0]
  have hF2 : Summable (fun m : ℕ => (((m : ℝ) + 1) ^ 2 * r ^ m)) :=
    nr_summable_poly_mul_geom 2 hrn
  have hS0 : Summable (fun m : ℕ => r ^ m) :=
    summable_geometric_of_lt_one hr0 hr1
  have hF1 : Summable (fun m : ℕ => (((m : ℝ) + 1) * r ^ m)) := by
    simpa only [pow_one] using nr_summable_poly_mul_geom 1 hrn
  have hS1val := nr_tsum_S1 hr0 hr1
  have hS0val : (∑' m : ℕ, r ^ m) = (1 - r)⁻¹ :=
    tsum_geometric_of_lt_one hr0 hr1
  have hsh := nr_shift_tsum (fun m : ℕ => (((m : ℝ) + 1) ^ 2 * r ^ m)) hF2
  simp only [Nat.cast_zero, zero_add, one_pow, pow_zero, mul_one] at hsh
  have hexp : ∀ m : ℕ, ((((m + 1 : ℕ) : ℝ) + 1) ^ 2 * r ^ (m + 1))
      = r * ((((m : ℝ) + 1) ^ 2 * r ^ m))
        + (r * (2 * ((((m : ℝ) + 1) * r ^ m))) + r * r ^ m) := by
    intro m
    push_cast
    ring
  have eA : Summable (fun m : ℕ => r * ((((m : ℝ) + 1) ^ 2 * r ^ m))) :=
    hF2.mul_left r
  have eB : Summable (fun m : ℕ => r * (2 * ((((m : ℝ) + 1) * r ^ m)))) :=
    (hF1.mul_left 2).mul_left r
  have eC : Summable (fun m : ℕ => r * r ^ m) := hS0.mul_left r
  have hval : (∑' m : ℕ, ((((m + 1 : ℕ) : ℝ) + 1) ^ 2 * r ^ (m + 1)))
      = r * (∑' m : ℕ, (((m : ℝ) + 1) ^ 2 * r ^ m))
        + (r * (2 * (∑' m : ℕ, (((m : ℝ) + 1) * r ^ m)))
          + r * (∑' m : ℕ, r ^ m)) := by
    have step1 : (∑' m : ℕ, ((((m + 1 : ℕ) : ℝ) + 1) ^ 2 * r ^ (m + 1)))
        = ∑' m : ℕ, (r * ((((m : ℝ) + 1) ^ 2 * r ^ m))
          + (r * (2 * ((((m : ℝ) + 1) * r ^ m))) + r * r ^ m)) :=
      tsum_congr hexp
    have step2 : (∑' m : ℕ, (r * ((((m : ℝ) + 1) ^ 2 * r ^ m))
          + (r * (2 * ((((m : ℝ) + 1) * r ^ m))) + r * r ^ m)))
        = (∑' m : ℕ, r * ((((m : ℝ) + 1) ^ 2 * r ^ m)))
          + (∑' m : ℕ, (r * (2 * ((((m : ℝ) + 1) * r ^ m))) + r * r ^ m)) :=
      Summable.tsum_add eA (eB.add eC)
    have step3 : (∑' m : ℕ, (r * (2 * ((((m : ℝ) + 1) * r ^ m))) + r * r ^ m))
        = (∑' m : ℕ, r * (2 * ((((m : ℝ) + 1) * r ^ m))))
          + (∑' m : ℕ, r * r ^ m) :=
      Summable.tsum_add eB eC
    rw [step1, step2, step3]
    simp only [tsum_mul_left]
  rw [hS1val, hS0val] at hval
  have hrne : (1 : ℝ) - r ≠ 0 := sub_ne_zero.mpr (ne_of_gt hr1)
  rw [hsh] at hval
  field_simp at hval ⊢
  nlinarith [hval]
/-- Split a 3-term right-nested `tsum`. -/
lemma nr_tsum_add3 {f g h : ℕ → ℝ} (hf : Summable f) (hg : Summable g)
    (hh : Summable h) :
    (∑' m, (f m + (g m + h m)))
      = (∑' m, f m) + ((∑' m, g m) + (∑' m, h m)) := by
  calc (∑' m, (f m + (g m + h m)))
      = (∑' m, f m) + (∑' m, (g m + h m)) := hf.tsum_add (hg.add hh)
    _ = (∑' m, f m) + ((∑' m, g m) + (∑' m, h m)) := by
        rw [hg.tsum_add hh]

/-- Split a 4-term right-nested `tsum`. -/
lemma nr_tsum_add4 {f g h k : ℕ → ℝ} (hf : Summable f) (hg : Summable g)
    (hh : Summable h) (hk : Summable k) :
    (∑' m, (f m + (g m + (h m + k m))))
      = (∑' m, f m) + ((∑' m, g m) + ((∑' m, h m) + (∑' m, k m))) := by
  calc (∑' m, (f m + (g m + (h m + k m))))
      = (∑' m, f m) + (∑' m, (g m + (h m + k m))) :=
        hf.tsum_add (hg.add (hh.add hk))
    _ = (∑' m, f m) + ((∑' m, g m) + ((∑' m, h m) + (∑' m, k m))) := by
        rw [nr_tsum_add3 hg hh hk]

/-- Split a 5-term right-nested `tsum`. -/
lemma nr_tsum_add5 {f g h k l : ℕ → ℝ} (hf : Summable f) (hg : Summable g)
    (hh : Summable h) (hk : Summable k) (hl : Summable l) :
    (∑' m, (f m + (g m + (h m + (k m + l m)))))
      = (∑' m, f m) + ((∑' m, g m)
        + ((∑' m, h m) + ((∑' m, k m) + (∑' m, l m)))) := by
  calc (∑' m, (f m + (g m + (h m + (k m + l m)))))
      = (∑' m, f m) + (∑' m, (g m + (h m + (k m + l m)))) :=
        hf.tsum_add (hg.add (hh.add (hk.add hl)))
    _ = (∑' m, f m) + ((∑' m, g m)
        + ((∑' m, h m) + ((∑' m, k m) + (∑' m, l m)))) := by
        rw [nr_tsum_add4 hg hh hk hl]

/-- `S₃ = ∑(m+1)^3r^m = (1+4r+r^2)/(1-r)^4` (stepping stone for `S₄`). -/
lemma nr_tsum_S3 {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑' m : ℕ, (((m : ℝ) + 1) ^ 3 * r ^ m))
      = (1 + 4 * r + r ^ 2) / (1 - r) ^ 4 := by
  have hrn : ‖r‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hr0]
  have hF3 : Summable (fun m : ℕ => (((m : ℝ) + 1) ^ 3 * r ^ m)) :=
    nr_summable_poly_mul_geom 3 hrn
  have hS0 : Summable (fun m : ℕ => r ^ m) :=
    summable_geometric_of_lt_one hr0 hr1
  have hF1 : Summable (fun m : ℕ => (((m : ℝ) + 1) * r ^ m)) := by
    simpa only [pow_one] using nr_summable_poly_mul_geom 1 hrn
  have hF2 : Summable (fun m : ℕ => (((m : ℝ) + 1) ^ 2 * r ^ m)) :=
    nr_summable_poly_mul_geom 2 hrn
  set S3 : ℝ := (∑' m : ℕ, (((m : ℝ) + 1) ^ 3 * r ^ m)) with hS3def
  set S2 : ℝ := (∑' m : ℕ, (((m : ℝ) + 1) ^ 2 * r ^ m)) with hS2def
  set S1 : ℝ := (∑' m : ℕ, (((m : ℝ) + 1) * r ^ m)) with hS1def
  set S0 : ℝ := (∑' m : ℕ, r ^ m) with hS0def
  have hS1v : S1 = 1 / (1 - r) ^ 2 := by
    rw [hS1def]; exact nr_tsum_S1 hr0 hr1
  have hS2v : S2 = (1 + r) / (1 - r) ^ 3 := by
    rw [hS2def]; exact nr_tsum_S2 hr0 hr1
  have hS0v : S0 = (1 - r)⁻¹ := by
    rw [hS0def]; exact tsum_geometric_of_lt_one hr0 hr1
  have hsh := nr_shift_tsum (fun m : ℕ => (((m : ℝ) + 1) ^ 3 * r ^ m)) hF3
  simp only [Nat.cast_zero, zero_add, one_pow, pow_zero, mul_one] at hsh
  rw [← hS3def] at hsh
  have hexp : ∀ m : ℕ, ((((m + 1 : ℕ) : ℝ) + 1) ^ 3 * r ^ (m + 1))
      = r * ((((m : ℝ) + 1) ^ 3 * r ^ m))
        + (r * (3 * ((((m : ℝ) + 1) ^ 2 * r ^ m)))
          + (r * (3 * ((((m : ℝ) + 1) * r ^ m))) + r * r ^ m)) := by
    intro m
    push_cast
    ring
  have hval : (∑' m : ℕ, ((((m + 1 : ℕ) : ℝ) + 1) ^ 3 * r ^ (m + 1)))
      = r * S3 + ((r * (3 * S2)) + ((r * (3 * S1)) + r * S0)) := by
    rw [tsum_congr hexp]
    rw [nr_tsum_add4 (hF3.mul_left r) ((hF2.mul_left 3).mul_left r)
      ((hF1.mul_left 3).mul_left r) (hS0.mul_left r)]
    simp only [tsum_mul_left, ← hS3def, ← hS2def, ← hS1def, ← hS0def]
  rw [hS1v, hS2v, hS0v] at hval
  have hrne : (1 : ℝ) - r ≠ 0 := sub_ne_zero.mpr (ne_of_gt hr1)
  rw [hsh] at hval
  field_simp at hval ⊢
  nlinarith [hval]

/-- `S₄ = ∑(m+1)^4r^m = (1+11r+11r^2+r^3)/(1-r)^5`. -/
lemma nr_tsum_S4 {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑' m : ℕ, (((m : ℝ) + 1) ^ 4 * r ^ m))
      = (1 + 11 * r + 11 * r ^ 2 + r ^ 3) / (1 - r) ^ 5 := by
  have hrn : ‖r‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hr0]
  have hF4 : Summable (fun m : ℕ => (((m : ℝ) + 1) ^ 4 * r ^ m)) :=
    nr_summable_poly_mul_geom 4 hrn
  have hS0 : Summable (fun m : ℕ => r ^ m) :=
    summable_geometric_of_lt_one hr0 hr1
  have hF1 : Summable (fun m : ℕ => (((m : ℝ) + 1) * r ^ m)) := by
    simpa only [pow_one] using nr_summable_poly_mul_geom 1 hrn
  have hF2 : Summable (fun m : ℕ => (((m : ℝ) + 1) ^ 2 * r ^ m)) :=
    nr_summable_poly_mul_geom 2 hrn
  have hF3 : Summable (fun m : ℕ => (((m : ℝ) + 1) ^ 3 * r ^ m)) :=
    nr_summable_poly_mul_geom 3 hrn
  set S4 : ℝ := (∑' m : ℕ, (((m : ℝ) + 1) ^ 4 * r ^ m)) with hS4def
  set S3 : ℝ := (∑' m : ℕ, (((m : ℝ) + 1) ^ 3 * r ^ m)) with hS3def
  set S2 : ℝ := (∑' m : ℕ, (((m : ℝ) + 1) ^ 2 * r ^ m)) with hS2def
  set S1 : ℝ := (∑' m : ℕ, (((m : ℝ) + 1) * r ^ m)) with hS1def
  set S0 : ℝ := (∑' m : ℕ, r ^ m) with hS0def
  have hS1v : S1 = 1 / (1 - r) ^ 2 := by
    rw [hS1def]; exact nr_tsum_S1 hr0 hr1
  have hS2v : S2 = (1 + r) / (1 - r) ^ 3 := by
    rw [hS2def]; exact nr_tsum_S2 hr0 hr1
  have hS3v : S3 = (1 + 4 * r + r ^ 2) / (1 - r) ^ 4 := by
    rw [hS3def]; exact nr_tsum_S3 hr0 hr1
  have hS0v : S0 = (1 - r)⁻¹ := by
    rw [hS0def]; exact tsum_geometric_of_lt_one hr0 hr1
  have hsh := nr_shift_tsum (fun m : ℕ => (((m : ℝ) + 1) ^ 4 * r ^ m)) hF4
  simp only [Nat.cast_zero, zero_add, one_pow, pow_zero, mul_one] at hsh
  rw [← hS4def] at hsh
  have hexp : ∀ m : ℕ, ((((m + 1 : ℕ) : ℝ) + 1) ^ 4 * r ^ (m + 1))
      = r * ((((m : ℝ) + 1) ^ 4 * r ^ m))
        + (r * (4 * ((((m : ℝ) + 1) ^ 3 * r ^ m)))
          + (r * (6 * ((((m : ℝ) + 1) ^ 2 * r ^ m)))
            + (r * (4 * ((((m : ℝ) + 1) * r ^ m))) + r * r ^ m))) := by
    intro m
    push_cast
    ring
  have hval : (∑' m : ℕ, ((((m + 1 : ℕ) : ℝ) + 1) ^ 4 * r ^ (m + 1)))
      = r * S4 + ((r * (4 * S3)) + ((r * (6 * S2)) + ((r * (4 * S1)) + r * S0))) := by
    rw [tsum_congr hexp]
    rw [nr_tsum_add5 (hF4.mul_left r) ((hF3.mul_left 4).mul_left r)
      ((hF2.mul_left 6).mul_left r) ((hF1.mul_left 4).mul_left r)
      (hS0.mul_left r)]
    simp only [tsum_mul_left, ← hS4def, ← hS3def, ← hS2def, ← hS1def, ← hS0def]
  rw [hS1v, hS2v, hS3v, hS0v] at hval
  have hrne : (1 : ℝ) - r ≠ 0 := sub_ne_zero.mpr (ne_of_gt hr1)
  rw [hsh] at hval
  field_simp at hval ⊢
  nlinarith [hval]

/-! ## §2. `E2`, `E2*`, `η` majorants and weighted tail bounds. -/

/-- Closed-form `η1` majorant in `r = e^{-αq}`. -/
def nrEta1 (r : ℝ) : ℝ := (1 + r) / (1 - r) ^ 3

/-- Closed-form `η2` majorant in `r = e^{-αq}`. -/
def nrEta2 (r : ℝ) : ℝ :=
  (1 + 11 * r + 11 * r ^ 2 + r ^ 3) / (1 - r) ^ 5

/-- `r = e^{-αq}`. -/
noncomputable def nrR (τ : ℝ) (q : ℕ) : ℝ :=
  Real.exp (-(besselAlpha τ (q : ℝ)))

/-- Collar width `Bc = τ/q²`. -/
def nrB (τ : ℝ) (q : ℕ) : ℝ := τ / (q : ℝ) ^ 2

/-- `η1` at `(τ,q)`. -/
noncomputable def nrEta1of (τ : ℝ) (q : ℕ) : ℝ := nrEta1 (nrR τ q)

/-- `η2` at `(τ,q)`. -/
noncomputable def nrEta2of (τ : ℝ) (q : ℕ) : ℝ := nrEta2 (nrR τ q)

/-- `E2 = 2∑_{m} B(q+m)`. -/
noncomputable def nrE2 (τ : ℝ) (q : ℕ) : ℝ :=
  2 * ∑' m : ℕ, majorB τ (q + m)

/-- `E2*` closed form. -/
noncomputable def nrE2star (τ : ℝ) (q : ℕ) : ℝ :=
  2 * Real.sqrt (Real.pi / 8) * Real.exp (-(besselF τ (q : ℝ)))
    / (Real.sqrt (Real.sqrt ((q : ℝ) ^ 2 - τ ^ 2))
      * (1 - Real.exp (-(besselAlpha τ (q : ℝ)))))

/-- Restated `Ccal` (D2-term `32·η2·q²`, from the tree's `|T''| ≤ 16k⁴`). -/
noncomputable def nrCcal (τ : ℝ) (q : ℕ) : ℝ :=
  (2 / Real.pi) * (1 / (q : ℝ))
    * Real.sqrt (2 * (1 + (nrB τ q) / τ) * (1 + (4 / 27) * (nrEta1of τ q))
      * (32 * (nrEta2of τ q) * (q : ℝ) ^ 2 + 44
        + 2 * (12 + 16 / 27) * (nrEta1of τ q)))

/-- `majorB` is nonnegative. -/
lemma nr_majorB_nonneg (τ : ℝ) (k : ℕ) : 0 ≤ majorB τ k := by
  unfold majorB
  apply div_nonneg _ (Real.sqrt_nonneg _)
  exact mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le

/-- Summability of the `B`-tail. -/
lemma nr_summable_majorB {τ : ℝ} (hτ : 0 < τ) {q : ℕ} (hq1 : 1 ≤ q)
    (hlt : τ < (q : ℝ)) :
    Summable (fun m : ℕ => majorB τ (q + m)) := by
  have hα : 0 < besselAlpha τ (q : ℝ) := by
    unfold besselAlpha
    exact Real.arcosh_pos ((one_lt_div hτ).mpr hlt)
  have hr0 : (0 : ℝ) ≤ Real.exp (-(besselAlpha τ (q : ℝ))) :=
    (Real.exp_pos _).le
  have hr1 : Real.exp (-(besselAlpha τ (q : ℝ))) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith [hα]
  have hmaj : Summable
      (fun m : ℕ => majorB τ q * (Real.exp (-(besselAlpha τ (q : ℝ)))) ^ m) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  refine Summable.of_nonneg_of_le (fun m => nr_majorB_nonneg τ (q + m)) ?_ hmaj
  intro m
  have h := majorB_geom hτ hq1 hlt m
  have e : Real.exp (-(besselAlpha τ (q : ℝ)) * (m : ℝ))
      = (Real.exp (-(besselAlpha τ (q : ℝ)))) ^ m := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rwa [e] at h

/-- `E2 ≤ E2*`. -/
lemma nrE2_le_E2star {τ : ℝ} (hτ : 0 < τ) {q : ℕ} (hq1 : 1 ≤ q)
    (hlt : τ < (q : ℝ)) :
    nrE2 τ q ≤ nrE2star τ q := by
  have hα : 0 < besselAlpha τ (q : ℝ) := by
    unfold besselAlpha
    exact Real.arcosh_pos ((one_lt_div hτ).mpr hlt)
  have hr0 : (0 : ℝ) ≤ Real.exp (-(besselAlpha τ (q : ℝ))) :=
    (Real.exp_pos _).le
  have hr1 : Real.exp (-(besselAlpha τ (q : ℝ))) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith [hα]
  have hmaj : Summable
      (fun m : ℕ => majorB τ q * (Real.exp (-(besselAlpha τ (q : ℝ)))) ^ m) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hpt : ∀ m : ℕ, majorB τ (q + m)
      ≤ majorB τ q * (Real.exp (-(besselAlpha τ (q : ℝ)))) ^ m := by
    intro m
    have h := majorB_geom hτ hq1 hlt m
    have e : Real.exp (-(besselAlpha τ (q : ℝ)) * (m : ℝ))
        = (Real.exp (-(besselAlpha τ (q : ℝ)))) ^ m := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rwa [e] at h
  have hle := Summable.tsum_le_tsum hpt
    (nr_summable_majorB hτ hq1 hlt) hmaj
  rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1] at hle
  have hfin : nrE2star τ q
      = 2 * (majorB τ q * (1 - Real.exp (-(besselAlpha τ (q : ℝ))))⁻¹) := by
    unfold nrE2star majorB
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  calc nrE2 τ q = 2 * (∑' m : ℕ, majorB τ (q + m)) := rfl
    _ ≤ 2 * (majorB τ q * (1 - Real.exp (-(besselAlpha τ (q : ℝ))))⁻¹) :=
        mul_le_mul_of_nonneg_left hle (by norm_num)
    _ = nrE2star τ q := hfin.symm

/-- Weighted tail, first order: `∑(q+m)²B(q+m) ≤ q²·η1·∑B`. -/
lemma nr_weighted1 {τ : ℝ} (hτ : 0 < τ) {q : ℕ} (hq2 : 2 ≤ q)
    (hlt : τ < (q : ℝ)) :
    (∑' m : ℕ, ((((q : ℝ) + (m : ℝ)) ^ 2 * majorB τ (q + m))))
      ≤ (q : ℝ) ^ 2 * nrEta1 (nrR τ q)
        * (∑' m : ℕ, majorB τ (q + m)) := by
  have hq1 : (1 : ℕ) ≤ q := by omega
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
  have hα : 0 < besselAlpha τ (q : ℝ) := by
    unfold besselAlpha
    exact Real.arcosh_pos ((one_lt_div hτ).mpr hlt)
  have hr0 : (0 : ℝ) ≤ nrR τ q := by
    unfold nrR
    exact (Real.exp_pos _).le
  have hr1 : nrR τ q < 1 := by
    unfold nrR
    rw [Real.exp_lt_one_iff]
    linarith [hα]
  have hrn : ‖nrR τ q‖ < 1 := by
    rwa [Real.norm_eq_abs, abs_of_nonneg hr0]
  have hS2 := nr_tsum_S2 hr0 hr1
  have hpt : ∀ m : ℕ, ((((q : ℝ) + (m : ℝ)) ^ 2 * majorB τ (q + m)))
      ≤ (q : ℝ) ^ 2 * majorB τ q * ((((m : ℝ) + 1) ^ 2 * (nrR τ q) ^ m)) := by
    intro m
    have hqm : (q : ℝ) + (m : ℝ) ≤ (q : ℝ) * ((m : ℝ) + 1) := by
      have h1 : (m : ℝ) ≤ (q : ℝ) * (m : ℝ) := by
        calc (m : ℝ) = 1 * (m : ℝ) := (one_mul _).symm
          _ ≤ (q : ℝ) * (m : ℝ) :=
            mul_le_mul_of_nonneg_right hqR (Nat.cast_nonneg m)
      have h2 : (q : ℝ) * ((m : ℝ) + 1) = (q : ℝ) * (m : ℝ) + (q : ℝ) := by
        ring
      linarith [h1, h2]
    have hsq : (((q : ℝ) + (m : ℝ)) ^ 2) ≤ ((q : ℝ) * ((m : ℝ) + 1)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hqm 2
    have hB := majorB_geom hτ hq1 hlt m
    have er : Real.exp (-(besselAlpha τ (q : ℝ)) * (m : ℝ)) = (nrR τ q) ^ m := by
      unfold nrR
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [er] at hB
    calc ((((q : ℝ) + (m : ℝ)) ^ 2 * majorB τ (q + m)))
        ≤ (((q : ℝ) * ((m : ℝ) + 1)) ^ 2 * (majorB τ q * (nrR τ q) ^ m)) :=
          mul_le_mul hsq hB (nr_majorB_nonneg τ (q + m)) (by positivity)
      _ = (q : ℝ) ^ 2 * majorB τ q * ((((m : ℝ) + 1) ^ 2 * (nrR τ q) ^ m)) := by
          ring
  have hC := (nr_summable_poly_mul_geom 2 hrn).mul_left
    ((q : ℝ) ^ 2 * majorB τ q)
  have hW : Summable
      (fun m : ℕ => ((((q : ℝ) + (m : ℝ)) ^ 2 * majorB τ (q + m)))) := by
    have hbas : ∀ m : ℕ, (0:ℝ) ≤ ((q:ℝ) + (m:ℝ)) :=
      fun m => add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    exact Summable.of_nonneg_of_le
      (fun m => mul_nonneg (pow_nonneg (hbas m) 2)
        (nr_majorB_nonneg τ (q + m))) hpt hC
  have hle := Summable.tsum_le_tsum hpt hW hC
  have hval : (∑' m : ℕ, (q : ℝ) ^ 2 * majorB τ q
        * ((((m : ℝ) + 1) ^ 2 * (nrR τ q) ^ m)))
      = (q : ℝ) ^ 2 * majorB τ q * ((1 + nrR τ q) / (1 - nrR τ q) ^ 3) := by
    rw [tsum_mul_left, hS2]
  rw [hval] at hle
  have hBqS : majorB τ q ≤ ∑' m : ℕ, majorB τ (q + m) := by
    have h := (nr_summable_majorB hτ hq1 hlt).sum_add_tsum_nat_add 1
    simp only [Finset.range_one, Finset.sum_singleton] at h
    have hnn : 0 ≤ ∑' m : ℕ, majorB τ (q + (m + 1)) :=
      tsum_nonneg (fun m => nr_majorB_nonneg τ (q + (m + 1)))
    have e : q + 0 = q := add_zero q
    rw [e] at h
    linarith [h, hnn]
  have heta : nrEta1 (nrR τ q) = (1 + nrR τ q) / (1 - nrR τ q) ^ 3 := rfl
  rw [heta] at ⊢
  have h1r : (0 : ℝ) ≤ 1 - nrR τ q := by linarith [hr1]
  have hqnn : (0:ℝ) ≤ (q:ℝ) := Nat.cast_nonneg _
  have hnn2 : (0 : ℝ) ≤ (q : ℝ) ^ 2 * ((1 + nrR τ q) / (1 - nrR τ q) ^ 3) :=
    mul_nonneg (pow_nonneg hqnn 2) (div_nonneg (by linarith [hr0]) (pow_nonneg h1r 3))
  calc (∑' m : ℕ, ((((q : ℝ) + (m : ℝ)) ^ 2 * majorB τ (q + m))))
      ≤ (q : ℝ) ^ 2 * majorB τ q * ((1 + nrR τ q) / (1 - nrR τ q) ^ 3) := hle
    _ = ((q : ℝ) ^ 2 * ((1 + nrR τ q) / (1 - nrR τ q) ^ 3)) * majorB τ q := by
        ring
    _ ≤ ((q : ℝ) ^ 2 * ((1 + nrR τ q) / (1 - nrR τ q) ^ 3))
        * (∑' m : ℕ, majorB τ (q + m)) :=
        mul_le_mul_of_nonneg_left hBqS hnn2
    _ = (q : ℝ) ^ 2 * ((1 + nrR τ q) / (1 - nrR τ q) ^ 3)
        * (∑' m : ℕ, majorB τ (q + m)) := by
        ring

/-- Weighted tail, second order: `∑(q+m)⁴B(q+m) ≤ q⁴·η2·∑B`. -/
lemma nr_weighted2 {τ : ℝ} (hτ : 0 < τ) {q : ℕ} (hq2 : 2 ≤ q)
    (hlt : τ < (q : ℝ)) :
    (∑' m : ℕ, ((((q : ℝ) + (m : ℝ)) ^ 4 * majorB τ (q + m))))
      ≤ (q : ℝ) ^ 4 * nrEta2 (nrR τ q)
        * (∑' m : ℕ, majorB τ (q + m)) := by
  have hq1 : (1 : ℕ) ≤ q := by omega
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
  have hα : 0 < besselAlpha τ (q : ℝ) := by
    unfold besselAlpha
    exact Real.arcosh_pos ((one_lt_div hτ).mpr hlt)
  have hr0 : (0 : ℝ) ≤ nrR τ q := by
    unfold nrR
    exact (Real.exp_pos _).le
  have hr1 : nrR τ q < 1 := by
    unfold nrR
    rw [Real.exp_lt_one_iff]
    linarith [hα]
  have hrn : ‖nrR τ q‖ < 1 := by
    rwa [Real.norm_eq_abs, abs_of_nonneg hr0]
  have hS4 := nr_tsum_S4 hr0 hr1
  have hpt : ∀ m : ℕ, ((((q : ℝ) + (m : ℝ)) ^ 4 * majorB τ (q + m)))
      ≤ (q : ℝ) ^ 4 * majorB τ q * ((((m : ℝ) + 1) ^ 4 * (nrR τ q) ^ m)) := by
    intro m
    have hqm : (q : ℝ) + (m : ℝ) ≤ (q : ℝ) * ((m : ℝ) + 1) := by
      have h1 : (m : ℝ) ≤ (q : ℝ) * (m : ℝ) := by
        calc (m : ℝ) = 1 * (m : ℝ) := (one_mul _).symm
          _ ≤ (q : ℝ) * (m : ℝ) :=
            mul_le_mul_of_nonneg_right hqR (Nat.cast_nonneg m)
      have h2 : (q : ℝ) * ((m : ℝ) + 1) = (q : ℝ) * (m : ℝ) + (q : ℝ) := by
        ring
      linarith [h1, h2]
    have hsq : (((q : ℝ) + (m : ℝ)) ^ 4) ≤ ((q : ℝ) * ((m : ℝ) + 1)) ^ 4 :=
      pow_le_pow_left₀ (by positivity) hqm 4
    have hB := majorB_geom hτ hq1 hlt m
    have er : Real.exp (-(besselAlpha τ (q : ℝ)) * (m : ℝ)) = (nrR τ q) ^ m := by
      unfold nrR
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [er] at hB
    calc ((((q : ℝ) + (m : ℝ)) ^ 4 * majorB τ (q + m)))
        ≤ (((q : ℝ) * ((m : ℝ) + 1)) ^ 4 * (majorB τ q * (nrR τ q) ^ m)) :=
          mul_le_mul hsq hB (nr_majorB_nonneg τ (q + m)) (by positivity)
      _ = (q : ℝ) ^ 4 * majorB τ q * ((((m : ℝ) + 1) ^ 4 * (nrR τ q) ^ m)) := by
          ring
  have hC := (nr_summable_poly_mul_geom 4 hrn).mul_left
    ((q : ℝ) ^ 4 * majorB τ q)
  have hW : Summable
      (fun m : ℕ => ((((q : ℝ) + (m : ℝ)) ^ 4 * majorB τ (q + m)))) := by
    have hbas : ∀ m : ℕ, (0:ℝ) ≤ ((q:ℝ) + (m:ℝ)) :=
      fun m => add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    exact Summable.of_nonneg_of_le
      (fun m => mul_nonneg (pow_nonneg (hbas m) 4)
        (nr_majorB_nonneg τ (q + m))) hpt hC
  have hle := Summable.tsum_le_tsum hpt hW hC
  have hval : (∑' m : ℕ, (q : ℝ) ^ 4 * majorB τ q
        * ((((m : ℝ) + 1) ^ 4 * (nrR τ q) ^ m)))
      = (q : ℝ) ^ 4 * majorB τ q
        * ((1 + 11 * nrR τ q + 11 * (nrR τ q) ^ 2 + (nrR τ q) ^ 3)
          / (1 - nrR τ q) ^ 5) := by
    rw [tsum_mul_left, hS4]
  rw [hval] at hle
  have hBqS : majorB τ q ≤ ∑' m : ℕ, majorB τ (q + m) := by
    have h := (nr_summable_majorB hτ hq1 hlt).sum_add_tsum_nat_add 1
    simp only [Finset.range_one, Finset.sum_singleton] at h
    have hnn : 0 ≤ ∑' m : ℕ, majorB τ (q + (m + 1)) :=
      tsum_nonneg (fun m => nr_majorB_nonneg τ (q + (m + 1)))
    have e : q + 0 = q := add_zero q
    rw [e] at h
    linarith [h, hnn]
  have heta : nrEta2 (nrR τ q)
      = (1 + 11 * nrR τ q + 11 * (nrR τ q) ^ 2 + (nrR τ q) ^ 3)
        / (1 - nrR τ q) ^ 5 := rfl
  rw [heta] at ⊢
  have h1r : (0 : ℝ) ≤ 1 - nrR τ q := by linarith [hr1]
  have hnum : (0 : ℝ) ≤ 1 + 11 * nrR τ q + 11 * (nrR τ q) ^ 2 + (nrR τ q) ^ 3 := by
    have hr0' : (0 : ℝ) ≤ nrR τ q := hr0
    positivity
  have hqnn : (0:ℝ) ≤ (q:ℝ) := Nat.cast_nonneg _
  have hnn2 : (0 : ℝ) ≤ (q : ℝ) ^ 4
      * ((1 + 11 * nrR τ q + 11 * (nrR τ q) ^ 2 + (nrR τ q) ^ 3)
        / (1 - nrR τ q) ^ 5) :=
    mul_nonneg (pow_nonneg hqnn 4) (div_nonneg hnum (pow_nonneg h1r 5))
  calc (∑' m : ℕ, ((((q : ℝ) + (m : ℝ)) ^ 4 * majorB τ (q + m))))
      ≤ (q : ℝ) ^ 4 * majorB τ q
        * ((1 + 11 * nrR τ q + 11 * (nrR τ q) ^ 2 + (nrR τ q) ^ 3)
          / (1 - nrR τ q) ^ 5) := hle
    _ = ((q : ℝ) ^ 4
          * ((1 + 11 * nrR τ q + 11 * (nrR τ q) ^ 2 + (nrR τ q) ^ 3)
            / (1 - nrR τ q) ^ 5)) * majorB τ q := by
        ring
    _ ≤ ((q : ℝ) ^ 4
          * ((1 + 11 * nrR τ q + 11 * (nrR τ q) ^ 2 + (nrR τ q) ^ 3)
            / (1 - nrR τ q) ^ 5))
        * (∑' m : ℕ, majorB τ (q + m)) :=
        mul_le_mul_of_nonneg_left hBqS hnn2
    _ = (q : ℝ) ^ 4
        * ((1 + 11 * nrR τ q + 11 * (nrR τ q) ^ 2 + (nrR τ q) ^ 3)
          / (1 - nrR τ q) ^ 5)
        * (∑' m : ℕ, majorB τ (q + m)) := by
        ring
/-! ## §3. Chebyshev bundle and L4 inequalities. -/

/-- Remainder term (level 0). -/
noncomputable def nrTerm0 (a : ℕ → ℂ) (τ : ℝ) (q : ℕ) (m : ℕ) (μ : ℝ) : ℂ :=
  a m * (Polynomial.Chebyshev.T ℂ (((q + m : ℕ) : ℤ))).eval (((μ / τ : ℝ)) : ℂ)

/-- Remainder term, first derivative shape. -/
noncomputable def nrTerm1 (a : ℕ → ℂ) (τ : ℝ) (q : ℕ) (m : ℕ) (μ : ℝ) : ℂ :=
  a m * ((Polynomial.Chebyshev.T ℂ (((q + m : ℕ) : ℤ))).derivative.eval
    (((μ / τ : ℝ)) : ℂ) / (((τ : ℝ)) : ℂ))

/-- Remainder term, second derivative shape. -/
noncomputable def nrTerm2 (a : ℕ → ℂ) (τ : ℝ) (q : ℕ) (m : ℕ) (μ : ℝ) : ℂ :=
  a m * ((Polynomial.Chebyshev.T ℂ (((q + m : ℕ) : ℤ))).derivative.derivative.eval
    (((μ / τ : ℝ)) : ℂ) / ((((τ : ℝ)) : ℂ) ^ 2))

/-- Hypothesis bundle for the Chebyshev truncation (D1):
Jacobi–Anger remainder series plus its two termwise differentiations,
with coefficient bounds; only the series representations are external. -/
structure nrCheb where
  q : ℕ
  τ : ℝ
  Ψ : ℝ → ℂ
  a : ℕ → ℂ
  Q : Polynomial ℂ
  χ : ℝ → ℝ
  hq2 : 2 ≤ q
  hτ1 : 1 ≤ τ
  hτq : τ < (q : ℝ)
  hΨ : ContDiff ℝ 2 Ψ
  hA : ∀ m : ℕ, ‖a m‖ ≤ 2 * majorB τ (q + m)
  hSer0 : ∀ μ : ℝ, |μ| ≤ τ → HasSum (fun m : ℕ => nrTerm0 a τ q m μ) (Ψ μ)
  hSer1 : ∀ μ : ℝ, |μ| ≤ τ →
    HasSum (fun m : ℕ => nrTerm1 a τ q m μ) (deriv Ψ μ)
  hSer2 : ∀ μ : ℝ, |μ| ≤ τ →
    HasSum (fun m : ℕ => nrTerm2 a τ q m μ) (deriv (deriv Ψ) μ)
  hQ : Q.natDegree < q
  hΨeq : ∀ μ : ℝ, |μ| ≤ τ →
    Ψ μ = Complex.exp (-((μ : ℂ)) * Complex.I) - Q.eval ((μ : ℂ))
  hχ : ContDiff ℝ 2 χ
  hχ1 : ∀ μ : ℝ, |μ| ≤ τ → χ μ = 1
  hχb : ∀ μ : ℝ, |χ μ| ≤ 1
  hχd1 : ∀ μ : ℝ, ‖deriv χ μ‖ ≤ 4 / nrB τ q
  hχd2 : ∀ μ : ℝ, ‖deriv (deriv χ) μ‖ ≤ 4 / (nrB τ q) ^ 2

/-- `|T_n| ≤ 1` on `[-1,1]`. -/
lemma nr_abs_chebT_le_one (n : ℤ) {u : ℝ} (hu : u ∈ Set.Icc (-1 : ℝ) 1) :
    |(Polynomial.Chebyshev.T ℝ n).eval u| ≤ 1 := by
  have hcos : Real.cos (Real.arccos u) = u :=
    Real.cos_arccos hu.1 hu.2
  rw [← hcos, Polynomial.Chebyshev.T_real_cos]
  exact Real.abs_cos_le_one _

/-- `‖T_n‖ ≤ 1` (complex polynomial at a real point of `[-1,1]`). -/
lemma nr_norm_chebT_le_one (n : ℤ) {u : ℝ} (hu : u ∈ Set.Icc (-1 : ℝ) 1) :
    ‖(Polynomial.Chebyshev.T ℂ n).eval ((u : ℝ) : ℂ)‖ ≤ 1 := by
  rw [← Polynomial.Chebyshev.complex_ofReal_eval_T, Complex.norm_real]
  exact nr_abs_chebT_le_one n hu

/-- `μ/τ ∈ [-1,1]` for `|μ| ≤ τ`, `τ > 0`. -/
lemma nr_div_mem_Icc {τ μ : ℝ} (hτ : 0 < τ) (hμ : |μ| ≤ τ) :
    μ / τ ∈ Set.Icc (-1 : ℝ) 1 := by
  have h1 : |μ / τ| ≤ 1 := by
    rw [abs_div, abs_of_pos hτ]
    exact (div_le_one hτ).mpr hμ
  exact Set.mem_Icc.mpr ⟨(abs_le.mp h1).1, (abs_le.mp h1).2⟩
/-- Term-0 bound. -/
lemma nr_term0_le (C : nrCheb) {μ : ℝ} (hμ : |μ| ≤ C.τ) (m : ℕ) :
    ‖nrTerm0 C.a C.τ C.q m μ‖ ≤ 2 * majorB C.τ (C.q + m) := by
  have hτ : 0 < C.τ := by linarith [C.hτ1]
  have hu := nr_div_mem_Icc hτ hμ
  have hT := nr_norm_chebT_le_one (((C.q + m : ℕ)) : ℤ) hu
  have hA := C.hA m
  have hBnn : (0 : ℝ) ≤ 2 * majorB C.τ (C.q + m) :=
    mul_nonneg (by norm_num) (nr_majorB_nonneg _ _)
  unfold nrTerm0
  rw [norm_mul]
  exact (mul_le_mul hA hT (norm_nonneg _) hBnn).trans_eq (mul_one _)

/-- Term-1 bound, in weighted form. -/
lemma nr_term1_le (C : nrCheb) {μ : ℝ} (hμ : |μ| ≤ C.τ) (m : ℕ) :
    ‖nrTerm1 C.a C.τ C.q m μ‖
      ≤ (2 / C.τ) * ((((C.q : ℝ) + (m : ℝ)) ^ 2 * majorB C.τ (C.q + m))) := by
  have hτ : 0 < C.τ := by linarith [C.hτ1]
  have hu := nr_div_mem_Icc hτ hμ
  have hT := norm_deriv_chebyshevT_complex_le (((C.q + m : ℕ)) : ℤ) hu
  rw [Int.natAbs_natCast] at hT
  have hA := C.hA m
  have hτC : ‖((((C.τ : ℝ))) : ℂ)‖ = C.τ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ]
  have hkm : ((((C.q + m : ℕ)) : ℝ)) = (C.q : ℝ) + (m : ℝ) := by
    push_cast
    ring
  have hBnn : (0 : ℝ) ≤ 2 * majorB C.τ (C.q + m) :=
    mul_nonneg (by norm_num) (nr_majorB_nonneg _ _)
  unfold nrTerm1
  rw [norm_mul, norm_div, hτC]
  have hT2 : ‖(Polynomial.Chebyshev.T ℂ (((C.q + m : ℕ)) : ℤ)).derivative.eval
      (((μ / C.τ : ℝ)) : ℂ)‖ / C.τ ≤ (((C.q : ℝ) + (m : ℝ)) ^ 2) / C.τ := by
    have hle : ‖(Polynomial.Chebyshev.T ℂ (((C.q + m : ℕ)) : ℤ)).derivative.eval
        (((μ / C.τ : ℝ)) : ℂ)‖ ≤ (((C.q : ℝ) + (m : ℝ)) ^ 2) := by
      rw [← hkm]
      exact hT
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hle (inv_nonneg.mpr hτ.le)
  calc ‖C.a m‖ * (‖(Polynomial.Chebyshev.T ℂ (((C.q + m : ℕ)) : ℤ)).derivative.eval
        (((μ / C.τ : ℝ)) : ℂ)‖ / C.τ)
      ≤ (2 * majorB C.τ (C.q + m)) * ((((C.q : ℝ) + (m : ℝ)) ^ 2) / C.τ) :=
        mul_le_mul hA hT2 (div_nonneg (norm_nonneg _) hτ.le) hBnn
    _ = (2 / C.τ) * ((((C.q : ℝ) + (m : ℝ)) ^ 2 * majorB C.τ (C.q + m))) := by
        ring

/-- Term-2 bound, in weighted form (tree's `16k⁴`). -/
lemma nr_term2_le (C : nrCheb) {μ : ℝ} (hμ : |μ| ≤ C.τ) (m : ℕ) :
    ‖nrTerm2 C.a C.τ C.q m μ‖
      ≤ (32 / C.τ ^ 2)
        * ((((C.q : ℝ) + (m : ℝ)) ^ 4 * majorB C.τ (C.q + m))) := by
  have hτ : 0 < C.τ := by linarith [C.hτ1]
  have hu := nr_div_mem_Icc hτ hμ
  have hT := norm_deriv2_chebyshevT_complex_le (((C.q + m : ℕ)) : ℤ) hu
  rw [Int.natAbs_natCast] at hT
  have hA := C.hA m
  have hτC : ‖((((C.τ : ℝ))) : ℂ) ^ 2‖ = C.τ ^ 2 := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ]
  have hkm : ((((C.q + m : ℕ)) : ℝ)) = (C.q : ℝ) + (m : ℝ) := by
    push_cast
    ring
  have hBnn : (0 : ℝ) ≤ 2 * majorB C.τ (C.q + m) :=
    mul_nonneg (by norm_num) (nr_majorB_nonneg _ _)
  unfold nrTerm2
  rw [norm_mul, norm_div, hτC]
  have hT16 : ‖(Polynomial.Chebyshev.T ℂ (((C.q + m : ℕ)) : ℤ)).derivative.derivative.eval
      (((μ / C.τ : ℝ)) : ℂ)‖ ≤ 16 * (((C.q : ℝ) + (m : ℝ)) ^ 4) := by
    have h1 := hT
    rwa [hkm] at h1
  have hT2 : ‖(Polynomial.Chebyshev.T ℂ (((C.q + m : ℕ)) : ℤ)).derivative.derivative.eval
      (((μ / C.τ : ℝ)) : ℂ)‖ / C.τ ^ 2
      ≤ (16 * (((C.q : ℝ) + (m : ℝ)) ^ 4)) / C.τ ^ 2 := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hT16
      (inv_nonneg.mpr (pow_nonneg hτ.le 2))
  calc ‖C.a m‖ * (‖(Polynomial.Chebyshev.T ℂ (((C.q + m : ℕ)) : ℤ)).derivative.derivative.eval
        (((μ / C.τ : ℝ)) : ℂ)‖ / C.τ ^ 2)
      ≤ (2 * majorB C.τ (C.q + m)) * ((16 * (((C.q : ℝ) + (m : ℝ)) ^ 4)) / C.τ ^ 2) :=
        mul_le_mul hA hT2
          (div_nonneg (norm_nonneg _) (pow_nonneg hτ.le 2)) hBnn
    _ = (32 / C.τ ^ 2)
        * ((((C.q : ℝ) + (m : ℝ)) ^ 4 * majorB C.τ (C.q + m))) := by
        ring
/-- `0 ≤ r = e^{-α}`. -/
lemma nrR_nonneg (τ : ℝ) (q : ℕ) : 0 ≤ nrR τ q := by
  unfold nrR
  exact (Real.exp_pos _).le

/-- `r < 1` from `α > 0`. -/
lemma nrR_lt_one {τ : ℝ} {q : ℕ} (hα : 0 < besselAlpha τ (q : ℝ)) :
    nrR τ q < 1 := by
  unfold nrR
  rw [Real.exp_lt_one_iff]
  linarith [hα]

/-- `αq > 0`. -/
lemma nr_alpha_pos {τ : ℝ} (hτ : 0 < τ) {q : ℕ} (hlt : τ < (q : ℝ)) :
    0 < besselAlpha τ (q : ℝ) := by
  unfold besselAlpha
  exact Real.arcosh_pos ((one_lt_div hτ).mpr hlt)

/-- `η1 ≥ 0`. -/
lemma nrEta1_nonneg {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) : 0 ≤ nrEta1 r := by
  unfold nrEta1
  exact div_nonneg (by linarith) (pow_nonneg (by linarith) 3)

/-- `η2 ≥ 0`. -/
lemma nrEta2_nonneg {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) : 0 ≤ nrEta2 r := by
  unfold nrEta2
  apply div_nonneg _ (pow_nonneg (by linarith) 5)
  have h1 : (0 : ℝ) ≤ 11 * r := mul_nonneg (by norm_num) hr0
  have h2 : (0 : ℝ) ≤ 11 * r ^ 2 :=
    mul_nonneg (by norm_num) (pow_nonneg hr0 2)
  have h3 : (0 : ℝ) ≤ r ^ 3 := pow_nonneg hr0 3
  linarith [h1, h2, h3]

/-- General weighted summability. -/
lemma nr_summable_weighted {τ : ℝ} (hτ : 0 < τ) {q : ℕ} (hq2 : 2 ≤ q)
    (hlt : τ < (q : ℝ)) (j : ℕ) :
    Summable (fun m : ℕ => ((((q : ℝ) + (m : ℝ)) ^ (2 * j) * majorB τ (q + m)))) := by
  have hq1 : (1 : ℕ) ≤ q := by omega
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
  have hα := nr_alpha_pos hτ hlt
  have hr0 := nrR_nonneg τ q
  have hr1 := nrR_lt_one hα
  have hrn : ‖nrR τ q‖ < 1 := by
    rwa [Real.norm_eq_abs, abs_of_nonneg hr0]
  have hC := (nr_summable_poly_mul_geom (2 * j) hrn).mul_left
    ((q : ℝ) ^ (2 * j) * majorB τ q)
  have hbas : ∀ m : ℕ, (0:ℝ) ≤ ((q:ℝ) + (m:ℝ)) :=
    fun m => add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hpt : ∀ m : ℕ, ((((q : ℝ) + (m : ℝ)) ^ (2 * j) * majorB τ (q + m)))
      ≤ ((q : ℝ) ^ (2 * j) * majorB τ q)
        * ((((m : ℝ) + 1) ^ (2 * j) * (nrR τ q) ^ m)) := by
    intro m
    have hqm : (q : ℝ) + (m : ℝ) ≤ (q : ℝ) * ((m : ℝ) + 1) := by
      have h1 : (m : ℝ) ≤ (q : ℝ) * (m : ℝ) := by
        calc (m : ℝ) = 1 * (m : ℝ) := (one_mul _).symm
          _ ≤ (q : ℝ) * (m : ℝ) :=
            mul_le_mul_of_nonneg_right hqR (Nat.cast_nonneg m)
      have h2 : (q : ℝ) * ((m : ℝ) + 1) = (q : ℝ) * (m : ℝ) + (q : ℝ) := by
        ring
      linarith [h1, h2]
    have hsq : (((q : ℝ) + (m : ℝ)) ^ (2 * j))
        ≤ ((q : ℝ) * ((m : ℝ) + 1)) ^ (2 * j) :=
      pow_le_pow_left₀ (hbas m) hqm (2 * j)
    have hB := majorB_geom hτ hq1 hlt m
    have er : Real.exp (-(besselAlpha τ (q : ℝ)) * (m : ℝ)) = (nrR τ q) ^ m := by
      unfold nrR
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [er] at hB
    have hmp : ((q : ℝ) * ((m : ℝ) + 1)) ^ (2 * j)
        = (q : ℝ) ^ (2 * j) * (((m : ℝ) + 1) ^ (2 * j)) := mul_pow _ _ _
    have hnnB : (0 : ℝ) ≤ ((q : ℝ) * ((m : ℝ) + 1)) ^ (2 * j) :=
      pow_nonneg (mul_nonneg (Nat.cast_nonneg _)
        (add_nonneg (Nat.cast_nonneg _) (by norm_num))) (2 * j)
    calc ((((q : ℝ) + (m : ℝ)) ^ (2 * j) * majorB τ (q + m)))
        ≤ (((q : ℝ) * ((m : ℝ) + 1)) ^ (2 * j) * (majorB τ q * (nrR τ q) ^ m)) :=
          mul_le_mul hsq hB (nr_majorB_nonneg τ (q + m)) hnnB
      _ = ((q : ℝ) ^ (2 * j) * majorB τ q)
          * ((((m : ℝ) + 1) ^ (2 * j) * (nrR τ q) ^ m)) := by
          rw [hmp]
          ring
  exact Summable.of_nonneg_of_le
    (fun m => mul_nonneg (pow_nonneg (hbas m) (2 * j))
      (nr_majorB_nonneg τ (q + m))) hpt hC

/-- `0 ≤ E2`. -/
lemma nrE2_nonneg (τ : ℝ) (q : ℕ) : 0 ≤ nrE2 τ q := by
  unfold nrE2
  exact mul_nonneg (by norm_num)
    (tsum_nonneg (fun m => nr_majorB_nonneg τ (q + m)))

/-- `majorB` is positive for `τ < k`. -/
lemma nr_majorB_pos {τ : ℝ} (hτ : 0 < τ) {k : ℕ} (hlt : τ < (k : ℝ)) :
    0 < majorB τ k := by
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
  have hD : (0 : ℝ) < (k : ℝ) ^ 2 - τ ^ 2 := by
    have h1 : (0 : ℝ) < (k : ℝ) - τ := by linarith [hlt]
    have h2 : (0 : ℝ) < (k : ℝ) + τ := by linarith [hτ, hk0]
    have e : (k : ℝ) ^ 2 - τ ^ 2 = ((k : ℝ) - τ) * ((k : ℝ) + τ) := by ring
    rw [e]
    exact mul_pos h1 h2
  unfold majorB
  apply div_pos _ (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hD))
  exact mul_pos (Real.sqrt_pos.mpr (by positivity)) (Real.exp_pos _)

/-- `B(q) ≤ ∑B`. -/
lemma nr_majorB_le_tsum {τ : ℝ} (hτ : 0 < τ) {q : ℕ} (hq1 : 1 ≤ q)
    (hlt : τ < (q : ℝ)) :
    majorB τ q ≤ ∑' m : ℕ, majorB τ (q + m) := by
  have h := (nr_summable_majorB hτ hq1 hlt).sum_add_tsum_nat_add 1
  simp only [Finset.range_one, Finset.sum_singleton] at h
  have hnn : 0 ≤ ∑' m : ℕ, majorB τ (q + (m + 1)) :=
    tsum_nonneg (fun m => nr_majorB_nonneg τ (q + (m + 1)))
  have e : q + 0 = q := add_zero q
  rw [e] at h
  linarith [h, hnn]

/-- `0 < E2`. -/
lemma nrE2_pos {τ : ℝ} (hτ : 0 < τ) {q : ℕ} (hq1 : 1 ≤ q)
    (hlt : τ < (q : ℝ)) :
    0 < nrE2 τ q := by
  have hBq := nr_majorB_pos hτ hlt (k := q)
  have hle := nr_majorB_le_tsum hτ hq1 hlt
  have hS : 0 < ∑' m : ℕ, majorB τ (q + m) := lt_of_lt_of_le hBq hle
  unfold nrE2
  exact mul_pos (by norm_num) hS

/-- `D1` bound value. -/
noncomputable def nrD1of (C : nrCheb) : ℝ :=
  nrEta1of C.τ C.q * (C.q : ℝ) ^ 2 * nrE2 C.τ C.q / C.τ

/-- `D2` bound value (restated `16`-form). -/
noncomputable def nrD2of (C : nrCheb) : ℝ :=
  16 * nrEta2of C.τ C.q * (C.q : ℝ) ^ 4 * nrE2 C.τ C.q / C.τ ^ 2

/-- L4 sup bound: `‖Ψ‖ ≤ E2`. -/
lemma nr_sup_le (C : nrCheb) {μ : ℝ} (hμ : |μ| ≤ C.τ) :
    ‖C.Ψ μ‖ ≤ nrE2 C.τ C.q := by
  have hτ : 0 < C.τ := by linarith [C.hτ1]
  have hq1 : 1 ≤ C.q := by have h := C.hq2; omega
  have hS := C.hSer0 μ hμ
  rw [← hS.tsum_eq]
  have hCsum : Summable (fun m : ℕ => 2 * majorB C.τ (C.q + m)) :=
    (nr_summable_majorB hτ hq1 C.hτq).mul_left 2
  have hnorm : Summable (fun m : ℕ => ‖nrTerm0 C.a C.τ C.q m μ‖) :=
    Summable.of_nonneg_of_le (fun m => norm_nonneg _)
      (fun m => nr_term0_le C hμ m) hCsum
  calc ‖∑' m : ℕ, nrTerm0 C.a C.τ C.q m μ‖
      ≤ ∑' m : ℕ, ‖nrTerm0 C.a C.τ C.q m μ‖ :=
        norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' m : ℕ, 2 * majorB C.τ (C.q + m) :=
        Summable.tsum_le_tsum (fun m => nr_term0_le C hμ m) hnorm hCsum
    _ = nrE2 C.τ C.q := by
        unfold nrE2
        rw [tsum_mul_left]

/-- L4 first-derivative bound. -/
lemma nr_D1_le (C : nrCheb) {μ : ℝ} (hμ : |μ| ≤ C.τ) :
    ‖deriv C.Ψ μ‖ ≤ nrD1of C := by
  have hτ : 0 < C.τ := by linarith [C.hτ1]
  have hq2 : 2 ≤ C.q := C.hq2
  have hS := C.hSer1 μ hμ
  rw [← hS.tsum_eq]
  have hW1 : Summable
      (fun m : ℕ => ((((C.q : ℝ) + (m : ℝ)) ^ 2 * majorB C.τ (C.q + m)))) := by
    have h := nr_summable_weighted hτ hq2 C.hτq 1
    simpa using h
  have hCsum : Summable (fun m : ℕ => (2 / C.τ)
      * ((((C.q : ℝ) + (m : ℝ)) ^ 2 * majorB C.τ (C.q + m)))) :=
    hW1.mul_left (2 / C.τ)
  have hnorm : Summable (fun m : ℕ => ‖nrTerm1 C.a C.τ C.q m μ‖) :=
    Summable.of_nonneg_of_le (fun m => norm_nonneg _)
      (fun m => nr_term1_le C hμ m) hCsum
  have hW := nr_weighted1 hτ hq2 C.hτq
  have hnnc : (0 : ℝ) ≤ 2 / C.τ := div_nonneg (by norm_num) hτ.le
  calc ‖∑' m : ℕ, nrTerm1 C.a C.τ C.q m μ‖
      ≤ ∑' m : ℕ, ‖nrTerm1 C.a C.τ C.q m μ‖ :=
        norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' m : ℕ, (2 / C.τ)
          * ((((C.q : ℝ) + (m : ℝ)) ^ 2 * majorB C.τ (C.q + m))) :=
        Summable.tsum_le_tsum (fun m => nr_term1_le C hμ m) hnorm hCsum
    _ = (2 / C.τ) * (∑' m : ℕ, ((((C.q : ℝ) + (m : ℝ)) ^ 2
          * majorB C.τ (C.q + m)))) := tsum_mul_left
    _ ≤ (2 / C.τ) * ((C.q : ℝ) ^ 2 * nrEta1 (nrR C.τ C.q)
          * (∑' m : ℕ, majorB C.τ (C.q + m))) :=
        mul_le_mul_of_nonneg_left hW hnnc
    _ = nrD1of C := by
        unfold nrD1of nrEta1of nrE2
        ring

/-- L4 second-derivative bound (restated `16`-form). -/
lemma nr_D2_le (C : nrCheb) {μ : ℝ} (hμ : |μ| ≤ C.τ) :
    ‖deriv (deriv C.Ψ) μ‖ ≤ nrD2of C := by
  have hτ : 0 < C.τ := by linarith [C.hτ1]
  have hq2 : 2 ≤ C.q := C.hq2
  have hS := C.hSer2 μ hμ
  rw [← hS.tsum_eq]
  have hW1 : Summable
      (fun m : ℕ => ((((C.q : ℝ) + (m : ℝ)) ^ 4 * majorB C.τ (C.q + m)))) := by
    have h := nr_summable_weighted hτ hq2 C.hτq 2
    simpa using h
  have hCsum : Summable (fun m : ℕ => (32 / C.τ ^ 2)
      * ((((C.q : ℝ) + (m : ℝ)) ^ 4 * majorB C.τ (C.q + m)))) :=
    hW1.mul_left (32 / C.τ ^ 2)
  have hnorm : Summable (fun m : ℕ => ‖nrTerm2 C.a C.τ C.q m μ‖) :=
    Summable.of_nonneg_of_le (fun m => norm_nonneg _)
      (fun m => nr_term2_le C hμ m) hCsum
  have hW := nr_weighted2 hτ hq2 C.hτq
  have hnnc : (0 : ℝ) ≤ 32 / C.τ ^ 2 :=
    div_nonneg (by norm_num) (pow_nonneg hτ.le 2)
  calc ‖∑' m : ℕ, nrTerm2 C.a C.τ C.q m μ‖
      ≤ ∑' m : ℕ, ‖nrTerm2 C.a C.τ C.q m μ‖ :=
        norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' m : ℕ, (32 / C.τ ^ 2)
          * ((((C.q : ℝ) + (m : ℝ)) ^ 4 * majorB C.τ (C.q + m))) :=
        Summable.tsum_le_tsum (fun m => nr_term2_le C hμ m) hnorm hCsum
    _ = (32 / C.τ ^ 2) * (∑' m : ℕ, ((((C.q : ℝ) + (m : ℝ)) ^ 4
          * majorB C.τ (C.q + m)))) := tsum_mul_left
    _ ≤ (32 / C.τ ^ 2) * ((C.q : ℝ) ^ 4 * nrEta2 (nrR C.τ C.q)
          * (∑' m : ℕ, majorB C.τ (C.q + m))) :=
        mul_le_mul_of_nonneg_left hW hnnc
    _ = nrD2of C := by
        unfold nrD2of nrEta2of nrE2
        ring
/-- `D1`/`D2` bounds are nonnegative. -/
lemma nrD1of_nonneg (C : nrCheb) : 0 ≤ nrD1of C := by
  have hτ : 0 < C.τ := by linarith [C.hτ1]
  have heta := nrEta1_nonneg (nrR_nonneg C.τ C.q)
    (nrR_lt_one (nr_alpha_pos hτ C.hτq))
  unfold nrD1of nrEta1of
  exact div_nonneg (mul_nonneg (mul_nonneg heta
    (pow_nonneg (Nat.cast_nonneg _) 2)) (nrE2_nonneg _ _)) hτ.le

lemma nrD2of_nonneg (C : nrCheb) : 0 ≤ nrD2of C := by
  have hτ : 0 < C.τ := by linarith [C.hτ1]
  have heta := nrEta2_nonneg (nrR_nonneg C.τ C.q)
    (nrR_lt_one (nr_alpha_pos hτ C.hτq))
  unfold nrD2of nrEta2of
  exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) heta)
    (pow_nonneg (Nat.cast_nonneg _) 4)) (nrE2_nonneg _ _))
    (pow_nonneg hτ.le 2)

/-- `A·C` factored form. -/
lemma nr_AC_eq (C : nrCheb) (hτ0 : C.τ ≠ 0) (hq0 : (C.q : ℝ) ≠ 0) :
    Realize.RealizeA C.τ (nrB C.τ C.q) (nrE2 C.τ C.q) (nrD1of C)
      * Realize.RealizeC C.τ (nrB C.τ C.q) (nrE2 C.τ C.q) (nrD1of C)
        (nrD2of C) 4
      = ((C.q : ℝ) * nrE2 C.τ C.q) ^ 2
        * (2 * (1 + nrB C.τ C.q / C.τ)
          * (1 + 4 / 27 * nrEta1of C.τ C.q)
          * (32 * nrEta2of C.τ C.q * (C.q : ℝ) ^ 2 + 44
            + 2 * (12 + 16 / 27) * nrEta1of C.τ C.q)) := by
  unfold Realize.RealizeA Realize.RealizeC nrD1of nrD2of nrB
  field_simp
  ring

/-- L4 kernel bound: `‖κ‖₁ ≤ Ccal·q²·E2`. -/
lemma nr_kappa_le (C : nrCheb) :
    ∫ t : ℝ, ‖Realize.kap C.τ (nrB C.τ C.q) C.Ψ C.χ t‖
      ≤ nrCcal C.τ C.q * (C.q : ℝ) ^ 2 * nrE2 C.τ C.q := by
  have hτ : 0 < C.τ := by linarith [C.hτ1]
  have hτ0 : C.τ ≠ 0 := ne_of_gt hτ
  have hq1 : 1 ≤ C.q := by have h := C.hq2; omega
  have hqR : (1 : ℝ) ≤ (C.q : ℝ) := by exact_mod_cast hq1
  have hqpos : (0 : ℝ) < (C.q : ℝ) := by linarith [hqR]
  have hq0 : (C.q : ℝ) ≠ 0 := ne_of_gt hqpos
  have hB0 : 0 < nrB C.τ C.q := by
    unfold nrB
    exact div_pos hτ (pow_pos hqpos 2)
  have hE0 : 0 < nrE2 C.τ C.q := nrE2_pos hτ hq1 C.hτq
  have hD1nn : 0 ≤ nrD1of C := nrD1of_nonneg C
  have hD2nn : 0 ≤ nrD2of C := nrD2of_nonneg C
  have hΨ0 : ∀ μ : ℝ, |μ| ≤ C.τ → ‖C.Ψ μ‖ ≤ nrE2 C.τ C.q :=
    fun μ hμ => nr_sup_le C hμ
  have hΨ1 : ∀ μ : ℝ, |μ| ≤ C.τ → ‖deriv C.Ψ μ‖ ≤ nrD1of C :=
    fun μ hμ => nr_D1_le C hμ
  have hΨ2 : ∀ μ : ℝ, |μ| ≤ C.τ → ‖deriv (deriv C.Ψ) μ‖ ≤ nrD2of C :=
    fun μ hμ => nr_D2_le C hμ
  have hkap := Realize.kap_L1_le C.hτ1 hB0 hE0 (show (1 : ℝ) ≤ 4 by norm_num)
    hD1nn hD2nn C.hΨ hΨ0 hΨ1 hΨ2 C.hχ C.hχ1 C.hχb C.hχd1 C.hχd2
  have hqe : (0 : ℝ) ≤ (C.q : ℝ) * nrE2 C.τ C.q :=
    mul_nonneg hqpos.le (nrE2_nonneg _ _)
  have hAC := nr_AC_eq C hτ0 hq0
  calc ∫ t : ℝ, ‖Realize.kap C.τ (nrB C.τ C.q) C.Ψ C.χ t‖
      ≤ (2 / Real.pi) * Real.sqrt (Realize.RealizeA C.τ (nrB C.τ C.q)
          (nrE2 C.τ C.q) (nrD1of C)
          * Realize.RealizeC C.τ (nrB C.τ C.q) (nrE2 C.τ C.q) (nrD1of C)
            (nrD2of C) 4) := hkap
    _ = (2 / Real.pi) * (((C.q : ℝ) * nrE2 C.τ C.q)
          * Real.sqrt (2 * (1 + nrB C.τ C.q / C.τ)
            * (1 + 4 / 27 * nrEta1of C.τ C.q)
            * (32 * nrEta2of C.τ C.q * (C.q : ℝ) ^ 2 + 44
              + 2 * (12 + 16 / 27) * nrEta1of C.τ C.q))) := by
        rw [hAC, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hqe]
    _ = nrCcal C.τ C.q * (C.q : ℝ) ^ 2 * nrE2 C.τ C.q := by
        unfold nrCcal
        field_simp
/-! ## §4. L5 main rung. -/

/-- `|h| ≤ 2` everywhere. -/
lemma nr_h_abs_le_two (L : ℕ) (α θ : Fin L → ℝ) (lam : ℝ) :
    |h L α θ lam| ≤ 2 := by
  have h1 : ‖U L α θ 1‖ = 1 :=
    norm_eq_one_of_conjTranspose_mul_eq_one _ (U_conjTranspose_mul L α θ 1)
  have hlam : ‖U L α θ lam‖ = 1 :=
    norm_eq_one_of_conjTranspose_mul_eq_one _ (U_conjTranspose_mul L α θ lam)
  have hM : ‖(U L α θ 1)ᴴ * U L α θ lam‖ ≤ 1 := by
    calc ‖(U L α θ 1)ᴴ * U L α θ lam‖
        ≤ ‖(U L α θ 1)ᴴ‖ * ‖U L α θ lam‖ := norm_mul_le _ _
      _ = 1 := by rw [Matrix.l2_opNorm_conjTranspose, h1, hlam, mul_one]
  have htr : ‖((U L α θ 1)ᴴ * U L α θ lam).trace‖ ≤ 2 := by
    calc ‖((U L α θ 1)ᴴ * U L α θ lam).trace‖
        ≤ 2 * ‖(U L α θ 1)ᴴ * U L α θ lam‖ := norm_trace_le _
      _ ≤ 2 * 1 :=
          mul_le_mul_of_nonneg_left hM (by norm_num)
      _ = 2 := mul_one _
  have hre : |(((U L α θ 1)ᴴ * U L α θ lam).trace).re| ≤ 2 :=
    (Complex.abs_re_le_norm _).trans htr
  show |1 - 1 / 2 * (((U L α θ 1)ᴴ * U L α θ lam).trace).re| ≤ 2
  rw [abs_le]
  have hab := abs_le.mp hre
  constructor <;> linarith [hab.1, hab.2]

/-- Shifted moments: with `Γᵢ = e^{iνᵢ}cᵢ`, `Σ ΓᵢP(νᵢ) = 0` for `deg P < q`. -/
lemma nr_gamma_moments {ι : Type} [Fintype ι] {c : ι → ℂ} {ν : ι → ℝ}
    {Γ : ι → ℂ} {q : ℕ}
    (hΓ : ∀ i, Γ i = Complex.exp ((((ν i : ℝ)) : ℂ) * Complex.I) * c i)
    (hmom : ∀ P : Polynomial ℂ, P.natDegree < q →
      ∑ i, Complex.exp ((((ν i : ℝ)) : ℂ) * Complex.I)
        * P.eval ((((ν i : ℝ)) : ℂ)) * c i = 0)
    (P : Polynomial ℂ) (hP : P.natDegree < q) :
    ∑ i, P.eval ((((ν i : ℝ)) : ℂ)) * Γ i = 0 := by
  have h := hmom P hP
  rw [← h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hΓ i]
  ring

/-- `nrCcal ≥ 0`. -/
lemma nrCcal_nonneg (τ : ℝ) (q : ℕ) (hqpos : (0 : ℝ) < (q : ℝ)) :
    0 ≤ nrCcal τ q := by
  unfold nrCcal
  have h1 : (0 : ℝ) ≤ 2 / Real.pi :=
    div_nonneg (by norm_num) Real.pi_pos.le
  have h2 : (0 : ℝ) ≤ 1 / (q : ℝ) :=
    div_nonneg (by norm_num) hqpos.le
  exact mul_nonneg (mul_nonneg h1 h2) (Real.sqrt_nonneg _)

/-- L5 main rung. -/
theorem nr_main_rung {N : ℕ} {φ : ℝ} {L : ℕ} {α θ : Fin L → ℝ} (C : nrCheb)
    (hN : 1 ≤ N) (hφ0 : 0 < φ) (hφπ : φ ≤ Real.pi)
    (hAdm : Admissible N φ L α θ)
    (hqN : C.q = 2 * N + 2)
    (hmain : nrCcal C.τ C.q * (C.q : ℝ) ^ 2 * nrE2star C.τ C.q
      < Real.sin (φ / 4) ^ 2) :
    2 * C.τ < cost θ := by
  by_contra hcon
  have hcon : cost θ ≤ 2 * C.τ := le_of_not_gt hcon
  obtain ⟨ι, hι, c, ν, hν, hrep, hmom, hsum0⟩ := h_moments N φ L α θ hAdm
  have hτ : 0 < C.τ := by linarith [C.hτ1]
  have hqpos : (0 : ℝ) < (C.q : ℝ) := by
    have h2 := C.hq2
    have : (0 : ℕ) < C.q := by omega
    exact_mod_cast this
  -- frequencies lie in the band
  have hTτ : ∀ i, |ν i| ≤ C.τ := by
    intro i
    have h1 := hν i
    have h2 : (∑ j, θ j) / 2 ≤ C.τ := by
      have hT : (∑ j, θ j) = cost θ := rfl
      rw [hT]
      linarith [hcon]
    linarith [h1, h2]
  -- shifted coefficients
  set Γ : ι → ℂ := fun i =>
    Complex.exp ((((ν i : ℝ)) : ℂ) * Complex.I) * c i with hΓdef
  have hΓ : ∀ i, Γ i =
      Complex.exp ((((ν i : ℝ)) : ℂ) * Complex.I) * c i := fun i => by
    rw [hΓdef]
  have hq : C.q = 2 * N + 2 := hqN
  -- `h(0) = Σ ΓΨ(ν)`
  have hPsi_sum : ∑ i, Γ i * C.Ψ (ν i) = ((h L α θ 0 : ℝ) : ℂ) := by
    have hQ0 : ∑ i, Γ i * C.Q.eval ((((ν i : ℝ)) : ℂ)) = 0 := by
      have h := nr_gamma_moments (q := C.q) hΓ
        (fun P hP => hmom P (hq ▸ hP)) C.Q C.hQ
      calc ∑ i, Γ i * C.Q.eval ((((ν i : ℝ)) : ℂ))
          = ∑ i, C.Q.eval ((((ν i : ℝ)) : ℂ)) * Γ i :=
            Finset.sum_congr rfl fun i _ => mul_comm _ _
        _ = 0 := h
    have hE : ∀ i ∈ Finset.univ,
        Γ i * Complex.exp (-((((ν i : ℝ)) : ℂ)) * Complex.I) = c i := by
      intro i _
      have hexp : Complex.exp ((((ν i : ℝ)) : ℂ) * Complex.I)
          * Complex.exp (-((((ν i : ℝ)) : ℂ)) * Complex.I) = 1 := by
        rw [← Complex.exp_add]
        have hz : ((((ν i : ℝ)) : ℂ) * Complex.I
            + -((((ν i : ℝ)) : ℂ)) * Complex.I) = 0 := by ring
        rw [hz, Complex.exp_zero]
      calc Γ i * Complex.exp (-((((ν i : ℝ)) : ℂ)) * Complex.I)
          = (Complex.exp ((((ν i : ℝ)) : ℂ) * Complex.I)
              * Complex.exp (-((((ν i : ℝ)) : ℂ)) * Complex.I)) * c i := by
              rw [hΓ i]; ring
        _ = 1 * c i := by rw [hexp]
        _ = c i := one_mul _
    have hEsum : ∑ i, Γ i * Complex.exp (-((((ν i : ℝ)) : ℂ)) * Complex.I)
        = ((h L α θ 0 : ℝ) : ℂ) := by
      calc ∑ i, Γ i * Complex.exp (-((((ν i : ℝ)) : ℂ)) * Complex.I)
          = ∑ i, c i := Finset.sum_congr rfl hE
        _ = ((h L α θ 0 : ℝ) : ℂ) := hsum0.symm
    have eΨ : ∀ i ∈ Finset.univ, Γ i * C.Ψ (ν i)
        = (Γ i * Complex.exp (-((((ν i : ℝ)) : ℂ)) * Complex.I))
          - Γ i * C.Q.eval ((((ν i : ℝ)) : ℂ)) := by
      intro i _
      rw [C.hΨeq (ν i) (hTτ i)]
      ring
    calc ∑ i, Γ i * C.Ψ (ν i)
        = ∑ i, ((Γ i * Complex.exp (-((((ν i : ℝ)) : ℂ)) * Complex.I))
          - Γ i * C.Q.eval ((((ν i : ℝ)) : ℂ))) :=
          Finset.sum_congr rfl eΨ
      _ = (∑ i, Γ i * Complex.exp (-((((ν i : ℝ)) : ℂ)) * Complex.I))
          - (∑ i, Γ i * C.Q.eval ((((ν i : ℝ)) : ℂ))) :=
          Finset.sum_sub_distrib _ _
      _ = ((h L α θ 0 : ℝ) : ℂ) - 0 := by rw [hEsum, hQ0]
      _ = ((h L α θ 0 : ℝ) : ℂ) := sub_zero _
  -- kernel data
  have hq1 : 1 ≤ C.q := by have h := C.hq2; omega
  have hB0 : 0 < nrB C.τ C.q := by
    unfold nrB
    exact div_pos hτ (pow_pos hqpos 2)
  have hE0 : 0 < nrE2 C.τ C.q := nrE2_pos hτ hq1 C.hτq
  have hD1nn : 0 ≤ nrD1of C := nrD1of_nonneg C
  have hD2nn : 0 ≤ nrD2of C := nrD2of_nonneg C
  have hΨ0 : ∀ μ : ℝ, |μ| ≤ C.τ → ‖C.Ψ μ‖ ≤ nrE2 C.τ C.q :=
    fun μ hμ => nr_sup_le C hμ
  have hΨ1 : ∀ μ : ℝ, |μ| ≤ C.τ → ‖deriv C.Ψ μ‖ ≤ nrD1of C :=
    fun μ hμ => nr_D1_le C hμ
  have hΨ2 : ∀ μ : ℝ, |μ| ≤ C.τ → ‖deriv (deriv C.Ψ) μ‖ ≤ nrD2of C :=
    fun μ hμ => nr_D2_le C hμ
  have hκint : Integrable (Realize.kap C.τ (nrB C.τ C.q) C.Ψ C.χ) :=
    Realize.kap_integrable C.hτ1 hB0 hE0 (show (1 : ℝ) ≤ 4 by norm_num)
      hD1nn hD2nn C.hΨ hΨ0 hΨ1 hΨ2 C.hχ C.hχ1 C.hχb C.hχd1 C.hχd2
  have hinv := Realize.inversion_on_band C.hτ1 hB0 hE0
    (show (1 : ℝ) ≤ 4 by norm_num) hD1nn hD2nn C.hΨ hΨ0 hΨ1 hΨ2 C.hχ
    C.hχ1 C.hχb C.hχd1 C.hχd2
  -- per-frequency inversion in `ExpSum` exponential form
  have hinv_i : ∀ i, (∫ t : ℝ, Realize.kap C.τ (nrB C.τ C.q) C.Ψ C.χ t
      * Complex.exp ((((ν i * t : ℝ)) : ℂ) * Complex.I)) = C.Ψ (ν i) := by
    intro i
    have h := hinv (ν i) (hTτ i)
    have eexp : ∀ t : ℝ, Complex.exp ((((ν i * t : ℝ)) : ℂ) * Complex.I)
        = Complex.exp ((((ν i : ℝ)) : ℂ) * Complex.I * ((t : ℝ) : ℂ)) := by
      intro t
      congr 1
      push_cast
      ring
    calc (∫ t : ℝ, Realize.kap C.τ (nrB C.τ C.q) C.Ψ C.χ t
          * Complex.exp ((((ν i * t : ℝ)) : ℂ) * Complex.I))
        = ∫ t : ℝ, Realize.kap C.τ (nrB C.τ C.q) C.Ψ C.χ t
          * Complex.exp ((((ν i : ℝ)) : ℂ) * Complex.I * ((t : ℝ) : ℂ)) := by
            refine MeasureTheory.integral_congr_ae
              (Filter.Eventually.of_forall fun t => ?_)
            simp only []
            rw [eexp t]
      _ = C.Ψ (ν i) := h
  -- per-term integrability
  have hFi : ∀ i ∈ Finset.univ,
      Integrable (fun t : ℝ => Realize.kap C.τ (nrB C.τ C.q) C.Ψ C.χ t
        * (Γ i * Complex.exp ((((ν i * t : ℝ)) : ℂ) * Complex.I))) := by
    intro i _
    have hcont : Continuous
        (fun t : ℝ => Γ i * Complex.exp ((((ν i * t : ℝ)) : ℂ) * Complex.I)) := by
      fun_prop
    have hbdd : ∀ᵐ t : ℝ, ‖Γ i
        * Complex.exp ((((ν i * t : ℝ)) : ℂ) * Complex.I)‖ ≤ ‖Γ i‖ := by
      refine Filter.Eventually.of_forall fun t => ?_
      have he : ‖Complex.exp ((((ν i * t : ℝ)) : ℂ) * Complex.I)‖ = 1 := by
        rw [Complex.norm_exp]
        have hre : ((((ν i * t : ℝ)) : ℂ) * Complex.I).re = 0 := by
          simp [Complex.mul_re]
        rw [hre, Real.exp_zero]
      rw [norm_mul, he, mul_one]
    exact hκint.mul_bdd hcont.aestronglyMeasurable hbdd
  -- `∫κ·G = ΣΓΨ`
  have hG : (∫ t : ℝ, Realize.kap C.τ (nrB C.τ C.q) C.Ψ C.χ t
      * (∑ i, Γ i * Complex.exp ((((ν i * t : ℝ)) : ℂ) * Complex.I)))
      = ∑ i, Γ i * C.Ψ (ν i) := by
    have eG : (fun t : ℝ => Realize.kap C.τ (nrB C.τ C.q) C.Ψ C.χ t
        * (∑ i, Γ i * Complex.exp ((((ν i * t : ℝ)) : ℂ) * Complex.I)))
        = (fun t : ℝ => ∑ i, Realize.kap C.τ (nrB C.τ C.q) C.Ψ C.χ t
          * (Γ i * Complex.exp ((((ν i * t : ℝ)) : ℂ) * Complex.I))) := by
      funext t
      rw [Finset.mul_sum]
    rw [eG, MeasureTheory.integral_finsetSum _ (fun i hi => hFi i hi)]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hIi : (∫ t : ℝ, Realize.kap C.τ (nrB C.τ C.q) C.Ψ C.χ t
        * (Γ i * Complex.exp ((((ν i * t : ℝ)) : ℂ) * Complex.I)))
        = Γ i * (∫ t : ℝ, Realize.kap C.τ (nrB C.τ C.q) C.Ψ C.χ t
          * Complex.exp ((((ν i * t : ℝ)) : ℂ) * Complex.I)) := by
      have e : (fun t : ℝ => Realize.kap C.τ (nrB C.τ C.q) C.Ψ C.χ t
          * (Γ i * Complex.exp ((((ν i * t : ℝ)) : ℂ) * Complex.I)))
          = (fun t : ℝ => Γ i * (Realize.kap C.τ (nrB C.τ C.q) C.Ψ C.χ t
            * Complex.exp ((((ν i * t : ℝ)) : ℂ) * Complex.I))) := by
        funext t
        ring
      rw [e, MeasureTheory.integral_const_mul]
    rw [hIi, hinv_i i]
  -- norm bound
  have hGint : Integrable (fun t : ℝ => Realize.kap C.τ (nrB C.τ C.q) C.Ψ C.χ t
      * (∑ i, Γ i * Complex.exp ((((ν i * t : ℝ)) : ℂ) * Complex.I))) := by
    have eG : (fun t : ℝ => Realize.kap C.τ (nrB C.τ C.q) C.Ψ C.χ t
        * (∑ i, Γ i * Complex.exp ((((ν i * t : ℝ)) : ℂ) * Complex.I)))
        = (fun t : ℝ => ∑ i, Realize.kap C.τ (nrB C.τ C.q) C.Ψ C.χ t
          * (Γ i * Complex.exp ((((ν i * t : ℝ)) : ℂ) * Complex.I))) := by
      funext t
      rw [Finset.mul_sum]
    rw [eG]
    exact MeasureTheory.integrable_finsetSum _ (fun i hi => hFi i hi)
  have hbnd : ‖(∫ t : ℝ, Realize.kap C.τ (nrB C.τ C.q) C.Ψ C.χ t
      * (∑ i, Γ i * Complex.exp ((((ν i * t : ℝ)) : ℂ) * Complex.I)))‖
      ≤ 2 * (nrCcal C.τ C.q * (C.q : ℝ) ^ 2 * nrE2 C.τ C.q) := by
    have hle1 : ‖(∫ t : ℝ, Realize.kap C.τ (nrB C.τ C.q) C.Ψ C.χ t
        * (∑ i, Γ i * Complex.exp ((((ν i * t : ℝ)) : ℂ) * Complex.I)))‖
        ≤ ∫ t : ℝ, ‖Realize.kap C.τ (nrB C.τ C.q) C.Ψ C.χ t
          * (∑ i, Γ i * Complex.exp ((((ν i * t : ℝ)) : ℂ) * Complex.I))‖ :=
      MeasureTheory.norm_integral_le_integral_norm _
    have hle2 : (∫ t : ℝ, ‖Realize.kap C.τ (nrB C.τ C.q) C.Ψ C.χ t
        * (∑ i, Γ i * Complex.exp ((((ν i * t : ℝ)) : ℂ) * Complex.I))‖)
        ≤ ∫ t : ℝ, 2 * ‖Realize.kap C.τ (nrB C.τ C.q) C.Ψ C.χ t‖ := by
      apply MeasureTheory.integral_mono_ae hGint.norm
        (hκint.norm.const_mul 2)
      refine Filter.Eventually.of_forall fun t => ?_
      have h2 : ‖(∑ i, Γ i
          * Complex.exp ((((ν i * t : ℝ)) : ℂ) * Complex.I))‖ ≤ 2 := by
        have e : (∑ i, Γ i * Complex.exp ((((ν i * t : ℝ)) : ℂ) * Complex.I))
            = ((h L α θ (t + 1) : ℝ) : ℂ) := by
          have hr := hrep (t + 1)
          rw [hr]
          refine Finset.sum_congr rfl fun i _ => ?_
          have ex : Complex.exp ((((ν i * (t + 1) : ℝ)) : ℂ) * Complex.I)
              = Complex.exp ((((ν i * t : ℝ)) : ℂ) * Complex.I)
                * Complex.exp ((((ν i : ℝ)) : ℂ) * Complex.I) := by
            rw [← Complex.exp_add]
            congr 1
            push_cast
            ring
          rw [hΓ i, ex]
          ring
        rw [e, Complex.norm_real, Real.norm_eq_abs]
        exact nr_h_abs_le_two L α θ (t + 1)
      calc ‖Realize.kap C.τ (nrB C.τ C.q) C.Ψ C.χ t
            * (∑ i, Γ i * Complex.exp ((((ν i * t : ℝ)) : ℂ) * Complex.I))‖
          = ‖Realize.kap C.τ (nrB C.τ C.q) C.Ψ C.χ t‖
            * ‖(∑ i, Γ i * Complex.exp ((((ν i * t : ℝ)) : ℂ) * Complex.I))‖ :=
            norm_mul _ _
        _ ≤ ‖Realize.kap C.τ (nrB C.τ C.q) C.Ψ C.χ t‖ * 2 :=
            mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
        _ = 2 * ‖Realize.kap C.τ (nrB C.τ C.q) C.Ψ C.χ t‖ := mul_comm _ _
    have hle3 : (∫ t : ℝ, 2
        * ‖Realize.kap C.τ (nrB C.τ C.q) C.Ψ C.χ t‖)
        = 2 * ∫ t : ℝ, ‖Realize.kap C.τ (nrB C.τ C.q) C.Ψ C.χ t‖ := by
      rw [MeasureTheory.integral_const_mul]
    have hle4 : ∫ t : ℝ, ‖Realize.kap C.τ (nrB C.τ C.q) C.Ψ C.χ t‖
        ≤ nrCcal C.τ C.q * (C.q : ℝ) ^ 2 * nrE2 C.τ C.q := nr_kappa_le C
    linarith [hle1, hle2, hle3, hle4]
  -- contradiction
  have h0R : 2 * Real.sin (φ / 4) ^ 2 ≤ h L α θ 0 :=
    two_mul_sin_sq_le_h_zero N L α θ hφ0 hφπ hAdm
  have h0C : ((h L α θ 0 : ℝ) : ℂ)
      = (∫ t : ℝ, Realize.kap C.τ (nrB C.τ C.q) C.Ψ C.χ t
        * (∑ i, Γ i * Complex.exp ((((ν i * t : ℝ)) : ℂ) * Complex.I))) := by
    rw [hG, hPsi_sum]
  have h0nn : (0 : ℝ) ≤ h L α θ 0 := by
    have hs : (0 : ℝ) ≤ Real.sin (φ / 4) ^ 2 := sq_nonneg _
    linarith [h0R, hs]
  have hfin : h L α θ 0 ≤ 2 * (nrCcal C.τ C.q * (C.q : ℝ) ^ 2 * nrE2 C.τ C.q) := by
    have e : ‖((h L α θ 0 : ℝ) : ℂ)‖ = h L α θ 0 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0nn]
    rw [h0C] at e
    linarith [e, hbnd]
  have hE2s : nrE2 C.τ C.q ≤ nrE2star C.τ C.q :=
    nrE2_le_E2star hτ hq1 C.hτq
  have hCnn : (0 : ℝ) ≤ nrCcal C.τ C.q * (C.q : ℝ) ^ 2 :=
    mul_nonneg (nrCcal_nonneg C.τ C.q hqpos) (pow_nonneg hqpos.le 2)
  have hfin2 : h L α θ 0
      ≤ 2 * (nrCcal C.τ C.q * (C.q : ℝ) ^ 2 * nrE2star C.τ C.q) := by
    have hle : nrCcal C.τ C.q * (C.q : ℝ) ^ 2 * nrE2 C.τ C.q
        ≤ nrCcal C.τ C.q * (C.q : ℝ) ^ 2 * nrE2star C.τ C.q :=
      mul_le_mul_of_nonneg_left hE2s hCnn
    linarith [hfin, hle]
  linarith [h0R, hfin2, hmain]
/-! ## §5. Finitized closed form (L6.1 without `o(1)`). -/

/-- `cosh s ≤ exp (s²/2)` for `s ≥ 0` (via `tanh ≤ id`). -/
lemma nr_cosh_le_exp_half_sq (s : ℝ) (hs : 0 ≤ s) :
    Real.cosh s ≤ Real.exp (s ^ 2 / 2) := by
  have hpos : ∀ t : ℝ, 0 < Real.exp (-(t ^ 2 / 2)) := fun t => Real.exp_pos _
  -- `k(t) = cosh t * exp(-t²/2)` is antitone on `[0,s]`
  have hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) s,
      HasDerivAt (fun t => Real.cosh t * Real.exp (-(t ^ 2 / 2)))
        (Real.exp (-(t ^ 2 / 2)) * (Real.sinh t - t * Real.cosh t)) t := by
    intro t _
    have h1 : HasDerivAt Real.cosh (Real.sinh t) t := Real.hasDerivAt_cosh t
    have hp2 : HasDerivAt (fun t : ℝ => t ^ 2) (2 * t) t := by
      simpa using hasDerivAt_pow 2 t
    have h2 : HasDerivAt (fun t => -(t ^ 2 / 2)) (-((2 * t) / 2)) t :=
      (hp2.div_const 2).neg
    have h3 : HasDerivAt (fun t => Real.exp (-(t ^ 2 / 2)))
        (Real.exp (-(t ^ 2 / 2)) * (-((2 * t) / 2))) t :=
      HasDerivAt.exp h2
    have h4 := h1.mul h3
    have hv : Real.sinh t * Real.exp (-(t ^ 2 / 2))
          + Real.cosh t * (Real.exp (-(t ^ 2 / 2)) * (-((2 * t) / 2)))
        = Real.exp (-(t ^ 2 / 2)) * (Real.sinh t - t * Real.cosh t) := by
      ring
    rwa [hv] at h4
  have hcont : ContinuousOn (fun t => Real.cosh t * Real.exp (-(t ^ 2 / 2)))
      (Set.Icc 0 s) :=
    (Real.continuous_cosh.mul
      (Real.continuous_exp.comp (by continuity))).continuousOn
  have hdiff : DifferentiableOn ℝ
      (fun t => Real.cosh t * Real.exp (-(t ^ 2 / 2)))
      (interior (Set.Icc 0 s)) := by
    intro x hx
    rw [interior_Icc] at hx
    exact (hderiv x hx).differentiableAt.differentiableWithinAt
  have hanti : AntitoneOn (fun t => Real.cosh t * Real.exp (-(t ^ 2 / 2)))
      (Set.Icc 0 s) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 s) hcont hdiff
    intro x hx
    rw [interior_Icc] at hx
    have hx0 : (0 : ℝ) ≤ x := le_of_lt hx.1
    have hle : Real.sinh x - x * Real.cosh x ≤ 0 := by
      have h := sinh_le_mul_cosh hx0
      linarith [h]
    have hderiv_eq : deriv (fun t => Real.cosh t * Real.exp (-(t ^ 2 / 2))) x
        = Real.exp (-(x ^ 2 / 2)) * (Real.sinh x - x * Real.cosh x) :=
      (hderiv x hx).deriv
    rw [hderiv_eq]
    exact mul_nonpos_of_nonneg_of_nonpos (hpos x).le hle
  have h01 : (0 : ℝ) ∈ Set.Icc 0 s := Set.mem_Icc.mpr ⟨le_rfl, hs⟩
  have hs1 : s ∈ Set.Icc 0 s := Set.mem_Icc.mpr ⟨hs, le_rfl⟩
  have hle := hanti h01 hs1 hs
  have hk0 : (fun t => Real.cosh t * Real.exp (-(t ^ 2 / 2))) 0 = 1 := by
    simp [Real.cosh_zero]
  rw [hk0] at hle
  -- `hle : cosh s * exp(-s²/2) ≤ 1`
  have hpos2 : (0 : ℝ) < Real.exp (s ^ 2 / 2) := Real.exp_pos _
  calc Real.cosh s
      = (Real.cosh s * Real.exp (-(s ^ 2 / 2))) * Real.exp (s ^ 2 / 2) := by
        rw [mul_assoc, ← Real.exp_add]
        simp
    _ ≤ 1 * Real.exp (s ^ 2 / 2) :=
        mul_le_mul_of_nonneg_right hle hpos2.le
    _ = Real.exp (s ^ 2 / 2) := one_mul _

/-- `α = arcosh(1/(1-u)) ≥ √(2u)` for `u ∈ [0,1/2]`. -/
lemma nr_alpha_ge_sqrt {u : ℝ} (hu0 : 0 ≤ u) (hu2 : u ≤ 1 / 2) :
    Real.sqrt (2 * u) ≤ Real.arcosh (1 / (1 - u)) := by
  have h1u : (0 : ℝ) < 1 - u := by linarith
  have hA : (1 : ℝ) ≤ 1 / (1 - u) := by
    rw [le_div_iff₀ h1u]
    linarith [hu0]
  have hcosh : Real.cosh (Real.sqrt (2 * u)) ≤ 1 / (1 - u) := by
    have h1 := nr_cosh_le_exp_half_sq (Real.sqrt (2 * u)) (Real.sqrt_nonneg _)
    rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * u)] at h1
    have e : ((2 * u) / 2) = u := by ring
    rw [e] at h1
    have h2 : Real.exp u ≤ 1 / (1 - u) := by
      have h3 : Real.exp u * (1 - u) ≤ 1 := by
        have h4 : (1 - u) ≤ Real.exp (-u) := by
          have h5 := Real.add_one_le_exp (-u)
          linarith [h5]
        calc Real.exp u * (1 - u)
            ≤ Real.exp u * Real.exp (-u) :=
              mul_le_mul_of_nonneg_left h4 (Real.exp_pos _).le
          _ = 1 := by
              rw [← Real.exp_add]
              simp
      exact (le_div_iff₀ h1u).mpr h3
    exact h1.trans h2
  have hApos : (0 : ℝ) < 1 / (1 - u) := div_pos one_pos h1u
  have hle := (Real.arcosh_le_arcosh (Real.cosh_pos _) hApos).mpr hcosh
  rwa [Real.arcosh_cosh (Real.sqrt_nonneg _)] at hle
/-- `f = qα - √(q²-τ²) ≥ q·u^{3/2}/3` for `τ = q(1-u)`. -/
lemma nr_f_ge {τ q u : ℝ} (hq0 : 0 < q) (hu0 : 0 < u) (hu2 : u ≤ 1 / 2)
    (hτeq : τ = q * (1 - u)) :
    q * (u ^ ((3 / 2 : ℝ))) / 3
      ≤ q * besselAlpha τ q - Real.sqrt (q ^ 2 - τ ^ 2) := by
  have h1u : (0 : ℝ) < 1 - u := by linarith
  have hτpos : (0 : ℝ) < τ := by
    rw [hτeq]
    exact mul_pos hq0 h1u
  have hqτ : q / τ = 1 / (1 - u) := by
    rw [hτeq]
    field_simp
  have hα : Real.sqrt (2 * u) ≤ besselAlpha τ q := by
    have h := nr_alpha_ge_sqrt hu0.le hu2
    unfold besselAlpha
    rwa [← hqτ] at h
  have hsq1 : Real.sqrt (q ^ 2 - τ ^ 2) = q * Real.sqrt (2 * u - u ^ 2) := by
    have e : q ^ 2 - τ ^ 2 = q ^ 2 * (2 * u - u ^ 2) := by
      rw [hτeq]
      ring
    rw [e, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hq0.le]
  have hsq2 : Real.sqrt (2 * u - u ^ 2)
      = Real.sqrt (2 * u) * Real.sqrt (1 - u / 2) := by
    have e : (2 * u - u ^ 2) = (2 * u) * (1 - u / 2) := by ring
    rw [e, Real.sqrt_mul (by positivity)]
  have hsq3 : Real.sqrt (1 - u / 2) ≤ 1 - u / 4 := by
    have hnn : (0 : ℝ) ≤ 1 - u / 4 := by linarith
    have hle : (1 - u / 2) ≤ (1 - u / 4) ^ 2 := by nlinarith [sq_nonneg u]
    calc Real.sqrt (1 - u / 2) ≤ Real.sqrt ((1 - u / 4) ^ 2) :=
          Real.sqrt_le_sqrt hle
      _ = 1 - u / 4 := by
          rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hnn]
  have hA : q * Real.sqrt (2 * u - u ^ 2)
      ≤ q * (Real.sqrt (2 * u) * (1 - u / 4)) := by
    rw [hsq2]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hsq3 (Real.sqrt_nonneg _)) hq0.le
  have hE : q * Real.sqrt (2 * u) * (u / 4)
      ≤ q * Real.sqrt (2 * u) - q * Real.sqrt (2 * u - u ^ 2) := by
    have e : q * Real.sqrt (2 * u) * (u / 4)
        = q * Real.sqrt (2 * u) - q * (Real.sqrt (2 * u) * (1 - u / 4)) := by
      ring
    rw [e]
    linarith [hA]
  have hC : q * (Real.sqrt (2 * u) - Real.sqrt (2 * u - u ^ 2))
      ≤ q * (besselAlpha τ q - Real.sqrt (2 * u - u ^ 2)) := by
    apply mul_le_mul_of_nonneg_left _ hq0.le
    linarith [hα]
  have hB : q * besselAlpha τ q - Real.sqrt (q ^ 2 - τ ^ 2)
      = q * (besselAlpha τ q - Real.sqrt (2 * u - u ^ 2)) := by
    rw [hsq1]
    ring
  have hmain : q * Real.sqrt (2 * u) * (u / 4)
      ≤ q * besselAlpha τ q - Real.sqrt (q ^ 2 - τ ^ 2) := by
    rw [hB]
    linarith [hE, hC]
  -- convert `√(2u)·u/4` to `u^{3/2}/3`
  have hu0' : (0 : ℝ) ≤ u := hu0.le
  have s1 : Real.sqrt (2 * u)
      = ((2 : ℝ) ^ ((1 / 2 : ℝ))) * u ^ ((1 / 2 : ℝ)) := by
    have e : Real.sqrt (2 * u) = Real.sqrt 2 * Real.sqrt u :=
      Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2) u
    rw [e, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  have s2 : u * u ^ ((1 / 2 : ℝ)) = u ^ ((3 / 2 : ℝ)) := by
    have e1 : u * u ^ ((1 / 2 : ℝ)) = u ^ ((1 : ℝ)) * u ^ ((1 / 2 : ℝ)) := by
      rw [Real.rpow_one]
    rw [e1, ← Real.rpow_add hu0]
    congr 1
    norm_num
  have epart : Real.sqrt (2 * u) * u / 4
      = (((2 : ℝ) ^ ((1 / 2 : ℝ))) / 4) * (u ^ ((3 / 2 : ℝ))) := by
    rw [s1]
    have : ((2 : ℝ) ^ ((1 / 2 : ℝ))) * u ^ ((1 / 2 : ℝ)) * u / 4
        = (((2 : ℝ) ^ ((1 / 2 : ℝ))) / 4) * (u * u ^ ((1 / 2 : ℝ))) := by
      ring
    rw [this, s2]
  have s3 : (1 : ℝ) / 3 ≤ ((2 : ℝ) ^ ((1 / 2 : ℝ))) / 4 := by
    have e : ((2 : ℝ) ^ ((1 / 2 : ℝ))) = Real.sqrt 2 := (Real.sqrt_eq_rpow 2).symm
    rw [e]
    have h : (4 / 3 : ℝ) ≤ Real.sqrt 2 := by
      rw [Real.le_sqrt (by norm_num) (by norm_num)]
      norm_num
    linarith [h]
  have hpos : (0 : ℝ) ≤ u ^ ((3 / 2 : ℝ)) := Real.rpow_nonneg hu0' _
  have efinal : u ^ ((3 / 2 : ℝ)) / 3 ≤ Real.sqrt (2 * u) * u / 4 := by
    rw [epart]
    calc u ^ ((3 / 2 : ℝ)) / 3 = (1 / 3) * (u ^ ((3 / 2 : ℝ))) := by ring
      _ ≤ (((2 : ℝ) ^ ((1 / 2 : ℝ))) / 4) * (u ^ ((3 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_right s3 hpos
  calc q * (u ^ ((3 / 2 : ℝ))) / 3
      = q * (u ^ ((3 / 2 : ℝ)) / 3) := by ring
    _ ≤ q * (Real.sqrt (2 * u) * u / 4) :=
        mul_le_mul_of_nonneg_left efinal hq0.le
    _ = q * Real.sqrt (2 * u) * (u / 4) := by ring
    _ ≤ q * besselAlpha τ q - Real.sqrt (q ^ 2 - τ ^ 2) := hmain
/-- `1/(1-r) ≤ 1+1/α` for `r = e^{-α}`. -/
lemma nr_inv_sub_le {α r : ℝ} (hr : r = Real.exp (-α)) (hα : 0 < α) :
    1 / (1 - r) ≤ 1 + 1 / α := by
  have h := tailFactor_le hα
  unfold tailFactor at h
  rwa [← hr] at h

/-- `η1 ≤ 2(1+1/α)³`. -/
lemma nr_eta1_le {α r : ℝ} (hr : r = Real.exp (-α)) (hα : 0 < α) :
    nrEta1 r ≤ 2 * (1 + 1 / α) ^ 3 := by
  have hr0 : (0 : ℝ) ≤ r := by
    rw [hr]
    exact (Real.exp_pos _).le
  have hr1 : r < 1 := by
    rw [hr, Real.exp_lt_one_iff]
    linarith [hα]
  have h1r : (0 : ℝ) ≤ 1 - r := by linarith
  have h1rne : (1 : ℝ) - r ≠ 0 := sub_ne_zero.mpr (ne_of_gt (by linarith))
  have hinv : 1 / (1 - r) ≤ 1 + 1 / α := nr_inv_sub_le hr hα
  have ha0 : (0 : ℝ) ≤ 1 / (1 - r) := div_nonneg (by norm_num) h1r
  have hB : (1 / (1 - r)) ^ 3 ≤ (1 + 1 / α) ^ 3 :=
    pow_le_pow_left₀ ha0 hinv 3
  have hA : (1 + r) ≤ 2 := by linarith
  have e : nrEta1 r = (1 + r) * (1 / (1 - r)) ^ 3 := by
    unfold nrEta1
    field_simp

  rw [e]
  have hc0 : (0 : ℝ) ≤ (1 / (1 - r)) ^ 3 :=
    pow_nonneg (div_nonneg (by norm_num) h1r) 3
  calc (1 + r) * (1 / (1 - r)) ^ 3
      ≤ 2 * (1 + 1 / α) ^ 3 :=
        mul_le_mul hA hB hc0 (by norm_num)

/-- `η2 ≤ 24(1+1/α)^5`. -/
lemma nr_eta2_le {α r : ℝ} (hr : r = Real.exp (-α)) (hα : 0 < α) :
    nrEta2 r ≤ 24 * (1 + 1 / α) ^ 5 := by
  have hr0 : (0 : ℝ) ≤ r := by
    rw [hr]
    exact (Real.exp_pos _).le
  have hr1 : r < 1 := by
    rw [hr, Real.exp_lt_one_iff]
    linarith [hα]
  have h1r : (0 : ℝ) ≤ 1 - r := by linarith
  have h1rne : (1 : ℝ) - r ≠ 0 := sub_ne_zero.mpr (ne_of_gt (by linarith))
  have hinv : 1 / (1 - r) ≤ 1 + 1 / α := nr_inv_sub_le hr hα
  have ha0 : (0 : ℝ) ≤ 1 / (1 - r) := div_nonneg (by norm_num) h1r
  have hB : (1 / (1 - r)) ^ 5 ≤ (1 + 1 / α) ^ 5 :=
    pow_le_pow_left₀ ha0 hinv 5
  have hA : (1 + 11 * r + 11 * r ^ 2 + r ^ 3) ≤ 24 := by
    have h1 : r ^ 2 ≤ 1 := by nlinarith [hr0, hr1]
    have h2 : r ^ 3 ≤ 1 := by nlinarith [hr0, hr1]
    linarith [hr1]
  have e : nrEta2 r
      = (1 + 11 * r + 11 * r ^ 2 + r ^ 3) * (1 / (1 - r)) ^ 5 := by
    unfold nrEta2
    field_simp

  rw [e]
  have hc0 : (0 : ℝ) ≤ (1 / (1 - r)) ^ 5 :=
    pow_nonneg (div_nonneg (by norm_num) h1r) 5
  calc (1 + 11 * r + 11 * r ^ 2 + r ^ 3) * (1 / (1 - r)) ^ 5
      ≤ 24 * (1 + 1 / α) ^ 5 :=
        mul_le_mul hA hB hc0 (by norm_num)

/-- `η1 ≥ 1`. -/
lemma nrEta1_ge_one {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) : 1 ≤ nrEta1 r := by
  have h1r : (0 : ℝ) < 1 - r := by linarith
  have hD : (0 : ℝ) < (1 - r) ^ 3 := pow_pos h1r 3
  have hkey : (1 - r) ^ 3 ≤ 1 + r := by
    have e : (1 - r) ^ 3 = 1 - 3 * r + 3 * r ^ 2 - r ^ 3 := by ring
    have hnn : (0 : ℝ) ≤ 4 * r - 3 * r ^ 2 + r ^ 3 := by
      have h1 : (0 : ℝ) ≤ r * (4 - 3 * r + r ^ 2) :=
        mul_nonneg hr0 (by nlinarith [sq_nonneg (r - 3 / 2)])
      nlinarith [h1]
    nlinarith [e, hnn]
  unfold nrEta1
  rw [le_div_iff₀ hD]
  linarith [hkey]

/-- `η1 ≤ η2`. -/
lemma nrEta1_le_eta2 {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    nrEta1 r ≤ nrEta2 r := by
  have h1r : (0 : ℝ) < 1 - r := by linarith
  have hD : (0 : ℝ) < (1 - r) ^ 5 := pow_pos h1r 5
  have h1rne : (1 : ℝ) - r ≠ 0 := ne_of_gt h1r
  have e1 : nrEta1 r = ((1 + r) * (1 - r) ^ 2) / (1 - r) ^ 5 := by
    unfold nrEta1
    field_simp

  rw [e1]
  unfold nrEta2
  rw [div_le_div_iff₀ hD hD]
  have hkey : (1 + r) * (1 - r) ^ 2
      ≤ 1 + 11 * r + 11 * r ^ 2 + r ^ 3 := by
    have e : (1 + r) * (1 - r) ^ 2 = 1 - r - r ^ 2 + r ^ 3 := by ring
    have hnn : (0 : ℝ) ≤ 12 * r + 12 * r ^ 2 := by
      have h1 : (0 : ℝ) ≤ 12 * r := by positivity
      have h2 : (0 : ℝ) ≤ 12 * r ^ 2 := by positivity
      linarith [h1, h2]
    nlinarith [e, hnn]
  have hDnn : (0 : ℝ) ≤ (1 - r) ^ 5 := hD.le
  exact mul_le_mul_of_nonneg_right hkey hDnn
/-- `1 + 1/α ≤ 2(2u)^{-1/2}` from `√(2u) ≤ α`, `u ≤ 1/2`. -/
lemma nr_one_plus_inv_alpha_le {α u : ℝ} (hα0 : 0 < α)
    (hαu : Real.sqrt (2 * u) ≤ α) (hu0 : 0 < u) (hu2 : u ≤ 1 / 2) :
    1 + 1 / α ≤ 2 * (2 * u) ^ (-(1 / 2 : ℝ)) := by
  have h2u : (0 : ℝ) < 2 * u := by positivity
  have hM : (1 : ℝ) ≤ (2 * u) ^ (-(1 / 2 : ℝ)) := by
    have hy : (2 * u) ^ ((1 / 2 : ℝ)) ≤ 1 := by
      calc (2 * u) ^ ((1 / 2 : ℝ)) ≤ (1 : ℝ) ^ ((1 / 2 : ℝ)) :=
            Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
        _ = 1 := Real.one_rpow _
    have hypos : (0 : ℝ) < (2 * u) ^ ((1 / 2 : ℝ)) :=
      Real.rpow_pos_of_pos h2u _
    rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ 2 * u), inv_eq_one_div]
    have h := one_div_le_one_div_of_le hypos hy
    simpa using h
  have hA : 1 / α ≤ (2 * u) ^ (-(1 / 2 : ℝ)) := by
    have h1 : 1 / α ≤ 1 / Real.sqrt (2 * u) :=
      one_div_le_one_div_of_le (Real.sqrt_pos.mpr h2u) hαu
    have e : (1 : ℝ) / Real.sqrt (2 * u) = (2 * u) ^ (-(1 / 2 : ℝ)) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_neg (by positivity : (0:ℝ) ≤ 2 * u),
        inv_eq_one_div]
    rwa [e] at h1
  linarith [hM, hA]

/-- `η2 ≤ 768(2u)^{-5/2}`. -/
lemma nr_eta2_le_768 {τ : ℝ} {q : ℕ} {u α r : ℝ}
    (hr : r = Real.exp (-α)) (hα0 : 0 < α)
    (hαu : Real.sqrt (2 * u) ≤ α) (hu0 : 0 < u) (hu2 : u ≤ 1 / 2)
    (heta : nrEta2of τ q = nrEta2 r) :
    nrEta2of τ q ≤ 768 * (2 * u) ^ (-(5 / 2 : ℝ)) := by
  have h1 := nr_eta2_le hr hα0
  have h2 := nr_one_plus_inv_alpha_le hα0 hαu hu0 hu2
  have hnn : (0 : ℝ) ≤ 1 + 1 / α := by
    have hpos : (0 : ℝ) ≤ 1 / α := by positivity
    linarith [hpos]
  have h5 : (1 + 1 / α) ^ 5 ≤ (2 * (2 * u) ^ (-(1 / 2 : ℝ))) ^ 5 :=
    pow_le_pow_left₀ hnn h2 5
  have f : ((2 * u) ^ (-(1 / 2 : ℝ))) ^ 5 = (2 * u) ^ (-(5 / 2 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ 2 * u)]
    congr 1
    norm_num
  have e5 : (2 * (2 * u) ^ (-(1 / 2 : ℝ))) ^ 5
      = 32 * (2 * u) ^ (-(5 / 2 : ℝ)) := by
    rw [mul_pow, f]
    norm_num
  calc nrEta2of τ q = nrEta2 r := heta
    _ ≤ 24 * (1 + 1 / α) ^ 5 := h1
    _ ≤ 24 * ((2 * (2 * u) ^ (-(1 / 2 : ℝ))) ^ 5) :=
        mul_le_mul_of_nonneg_left h5 (by norm_num)
    _ = 768 * (2 * u) ^ (-(5 / 2 : ℝ)) := by
        rw [e5]
        ring
/-- `Ccal ≤ 6144(2u)^{-5/2}`. -/
lemma nr_ccal_le {τ : ℝ} {q : ℕ} {u : ℝ}
    (hq2 : (2 : ℝ) ≤ (q : ℝ))
    (hτ0 : 0 < τ)
    (heta1 : 1 ≤ nrEta1of τ q)
    (heta12 : nrEta1of τ q ≤ nrEta2of τ q)
    (heta2nn : 0 ≤ nrEta2of τ q)
    (heta2 : nrEta2of τ q ≤ 768 * (2 * u) ^ (-(5 / 2 : ℝ))) :
    nrCcal τ q ≤ 6144 * (2 * u) ^ (-(5 / 2 : ℝ)) := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by linarith
  have hq0' : (q : ℝ) ≠ 0 := ne_of_gt hq0
  have hτ0' : τ ≠ 0 := ne_of_gt hτ0
  have heta1nn : (0 : ℝ) ≤ nrEta1of τ q := by linarith
  have heta2ge : (1 : ℝ) ≤ nrEta2of τ q := by linarith
  -- (a)
  have hA1 : 1 + nrB τ q / τ ≤ 1.25 := by
    have e : nrB τ q / τ = 1 / (q : ℝ) ^ 2 := by
      unfold nrB
      field_simp
    rw [e]
    have hq4 : (4 : ℝ) ≤ (q : ℝ) ^ 2 := by
      calc (4 : ℝ) = 2 ^ 2 := by norm_num
        _ ≤ (q : ℝ) ^ 2 := pow_le_pow_left₀ (by norm_num) hq2 2
    have h14 : (1 : ℝ) / (q : ℝ) ^ 2 ≤ 1 / 4 :=
      one_div_le_one_div_of_le (by norm_num) hq4
    linarith [h14]
  have hA1nn : (0 : ℝ) ≤ 1 + nrB τ q / τ := by
    have : (0:ℝ) ≤ nrB τ q / τ := by
      unfold nrB
      exact div_nonneg (div_nonneg hτ0.le (pow_nonneg hq0.le 2)) hτ0.le
    linarith [this]
  -- (b)
  have hB1 : 1 + (4 / 27) * nrEta1of τ q ≤ (31 / 27) * nrEta2of τ q := by
    nlinarith [heta1, heta12]
  have hB1nn : (0 : ℝ) ≤ 1 + (4 / 27) * nrEta1of τ q := by
    have : (0:ℝ) ≤ (4 / 27) * nrEta1of τ q := by positivity
    linarith [this]
  -- (c)
  have hC1 : 32 * nrEta2of τ q * (q : ℝ) ^ 2 + 44
      + 2 * (12 + 16 / 27) * nrEta1of τ q
      ≤ 50 * nrEta2of τ q * (q : ℝ) ^ 2 := by
    have hq4 : (4 : ℝ) ≤ (q : ℝ) ^ 2 := by
      calc (4 : ℝ) = 2 ^ 2 := by norm_num
        _ ≤ (q : ℝ) ^ 2 := pow_le_pow_left₀ (by norm_num) hq2 2
    have g1 : (44 : ℝ) ≤ 44 * nrEta2of τ q := by
      have := mul_le_mul_of_nonneg_left heta2ge (by norm_num : (0:ℝ) ≤ 44)
      rwa [mul_one] at this
    have g2 : 2 * (12 + 16 / 27) * nrEta1of τ q ≤ 26 * nrEta2of τ q := by
      have hc : (2:ℝ) * (12 + 16 / 27) ≤ 26 := by norm_num
      have h1 : 2 * (12 + 16 / 27) * nrEta1of τ q ≤ 26 * nrEta1of τ q :=
        mul_le_mul_of_nonneg_right hc heta1nn
      have h2 : 26 * nrEta1of τ q ≤ 26 * nrEta2of τ q :=
        mul_le_mul_of_nonneg_left heta12 (by norm_num)
      linarith [h1, h2]
    have g3 : (32 : ℝ) * (q : ℝ) ^ 2 + 70 ≤ 50 * (q : ℝ) ^ 2 := by
      nlinarith [hq4]
    nlinarith [g1, g2, g3, heta2nn,
      mul_nonneg heta2nn (pow_nonneg hq0.le 2)]
  have hC1nn : (0 : ℝ) ≤ 32 * nrEta2of τ q * (q : ℝ) ^ 2 + 44
      + 2 * (12 + 16 / 27) * nrEta1of τ q := by
    have h1 : (0:ℝ) ≤ 32 * nrEta2of τ q * (q : ℝ) ^ 2 := by positivity
    have h2 : (0:ℝ) ≤ 2 * (12 + 16 / 27) * nrEta1of τ q := by positivity
    linarith [h1, h2]
  -- inner product
  have hI : 2 * (1 + nrB τ q / τ) * (1 + (4 / 27) * nrEta1of τ q)
      * (32 * nrEta2of τ q * (q : ℝ) ^ 2 + 44
        + 2 * (12 + 16 / 27) * nrEta1of τ q)
      ≤ (3875 / 27) * (nrEta2of τ q ^ 2 * (q : ℝ) ^ 2) := by
    have p1 : (0:ℝ) ≤ (1 + (4 / 27) * nrEta1of τ q)
        * (32 * nrEta2of τ q * (q : ℝ) ^ 2 + 44
          + 2 * (12 + 16 / 27) * nrEta1of τ q) :=
      mul_nonneg hB1nn hC1nn
    have p2 : (0:ℝ) ≤ ((31 / 27) * nrEta2of τ q)
        * (50 * nrEta2of τ q * (q : ℝ) ^ 2) := by
      positivity
    calc 2 * (1 + nrB τ q / τ) * (1 + (4 / 27) * nrEta1of τ q)
          * (32 * nrEta2of τ q * (q : ℝ) ^ 2 + 44
            + 2 * (12 + 16 / 27) * nrEta1of τ q)
        = (2 * (1 + nrB τ q / τ))
          * ((1 + (4 / 27) * nrEta1of τ q)
            * (32 * nrEta2of τ q * (q : ℝ) ^ 2 + 44
              + 2 * (12 + 16 / 27) * nrEta1of τ q)) := by
          ring
      _ ≤ (2 * 1.25) * (((31 / 27) * nrEta2of τ q)
          * (50 * nrEta2of τ q * (q : ℝ) ^ 2)) := by
          apply mul_le_mul _ _ p1 (by norm_num)
          · exact mul_le_mul_of_nonneg_left hA1 (by norm_num)
          · exact mul_le_mul hB1 hC1 hC1nn (by positivity)
      _ = (3875 / 27) * (nrEta2of τ q ^ 2 * (q : ℝ) ^ 2) := by
          ring
  have hS : Real.sqrt (2 * (1 + nrB τ q / τ) * (1 + (4 / 27) * nrEta1of τ q)
      * (32 * nrEta2of τ q * (q : ℝ) ^ 2 + 44
        + 2 * (12 + 16 / 27) * nrEta1of τ q))
      ≤ 12 * nrEta2of τ q * (q : ℝ) := by
    have hle : 2 * (1 + nrB τ q / τ) * (1 + (4 / 27) * nrEta1of τ q)
        * (32 * nrEta2of τ q * (q : ℝ) ^ 2 + 44
          + 2 * (12 + 16 / 27) * nrEta1of τ q)
        ≤ (12 * nrEta2of τ q * (q : ℝ)) ^ 2 := by
      have e : (12 * nrEta2of τ q * (q : ℝ)) ^ 2
          = 144 * (nrEta2of τ q ^ 2 * (q : ℝ) ^ 2) := by ring
      rw [e]
      have h3875 : (3875 / 27 : ℝ) ≤ 144 := by norm_num
      have hnn : (0:ℝ) ≤ nrEta2of τ q ^ 2 * (q : ℝ) ^ 2 :=
        mul_nonneg (pow_nonneg heta2nn 2) (pow_nonneg hq0.le 2)
      calc 2 * (1 + nrB τ q / τ) * (1 + (4 / 27) * nrEta1of τ q)
            * (32 * nrEta2of τ q * (q : ℝ) ^ 2 + 44
              + 2 * (12 + 16 / 27) * nrEta1of τ q)
          ≤ (3875 / 27) * (nrEta2of τ q ^ 2 * (q : ℝ) ^ 2) := hI
        _ ≤ 144 * (nrEta2of τ q ^ 2 * (q : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_right h3875 hnn
    calc Real.sqrt _
        ≤ Real.sqrt ((12 * nrEta2of τ q * (q : ℝ)) ^ 2) :=
          Real.sqrt_le_sqrt hle
      _ = 12 * nrEta2of τ q * (q : ℝ) := by
          rw [Real.sqrt_sq]
          positivity
  have h24 : (24 : ℝ) / Real.pi ≤ 8 := by
    rw [div_le_iff₀ Real.pi_pos]
    have := Real.pi_gt_three
    linarith [this]
  calc nrCcal τ q
      = (2 / Real.pi) * (1 / (q : ℝ))
        * Real.sqrt (2 * (1 + nrB τ q / τ) * (1 + (4 / 27) * nrEta1of τ q)
          * (32 * nrEta2of τ q * (q : ℝ) ^ 2 + 44
            + 2 * (12 + 16 / 27) * nrEta1of τ q)) := by
        unfold nrCcal
        ring_nf
    _ ≤ (2 / Real.pi) * (1 / (q : ℝ)) * (12 * nrEta2of τ q * (q : ℝ)) := by
        apply mul_le_mul_of_nonneg_left hS
        apply mul_nonneg _ (by positivity)
        rw [div_nonneg_iff]
        left
        exact ⟨by norm_num, Real.pi_pos.le⟩
    _ = (24 / Real.pi) * nrEta2of τ q := by
        field_simp
        ring
    _ ≤ 8 * nrEta2of τ q :=
        mul_le_mul_of_nonneg_right h24 heta2nn
    _ ≤ 8 * (768 * (2 * u) ^ (-(5 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left heta2 (by norm_num)
    _ = 6144 * (2 * u) ^ (-(5 / 2 : ℝ)) := by
        ring
/-- `√√x = x^{1/4}`. -/
lemma nr_sqrt4 (x : ℝ) (hx : 0 ≤ x) :
    Real.sqrt (Real.sqrt x) = x ^ ((1 / 4 : ℝ)) := by
  have e : Real.sqrt (Real.sqrt x) = ((x ^ ((1 / 2 : ℝ)))) ^ ((1 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  rw [e, ← Real.rpow_mul hx]
  congr 1
  norm_num

/-- `1/(1-e^{-α}) ≤ 2(2u)^{-1/2}`. -/
lemma nr_tfactor_le {α u : ℝ} (hα0 : 0 < α)
    (hαu : Real.sqrt (2 * u) ≤ α) (hu0 : 0 < u) (hu2 : u ≤ 1 / 2) :
    1 / (1 - Real.exp (-α)) ≤ 2 * (2 * u) ^ (-(1 / 2 : ℝ)) :=
  (nr_inv_sub_le rfl hα0).trans (nr_one_plus_inv_alpha_le hα0 hαu hu0 hu2)

/-- `E2* ≤ 2.52·e^{-f}·q^{-1/2}·u^{-3/4}`. -/
lemma nr_e2star_le {τ : ℝ} {q : ℕ} {u : ℝ}
    (hq0 : 0 < (q : ℝ)) (hu0 : 0 < u)
    (hα0 : 0 ≤ besselAlpha τ (q : ℝ))
    (hqq : (q : ℝ) ^ 2 * u ≤ (q : ℝ) ^ 2 - τ ^ 2)
    (hαinv : 1 / (1 - Real.exp (-(besselAlpha τ (q : ℝ))))
      ≤ 2 * (2 * u) ^ (-(1 / 2 : ℝ))) :
    nrE2star τ q ≤ 2.52 * Real.exp (-(besselF τ (q : ℝ)))
      * ((q : ℝ) ^ (-(1 / 2 : ℝ)) * u ^ (-(3 / 4 : ℝ))) := by
  have hpi : Real.sqrt (Real.pi / 8) ≤ 0.63 := by
    have e : (0.63 : ℝ) ^ 2 = 0.3969 := by norm_num
    have h1 : Real.pi / 8 ≤ (0.63) ^ 2 := by
      have hpi4 := Real.pi_lt_d4
      nlinarith [hpi4, e]
    calc Real.sqrt (Real.pi / 8) ≤ Real.sqrt ((0.63) ^ 2) :=
          Real.sqrt_le_sqrt h1
      _ = 0.63 := Real.sqrt_sq (by norm_num)
  have hqu0 : (0 : ℝ) ≤ (q : ℝ) ^ 2 * u := by positivity
  have hD : (0 : ℝ) < (q : ℝ) ^ 2 - τ ^ 2 := by
    have hpos : (0:ℝ) < (q:ℝ)^2 * u := by positivity
    linarith [hqq, hpos]
  have hsqrt_le : (1 : ℝ) / Real.sqrt (Real.sqrt ((q : ℝ) ^ 2 - τ ^ 2))
      ≤ 1 / Real.sqrt (Real.sqrt ((q : ℝ) ^ 2 * u)) := by
    have hpos : (0 : ℝ) < Real.sqrt (Real.sqrt ((q : ℝ) ^ 2 * u)) := by
      apply Real.sqrt_pos.mpr
      apply Real.sqrt_pos.mpr
      positivity
    have hle : Real.sqrt (Real.sqrt ((q : ℝ) ^ 2 * u))
        ≤ Real.sqrt (Real.sqrt ((q : ℝ) ^ 2 - τ ^ 2)) := by
      apply Real.sqrt_le_sqrt
      apply Real.sqrt_le_sqrt
      exact hqq
    exact one_div_le_one_div_of_le hpos hle
  have hconv : (1 : ℝ) / Real.sqrt (Real.sqrt ((q : ℝ) ^ 2 * u))
      = ((q : ℝ) ^ (-(1 / 2 : ℝ)) * u ^ (-(1 / 4 : ℝ))) := by
    have e1 : Real.sqrt (Real.sqrt ((q : ℝ) ^ 2 * u))
        = ((q : ℝ) ^ 2 * u) ^ ((1 / 4 : ℝ)) := nr_sqrt4 _ hqu0
    have e2 : (((q : ℝ) ^ 2 * u) ^ ((1 / 4 : ℝ)))
        = ((q : ℝ) ^ 2) ^ ((1 / 4 : ℝ)) * u ^ ((1 / 4 : ℝ)) :=
      Real.mul_rpow (by positivity) (by positivity)
    have e3 : (((q : ℝ) ^ 2) ^ ((1 / 4 : ℝ))) = (q : ℝ) ^ ((1 / 2 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hq0.le]
      congr 1
      norm_num
    have e4 : (1 : ℝ) / (((q : ℝ) ^ 2) ^ ((1 / 4 : ℝ)) * u ^ ((1 / 4 : ℝ)))
        = ((q : ℝ) ^ (-(1 / 2 : ℝ)) * u ^ (-(1 / 4 : ℝ))) := by
      have f1 : ((((q : ℝ) ^ 2) ^ ((1 / 4 : ℝ))))⁻¹
          = (q : ℝ) ^ (-(1 / 2 : ℝ)) := by
        rw [e3]
        exact (Real.rpow_neg hq0.le _).symm
      have f2 : ((u ^ ((1 / 4 : ℝ))))⁻¹ = u ^ (-(1 / 4 : ℝ)) :=
        (Real.rpow_neg hu0.le _).symm
      rw [div_eq_mul_inv, mul_inv_rev, f1, f2, one_mul]
      ring
    rw [e1, e2]
    exact e4
  have h2u : (2 * u) ^ (-(1 / 2 : ℝ)) ≤ u ^ (-(1 / 2 : ℝ)) := by
    have e : (2 * u) ^ (-(1 / 2 : ℝ))
        = (2 : ℝ) ^ (-(1 / 2 : ℝ)) * u ^ (-(1 / 2 : ℝ)) :=
      Real.mul_rpow (by norm_num) hu0.le
    have h21 : (2 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 := by
      have h := Real.rpow_le_rpow_of_nonpos (show (0:ℝ) < 1 by norm_num)
        (show (1:ℝ) ≤ 2 by norm_num) (show (-(1 / 2 : ℝ)) ≤ 0 by norm_num)
      rwa [Real.one_rpow] at h
    calc (2 * u) ^ (-(1 / 2 : ℝ))
        = (2 : ℝ) ^ (-(1 / 2 : ℝ)) * u ^ (-(1 / 2 : ℝ)) := e
      _ ≤ 1 * u ^ (-(1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_right h21
            (Real.rpow_nonneg hu0.le _)
      _ = u ^ (-(1 / 2 : ℝ)) := one_mul _
  -- assemble
  have hE2 : nrE2star τ q
      = (2 * Real.sqrt (Real.pi / 8)) * Real.exp (-(besselF τ (q : ℝ)))
        * ((1 / Real.sqrt (Real.sqrt ((q : ℝ) ^ 2 - τ ^ 2)))
          * (1 / (1 - Real.exp (-(besselAlpha τ (q : ℝ)))))) := by
    unfold nrE2star
    field_simp
  rw [hE2]
  have n1 : (0:ℝ) ≤ Real.exp (-(besselF τ (q : ℝ))) := (Real.exp_pos _).le
  have n2 : (0:ℝ) ≤ 1 / Real.sqrt (Real.sqrt ((q : ℝ) ^ 2 - τ ^ 2)) :=
    div_nonneg (by norm_num) (Real.sqrt_nonneg _)
  have n3 : (0:ℝ) ≤ 1 / (1 - Real.exp (-(besselAlpha τ (q : ℝ)))) := by
    apply div_nonneg (by norm_num)
    have e1 : Real.exp (-(besselAlpha τ (q : ℝ))) ≤ Real.exp 0 :=
      Real.exp_le_exp.mpr (by linarith [hα0])
    rw [Real.exp_zero] at e1
    linarith [e1]
  have g1 : (2 * Real.sqrt (Real.pi / 8)) ≤ 1.26 := by linarith [hpi]
  have g2 : (1 / Real.sqrt (Real.sqrt ((q : ℝ) ^ 2 - τ ^ 2)))
      ≤ ((q : ℝ) ^ (-(1 / 2 : ℝ)) * u ^ (-(1 / 4 : ℝ))) :=
    hsqrt_le.trans (le_of_eq hconv)
  have g3 : (1 / (1 - Real.exp (-(besselAlpha τ (q : ℝ)))))
      ≤ 2 * u ^ (-(1 / 2 : ℝ)) := hαinv.trans (by
        have := h2u
        linarith [this])
  -- combine: 1.26 * e * (q^{-1/2} u^{-1/4}) * (2 u^{-1/2})
  have hDnn : (0:ℝ) ≤ ((q : ℝ) ^ (-(1 / 2 : ℝ)) * u ^ (-(1 / 4 : ℝ))) :=
    mul_nonneg (Real.rpow_nonneg hq0.le _) (Real.rpow_nonneg hu0.le _)
  have hPnn : (0:ℝ) ≤ 1.26 * Real.exp (-(besselF τ (q : ℝ))) :=
    mul_nonneg (by norm_num) n1
  have hQnn : (0:ℝ) ≤ (1 / Real.sqrt (Real.sqrt ((q : ℝ) ^ 2 - τ ^ 2)))
      * (1 / (1 - Real.exp (-(besselAlpha τ (q : ℝ))))) :=
    mul_nonneg n2 n3
  have hmul : (2 * Real.sqrt (Real.pi / 8)) * Real.exp (-(besselF τ (q : ℝ)))
      * ((1 / Real.sqrt (Real.sqrt ((q : ℝ) ^ 2 - τ ^ 2)))
        * (1 / (1 - Real.exp (-(besselAlpha τ (q : ℝ))))))
      ≤ 1.26 * Real.exp (-(besselF τ (q : ℝ)))
        * ((((q : ℝ) ^ (-(1 / 2 : ℝ)) * u ^ (-(1 / 4 : ℝ))))
          * (2 * u ^ (-(1 / 2 : ℝ)))) :=
    mul_le_mul (mul_le_mul_of_nonneg_right g1 n1)
      (mul_le_mul g2 g3 n3 hDnn) hQnn hPnn
  refine hmul.trans ?_
  -- `1.26 * e * ((q^{-1/2} u^{-1/4}) * (2 u^{-1/2})) = 2.52 * e * (q^{-1/2} u^{-3/4})`
  have eu : u ^ (-(1 / 4 : ℝ)) * u ^ (-(1 / 2 : ℝ)) = u ^ (-(3 / 4 : ℝ)) := by
    rw [← Real.rpow_add hu0]
    congr 1
    norm_num
  have hfin : 1.26 * Real.exp (-(besselF τ (q : ℝ)))
        * ((((q : ℝ) ^ (-(1 / 2 : ℝ)) * u ^ (-(1 / 4 : ℝ))))
          * (2 * u ^ (-(1 / 2 : ℝ))))
      = 2.52 * Real.exp (-(besselF τ (q : ℝ)))
        * ((q : ℝ) ^ (-(1 / 2 : ℝ)) * u ^ (-(3 / 4 : ℝ))) := by
        rw [← eu]
        ring
  exact le_of_eq hfin
/-- `log q ≤ 4q^{1/4}`. -/
lemma nr_log_le_four_rpow (q : ℝ) (hq0 : 0 < q) :
    Real.log q ≤ 4 * q ^ ((1 / 4 : ℝ)) := by
  have h1 : Real.log (q ^ ((1 / 4 : ℝ))) ≤ q ^ ((1 / 4 : ℝ)) - 1 :=
    Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hq0 _)
  have h2 : Real.log (q ^ ((1 / 4 : ℝ))) = (1 / 4) * Real.log q :=
    Real.log_rpow hq0 _
  nlinarith [h1, h2, Real.rpow_nonneg hq0.le ((1 / 4 : ℝ))]

/-- Deficit parameter `u = 6(log q/q)^{2/3}`. -/
noncomputable def nrU (q : ℝ) : ℝ := 6 * ((Real.log q / q) ^ ((2 / 3 : ℝ)))

/-- Side bounds `0 < nrU q ≤ 1/2` for `q ≥ 1000`, `log q ≥ 1`. -/
lemma nr_u_bounds (q : ℝ) (hq : 1000 ≤ q) (hlog : 1 ≤ Real.log q) :
    0 < nrU q ∧ nrU q ≤ 1 / 2 := by
  have hq0 : (0 : ℝ) < q := by linarith
  have hw0 : (0 : ℝ) < Real.log q / q := div_pos (by linarith) hq0
  have hw0' : (0 : ℝ) ≤ Real.log q / q := hw0.le
  have hu_pos : 0 < nrU q := by
    unfold nrU
    apply mul_pos (by norm_num)
    exact Real.rpow_pos_of_pos hw0 _
  refine ⟨hu_pos, ?_⟩
  have hlogle := nr_log_le_four_rpow q hq0
  have hw : Real.log q / q ≤ 4 * q ^ ((1 / 4 : ℝ)) / q :=
    (div_le_div_iff_of_pos_right hq0).mpr hlogle
  have hw4 : (Real.log q / q) ^ 4 ≤ (4 * q ^ ((1 / 4 : ℝ)) / q) ^ 4 :=
    pow_le_pow_left₀ hw0' hw 4
  have hrw4 : (4 * q ^ ((1 / 4 : ℝ)) / q) ^ 4 = 256 * q / q ^ 4 := by
    have e1 : (q ^ ((1 / 4 : ℝ))) ^ 4 = q := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hq0.le]
      norm_num
    rw [div_pow, mul_pow, e1]
    ring
  have hq3 : (1000000000 : ℝ) ≤ q ^ 3 := by
    calc (1000000000 : ℝ) = 1000 ^ 3 := by norm_num
      _ ≤ q ^ 3 := pow_le_pow_left₀ (by norm_num) hq 3
  have hfrac : (256 : ℝ) * q / q ^ 4 ≤ 1 / 2985984 := by
    have hq40 : (0 : ℝ) < q ^ 4 := pow_pos hq0 4
    rw [div_le_div_iff₀ hq40 (by norm_num)]
    have h1 : (764411904 : ℝ) ≤ q ^ 3 := by
      have h0 : (764411904 : ℝ) ≤ 1000000000 := by norm_num
      linarith [hq3, h0]
    have h2 : (764411904 : ℝ) * q ≤ q ^ 3 * q :=
      mul_le_mul_of_nonneg_right h1 hq0.le
    have e2 : q ^ 3 * q = q ^ 4 := by ring
    have e3 : (256 : ℝ) * q * 2985984 = 764411904 * q := by ring
    nlinarith [h2, e2, e3]
  have hw4b : (Real.log q / q) ^ 4 ≤ 1 / 2985984 := by
    calc (Real.log q / q) ^ 4 ≤ (4 * q ^ ((1 / 4 : ℝ)) / q) ^ 4 := hw4
      _ = 256 * q / q ^ 4 := hrw4
      _ ≤ 1 / 2985984 := hfrac
  -- `(w⁴)^{1/3} ≤ 1/144`
  have e3 : (((1 / 144 : ℝ)) ^ 3) = 1 / 2985984 := by norm_num
  have hw43 : (Real.log q / q) ^ ((4 / 3 : ℝ)) ≤ 1 / 144 := by
    have e1' : ((((Real.log q / q) ^ 4) ^ ((((3:ℕ)):ℝ)⁻¹)))
        = (Real.log q / q) ^ ((4 / 3 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hw0']
      congr 1
    have e2' : ((((1 / 144 : ℝ)) ^ 3) ^ ((((3:ℕ)):ℝ)⁻¹)) = 1 / 144 :=
      Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)
    rw [← e1', ← e2']
    exact Real.rpow_le_rpow (pow_nonneg hw0' 4)
      (by rw [e3]; exact hw4b) (by norm_num)
  -- `u² = 36w^{4/3} ≤ 1/4`
  have eu2 : (nrU q) ^ 2 = 36 * (Real.log q / q) ^ ((4 / 3 : ℝ)) := by
    have e2 : (((Real.log q / q) ^ ((2 / 3 : ℝ))) ^ 2)
        = (Real.log q / q) ^ ((4 / 3 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hw0']
      congr 1
      norm_num
    unfold nrU
    rw [mul_pow, e2]
    norm_num
  have hle : (nrU q) ^ 2 ≤ (1 / 2) ^ 2 := by
    have h : (36 : ℝ) * ((Real.log q / q) ^ ((4 / 3 : ℝ))) ≤ 36 * (1 / 144) :=
      mul_le_mul_of_nonneg_left hw43 (by norm_num)
    have e : (36 : ℝ) * (1 / 144) = (1 / 2) ^ 2 := by norm_num
    rw [eu2]
    rwa [e] at h
  exact le_of_sq_le_sq hle (by norm_num)
/-- `6^{3/2} ≥ 14.6`. -/
lemma nr_63 : (14.6 : ℝ) ≤ (6 : ℝ) ^ ((3 / 2 : ℝ)) := by
  have g1 : (6 : ℝ) ^ ((3 / 2 : ℝ)) = 6 * Real.sqrt 6 := by
    have f1 : (6 : ℝ) ^ ((3 / 2 : ℝ))
        = (6 : ℝ) ^ ((1 : ℝ)) * (6 : ℝ) ^ ((1 / 2 : ℝ)) := by
      rw [← Real.rpow_add (by norm_num)]
      congr 1
      norm_num
    rw [f1, Real.rpow_one, ← Real.sqrt_eq_rpow]
  have e : ((((6 : ℝ) ^ ((3 / 2 : ℝ)))) ^ 2) = 216 := by
    rw [g1, mul_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have hsq : ((14.6 : ℝ)) ^ 2 ≤ ((((6 : ℝ) ^ ((3 / 2 : ℝ)))) ^ 2) := by
    rw [e]
    norm_num
  exact le_of_sq_le_sq hsq (Real.rpow_nonneg (by norm_num) _)

/-- `u^{3/2} = 6^{3/2}·w` for `u = 6w^{2/3}`. -/
lemma nr_u32 {w u : ℝ} (hw0 : 0 ≤ w) (hu : u = 6 * w ^ ((2 / 3 : ℝ))) :
    u ^ ((3 / 2 : ℝ)) = (6 : ℝ) ^ ((3 / 2 : ℝ)) * w := by
  have e : ((w ^ ((2 / 3 : ℝ))) ^ ((3 / 2 : ℝ))) = w := by
    rw [← Real.rpow_mul hw0, show ((2/3:ℝ))*(3/2) = 1 by norm_num,
      Real.rpow_one]
  calc u ^ ((3 / 2 : ℝ)) = (6 * w ^ ((2 / 3 : ℝ))) ^ ((3 / 2 : ℝ)) := by
        rw [hu]
    _ = (6 : ℝ) ^ ((3 / 2 : ℝ)) * (w ^ ((2 / 3 : ℝ))) ^ ((3 / 2 : ℝ)) :=
        Real.mul_rpow (by norm_num) (Real.rpow_nonneg hw0 _)
    _ = (6 : ℝ) ^ ((3 / 2 : ℝ)) * w := by
        rw [e]

/-- `(2u)^{-5/2}·u^{-3/4} ≤ u^{-13/4}`. -/
lemma nr_u34 {u : ℝ} (hu0 : 0 < u) :
    (2 * u) ^ (-(5 / 2 : ℝ)) * u ^ (-(3 / 4 : ℝ)) ≤ u ^ (-(13 / 4 : ℝ)) := by
  have e : (2 * u) ^ (-(5 / 2 : ℝ))
      = (2 : ℝ) ^ (-(5 / 2 : ℝ)) * u ^ (-(5 / 2 : ℝ)) :=
    Real.mul_rpow (by norm_num) hu0.le
  have h2 : (2 : ℝ) ^ (-(5 / 2 : ℝ)) ≤ 1 := by
    have h := Real.rpow_le_rpow_of_nonpos (show (0:ℝ) < 1 by norm_num)
      (show (1:ℝ) ≤ 2 by norm_num) (show (-(5 / 2 : ℝ)) ≤ 0 by norm_num)
    rwa [Real.one_rpow] at h
  calc (2 * u) ^ (-(5 / 2 : ℝ)) * u ^ (-(3 / 4 : ℝ))
      = ((2 : ℝ) ^ (-(5 / 2 : ℝ)) * u ^ (-(5 / 2 : ℝ))) * u ^ (-(3 / 4 : ℝ)) := by
        rw [e]
    _ ≤ (1 * u ^ (-(5 / 2 : ℝ))) * u ^ (-(3 / 4 : ℝ)) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hu0.le _)
        exact mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hu0.le _)
    _ = u ^ (-(13 / 4 : ℝ)) := by
        rw [one_mul, ← Real.rpow_add hu0]
        congr 1
        norm_num

/-- `q²·q^{-1/2} ≤ q^{3/2}` (equality). -/
lemma nr_q32 {q : ℝ} (hq0 : 0 < q) :
    (q : ℝ) ^ 2 * (q : ℝ) ^ (-(1 / 2 : ℝ)) ≤ (q : ℝ) ^ ((3 / 2 : ℝ)) := by
  have e : (q : ℝ) ^ 2 * (q : ℝ) ^ (-(1 / 2 : ℝ)) = (q : ℝ) ^ ((3 / 2 : ℝ)) := by
    have f : ((q : ℝ) ^ 2) = (q : ℝ) ^ ((2 : ℝ)) := (Real.rpow_natCast q 2).symm
    rw [f, ← Real.rpow_add hq0]
    congr 1
    norm_num
  exact le_of_eq e

/-- `log 15500 ≤ 10`. -/
lemma nr_log15500 : Real.log 15500 ≤ 10 := by
  have hexp10 : (15500 : ℝ) ≤ Real.exp 10 := by
    have e1 : Real.exp (10 : ℝ) = (Real.exp 1) ^ 10 := by
      have h10 : (10 : ℝ) = ((10 : ℕ) : ℝ) * 1 := by norm_num
      rw [h10, Real.exp_nat_mul]
    have e2 : (2.7 : ℝ) ^ 10 ≤ (Real.exp 1) ^ 10 := by
      apply pow_le_pow_left₀ (by norm_num) _ 10
      have h := Real.exp_one_gt_d9
      linarith [h]
    have e3 : (15500 : ℝ) ≤ (2.7 : ℝ) ^ 10 := by norm_num
    rw [e1]
    linarith [e2, e3]
  calc Real.log 15500 ≤ Real.log (Real.exp 10) :=
        Real.log_le_log (by norm_num) hexp10
    _ = 10 := Real.log_exp _
/-- `E2*` is nonnegative. -/
lemma nrE2star_nonneg {τ : ℝ} {q : ℕ} (hα : 0 ≤ besselAlpha τ (q : ℝ)) :
    0 ≤ nrE2star τ q := by
  unfold nrE2star
  apply div_nonneg _ _
  · positivity
  · exact mul_nonneg (Real.sqrt_nonneg _)
      (sub_nonneg.mpr (by
        have h : Real.exp (-(besselAlpha τ (q : ℝ))) ≤ Real.exp 0 :=
          Real.exp_le_exp.mpr (by linarith [hα])
        rwa [Real.exp_zero] at h))

/-- Master product bound. -/
lemma nr_master_bound {τ : ℝ} {q : ℕ} {u : ℝ}
    (hq0 : 0 < (q : ℝ)) (hu0 : 0 < u)
    (hCcal : nrCcal τ q ≤ 6144 * (2 * u) ^ (-(5 / 2 : ℝ)))
    (hE2 : nrE2star τ q ≤ 2.52 * Real.exp (-(besselF τ (q : ℝ)))
      * ((q : ℝ) ^ (-(1 / 2 : ℝ)) * u ^ (-(3 / 4 : ℝ))))
    (hE2nn : 0 ≤ nrE2star τ q)
    (hCnn : 0 ≤ nrCcal τ q * (q : ℝ) ^ 2)
    (hu34 : (2 * u) ^ (-(5 / 2 : ℝ)) * u ^ (-(3 / 4 : ℝ))
      ≤ u ^ (-(13 / 4 : ℝ)))
    (hq32 : (q : ℝ) ^ 2 * (q : ℝ) ^ (-(1 / 2 : ℝ))
      ≤ (q : ℝ) ^ ((3 / 2 : ℝ))) :
    nrCcal τ q * (q : ℝ) ^ 2 * nrE2star τ q
      ≤ 15500 * Real.exp (-(besselF τ (q : ℝ)))
        * ((q : ℝ) ^ ((3 / 2 : ℝ)) * u ^ (-(13 / 4 : ℝ))) := by
  have hq2nn : (0 : ℝ) ≤ (q : ℝ) ^ 2 := pow_nonneg hq0.le 2
  have hCnn' : (0 : ℝ) ≤ 6144 * (2 * u) ^ (-(5 / 2 : ℝ)) :=
    mul_nonneg (by norm_num) (Real.rpow_nonneg (by positivity) _)
  have h1 : nrCcal τ q * (q : ℝ) ^ 2
      ≤ (6144 * (2 * u) ^ (-(5 / 2 : ℝ))) * ((q : ℝ) ^ 2) :=
    mul_le_mul hCcal (le_refl _) hq2nn hCnn'
  have h2 : nrCcal τ q * (q : ℝ) ^ 2 * nrE2star τ q
      ≤ (6144 * (2 * u) ^ (-(5 / 2 : ℝ))) * ((q : ℝ) ^ 2)
        * (2.52 * Real.exp (-(besselF τ (q : ℝ)))
          * ((q : ℝ) ^ (-(1 / 2 : ℝ)) * u ^ (-(3 / 4 : ℝ)))) :=
    mul_le_mul h1 hE2 hE2nn
      (mul_nonneg hCnn' hq2nn)
  have h3 : (6144 * (2 * u) ^ (-(5 / 2 : ℝ))) * ((q : ℝ) ^ 2)
      * (2.52 * Real.exp (-(besselF τ (q : ℝ)))
        * ((q : ℝ) ^ (-(1 / 2 : ℝ)) * u ^ (-(3 / 4 : ℝ))))
      = (6144 * 2.52) * Real.exp (-(besselF τ (q : ℝ)))
        * (((q : ℝ) ^ 2 * (q : ℝ) ^ (-(1 / 2 : ℝ)))
          * ((2 * u) ^ (-(5 / 2 : ℝ)) * u ^ (-(3 / 4 : ℝ)))) := by
    ring
  rw [h3] at h2
  set A : ℝ := (q : ℝ) ^ 2 * (q : ℝ) ^ (-(1 / 2 : ℝ)) with hAdef
  set B : ℝ := (2 * u) ^ (-(5 / 2 : ℝ)) * u ^ (-(3 / 4 : ℝ)) with hBdef
  set A' : ℝ := (q : ℝ) ^ ((3 / 2 : ℝ)) with hA'def
  set B' : ℝ := u ^ (-(13 / 4 : ℝ)) with hB'def
  set Cc : ℝ := (6144 * 2.52) * Real.exp (-(besselF τ (q : ℝ))) with hCdef
  have h4 : A * B ≤ A' * B' :=
    mul_le_mul hq32 hu34
      (mul_nonneg (Real.rpow_nonneg (by positivity) _)
        (Real.rpow_nonneg hu0.le _))
      (Real.rpow_nonneg hq0.le _)
  have hCcnn : (0 : ℝ) ≤ Cc := by
    rw [hCdef]
    positivity
  have h5 : Cc * (A * B) ≤ Cc * (A' * B') :=
    mul_le_mul_of_nonneg_left h4 hCcnn
  have h6 : Cc * (A' * B')
      ≤ 15500 * Real.exp (-(besselF τ (q : ℝ))) * (A' * B') := by
    have hc : (6144 * 2.52 : ℝ) ≤ 15500 := by norm_num
    have hE : (0 : ℝ) ≤ Real.exp (-(besselF τ (q : ℝ))) * (A' * B') := by
      positivity
    rw [hCdef]
    calc ((6144 * 2.52) * Real.exp (-(besselF τ (q : ℝ)))) * (A' * B')
        = (6144 * 2.52) * (Real.exp (-(besselF τ (q : ℝ))) * (A' * B')) := by
          ring
      _ ≤ 15500 * (Real.exp (-(besselF τ (q : ℝ))) * (A' * B')) :=
          mul_le_mul_of_nonneg_right hc hE
      _ = 15500 * Real.exp (-(besselF τ (q : ℝ))) * (A' * B') := by
          ring
  exact h2.trans (h5.trans h6)
/-- Closed form, finitized L6.1: `T ≥ 4(N+1)[1-6(log q/q)^{2/3}]`, `c = 6`. -/
theorem nr_closed_form {N : ℕ} {φ : ℝ} {L : ℕ} {α θ : Fin L → ℝ} (C : nrCheb)
    (hφ0 : 0 < φ) (hφπ : φ ≤ Real.pi)
    (hAdm : Admissible N φ L α θ)
    (hqN : C.q = 2 * N + 2)
    (hCτ : C.τ = ((2*N+2 : ℕ):ℝ) * (1 - nrU ((2*N+2 : ℕ):ℝ)))
    (s0 : ℝ) (hs0 : 0 < s0) (hs0le : s0 ≤ Real.sin (φ / 4) ^ 2)
    (hN : 500 + ⌈Real.exp ((11 + |Real.log s0|) / 1.2)⌉₊ ≤ N) :
    4 * ((N : ℝ) + 1) * (1 - nrU ((2*N+2 : ℕ):ℝ)) ≤ cost θ := by
  set qr : ℝ := ((2*N+2 : ℕ):ℝ) with hqrdef
  have hCqR : (C.q : ℝ) = qr := by rw [hqN, hqrdef]
  have hN500 : 500 ≤ N := by omega
  have hqr1000 : (1000 : ℝ) ≤ qr := by
    rw [hqrdef]
    have h : (1000 : ℕ) ≤ 2 * N + 2 := by omega
    calc (1000 : ℝ) = ((1000 : ℕ) : ℝ) := by norm_num
      _ ≤ ((2 * N + 2 : ℕ) : ℝ) := Nat.cast_le.mpr h
  have hqr0 : (0 : ℝ) < qr := by linarith
  have hqr0' : qr ≠ 0 := ne_of_gt hqr0
  have hlogL : (11 + |Real.log s0|) / 1.2 ≤ Real.log qr := by
    have hexp : Real.exp ((11 + |Real.log s0|) / 1.2) ≤ qr := by
      have h1 : Real.exp ((11 + |Real.log s0|) / 1.2)
          ≤ ((⌈Real.exp ((11 + |Real.log s0|) / 1.2)⌉₊ : ℕ) : ℝ) :=
        Nat.le_ceil _
      have h2 : ⌈Real.exp ((11 + |Real.log s0|) / 1.2)⌉₊ ≤ N := by omega
      have h3 : ((⌈Real.exp ((11 + |Real.log s0|) / 1.2)⌉₊ : ℕ) : ℝ)
          ≤ ((N : ℕ) : ℝ) :=
        Nat.cast_le.mpr h2
      have h4 : ((N : ℕ) : ℝ) ≤ qr := by
        rw [hqrdef]
        exact_mod_cast (show N ≤ 2 * N + 2 by omega)
      linarith [h1, h3, h4]
    exact (Real.le_log_iff_exp_le hqr0).mpr hexp
  have hlog1 : 1 ≤ Real.log qr := by
    have habs : (0 : ℝ) ≤ |Real.log s0| := abs_nonneg _
    have h8 : 11 + |Real.log s0| ≤ 1.2 * Real.log qr := by
      have h := hlogL
      rw [div_le_iff₀ (by norm_num)] at h
      linarith [h]
    linarith [h8, habs]
  have hu := nr_u_bounds qr hqr1000 hlog1
  obtain ⟨hu0, hu2⟩ := hu
  have hwpos : (0 : ℝ) < Real.log qr / qr := div_pos (by linarith) hqr0
  have hwpos' : (0 : ℝ) ≤ Real.log qr / qr := hwpos.le
  have hτpos : 0 < C.τ := by
    rw [hCτ]
    apply mul_pos hqr0
    linarith [hu2]
  have hτq : C.τ < qr := by
    rw [hCτ]
    have hlt : qr * (1 - nrU qr) < qr * 1 :=
      mul_lt_mul_of_pos_left (by linarith [hu0]) hqr0
    rwa [mul_one] at hlt
  have hqq : qr ^ 2 * nrU qr ≤ qr ^ 2 - C.τ ^ 2 := by
    have e : qr ^ 2 - C.τ ^ 2 = qr ^ 2 * (2 * nrU qr - (nrU qr) ^ 2) := by
      rw [hCτ]
      ring
    rw [e]
    have hle : nrU qr ≤ 2 * nrU qr - (nrU qr) ^ 2 := by
      have hpos : (0 : ℝ) ≤ nrU qr * (1 - nrU qr) :=
        mul_nonneg hu0.le (by linarith [hu2])
      nlinarith [hpos]
    exact mul_le_mul_of_nonneg_left hle (pow_nonneg hqr0.le 2)
  have hα : Real.sqrt (2 * nrU qr) ≤ besselAlpha C.τ qr := by
    have e : qr / C.τ = 1 / (1 - nrU qr) := by
      rw [hCτ]
      have hu1 : (1 : ℝ) - nrU qr ≠ 0 := ne_of_gt (by linarith [hu2])
      field_simp
    have h := nr_alpha_ge_sqrt hu0.le hu2
    unfold besselAlpha
    rwa [e]
  have hαpos : 0 < besselAlpha C.τ qr := by
    have hsq : (0 : ℝ) < Real.sqrt (2 * nrU qr) :=
      Real.sqrt_pos.mpr (by positivity)
    linarith [hα, hsq]
  have hα0 : 0 ≤ besselAlpha C.τ (C.q : ℝ) := by
    rw [hCqR]
    exact hαpos.le
  have hr : nrR C.τ C.q = Real.exp (-(besselAlpha C.τ qr)) := by
    unfold nrR
    rw [hCqR]
  have hr0 := nrR_nonneg C.τ C.q
  have hr1 : nrR C.τ C.q < 1 := by
    have hpos : 0 < besselAlpha C.τ (C.q : ℝ) := by
      rw [hCqR]
      exact hαpos
    exact nrR_lt_one hpos
  have heta1 : 1 ≤ nrEta1of C.τ C.q := nrEta1_ge_one hr0 hr1
  have heta12 : nrEta1of C.τ C.q ≤ nrEta2of C.τ C.q :=
    nrEta1_le_eta2 hr0 hr1
  have heta2nn : 0 ≤ nrEta2of C.τ C.q := nrEta2_nonneg hr0 hr1
  have heta2 : nrEta2of C.τ C.q ≤ 768 * (2 * nrU qr) ^ (-(5 / 2 : ℝ)) := by
    have heta : nrEta2of C.τ C.q = nrEta2 (nrR C.τ C.q) := rfl
    exact nr_eta2_le_768 hr hαpos hα hu0 hu2 heta
  have hq2 : (2 : ℝ) ≤ qr := by linarith [hqr1000]
  have hq2' : (2 : ℝ) ≤ (C.q : ℝ) := by
    rw [hCqR]
    exact hq2
  have hccal : nrCcal C.τ C.q ≤ 6144 * (2 * nrU qr) ^ (-(5 / 2 : ℝ)) :=
    nr_ccal_le hq2' (by linarith [hτpos]) heta1 heta12 heta2nn heta2
  have hαinv : 1 / (1 - Real.exp (-(besselAlpha C.τ (C.q : ℝ))))
      ≤ 2 * (2 * nrU qr) ^ (-(1 / 2 : ℝ)) := by
    have h1 : 0 < besselAlpha C.τ (C.q : ℝ) := by
      rw [hCqR]
      exact hαpos
    have h2 : Real.sqrt (2 * nrU qr) ≤ besselAlpha C.τ (C.q : ℝ) := by
      rw [hCqR]
      exact hα
    exact nr_tfactor_le h1 h2 hu0 hu2
  have he2 : nrE2star C.τ C.q ≤ 2.52 * Real.exp (-(besselF C.τ (C.q : ℝ)))
      * ((C.q : ℝ) ^ (-(1 / 2 : ℝ)) * (nrU qr) ^ (-(3 / 4 : ℝ))) := by
    have hqr0' : (0 : ℝ) < (C.q : ℝ) := by
      rw [hCqR]
      exact hqr0
    have hqq' : (C.q : ℝ) ^ 2 * nrU qr ≤ (C.q : ℝ) ^ 2 - C.τ ^ 2 := by
      rw [hCqR]
      exact hqq
    exact nr_e2star_le hqr0' hu0 hα0 hqq' hαinv
  have hfQr : qr * ((nrU qr) ^ ((3 / 2 : ℝ))) / 3
      ≤ qr * besselAlpha C.τ qr - Real.sqrt (qr ^ 2 - C.τ ^ 2) :=
    nr_f_ge hqr0 hu0 hu2 hCτ
  have hu32 : (nrU qr) ^ ((3 / 2 : ℝ))
      = (6 : ℝ) ^ ((3 / 2 : ℝ)) * (Real.log qr / qr) := by
    have hu_eq : nrU qr = 6 * ((Real.log qr / qr) ^ ((2 / 3 : ℝ))) := rfl
    have h := nr_u32 hwpos' hu_eq
    exact h
  have hw32 : (14.6 : ℝ) * (Real.log qr / qr) ≤ (nrU qr) ^ ((3 / 2 : ℝ)) := by
    rw [hu32]
    exact mul_le_mul_of_nonneg_right nr_63 hwpos'
  have hf : (14.6 / 3) * Real.log qr ≤ besselF C.τ C.q := by
    have h1 : qr * ((nrU qr) ^ ((3 / 2 : ℝ))) / 3
        ≤ qr * besselAlpha C.τ qr - Real.sqrt (qr ^ 2 - C.τ ^ 2) := hfQr
    have h2 : qr * ((14.6) * (Real.log qr / qr)) / 3
        ≤ qr * ((nrU qr) ^ ((3 / 2 : ℝ))) / 3 := by
      have h := mul_le_mul_of_nonneg_left hw32 (show (0:ℝ) ≤ qr / 3 by positivity)
      linarith [h]
    have h3 : (14.6 / 3) * Real.log qr
        = qr * ((14.6) * (Real.log qr / qr)) / 3 := by
      field_simp
    have h4 : besselF C.τ C.q
        = qr * besselAlpha C.τ qr - Real.sqrt (qr ^ 2 - C.τ ^ 2) := by
      unfold besselF
      rw [hCqR]
    rw [h4, h3]
    exact h2.trans h1
  have hu13 : (nrU qr) ^ (-(13 / 4 : ℝ)) ≤ qr ^ ((13 / 6 : ℝ)) := by
    have e1 : (nrU qr) ^ (-(13 / 4 : ℝ))
        = (6 : ℝ) ^ (-(13 / 4 : ℝ)) * ((Real.log qr / qr)) ^ (-(13 / 6 : ℝ)) := by
      have hu_eq : nrU qr = 6 * ((Real.log qr / qr) ^ ((2 / 3 : ℝ))) := rfl
      rw [hu_eq, Real.mul_rpow (by norm_num) (Real.rpow_nonneg hwpos' _),
        ← Real.rpow_mul hwpos']
      congr 1
      norm_num
    have e2 : (6 : ℝ) ^ (-(13 / 4 : ℝ)) ≤ 1 := by
      have h := Real.rpow_le_rpow_of_nonpos (show (0:ℝ) < 1 by norm_num)
        (show (1:ℝ) ≤ 6 by norm_num) (show (-(13 / 4 : ℝ)) ≤ 0 by norm_num)
      rwa [Real.one_rpow] at h
    have e3 : ((Real.log qr / qr)) ^ (-(13 / 6 : ℝ)) ≤ qr ^ ((13 / 6 : ℝ)) := by
      have h1 : (1 : ℝ)
          ≤ (qr ^ ((13 / 6 : ℝ))) * (((Real.log qr / qr)) ^ ((13 / 6 : ℝ))) := by
        have e : (qr ^ ((13 / 6 : ℝ))) * (((Real.log qr / qr)) ^ ((13 / 6 : ℝ)))
            = (Real.log qr) ^ ((13 / 6 : ℝ)) := by
          rw [← Real.mul_rpow (by positivity) (by positivity)]
          congr 1
          field_simp
        rw [e]
        calc (1 : ℝ) = (1 : ℝ) ^ ((13 / 6 : ℝ)) := (Real.one_rpow _).symm
          _ ≤ (Real.log qr) ^ ((13 / 6 : ℝ)) :=
              Real.rpow_le_rpow (by norm_num) hlog1 (by norm_num)
      have hB : (0 : ℝ) < ((Real.log qr / qr)) ^ ((13 / 6 : ℝ)) :=
        Real.rpow_pos_of_pos hwpos _
      have hA : ((Real.log qr / qr)) ^ (-(13 / 6 : ℝ))
          = 1 / (((Real.log qr / qr)) ^ ((13 / 6 : ℝ))) := by
        rw [Real.rpow_neg hwpos']
        rw [inv_eq_one_div]
      rw [hA]
      have hC : (1 : ℝ) / (((Real.log qr / qr)) ^ ((13 / 6 : ℝ)))
          ≤ qr ^ ((13 / 6 : ℝ)) := by
        -- `1/B ≤ C ⟺ 1 ≤ C*B`
        have hD : (1 : ℝ)
            ≤ (qr ^ ((13 / 6 : ℝ))) * (((Real.log qr / qr)) ^ ((13 / 6 : ℝ))) := h1
        have hE : (1 : ℝ) / (((Real.log qr / qr)) ^ ((13 / 6 : ℝ)))
            ≤ qr ^ ((13 / 6 : ℝ)) := by
          rw [div_le_iff₀ hB]
          linarith [hD]
        exact hE
      exact hC
    calc (nrU qr) ^ (-(13 / 4 : ℝ))
        = (6 : ℝ) ^ (-(13 / 4 : ℝ)) * ((Real.log qr / qr)) ^ (-(13 / 6 : ℝ)) := e1
      _ ≤ 1 * qr ^ ((13 / 6 : ℝ)) :=
          mul_le_mul e2 e3 (by positivity) (by norm_num)
      _ = qr ^ ((13 / 6 : ℝ)) := one_mul _
  have hCnn : 0 ≤ nrCcal C.τ C.q * (C.q : ℝ) ^ 2 := by
    have hqC : (0 : ℝ) < (C.q : ℝ) := by
      rw [hCqR]
      exact hqr0
    exact mul_nonneg (nrCcal_nonneg _ _ hqC) (pow_nonneg hqC.le 2)
  have hE2nn : 0 ≤ nrE2star C.τ C.q := by
    have hαC : 0 ≤ besselAlpha C.τ (C.q : ℝ) := by
      rw [hCqR]
      exact hαpos.le
    exact nrE2star_nonneg hαC
  have hq32 : (C.q : ℝ) ^ 2 * (C.q : ℝ) ^ (-(1 / 2 : ℝ))
      ≤ (C.q : ℝ) ^ ((3 / 2 : ℝ)) := by
    have hqC : (0 : ℝ) < (C.q : ℝ) := by
      rw [hCqR]
      exact hqr0
    exact nr_q32 hqC
  have hu34 : (2 * nrU qr) ^ (-(5 / 2 : ℝ)) * (nrU qr) ^ (-(3 / 4 : ℝ))
      ≤ (nrU qr) ^ (-(13 / 4 : ℝ)) :=
    nr_u34 hu0
  have hqr0' : (0 : ℝ) < (C.q : ℝ) := by
    rw [hCqR]
    exact hqr0
  have hprod : nrCcal C.τ C.q * (C.q : ℝ) ^ 2 * nrE2star C.τ C.q
      ≤ 15500 * Real.exp (-(besselF C.τ C.q))
        * (((C.q : ℝ) ^ ((3 / 2 : ℝ))) * (nrU qr) ^ (-(13 / 4 : ℝ))) :=
    nr_master_bound hqr0' hu0 hccal he2 hE2nn hCnn hu34 hq32
  have hcomb : ((C.q : ℝ) ^ ((3 / 2 : ℝ))) * (nrU qr) ^ (-(13 / 4 : ℝ))
      ≤ qr ^ ((11 / 3 : ℝ)) := by
    have e1 : ((C.q : ℝ) ^ ((3 / 2 : ℝ))) = qr ^ ((3 / 2 : ℝ)) := by
      rw [hCqR]
    rw [e1]
    have h1 : qr ^ ((3 / 2 : ℝ)) * (nrU qr) ^ (-(13 / 4 : ℝ))
        ≤ qr ^ ((3 / 2 : ℝ)) * qr ^ ((13 / 6 : ℝ)) :=
      mul_le_mul_of_nonneg_left hu13 (Real.rpow_nonneg hqr0.le _)
    have h2 : qr ^ ((3 / 2 : ℝ)) * qr ^ ((13 / 6 : ℝ)) = qr ^ ((11 / 3 : ℝ)) := by
      rw [← Real.rpow_add hqr0]
      congr 1
      norm_num
    rwa [h2] at h1
  have hprod2 : nrCcal C.τ C.q * (C.q : ℝ) ^ 2 * nrE2star C.τ C.q
      ≤ 15500 * Real.exp (-(besselF C.τ C.q)) * (qr ^ ((11 / 3 : ℝ))) :=
    hprod.trans (mul_le_mul_of_nonneg_left hcomb (by positivity))
  -- log step
  have hXpos : (0 : ℝ)
      < 15500 * Real.exp (-(besselF C.τ C.q)) * (qr ^ ((11 / 3 : ℝ))) := by
    positivity
  have hlogX : Real.log (15500 * Real.exp (-(besselF C.τ C.q)) * (qr ^ ((11 / 3 : ℝ))))
      < Real.log s0 := by
    have e : Real.log (15500 * Real.exp (-(besselF C.τ C.q)) * (qr ^ ((11 / 3 : ℝ))))
        = Real.log 15500 + (-(besselF C.τ C.q)) + (11 / 3) * Real.log qr := by
      have hX1 : (0 : ℝ) < 15500 * Real.exp (-(besselF C.τ C.q)) := by
        positivity
      have hX2 : (0 : ℝ) < qr ^ ((11 / 3 : ℝ)) :=
        Real.rpow_pos_of_pos hqr0 _
      have hX1ne : (15500 * Real.exp (-(besselF C.τ C.q))) ≠ 0 :=
        ne_of_gt hX1
      have hX2ne : (qr ^ ((11 / 3 : ℝ))) ≠ 0 := ne_of_gt hX2
      have he1 : (15500 : ℝ) ≠ 0 := by norm_num
      have he2 : Real.exp (-(besselF C.τ C.q)) ≠ 0 :=
        ne_of_gt (Real.exp_pos _)
      rw [Real.log_mul hX1ne hX2ne, Real.log_mul he1 he2,
        Real.log_exp, Real.log_rpow hqr0]
    have hlog15500 := nr_log15500
    have hs0neg : -Real.log s0 ≤ |Real.log s0| := by
      have h := le_abs_self (-Real.log s0)
      rwa [abs_neg] at h
    have hlogL' : 11 + |Real.log s0| ≤ 1.2 * Real.log qr := by
      have h := hlogL
      rw [div_le_iff₀ (by norm_num)] at h
      linarith [h]
    linarith [hlog15500, hf, hlogL', hs0neg]
  have hXlt : 15500 * Real.exp (-(besselF C.τ C.q)) * (qr ^ ((11 / 3 : ℝ))) < s0 := by
    have e1 : (15500 * Real.exp (-(besselF C.τ C.q)) * (qr ^ ((11 / 3 : ℝ))))
        = Real.exp (Real.log (15500 * Real.exp (-(besselF C.τ C.q))
          * (qr ^ ((11 / 3 : ℝ))))) :=
      (Real.exp_log hXpos).symm
    have e2 : s0 = Real.exp (Real.log s0) := (Real.exp_log hs0).symm
    rw [e1, e2]
    exact Real.exp_lt_exp.mpr hlogX
  have hmain : nrCcal C.τ C.q * (C.q : ℝ) ^ 2 * nrE2star C.τ C.q
      < Real.sin (φ / 4) ^ 2 :=
    ((hprod2.trans_lt hXlt).trans_le hs0le)
  have hfin := nr_main_rung C (show 1 ≤ N by omega) hφ0 hφπ hAdm hqN hmain
  rw [hCτ] at hfin
  have efin : (2 : ℝ) * (qr * (1 - nrU qr))
      = 4 * ((N : ℝ) + 1) * (1 - nrU ((2 * N + 2 : ℕ):ℝ)) := by
    rw [hqrdef]
    push_cast
    ring
  rw [efin] at hfin
  exact le_of_lt hfin

end RobustZ

