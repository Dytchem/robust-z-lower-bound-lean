/-
# L¹ bound for kernels with a sup bound and a quadratic decay bound

If `κ : ℝ → ℂ` satisfies `‖κ t‖ ≤ C₁` everywhere and `‖κ t‖ ≤ C₂ / t²` off the origin,
then the (Lebesgue) L¹ norm of `‖κ ·‖` is bounded by `2 R C₁ + 2 C₂ / R` for every `R > 0`
(split the line into `|t| ≤ R` and `|t| > R`), and by `4 √(C₁ C₂)` after optimising `R`.

The second bound is proved as a standalone statement (`integral_norm_le_sqrt`); note that
the constant `4` is optimal: the even kernel `t ↦ min C₁ (C₂ / t²)` has L¹ norm exactly
`4 √(C₁ C₂)`, so no better constant can hold with these two hypotheses alone.
-/
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Tactic

noncomputable section

open scoped Real
open Filter MeasureTheory

namespace RobustZ

/-! ### The tail integrals of `t ↦ (t ^ 2)⁻¹` -/

/-- `t ↦ (t ^ 2)⁻¹` is integrable on the right half-line `(R, ∞)`. -/
lemma integrableOn_inv_sq_Ioi {R : ℝ} (hR : 0 < R) :
    IntegrableOn (fun t : ℝ => (t ^ 2)⁻¹) (Set.Ioi R) := by
  refine (integrableOn_Ioi_rpow_of_lt (a := -2) (by norm_num) hR).congr_fun ?_ measurableSet_Ioi
  intro t ht
  show t ^ (-2 : ℝ) = (t ^ 2)⁻¹
  rw [Real.rpow_neg (le_of_lt (hR.trans (Set.mem_Ioi.mp ht))), Real.rpow_two]

/-- `∫_{R}^{∞} t⁻² dt = 1 / R`. -/
lemma integral_inv_sq_Ioi {R : ℝ} (hR : 0 < R) :
    ∫ t in Set.Ioi R, (t ^ 2)⁻¹ = R⁻¹ := by
  have hmain : ∫ t in Set.Ioi R, t ^ (-2 : ℝ) = R⁻¹ := by
    rw [integral_Ioi_rpow_of_lt (a := -2) (by norm_num) hR,
      show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
    ring
  have hcongr : ∫ t in Set.Ioi R, (t ^ 2)⁻¹ = ∫ t in Set.Ioi R, t ^ (-2 : ℝ) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    show (t ^ 2)⁻¹ = t ^ (-2 : ℝ)
    rw [Real.rpow_neg (le_of_lt (hR.trans (Set.mem_Ioi.mp ht))), Real.rpow_two]
  rw [hcongr, hmain]

/-- `t ↦ (t ^ 2)⁻¹` is integrable on the left half-line `(-∞, -R]`. -/
lemma integrableOn_inv_sq_Iic {R : ℝ} (hR : 0 < R) :
    IntegrableOn (fun t : ℝ => (t ^ 2)⁻¹) (Set.Iic (-R)) := by
  have h0 : IntegrableOn (fun t : ℝ => (t ^ 2)⁻¹) (Set.Ioi (-(-R))) := by
    simpa using integrableOn_inv_sq_Ioi hR
  have h1 : IntegrableOn (fun t : ℝ => ((-t) ^ 2)⁻¹) (Set.Iio (-R)) :=
    h0.comp_neg_Iio (c := -R)
  have h2 : IntegrableOn (fun t : ℝ => (t ^ 2)⁻¹) (Set.Iio (-R)) := by
    refine h1.congr_fun (fun t _ => ?_) measurableSet_Iio
    show ((-t) ^ 2)⁻¹ = (t ^ 2)⁻¹
    rw [show (-t) ^ 2 = t ^ 2 by ring]
  rw [integrableOn_Iic_iff_integrableOn_Iio]
  exact h2

/-- `∫_{-∞}^{-R} t⁻² dt = 1 / R`. -/
lemma integral_inv_sq_Iic {R : ℝ} (hR : 0 < R) :
    ∫ t in Set.Iic (-R), (t ^ 2)⁻¹ = R⁻¹ := by
  have hswap : ∫ t in Set.Iic (-R), (t ^ 2)⁻¹ = ∫ t in Set.Ioi R, ((-t) ^ 2)⁻¹ :=
    (integral_comp_neg_Ioi R (fun t : ℝ => (t ^ 2)⁻¹)).symm
  have hcongr : ∫ t in Set.Ioi R, ((-t) ^ 2)⁻¹ = ∫ t in Set.Ioi R, (t ^ 2)⁻¹ := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    show ((-t) ^ 2)⁻¹ = (t ^ 2)⁻¹
    rw [show (-t) ^ 2 = t ^ 2 by ring]
  rw [hswap, hcongr, integral_inv_sq_Ioi hR]

/-! ### The split bound -/

/-- **L¹ bound, split form.**  A kernel bounded by `C₁` everywhere and by `C₂ / t²` off the
origin has L¹ norm at most `2 R C₁ + 2 C₂ / R`, for any `R > 0`. -/
theorem integral_norm_le_split (κ : ℝ → ℂ) {C₁ C₂ R : ℝ}
    (hC1 : ∀ t, ‖κ t‖ ≤ C₁) (hC2 : ∀ t, t ≠ 0 → ‖κ t‖ ≤ C₂ / t ^ 2)
    (hR : 0 < R) (hC1nn : 0 ≤ C₁) (hC2nn : 0 ≤ C₂) :
    ∫ t : ℝ, ‖κ t‖ ≤ 2 * R * C₁ + 2 * C₂ / R := by
  by_cases hint : Integrable fun t : ℝ => ‖κ t‖
  · -- middle piece `|t| ≤ R`
    have hmid : ∫ t in Set.Ioc (-R) R, ‖κ t‖ ≤ 2 * R * C₁ := by
      have hmono : ∫ t in Set.Ioc (-R) R, ‖κ t‖ ≤ ∫ t in Set.Ioc (-R) R, C₁ :=
        setIntegral_mono_on hint.integrableOn
          (integrableOn_const (C := C₁) (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top))
          measurableSet_Ioc (fun t _ => hC1 t)
      calc ∫ t in Set.Ioc (-R) R, ‖κ t‖ ≤ ∫ t in Set.Ioc (-R) R, C₁ := hmono
        _ = volume.real (Set.Ioc (-R) R) * C₁ := by rw [setIntegral_const, smul_eq_mul]
        _ = 2 * R * C₁ := by rw [Real.volume_real_Ioc_of_le (by linarith)]; ring
    -- right tail `t > R`
    have hright : ∫ t in Set.Ioi R, ‖κ t‖ ≤ C₂ * R⁻¹ := by
      have hmono : ∫ t in Set.Ioi R, ‖κ t‖ ≤ ∫ t in Set.Ioi R, C₂ * (t ^ 2)⁻¹ :=
        setIntegral_mono_on hint.integrableOn
          ((integrableOn_inv_sq_Ioi hR).const_mul C₂) measurableSet_Ioi
          (fun t ht => by
            have ht0 : t ≠ 0 := ne_of_gt (hR.trans (Set.mem_Ioi.mp ht))
            simpa only [div_eq_mul_inv] using hC2 t ht0)
      calc ∫ t in Set.Ioi R, ‖κ t‖ ≤ ∫ t in Set.Ioi R, C₂ * (t ^ 2)⁻¹ := hmono
        _ = C₂ * ∫ t in Set.Ioi R, (t ^ 2)⁻¹ := by rw [integral_const_mul]
        _ = C₂ * R⁻¹ := by rw [integral_inv_sq_Ioi hR]
    -- left tail `t ≤ -R`
    have hleft : ∫ t in Set.Iic (-R), ‖κ t‖ ≤ C₂ * R⁻¹ := by
      have hmono : ∫ t in Set.Iic (-R), ‖κ t‖ ≤ ∫ t in Set.Iic (-R), C₂ * (t ^ 2)⁻¹ :=
        setIntegral_mono_on hint.integrableOn
          ((integrableOn_inv_sq_Iic hR).const_mul C₂) measurableSet_Iic
          (fun t ht => by
            have ht0 : t ≠ 0 := ne_of_lt (by linarith [Set.mem_Iic.mp ht, hR])
            simpa only [div_eq_mul_inv] using hC2 t ht0)
      calc ∫ t in Set.Iic (-R), ‖κ t‖ ≤ ∫ t in Set.Iic (-R), C₂ * (t ^ 2)⁻¹ := hmono
        _ = C₂ * ∫ t in Set.Iic (-R), (t ^ 2)⁻¹ := by rw [integral_const_mul]
        _ = C₂ * R⁻¹ := by rw [integral_inv_sq_Iic hR]
    -- split the line at `Ioc (-R) R`
    have hsplit : (∫ t : ℝ, ‖κ t‖)
        = (∫ t in Set.Ioc (-R) R, ‖κ t‖) + (∫ t in (Set.Ioc (-R) R)ᶜ, ‖κ t‖) :=
      (integral_add_compl (s := Set.Ioc (-R) R) measurableSet_Ioc hint).symm
    have hcompl : (∫ t in (Set.Ioc (-R) R)ᶜ, ‖κ t‖)
        = (∫ t in Set.Iic (-R), ‖κ t‖) + (∫ t in Set.Ioi R, ‖κ t‖) := by
      rw [Set.compl_Ioc]
      exact setIntegral_union (s := Set.Iic (-R)) (t := Set.Ioi R)
        (Set.Iic_disjoint_Ioi (by linarith)) measurableSet_Ioi
        hint.integrableOn hint.integrableOn
    calc (∫ t : ℝ, ‖κ t‖)
        = (∫ t in Set.Ioc (-R) R, ‖κ t‖) + (∫ t in (Set.Ioc (-R) R)ᶜ, ‖κ t‖) := hsplit
      _ = (∫ t in Set.Ioc (-R) R, ‖κ t‖)
            + ((∫ t in Set.Iic (-R), ‖κ t‖) + (∫ t in Set.Ioi R, ‖κ t‖)) := by rw [hcompl]
      _ ≤ 2 * R * C₁ + (C₂ * R⁻¹ + C₂ * R⁻¹) := add_le_add hmid (add_le_add hleft hright)
      _ = 2 * R * C₁ + 2 * C₂ / R := by rw [div_eq_mul_inv]; ring
  · -- non-integrable: the Bochner integral is `0`
    rw [integral_undef hint]
    have h1 : 0 ≤ 2 * R * C₁ := by nlinarith [hR.le, hC1nn]
    have h2 : 0 ≤ 2 * C₂ / R := div_nonneg (by linarith) hR.le
    linarith

/-! ### The optimised bound -/

/-- **L¹ bound, optimised form.**  With `R = √(C₂ / C₁)` the split bound becomes
`4 √(C₁ C₂)`; the degenerate cases `C₁ = 0` or `C₂ = 0` are handled separately
(there the kernel vanishes, respectively a.e.). -/
theorem integral_norm_le_sqrt (κ : ℝ → ℂ) {C₁ C₂ : ℝ}
    (hC1 : ∀ t, ‖κ t‖ ≤ C₁) (hC2 : ∀ t, t ≠ 0 → ‖κ t‖ ≤ C₂ / t ^ 2)
    (hC1nn : 0 ≤ C₁) (hC2nn : 0 ≤ C₂) :
    ∫ t : ℝ, ‖κ t‖ ≤ 4 * Real.sqrt (C₁ * C₂) := by
  rcases eq_or_lt_of_le hC1nn with hC1z | hC1pos
  · -- `C₁ = 0`: the kernel vanishes identically
    have hz : ∀ t, ‖κ t‖ = 0 := by
      intro t
      have h := hC1 t
      rw [← hC1z] at h
      exact le_antisymm h (norm_nonneg _)
    have hzero : (∫ t : ℝ, ‖κ t‖) = 0 := by
      rw [integral_congr_ae
        (show (fun t : ℝ => ‖κ t‖) =ᵐ[volume] (fun _ => 0) from Eventually.of_forall hz)]
      simp
    rw [hzero]
    exact mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  · rcases eq_or_lt_of_le hC2nn with hC2z | hC2pos
    · -- `C₂ = 0`: the kernel vanishes off the origin, hence a.e.
      have hpoint : ∀ t, t ≠ 0 → ‖κ t‖ = 0 := by
        intro t ht
        have h := hC2 t ht
        rw [← hC2z, zero_div] at h
        exact le_antisymm h (norm_nonneg _)
      have hae : ∀ᵐ t ∂(volume : Measure ℝ), ‖κ t‖ = 0 := by
        filter_upwards [show ∀ᵐ t ∂(volume : Measure ℝ), t ≠ 0 from by
          rw [MeasureTheory.ae_iff]; simp] with t ht
        exact hpoint t ht
      have hzero : (∫ t : ℝ, ‖κ t‖) = 0 := by
        rw [integral_congr_ae
          (show (fun t : ℝ => ‖κ t‖) =ᵐ[volume] (fun _ => 0) from hae)]
        simp
      rw [hzero]
      exact mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
    · -- both constants positive: optimise at `R = √(C₂ / C₁)`
      have hq : (0 : ℝ) ≤ C₂ / C₁ := by positivity
      have hs : (0 : ℝ) ≤ C₁ * C₂ := by positivity
      -- `√(C₂/C₁) * C₁ = √(C₁ C₂)`
      have h1 : Real.sqrt (C₂ / C₁) * C₁ = Real.sqrt (C₁ * C₂) := by
        rw [eq_comm, Real.sqrt_eq_iff_eq_sq hs (mul_nonneg (Real.sqrt_nonneg _) hC1nn),
          mul_pow, Real.sq_sqrt hq]
        field_simp
      -- `C₂ / √(C₂/C₁) = √(C₁ C₂)`
      have h2 : C₂ / Real.sqrt (C₂ / C₁) = Real.sqrt (C₁ * C₂) := by
        rw [eq_comm, Real.sqrt_eq_iff_eq_sq hs (by positivity), div_pow, Real.sq_sqrt hq]
        field_simp
      refine (integral_norm_le_split (R := Real.sqrt (C₂ / C₁)) κ hC1 hC2
        (Real.sqrt_pos_of_pos (by positivity)) hC1nn hC2nn).trans_eq ?_
      rw [mul_assoc, h1, mul_div_assoc, h2]
      ring

end RobustZ
