import RobustZ.NewRung
import RobustZ.ChebBundle
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Final rung: unconditional exact-criterion lower bound plus certified numeric instances.

Task 1 is `new_rung_final`: the exact-criterion rung with no `nrCheb`/`nrInv`/kernel
hypotheses, obtained by applying `nr_main_rung` to `nrCheb_of_truncation`.
Task 2 certifies concrete lower bounds at `φ = π` for `N = 2, …, 12` by verifying the
criterion `nrCcal τ q * q^2 * nrE2star τ q < sin(π/4)^2 = 1/2` inside Lean with
rigorous explicit bounds (rational square-root enclosures, Mathlib `d9` logarithm /
exponential bounds, monotone majorants). All numeric premises are exact rational or
decimal comparisons discharged by `norm_num`; no `sorry`/`admit`/`axiom` is used.
-/

namespace RobustZ

/-! ## §1. Enclosure helpers (proved once, reused by every certified number). -/

/-- `log` lower bound through `arcosh` (which is *defined* as `log (x + √(x²-1))`). -/
lemma log_le_arcosh {x m : ℝ} (_hx : 1 < x) (hm : 0 < m)
    (hmy : m ≤ x + Real.sqrt (x ^ 2 - 1)) :
    Real.log m ≤ Real.arcosh x := by
  have hdef : Real.arcosh x = Real.log (x + Real.sqrt (x ^ 2 - 1)) := rfl
  rw [hdef]
  exact Real.log_le_log hm hmy

/-- `exp(-arcosh x) ≤ 1/m` for `m ≤ x + √(x²-1)`. -/
lemma exp_neg_arcosh_le_inv {x m : ℝ} (hx : 1 < x) (hm : 0 < m)
    (hmy : m ≤ x + Real.sqrt (x ^ 2 - 1)) :
    Real.exp (-(Real.arcosh x)) ≤ 1 / m := by
  have hα : Real.exp (Real.arcosh x) = x + Real.sqrt (x ^ 2 - 1) :=
    Real.exp_arcosh hx.le
  rw [Real.exp_neg, hα, one_div]
  exact inv_anti₀ hm hmy

/-- Monotonicity of the `η1` closed form on `[0, s]` with `s < 1`. -/
lemma nrEta1_mono {r s : ℝ} (hr0 : 0 ≤ r) (hrs : r ≤ s) (hs1 : s < 1) :
    nrEta1 r ≤ nrEta1 s := by
  have h1s : (0 : ℝ) < 1 - s := by linarith
  unfold nrEta1
  exact div_le_div₀ (by linarith) (by linarith) (pow_pos h1s 3)
    (pow_le_pow_left₀ h1s.le (by linarith) 3)

/-- Monotonicity of the `η2` closed form on `[0, s]` with `s < 1`. -/
lemma nrEta2_mono {r s : ℝ} (hr0 : 0 ≤ r) (hrs : r ≤ s) (hs1 : s < 1) :
    nrEta2 r ≤ nrEta2 s := by
  have h1s : (0 : ℝ) < 1 - s := by linarith
  have hs0 : (0 : ℝ) ≤ s := le_trans hr0 hrs
  have hnum : 1 + 11 * r + 11 * r ^ 2 + r ^ 3
      ≤ 1 + 11 * s + 11 * s ^ 2 + s ^ 3 := by
    have p2 : r ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ hr0 hrs 2
    have p3 : r ^ 3 ≤ s ^ 3 := pow_le_pow_left₀ hr0 hrs 3
    have m1 : (11 : ℝ) * r ≤ 11 * s := by linarith
    have m2 : (11 : ℝ) * r ^ 2 ≤ 11 * s ^ 2 := by linarith
    linarith
  have hc : (0 : ℝ) ≤ 1 + 11 * s + 11 * s ^ 2 + s ^ 3 := by
    have q1 : (0 : ℝ) ≤ 11 * s := mul_nonneg (by norm_num) hs0
    have q2 : (0 : ℝ) ≤ 11 * s ^ 2 := mul_nonneg (by norm_num) (pow_nonneg hs0 2)
    have q3 : (0 : ℝ) ≤ s ^ 3 := pow_nonneg hs0 3
    linarith
  unfold nrEta2
  exact div_le_div₀ hc hnum (pow_pos h1s 5)
    (pow_le_pow_left₀ h1s.le (by linarith) 5)

/-- `nrB τ q / τ = 1/q²`. -/
lemma nrB_div_eq {τ : ℝ} {q : ℕ} (hτ : τ ≠ 0) (hq : ((q : ℕ) : ℝ) ≠ 0) :
    nrB τ q / τ = 1 / ((q : ℕ) : ℝ) ^ 2 := by
  have hq2 : ((q : ℕ) : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hq
  unfold nrB
  field_simp

/-- `Ccal` upper bound from `η` upper bounds. -/
lemma nrCcal_le_of {τ : ℝ} {q : ℕ} {e1 e2 Cs : ℝ}
    (hq : (2 : ℝ) ≤ ((q : ℕ) : ℝ)) (hτ : (0 : ℝ) < τ) (hlt : τ < ((q : ℕ) : ℝ))
    (he1 : nrEta1of τ q ≤ e1) (he1nn : (0 : ℝ) ≤ e1)
    (he2 : nrEta2of τ q ≤ e2) (he2nn : (0 : ℝ) ≤ e2)
    (hCs : 2 * (1 + 1 / ((q : ℕ) : ℝ) ^ 2) * (1 + (4 / 27) * e1)
      * (32 * e2 * ((q : ℕ) : ℝ) ^ 2 + 44 + 2 * (12 + 16 / 27) * e1)
      ≤ Cs ^ 2)
    (hCsnn : (0 : ℝ) ≤ Cs) :
    nrCcal τ q ≤ (2 / 3) * (1 / ((q : ℕ) : ℝ)) * Cs := by
  have hq0 : (0 : ℝ) < ((q : ℕ) : ℝ) := by linarith
  have hB : nrB τ q / τ = 1 / ((q : ℕ) : ℝ) ^ 2 :=
    nrB_div_eq (ne_of_gt hτ) (ne_of_gt hq0)
  have hαpos : (0 : ℝ) < besselAlpha τ ((q : ℕ) : ℝ) := by
    unfold besselAlpha
    exact Real.arcosh_pos ((one_lt_div hτ).mpr hlt)
  have hr0 := nrR_nonneg τ q
  have hr1 := nrR_lt_one hαpos
  have he1nn0 : (0 : ℝ) ≤ nrEta1of τ q := by
    have h := nrEta1_ge_one hr0 hr1
    have rfl1 : nrEta1of τ q = nrEta1 (nrR τ q) := rfl
    rw [rfl1]
    exact le_trans zero_le_one h
  have he2nn0 : (0 : ℝ) ≤ nrEta2of τ q := by
    have h := nrEta2_nonneg hr0 hr1
    have rfl2 : nrEta2of τ q = nrEta2 (nrR τ q) := rfl
    rw [rfl2]
    exact h
  have hpi : (2 : ℝ) / Real.pi ≤ 2 / 3 :=
    div_le_div₀ (by norm_num) le_rfl (by norm_num) Real.pi_gt_three.le
  have f1 : (1 : ℝ) + (4 / 27) * (nrEta1of τ q) ≤ 1 + (4 / 27) * e1 :=
    add_le_add (le_refl _)
      (mul_le_mul_of_nonneg_left he1 (show (0 : ℝ) ≤ 4 / 27 by norm_num))
  have f2 : 32 * (nrEta2of τ q) * ((q : ℕ) : ℝ) ^ 2 + 44
        + 2 * (12 + 16 / 27) * (nrEta1of τ q)
      ≤ 32 * e2 * ((q : ℕ) : ℝ) ^ 2 + 44 + 2 * (12 + 16 / 27) * e1 := by
    have g1 : 32 * (nrEta2of τ q) * ((q : ℕ) : ℝ) ^ 2
        ≤ 32 * e2 * ((q : ℕ) : ℝ) ^ 2 :=
      mul_le_mul (mul_le_mul_of_nonneg_left he2 (by norm_num)) (le_refl _)
        (sq_nonneg _) (mul_nonneg (by norm_num) he2nn)
    have g2 : 2 * (12 + 16 / 27) * (nrEta1of τ q)
        ≤ 2 * (12 + 16 / 27) * e1 :=
      mul_le_mul_of_nonneg_left he1 (by norm_num)
    exact add_le_add (add_le_add g1 (le_refl _)) g2
  have harg : 2 * (1 + nrB τ q / τ) * (1 + (4 / 27) * (nrEta1of τ q))
        * (32 * (nrEta2of τ q) * ((q : ℕ) : ℝ) ^ 2 + 44
          + 2 * (12 + 16 / 27) * (nrEta1of τ q))
      ≤ 2 * (1 + 1 / ((q : ℕ) : ℝ) ^ 2) * (1 + (4 / 27) * e1)
        * (32 * e2 * ((q : ℕ) : ℝ) ^ 2 + 44 + 2 * (12 + 16 / 27) * e1) := by
    rw [hB]
    have i1 : 2 * (1 + 1 / ((q : ℕ) : ℝ) ^ 2) * (1 + (4 / 27) * (nrEta1of τ q))
        ≤ 2 * (1 + 1 / ((q : ℕ) : ℝ) ^ 2) * (1 + (4 / 27) * e1) := by
      apply mul_le_mul (le_refl _) f1 _ _
      · exact add_nonneg zero_le_one
          (mul_nonneg (by norm_num) he1nn0)
      · exact mul_nonneg (by norm_num)
          (add_nonneg zero_le_one
            (le_of_lt (one_div_pos.mpr (pow_pos hq0 2))))
    have j0 : (0 : ℝ) ≤ 32 * (nrEta2of τ q) * ((q : ℕ) : ℝ) ^ 2 + 44
        + 2 * (12 + 16 / 27) * (nrEta1of τ q) :=
      add_nonneg
        (add_nonneg
          (mul_nonneg (mul_nonneg (by norm_num) he2nn0) (sq_nonneg _))
          (by norm_num))
        (mul_nonneg (by norm_num) he1nn0)
    have j1 : (0 : ℝ) ≤ 2 * (1 + 1 / ((q : ℕ) : ℝ) ^ 2)
        * (1 + (4 / 27) * e1) := by
      have p : (0 : ℝ) ≤ 1 + (4 / 27) * e1 :=
        add_nonneg zero_le_one (mul_nonneg (by norm_num) he1nn)
      have q2 : (0 : ℝ) ≤ 2 * (1 + 1 / ((q : ℕ) : ℝ) ^ 2) :=
        mul_nonneg (by norm_num)
          (add_nonneg zero_le_one
            (le_of_lt (one_div_pos.mpr (pow_pos hq0 2))))
      exact mul_nonneg q2 p
    exact mul_le_mul i1 f2 j0 j1
  have hsqrt : Real.sqrt (2 * (1 + nrB τ q / τ) * (1 + (4 / 27) * (nrEta1of τ q))
        * (32 * (nrEta2of τ q) * ((q : ℕ) : ℝ) ^ 2 + 44
          + 2 * (12 + 16 / 27) * (nrEta1of τ q))) ≤ Cs := by
    have hle : Real.sqrt (2 * (1 + nrB τ q / τ) * (1 + (4 / 27) * (nrEta1of τ q))
          * (32 * (nrEta2of τ q) * ((q : ℕ) : ℝ) ^ 2 + 44
            + 2 * (12 + 16 / 27) * (nrEta1of τ q)))
        ≤ Real.sqrt (Cs ^ 2) :=
      Real.sqrt_le_sqrt (le_trans harg hCs)
    rwa [Real.sqrt_sq hCsnn] at hle
  have hqinv : (0 : ℝ) < 1 / ((q : ℕ) : ℝ) := one_div_pos.mpr hq0
  have hpre : (2 / Real.pi) * (1 / ((q : ℕ) : ℝ))
      ≤ (2 / 3) * (1 / ((q : ℕ) : ℝ)) :=
    mul_le_mul_of_nonneg_right hpi hqinv.le
  unfold nrCcal
  exact mul_le_mul hpre hsqrt (Real.sqrt_nonneg _)
    (mul_nonneg (by norm_num) hqinv.le)

/-- `exp(-F) ≤ 1/E` from an integer lower bound `k ≤ F` and `E ≤ e^k`. -/
lemma nr_exp_neg_le {F : ℝ} {k : ℕ} {E : ℝ}
    (hk : ((k : ℕ) : ℝ) ≤ F) (hE : E ≤ (2.7182818283 : ℝ) ^ k)
    (hE0 : (0 : ℝ) < E) :
    Real.exp (-F) ≤ 1 / E := by
  have he : (2.7182818283 : ℝ) ≤ Real.exp 1 := Real.exp_one_gt_d9.le
  have h1 : Real.exp ((k : ℝ)) ≤ Real.exp F := Real.exp_le_exp.mpr hk
  have h2 : (Real.exp 1) ^ k ≤ Real.exp ((k : ℝ)) := by
    have e : Real.exp ((k : ℝ)) = (Real.exp 1) ^ k := by
      conv_lhs => rw [show ((k : ℕ) : ℝ) = ((k : ℕ) : ℝ) * 1 from by ring]
      rw [Real.exp_nat_mul]
    rw [e]
  have h3 : E ≤ Real.exp F :=
    le_trans (le_trans hE (pow_le_pow_left₀ (by norm_num) he k)) (le_trans h2 h1)
  rw [Real.exp_neg, one_div]
  exact inv_anti₀ hE0 h3

/-- `E2*` upper bound from an `exp(-F)` bound, a denominator lower bound, and
`2√(π/8) ≤ N`. -/
lemma nrE2star_le_of {τ : ℝ} {q : ℕ} {eNeg tlo rhi N : ℝ}
    (hexp : Real.exp (-(besselF τ ((q : ℕ) : ℝ))) ≤ eNeg)
    (heNegnn : (0 : ℝ) ≤ eNeg)
    (htlo : tlo ≤ Real.sqrt (Real.sqrt (((q : ℕ) : ℝ) ^ 2 - τ ^ 2)))
    (htlo0 : (0 : ℝ) < tlo)
    (hr : Real.exp (-(besselAlpha τ ((q : ℕ) : ℝ))) ≤ rhi) (hr1 : rhi < 1)
    (hN : 2 * Real.sqrt (Real.pi / 8) ≤ N) (hNnn : (0 : ℝ) ≤ N) :
    nrE2star τ q ≤ N * eNeg / (tlo * (1 - rhi)) := by
  have hexpnn : (0 : ℝ) ≤ Real.exp (-(besselF τ ((q : ℕ) : ℝ))) :=
    (Real.exp_pos _).le
  have hnum : 2 * Real.sqrt (Real.pi / 8)
      * Real.exp (-(besselF τ ((q : ℕ) : ℝ))) ≤ N * eNeg :=
    mul_le_mul hN hexp hexpnn hNnn
  have h1e : (0 : ℝ) ≤ 1 - Real.exp (-(besselAlpha τ ((q : ℕ) : ℝ))) :=
    sub_nonneg.mpr (le_trans hr hr1.le)
  have hden : tlo * (1 - rhi)
      ≤ Real.sqrt (Real.sqrt (((q : ℕ) : ℝ) ^ 2 - τ ^ 2))
        * (1 - Real.exp (-(besselAlpha τ ((q : ℕ) : ℝ)))) :=
    mul_le_mul htlo (sub_le_sub_left hr _) (sub_nonneg.mpr hr1.le)
      (Real.sqrt_nonneg _)
  have hdenpos : (0 : ℝ) < tlo * (1 - rhi) :=
    mul_pos htlo0 (sub_pos.mpr hr1)
  unfold nrE2star
  exact div_le_div₀ (mul_nonneg hNnn heNegnn) hnum hdenpos hden

/-- `sin(π/4)^2 = 1/2`: the exact criterion threshold at `φ = π`. -/
lemma sin_pi_div_four_sq : Real.sin (Real.pi / 4) ^ 2 = 1 / 2 := by
  rw [Real.sin_pi_div_four, div_pow, Real.sq_sqrt (by norm_num)]
  norm_num

/-! ## §2. Task 1: the unconditional exact-criterion rung. -/

/-- Unconditional rung: for `1 ≤ N`, `0 < φ ≤ π`, admissible data, and `1 ≤ τ < q`
(`q = 2N+2`), the exact criterion `nrCcal τ q * q^2 * nrE2star τ q < sin(φ/4)^2`
implies `2τ < cost θ`. No `nrCheb`/inversion/kernel hypotheses remain: the bundle
is supplied by `nrCheb_of_truncation` (whose `.τ`/`.q` fields project
definitionally, so `hqN := rfl`). -/
theorem new_rung_final {N : ℕ} {φ : ℝ} {L : ℕ} {α θ : Fin L → ℝ}
    (hN : 1 ≤ N) (hφ0 : 0 < φ) (hφπ : φ ≤ Real.pi)
    (hAdm : Admissible N φ L α θ) (τ : ℝ) (hτ1 : 1 ≤ τ)
    (hlt : τ < ((2 * N + 2 : ℕ) : ℝ))
    (hmain : nrCcal τ (2 * N + 2) * ((((2 * N + 2 : ℕ)) : ℝ)) ^ 2
      * nrE2star τ (2 * N + 2) < Real.sin (φ / 4) ^ 2) :
    2 * τ < cost θ := by
  have hq2 : 2 ≤ 2 * N + 2 := by omega
  exact nr_main_rung (nrCheb_of_truncation τ (2 * N + 2) hτ1 hq2 hlt)
    hN hφ0 hφπ hAdm rfl hmain

/-! ## §3. Task 2: certified numeric instances at `φ = π`. -/

/-- Certified number at `N = 2` (`φ = π`): `cost θ ≥ 2`, via the exact criterion
at `τ = 1`, `q = 6` (criterion value `≈ 0.2715 < 1/2`). -/
theorem cert_N2 {L : ℕ} {α θ : Fin L → ℝ}
    (hAdm : Admissible 2 Real.pi L α θ) : 2 ≤ cost θ := by
  have hmain12 : nrCcal (1:ℝ) 6 * (((6:ℕ):ℝ)) ^ 2
      * nrE2star (1:ℝ) 6 < Real.sin (Real.pi / 4) ^ 2 := by
    rw [sin_pi_div_four_sq]
    have hx1 : (1 : ℝ) < ((6:ℕ):ℝ) / (1:ℝ) := by norm_num
    have hs1 : (5.91:ℝ) ^ 2 ≤ (((6:ℕ):ℝ) / (1:ℝ)) ^ 2 - 1 := by norm_num
    have hsq1 : (5.91:ℝ)
        ≤ Real.sqrt ((((6:ℕ):ℝ) / (1:ℝ)) ^ 2 - 1) :=
      (Real.le_sqrt (by norm_num) (by norm_num)).mpr hs1
    have hy : (10:ℝ) ≤ ((6:ℕ):ℝ) / (1:ℝ)
        + Real.sqrt ((((6:ℕ):ℝ) / (1:ℝ)) ^ 2 - 1) :=
      le_trans (show (10:ℝ) ≤ ((6:ℕ):ℝ) / (1:ℝ) + (5.91:ℝ) by norm_num)
        (add_le_add (le_refl _) hsq1)
    have ha : Real.log (10:ℝ) ≤ Real.arcosh (((6:ℕ):ℝ) / (1:ℝ)) :=
      log_le_arcosh hx1 (show (0 : ℝ) < (10:ℝ) by norm_num) hy
    have hlogm : Real.log (10:ℝ) = Real.log 2 + Real.log 5 := Real.log_ten_eq
    have hα : (0.6931471803+1.6094379123:ℝ) ≤ Real.arcosh (((6:ℕ):ℝ) / (1:ℝ)) :=
      calc (0.6931471803+1.6094379123:ℝ) ≤ Real.log 2 + Real.log 5 :=
            add_le_add Real.log_two_gt_d9.le Real.log_five_gt_d9.le
        _ = Real.log 10 := hlogm.symm
        _ ≤ Real.arcosh (((6:ℕ):ℝ) / (1:ℝ)) := ha
    have hba : besselAlpha (1:ℝ) ((6:ℕ):ℝ)
        = Real.arcosh (((6:ℕ):ℝ) / (1:ℝ)) := rfl
    have hr : nrR (1:ℝ) 6 ≤ (0.1:ℝ) := by
      have e := exp_neg_arcosh_le_inv hx1 (show (0 : ℝ) < (10:ℝ) by norm_num) hy
      unfold nrR
      rw [hba]
      have e2 : (1 : ℝ) / (10:ℝ) = (0.1:ℝ) := by norm_num
      rw [← e2]
      exact e
    have he1 : nrEta1of (1:ℝ) 6 ≤ ((1100/729):ℝ) := by
      have hmono := nrEta1_mono (nrR_nonneg _ _) hr (by norm_num)
      have e : nrEta1 (0.1:ℝ) = ((1100/729):ℝ) := by unfold nrEta1; norm_num
      show nrEta1 (nrR (1:ℝ) 6) ≤ _
      calc nrEta1 (nrR (1:ℝ) 6) ≤ nrEta1 (0.1:ℝ) := hmono
        _ = ((1100/729):ℝ) := e
    have he2 : nrEta2of (1:ℝ) 6 ≤ ((73700/19683):ℝ) := by
      have hmono := nrEta2_mono (nrR_nonneg _ _) hr (by norm_num)
      have e : nrEta2 (0.1:ℝ) = ((73700/19683):ℝ) := by unfold nrEta2; norm_num
      show nrEta2 (nrR (1:ℝ) 6) ≤ _
      calc nrEta2 (nrR (1:ℝ) 6) ≤ nrEta2 (0.1:ℝ) := hmono
        _ = ((73700/19683):ℝ) := e
    have hsqU : Real.sqrt (((6:ℕ):ℝ) ^ 2 - (1:ℝ) ^ 2) ≤ (6:ℝ) := by
      rw [Real.sqrt_le_iff]
      refine ⟨by norm_num, by norm_num⟩
    have hsqL : (5:ℝ) ≤ Real.sqrt (((6:ℕ):ℝ) ^ 2 - (1:ℝ) ^ 2) :=
      (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
    have htlo : (2.23:ℝ)
        ≤ Real.sqrt (Real.sqrt (((6:ℕ):ℝ) ^ 2 - (1:ℝ) ^ 2)) := by
      have htlo2 : (2.23:ℝ) ^ 2
          ≤ Real.sqrt (((6:ℕ):ℝ) ^ 2 - (1:ℝ) ^ 2) :=
        le_trans (by norm_num) hsqL
      exact (Real.le_sqrt (by norm_num) (Real.sqrt_nonneg _)).mpr htlo2
    have hC := nrCcal_le_of (show (2 : ℝ) ≤ ((6:ℕ):ℝ) by norm_num)
      (show (0 : ℝ) < (1:ℝ) by norm_num)
      (show (1:ℝ) < ((6:ℕ):ℝ) by norm_num)
      he1 (show (0 : ℝ) ≤ ((1100/729):ℝ) by norm_num)
      he2 (show (0 : ℝ) ≤ ((73700/19683):ℝ) by norm_num)
      (show 2 * (1 + 1 / ((6:ℕ):ℝ) ^ 2) * (1 + (4 / 27) * ((1100/729):ℝ))
        * (32 * ((73700/19683):ℝ) * ((6:ℕ):ℝ) ^ 2 + 44 + 2 * (12 + 16 / 27) * ((1100/729):ℝ))
        ≤ (105.15:ℝ) ^ 2 by norm_num)
      (show (0 : ℝ) ≤ (105.15:ℝ) by norm_num)
    have hF : ((7:ℕ):ℝ) ≤ besselF (1:ℝ) ((6:ℕ):ℝ) := by
      have hq : ((6:ℕ):ℝ) = (6:ℝ) := by norm_num
      have hk : ((7:ℕ):ℝ) = (7:ℝ) := by norm_num
      rw [hq, hk]
      unfold besselF besselAlpha
      have g1 : (0.6931471803+1.6094379123:ℝ) ≤ Real.arcosh ((6:ℝ) / (1:ℝ)) := by
        rw [← hq]
        exact hα
      have g2 : Real.sqrt ((6:ℝ) ^ 2 - (1:ℝ) ^ 2) ≤ (6:ℝ) := by
        rw [← hq]
        exact hsqU
      have hmul : (6:ℝ) * (0.6931471803+1.6094379123:ℝ)
          ≤ (6:ℝ) * Real.arcosh ((6:ℝ) / (1:ℝ)) :=
        mul_le_mul_of_nonneg_left g1 (by norm_num)
      have key : (7:ℝ) ≤ (6:ℝ) * (0.6931471803+1.6094379123:ℝ) - (6:ℝ) := by norm_num
      calc (7:ℝ) ≤ (6:ℝ) * (0.6931471803+1.6094379123:ℝ) - (6:ℝ) := key
        _ ≤ (6:ℝ) * Real.arcosh ((6:ℝ) / (1:ℝ))
            - Real.sqrt ((6:ℝ) ^ 2 - (1:ℝ) ^ 2) :=
          sub_le_sub hmul g2
    have hEpow : (1096:ℝ) ≤ (2.7182818283 : ℝ) ^ 7 := by norm_num
    have hexp : Real.exp (-(besselF (1:ℝ) ((6:ℕ):ℝ))) ≤ 1 / (1096:ℝ) :=
      nr_exp_neg_le hF hEpow (by norm_num)
    have hN : 2 * Real.sqrt (Real.pi / 8) ≤ (1.42 : ℝ) := by
      have hpi : Real.pi ≤ (4 : ℝ) := Real.pi_lt_four.le
      have h : Real.sqrt (Real.pi / 8) ≤ Real.sqrt ((4 : ℝ) / 8) :=
        Real.sqrt_le_sqrt (by linarith [hpi])
      have h4 : Real.sqrt ((4 : ℝ) / 8) ≤ (0.71 : ℝ) := by
        rw [Real.sqrt_le_iff]
        refine ⟨by norm_num, by norm_num⟩
      calc 2 * Real.sqrt (Real.pi / 8) ≤ 2 * Real.sqrt ((4:ℝ)/8) :=
            mul_le_mul_of_nonneg_left h (by norm_num)
        _ ≤ 2 * (0.71:ℝ) := mul_le_mul_of_nonneg_left h4 (by norm_num)
        _ = (1.42:ℝ) := by norm_num
    have hE := nrE2star_le_of hexp (show (0 : ℝ) ≤ 1 / (1096:ℝ) by norm_num)
      htlo (show (0 : ℝ) < (2.23:ℝ) by norm_num)
      hr (show (0.1:ℝ) < 1 by norm_num)
      hN (show (0 : ℝ) ≤ (1.42 : ℝ) by norm_num)
    have hfin : ((2 / 3) * (1 / ((6:ℕ):ℝ)) * (105.15:ℝ)) * (((6:ℕ):ℝ)) ^ 2
        * ((1.42 : ℝ) * (1 / (1096:ℝ)) / ((2.23:ℝ) * (1 - (0.1:ℝ)))) < 1 / 2 := by
      norm_num
    have hnnC : (0 : ℝ) ≤ nrCcal (1:ℝ) 6 * (((6:ℕ):ℝ)) ^ 2 :=
      mul_nonneg (nrCcal_nonneg _ _ (by norm_num)) (sq_nonneg _)
    have hαnn : (0 : ℝ) ≤ besselAlpha (1:ℝ) (((6:ℕ):ℝ)) := by
      rw [hba]
      exact le_trans (show (0:ℝ) ≤ (0.6931471803+1.6094379123:ℝ) by norm_num) hα
    have hnnE : (0 : ℝ) ≤ nrE2star (1:ℝ) 6 := nrE2star_nonneg hαnn
    have hCnn : (0 : ℝ) ≤ (2 / 3) * (1 / ((6:ℕ):ℝ)) * (105.15:ℝ) := by
      have h1 : (0 : ℝ) ≤ (2 / 3) * (1 / ((6:ℕ):ℝ)) :=
        mul_nonneg (by norm_num)
          (le_of_lt (one_div_pos.mpr (by norm_num)))
      exact mul_nonneg h1 (by norm_num)
    have step1 : nrCcal (1:ℝ) 6 * (((6:ℕ):ℝ)) ^ 2
        ≤ ((2 / 3) * (1 / ((6:ℕ):ℝ)) * (105.15:ℝ)) * (((6:ℕ):ℝ)) ^ 2 :=
      mul_le_mul_of_nonneg_right hC (sq_nonneg _)
    have step2 : (nrCcal (1:ℝ) 6 * (((6:ℕ):ℝ)) ^ 2)
          * nrE2star (1:ℝ) 6
        ≤ (((2 / 3) * (1 / ((6:ℕ):ℝ)) * (105.15:ℝ)) * (((6:ℕ):ℝ)) ^ 2)
          * ((1.42 : ℝ) * (1 / (1096:ℝ)) / ((2.23:ℝ) * (1 - (0.1:ℝ)))) :=
      mul_le_mul step1 hE hnnE (mul_nonneg hCnn (sq_nonneg _))
    have hProd : nrCcal (1:ℝ) 6 * (((6:ℕ):ℝ)) ^ 2
        * nrE2star (1:ℝ) 6 < 1 / 2 :=
      lt_of_le_of_lt step2 hfin
    exact hProd
  have hcost := new_rung_final (hN := by norm_num) (hφ0 := Real.pi_pos)
    (hφπ := le_rfl) (hAdm := hAdm) (τ := (1 : ℝ)) (hτ1 := by norm_num)
    (hlt := by norm_num) hmain12
  calc (2:ℝ) = 2 * (1:ℝ) := by norm_num
    _ ≤ cost θ := le_of_lt hcost

/-- Certified number at `N = 3` (`φ = π`): `cost θ ≥ 2`, via the exact criterion
at `τ = 1`, `q = 8` (criterion value `≈ 0.0007827 < 1/2`). -/
theorem cert_N3 {L : ℕ} {α θ : Fin L → ℝ}
    (hAdm : Admissible 3 Real.pi L α θ) : 2 ≤ cost θ := by
  have hmain12 : nrCcal (1:ℝ) 8 * (((8:ℕ):ℝ)) ^ 2
      * nrE2star (1:ℝ) 8 < Real.sin (Real.pi / 4) ^ 2 := by
    rw [sin_pi_div_four_sq]
    have hx1 : (1 : ℝ) < ((8:ℕ):ℝ) / (1:ℝ) := by norm_num
    have hs1 : (7.93:ℝ) ^ 2 ≤ (((8:ℕ):ℝ) / (1:ℝ)) ^ 2 - 1 := by norm_num
    have hsq1 : (7.93:ℝ)
        ≤ Real.sqrt ((((8:ℕ):ℝ) / (1:ℝ)) ^ 2 - 1) :=
      (Real.le_sqrt (by norm_num) (by norm_num)).mpr hs1
    have hy : (15:ℝ) ≤ ((8:ℕ):ℝ) / (1:ℝ)
        + Real.sqrt ((((8:ℕ):ℝ) / (1:ℝ)) ^ 2 - 1) :=
      le_trans (show (15:ℝ) ≤ ((8:ℕ):ℝ) / (1:ℝ) + (7.93:ℝ) by norm_num)
        (add_le_add (le_refl _) hsq1)
    have ha : Real.log (15:ℝ) ≤ Real.arcosh (((8:ℕ):ℝ) / (1:ℝ)) :=
      log_le_arcosh hx1 (show (0 : ℝ) < (15:ℝ) by norm_num) hy
    have hlogm : Real.log (15:ℝ) = Real.log 3 + Real.log 5 := by
      rw [show (15:ℝ) = 3 * 5 from by norm_num,
        Real.log_mul (by norm_num) (by norm_num)]
    have hα : (1.0986122885+1.6094379123:ℝ) ≤ Real.arcosh (((8:ℕ):ℝ) / (1:ℝ)) :=
      calc (1.0986122885+1.6094379123:ℝ) ≤ Real.log 3 + Real.log 5 :=
            add_le_add Real.log_three_gt_d9.le Real.log_five_gt_d9.le
        _ = Real.log 15 := hlogm.symm
        _ ≤ Real.arcosh (((8:ℕ):ℝ) / (1:ℝ)) := ha
    have hba : besselAlpha (1:ℝ) ((8:ℕ):ℝ)
        = Real.arcosh (((8:ℕ):ℝ) / (1:ℝ)) := rfl
    have hr : nrR (1:ℝ) 8 ≤ ((1/15):ℝ) := by
      have e := exp_neg_arcosh_le_inv hx1 (show (0 : ℝ) < (15:ℝ) by norm_num) hy
      unfold nrR
      rw [hba]
      have e2 : (1 : ℝ) / (15:ℝ) = ((1/15):ℝ) := by norm_num
      rw [← e2]
      exact e
    have he1 : nrEta1of (1:ℝ) 8 ≤ ((450/343):ℝ) := by
      have hmono := nrEta1_mono (nrR_nonneg _ _) hr (by norm_num)
      have e : nrEta1 ((1/15):ℝ) = ((450/343):ℝ) := by unfold nrEta1; norm_num
      show nrEta1 (nrR (1:ℝ) 8) ≤ _
      calc nrEta1 (nrR (1:ℝ) 8) ≤ nrEta1 ((1/15):ℝ) := hmono
        _ = ((450/343):ℝ) := e
    have he2 : nrEta2of (1:ℝ) 8 ≤ ((42300/16807):ℝ) := by
      have hmono := nrEta2_mono (nrR_nonneg _ _) hr (by norm_num)
      have e : nrEta2 ((1/15):ℝ) = ((42300/16807):ℝ) := by unfold nrEta2; norm_num
      show nrEta2 (nrR (1:ℝ) 8) ≤ _
      calc nrEta2 (nrR (1:ℝ) 8) ≤ nrEta2 ((1/15):ℝ) := hmono
        _ = ((42300/16807):ℝ) := e
    have hsqU : Real.sqrt (((8:ℕ):ℝ) ^ 2 - (1:ℝ) ^ 2) ≤ (8:ℝ) := by
      rw [Real.sqrt_le_iff]
      refine ⟨by norm_num, by norm_num⟩
    have hsqL : (7:ℝ) ≤ Real.sqrt (((8:ℕ):ℝ) ^ 2 - (1:ℝ) ^ 2) :=
      (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
    have htlo : (2.64:ℝ)
        ≤ Real.sqrt (Real.sqrt (((8:ℕ):ℝ) ^ 2 - (1:ℝ) ^ 2)) := by
      have htlo2 : (2.64:ℝ) ^ 2
          ≤ Real.sqrt (((8:ℕ):ℝ) ^ 2 - (1:ℝ) ^ 2) :=
        le_trans (by norm_num) hsqL
      exact (Real.le_sqrt (by norm_num) (Real.sqrt_nonneg _)).mpr htlo2
    have hC := nrCcal_le_of (show (2 : ℝ) ≤ ((8:ℕ):ℝ) by norm_num)
      (show (0 : ℝ) < (1:ℝ) by norm_num)
      (show (1:ℝ) < ((8:ℕ):ℝ) by norm_num)
      he1 (show (0 : ℝ) ≤ ((450/343):ℝ) by norm_num)
      he2 (show (0 : ℝ) ≤ ((42300/16807):ℝ) by norm_num)
      (show 2 * (1 + 1 / ((8:ℕ):ℝ) ^ 2) * (1 + (4 / 27) * ((450/343):ℝ))
        * (32 * ((42300/16807):ℝ) * ((8:ℕ):ℝ) ^ 2 + 44 + 2 * (12 + 16 / 27) * ((450/343):ℝ))
        ≤ (112.66:ℝ) ^ 2 by norm_num)
      (show (0 : ℝ) ≤ (112.66:ℝ) by norm_num)
    have hF : ((13:ℕ):ℝ) ≤ besselF (1:ℝ) ((8:ℕ):ℝ) := by
      have hq : ((8:ℕ):ℝ) = (8:ℝ) := by norm_num
      have hk : ((13:ℕ):ℝ) = (13:ℝ) := by norm_num
      rw [hq, hk]
      unfold besselF besselAlpha
      have g1 : (1.0986122885+1.6094379123:ℝ) ≤ Real.arcosh ((8:ℝ) / (1:ℝ)) := by
        rw [← hq]
        exact hα
      have g2 : Real.sqrt ((8:ℝ) ^ 2 - (1:ℝ) ^ 2) ≤ (8:ℝ) := by
        rw [← hq]
        exact hsqU
      have hmul : (8:ℝ) * (1.0986122885+1.6094379123:ℝ)
          ≤ (8:ℝ) * Real.arcosh ((8:ℝ) / (1:ℝ)) :=
        mul_le_mul_of_nonneg_left g1 (by norm_num)
      have key : (13:ℝ) ≤ (8:ℝ) * (1.0986122885+1.6094379123:ℝ) - (8:ℝ) := by norm_num
      calc (13:ℝ) ≤ (8:ℝ) * (1.0986122885+1.6094379123:ℝ) - (8:ℝ) := key
        _ ≤ (8:ℝ) * Real.arcosh ((8:ℝ) / (1:ℝ))
            - Real.sqrt ((8:ℝ) ^ 2 - (1:ℝ) ^ 2) :=
          sub_le_sub hmul g2
    have hEpow : (442413:ℝ) ≤ (2.7182818283 : ℝ) ^ 13 := by norm_num
    have hexp : Real.exp (-(besselF (1:ℝ) ((8:ℕ):ℝ))) ≤ 1 / (442413:ℝ) :=
      nr_exp_neg_le hF hEpow (by norm_num)
    have hN : 2 * Real.sqrt (Real.pi / 8) ≤ (1.42 : ℝ) := by
      have hpi : Real.pi ≤ (4 : ℝ) := Real.pi_lt_four.le
      have h : Real.sqrt (Real.pi / 8) ≤ Real.sqrt ((4 : ℝ) / 8) :=
        Real.sqrt_le_sqrt (by linarith [hpi])
      have h4 : Real.sqrt ((4 : ℝ) / 8) ≤ (0.71 : ℝ) := by
        rw [Real.sqrt_le_iff]
        refine ⟨by norm_num, by norm_num⟩
      calc 2 * Real.sqrt (Real.pi / 8) ≤ 2 * Real.sqrt ((4:ℝ)/8) :=
            mul_le_mul_of_nonneg_left h (by norm_num)
        _ ≤ 2 * (0.71:ℝ) := mul_le_mul_of_nonneg_left h4 (by norm_num)
        _ = (1.42:ℝ) := by norm_num
    have hE := nrE2star_le_of hexp (show (0 : ℝ) ≤ 1 / (442413:ℝ) by norm_num)
      htlo (show (0 : ℝ) < (2.64:ℝ) by norm_num)
      hr (show ((1/15):ℝ) < 1 by norm_num)
      hN (show (0 : ℝ) ≤ (1.42 : ℝ) by norm_num)
    have hfin : ((2 / 3) * (1 / ((8:ℕ):ℝ)) * (112.66:ℝ)) * (((8:ℕ):ℝ)) ^ 2
        * ((1.42 : ℝ) * (1 / (442413:ℝ)) / ((2.64:ℝ) * (1 - ((1/15):ℝ)))) < 1 / 2 := by
      norm_num
    have hnnC : (0 : ℝ) ≤ nrCcal (1:ℝ) 8 * (((8:ℕ):ℝ)) ^ 2 :=
      mul_nonneg (nrCcal_nonneg _ _ (by norm_num)) (sq_nonneg _)
    have hαnn : (0 : ℝ) ≤ besselAlpha (1:ℝ) (((8:ℕ):ℝ)) := by
      rw [hba]
      exact le_trans (show (0:ℝ) ≤ (1.0986122885+1.6094379123:ℝ) by norm_num) hα
    have hnnE : (0 : ℝ) ≤ nrE2star (1:ℝ) 8 := nrE2star_nonneg hαnn
    have hCnn : (0 : ℝ) ≤ (2 / 3) * (1 / ((8:ℕ):ℝ)) * (112.66:ℝ) := by
      have h1 : (0 : ℝ) ≤ (2 / 3) * (1 / ((8:ℕ):ℝ)) :=
        mul_nonneg (by norm_num)
          (le_of_lt (one_div_pos.mpr (by norm_num)))
      exact mul_nonneg h1 (by norm_num)
    have step1 : nrCcal (1:ℝ) 8 * (((8:ℕ):ℝ)) ^ 2
        ≤ ((2 / 3) * (1 / ((8:ℕ):ℝ)) * (112.66:ℝ)) * (((8:ℕ):ℝ)) ^ 2 :=
      mul_le_mul_of_nonneg_right hC (sq_nonneg _)
    have step2 : (nrCcal (1:ℝ) 8 * (((8:ℕ):ℝ)) ^ 2)
          * nrE2star (1:ℝ) 8
        ≤ (((2 / 3) * (1 / ((8:ℕ):ℝ)) * (112.66:ℝ)) * (((8:ℕ):ℝ)) ^ 2)
          * ((1.42 : ℝ) * (1 / (442413:ℝ)) / ((2.64:ℝ) * (1 - ((1/15):ℝ)))) :=
      mul_le_mul step1 hE hnnE (mul_nonneg hCnn (sq_nonneg _))
    have hProd : nrCcal (1:ℝ) 8 * (((8:ℕ):ℝ)) ^ 2
        * nrE2star (1:ℝ) 8 < 1 / 2 :=
      lt_of_le_of_lt step2 hfin
    exact hProd
  have hcost := new_rung_final (hN := by norm_num) (hφ0 := Real.pi_pos)
    (hφπ := le_rfl) (hAdm := hAdm) (τ := (1 : ℝ)) (hτ1 := by norm_num)
    (hlt := by norm_num) hmain12
  calc (2:ℝ) = 2 * (1:ℝ) := by norm_num
    _ ≤ cost θ := le_of_lt hcost

/-- Certified number at `N = 4` (`φ = π`): `cost θ ≥ 4`, via the exact criterion
at `τ = 2`, `q = 10` (criterion value `≈ 0.01095 < 1/2`). -/
theorem cert_N4 {L : ℕ} {α θ : Fin L → ℝ}
    (hAdm : Admissible 4 Real.pi L α θ) : 4 ≤ cost θ := by
  have hmain12 : nrCcal (2:ℝ) 10 * (((10:ℕ):ℝ)) ^ 2
      * nrE2star (2:ℝ) 10 < Real.sin (Real.pi / 4) ^ 2 := by
    rw [sin_pi_div_four_sq]
    have hx1 : (1 : ℝ) < ((10:ℕ):ℝ) / (2:ℝ) := by norm_num
    have hs1 : (4.89:ℝ) ^ 2 ≤ (((10:ℕ):ℝ) / (2:ℝ)) ^ 2 - 1 := by norm_num
    have hsq1 : (4.89:ℝ)
        ≤ Real.sqrt ((((10:ℕ):ℝ) / (2:ℝ)) ^ 2 - 1) :=
      (Real.le_sqrt (by norm_num) (by norm_num)).mpr hs1
    have hy : (9:ℝ) ≤ ((10:ℕ):ℝ) / (2:ℝ)
        + Real.sqrt ((((10:ℕ):ℝ) / (2:ℝ)) ^ 2 - 1) :=
      le_trans (show (9:ℝ) ≤ ((10:ℕ):ℝ) / (2:ℝ) + (4.89:ℝ) by norm_num)
        (add_le_add (le_refl _) hsq1)
    have ha : Real.log (9:ℝ) ≤ Real.arcosh (((10:ℕ):ℝ) / (2:ℝ)) :=
      log_le_arcosh hx1 (show (0 : ℝ) < (9:ℝ) by norm_num) hy
    have hlogm : Real.log (9:ℝ) = Real.log 3 + Real.log 3 := by
      rw [show (9:ℝ) = 3 * 3 from by norm_num,
        Real.log_mul (by norm_num) (by norm_num)]
    have hα : (1.0986122885+1.0986122885:ℝ) ≤ Real.arcosh (((10:ℕ):ℝ) / (2:ℝ)) :=
      calc (1.0986122885+1.0986122885:ℝ) ≤ Real.log 3 + Real.log 3 :=
            add_le_add Real.log_three_gt_d9.le Real.log_three_gt_d9.le
        _ = Real.log 9 := hlogm.symm
        _ ≤ Real.arcosh (((10:ℕ):ℝ) / (2:ℝ)) := ha
    have hba : besselAlpha (2:ℝ) ((10:ℕ):ℝ)
        = Real.arcosh (((10:ℕ):ℝ) / (2:ℝ)) := rfl
    have hr : nrR (2:ℝ) 10 ≤ ((1/9):ℝ) := by
      have e := exp_neg_arcosh_le_inv hx1 (show (0 : ℝ) < (9:ℝ) by norm_num) hy
      unfold nrR
      rw [hba]
      have e2 : (1 : ℝ) / (9:ℝ) = ((1/9):ℝ) := by norm_num
      rw [← e2]
      exact e
    have he1 : nrEta1of (2:ℝ) 10 ≤ (1.58203125:ℝ) := by
      have hmono := nrEta1_mono (nrR_nonneg _ _) hr (by norm_num)
      have e : nrEta1 ((1/9):ℝ) = (1.58203125:ℝ) := by unfold nrEta1; norm_num
      show nrEta1 (nrR (2:ℝ) 10) ≤ _
      calc nrEta1 (nrR (2:ℝ) 10) ≤ nrEta1 ((1/9):ℝ) := hmono
        _ = (1.58203125:ℝ) := e
    have he2 : nrEta2of (2:ℝ) 10 ≤ (4.251708984375:ℝ) := by
      have hmono := nrEta2_mono (nrR_nonneg _ _) hr (by norm_num)
      have e : nrEta2 ((1/9):ℝ) = (4.251708984375:ℝ) := by unfold nrEta2; norm_num
      show nrEta2 (nrR (2:ℝ) 10) ≤ _
      calc nrEta2 (nrR (2:ℝ) 10) ≤ nrEta2 ((1/9):ℝ) := hmono
        _ = (4.251708984375:ℝ) := e
    have hsqU : Real.sqrt (((10:ℕ):ℝ) ^ 2 - (2:ℝ) ^ 2) ≤ (10:ℝ) := by
      rw [Real.sqrt_le_iff]
      refine ⟨by norm_num, by norm_num⟩
    have hsqL : (9:ℝ) ≤ Real.sqrt (((10:ℕ):ℝ) ^ 2 - (2:ℝ) ^ 2) :=
      (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
    have htlo : (3:ℝ)
        ≤ Real.sqrt (Real.sqrt (((10:ℕ):ℝ) ^ 2 - (2:ℝ) ^ 2)) := by
      have htlo2 : (3:ℝ) ^ 2
          ≤ Real.sqrt (((10:ℕ):ℝ) ^ 2 - (2:ℝ) ^ 2) :=
        le_trans (by norm_num) hsqL
      exact (Real.le_sqrt (by norm_num) (Real.sqrt_nonneg _)).mpr htlo2
    have hC := nrCcal_le_of (show (2 : ℝ) ≤ ((10:ℕ):ℝ) by norm_num)
      (show (0 : ℝ) < (2:ℝ) by norm_num)
      (show (2:ℝ) < ((10:ℕ):ℝ) by norm_num)
      he1 (show (0 : ℝ) ≤ (1.58203125:ℝ) by norm_num)
      he2 (show (0 : ℝ) ≤ (4.251708984375:ℝ) by norm_num)
      (show 2 * (1 + 1 / ((10:ℕ):ℝ) ^ 2) * (1 + (4 / 27) * (1.58203125:ℝ))
        * (32 * (4.251708984375:ℝ) * ((10:ℕ):ℝ) ^ 2 + 44 + 2 * (12 + 16 / 27) * (1.58203125:ℝ))
        ≤ (184.76:ℝ) ^ 2 by norm_num)
      (show (0 : ℝ) ≤ (184.76:ℝ) by norm_num)
    have hF : ((11:ℕ):ℝ) ≤ besselF (2:ℝ) ((10:ℕ):ℝ) := by
      have hq : ((10:ℕ):ℝ) = (10:ℝ) := by norm_num
      have hk : ((11:ℕ):ℝ) = (11:ℝ) := by norm_num
      rw [hq, hk]
      unfold besselF besselAlpha
      have g1 : (1.0986122885+1.0986122885:ℝ) ≤ Real.arcosh ((10:ℝ) / (2:ℝ)) := by
        rw [← hq]
        exact hα
      have g2 : Real.sqrt ((10:ℝ) ^ 2 - (2:ℝ) ^ 2) ≤ (10:ℝ) := by
        rw [← hq]
        exact hsqU
      have hmul : (10:ℝ) * (1.0986122885+1.0986122885:ℝ)
          ≤ (10:ℝ) * Real.arcosh ((10:ℝ) / (2:ℝ)) :=
        mul_le_mul_of_nonneg_left g1 (by norm_num)
      have key : (11:ℝ) ≤ (10:ℝ) * (1.0986122885+1.0986122885:ℝ) - (10:ℝ) := by norm_num
      calc (11:ℝ) ≤ (10:ℝ) * (1.0986122885+1.0986122885:ℝ) - (10:ℝ) := key
        _ ≤ (10:ℝ) * Real.arcosh ((10:ℝ) / (2:ℝ))
            - Real.sqrt ((10:ℝ) ^ 2 - (2:ℝ) ^ 2) :=
          sub_le_sub hmul g2
    have hEpow : (59874:ℝ) ≤ (2.7182818283 : ℝ) ^ 11 := by norm_num
    have hexp : Real.exp (-(besselF (2:ℝ) ((10:ℕ):ℝ))) ≤ 1 / (59874:ℝ) :=
      nr_exp_neg_le hF hEpow (by norm_num)
    have hN : 2 * Real.sqrt (Real.pi / 8) ≤ (1.42 : ℝ) := by
      have hpi : Real.pi ≤ (4 : ℝ) := Real.pi_lt_four.le
      have h : Real.sqrt (Real.pi / 8) ≤ Real.sqrt ((4 : ℝ) / 8) :=
        Real.sqrt_le_sqrt (by linarith [hpi])
      have h4 : Real.sqrt ((4 : ℝ) / 8) ≤ (0.71 : ℝ) := by
        rw [Real.sqrt_le_iff]
        refine ⟨by norm_num, by norm_num⟩
      calc 2 * Real.sqrt (Real.pi / 8) ≤ 2 * Real.sqrt ((4:ℝ)/8) :=
            mul_le_mul_of_nonneg_left h (by norm_num)
        _ ≤ 2 * (0.71:ℝ) := mul_le_mul_of_nonneg_left h4 (by norm_num)
        _ = (1.42:ℝ) := by norm_num
    have hE := nrE2star_le_of hexp (show (0 : ℝ) ≤ 1 / (59874:ℝ) by norm_num)
      htlo (show (0 : ℝ) < (3:ℝ) by norm_num)
      hr (show ((1/9):ℝ) < 1 by norm_num)
      hN (show (0 : ℝ) ≤ (1.42 : ℝ) by norm_num)
    have hfin : ((2 / 3) * (1 / ((10:ℕ):ℝ)) * (184.76:ℝ)) * (((10:ℕ):ℝ)) ^ 2
        * ((1.42 : ℝ) * (1 / (59874:ℝ)) / ((3:ℝ) * (1 - ((1/9):ℝ)))) < 1 / 2 := by
      norm_num
    have hnnC : (0 : ℝ) ≤ nrCcal (2:ℝ) 10 * (((10:ℕ):ℝ)) ^ 2 :=
      mul_nonneg (nrCcal_nonneg _ _ (by norm_num)) (sq_nonneg _)
    have hαnn : (0 : ℝ) ≤ besselAlpha (2:ℝ) (((10:ℕ):ℝ)) := by
      rw [hba]
      exact le_trans (show (0:ℝ) ≤ (1.0986122885+1.0986122885:ℝ) by norm_num) hα
    have hnnE : (0 : ℝ) ≤ nrE2star (2:ℝ) 10 := nrE2star_nonneg hαnn
    have hCnn : (0 : ℝ) ≤ (2 / 3) * (1 / ((10:ℕ):ℝ)) * (184.76:ℝ) := by
      have h1 : (0 : ℝ) ≤ (2 / 3) * (1 / ((10:ℕ):ℝ)) :=
        mul_nonneg (by norm_num)
          (le_of_lt (one_div_pos.mpr (by norm_num)))
      exact mul_nonneg h1 (by norm_num)
    have step1 : nrCcal (2:ℝ) 10 * (((10:ℕ):ℝ)) ^ 2
        ≤ ((2 / 3) * (1 / ((10:ℕ):ℝ)) * (184.76:ℝ)) * (((10:ℕ):ℝ)) ^ 2 :=
      mul_le_mul_of_nonneg_right hC (sq_nonneg _)
    have step2 : (nrCcal (2:ℝ) 10 * (((10:ℕ):ℝ)) ^ 2)
          * nrE2star (2:ℝ) 10
        ≤ (((2 / 3) * (1 / ((10:ℕ):ℝ)) * (184.76:ℝ)) * (((10:ℕ):ℝ)) ^ 2)
          * ((1.42 : ℝ) * (1 / (59874:ℝ)) / ((3:ℝ) * (1 - ((1/9):ℝ)))) :=
      mul_le_mul step1 hE hnnE (mul_nonneg hCnn (sq_nonneg _))
    have hProd : nrCcal (2:ℝ) 10 * (((10:ℕ):ℝ)) ^ 2
        * nrE2star (2:ℝ) 10 < 1 / 2 :=
      lt_of_le_of_lt step2 hfin
    exact hProd
  have hcost := new_rung_final (hN := by norm_num) (hφ0 := Real.pi_pos)
    (hφπ := le_rfl) (hAdm := hAdm) (τ := (2 : ℝ)) (hτ1 := by norm_num)
    (hlt := by norm_num) hmain12
  calc (4:ℝ) = 2 * (2:ℝ) := by norm_num
    _ ≤ cost θ := le_of_lt hcost

/-- Certified number at `N = 5` (`φ = π`): `cost θ ≥ 6`, via the exact criterion
at `τ = 3`, `q = 12` (criterion value `≈ 0.1563 < 1/2`). -/
theorem cert_N5 {L : ℕ} {α θ : Fin L → ℝ}
    (hAdm : Admissible 5 Real.pi L α θ) : 6 ≤ cost θ := by
  have hmain12 : nrCcal (3:ℝ) 12 * (((12:ℕ):ℝ)) ^ 2
      * nrE2star (3:ℝ) 12 < Real.sin (Real.pi / 4) ^ 2 := by
    rw [sin_pi_div_four_sq]
    have hx1 : (1 : ℝ) < ((12:ℕ):ℝ) / (3:ℝ) := by norm_num
    have hs1 : (3.87:ℝ) ^ 2 ≤ (((12:ℕ):ℝ) / (3:ℝ)) ^ 2 - 1 := by norm_num
    have hsq1 : (3.87:ℝ)
        ≤ Real.sqrt ((((12:ℕ):ℝ) / (3:ℝ)) ^ 2 - 1) :=
      (Real.le_sqrt (by norm_num) (by norm_num)).mpr hs1
    have hy : (6:ℝ) ≤ ((12:ℕ):ℝ) / (3:ℝ)
        + Real.sqrt ((((12:ℕ):ℝ) / (3:ℝ)) ^ 2 - 1) :=
      le_trans (show (6:ℝ) ≤ ((12:ℕ):ℝ) / (3:ℝ) + (3.87:ℝ) by norm_num)
        (add_le_add (le_refl _) hsq1)
    have ha : Real.log (6:ℝ) ≤ Real.arcosh (((12:ℕ):ℝ) / (3:ℝ)) :=
      log_le_arcosh hx1 (show (0 : ℝ) < (6:ℝ) by norm_num) hy
    have hlogm : Real.log (6:ℝ) = Real.log 2 + Real.log 3 := by
      rw [show (6:ℝ) = 2 * 3 from by norm_num,
        Real.log_mul (by norm_num) (by norm_num)]
    have hα : (0.6931471803+1.0986122885:ℝ) ≤ Real.arcosh (((12:ℕ):ℝ) / (3:ℝ)) :=
      calc (0.6931471803+1.0986122885:ℝ) ≤ Real.log 2 + Real.log 3 :=
            add_le_add Real.log_two_gt_d9.le Real.log_three_gt_d9.le
        _ = Real.log 6 := hlogm.symm
        _ ≤ Real.arcosh (((12:ℕ):ℝ) / (3:ℝ)) := ha
    have hba : besselAlpha (3:ℝ) ((12:ℕ):ℝ)
        = Real.arcosh (((12:ℕ):ℝ) / (3:ℝ)) := rfl
    have hr : nrR (3:ℝ) 12 ≤ ((1/6):ℝ) := by
      have e := exp_neg_arcosh_le_inv hx1 (show (0 : ℝ) < (6:ℝ) by norm_num) hy
      unfold nrR
      rw [hba]
      have e2 : (1 : ℝ) / (6:ℝ) = ((1/6):ℝ) := by norm_num
      rw [← e2]
      exact e
    have he1 : nrEta1of (3:ℝ) 12 ≤ (2.016:ℝ) := by
      have hmono := nrEta1_mono (nrR_nonneg _ _) hr (by norm_num)
      have e : nrEta1 ((1/6):ℝ) = (2.016:ℝ) := by unfold nrEta1; norm_num
      show nrEta1 (nrR (3:ℝ) 12) ≤ _
      calc nrEta1 (nrR (3:ℝ) 12) ≤ nrEta1 ((1/6):ℝ) := hmono
        _ = (2.016:ℝ) := e
    have he2 : nrEta2of (3:ℝ) 12 ≤ (7.82208:ℝ) := by
      have hmono := nrEta2_mono (nrR_nonneg _ _) hr (by norm_num)
      have e : nrEta2 ((1/6):ℝ) = (7.82208:ℝ) := by unfold nrEta2; norm_num
      show nrEta2 (nrR (3:ℝ) 12) ≤ _
      calc nrEta2 (nrR (3:ℝ) 12) ≤ nrEta2 ((1/6):ℝ) := hmono
        _ = (7.82208:ℝ) := e
    have hsqU : Real.sqrt (((12:ℕ):ℝ) ^ 2 - (3:ℝ) ^ 2) ≤ (12:ℝ) := by
      rw [Real.sqrt_le_iff]
      refine ⟨by norm_num, by norm_num⟩
    have hsqL : (11:ℝ) ≤ Real.sqrt (((12:ℕ):ℝ) ^ 2 - (3:ℝ) ^ 2) :=
      (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
    have htlo : (3.31:ℝ)
        ≤ Real.sqrt (Real.sqrt (((12:ℕ):ℝ) ^ 2 - (3:ℝ) ^ 2)) := by
      have htlo2 : (3.31:ℝ) ^ 2
          ≤ Real.sqrt (((12:ℕ):ℝ) ^ 2 - (3:ℝ) ^ 2) :=
        le_trans (by norm_num) hsqL
      exact (Real.le_sqrt (by norm_num) (Real.sqrt_nonneg _)).mpr htlo2
    have hC := nrCcal_le_of (show (2 : ℝ) ≤ ((12:ℕ):ℝ) by norm_num)
      (show (0 : ℝ) < (3:ℝ) by norm_num)
      (show (3:ℝ) < ((12:ℕ):ℝ) by norm_num)
      he1 (show (0 : ℝ) ≤ (2.016:ℝ) by norm_num)
      he2 (show (0 : ℝ) ≤ (7.82208:ℝ) by norm_num)
      (show 2 * (1 + 1 / ((12:ℕ):ℝ) ^ 2) * (1 + (4 / 27) * (2.016:ℝ))
        * (32 * (7.82208:ℝ) * ((12:ℕ):ℝ) ^ 2 + 44 + 2 * (12 + 16 / 27) * (2.016:ℝ))
        ≤ (307.44:ℝ) ^ 2 by norm_num)
      (show (0 : ℝ) ≤ (307.44:ℝ) by norm_num)
    have hF : ((9:ℕ):ℝ) ≤ besselF (3:ℝ) ((12:ℕ):ℝ) := by
      have hq : ((12:ℕ):ℝ) = (12:ℝ) := by norm_num
      have hk : ((9:ℕ):ℝ) = (9:ℝ) := by norm_num
      rw [hq, hk]
      unfold besselF besselAlpha
      have g1 : (0.6931471803+1.0986122885:ℝ) ≤ Real.arcosh ((12:ℝ) / (3:ℝ)) := by
        rw [← hq]
        exact hα
      have g2 : Real.sqrt ((12:ℝ) ^ 2 - (3:ℝ) ^ 2) ≤ (12:ℝ) := by
        rw [← hq]
        exact hsqU
      have hmul : (12:ℝ) * (0.6931471803+1.0986122885:ℝ)
          ≤ (12:ℝ) * Real.arcosh ((12:ℝ) / (3:ℝ)) :=
        mul_le_mul_of_nonneg_left g1 (by norm_num)
      have key : (9:ℝ) ≤ (12:ℝ) * (0.6931471803+1.0986122885:ℝ) - (12:ℝ) := by norm_num
      calc (9:ℝ) ≤ (12:ℝ) * (0.6931471803+1.0986122885:ℝ) - (12:ℝ) := key
        _ ≤ (12:ℝ) * Real.arcosh ((12:ℝ) / (3:ℝ))
            - Real.sqrt ((12:ℝ) ^ 2 - (3:ℝ) ^ 2) :=
          sub_le_sub hmul g2
    have hEpow : (8103:ℝ) ≤ (2.7182818283 : ℝ) ^ 9 := by norm_num
    have hexp : Real.exp (-(besselF (3:ℝ) ((12:ℕ):ℝ))) ≤ 1 / (8103:ℝ) :=
      nr_exp_neg_le hF hEpow (by norm_num)
    have hN : 2 * Real.sqrt (Real.pi / 8) ≤ (1.42 : ℝ) := by
      have hpi : Real.pi ≤ (4 : ℝ) := Real.pi_lt_four.le
      have h : Real.sqrt (Real.pi / 8) ≤ Real.sqrt ((4 : ℝ) / 8) :=
        Real.sqrt_le_sqrt (by linarith [hpi])
      have h4 : Real.sqrt ((4 : ℝ) / 8) ≤ (0.71 : ℝ) := by
        rw [Real.sqrt_le_iff]
        refine ⟨by norm_num, by norm_num⟩
      calc 2 * Real.sqrt (Real.pi / 8) ≤ 2 * Real.sqrt ((4:ℝ)/8) :=
            mul_le_mul_of_nonneg_left h (by norm_num)
        _ ≤ 2 * (0.71:ℝ) := mul_le_mul_of_nonneg_left h4 (by norm_num)
        _ = (1.42:ℝ) := by norm_num
    have hE := nrE2star_le_of hexp (show (0 : ℝ) ≤ 1 / (8103:ℝ) by norm_num)
      htlo (show (0 : ℝ) < (3.31:ℝ) by norm_num)
      hr (show ((1/6):ℝ) < 1 by norm_num)
      hN (show (0 : ℝ) ≤ (1.42 : ℝ) by norm_num)
    have hfin : ((2 / 3) * (1 / ((12:ℕ):ℝ)) * (307.44:ℝ)) * (((12:ℕ):ℝ)) ^ 2
        * ((1.42 : ℝ) * (1 / (8103:ℝ)) / ((3.31:ℝ) * (1 - ((1/6):ℝ)))) < 1 / 2 := by
      norm_num
    have hnnC : (0 : ℝ) ≤ nrCcal (3:ℝ) 12 * (((12:ℕ):ℝ)) ^ 2 :=
      mul_nonneg (nrCcal_nonneg _ _ (by norm_num)) (sq_nonneg _)
    have hαnn : (0 : ℝ) ≤ besselAlpha (3:ℝ) (((12:ℕ):ℝ)) := by
      rw [hba]
      exact le_trans (show (0:ℝ) ≤ (0.6931471803+1.0986122885:ℝ) by norm_num) hα
    have hnnE : (0 : ℝ) ≤ nrE2star (3:ℝ) 12 := nrE2star_nonneg hαnn
    have hCnn : (0 : ℝ) ≤ (2 / 3) * (1 / ((12:ℕ):ℝ)) * (307.44:ℝ) := by
      have h1 : (0 : ℝ) ≤ (2 / 3) * (1 / ((12:ℕ):ℝ)) :=
        mul_nonneg (by norm_num)
          (le_of_lt (one_div_pos.mpr (by norm_num)))
      exact mul_nonneg h1 (by norm_num)
    have step1 : nrCcal (3:ℝ) 12 * (((12:ℕ):ℝ)) ^ 2
        ≤ ((2 / 3) * (1 / ((12:ℕ):ℝ)) * (307.44:ℝ)) * (((12:ℕ):ℝ)) ^ 2 :=
      mul_le_mul_of_nonneg_right hC (sq_nonneg _)
    have step2 : (nrCcal (3:ℝ) 12 * (((12:ℕ):ℝ)) ^ 2)
          * nrE2star (3:ℝ) 12
        ≤ (((2 / 3) * (1 / ((12:ℕ):ℝ)) * (307.44:ℝ)) * (((12:ℕ):ℝ)) ^ 2)
          * ((1.42 : ℝ) * (1 / (8103:ℝ)) / ((3.31:ℝ) * (1 - ((1/6):ℝ)))) :=
      mul_le_mul step1 hE hnnE (mul_nonneg hCnn (sq_nonneg _))
    have hProd : nrCcal (3:ℝ) 12 * (((12:ℕ):ℝ)) ^ 2
        * nrE2star (3:ℝ) 12 < 1 / 2 :=
      lt_of_le_of_lt step2 hfin
    exact hProd
  have hcost := new_rung_final (hN := by norm_num) (hφ0 := Real.pi_pos)
    (hφπ := le_rfl) (hAdm := hAdm) (τ := (3 : ℝ)) (hτ1 := by norm_num)
    (hlt := by norm_num) hmain12
  calc (6:ℝ) = 2 * (3:ℝ) := by norm_num
    _ ≤ cost θ := le_of_lt hcost

/-- Certified number at `N = 6` (`φ = π`): `cost θ ≥ 8`, via the exact criterion
at `τ = 4`, `q = 14` (criterion value `≈ 0.02643 < 1/2`). -/
theorem cert_N6 {L : ℕ} {α θ : Fin L → ℝ}
    (hAdm : Admissible 6 Real.pi L α θ) : 8 ≤ cost θ := by
  have hmain12 : nrCcal (4:ℝ) 14 * (((14:ℕ):ℝ)) ^ 2
      * nrE2star (4:ℝ) 14 < Real.sin (Real.pi / 4) ^ 2 := by
    rw [sin_pi_div_four_sq]
    have hx1 : (1 : ℝ) < ((14:ℕ):ℝ) / (4:ℝ) := by norm_num
    have hs1 : (3.35:ℝ) ^ 2 ≤ (((14:ℕ):ℝ) / (4:ℝ)) ^ 2 - 1 := by norm_num
    have hsq1 : (3.35:ℝ)
        ≤ Real.sqrt ((((14:ℕ):ℝ) / (4:ℝ)) ^ 2 - 1) :=
      (Real.le_sqrt (by norm_num) (by norm_num)).mpr hs1
    have hy : (6:ℝ) ≤ ((14:ℕ):ℝ) / (4:ℝ)
        + Real.sqrt ((((14:ℕ):ℝ) / (4:ℝ)) ^ 2 - 1) :=
      le_trans (show (6:ℝ) ≤ ((14:ℕ):ℝ) / (4:ℝ) + (3.35:ℝ) by norm_num)
        (add_le_add (le_refl _) hsq1)
    have ha : Real.log (6:ℝ) ≤ Real.arcosh (((14:ℕ):ℝ) / (4:ℝ)) :=
      log_le_arcosh hx1 (show (0 : ℝ) < (6:ℝ) by norm_num) hy
    have hlogm : Real.log (6:ℝ) = Real.log 2 + Real.log 3 := by
      rw [show (6:ℝ) = 2 * 3 from by norm_num,
        Real.log_mul (by norm_num) (by norm_num)]
    have hα : (0.6931471803+1.0986122885:ℝ) ≤ Real.arcosh (((14:ℕ):ℝ) / (4:ℝ)) :=
      calc (0.6931471803+1.0986122885:ℝ) ≤ Real.log 2 + Real.log 3 :=
            add_le_add Real.log_two_gt_d9.le Real.log_three_gt_d9.le
        _ = Real.log 6 := hlogm.symm
        _ ≤ Real.arcosh (((14:ℕ):ℝ) / (4:ℝ)) := ha
    have hba : besselAlpha (4:ℝ) ((14:ℕ):ℝ)
        = Real.arcosh (((14:ℕ):ℝ) / (4:ℝ)) := rfl
    have hr : nrR (4:ℝ) 14 ≤ ((1/6):ℝ) := by
      have e := exp_neg_arcosh_le_inv hx1 (show (0 : ℝ) < (6:ℝ) by norm_num) hy
      unfold nrR
      rw [hba]
      have e2 : (1 : ℝ) / (6:ℝ) = ((1/6):ℝ) := by norm_num
      rw [← e2]
      exact e
    have he1 : nrEta1of (4:ℝ) 14 ≤ (2.016:ℝ) := by
      have hmono := nrEta1_mono (nrR_nonneg _ _) hr (by norm_num)
      have e : nrEta1 ((1/6):ℝ) = (2.016:ℝ) := by unfold nrEta1; norm_num
      show nrEta1 (nrR (4:ℝ) 14) ≤ _
      calc nrEta1 (nrR (4:ℝ) 14) ≤ nrEta1 ((1/6):ℝ) := hmono
        _ = (2.016:ℝ) := e
    have he2 : nrEta2of (4:ℝ) 14 ≤ (7.82208:ℝ) := by
      have hmono := nrEta2_mono (nrR_nonneg _ _) hr (by norm_num)
      have e : nrEta2 ((1/6):ℝ) = (7.82208:ℝ) := by unfold nrEta2; norm_num
      show nrEta2 (nrR (4:ℝ) 14) ≤ _
      calc nrEta2 (nrR (4:ℝ) 14) ≤ nrEta2 ((1/6):ℝ) := hmono
        _ = (7.82208:ℝ) := e
    have hsqU : Real.sqrt (((14:ℕ):ℝ) ^ 2 - (4:ℝ) ^ 2) ≤ (14:ℝ) := by
      rw [Real.sqrt_le_iff]
      refine ⟨by norm_num, by norm_num⟩
    have hsqL : (13:ℝ) ≤ Real.sqrt (((14:ℕ):ℝ) ^ 2 - (4:ℝ) ^ 2) :=
      (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
    have htlo : (3.6:ℝ)
        ≤ Real.sqrt (Real.sqrt (((14:ℕ):ℝ) ^ 2 - (4:ℝ) ^ 2)) := by
      have htlo2 : (3.6:ℝ) ^ 2
          ≤ Real.sqrt (((14:ℕ):ℝ) ^ 2 - (4:ℝ) ^ 2) :=
        le_trans (by norm_num) hsqL
      exact (Real.le_sqrt (by norm_num) (Real.sqrt_nonneg _)).mpr htlo2
    have hC := nrCcal_le_of (show (2 : ℝ) ≤ ((14:ℕ):ℝ) by norm_num)
      (show (0 : ℝ) < (4:ℝ) by norm_num)
      (show (4:ℝ) < ((14:ℕ):ℝ) by norm_num)
      he1 (show (0 : ℝ) ≤ (2.016:ℝ) by norm_num)
      he2 (show (0 : ℝ) ≤ (7.82208:ℝ) by norm_num)
      (show 2 * (1 + 1 / ((14:ℕ):ℝ) ^ 2) * (1 + (4 / 27) * (2.016:ℝ))
        * (32 * (7.82208:ℝ) * ((14:ℕ):ℝ) ^ 2 + 44 + 2 * (12 + 16 / 27) * (2.016:ℝ))
        ≤ (358.23:ℝ) ^ 2 by norm_num)
      (show (0 : ℝ) ≤ (358.23:ℝ) by norm_num)
    have hF : ((11:ℕ):ℝ) ≤ besselF (4:ℝ) ((14:ℕ):ℝ) := by
      have hq : ((14:ℕ):ℝ) = (14:ℝ) := by norm_num
      have hk : ((11:ℕ):ℝ) = (11:ℝ) := by norm_num
      rw [hq, hk]
      unfold besselF besselAlpha
      have g1 : (0.6931471803+1.0986122885:ℝ) ≤ Real.arcosh ((14:ℝ) / (4:ℝ)) := by
        rw [← hq]
        exact hα
      have g2 : Real.sqrt ((14:ℝ) ^ 2 - (4:ℝ) ^ 2) ≤ (14:ℝ) := by
        rw [← hq]
        exact hsqU
      have hmul : (14:ℝ) * (0.6931471803+1.0986122885:ℝ)
          ≤ (14:ℝ) * Real.arcosh ((14:ℝ) / (4:ℝ)) :=
        mul_le_mul_of_nonneg_left g1 (by norm_num)
      have key : (11:ℝ) ≤ (14:ℝ) * (0.6931471803+1.0986122885:ℝ) - (14:ℝ) := by norm_num
      calc (11:ℝ) ≤ (14:ℝ) * (0.6931471803+1.0986122885:ℝ) - (14:ℝ) := key
        _ ≤ (14:ℝ) * Real.arcosh ((14:ℝ) / (4:ℝ))
            - Real.sqrt ((14:ℝ) ^ 2 - (4:ℝ) ^ 2) :=
          sub_le_sub hmul g2
    have hEpow : (59874:ℝ) ≤ (2.7182818283 : ℝ) ^ 11 := by norm_num
    have hexp : Real.exp (-(besselF (4:ℝ) ((14:ℕ):ℝ))) ≤ 1 / (59874:ℝ) :=
      nr_exp_neg_le hF hEpow (by norm_num)
    have hN : 2 * Real.sqrt (Real.pi / 8) ≤ (1.42 : ℝ) := by
      have hpi : Real.pi ≤ (4 : ℝ) := Real.pi_lt_four.le
      have h : Real.sqrt (Real.pi / 8) ≤ Real.sqrt ((4 : ℝ) / 8) :=
        Real.sqrt_le_sqrt (by linarith [hpi])
      have h4 : Real.sqrt ((4 : ℝ) / 8) ≤ (0.71 : ℝ) := by
        rw [Real.sqrt_le_iff]
        refine ⟨by norm_num, by norm_num⟩
      calc 2 * Real.sqrt (Real.pi / 8) ≤ 2 * Real.sqrt ((4:ℝ)/8) :=
            mul_le_mul_of_nonneg_left h (by norm_num)
        _ ≤ 2 * (0.71:ℝ) := mul_le_mul_of_nonneg_left h4 (by norm_num)
        _ = (1.42:ℝ) := by norm_num
    have hE := nrE2star_le_of hexp (show (0 : ℝ) ≤ 1 / (59874:ℝ) by norm_num)
      htlo (show (0 : ℝ) < (3.6:ℝ) by norm_num)
      hr (show ((1/6):ℝ) < 1 by norm_num)
      hN (show (0 : ℝ) ≤ (1.42 : ℝ) by norm_num)
    have hfin : ((2 / 3) * (1 / ((14:ℕ):ℝ)) * (358.23:ℝ)) * (((14:ℕ):ℝ)) ^ 2
        * ((1.42 : ℝ) * (1 / (59874:ℝ)) / ((3.6:ℝ) * (1 - ((1/6):ℝ)))) < 1 / 2 := by
      norm_num
    have hnnC : (0 : ℝ) ≤ nrCcal (4:ℝ) 14 * (((14:ℕ):ℝ)) ^ 2 :=
      mul_nonneg (nrCcal_nonneg _ _ (by norm_num)) (sq_nonneg _)
    have hαnn : (0 : ℝ) ≤ besselAlpha (4:ℝ) (((14:ℕ):ℝ)) := by
      rw [hba]
      exact le_trans (show (0:ℝ) ≤ (0.6931471803+1.0986122885:ℝ) by norm_num) hα
    have hnnE : (0 : ℝ) ≤ nrE2star (4:ℝ) 14 := nrE2star_nonneg hαnn
    have hCnn : (0 : ℝ) ≤ (2 / 3) * (1 / ((14:ℕ):ℝ)) * (358.23:ℝ) := by
      have h1 : (0 : ℝ) ≤ (2 / 3) * (1 / ((14:ℕ):ℝ)) :=
        mul_nonneg (by norm_num)
          (le_of_lt (one_div_pos.mpr (by norm_num)))
      exact mul_nonneg h1 (by norm_num)
    have step1 : nrCcal (4:ℝ) 14 * (((14:ℕ):ℝ)) ^ 2
        ≤ ((2 / 3) * (1 / ((14:ℕ):ℝ)) * (358.23:ℝ)) * (((14:ℕ):ℝ)) ^ 2 :=
      mul_le_mul_of_nonneg_right hC (sq_nonneg _)
    have step2 : (nrCcal (4:ℝ) 14 * (((14:ℕ):ℝ)) ^ 2)
          * nrE2star (4:ℝ) 14
        ≤ (((2 / 3) * (1 / ((14:ℕ):ℝ)) * (358.23:ℝ)) * (((14:ℕ):ℝ)) ^ 2)
          * ((1.42 : ℝ) * (1 / (59874:ℝ)) / ((3.6:ℝ) * (1 - ((1/6):ℝ)))) :=
      mul_le_mul step1 hE hnnE (mul_nonneg hCnn (sq_nonneg _))
    have hProd : nrCcal (4:ℝ) 14 * (((14:ℕ):ℝ)) ^ 2
        * nrE2star (4:ℝ) 14 < 1 / 2 :=
      lt_of_le_of_lt step2 hfin
    exact hProd
  have hcost := new_rung_final (hN := by norm_num) (hφ0 := Real.pi_pos)
    (hφπ := le_rfl) (hAdm := hAdm) (τ := (4 : ℝ)) (hτ1 := by norm_num)
    (hlt := by norm_num) hmain12
  calc (8:ℝ) = 2 * (4:ℝ) := by norm_num
    _ ≤ cost θ := le_of_lt hcost

/-- Certified number at `N = 7` (`φ = π`): `cost θ ≥ 12`, via the exact criterion
at `τ = 6`, `q = 16` (criterion value `≈ 0.1142 < 1/2`). -/
theorem cert_N7 {L : ℕ} {α θ : Fin L → ℝ}
    (hAdm : Admissible 7 Real.pi L α θ) : 12 ≤ cost θ := by
  have hmain12 : nrCcal (6:ℝ) 16 * (((16:ℕ):ℝ)) ^ 2
      * nrE2star (6:ℝ) 16 < Real.sin (Real.pi / 4) ^ 2 := by
    rw [sin_pi_div_four_sq]
    have hx1 : (1 : ℝ) < ((16:ℕ):ℝ) / (6:ℝ) := by norm_num
    have hs1 : (2.47:ℝ) ^ 2 ≤ (((16:ℕ):ℝ) / (6:ℝ)) ^ 2 - 1 := by norm_num
    have hsq1 : (2.47:ℝ)
        ≤ Real.sqrt ((((16:ℕ):ℝ) / (6:ℝ)) ^ 2 - 1) :=
      (Real.le_sqrt (by norm_num) (by norm_num)).mpr hs1
    have hy : (5:ℝ) ≤ ((16:ℕ):ℝ) / (6:ℝ)
        + Real.sqrt ((((16:ℕ):ℝ) / (6:ℝ)) ^ 2 - 1) :=
      le_trans (show (5:ℝ) ≤ ((16:ℕ):ℝ) / (6:ℝ) + (2.47:ℝ) by norm_num)
        (add_le_add (le_refl _) hsq1)
    have ha : Real.log (5:ℝ) ≤ Real.arcosh (((16:ℕ):ℝ) / (6:ℝ)) :=
      log_le_arcosh hx1 (show (0 : ℝ) < (5:ℝ) by norm_num) hy
    have hα : (1.6094379123:ℝ) ≤ Real.arcosh (((16:ℕ):ℝ) / (6:ℝ)) :=
      le_trans Real.log_five_gt_d9.le ha
    have hba : besselAlpha (6:ℝ) ((16:ℕ):ℝ)
        = Real.arcosh (((16:ℕ):ℝ) / (6:ℝ)) := rfl
    have hr : nrR (6:ℝ) 16 ≤ (0.2:ℝ) := by
      have e := exp_neg_arcosh_le_inv hx1 (show (0 : ℝ) < (5:ℝ) by norm_num) hy
      unfold nrR
      rw [hba]
      have e2 : (1 : ℝ) / (5:ℝ) = (0.2:ℝ) := by norm_num
      rw [← e2]
      exact e
    have he1 : nrEta1of (6:ℝ) 16 ≤ (2.34375:ℝ) := by
      have hmono := nrEta1_mono (nrR_nonneg _ _) hr (by norm_num)
      have e : nrEta1 (0.2:ℝ) = (2.34375:ℝ) := by unfold nrEta1; norm_num
      show nrEta1 (nrR (6:ℝ) 16) ≤ _
      calc nrEta1 (nrR (6:ℝ) 16) ≤ nrEta1 (0.2:ℝ) := hmono
        _ = (2.34375:ℝ) := e
    have he2 : nrEta2of (6:ℝ) 16 ≤ (11.1328125:ℝ) := by
      have hmono := nrEta2_mono (nrR_nonneg _ _) hr (by norm_num)
      have e : nrEta2 (0.2:ℝ) = (11.1328125:ℝ) := by unfold nrEta2; norm_num
      show nrEta2 (nrR (6:ℝ) 16) ≤ _
      calc nrEta2 (nrR (6:ℝ) 16) ≤ nrEta2 (0.2:ℝ) := hmono
        _ = (11.1328125:ℝ) := e
    have hsqU : Real.sqrt (((16:ℕ):ℝ) ^ 2 - (6:ℝ) ^ 2) ≤ (15:ℝ) := by
      rw [Real.sqrt_le_iff]
      refine ⟨by norm_num, by norm_num⟩
    have hsqL : (14:ℝ) ≤ Real.sqrt (((16:ℕ):ℝ) ^ 2 - (6:ℝ) ^ 2) :=
      (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
    have htlo : (3.74:ℝ)
        ≤ Real.sqrt (Real.sqrt (((16:ℕ):ℝ) ^ 2 - (6:ℝ) ^ 2)) := by
      have htlo2 : (3.74:ℝ) ^ 2
          ≤ Real.sqrt (((16:ℕ):ℝ) ^ 2 - (6:ℝ) ^ 2) :=
        le_trans (by norm_num) hsqL
      exact (Real.le_sqrt (by norm_num) (Real.sqrt_nonneg _)).mpr htlo2
    have hC := nrCcal_le_of (show (2 : ℝ) ≤ ((16:ℕ):ℝ) by norm_num)
      (show (0 : ℝ) < (6:ℝ) by norm_num)
      (show (6:ℝ) < ((16:ℕ):ℝ) by norm_num)
      he1 (show (0 : ℝ) ≤ (2.34375:ℝ) by norm_num)
      he2 (show (0 : ℝ) ≤ (11.1328125:ℝ) by norm_num)
      (show 2 * (1 + 1 / ((16:ℕ):ℝ) ^ 2) * (1 + (4 / 27) * (2.34375:ℝ))
        * (32 * (11.1328125:ℝ) * ((16:ℕ):ℝ) ^ 2 + 44 + 2 * (12 + 16 / 27) * (2.34375:ℝ))
        ≤ (496.97:ℝ) ^ 2 by norm_num)
      (show (0 : ℝ) ≤ (496.97:ℝ) by norm_num)
    have hF : ((10:ℕ):ℝ) ≤ besselF (6:ℝ) ((16:ℕ):ℝ) := by
      have hq : ((16:ℕ):ℝ) = (16:ℝ) := by norm_num
      have hk : ((10:ℕ):ℝ) = (10:ℝ) := by norm_num
      rw [hq, hk]
      unfold besselF besselAlpha
      have g1 : (1.6094379123:ℝ) ≤ Real.arcosh ((16:ℝ) / (6:ℝ)) := by
        rw [← hq]
        exact hα
      have g2 : Real.sqrt ((16:ℝ) ^ 2 - (6:ℝ) ^ 2) ≤ (15:ℝ) := by
        rw [← hq]
        exact hsqU
      have hmul : (16:ℝ) * (1.6094379123:ℝ)
          ≤ (16:ℝ) * Real.arcosh ((16:ℝ) / (6:ℝ)) :=
        mul_le_mul_of_nonneg_left g1 (by norm_num)
      have key : (10:ℝ) ≤ (16:ℝ) * (1.6094379123:ℝ) - (15:ℝ) := by norm_num
      calc (10:ℝ) ≤ (16:ℝ) * (1.6094379123:ℝ) - (15:ℝ) := key
        _ ≤ (16:ℝ) * Real.arcosh ((16:ℝ) / (6:ℝ))
            - Real.sqrt ((16:ℝ) ^ 2 - (6:ℝ) ^ 2) :=
          sub_le_sub hmul g2
    have hEpow : (22026:ℝ) ≤ (2.7182818283 : ℝ) ^ 10 := by norm_num
    have hexp : Real.exp (-(besselF (6:ℝ) ((16:ℕ):ℝ))) ≤ 1 / (22026:ℝ) :=
      nr_exp_neg_le hF hEpow (by norm_num)
    have hN : 2 * Real.sqrt (Real.pi / 8) ≤ (1.42 : ℝ) := by
      have hpi : Real.pi ≤ (4 : ℝ) := Real.pi_lt_four.le
      have h : Real.sqrt (Real.pi / 8) ≤ Real.sqrt ((4 : ℝ) / 8) :=
        Real.sqrt_le_sqrt (by linarith [hpi])
      have h4 : Real.sqrt ((4 : ℝ) / 8) ≤ (0.71 : ℝ) := by
        rw [Real.sqrt_le_iff]
        refine ⟨by norm_num, by norm_num⟩
      calc 2 * Real.sqrt (Real.pi / 8) ≤ 2 * Real.sqrt ((4:ℝ)/8) :=
            mul_le_mul_of_nonneg_left h (by norm_num)
        _ ≤ 2 * (0.71:ℝ) := mul_le_mul_of_nonneg_left h4 (by norm_num)
        _ = (1.42:ℝ) := by norm_num
    have hE := nrE2star_le_of hexp (show (0 : ℝ) ≤ 1 / (22026:ℝ) by norm_num)
      htlo (show (0 : ℝ) < (3.74:ℝ) by norm_num)
      hr (show (0.2:ℝ) < 1 by norm_num)
      hN (show (0 : ℝ) ≤ (1.42 : ℝ) by norm_num)
    have hfin : ((2 / 3) * (1 / ((16:ℕ):ℝ)) * (496.97:ℝ)) * (((16:ℕ):ℝ)) ^ 2
        * ((1.42 : ℝ) * (1 / (22026:ℝ)) / ((3.74:ℝ) * (1 - (0.2:ℝ)))) < 1 / 2 := by
      norm_num
    have hnnC : (0 : ℝ) ≤ nrCcal (6:ℝ) 16 * (((16:ℕ):ℝ)) ^ 2 :=
      mul_nonneg (nrCcal_nonneg _ _ (by norm_num)) (sq_nonneg _)
    have hαnn : (0 : ℝ) ≤ besselAlpha (6:ℝ) (((16:ℕ):ℝ)) := by
      rw [hba]
      exact le_trans (show (0:ℝ) ≤ (1.6094379123:ℝ) by norm_num) hα
    have hnnE : (0 : ℝ) ≤ nrE2star (6:ℝ) 16 := nrE2star_nonneg hαnn
    have hCnn : (0 : ℝ) ≤ (2 / 3) * (1 / ((16:ℕ):ℝ)) * (496.97:ℝ) := by
      have h1 : (0 : ℝ) ≤ (2 / 3) * (1 / ((16:ℕ):ℝ)) :=
        mul_nonneg (by norm_num)
          (le_of_lt (one_div_pos.mpr (by norm_num)))
      exact mul_nonneg h1 (by norm_num)
    have step1 : nrCcal (6:ℝ) 16 * (((16:ℕ):ℝ)) ^ 2
        ≤ ((2 / 3) * (1 / ((16:ℕ):ℝ)) * (496.97:ℝ)) * (((16:ℕ):ℝ)) ^ 2 :=
      mul_le_mul_of_nonneg_right hC (sq_nonneg _)
    have step2 : (nrCcal (6:ℝ) 16 * (((16:ℕ):ℝ)) ^ 2)
          * nrE2star (6:ℝ) 16
        ≤ (((2 / 3) * (1 / ((16:ℕ):ℝ)) * (496.97:ℝ)) * (((16:ℕ):ℝ)) ^ 2)
          * ((1.42 : ℝ) * (1 / (22026:ℝ)) / ((3.74:ℝ) * (1 - (0.2:ℝ)))) :=
      mul_le_mul step1 hE hnnE (mul_nonneg hCnn (sq_nonneg _))
    have hProd : nrCcal (6:ℝ) 16 * (((16:ℕ):ℝ)) ^ 2
        * nrE2star (6:ℝ) 16 < 1 / 2 :=
      lt_of_le_of_lt step2 hfin
    exact hProd
  have hcost := new_rung_final (hN := by norm_num) (hφ0 := Real.pi_pos)
    (hφπ := le_rfl) (hAdm := hAdm) (τ := (6 : ℝ)) (hτ1 := by norm_num)
    (hlt := by norm_num) hmain12
  calc (12:ℝ) = 2 * (6:ℝ) := by norm_num
    _ ≤ cost θ := le_of_lt hcost

/-- Certified number at `N = 8` (`φ = π`): `cost θ ≥ 12`, via the exact criterion
at `τ = 6`, `q = 18` (criterion value `≈ 0.0497 < 1/2`). -/
theorem cert_N8 {L : ℕ} {α θ : Fin L → ℝ}
    (hAdm : Admissible 8 Real.pi L α θ) : 12 ≤ cost θ := by
  have hmain12 : nrCcal (6:ℝ) 18 * (((18:ℕ):ℝ)) ^ 2
      * nrE2star (6:ℝ) 18 < Real.sin (Real.pi / 4) ^ 2 := by
    rw [sin_pi_div_four_sq]
    have hx1 : (1 : ℝ) < ((18:ℕ):ℝ) / (6:ℝ) := by norm_num
    have hs1 : (2.82:ℝ) ^ 2 ≤ (((18:ℕ):ℝ) / (6:ℝ)) ^ 2 - 1 := by norm_num
    have hsq1 : (2.82:ℝ)
        ≤ Real.sqrt ((((18:ℕ):ℝ) / (6:ℝ)) ^ 2 - 1) :=
      (Real.le_sqrt (by norm_num) (by norm_num)).mpr hs1
    have hy : (5:ℝ) ≤ ((18:ℕ):ℝ) / (6:ℝ)
        + Real.sqrt ((((18:ℕ):ℝ) / (6:ℝ)) ^ 2 - 1) :=
      le_trans (show (5:ℝ) ≤ ((18:ℕ):ℝ) / (6:ℝ) + (2.82:ℝ) by norm_num)
        (add_le_add (le_refl _) hsq1)
    have ha : Real.log (5:ℝ) ≤ Real.arcosh (((18:ℕ):ℝ) / (6:ℝ)) :=
      log_le_arcosh hx1 (show (0 : ℝ) < (5:ℝ) by norm_num) hy
    have hα : (1.6094379123:ℝ) ≤ Real.arcosh (((18:ℕ):ℝ) / (6:ℝ)) :=
      le_trans Real.log_five_gt_d9.le ha
    have hba : besselAlpha (6:ℝ) ((18:ℕ):ℝ)
        = Real.arcosh (((18:ℕ):ℝ) / (6:ℝ)) := rfl
    have hr : nrR (6:ℝ) 18 ≤ (0.2:ℝ) := by
      have e := exp_neg_arcosh_le_inv hx1 (show (0 : ℝ) < (5:ℝ) by norm_num) hy
      unfold nrR
      rw [hba]
      have e2 : (1 : ℝ) / (5:ℝ) = (0.2:ℝ) := by norm_num
      rw [← e2]
      exact e
    have he1 : nrEta1of (6:ℝ) 18 ≤ (2.34375:ℝ) := by
      have hmono := nrEta1_mono (nrR_nonneg _ _) hr (by norm_num)
      have e : nrEta1 (0.2:ℝ) = (2.34375:ℝ) := by unfold nrEta1; norm_num
      show nrEta1 (nrR (6:ℝ) 18) ≤ _
      calc nrEta1 (nrR (6:ℝ) 18) ≤ nrEta1 (0.2:ℝ) := hmono
        _ = (2.34375:ℝ) := e
    have he2 : nrEta2of (6:ℝ) 18 ≤ (11.1328125:ℝ) := by
      have hmono := nrEta2_mono (nrR_nonneg _ _) hr (by norm_num)
      have e : nrEta2 (0.2:ℝ) = (11.1328125:ℝ) := by unfold nrEta2; norm_num
      show nrEta2 (nrR (6:ℝ) 18) ≤ _
      calc nrEta2 (nrR (6:ℝ) 18) ≤ nrEta2 (0.2:ℝ) := hmono
        _ = (11.1328125:ℝ) := e
    have hsqU : Real.sqrt (((18:ℕ):ℝ) ^ 2 - (6:ℝ) ^ 2) ≤ (17:ℝ) := by
      rw [Real.sqrt_le_iff]
      refine ⟨by norm_num, by norm_num⟩
    have hsqL : (16:ℝ) ≤ Real.sqrt (((18:ℕ):ℝ) ^ 2 - (6:ℝ) ^ 2) :=
      (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
    have htlo : (4:ℝ)
        ≤ Real.sqrt (Real.sqrt (((18:ℕ):ℝ) ^ 2 - (6:ℝ) ^ 2)) := by
      have htlo2 : (4:ℝ) ^ 2
          ≤ Real.sqrt (((18:ℕ):ℝ) ^ 2 - (6:ℝ) ^ 2) :=
        le_trans (by norm_num) hsqL
      exact (Real.le_sqrt (by norm_num) (Real.sqrt_nonneg _)).mpr htlo2
    have hC := nrCcal_le_of (show (2 : ℝ) ≤ ((18:ℕ):ℝ) by norm_num)
      (show (0 : ℝ) < (6:ℝ) by norm_num)
      (show (6:ℝ) < ((18:ℕ):ℝ) by norm_num)
      he1 (show (0 : ℝ) ≤ (2.34375:ℝ) by norm_num)
      he2 (show (0 : ℝ) ≤ (11.1328125:ℝ) by norm_num)
      (show 2 * (1 + 1 / ((18:ℕ):ℝ) ^ 2) * (1 + (4 / 27) * (2.34375:ℝ))
        * (32 * (11.1328125:ℝ) * ((18:ℕ):ℝ) ^ 2 + 44 + 2 * (12 + 16 / 27) * (2.34375:ℝ))
        ≤ (558.79:ℝ) ^ 2 by norm_num)
      (show (0 : ℝ) ≤ (558.79:ℝ) by norm_num)
    have hF : ((11:ℕ):ℝ) ≤ besselF (6:ℝ) ((18:ℕ):ℝ) := by
      have hq : ((18:ℕ):ℝ) = (18:ℝ) := by norm_num
      have hk : ((11:ℕ):ℝ) = (11:ℝ) := by norm_num
      rw [hq, hk]
      unfold besselF besselAlpha
      have g1 : (1.6094379123:ℝ) ≤ Real.arcosh ((18:ℝ) / (6:ℝ)) := by
        rw [← hq]
        exact hα
      have g2 : Real.sqrt ((18:ℝ) ^ 2 - (6:ℝ) ^ 2) ≤ (17:ℝ) := by
        rw [← hq]
        exact hsqU
      have hmul : (18:ℝ) * (1.6094379123:ℝ)
          ≤ (18:ℝ) * Real.arcosh ((18:ℝ) / (6:ℝ)) :=
        mul_le_mul_of_nonneg_left g1 (by norm_num)
      have key : (11:ℝ) ≤ (18:ℝ) * (1.6094379123:ℝ) - (17:ℝ) := by norm_num
      calc (11:ℝ) ≤ (18:ℝ) * (1.6094379123:ℝ) - (17:ℝ) := key
        _ ≤ (18:ℝ) * Real.arcosh ((18:ℝ) / (6:ℝ))
            - Real.sqrt ((18:ℝ) ^ 2 - (6:ℝ) ^ 2) :=
          sub_le_sub hmul g2
    have hEpow : (59874:ℝ) ≤ (2.7182818283 : ℝ) ^ 11 := by norm_num
    have hexp : Real.exp (-(besselF (6:ℝ) ((18:ℕ):ℝ))) ≤ 1 / (59874:ℝ) :=
      nr_exp_neg_le hF hEpow (by norm_num)
    have hN : 2 * Real.sqrt (Real.pi / 8) ≤ (1.42 : ℝ) := by
      have hpi : Real.pi ≤ (4 : ℝ) := Real.pi_lt_four.le
      have h : Real.sqrt (Real.pi / 8) ≤ Real.sqrt ((4 : ℝ) / 8) :=
        Real.sqrt_le_sqrt (by linarith [hpi])
      have h4 : Real.sqrt ((4 : ℝ) / 8) ≤ (0.71 : ℝ) := by
        rw [Real.sqrt_le_iff]
        refine ⟨by norm_num, by norm_num⟩
      calc 2 * Real.sqrt (Real.pi / 8) ≤ 2 * Real.sqrt ((4:ℝ)/8) :=
            mul_le_mul_of_nonneg_left h (by norm_num)
        _ ≤ 2 * (0.71:ℝ) := mul_le_mul_of_nonneg_left h4 (by norm_num)
        _ = (1.42:ℝ) := by norm_num
    have hE := nrE2star_le_of hexp (show (0 : ℝ) ≤ 1 / (59874:ℝ) by norm_num)
      htlo (show (0 : ℝ) < (4:ℝ) by norm_num)
      hr (show (0.2:ℝ) < 1 by norm_num)
      hN (show (0 : ℝ) ≤ (1.42 : ℝ) by norm_num)
    have hfin : ((2 / 3) * (1 / ((18:ℕ):ℝ)) * (558.79:ℝ)) * (((18:ℕ):ℝ)) ^ 2
        * ((1.42 : ℝ) * (1 / (59874:ℝ)) / ((4:ℝ) * (1 - (0.2:ℝ)))) < 1 / 2 := by
      norm_num
    have hnnC : (0 : ℝ) ≤ nrCcal (6:ℝ) 18 * (((18:ℕ):ℝ)) ^ 2 :=
      mul_nonneg (nrCcal_nonneg _ _ (by norm_num)) (sq_nonneg _)
    have hαnn : (0 : ℝ) ≤ besselAlpha (6:ℝ) (((18:ℕ):ℝ)) := by
      rw [hba]
      exact le_trans (show (0:ℝ) ≤ (1.6094379123:ℝ) by norm_num) hα
    have hnnE : (0 : ℝ) ≤ nrE2star (6:ℝ) 18 := nrE2star_nonneg hαnn
    have hCnn : (0 : ℝ) ≤ (2 / 3) * (1 / ((18:ℕ):ℝ)) * (558.79:ℝ) := by
      have h1 : (0 : ℝ) ≤ (2 / 3) * (1 / ((18:ℕ):ℝ)) :=
        mul_nonneg (by norm_num)
          (le_of_lt (one_div_pos.mpr (by norm_num)))
      exact mul_nonneg h1 (by norm_num)
    have step1 : nrCcal (6:ℝ) 18 * (((18:ℕ):ℝ)) ^ 2
        ≤ ((2 / 3) * (1 / ((18:ℕ):ℝ)) * (558.79:ℝ)) * (((18:ℕ):ℝ)) ^ 2 :=
      mul_le_mul_of_nonneg_right hC (sq_nonneg _)
    have step2 : (nrCcal (6:ℝ) 18 * (((18:ℕ):ℝ)) ^ 2)
          * nrE2star (6:ℝ) 18
        ≤ (((2 / 3) * (1 / ((18:ℕ):ℝ)) * (558.79:ℝ)) * (((18:ℕ):ℝ)) ^ 2)
          * ((1.42 : ℝ) * (1 / (59874:ℝ)) / ((4:ℝ) * (1 - (0.2:ℝ)))) :=
      mul_le_mul step1 hE hnnE (mul_nonneg hCnn (sq_nonneg _))
    have hProd : nrCcal (6:ℝ) 18 * (((18:ℕ):ℝ)) ^ 2
        * nrE2star (6:ℝ) 18 < 1 / 2 :=
      lt_of_le_of_lt step2 hfin
    exact hProd
  have hcost := new_rung_final (hN := by norm_num) (hφ0 := Real.pi_pos)
    (hφπ := le_rfl) (hAdm := hAdm) (τ := (6 : ℝ)) (hτ1 := by norm_num)
    (hlt := by norm_num) hmain12
  calc (12:ℝ) = 2 * (6:ℝ) := by norm_num
    _ ≤ cost θ := le_of_lt hcost

/-- Certified number at `N = 9` (`φ = π`): `cost θ ≥ 14`, via the exact criterion
at `τ = 7`, `q = 20` (criterion value `≈ 0.007831 < 1/2`). -/
theorem cert_N9 {L : ℕ} {α θ : Fin L → ℝ}
    (hAdm : Admissible 9 Real.pi L α θ) : 14 ≤ cost θ := by
  have hmain12 : nrCcal (7:ℝ) 20 * (((20:ℕ):ℝ)) ^ 2
      * nrE2star (7:ℝ) 20 < Real.sin (Real.pi / 4) ^ 2 := by
    rw [sin_pi_div_four_sq]
    have hx1 : (1 : ℝ) < ((20:ℕ):ℝ) / (7:ℝ) := by norm_num
    have hs1 : (2.67:ℝ) ^ 2 ≤ (((20:ℕ):ℝ) / (7:ℝ)) ^ 2 - 1 := by norm_num
    have hsq1 : (2.67:ℝ)
        ≤ Real.sqrt ((((20:ℕ):ℝ) / (7:ℝ)) ^ 2 - 1) :=
      (Real.le_sqrt (by norm_num) (by norm_num)).mpr hs1
    have hy : (5:ℝ) ≤ ((20:ℕ):ℝ) / (7:ℝ)
        + Real.sqrt ((((20:ℕ):ℝ) / (7:ℝ)) ^ 2 - 1) :=
      le_trans (show (5:ℝ) ≤ ((20:ℕ):ℝ) / (7:ℝ) + (2.67:ℝ) by norm_num)
        (add_le_add (le_refl _) hsq1)
    have ha : Real.log (5:ℝ) ≤ Real.arcosh (((20:ℕ):ℝ) / (7:ℝ)) :=
      log_le_arcosh hx1 (show (0 : ℝ) < (5:ℝ) by norm_num) hy
    have hα : (1.6094379123:ℝ) ≤ Real.arcosh (((20:ℕ):ℝ) / (7:ℝ)) :=
      le_trans Real.log_five_gt_d9.le ha
    have hba : besselAlpha (7:ℝ) ((20:ℕ):ℝ)
        = Real.arcosh (((20:ℕ):ℝ) / (7:ℝ)) := rfl
    have hr : nrR (7:ℝ) 20 ≤ (0.2:ℝ) := by
      have e := exp_neg_arcosh_le_inv hx1 (show (0 : ℝ) < (5:ℝ) by norm_num) hy
      unfold nrR
      rw [hba]
      have e2 : (1 : ℝ) / (5:ℝ) = (0.2:ℝ) := by norm_num
      rw [← e2]
      exact e
    have he1 : nrEta1of (7:ℝ) 20 ≤ (2.34375:ℝ) := by
      have hmono := nrEta1_mono (nrR_nonneg _ _) hr (by norm_num)
      have e : nrEta1 (0.2:ℝ) = (2.34375:ℝ) := by unfold nrEta1; norm_num
      show nrEta1 (nrR (7:ℝ) 20) ≤ _
      calc nrEta1 (nrR (7:ℝ) 20) ≤ nrEta1 (0.2:ℝ) := hmono
        _ = (2.34375:ℝ) := e
    have he2 : nrEta2of (7:ℝ) 20 ≤ (11.1328125:ℝ) := by
      have hmono := nrEta2_mono (nrR_nonneg _ _) hr (by norm_num)
      have e : nrEta2 (0.2:ℝ) = (11.1328125:ℝ) := by unfold nrEta2; norm_num
      show nrEta2 (nrR (7:ℝ) 20) ≤ _
      calc nrEta2 (nrR (7:ℝ) 20) ≤ nrEta2 (0.2:ℝ) := hmono
        _ = (11.1328125:ℝ) := e
    have hsqU : Real.sqrt (((20:ℕ):ℝ) ^ 2 - (7:ℝ) ^ 2) ≤ (19:ℝ) := by
      rw [Real.sqrt_le_iff]
      refine ⟨by norm_num, by norm_num⟩
    have hsqL : (18:ℝ) ≤ Real.sqrt (((20:ℕ):ℝ) ^ 2 - (7:ℝ) ^ 2) :=
      (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
    have htlo : (4.24:ℝ)
        ≤ Real.sqrt (Real.sqrt (((20:ℕ):ℝ) ^ 2 - (7:ℝ) ^ 2)) := by
      have htlo2 : (4.24:ℝ) ^ 2
          ≤ Real.sqrt (((20:ℕ):ℝ) ^ 2 - (7:ℝ) ^ 2) :=
        le_trans (by norm_num) hsqL
      exact (Real.le_sqrt (by norm_num) (Real.sqrt_nonneg _)).mpr htlo2
    have hC := nrCcal_le_of (show (2 : ℝ) ≤ ((20:ℕ):ℝ) by norm_num)
      (show (0 : ℝ) < (7:ℝ) by norm_num)
      (show (7:ℝ) < ((20:ℕ):ℝ) by norm_num)
      he1 (show (0 : ℝ) ≤ (2.34375:ℝ) by norm_num)
      he2 (show (0 : ℝ) ≤ (11.1328125:ℝ) by norm_num)
      (show 2 * (1 + 1 / ((20:ℕ):ℝ) ^ 2) * (1 + (4 / 27) * (2.34375:ℝ))
        * (32 * (11.1328125:ℝ) * ((20:ℕ):ℝ) ^ 2 + 44 + 2 * (12 + 16 / 27) * (2.34375:ℝ))
        ≤ (620.65:ℝ) ^ 2 by norm_num)
      (show (0 : ℝ) ≤ (620.65:ℝ) by norm_num)
    have hF : ((13:ℕ):ℝ) ≤ besselF (7:ℝ) ((20:ℕ):ℝ) := by
      have hq : ((20:ℕ):ℝ) = (20:ℝ) := by norm_num
      have hk : ((13:ℕ):ℝ) = (13:ℝ) := by norm_num
      rw [hq, hk]
      unfold besselF besselAlpha
      have g1 : (1.6094379123:ℝ) ≤ Real.arcosh ((20:ℝ) / (7:ℝ)) := by
        rw [← hq]
        exact hα
      have g2 : Real.sqrt ((20:ℝ) ^ 2 - (7:ℝ) ^ 2) ≤ (19:ℝ) := by
        rw [← hq]
        exact hsqU
      have hmul : (20:ℝ) * (1.6094379123:ℝ)
          ≤ (20:ℝ) * Real.arcosh ((20:ℝ) / (7:ℝ)) :=
        mul_le_mul_of_nonneg_left g1 (by norm_num)
      have key : (13:ℝ) ≤ (20:ℝ) * (1.6094379123:ℝ) - (19:ℝ) := by norm_num
      calc (13:ℝ) ≤ (20:ℝ) * (1.6094379123:ℝ) - (19:ℝ) := key
        _ ≤ (20:ℝ) * Real.arcosh ((20:ℝ) / (7:ℝ))
            - Real.sqrt ((20:ℝ) ^ 2 - (7:ℝ) ^ 2) :=
          sub_le_sub hmul g2
    have hEpow : (442413:ℝ) ≤ (2.7182818283 : ℝ) ^ 13 := by norm_num
    have hexp : Real.exp (-(besselF (7:ℝ) ((20:ℕ):ℝ))) ≤ 1 / (442413:ℝ) :=
      nr_exp_neg_le hF hEpow (by norm_num)
    have hN : 2 * Real.sqrt (Real.pi / 8) ≤ (1.42 : ℝ) := by
      have hpi : Real.pi ≤ (4 : ℝ) := Real.pi_lt_four.le
      have h : Real.sqrt (Real.pi / 8) ≤ Real.sqrt ((4 : ℝ) / 8) :=
        Real.sqrt_le_sqrt (by linarith [hpi])
      have h4 : Real.sqrt ((4 : ℝ) / 8) ≤ (0.71 : ℝ) := by
        rw [Real.sqrt_le_iff]
        refine ⟨by norm_num, by norm_num⟩
      calc 2 * Real.sqrt (Real.pi / 8) ≤ 2 * Real.sqrt ((4:ℝ)/8) :=
            mul_le_mul_of_nonneg_left h (by norm_num)
        _ ≤ 2 * (0.71:ℝ) := mul_le_mul_of_nonneg_left h4 (by norm_num)
        _ = (1.42:ℝ) := by norm_num
    have hE := nrE2star_le_of hexp (show (0 : ℝ) ≤ 1 / (442413:ℝ) by norm_num)
      htlo (show (0 : ℝ) < (4.24:ℝ) by norm_num)
      hr (show (0.2:ℝ) < 1 by norm_num)
      hN (show (0 : ℝ) ≤ (1.42 : ℝ) by norm_num)
    have hfin : ((2 / 3) * (1 / ((20:ℕ):ℝ)) * (620.65:ℝ)) * (((20:ℕ):ℝ)) ^ 2
        * ((1.42 : ℝ) * (1 / (442413:ℝ)) / ((4.24:ℝ) * (1 - (0.2:ℝ)))) < 1 / 2 := by
      norm_num
    have hnnC : (0 : ℝ) ≤ nrCcal (7:ℝ) 20 * (((20:ℕ):ℝ)) ^ 2 :=
      mul_nonneg (nrCcal_nonneg _ _ (by norm_num)) (sq_nonneg _)
    have hαnn : (0 : ℝ) ≤ besselAlpha (7:ℝ) (((20:ℕ):ℝ)) := by
      rw [hba]
      exact le_trans (show (0:ℝ) ≤ (1.6094379123:ℝ) by norm_num) hα
    have hnnE : (0 : ℝ) ≤ nrE2star (7:ℝ) 20 := nrE2star_nonneg hαnn
    have hCnn : (0 : ℝ) ≤ (2 / 3) * (1 / ((20:ℕ):ℝ)) * (620.65:ℝ) := by
      have h1 : (0 : ℝ) ≤ (2 / 3) * (1 / ((20:ℕ):ℝ)) :=
        mul_nonneg (by norm_num)
          (le_of_lt (one_div_pos.mpr (by norm_num)))
      exact mul_nonneg h1 (by norm_num)
    have step1 : nrCcal (7:ℝ) 20 * (((20:ℕ):ℝ)) ^ 2
        ≤ ((2 / 3) * (1 / ((20:ℕ):ℝ)) * (620.65:ℝ)) * (((20:ℕ):ℝ)) ^ 2 :=
      mul_le_mul_of_nonneg_right hC (sq_nonneg _)
    have step2 : (nrCcal (7:ℝ) 20 * (((20:ℕ):ℝ)) ^ 2)
          * nrE2star (7:ℝ) 20
        ≤ (((2 / 3) * (1 / ((20:ℕ):ℝ)) * (620.65:ℝ)) * (((20:ℕ):ℝ)) ^ 2)
          * ((1.42 : ℝ) * (1 / (442413:ℝ)) / ((4.24:ℝ) * (1 - (0.2:ℝ)))) :=
      mul_le_mul step1 hE hnnE (mul_nonneg hCnn (sq_nonneg _))
    have hProd : nrCcal (7:ℝ) 20 * (((20:ℕ):ℝ)) ^ 2
        * nrE2star (7:ℝ) 20 < 1 / 2 :=
      lt_of_le_of_lt step2 hfin
    exact hProd
  have hcost := new_rung_final (hN := by norm_num) (hφ0 := Real.pi_pos)
    (hφπ := le_rfl) (hAdm := hAdm) (τ := (7 : ℝ)) (hτ1 := by norm_num)
    (hlt := by norm_num) hmain12
  calc (14:ℝ) = 2 * (7:ℝ) := by norm_num
    _ ≤ cost θ := le_of_lt hcost

/-- Certified number at `N = 10` (`φ = π`): `cost θ ≥ 20`, via the exact criterion
at `τ = 10`, `q = 22` (criterion value `≈ 0.2654 < 1/2`). -/
theorem cert_N10 {L : ℕ} {α θ : Fin L → ℝ}
    (hAdm : Admissible 10 Real.pi L α θ) : 20 ≤ cost θ := by
  have hmain12 : nrCcal (10:ℝ) 22 * (((22:ℕ):ℝ)) ^ 2
      * nrE2star (10:ℝ) 22 < Real.sin (Real.pi / 4) ^ 2 := by
    rw [sin_pi_div_four_sq]
    have hx1 : (1 : ℝ) < ((22:ℕ):ℝ) / (10:ℝ) := by norm_num
    have hs1 : (1.95:ℝ) ^ 2 ≤ (((22:ℕ):ℝ) / (10:ℝ)) ^ 2 - 1 := by norm_num
    have hsq1 : (1.95:ℝ)
        ≤ Real.sqrt ((((22:ℕ):ℝ) / (10:ℝ)) ^ 2 - 1) :=
      (Real.le_sqrt (by norm_num) (by norm_num)).mpr hs1
    have hy : (4:ℝ) ≤ ((22:ℕ):ℝ) / (10:ℝ)
        + Real.sqrt ((((22:ℕ):ℝ) / (10:ℝ)) ^ 2 - 1) :=
      le_trans (show (4:ℝ) ≤ ((22:ℕ):ℝ) / (10:ℝ) + (1.95:ℝ) by norm_num)
        (add_le_add (le_refl _) hsq1)
    have ha : Real.log (4:ℝ) ≤ Real.arcosh (((22:ℕ):ℝ) / (10:ℝ)) :=
      log_le_arcosh hx1 (show (0 : ℝ) < (4:ℝ) by norm_num) hy
    have hlogm : Real.log (4:ℝ) = 2 * Real.log 2 := Real.log_four_eq
    have hα : (2*0.6931471803:ℝ) ≤ Real.arcosh (((22:ℕ):ℝ) / (10:ℝ)) :=
      calc (2*0.6931471803:ℝ) ≤ 2 * Real.log 2 :=
            mul_le_mul_of_nonneg_left Real.log_two_gt_d9.le (by norm_num)
        _ = Real.log 4 := hlogm.symm
        _ ≤ Real.arcosh (((22:ℕ):ℝ) / (10:ℝ)) := ha
    have hba : besselAlpha (10:ℝ) ((22:ℕ):ℝ)
        = Real.arcosh (((22:ℕ):ℝ) / (10:ℝ)) := rfl
    have hr : nrR (10:ℝ) 22 ≤ (0.25:ℝ) := by
      have e := exp_neg_arcosh_le_inv hx1 (show (0 : ℝ) < (4:ℝ) by norm_num) hy
      unfold nrR
      rw [hba]
      have e2 : (1 : ℝ) / (4:ℝ) = (0.25:ℝ) := by norm_num
      rw [← e2]
      exact e
    have he1 : nrEta1of (10:ℝ) 22 ≤ ((80/27):ℝ) := by
      have hmono := nrEta1_mono (nrR_nonneg _ _) hr (by norm_num)
      have e : nrEta1 (0.25:ℝ) = ((80/27):ℝ) := by unfold nrEta1; norm_num
      show nrEta1 (nrR (10:ℝ) 22) ≤ _
      calc nrEta1 (nrR (10:ℝ) 22) ≤ nrEta1 (0.25:ℝ) := hmono
        _ = ((80/27):ℝ) := e
    have he2 : nrEta2of (10:ℝ) 22 ≤ ((1520/81):ℝ) := by
      have hmono := nrEta2_mono (nrR_nonneg _ _) hr (by norm_num)
      have e : nrEta2 (0.25:ℝ) = ((1520/81):ℝ) := by unfold nrEta2; norm_num
      show nrEta2 (nrR (10:ℝ) 22) ≤ _
      calc nrEta2 (nrR (10:ℝ) 22) ≤ nrEta2 (0.25:ℝ) := hmono
        _ = ((1520/81):ℝ) := e
    have hsqU : Real.sqrt (((22:ℕ):ℝ) ^ 2 - (10:ℝ) ^ 2) ≤ (20:ℝ) := by
      rw [Real.sqrt_le_iff]
      refine ⟨by norm_num, by norm_num⟩
    have hsqL : (19:ℝ) ≤ Real.sqrt (((22:ℕ):ℝ) ^ 2 - (10:ℝ) ^ 2) :=
      (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
    have htlo : (4.35:ℝ)
        ≤ Real.sqrt (Real.sqrt (((22:ℕ):ℝ) ^ 2 - (10:ℝ) ^ 2)) := by
      have htlo2 : (4.35:ℝ) ^ 2
          ≤ Real.sqrt (((22:ℕ):ℝ) ^ 2 - (10:ℝ) ^ 2) :=
        le_trans (by norm_num) hsqL
      exact (Real.le_sqrt (by norm_num) (Real.sqrt_nonneg _)).mpr htlo2
    have hC := nrCcal_le_of (show (2 : ℝ) ≤ ((22:ℕ):ℝ) by norm_num)
      (show (0 : ℝ) < (10:ℝ) by norm_num)
      (show (10:ℝ) < ((22:ℕ):ℝ) by norm_num)
      he1 (show (0 : ℝ) ≤ ((80/27):ℝ) by norm_num)
      he2 (show (0 : ℝ) ≤ ((1520/81):ℝ) by norm_num)
      (show 2 * (1 + 1 / ((22:ℕ):ℝ) ^ 2) * (1 + (4 / 27) * ((80/27):ℝ))
        * (32 * ((1520/81):ℝ) * ((22:ℕ):ℝ) ^ 2 + 44 + 2 * (12 + 16 / 27) * ((80/27):ℝ))
        ≤ (915.7:ℝ) ^ 2 by norm_num)
      (show (0 : ℝ) ≤ (915.7:ℝ) by norm_num)
    have hF : ((10:ℕ):ℝ) ≤ besselF (10:ℝ) ((22:ℕ):ℝ) := by
      have hq : ((22:ℕ):ℝ) = (22:ℝ) := by norm_num
      have hk : ((10:ℕ):ℝ) = (10:ℝ) := by norm_num
      rw [hq, hk]
      unfold besselF besselAlpha
      have g1 : (2*0.6931471803:ℝ) ≤ Real.arcosh ((22:ℝ) / (10:ℝ)) := by
        rw [← hq]
        exact hα
      have g2 : Real.sqrt ((22:ℝ) ^ 2 - (10:ℝ) ^ 2) ≤ (20:ℝ) := by
        rw [← hq]
        exact hsqU
      have hmul : (22:ℝ) * (2*0.6931471803:ℝ)
          ≤ (22:ℝ) * Real.arcosh ((22:ℝ) / (10:ℝ)) :=
        mul_le_mul_of_nonneg_left g1 (by norm_num)
      have key : (10:ℝ) ≤ (22:ℝ) * (2*0.6931471803:ℝ) - (20:ℝ) := by norm_num
      calc (10:ℝ) ≤ (22:ℝ) * (2*0.6931471803:ℝ) - (20:ℝ) := key
        _ ≤ (22:ℝ) * Real.arcosh ((22:ℝ) / (10:ℝ))
            - Real.sqrt ((22:ℝ) ^ 2 - (10:ℝ) ^ 2) :=
          sub_le_sub hmul g2
    have hEpow : (22026:ℝ) ≤ (2.7182818283 : ℝ) ^ 10 := by norm_num
    have hexp : Real.exp (-(besselF (10:ℝ) ((22:ℕ):ℝ))) ≤ 1 / (22026:ℝ) :=
      nr_exp_neg_le hF hEpow (by norm_num)
    have hN : 2 * Real.sqrt (Real.pi / 8) ≤ (1.42 : ℝ) := by
      have hpi : Real.pi ≤ (4 : ℝ) := Real.pi_lt_four.le
      have h : Real.sqrt (Real.pi / 8) ≤ Real.sqrt ((4 : ℝ) / 8) :=
        Real.sqrt_le_sqrt (by linarith [hpi])
      have h4 : Real.sqrt ((4 : ℝ) / 8) ≤ (0.71 : ℝ) := by
        rw [Real.sqrt_le_iff]
        refine ⟨by norm_num, by norm_num⟩
      calc 2 * Real.sqrt (Real.pi / 8) ≤ 2 * Real.sqrt ((4:ℝ)/8) :=
            mul_le_mul_of_nonneg_left h (by norm_num)
        _ ≤ 2 * (0.71:ℝ) := mul_le_mul_of_nonneg_left h4 (by norm_num)
        _ = (1.42:ℝ) := by norm_num
    have hE := nrE2star_le_of hexp (show (0 : ℝ) ≤ 1 / (22026:ℝ) by norm_num)
      htlo (show (0 : ℝ) < (4.35:ℝ) by norm_num)
      hr (show (0.25:ℝ) < 1 by norm_num)
      hN (show (0 : ℝ) ≤ (1.42 : ℝ) by norm_num)
    have hfin : ((2 / 3) * (1 / ((22:ℕ):ℝ)) * (915.7:ℝ)) * (((22:ℕ):ℝ)) ^ 2
        * ((1.42 : ℝ) * (1 / (22026:ℝ)) / ((4.35:ℝ) * (1 - (0.25:ℝ)))) < 1 / 2 := by
      norm_num
    have hnnC : (0 : ℝ) ≤ nrCcal (10:ℝ) 22 * (((22:ℕ):ℝ)) ^ 2 :=
      mul_nonneg (nrCcal_nonneg _ _ (by norm_num)) (sq_nonneg _)
    have hαnn : (0 : ℝ) ≤ besselAlpha (10:ℝ) (((22:ℕ):ℝ)) := by
      rw [hba]
      exact le_trans (show (0:ℝ) ≤ (2*0.6931471803:ℝ) by norm_num) hα
    have hnnE : (0 : ℝ) ≤ nrE2star (10:ℝ) 22 := nrE2star_nonneg hαnn
    have hCnn : (0 : ℝ) ≤ (2 / 3) * (1 / ((22:ℕ):ℝ)) * (915.7:ℝ) := by
      have h1 : (0 : ℝ) ≤ (2 / 3) * (1 / ((22:ℕ):ℝ)) :=
        mul_nonneg (by norm_num)
          (le_of_lt (one_div_pos.mpr (by norm_num)))
      exact mul_nonneg h1 (by norm_num)
    have step1 : nrCcal (10:ℝ) 22 * (((22:ℕ):ℝ)) ^ 2
        ≤ ((2 / 3) * (1 / ((22:ℕ):ℝ)) * (915.7:ℝ)) * (((22:ℕ):ℝ)) ^ 2 :=
      mul_le_mul_of_nonneg_right hC (sq_nonneg _)
    have step2 : (nrCcal (10:ℝ) 22 * (((22:ℕ):ℝ)) ^ 2)
          * nrE2star (10:ℝ) 22
        ≤ (((2 / 3) * (1 / ((22:ℕ):ℝ)) * (915.7:ℝ)) * (((22:ℕ):ℝ)) ^ 2)
          * ((1.42 : ℝ) * (1 / (22026:ℝ)) / ((4.35:ℝ) * (1 - (0.25:ℝ)))) :=
      mul_le_mul step1 hE hnnE (mul_nonneg hCnn (sq_nonneg _))
    have hProd : nrCcal (10:ℝ) 22 * (((22:ℕ):ℝ)) ^ 2
        * nrE2star (10:ℝ) 22 < 1 / 2 :=
      lt_of_le_of_lt step2 hfin
    exact hProd
  have hcost := new_rung_final (hN := by norm_num) (hφ0 := Real.pi_pos)
    (hφπ := le_rfl) (hAdm := hAdm) (τ := (10 : ℝ)) (hτ1 := by norm_num)
    (hlt := by norm_num) hmain12
  calc (20:ℝ) = 2 * (10:ℝ) := by norm_num
    _ ≤ cost θ := le_of_lt hcost

/-- Certified number at `N = 11` (`φ = π`): `cost θ ≥ 22`, via the exact criterion
at `τ = 11`, `q = 24` (criterion value `≈ 0.1103 < 1/2`). -/
theorem cert_N11 {L : ℕ} {α θ : Fin L → ℝ}
    (hAdm : Admissible 11 Real.pi L α θ) : 22 ≤ cost θ := by
  have hmain12 : nrCcal (11:ℝ) 24 * (((24:ℕ):ℝ)) ^ 2
      * nrE2star (11:ℝ) 24 < Real.sin (Real.pi / 4) ^ 2 := by
    rw [sin_pi_div_four_sq]
    have hx1 : (1 : ℝ) < ((24:ℕ):ℝ) / (11:ℝ) := by norm_num
    have hs1 : (1.93:ℝ) ^ 2 ≤ (((24:ℕ):ℝ) / (11:ℝ)) ^ 2 - 1 := by norm_num
    have hsq1 : (1.93:ℝ)
        ≤ Real.sqrt ((((24:ℕ):ℝ) / (11:ℝ)) ^ 2 - 1) :=
      (Real.le_sqrt (by norm_num) (by norm_num)).mpr hs1
    have hy : (4:ℝ) ≤ ((24:ℕ):ℝ) / (11:ℝ)
        + Real.sqrt ((((24:ℕ):ℝ) / (11:ℝ)) ^ 2 - 1) :=
      le_trans (show (4:ℝ) ≤ ((24:ℕ):ℝ) / (11:ℝ) + (1.93:ℝ) by norm_num)
        (add_le_add (le_refl _) hsq1)
    have ha : Real.log (4:ℝ) ≤ Real.arcosh (((24:ℕ):ℝ) / (11:ℝ)) :=
      log_le_arcosh hx1 (show (0 : ℝ) < (4:ℝ) by norm_num) hy
    have hlogm : Real.log (4:ℝ) = 2 * Real.log 2 := Real.log_four_eq
    have hα : (2*0.6931471803:ℝ) ≤ Real.arcosh (((24:ℕ):ℝ) / (11:ℝ)) :=
      calc (2*0.6931471803:ℝ) ≤ 2 * Real.log 2 :=
            mul_le_mul_of_nonneg_left Real.log_two_gt_d9.le (by norm_num)
        _ = Real.log 4 := hlogm.symm
        _ ≤ Real.arcosh (((24:ℕ):ℝ) / (11:ℝ)) := ha
    have hba : besselAlpha (11:ℝ) ((24:ℕ):ℝ)
        = Real.arcosh (((24:ℕ):ℝ) / (11:ℝ)) := rfl
    have hr : nrR (11:ℝ) 24 ≤ (0.25:ℝ) := by
      have e := exp_neg_arcosh_le_inv hx1 (show (0 : ℝ) < (4:ℝ) by norm_num) hy
      unfold nrR
      rw [hba]
      have e2 : (1 : ℝ) / (4:ℝ) = (0.25:ℝ) := by norm_num
      rw [← e2]
      exact e
    have he1 : nrEta1of (11:ℝ) 24 ≤ ((80/27):ℝ) := by
      have hmono := nrEta1_mono (nrR_nonneg _ _) hr (by norm_num)
      have e : nrEta1 (0.25:ℝ) = ((80/27):ℝ) := by unfold nrEta1; norm_num
      show nrEta1 (nrR (11:ℝ) 24) ≤ _
      calc nrEta1 (nrR (11:ℝ) 24) ≤ nrEta1 (0.25:ℝ) := hmono
        _ = ((80/27):ℝ) := e
    have he2 : nrEta2of (11:ℝ) 24 ≤ ((1520/81):ℝ) := by
      have hmono := nrEta2_mono (nrR_nonneg _ _) hr (by norm_num)
      have e : nrEta2 (0.25:ℝ) = ((1520/81):ℝ) := by unfold nrEta2; norm_num
      show nrEta2 (nrR (11:ℝ) 24) ≤ _
      calc nrEta2 (nrR (11:ℝ) 24) ≤ nrEta2 (0.25:ℝ) := hmono
        _ = ((1520/81):ℝ) := e
    have hsqU : Real.sqrt (((24:ℕ):ℝ) ^ 2 - (11:ℝ) ^ 2) ≤ (22:ℝ) := by
      rw [Real.sqrt_le_iff]
      refine ⟨by norm_num, by norm_num⟩
    have hsqL : (21:ℝ) ≤ Real.sqrt (((24:ℕ):ℝ) ^ 2 - (11:ℝ) ^ 2) :=
      (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
    have htlo : (4.58:ℝ)
        ≤ Real.sqrt (Real.sqrt (((24:ℕ):ℝ) ^ 2 - (11:ℝ) ^ 2)) := by
      have htlo2 : (4.58:ℝ) ^ 2
          ≤ Real.sqrt (((24:ℕ):ℝ) ^ 2 - (11:ℝ) ^ 2) :=
        le_trans (by norm_num) hsqL
      exact (Real.le_sqrt (by norm_num) (Real.sqrt_nonneg _)).mpr htlo2
    have hC := nrCcal_le_of (show (2 : ℝ) ≤ ((24:ℕ):ℝ) by norm_num)
      (show (0 : ℝ) < (11:ℝ) by norm_num)
      (show (11:ℝ) < ((24:ℕ):ℝ) by norm_num)
      he1 (show (0 : ℝ) ≤ ((80/27):ℝ) by norm_num)
      he2 (show (0 : ℝ) ≤ ((1520/81):ℝ) by norm_num)
      (show 2 * (1 + 1 / ((24:ℕ):ℝ) ^ 2) * (1 + (4 / 27) * ((80/27):ℝ))
        * (32 * ((1520/81):ℝ) * ((24:ℕ):ℝ) ^ 2 + 44 + 2 * (12 + 16 / 27) * ((80/27):ℝ))
        ≤ (998.75:ℝ) ^ 2 by norm_num)
      (show (0 : ℝ) ≤ (998.75:ℝ) by norm_num)
    have hF : ((11:ℕ):ℝ) ≤ besselF (11:ℝ) ((24:ℕ):ℝ) := by
      have hq : ((24:ℕ):ℝ) = (24:ℝ) := by norm_num
      have hk : ((11:ℕ):ℝ) = (11:ℝ) := by norm_num
      rw [hq, hk]
      unfold besselF besselAlpha
      have g1 : (2*0.6931471803:ℝ) ≤ Real.arcosh ((24:ℝ) / (11:ℝ)) := by
        rw [← hq]
        exact hα
      have g2 : Real.sqrt ((24:ℝ) ^ 2 - (11:ℝ) ^ 2) ≤ (22:ℝ) := by
        rw [← hq]
        exact hsqU
      have hmul : (24:ℝ) * (2*0.6931471803:ℝ)
          ≤ (24:ℝ) * Real.arcosh ((24:ℝ) / (11:ℝ)) :=
        mul_le_mul_of_nonneg_left g1 (by norm_num)
      have key : (11:ℝ) ≤ (24:ℝ) * (2*0.6931471803:ℝ) - (22:ℝ) := by norm_num
      calc (11:ℝ) ≤ (24:ℝ) * (2*0.6931471803:ℝ) - (22:ℝ) := key
        _ ≤ (24:ℝ) * Real.arcosh ((24:ℝ) / (11:ℝ))
            - Real.sqrt ((24:ℝ) ^ 2 - (11:ℝ) ^ 2) :=
          sub_le_sub hmul g2
    have hEpow : (59874:ℝ) ≤ (2.7182818283 : ℝ) ^ 11 := by norm_num
    have hexp : Real.exp (-(besselF (11:ℝ) ((24:ℕ):ℝ))) ≤ 1 / (59874:ℝ) :=
      nr_exp_neg_le hF hEpow (by norm_num)
    have hN : 2 * Real.sqrt (Real.pi / 8) ≤ (1.42 : ℝ) := by
      have hpi : Real.pi ≤ (4 : ℝ) := Real.pi_lt_four.le
      have h : Real.sqrt (Real.pi / 8) ≤ Real.sqrt ((4 : ℝ) / 8) :=
        Real.sqrt_le_sqrt (by linarith [hpi])
      have h4 : Real.sqrt ((4 : ℝ) / 8) ≤ (0.71 : ℝ) := by
        rw [Real.sqrt_le_iff]
        refine ⟨by norm_num, by norm_num⟩
      calc 2 * Real.sqrt (Real.pi / 8) ≤ 2 * Real.sqrt ((4:ℝ)/8) :=
            mul_le_mul_of_nonneg_left h (by norm_num)
        _ ≤ 2 * (0.71:ℝ) := mul_le_mul_of_nonneg_left h4 (by norm_num)
        _ = (1.42:ℝ) := by norm_num
    have hE := nrE2star_le_of hexp (show (0 : ℝ) ≤ 1 / (59874:ℝ) by norm_num)
      htlo (show (0 : ℝ) < (4.58:ℝ) by norm_num)
      hr (show (0.25:ℝ) < 1 by norm_num)
      hN (show (0 : ℝ) ≤ (1.42 : ℝ) by norm_num)
    have hfin : ((2 / 3) * (1 / ((24:ℕ):ℝ)) * (998.75:ℝ)) * (((24:ℕ):ℝ)) ^ 2
        * ((1.42 : ℝ) * (1 / (59874:ℝ)) / ((4.58:ℝ) * (1 - (0.25:ℝ)))) < 1 / 2 := by
      norm_num
    have hnnC : (0 : ℝ) ≤ nrCcal (11:ℝ) 24 * (((24:ℕ):ℝ)) ^ 2 :=
      mul_nonneg (nrCcal_nonneg _ _ (by norm_num)) (sq_nonneg _)
    have hαnn : (0 : ℝ) ≤ besselAlpha (11:ℝ) (((24:ℕ):ℝ)) := by
      rw [hba]
      exact le_trans (show (0:ℝ) ≤ (2*0.6931471803:ℝ) by norm_num) hα
    have hnnE : (0 : ℝ) ≤ nrE2star (11:ℝ) 24 := nrE2star_nonneg hαnn
    have hCnn : (0 : ℝ) ≤ (2 / 3) * (1 / ((24:ℕ):ℝ)) * (998.75:ℝ) := by
      have h1 : (0 : ℝ) ≤ (2 / 3) * (1 / ((24:ℕ):ℝ)) :=
        mul_nonneg (by norm_num)
          (le_of_lt (one_div_pos.mpr (by norm_num)))
      exact mul_nonneg h1 (by norm_num)
    have step1 : nrCcal (11:ℝ) 24 * (((24:ℕ):ℝ)) ^ 2
        ≤ ((2 / 3) * (1 / ((24:ℕ):ℝ)) * (998.75:ℝ)) * (((24:ℕ):ℝ)) ^ 2 :=
      mul_le_mul_of_nonneg_right hC (sq_nonneg _)
    have step2 : (nrCcal (11:ℝ) 24 * (((24:ℕ):ℝ)) ^ 2)
          * nrE2star (11:ℝ) 24
        ≤ (((2 / 3) * (1 / ((24:ℕ):ℝ)) * (998.75:ℝ)) * (((24:ℕ):ℝ)) ^ 2)
          * ((1.42 : ℝ) * (1 / (59874:ℝ)) / ((4.58:ℝ) * (1 - (0.25:ℝ)))) :=
      mul_le_mul step1 hE hnnE (mul_nonneg hCnn (sq_nonneg _))
    have hProd : nrCcal (11:ℝ) 24 * (((24:ℕ):ℝ)) ^ 2
        * nrE2star (11:ℝ) 24 < 1 / 2 :=
      lt_of_le_of_lt step2 hfin
    exact hProd
  have hcost := new_rung_final (hN := by norm_num) (hφ0 := Real.pi_pos)
    (hφπ := le_rfl) (hAdm := hAdm) (τ := (11 : ℝ)) (hτ1 := by norm_num)
    (hlt := by norm_num) hmain12
  calc (22:ℝ) = 2 * (11:ℝ) := by norm_num
    _ ≤ cost θ := le_of_lt hcost

/-- Certified number at `N = 12` (`φ = π`): `cost θ ≥ 24`, via the exact criterion
at `τ = 12`, `q = 26` (criterion value `≈ 0.04554 < 1/2`). -/
theorem cert_N12 {L : ℕ} {α θ : Fin L → ℝ}
    (hAdm : Admissible 12 Real.pi L α θ) : 24 ≤ cost θ := by
  have hmain12 : nrCcal (12:ℝ) 26 * (((26:ℕ):ℝ)) ^ 2
      * nrE2star (12:ℝ) 26 < Real.sin (Real.pi / 4) ^ 2 := by
    rw [sin_pi_div_four_sq]
    have hx1 : (1 : ℝ) < ((26:ℕ):ℝ) / (12:ℝ) := by norm_num
    have hs1 : (1.92:ℝ) ^ 2 ≤ (((26:ℕ):ℝ) / (12:ℝ)) ^ 2 - 1 := by norm_num
    have hsq1 : (1.92:ℝ)
        ≤ Real.sqrt ((((26:ℕ):ℝ) / (12:ℝ)) ^ 2 - 1) :=
      (Real.le_sqrt (by norm_num) (by norm_num)).mpr hs1
    have hy : (4:ℝ) ≤ ((26:ℕ):ℝ) / (12:ℝ)
        + Real.sqrt ((((26:ℕ):ℝ) / (12:ℝ)) ^ 2 - 1) :=
      le_trans (show (4:ℝ) ≤ ((26:ℕ):ℝ) / (12:ℝ) + (1.92:ℝ) by norm_num)
        (add_le_add (le_refl _) hsq1)
    have ha : Real.log (4:ℝ) ≤ Real.arcosh (((26:ℕ):ℝ) / (12:ℝ)) :=
      log_le_arcosh hx1 (show (0 : ℝ) < (4:ℝ) by norm_num) hy
    have hlogm : Real.log (4:ℝ) = 2 * Real.log 2 := Real.log_four_eq
    have hα : (2*0.6931471803:ℝ) ≤ Real.arcosh (((26:ℕ):ℝ) / (12:ℝ)) :=
      calc (2*0.6931471803:ℝ) ≤ 2 * Real.log 2 :=
            mul_le_mul_of_nonneg_left Real.log_two_gt_d9.le (by norm_num)
        _ = Real.log 4 := hlogm.symm
        _ ≤ Real.arcosh (((26:ℕ):ℝ) / (12:ℝ)) := ha
    have hba : besselAlpha (12:ℝ) ((26:ℕ):ℝ)
        = Real.arcosh (((26:ℕ):ℝ) / (12:ℝ)) := rfl
    have hr : nrR (12:ℝ) 26 ≤ (0.25:ℝ) := by
      have e := exp_neg_arcosh_le_inv hx1 (show (0 : ℝ) < (4:ℝ) by norm_num) hy
      unfold nrR
      rw [hba]
      have e2 : (1 : ℝ) / (4:ℝ) = (0.25:ℝ) := by norm_num
      rw [← e2]
      exact e
    have he1 : nrEta1of (12:ℝ) 26 ≤ ((80/27):ℝ) := by
      have hmono := nrEta1_mono (nrR_nonneg _ _) hr (by norm_num)
      have e : nrEta1 (0.25:ℝ) = ((80/27):ℝ) := by unfold nrEta1; norm_num
      show nrEta1 (nrR (12:ℝ) 26) ≤ _
      calc nrEta1 (nrR (12:ℝ) 26) ≤ nrEta1 (0.25:ℝ) := hmono
        _ = ((80/27):ℝ) := e
    have he2 : nrEta2of (12:ℝ) 26 ≤ ((1520/81):ℝ) := by
      have hmono := nrEta2_mono (nrR_nonneg _ _) hr (by norm_num)
      have e : nrEta2 (0.25:ℝ) = ((1520/81):ℝ) := by unfold nrEta2; norm_num
      show nrEta2 (nrR (12:ℝ) 26) ≤ _
      calc nrEta2 (nrR (12:ℝ) 26) ≤ nrEta2 (0.25:ℝ) := hmono
        _ = ((1520/81):ℝ) := e
    have hsqU : Real.sqrt (((26:ℕ):ℝ) ^ 2 - (12:ℝ) ^ 2) ≤ (24:ℝ) := by
      rw [Real.sqrt_le_iff]
      refine ⟨by norm_num, by norm_num⟩
    have hsqL : (23:ℝ) ≤ Real.sqrt (((26:ℕ):ℝ) ^ 2 - (12:ℝ) ^ 2) :=
      (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
    have htlo : (4.79:ℝ)
        ≤ Real.sqrt (Real.sqrt (((26:ℕ):ℝ) ^ 2 - (12:ℝ) ^ 2)) := by
      have htlo2 : (4.79:ℝ) ^ 2
          ≤ Real.sqrt (((26:ℕ):ℝ) ^ 2 - (12:ℝ) ^ 2) :=
        le_trans (by norm_num) hsqL
      exact (Real.le_sqrt (by norm_num) (Real.sqrt_nonneg _)).mpr htlo2
    have hC := nrCcal_le_of (show (2 : ℝ) ≤ ((26:ℕ):ℝ) by norm_num)
      (show (0 : ℝ) < (12:ℝ) by norm_num)
      (show (12:ℝ) < ((26:ℕ):ℝ) by norm_num)
      he1 (show (0 : ℝ) ≤ ((80/27):ℝ) by norm_num)
      he2 (show (0 : ℝ) ≤ ((1520/81):ℝ) by norm_num)
      (show 2 * (1 + 1 / ((26:ℕ):ℝ) ^ 2) * (1 + (4 / 27) * ((80/27):ℝ))
        * (32 * ((1520/81):ℝ) * ((26:ℕ):ℝ) ^ 2 + 44 + 2 * (12 + 16 / 27) * ((80/27):ℝ))
        ≤ (1081.82:ℝ) ^ 2 by norm_num)
      (show (0 : ℝ) ≤ (1081.82:ℝ) by norm_num)
    have hF : ((12:ℕ):ℝ) ≤ besselF (12:ℝ) ((26:ℕ):ℝ) := by
      have hq : ((26:ℕ):ℝ) = (26:ℝ) := by norm_num
      have hk : ((12:ℕ):ℝ) = (12:ℝ) := by norm_num
      rw [hq, hk]
      unfold besselF besselAlpha
      have g1 : (2*0.6931471803:ℝ) ≤ Real.arcosh ((26:ℝ) / (12:ℝ)) := by
        rw [← hq]
        exact hα
      have g2 : Real.sqrt ((26:ℝ) ^ 2 - (12:ℝ) ^ 2) ≤ (24:ℝ) := by
        rw [← hq]
        exact hsqU
      have hmul : (26:ℝ) * (2*0.6931471803:ℝ)
          ≤ (26:ℝ) * Real.arcosh ((26:ℝ) / (12:ℝ)) :=
        mul_le_mul_of_nonneg_left g1 (by norm_num)
      have key : (12:ℝ) ≤ (26:ℝ) * (2*0.6931471803:ℝ) - (24:ℝ) := by norm_num
      calc (12:ℝ) ≤ (26:ℝ) * (2*0.6931471803:ℝ) - (24:ℝ) := key
        _ ≤ (26:ℝ) * Real.arcosh ((26:ℝ) / (12:ℝ))
            - Real.sqrt ((26:ℝ) ^ 2 - (12:ℝ) ^ 2) :=
          sub_le_sub hmul g2
    have hEpow : (162754:ℝ) ≤ (2.7182818283 : ℝ) ^ 12 := by norm_num
    have hexp : Real.exp (-(besselF (12:ℝ) ((26:ℕ):ℝ))) ≤ 1 / (162754:ℝ) :=
      nr_exp_neg_le hF hEpow (by norm_num)
    have hN : 2 * Real.sqrt (Real.pi / 8) ≤ (1.42 : ℝ) := by
      have hpi : Real.pi ≤ (4 : ℝ) := Real.pi_lt_four.le
      have h : Real.sqrt (Real.pi / 8) ≤ Real.sqrt ((4 : ℝ) / 8) :=
        Real.sqrt_le_sqrt (by linarith [hpi])
      have h4 : Real.sqrt ((4 : ℝ) / 8) ≤ (0.71 : ℝ) := by
        rw [Real.sqrt_le_iff]
        refine ⟨by norm_num, by norm_num⟩
      calc 2 * Real.sqrt (Real.pi / 8) ≤ 2 * Real.sqrt ((4:ℝ)/8) :=
            mul_le_mul_of_nonneg_left h (by norm_num)
        _ ≤ 2 * (0.71:ℝ) := mul_le_mul_of_nonneg_left h4 (by norm_num)
        _ = (1.42:ℝ) := by norm_num
    have hE := nrE2star_le_of hexp (show (0 : ℝ) ≤ 1 / (162754:ℝ) by norm_num)
      htlo (show (0 : ℝ) < (4.79:ℝ) by norm_num)
      hr (show (0.25:ℝ) < 1 by norm_num)
      hN (show (0 : ℝ) ≤ (1.42 : ℝ) by norm_num)
    have hfin : ((2 / 3) * (1 / ((26:ℕ):ℝ)) * (1081.82:ℝ)) * (((26:ℕ):ℝ)) ^ 2
        * ((1.42 : ℝ) * (1 / (162754:ℝ)) / ((4.79:ℝ) * (1 - (0.25:ℝ)))) < 1 / 2 := by
      norm_num
    have hnnC : (0 : ℝ) ≤ nrCcal (12:ℝ) 26 * (((26:ℕ):ℝ)) ^ 2 :=
      mul_nonneg (nrCcal_nonneg _ _ (by norm_num)) (sq_nonneg _)
    have hαnn : (0 : ℝ) ≤ besselAlpha (12:ℝ) (((26:ℕ):ℝ)) := by
      rw [hba]
      exact le_trans (show (0:ℝ) ≤ (2*0.6931471803:ℝ) by norm_num) hα
    have hnnE : (0 : ℝ) ≤ nrE2star (12:ℝ) 26 := nrE2star_nonneg hαnn
    have hCnn : (0 : ℝ) ≤ (2 / 3) * (1 / ((26:ℕ):ℝ)) * (1081.82:ℝ) := by
      have h1 : (0 : ℝ) ≤ (2 / 3) * (1 / ((26:ℕ):ℝ)) :=
        mul_nonneg (by norm_num)
          (le_of_lt (one_div_pos.mpr (by norm_num)))
      exact mul_nonneg h1 (by norm_num)
    have step1 : nrCcal (12:ℝ) 26 * (((26:ℕ):ℝ)) ^ 2
        ≤ ((2 / 3) * (1 / ((26:ℕ):ℝ)) * (1081.82:ℝ)) * (((26:ℕ):ℝ)) ^ 2 :=
      mul_le_mul_of_nonneg_right hC (sq_nonneg _)
    have step2 : (nrCcal (12:ℝ) 26 * (((26:ℕ):ℝ)) ^ 2)
          * nrE2star (12:ℝ) 26
        ≤ (((2 / 3) * (1 / ((26:ℕ):ℝ)) * (1081.82:ℝ)) * (((26:ℕ):ℝ)) ^ 2)
          * ((1.42 : ℝ) * (1 / (162754:ℝ)) / ((4.79:ℝ) * (1 - (0.25:ℝ)))) :=
      mul_le_mul step1 hE hnnE (mul_nonneg hCnn (sq_nonneg _))
    have hProd : nrCcal (12:ℝ) 26 * (((26:ℕ):ℝ)) ^ 2
        * nrE2star (12:ℝ) 26 < 1 / 2 :=
      lt_of_le_of_lt step2 hfin
    exact hProd
  have hcost := new_rung_final (hN := by norm_num) (hφ0 := Real.pi_pos)
    (hφπ := le_rfl) (hAdm := hAdm) (τ := (12 : ℝ)) (hτ1 := by norm_num)
    (hlt := by norm_num) hmain12
  calc (24:ℝ) = 2 * (12:ℝ) := by norm_num
    _ ≤ cost θ := le_of_lt hcost

end RobustZ
