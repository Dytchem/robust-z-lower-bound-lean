/-
Copyright (c) 2025 RobustZ project. All rights reserved.

# `SharpDerivGen`：把 `SharpDeriv` 的 collar 界从 `ρ ≤ 1/32` 推广到 `ρ < 1`

`SharpDeriv` 里的几何级数界（`tsum_add_one_pow_{two,four}_mul_geometric_le`）依赖
`16ρ ≤ 1/2`，在应用里（`r = e^{-δ'}`、`δ'` 很小）**不成立**。本文件给出：

* 一般几何级数界（`0 ≤ ρ < 1`，显式 `1/(1-ρ)` 常数）；
* 用 `(k+j)² ≤ 2k² + 2j²`、`(k+j)⁴ ≤ 8k⁴ + 8j⁴` 的**分裂技巧**得到的尾部级数界，
  常数形如 `k²/(1-ρ) + 1/(1-ρ)³`，从而在应用里把 `1/(1-r')` 与 `ε_h ≤ ε(1-r')/2`
  的因子**相消**，得到与 `k` 无关的常数。

记号：`tailR B τ r = r·e^{2√(B/τ)}`（带 collar 增长因子的几何比）。
-/
import RobustZ.SharpDeriv
import Mathlib.Combinatorics.Enumerative.Stirling

noncomputable section

namespace RobustZ

open Filter MeasureTheory
open scoped Real Topology ComplexConjugate

set_option maxHeartbeats 1000000

/-! ## §1 一般几何级数界 -/

/-- `r' = r·e^{2√(B/τ)}`：带 collar 增长因子的几何比。 -/
noncomputable def tailR (B τ r : ℝ) : ℝ := r * Real.exp (2 * Real.sqrt (B / τ))

lemma tailR_nonneg {B τ r : ℝ} (hr : 0 ≤ r) : 0 ≤ tailR B τ r := by
  rw [tailR]; positivity

/-- `Σ_j j²ρ^j ≤ 2/(1-ρ)³`（`0 ≤ ρ < 1`）。 -/
lemma tsum_sq_mul_geometric_le {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) :
    ∑' j : ℕ, (j : ℝ) ^ 2 * ρ ^ j ≤ 2 / (1 - ρ) ^ 3 := by
  have hr : ‖ρ‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg h0]
  rw [tsum_sq_mul_geometric_of_norm_lt_one (r := ρ) hr]
  have hden : 0 < (1 - ρ) ^ 3 := by positivity
  rw [div_le_div_iff_of_pos_right hden]
  nlinarith [h0, h1]

/-- `Σ_j j⁴ρ^j ≤ 75/(1-ρ)⁵`（`0 ≤ ρ < 1`）。 -/
lemma tsum_pow_four_mul_geometric_le {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) :
    ∑' j : ℕ, (j : ℝ) ^ 4 * ρ ^ j ≤ 75 / (1 - ρ) ^ 5 := by
  have hr : ‖ρ‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg h0]
  rw [tsum_pow_mul_geometric_of_norm_lt_one 4 (r := ρ) hr]
  have hs1 : Nat.stirlingSecond 4 1 = 1 := by decide
  have hs2 : Nat.stirlingSecond 4 2 = 7 := by decide
  have hs3 : Nat.stirlingSecond 4 3 = 6 := by decide
  have hs4 : Nat.stirlingSecond 4 4 = 1 := by decide
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [hs1, hs2, hs3, hs4, Nat.factorial]
  have h1m : 0 < 1 - ρ := by linarith
  field_simp
  nlinarith [h0, h1, sq_nonneg ρ, sq_nonneg (1 - ρ), mul_nonneg h0 (sq_nonneg (1 - ρ)),
    mul_nonneg (mul_nonneg h0 h0) (sq_nonneg (1 - ρ)), mul_nonneg (mul_nonneg h0 h0) h0,
    mul_nonneg (mul_nonneg h0 h0) (mul_nonneg h0 h0), mul_nonneg h0 h0]

lemma summable_sq_mul_geometric {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) :
    Summable (fun j : ℕ => (j : ℝ) ^ 2 * ρ ^ j) := by
  have hr : ‖ρ‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg h0]
  simpa using summable_pow_mul_geometric_of_norm_lt_one 2 (r := ρ) hr

lemma summable_pow_four_mul_geometric {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) :
    Summable (fun j : ℕ => (j : ℝ) ^ 4 * ρ ^ j) := by
  have hr : ‖ρ‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg h0]
  simpa using summable_pow_mul_geometric_of_norm_lt_one 4 (r := ρ) hr

/-- `(a+b)² ≤ 2a² + 2b²`。 -/
lemma add_sq_le_two (a b : ℝ) : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by nlinarith [sq_nonneg (a - b)]

/-- `(a+b)⁴ ≤ 8a⁴ + 8b⁴`（`a,b ≥ 0`）。 -/
lemma add_pow_four_le_eight (a b : ℝ) : (a + b) ^ 4 ≤ 8 * a ^ 4 + 8 * b ^ 4 := by
  have h1 : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := add_sq_le_two a b
  have h2 : (0 : ℝ) ≤ (a + b) ^ 2 := sq_nonneg _
  have h3 : ((a + b) ^ 2) ^ 2 ≤ (2 * a ^ 2 + 2 * b ^ 2) ^ 2 := pow_le_pow_left₀ h2 h1 2
  have h4 : (2 * a ^ 2 + 2 * b ^ 2) ^ 2 ≤ 2 * (2 * a ^ 2) ^ 2 + 2 * (2 * b ^ 2) ^ 2 :=
    add_sq_le_two (2 * a ^ 2) (2 * b ^ 2)
  calc (a + b) ^ 4 = ((a + b) ^ 2) ^ 2 := by ring
    _ ≤ (2 * a ^ 2 + 2 * b ^ 2) ^ 2 := h3
    _ ≤ 2 * (2 * a ^ 2) ^ 2 + 2 * (2 * b ^ 2) ^ 2 := h4
    _ = 8 * a ^ 4 + 8 * b ^ 4 := by ring

/-- `Σ_j (k+j)²ρ^j ≤ 2k²/(1-ρ) + 4/(1-ρ)³`。 -/
lemma tsum_add_pow_two_mul_geometric_le {k : ℕ} {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) :
    ∑' j : ℕ, (((k + j : ℕ)) : ℝ) ^ 2 * ρ ^ j ≤ 2 * (k : ℝ) ^ 2 / (1 - ρ) + 4 / (1 - ρ) ^ 3 := by
  have hden : 0 < 1 - ρ := by linarith
  have hmaj : Summable (fun j : ℕ => 2 * (k : ℝ) ^ 2 * ρ ^ j + 2 * ((j : ℝ) ^ 2 * ρ ^ j)) :=
    ((summable_geometric_of_lt_one h0 h1).mul_left (2 * (k : ℝ) ^ 2)).add
      ((summable_sq_mul_geometric h0 h1).mul_left 2)
  have hpt : ∀ j : ℕ, (((k + j : ℕ)) : ℝ) ^ 2 * ρ ^ j
      ≤ 2 * (k : ℝ) ^ 2 * ρ ^ j + 2 * ((j : ℝ) ^ 2 * ρ ^ j) := by
    intro j
    have h1' : (((k + j : ℕ)) : ℝ) ^ 2 ≤ 2 * (k : ℝ) ^ 2 + 2 * (j : ℝ) ^ 2 := by
      have h : (((k + j : ℕ)) : ℝ) = (k : ℝ) + (j : ℝ) := by push_cast; ring
      rw [h]; exact add_sq_le_two _ _
    calc (((k + j : ℕ)) : ℝ) ^ 2 * ρ ^ j
        ≤ (2 * (k : ℝ) ^ 2 + 2 * (j : ℝ) ^ 2) * ρ ^ j :=
          mul_le_mul_of_nonneg_right h1' (pow_nonneg h0 j)
      _ = 2 * (k : ℝ) ^ 2 * ρ ^ j + 2 * ((j : ℝ) ^ 2 * ρ ^ j) := by ring
  have hs : Summable (fun j : ℕ => (((k + j : ℕ)) : ℝ) ^ 2 * ρ ^ j) :=
    Summable.of_nonneg_of_le (fun j => by positivity) hpt hmaj
  calc ∑' j : ℕ, (((k + j : ℕ)) : ℝ) ^ 2 * ρ ^ j
      ≤ ∑' j : ℕ, (2 * (k : ℝ) ^ 2 * ρ ^ j + 2 * ((j : ℝ) ^ 2 * ρ ^ j)) :=
        Summable.tsum_le_tsum hpt hs hmaj
    _ = 2 * (k : ℝ) ^ 2 * (∑' j : ℕ, ρ ^ j) + 2 * (∑' j : ℕ, (j : ℝ) ^ 2 * ρ ^ j) := by
        rw [Summable.tsum_add ((summable_geometric_of_lt_one h0 h1).mul_left (2 * (k : ℝ) ^ 2))
          ((summable_sq_mul_geometric h0 h1).mul_left 2), tsum_mul_left, tsum_mul_left]
    _ = 2 * (k : ℝ) ^ 2 * (1 - ρ)⁻¹ + 2 * (∑' j : ℕ, (j : ℝ) ^ 2 * ρ ^ j) := by
        rw [tsum_geometric_of_lt_one h0 h1]
    _ ≤ 2 * (k : ℝ) ^ 2 * (1 - ρ)⁻¹ + 2 * (2 / (1 - ρ) ^ 3) := by
        have h2 := tsum_sq_mul_geometric_le h0 h1
        linarith
    _ = 2 * (k : ℝ) ^ 2 / (1 - ρ) + 4 / (1 - ρ) ^ 3 := by
        rw [div_eq_mul_inv]; ring

/-- `Σ_j (k+j)⁴ρ^j ≤ 8k⁴/(1-ρ) + 600/(1-ρ)⁵`。 -/
lemma tsum_add_pow_four_mul_geometric_le {k : ℕ} {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) :
    ∑' j : ℕ, (((k + j : ℕ)) : ℝ) ^ 4 * ρ ^ j
      ≤ 8 * (k : ℝ) ^ 4 / (1 - ρ) + 600 / (1 - ρ) ^ 5 := by
  have hden : 0 < 1 - ρ := by linarith
  have hmaj : Summable (fun j : ℕ => 8 * (k : ℝ) ^ 4 * ρ ^ j + 8 * ((j : ℝ) ^ 4 * ρ ^ j)) :=
    ((summable_geometric_of_lt_one h0 h1).mul_left (8 * (k : ℝ) ^ 4)).add
      ((summable_pow_four_mul_geometric h0 h1).mul_left 8)
  have hpt : ∀ j : ℕ, (((k + j : ℕ)) : ℝ) ^ 4 * ρ ^ j
      ≤ 8 * (k : ℝ) ^ 4 * ρ ^ j + 8 * ((j : ℝ) ^ 4 * ρ ^ j) := by
    intro j
    have h1' : (((k + j : ℕ)) : ℝ) ^ 4 ≤ 8 * (k : ℝ) ^ 4 + 8 * (j : ℝ) ^ 4 := by
      have h : (((k + j : ℕ)) : ℝ) = (k : ℝ) + (j : ℝ) := by push_cast; ring
      rw [h]; exact add_pow_four_le_eight _ _
    calc (((k + j : ℕ)) : ℝ) ^ 4 * ρ ^ j
        ≤ (8 * (k : ℝ) ^ 4 + 8 * (j : ℝ) ^ 4) * ρ ^ j :=
          mul_le_mul_of_nonneg_right h1' (pow_nonneg h0 j)
      _ = 8 * (k : ℝ) ^ 4 * ρ ^ j + 8 * ((j : ℝ) ^ 4 * ρ ^ j) := by ring
  have hs : Summable (fun j : ℕ => (((k + j : ℕ)) : ℝ) ^ 4 * ρ ^ j) :=
    Summable.of_nonneg_of_le (fun j => by positivity) hpt hmaj
  calc ∑' j : ℕ, (((k + j : ℕ)) : ℝ) ^ 4 * ρ ^ j
      ≤ ∑' j : ℕ, (8 * (k : ℝ) ^ 4 * ρ ^ j + 8 * ((j : ℝ) ^ 4 * ρ ^ j)) :=
        Summable.tsum_le_tsum hpt hs hmaj
    _ = 8 * (k : ℝ) ^ 4 * (∑' j : ℕ, ρ ^ j) + 8 * (∑' j : ℕ, (j : ℝ) ^ 4 * ρ ^ j) := by
        rw [Summable.tsum_add ((summable_geometric_of_lt_one h0 h1).mul_left (8 * (k : ℝ) ^ 4))
          ((summable_pow_four_mul_geometric h0 h1).mul_left 8), tsum_mul_left, tsum_mul_left]
    _ = 8 * (k : ℝ) ^ 4 * (1 - ρ)⁻¹ + 8 * (∑' j : ℕ, (j : ℝ) ^ 4 * ρ ^ j) := by
        rw [tsum_geometric_of_lt_one h0 h1]
    _ ≤ 8 * (k : ℝ) ^ 4 * (1 - ρ)⁻¹ + 8 * (75 / (1 - ρ) ^ 5) := by
        have h2 := tsum_pow_four_mul_geometric_le h0 h1
        linarith
    _ = 8 * (k : ℝ) ^ 4 / (1 - ρ) + 600 / (1 - ρ) ^ 5 := by
        rw [div_eq_mul_inv]; ring

lemma summable_add_pow_two_mul_geometric {k : ℕ} {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) :
    Summable (fun j : ℕ => (((k + j : ℕ)) : ℝ) ^ 2 * ρ ^ j) := by
  have hmaj : Summable (fun j : ℕ => 2 * (k : ℝ) ^ 2 * ρ ^ j + 2 * ((j : ℝ) ^ 2 * ρ ^ j)) :=
    ((summable_geometric_of_lt_one h0 h1).mul_left (2 * (k : ℝ) ^ 2)).add
      ((summable_sq_mul_geometric h0 h1).mul_left 2)
  exact Summable.of_nonneg_of_le (fun j => by positivity)
    (fun j => by
      have h1' : (((k + j : ℕ)) : ℝ) ^ 2 ≤ 2 * (k : ℝ) ^ 2 + 2 * (j : ℝ) ^ 2 := by
        have h : (((k + j : ℕ)) : ℝ) = (k : ℝ) + (j : ℝ) := by push_cast; ring
        rw [h]; exact add_sq_le_two _ _
      calc (((k + j : ℕ)) : ℝ) ^ 2 * ρ ^ j
          ≤ (2 * (k : ℝ) ^ 2 + 2 * (j : ℝ) ^ 2) * ρ ^ j :=
            mul_le_mul_of_nonneg_right h1' (pow_nonneg h0 j)
        _ = 2 * (k : ℝ) ^ 2 * ρ ^ j + 2 * ((j : ℝ) ^ 2 * ρ ^ j) := by ring) hmaj

lemma summable_add_pow_four_mul_geometric {k : ℕ} {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) :
    Summable (fun j : ℕ => (((k + j : ℕ)) : ℝ) ^ 4 * ρ ^ j) := by
  have hmaj : Summable (fun j : ℕ => 8 * (k : ℝ) ^ 4 * ρ ^ j + 8 * ((j : ℝ) ^ 4 * ρ ^ j)) :=
    ((summable_geometric_of_lt_one h0 h1).mul_left (8 * (k : ℝ) ^ 4)).add
      ((summable_pow_four_mul_geometric h0 h1).mul_left 8)
  exact Summable.of_nonneg_of_le (fun j => by positivity)
    (fun j => by
      have h1' : (((k + j : ℕ)) : ℝ) ^ 4 ≤ 8 * (k : ℝ) ^ 4 + 8 * (j : ℝ) ^ 4 := by
        have h : (((k + j : ℕ)) : ℝ) = (k : ℝ) + (j : ℝ) := by push_cast; ring
        rw [h]; exact add_pow_four_le_eight _ _
      calc (((k + j : ℕ)) : ℝ) ^ 4 * ρ ^ j
          ≤ (8 * (k : ℝ) ^ 4 + 8 * (j : ℝ) ^ 4) * ρ ^ j :=
            mul_le_mul_of_nonneg_right h1' (pow_nonneg h0 j)
        _ = 8 * (k : ℝ) ^ 4 * ρ ^ j + 8 * ((j : ℝ) ^ 4 * ρ ^ j) := by ring) hmaj


/-! ## §2 collar 上的值与导数界（`ρ < 1` 版本） -/

/-- **值界（一般 `ρ`）**：`‖Q(τu)‖ ≤ 2e^{kg}ε/(1-r')`，`r' = r·e^{2√(B/τ)}`。 -/
lemma norm_chebTail_le_gen (τ B : ℝ) (hτ : 0 < τ) (hB : 0 < B) {k : ℕ}
    {ε r : ℝ} (hε : 0 ≤ ε) (hr : 0 ≤ r) (hr1 : tailR B τ r < 1)
    (hdec : ∀ j : ℕ, ‖fcoef τ (((k + j : ℕ)) : ℤ)‖ ≤ ε * r ^ j)
    {u : ℝ} (hu : |u| ≤ 1 + B / τ) :
    ‖chebTail τ k u‖
      ≤ 2 * Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ))) * ε / (1 - tailR B τ r) := by
  set g : ℝ := 2 * Real.sqrt (B / τ) with hg
  set ρ : ℝ := tailR B τ r with hρdef
  have hρ0 : 0 ≤ ρ := by rw [hρdef]; exact tailR_nonneg hr
  have hρ1 : ρ < 1 := by rw [hρdef]; exact hr1
  have hpt : ∀ j : ℕ, ‖2 * fcoef τ (((k + j : ℕ)) : ℤ)
        * ((((Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).eval u : ℝ)) : ℂ)‖
      ≤ (2 * ε * Real.exp ((k : ℝ) * g)) * ρ ^ j := by
    intro j
    have h := norm_chebTail_term_le (k := k) (j := j) τ B hτ hB hε hr hdec hu
    have hρ' : r * Real.exp g = ρ := by rw [hρdef, tailR, hg]
    rw [← hg, hρ'] at h
    exact h
  have hmaj : Summable (fun j : ℕ => (2 * ε * Real.exp ((k : ℝ) * g)) * ρ ^ j) :=
    (summable_geometric_of_lt_one hρ0 hρ1).mul_left _
  have hs : Summable (fun j : ℕ => ‖2 * fcoef τ (((k + j : ℕ)) : ℤ)
        * ((((Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).eval u : ℝ)) : ℂ)‖) :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _) hpt hmaj
  calc ‖chebTail τ k u‖
      ≤ ∑' j : ℕ, ‖2 * fcoef τ (((k + j : ℕ)) : ℤ)
          * ((((Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).eval u : ℝ)) : ℂ)‖ :=
        norm_tsum_le_tsum_norm hs
    _ ≤ ∑' j : ℕ, (2 * ε * Real.exp ((k : ℝ) * g)) * ρ ^ j := Summable.tsum_le_tsum hpt hs hmaj
    _ = (2 * ε * Real.exp ((k : ℝ) * g)) * (1 - ρ)⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hρ0 hρ1]
    _ = 2 * Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ))) * ε / (1 - tailR B τ r) := by
        rw [hρdef, hg]; ring

/-- 单项 `2c_{k+j}T'_{k+j}(y)` 的 collar 界（用 `(k+j)²` 而非 `k²(j+1)²`）。 -/
lemma norm_chebTailD1_term_le_gen (τ B : ℝ) (hτ : 0 < τ) (hB : 0 < B) {k j : ℕ}
    {ε r : ℝ} (hε : 0 ≤ ε) (hr : 0 ≤ r)
    (hdec : ∀ i : ℕ, ‖fcoef τ (((k + i : ℕ)) : ℤ)‖ ≤ ε * r ^ i)
    {y : ℝ} (hy : |y| ≤ 1 + B / τ) :
    ‖2 * fcoef τ (((k + j : ℕ)) : ℤ)
        * ((((Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).derivative.eval y : ℝ)) : ℂ)‖
      ≤ 2 * ε * Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ)))
        * ((((k + j : ℕ)) : ℝ) ^ 2 * tailR B τ r ^ j) := by
  set g : ℝ := 2 * Real.sqrt (B / τ) with hg
  have hg0 : 0 ≤ g := by rw [hg]; positivity
  have hBτ0 : 0 ≤ B / τ := by positivity
  have habs : |((((k + j : ℕ)) : ℤ) : ℝ)| = (((k + j : ℕ)) : ℝ) :=
    abs_of_nonneg (by positivity)
  have hT := abs_deriv_chebyshevT_le_exp (((k + j : ℕ)) : ℤ) hBτ0 hy
  rw [habs] at hT
  have hTg : |(Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).derivative.eval y|
      ≤ (((k + j : ℕ)) : ℝ) ^ 2 * Real.exp ((((k + j : ℕ)) : ℝ) * g) := by
    refine hT.trans (le_of_eq ?_)
    rw [hg]; push_cast; ring_nf
  have hexp : Real.exp ((((k + j : ℕ)) : ℝ) * g)
      = Real.exp ((k : ℝ) * g) * (Real.exp g) ^ j := by
    rw [show ((((k + j : ℕ)) : ℝ) * g) = (k : ℝ) * g + (j : ℝ) * g by push_cast; ring,
      Real.exp_add]
    congr 1
    exact Real.exp_nat_mul g j
  have hsplit : ‖2 * fcoef τ (((k + j : ℕ)) : ℤ)
        * ((((Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).derivative.eval y : ℝ)) : ℂ)‖
      = 2 * ‖fcoef τ (((k + j : ℕ)) : ℤ)‖
        * |(Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).derivative.eval y| := by
    rw [norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs]
  rw [hsplit]
  have htarget : 2 * ε * Real.exp ((k : ℝ) * g)
        * ((((k + j : ℕ)) : ℝ) ^ 2 * tailR B τ r ^ j)
      = 2 * (ε * r ^ j) * ((((k + j : ℕ)) : ℝ) ^ 2
          * (Real.exp ((k : ℝ) * g) * (Real.exp g) ^ j)) := by
    rw [tailR, hg, mul_pow]; ring
  rw [htarget]
  have h2 : |(Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).derivative.eval y|
      ≤ (((k + j : ℕ)) : ℝ) ^ 2 * (Real.exp ((k : ℝ) * g) * (Real.exp g) ^ j) := by
    rw [← hexp]; exact hTg
  have h1 := hdec j
  have hc0 : (0 : ℝ) ≤ ‖fcoef τ (((k + j : ℕ)) : ℤ)‖ := norm_nonneg _
  have hT0 : (0 : ℝ) ≤
    |(Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).derivative.eval y| := abs_nonneg _
  have h3 : (0 : ℝ) ≤ ε * r ^ j := by positivity
  have h4 : (0 : ℝ) ≤ (((k + j : ℕ)) : ℝ) ^ 2
      * (Real.exp ((k : ℝ) * g) * (Real.exp g) ^ j) := by positivity
  nlinarith [h1, h2, h3, h4, hc0, hT0,
    mul_nonneg (sub_nonneg.mpr h1) hT0, mul_nonneg hc0 (sub_nonneg.mpr h2)]

/-- 单项 `2c_{k+j}T''_{k+j}(y)` 的 collar 界（用 `(k+j)⁴`）。 -/
lemma norm_chebTailD2_term_le_gen (τ B : ℝ) (hτ : 0 < τ) (hB : 0 < B) {k j : ℕ}
    {ε r : ℝ} (hε : 0 ≤ ε) (hr : 0 ≤ r)
    (hdec : ∀ i : ℕ, ‖fcoef τ (((k + i : ℕ)) : ℤ)‖ ≤ ε * r ^ i)
    (hBτ : B / τ ≤ 1 / 2) {y : ℝ} (hy : |y| ≤ 1 + B / τ) :
    ‖2 * fcoef τ (((k + j : ℕ)) : ℤ)
        * ((((Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).derivative.derivative.eval y : ℝ)) : ℂ)‖
      ≤ 64 * ε * Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ)))
        * ((((k + j : ℕ)) : ℝ) ^ 4 * tailR B τ r ^ j) := by
  set g : ℝ := 2 * Real.sqrt (B / τ) with hg
  have hg0 : 0 ≤ g := by rw [hg]; positivity
  have hBτ0 : 0 ≤ B / τ := by positivity
  have habs : |((((k + j : ℕ)) : ℤ) : ℝ)| = (((k + j : ℕ)) : ℝ) :=
    abs_of_nonneg (by positivity)
  have hT := abs_deriv2_chebyshevT_le_exp (((k + j : ℕ)) : ℤ) hBτ0 hBτ hy
  rw [habs] at hT
  have hTg : |(Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).derivative.derivative.eval y|
      ≤ 32 * (((k + j : ℕ)) : ℝ) ^ 4 * Real.exp ((((k + j : ℕ)) : ℝ) * g) := by
    refine hT.trans (le_of_eq ?_)
    rw [hg]; push_cast; ring_nf
  have hexp : Real.exp ((((k + j : ℕ)) : ℝ) * g)
      = Real.exp ((k : ℝ) * g) * (Real.exp g) ^ j := by
    rw [show ((((k + j : ℕ)) : ℝ) * g) = (k : ℝ) * g + (j : ℝ) * g by push_cast; ring,
      Real.exp_add]
    congr 1
    exact Real.exp_nat_mul g j
  have hsplit : ‖2 * fcoef τ (((k + j : ℕ)) : ℤ)
        * ((((Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).derivative.derivative.eval y : ℝ)) : ℂ)‖
      = 2 * ‖fcoef τ (((k + j : ℕ)) : ℤ)‖
        * |(Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).derivative.derivative.eval y| := by
    rw [norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs]
  rw [hsplit]
  have htarget : 64 * ε * Real.exp ((k : ℝ) * g)
        * ((((k + j : ℕ)) : ℝ) ^ 4 * tailR B τ r ^ j)
      = 2 * (ε * r ^ j) * (32 * (((k + j : ℕ)) : ℝ) ^ 4
          * (Real.exp ((k : ℝ) * g) * (Real.exp g) ^ j)) := by
    rw [tailR, hg, mul_pow]; ring
  rw [htarget]
  have h2 : |(Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).derivative.derivative.eval y|
      ≤ 32 * (((k + j : ℕ)) : ℝ) ^ 4 * (Real.exp ((k : ℝ) * g) * (Real.exp g) ^ j) := by
    rw [← hexp]; exact hTg
  have h1 := hdec j
  have hc0 : (0 : ℝ) ≤ ‖fcoef τ (((k + j : ℕ)) : ℤ)‖ := norm_nonneg _
  have hT0 : (0 : ℝ) ≤
    |(Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).derivative.derivative.eval y| := abs_nonneg _
  have h3 : (0 : ℝ) ≤ ε * r ^ j := by positivity
  have h4 : (0 : ℝ) ≤ 32 * (((k + j : ℕ)) : ℝ) ^ 4
      * (Real.exp ((k : ℝ) * g) * (Real.exp g) ^ j) := by positivity
  nlinarith [h1, h2, h3, h4, hc0, hT0,
    mul_nonneg (sub_nonneg.mpr h1) hT0, mul_nonneg hc0 (sub_nonneg.mpr h2)]

/-- 尾部一阶导级数在 collar 上的界（一般 `ρ`）。 -/
lemma norm_chebTailD1_le_gen (τ B : ℝ) (hτ : 0 < τ) (hB : 0 < B) {k : ℕ}
    {ε r : ℝ} (hε : 0 ≤ ε) (hr : 0 ≤ r) (hr1 : tailR B τ r < 1)
    (hdec : ∀ j : ℕ, ‖fcoef τ (((k + j : ℕ)) : ℤ)‖ ≤ ε * r ^ j)
    {u : ℝ} (hu : |u| ≤ 1 + B / τ) :
    ‖chebTailD1 τ k u‖
      ≤ 2 * Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ)))
        * (2 * (k : ℝ) ^ 2 / (1 - tailR B τ r) + 4 / (1 - tailR B τ r) ^ 3) * ε := by
  set g : ℝ := 2 * Real.sqrt (B / τ) with hg
  set ρ : ℝ := tailR B τ r with hρdef
  have hρ0 : 0 ≤ ρ := by rw [hρdef]; exact tailR_nonneg hr
  have hρ1 : ρ < 1 := by rw [hρdef]; exact hr1
  have hpt : ∀ j : ℕ, ‖2 * fcoef τ (((k + j : ℕ)) : ℤ)
        * ((((Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).derivative.eval u : ℝ)) : ℂ)‖
      ≤ (2 * ε * Real.exp ((k : ℝ) * g)) * ((((k + j : ℕ)) : ℝ) ^ 2 * ρ ^ j) := by
    intro j
    have h := norm_chebTailD1_term_le_gen (k := k) (j := j) τ B hτ hB hε hr hdec hu
    rw [← hρdef, ← hg] at h
    exact h
  have hmaj : Summable (fun j : ℕ =>
      (2 * ε * Real.exp ((k : ℝ) * g)) * ((((k + j : ℕ)) : ℝ) ^ 2 * ρ ^ j)) :=
    (summable_add_pow_two_mul_geometric hρ0 hρ1).mul_left _
  have hs : Summable (fun j : ℕ => ‖2 * fcoef τ (((k + j : ℕ)) : ℤ)
        * ((((Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).derivative.eval u : ℝ)) : ℂ)‖) :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _) hpt hmaj
  calc ‖chebTailD1 τ k u‖
      = ‖∑' j : ℕ, 2 * fcoef τ (((k + j : ℕ)) : ℤ)
          * ((((Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).derivative.eval u : ℝ)) : ℂ)‖ := rfl
    _ ≤ ∑' j : ℕ, ‖2 * fcoef τ (((k + j : ℕ)) : ℤ)
          * ((((Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).derivative.eval u : ℝ)) : ℂ)‖ :=
        norm_tsum_le_tsum_norm hs
    _ ≤ ∑' j : ℕ, (2 * ε * Real.exp ((k : ℝ) * g))
          * ((((k + j : ℕ)) : ℝ) ^ 2 * ρ ^ j) := Summable.tsum_le_tsum hpt hs hmaj
    _ = (2 * ε * Real.exp ((k : ℝ) * g)) * ∑' j : ℕ, (((k + j : ℕ)) : ℝ) ^ 2 * ρ ^ j :=
        tsum_mul_left
    _ ≤ (2 * ε * Real.exp ((k : ℝ) * g)) * (2 * (k : ℝ) ^ 2 / (1 - ρ) + 4 / (1 - ρ) ^ 3) :=
        mul_le_mul_of_nonneg_left (tsum_add_pow_two_mul_geometric_le (k := k) hρ0 hρ1)
          (by positivity)
    _ = 2 * Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ)))
        * (2 * (k : ℝ) ^ 2 / (1 - tailR B τ r) + 4 / (1 - tailR B τ r) ^ 3) * ε := by
        rw [hρdef, hg]; ring

/-- 尾部二阶导级数在 collar 上的界（一般 `ρ`）。 -/
lemma norm_chebTailD2_le_gen (τ B : ℝ) (hτ : 0 < τ) (hB : 0 < B) {k : ℕ}
    {ε r : ℝ} (hε : 0 ≤ ε) (hr : 0 ≤ r) (hr1 : tailR B τ r < 1)
    (hdec : ∀ j : ℕ, ‖fcoef τ (((k + j : ℕ)) : ℤ)‖ ≤ ε * r ^ j) (hBτ : B / τ ≤ 1 / 2)
    {u : ℝ} (hu : |u| ≤ 1 + B / τ) :
    ‖chebTailD2 τ k u‖
      ≤ 2 * Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ)))
        * (256 * (k : ℝ) ^ 4 / (1 - tailR B τ r) + 19200 / (1 - tailR B τ r) ^ 5) * ε := by
  set g : ℝ := 2 * Real.sqrt (B / τ) with hg
  set ρ : ℝ := tailR B τ r with hρdef
  have hρ0 : 0 ≤ ρ := by rw [hρdef]; exact tailR_nonneg hr
  have hρ1 : ρ < 1 := by rw [hρdef]; exact hr1
  have hpt : ∀ j : ℕ, ‖2 * fcoef τ (((k + j : ℕ)) : ℤ)
        * ((((Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).derivative.derivative.eval u : ℝ)) : ℂ)‖
      ≤ (64 * ε * Real.exp ((k : ℝ) * g)) * ((((k + j : ℕ)) : ℝ) ^ 4 * ρ ^ j) := by
    intro j
    have h := norm_chebTailD2_term_le_gen (k := k) (j := j) τ B hτ hB hε hr hdec hBτ hu
    rw [← hρdef, ← hg] at h
    exact h
  have hmaj : Summable (fun j : ℕ =>
      (64 * ε * Real.exp ((k : ℝ) * g)) * ((((k + j : ℕ)) : ℝ) ^ 4 * ρ ^ j)) :=
    (summable_add_pow_four_mul_geometric hρ0 hρ1).mul_left _
  have hs : Summable (fun j : ℕ => ‖2 * fcoef τ (((k + j : ℕ)) : ℤ)
      * ((((Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).derivative.derivative.eval u : ℝ)) : ℂ)‖) :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _) hpt hmaj
  calc ‖chebTailD2 τ k u‖
      = ‖∑' j : ℕ, 2 * fcoef τ (((k + j : ℕ)) : ℤ)
          * ((((Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).derivative.derivative.eval u : ℝ)) : ℂ)‖ :=
        rfl
    _ ≤ ∑' j : ℕ, ‖2 * fcoef τ (((k + j : ℕ)) : ℤ)
          * ((((Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).derivative.derivative.eval u : ℝ)) : ℂ)‖ :=
        norm_tsum_le_tsum_norm hs
    _ ≤ ∑' j : ℕ, (64 * ε * Real.exp ((k : ℝ) * g))
          * ((((k + j : ℕ)) : ℝ) ^ 4 * ρ ^ j) := Summable.tsum_le_tsum hpt hs hmaj
    _ = (64 * ε * Real.exp ((k : ℝ) * g)) * ∑' j : ℕ, (((k + j : ℕ)) : ℝ) ^ 4 * ρ ^ j :=
        tsum_mul_left
    _ ≤ (64 * ε * Real.exp ((k : ℝ) * g))
          * (8 * (k : ℝ) ^ 4 / (1 - ρ) + 600 / (1 - ρ) ^ 5) :=
        mul_le_mul_of_nonneg_left (tsum_add_pow_four_mul_geometric_le (k := k) hρ0 hρ1)
          (by positivity)
    _ = 2 * Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ)))
        * (256 * (k : ℝ) ^ 4 / (1 - tailR B τ r) + 19200 / (1 - tailR B τ r) ^ 5) * ε := by
        rw [hρdef, hg]; ring


/-! ## §3 逐项求导、恒等式与 collar 上的最终界 -/

/-- **尾部级数逐项求导**（一般 `ρ`）。 -/
lemma hasDerivAt_chebTail_gen (τ B : ℝ) (hτ : 0 < τ) (hB : 0 < B) {k : ℕ} (hk : 1 ≤ k)
    {ε r : ℝ} (hε : 0 ≤ ε) (hr : 0 ≤ r) (hr1 : tailR B τ r < 1)
    (hdec : ∀ i : ℕ, ‖fcoef τ (((k + i : ℕ)) : ℤ)‖ ≤ ε * r ^ i)
    {u : ℝ} (hu : |u| < 1 + B / τ) :
    HasDerivAt (fun z : ℝ => chebTail τ k z) (chebTailD1 τ k u) u := by
  set g : ℝ := 2 * Real.sqrt (B / τ) with hg
  set ρ : ℝ := tailR B τ r with hρdef
  have hρ0 : 0 ≤ ρ := by rw [hρdef]; exact tailR_nonneg hr
  have hρ1 : ρ < 1 := by rw [hρdef]; exact hr1
  have hmem : u ∈ Set.Ioo (-(1 + B / τ)) (1 + B / τ) := by
    rw [Set.mem_Ioo]
    exact abs_lt.mp hu
  have hmaj : Summable (fun j : ℕ =>
      (2 * ε * Real.exp ((k : ℝ) * g)) * ((((k + j : ℕ)) : ℝ) ^ 2 * ρ ^ j)) :=
    (summable_add_pow_two_mul_geometric hρ0 hρ1).mul_left _
  have hbd : ∀ j : ℕ, ∀ y ∈ Set.Ioo (-(1 + B / τ)) (1 + B / τ),
      ‖2 * fcoef τ (((k + j : ℕ)) : ℤ)
        * ((((Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).derivative.eval y : ℝ)) : ℂ)‖
      ≤ (2 * ε * Real.exp ((k : ℝ) * g)) * ((((k + j : ℕ)) : ℝ) ^ 2 * ρ ^ j) := by
    intro j y hy
    have hy' : |y| ≤ 1 + B / τ := by
      have h := hy
      rw [Set.mem_Ioo] at h
      exact le_of_lt (abs_lt.mpr h)
    have h := norm_chebTailD1_term_le_gen (k := k) (j := j) τ B hτ hB hε hr hdec hy'
    rw [← hρdef, ← hg] at h
    exact h
  have hf0 : Summable (fun j : ℕ => 2 * fcoef τ (((k + j : ℕ)) : ℤ)
      * ((((Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).eval u : ℝ)) : ℂ)) := by
    refine Summable.of_norm ?_
    refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_) hmaj
    have hu' : |u| ≤ 1 + B / τ := le_of_lt hu
    have h := norm_chebTail_term_le (k := k) (j := j) τ B hτ hB hε hr hdec hu'
    have hρ' : r * Real.exp g = ρ := by rw [hρdef, tailR, hg]
    rw [← hg, hρ'] at h
    have hkj : (1 : ℝ) ≤ (((k + j : ℕ)) : ℝ) ^ 2 := by
      have h1 : (1 : ℕ) ≤ k + j := by omega
      have h2 : (1 : ℝ) ≤ (((k + j : ℕ)) : ℝ) := by exact_mod_cast h1
      nlinarith
    have hρj : (0 : ℝ) ≤ ρ ^ j := by positivity
    calc ‖2 * fcoef τ (((k + j : ℕ)) : ℤ)
          * ((((Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).eval u : ℝ)) : ℂ)‖
        ≤ 2 * ε * Real.exp ((k : ℝ) * g) * ρ ^ j := h
      _ ≤ 2 * ε * Real.exp ((k : ℝ) * g) * ((((k + j : ℕ)) : ℝ) ^ 2 * ρ ^ j) := by
          have h5 : ρ ^ j ≤ (((k + j : ℕ)) : ℝ) ^ 2 * ρ ^ j := by nlinarith [hkj, hρj]
          exact mul_le_mul_of_nonneg_left h5 (by positivity)
      _ = (2 * ε * Real.exp ((k : ℝ) * g)) * ((((k + j : ℕ)) : ℝ) ^ 2 * ρ ^ j) := by ring
  refine hasDerivAt_tsum_of_isPreconnected
    (u := fun j : ℕ => (2 * ε * Real.exp ((k : ℝ) * g)) * ((((k + j : ℕ)) : ℝ) ^ 2 * ρ ^ j))
    (g := fun j : ℕ => fun y : ℝ => 2 * fcoef τ (((k + j : ℕ)) : ℤ)
      * ((((Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).eval y : ℝ)) : ℂ))
    (g' := fun j : ℕ => fun y : ℝ => 2 * fcoef τ (((k + j : ℕ)) : ℤ)
      * ((((Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).derivative.eval y : ℝ)) : ℂ))
    (t := Set.Ioo (-(1 + B / τ)) (1 + B / τ))
    hmaj isOpen_Ioo isPreconnected_Ioo ?_ hbd hmem hf0 hmem
  intro n y _
  exact ((Polynomial.hasDerivAt (Polynomial.Chebyshev.T ℝ (((k + n : ℕ)) : ℤ)) y).ofReal_comp).const_mul _

/-- **`chebTailD1` 逐项求导**（一般 `ρ`）。 -/
lemma hasDerivAt_chebTailD1_gen (τ B : ℝ) (hτ : 0 < τ) (hB : 0 < B) {k : ℕ} (hk : 1 ≤ k)
    {ε r : ℝ} (hε : 0 ≤ ε) (hr : 0 ≤ r) (hr1 : tailR B τ r < 1)
    (hdec : ∀ i : ℕ, ‖fcoef τ (((k + i : ℕ)) : ℤ)‖ ≤ ε * r ^ i) (hBτ : B / τ ≤ 1 / 2)
    {u : ℝ} (hu : |u| < 1 + B / τ) :
    HasDerivAt (fun z : ℝ => chebTailD1 τ k z) (chebTailD2 τ k u) u := by
  set g : ℝ := 2 * Real.sqrt (B / τ) with hg
  set ρ : ℝ := tailR B τ r with hρdef
  have hρ0 : 0 ≤ ρ := by rw [hρdef]; exact tailR_nonneg hr
  have hρ1 : ρ < 1 := by rw [hρdef]; exact hr1
  have hmem : u ∈ Set.Ioo (-(1 + B / τ)) (1 + B / τ) := by
    rw [Set.mem_Ioo]
    exact abs_lt.mp hu
  have hmaj : Summable (fun j : ℕ =>
      (64 * ε * Real.exp ((k : ℝ) * g)) * ((((k + j : ℕ)) : ℝ) ^ 4 * ρ ^ j)) :=
    (summable_add_pow_four_mul_geometric hρ0 hρ1).mul_left _
  have hbd : ∀ j : ℕ, ∀ y ∈ Set.Ioo (-(1 + B / τ)) (1 + B / τ),
      ‖2 * fcoef τ (((k + j : ℕ)) : ℤ)
        * ((((Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).derivative.derivative.eval y : ℝ)) : ℂ)‖
      ≤ (64 * ε * Real.exp ((k : ℝ) * g)) * ((((k + j : ℕ)) : ℝ) ^ 4 * ρ ^ j) := by
    intro j y hy
    have hy' : |y| ≤ 1 + B / τ := by
      have h := hy
      rw [Set.mem_Ioo] at h
      exact le_of_lt (abs_lt.mpr h)
    have h := norm_chebTailD2_term_le_gen (k := k) (j := j) τ B hτ hB hε hr hdec hBτ hy'
    rw [← hρdef, ← hg] at h
    exact h
  have hf0 : Summable (fun j : ℕ => 2 * fcoef τ (((k + j : ℕ)) : ℤ)
      * ((((Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).derivative.eval u : ℝ)) : ℂ)) := by
    refine Summable.of_norm ?_
    refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_) hmaj
    have hu' : |u| ≤ 1 + B / τ := le_of_lt hu
    have h := norm_chebTailD1_term_le_gen (k := k) (j := j) τ B hτ hB hε hr hdec hu'
    rw [← hρdef, ← hg] at h
    have hx : (1 : ℝ) ≤ (((k + j : ℕ)) : ℝ) ^ 2 := by
      have h1 : (1 : ℕ) ≤ k + j := by omega
      have h2 : (1 : ℝ) ≤ (((k + j : ℕ)) : ℝ) := by exact_mod_cast h1
      nlinarith
    have hρj : (0 : ℝ) ≤ ρ ^ j := by positivity
    calc ‖2 * fcoef τ (((k + j : ℕ)) : ℤ)
          * ((((Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).derivative.eval u : ℝ)) : ℂ)‖
        ≤ 2 * ε * Real.exp ((k : ℝ) * g) * ((((k + j : ℕ)) : ℝ) ^ 2 * ρ ^ j) := h
      _ ≤ 64 * ε * Real.exp ((k : ℝ) * g) * ((((k + j : ℕ)) : ℝ) ^ 4 * ρ ^ j) := by
          have h5 : (((k + j : ℕ)) : ℝ) ^ 2 * ρ ^ j
              ≤ 32 * ((((k + j : ℕ)) : ℝ) ^ 4 * ρ ^ j) := by
            have h32 : (1 : ℝ) ≤ 32 * (((k + j : ℕ)) : ℝ) ^ 2 := by nlinarith [hx]
            calc (((k + j : ℕ)) : ℝ) ^ 2 * ρ ^ j
                = ((((k + j : ℕ)) : ℝ) ^ 2 * ρ ^ j) * 1 := by ring
              _ ≤ ((((k + j : ℕ)) : ℝ) ^ 2 * ρ ^ j) * (32 * (((k + j : ℕ)) : ℝ) ^ 2) :=
                  mul_le_mul_of_nonneg_left h32 (by positivity)
              _ = 32 * ((((k + j : ℕ)) : ℝ) ^ 4 * ρ ^ j) := by ring
          have h6 : (0 : ℝ) ≤ ε * Real.exp ((k : ℝ) * g) := by positivity
          nlinarith [h5, h6, mul_le_mul_of_nonneg_left h5 h6, Real.exp_pos ((k : ℝ) * g)]
      _ = (64 * ε * Real.exp ((k : ℝ) * g)) * ((((k + j : ℕ)) : ℝ) ^ 4 * ρ ^ j) := by ring
  refine hasDerivAt_tsum_of_isPreconnected
    (u := fun j : ℕ => (64 * ε * Real.exp ((k : ℝ) * g)) * ((((k + j : ℕ)) : ℝ) ^ 4 * ρ ^ j))
    (g := fun j : ℕ => fun y : ℝ => 2 * fcoef τ (((k + j : ℕ)) : ℤ)
      * ((((Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).derivative.eval y : ℝ)) : ℂ))
    (g' := fun j : ℕ => fun y : ℝ => 2 * fcoef τ (((k + j : ℕ)) : ℤ)
      * ((((Polynomial.Chebyshev.T ℝ (((k + j : ℕ)) : ℤ)).derivative.derivative.eval y : ℝ)) : ℂ))
    (t := Set.Ioo (-(1 + B / τ)) (1 + B / τ))
    hmaj isOpen_Ioo isPreconnected_Ioo ?_ hbd hmem hf0 hmem
  intro n y _
  exact ((Polynomial.hasDerivAt (Polynomial.Chebyshev.T ℝ (((k + n : ℕ)) : ℤ)).derivative y).ofReal_comp).const_mul _

/-- **一阶导恒等式（开 collar，一般 `ρ`）**：`deriv Q μ = chebTailD1 τ k (μ/τ)/τ`。 -/
lemma deriv_sharpErr_eq_chebTailD1_gen (τ B : ℝ) (hτ : 0 < τ) (hB : 0 < B) {k : ℕ} (hk : 1 ≤ k)
    {ε r : ℝ} (hε : 0 ≤ ε) (hr : 0 ≤ r) (hr1 : tailR B τ r < 1)
    (hdec : ∀ j : ℕ, ‖fcoef τ (((k + j : ℕ)) : ℤ)‖ ≤ ε * r ^ j)
    {μ : ℝ} (hμ : |μ| < τ + B) :
    deriv (sharpErr τ k) μ = chebTailD1 τ k (μ / τ) / τ := by
  have hτne : τ ≠ 0 := ne_of_gt hτ
  have hτneC : ((τ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hτne
  have hu : |μ / τ| < 1 + B / τ := by
    rw [abs_div, abs_of_pos hτ, div_lt_iff₀ hτ]
    have h : (1 + B / τ) * τ = τ + B := by field_simp
    rw [h]; exact hμ
  have hev : (fun z : ℝ => sharpErr τ k (τ * z)) =ᶠ[𝓝 (μ / τ)]
      (fun z : ℝ => chebTail τ k z) := by
    refine Filter.eventually_of_mem ((isOpen_lt continuous_abs continuous_const).mem_nhds hu)
      fun z hz => ?_
    rw [Set.mem_ofPred_eq] at hz
    exact (chebTail_eq_sharpErr_collar_all τ hτ hk B (le_of_lt hz)).symm
  have hder := Filter.EventuallyEq.deriv_eq hev
  have h1 : deriv (fun z : ℝ => sharpErr τ k (τ * z)) (μ / τ)
      = ((τ : ℝ) : ℂ) * deriv (sharpErr τ k) (τ * (μ / τ)) := by
    have hl : HasDerivAt (sharpErr τ k) (deriv (sharpErr τ k) (τ * (μ / τ))) (τ * (μ / τ)) :=
      (differentiableAt_sharpErr τ k (τ * (μ / τ))).hasDerivAt
    have hf : HasDerivAt (fun z : ℝ => τ * z) τ (μ / τ) := by
      simpa using (hasDerivAt_id (μ / τ)).const_mul τ
    have hcomp := (hl.hasFDerivAt).comp_hasDerivAt (μ / τ) hf
    have hd := hcomp.deriv
    rw [ContinuousLinearMap.toSpanSingleton_apply, Complex.real_smul] at hd
    exact hd
  have h2 : deriv (fun z : ℝ => chebTail τ k z) (μ / τ) = chebTailD1 τ k (μ / τ) :=
    (hasDerivAt_chebTail_gen τ B hτ hB hk hε hr hr1 hdec hu).deriv
  rw [h1, h2] at hder
  have hτu : τ * (μ / τ) = μ := by field_simp
  rw [hτu, mul_comm] at hder
  rw [eq_div_iff hτneC]
  exact hder

/-- **二阶导恒等式（开 collar，一般 `ρ`）**。 -/
lemma deriv2_sharpErr_eq_chebTailD2_gen (τ B : ℝ) (hτ : 0 < τ) (hB : 0 < B) {k : ℕ} (hk : 1 ≤ k)
    {ε r : ℝ} (hε : 0 ≤ ε) (hr : 0 ≤ r) (hr1 : tailR B τ r < 1)
    (hdec : ∀ j : ℕ, ‖fcoef τ (((k + j : ℕ)) : ℤ)‖ ≤ ε * r ^ j) (hBτ : B / τ ≤ 1 / 2)
    {μ : ℝ} (hμ : |μ| < τ + B) :
    deriv (deriv (sharpErr τ k)) μ = chebTailD2 τ k (μ / τ) / τ ^ 2 := by
  have hτne : τ ≠ 0 := ne_of_gt hτ
  have hτneC : ((τ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hτne
  have hu : |μ / τ| < 1 + B / τ := by
    rw [abs_div, abs_of_pos hτ, div_lt_iff₀ hτ]
    have h : (1 + B / τ) * τ = τ + B := by field_simp
    rw [h]; exact hμ
  have hev : (deriv (sharpErr τ k)) =ᶠ[𝓝 μ]
      (fun x : ℝ => chebTailD1 τ k (x / τ) / τ) := by
    refine Filter.eventually_of_mem ((isOpen_lt continuous_abs continuous_const).mem_nhds hμ)
      fun x hx => ?_
    rw [Set.mem_ofPred_eq] at hx
    exact deriv_sharpErr_eq_chebTailD1_gen τ B hτ hB hk hε hr hr1 hdec hx
  have hder := Filter.EventuallyEq.deriv_eq hev
  have hinner : HasDerivAt (fun x : ℝ => x / τ) (1 / τ) μ := by
    simpa using (hasDerivAt_id μ).div_const τ
  have houter : HasDerivAt (chebTailD1 τ k) (chebTailD2 τ k (μ / τ)) (μ / τ) :=
    hasDerivAt_chebTailD1_gen τ B hτ hB hk hε hr hr1 hdec hBτ hu
  have hcomp := (houter.hasFDerivAt).comp_hasDerivAt μ hinner
  have hdiv : HasDerivAt (fun x : ℝ => chebTailD1 τ k (x / τ) / τ)
      (((τ⁻¹ : ℝ) : ℂ) * chebTailD2 τ k (μ / τ) / τ) μ := by
    have hd := hcomp.div_const τ
    rw [ContinuousLinearMap.toSpanSingleton_apply, Complex.real_smul] at hd
    simpa [Function.comp_def] using hd
  rw [hdiv.deriv] at hder
  rw [Complex.ofReal_inv] at hder
  rw [hder]
  simp only [div_eq_mul_inv]
  rw [show (((τ : ℝ) : ℂ) ^ 2)⁻¹ = ((τ : ℝ) : ℂ)⁻¹ * ((τ : ℝ) : ℂ)⁻¹ by rw [sq, mul_inv]]
  ring

/-- **闭 collar 上的一阶导界（一般 `ρ`）**。 -/
theorem norm_deriv_sharpErr_le_gen (τ B : ℝ) (hτ : 0 < τ) (hB : 0 < B) {k : ℕ} (hk : 1 ≤ k)
    {ε r : ℝ} (hε : 0 ≤ ε) (hr : 0 ≤ r) (hr1 : tailR B τ r < 1)
    (hdec : ∀ j : ℕ, ‖fcoef τ (((k + j : ℕ)) : ℤ)‖ ≤ ε * r ^ j) :
    ∀ μ : ℝ, |μ| ≤ τ + B →
      ‖deriv (sharpErr τ k) μ‖
        ≤ 2 * Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ)))
          * (2 * (k : ℝ) ^ 2 / (1 - tailR B τ r) + 4 / (1 - tailR B τ r) ^ 3) * ε / τ := by
  intro μ hμ
  set C : ℝ := 2 * Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ)))
      * (2 * (k : ℝ) ^ 2 / (1 - tailR B τ r) + 4 / (1 - tailR B τ r) ^ 3) * ε / τ with hC
  have hsub : Set.Ioo (-(τ + B)) (τ + B) ⊆ {x : ℝ | ‖deriv (sharpErr τ k) x‖ ≤ C} := by
    intro x hx
    rw [Set.mem_Ioo] at hx
    rw [Set.mem_setOf_eq]
    have hx' : |x| < τ + B := abs_lt.mpr hx
    rw [deriv_sharpErr_eq_chebTailD1_gen τ B hτ hB hk hε hr hr1 hdec hx', norm_div,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ]
    have hxτ : |x / τ| ≤ 1 + B / τ := by
      rw [abs_div, abs_of_pos hτ, div_le_iff₀ hτ]
      have h : (1 + B / τ) * τ = τ + B := by field_simp
      rw [h]; exact le_of_lt hx'
    have h2 := norm_chebTailD1_le_gen τ B hτ hB hε hr hr1 hdec hxτ
    calc ‖chebTailD1 τ k (x / τ)‖ / τ
        ≤ (2 * Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ)))
            * (2 * (k : ℝ) ^ 2 / (1 - tailR B τ r) + 4 / (1 - tailR B τ r) ^ 3) * ε) / τ :=
          div_le_div_of_nonneg_right h2 hτ.le
      _ = C := by rw [hC]
  have hcl : IsClosed {x : ℝ | ‖deriv (sharpErr τ k) x‖ ≤ C} :=
    isClosed_le (continuous_norm.comp (continuous_deriv_sharpErr τ k)) continuous_const
  have hclosure : closure (Set.Ioo (-(τ + B)) (τ + B)) = Set.Icc (-(τ + B)) (τ + B) :=
    closure_Ioo (by linarith : -(τ + B) ≠ τ + B)
  have hIcc : μ ∈ Set.Icc (-(τ + B)) (τ + B) := by
    rw [Set.mem_Icc]; exact abs_le.mp hμ
  exact hcl.closure_subset_iff.mpr hsub (by rw [hclosure]; exact hIcc)

/-- **闭 collar 上的二阶导界（一般 `ρ`）**。 -/
theorem norm_deriv2_sharpErr_le_gen (τ B : ℝ) (hτ : 0 < τ) (hB : 0 < B) {k : ℕ} (hk : 1 ≤ k)
    {ε r : ℝ} (hε : 0 ≤ ε) (hr : 0 ≤ r) (hr1 : tailR B τ r < 1)
    (hdec : ∀ j : ℕ, ‖fcoef τ (((k + j : ℕ)) : ℤ)‖ ≤ ε * r ^ j) (hBτ : B / τ ≤ 1 / 2) :
    ∀ μ : ℝ, |μ| ≤ τ + B →
      ‖deriv (deriv (sharpErr τ k)) μ‖
        ≤ 2 * Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ)))
          * (256 * (k : ℝ) ^ 4 / (1 - tailR B τ r) + 19200 / (1 - tailR B τ r) ^ 5)
          * ε / τ ^ 2 := by
  intro μ hμ
  set C : ℝ := 2 * Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ)))
      * (256 * (k : ℝ) ^ 4 / (1 - tailR B τ r) + 19200 / (1 - tailR B τ r) ^ 5) * ε / τ ^ 2
    with hC
  have hsub : Set.Ioo (-(τ + B)) (τ + B) ⊆ {x : ℝ | ‖deriv (deriv (sharpErr τ k)) x‖ ≤ C} := by
    intro x hx
    rw [Set.mem_Ioo] at hx
    rw [Set.mem_setOf_eq]
    have hx' : |x| < τ + B := abs_lt.mpr hx
    rw [deriv2_sharpErr_eq_chebTailD2_gen τ B hτ hB hk hε hr hr1 hdec hBτ hx', norm_div,
      norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ]
    have hxτ : |x / τ| ≤ 1 + B / τ := by
      rw [abs_div, abs_of_pos hτ, div_le_iff₀ hτ]
      have h : (1 + B / τ) * τ = τ + B := by field_simp
      rw [h]; exact le_of_lt hx'
    have h2 := norm_chebTailD2_le_gen τ B hτ hB hε hr hr1 hdec hBτ hxτ
    calc ‖chebTailD2 τ k (x / τ)‖ / τ ^ 2
        ≤ (2 * Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ)))
            * (256 * (k : ℝ) ^ 4 / (1 - tailR B τ r) + 19200 / (1 - tailR B τ r) ^ 5)
            * ε) / τ ^ 2 := div_le_div_of_nonneg_right h2 (by positivity)
      _ = C := by rw [hC]
  have hcl : IsClosed {x : ℝ | ‖deriv (deriv (sharpErr τ k)) x‖ ≤ C} :=
    isClosed_le (continuous_norm.comp (continuous_deriv2_sharpErr τ k)) continuous_const
  have hclosure : closure (Set.Ioo (-(τ + B)) (τ + B)) = Set.Icc (-(τ + B)) (τ + B) :=
    closure_Ioo (by linarith : -(τ + B) ≠ τ + B)
  have hIcc : μ ∈ Set.Icc (-(τ + B)) (τ + B) := by
    rw [Set.mem_Icc]; exact abs_le.mp hμ
  exact hcl.closure_subset_iff.mpr hsub (by rw [hclosure]; exact hIcc)

/-- **`ψ_A` 一阶导的 collar 界（一般 `ρ`，显式 `1/(1-r')` 常数）**。 -/
theorem norm_deriv_psiA_scaled_collar_gen (τ B : ℝ) (hτ : 0 < τ) (hB : 0 < B) {k : ℕ}
    (hk : 1 ≤ k) {ε r : ℝ} (hε : 0 ≤ ε) (hr : 0 ≤ r) (hr1 : tailR B τ r < 1)
    (hdec : ∀ j : ℕ, ‖fcoef τ (((k + j : ℕ)) : ℤ)‖ ≤ ε * r ^ j) :
    ∀ μ : ℝ, |μ| ≤ τ + B →
      ‖deriv (fun x : ℝ => psiA (scaledApprox τ k) x) μ‖
        ≤ 2 * Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ)))
          * (2 * (k : ℝ) ^ 2 / (1 - tailR B τ r) + 4 / (1 - tailR B τ r) ^ 3
            + τ / (1 - tailR B τ r)) * ε / τ := by
  intro μ hμ
  rw [deriv_psiA, dpsiA_scaledApprox_eq]
  have h1 := norm_deriv_sharpErr_le_gen τ B hτ hB hk hε hr hr1 hdec μ hμ
  have hu : |μ / τ| ≤ 1 + B / τ := by
    rw [abs_div, abs_of_pos hτ, div_le_iff₀ hτ]
    have h : (1 + B / τ) * τ = τ + B := by field_simp
    rw [h]; exact hμ
  have h2 : ‖sharpErr τ k μ‖ ≤ 2 * Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ)))
      * ε / (1 - tailR B τ r) := by
    have h := norm_chebTail_le_gen τ B hτ hB hε hr hr1 hdec hu
    rwa [chebTail_eq_sharpErr_collar_all τ hτ hk B hu,
      show τ * (μ / τ) = μ by field_simp] at h
  have h3 : ‖Complex.exp ((μ : ℂ) * Complex.I) * Complex.I * sharpErr τ k μ‖
      ≤ 2 * Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ))) * (τ / (1 - tailR B τ r)) * ε / τ := by
    rw [norm_mul, norm_mul, norm_exp_mul_I, Complex.norm_I, one_mul, one_mul]
    have h4 : (0 : ℝ) < τ := hτ
    calc ‖sharpErr τ k μ‖ ≤ 2 * Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ))) * ε
          / (1 - tailR B τ r) := h2
      _ = 2 * Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ))) * (τ / (1 - tailR B τ r)) * ε / τ := by
          field_simp
  have h5 : ‖Complex.exp ((μ : ℂ) * Complex.I) * deriv (sharpErr τ k) μ‖
      ≤ 2 * Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ)))
        * (2 * (k : ℝ) ^ 2 / (1 - tailR B τ r) + 4 / (1 - tailR B τ r) ^ 3) * ε / τ := by
    rw [norm_mul, norm_exp_mul_I, one_mul]; exact h1
  calc ‖Complex.exp ((μ : ℂ) * Complex.I) * deriv (sharpErr τ k) μ
        + Complex.exp ((μ : ℂ) * Complex.I) * Complex.I * sharpErr τ k μ‖
      ≤ ‖Complex.exp ((μ : ℂ) * Complex.I) * deriv (sharpErr τ k) μ‖
        + ‖Complex.exp ((μ : ℂ) * Complex.I) * Complex.I * sharpErr τ k μ‖ := norm_add_le _ _
    _ ≤ 2 * Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ)))
          * (2 * (k : ℝ) ^ 2 / (1 - tailR B τ r) + 4 / (1 - tailR B τ r) ^ 3) * ε / τ
        + 2 * Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ)))
          * (τ / (1 - tailR B τ r)) * ε / τ := add_le_add h5 h3
    _ = 2 * Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ)))
          * (2 * (k : ℝ) ^ 2 / (1 - tailR B τ r) + 4 / (1 - tailR B τ r) ^ 3
            + τ / (1 - tailR B τ r)) * ε / τ := by
        field_simp

/-- **`ψ_A` 二阶导的 collar 界（一般 `ρ`，显式 `1/(1-r')` 常数）**。 -/
theorem norm_deriv2_psiA_scaled_collar_gen (τ B : ℝ) (hτ : 0 < τ) (hB : 0 < B) {k : ℕ}
    (hk : 1 ≤ k) {ε r : ℝ} (hε : 0 ≤ ε) (hr : 0 ≤ r) (hr1 : tailR B τ r < 1)
    (hdec : ∀ j : ℕ, ‖fcoef τ (((k + j : ℕ)) : ℤ)‖ ≤ ε * r ^ j) (hBτ : B / τ ≤ 1 / 2) :
    ∀ μ : ℝ, |μ| ≤ τ + B →
      ‖deriv (deriv (fun x : ℝ => psiA (scaledApprox τ k) x)) μ‖
        ≤ 2 * Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ)))
          * (256 * (k : ℝ) ^ 4 / (1 - tailR B τ r) + 19200 / (1 - tailR B τ r) ^ 5
            + 4 * τ * (k : ℝ) ^ 2 / (1 - tailR B τ r) + 8 * τ / (1 - tailR B τ r) ^ 3
            + τ ^ 2 / (1 - tailR B τ r)) * ε / τ ^ 2 := by
  intro μ hμ
  rw [deriv2_psiA_scaledApprox_eq]
  have h1 := norm_deriv2_sharpErr_le_gen τ B hτ hB hk hε hr hr1 hdec hBτ μ hμ
  have h2 := norm_deriv_sharpErr_le_gen τ B hτ hB hk hε hr hr1 hdec μ hμ
  have hu : |μ / τ| ≤ 1 + B / τ := by
    rw [abs_div, abs_of_pos hτ, div_le_iff₀ hτ]
    have h : (1 + B / τ) * τ = τ + B := by field_simp
    rw [h]; exact hμ
  have h3 : ‖sharpErr τ k μ‖ ≤ 2 * Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ)))
      * ε / (1 - tailR B τ r) := by
    have h := norm_chebTail_le_gen τ B hτ hB hε hr hr1 hdec hu
    rwa [chebTail_eq_sharpErr_collar_all τ hτ hk B hu,
      show τ * (μ / τ) = μ by field_simp] at h
  have h7 : ‖Complex.exp ((μ : ℂ) * Complex.I) * sharpErr τ k μ‖
      ≤ 2 * Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ))) * (τ ^ 2 / (1 - tailR B τ r)) * ε / τ ^ 2 := by
    rw [norm_mul, norm_exp_mul_I, one_mul]
    calc ‖sharpErr τ k μ‖ ≤ 2 * Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ))) * ε
          / (1 - tailR B τ r) := h3
      _ = 2 * Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ))) * (τ ^ 2 / (1 - tailR B τ r)) * ε
          / τ ^ 2 := by field_simp
  have h6 : ‖2 * (Complex.exp ((μ : ℂ) * Complex.I) * Complex.I * deriv (sharpErr τ k) μ)‖
      ≤ 2 * Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ)))
        * (4 * τ * (k : ℝ) ^ 2 / (1 - tailR B τ r) + 8 * τ / (1 - tailR B τ r) ^ 3)
        * ε / τ ^ 2 := by
    rw [norm_mul, norm_mul, norm_mul, norm_exp_mul_I, Complex.norm_I, Complex.norm_ofNat,
      one_mul, one_mul]
    calc 2 * ‖deriv (sharpErr τ k) μ‖
        ≤ 2 * (2 * Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ)))
            * (2 * (k : ℝ) ^ 2 / (1 - tailR B τ r) + 4 / (1 - tailR B τ r) ^ 3) * ε / τ) :=
          mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ = 2 * Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ)))
            * (4 * τ * (k : ℝ) ^ 2 / (1 - tailR B τ r) + 8 * τ / (1 - tailR B τ r) ^ 3)
            * ε / τ ^ 2 := by
          field_simp
          ring
  have h5 : ‖Complex.exp ((μ : ℂ) * Complex.I) * deriv (deriv (sharpErr τ k)) μ‖
      ≤ 2 * Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ)))
        * (256 * (k : ℝ) ^ 4 / (1 - tailR B τ r) + 19200 / (1 - tailR B τ r) ^ 5) * ε / τ ^ 2 := by
    rw [norm_mul, norm_exp_mul_I, one_mul]; exact h1
  calc ‖Complex.exp ((μ : ℂ) * Complex.I) * deriv (deriv (sharpErr τ k)) μ
        + 2 * (Complex.exp ((μ : ℂ) * Complex.I) * Complex.I * deriv (sharpErr τ k) μ)
        - Complex.exp ((μ : ℂ) * Complex.I) * sharpErr τ k μ‖
      ≤ ‖Complex.exp ((μ : ℂ) * Complex.I) * deriv (deriv (sharpErr τ k)) μ
          + 2 * (Complex.exp ((μ : ℂ) * Complex.I) * Complex.I * deriv (sharpErr τ k) μ)‖
        + ‖Complex.exp ((μ : ℂ) * Complex.I) * sharpErr τ k μ‖ := norm_sub_le _ _
    _ ≤ (‖Complex.exp ((μ : ℂ) * Complex.I) * deriv (deriv (sharpErr τ k)) μ‖
          + ‖2 * (Complex.exp ((μ : ℂ) * Complex.I) * Complex.I * deriv (sharpErr τ k) μ)‖)
        + ‖Complex.exp ((μ : ℂ) * Complex.I) * sharpErr τ k μ‖ := by
        have := norm_add_le (Complex.exp ((μ : ℂ) * Complex.I) * deriv (deriv (sharpErr τ k)) μ)
          (2 * (Complex.exp ((μ : ℂ) * Complex.I) * Complex.I * deriv (sharpErr τ k) μ))
        linarith
    _ ≤ (2 * Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ)))
          * (256 * (k : ℝ) ^ 4 / (1 - tailR B τ r) + 19200 / (1 - tailR B τ r) ^ 5) * ε / τ ^ 2
        + 2 * Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ)))
          * (4 * τ * (k : ℝ) ^ 2 / (1 - tailR B τ r) + 8 * τ / (1 - tailR B τ r) ^ 3)
          * ε / τ ^ 2)
        + 2 * Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ)))
          * (τ ^ 2 / (1 - tailR B τ r)) * ε / τ ^ 2 := by
        linarith [h5, h6, h7]
    _ = 2 * Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ)))
          * (256 * (k : ℝ) ^ 4 / (1 - tailR B τ r) + 19200 / (1 - tailR B τ r) ^ 5
            + 4 * τ * (k : ℝ) ^ 2 / (1 - tailR B τ r) + 8 * τ / (1 - tailR B τ r) ^ 3
            + τ ^ 2 / (1 - tailR B τ r)) * ε / τ ^ 2 := by
        field_simp
        ring

end RobustZ
