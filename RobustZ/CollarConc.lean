/-
Copyright (c) 2025 RobustZ project. All rights reserved.

# `CollarConc`：具体常数的 collar 界与**无条件**端到端定理

`Effective.effective_bound_of_sharp` 依赖固定的 `SharpCollar (Cd1, Cd2)`。
本文件用 `SharpDerivGen` 的 honest 一般 collar 界把它无条件落地：

* honest 尾部常数 `ε_h = e^{τ sinh δ'}e^{-δ'k}` 与 `SharpDerivGen` 里的 `1/(1-r')`
  相消（`honest_le_eps_mul`：`ε_h ≤ ε·(1-r')/2`）；
* 侧条件 `k²B ≤ τ/4`（`ksq_sqrt_epsOf_le_gen`）给出 `E = e^{k·2√(B/τ)} ≤ 3`；
* `1-r' ≥ 14/k`（由 `1-r' ≥ 1-e^{-(t-1/k)} ≥ (4/5)(t-1/k)` 与 `t ≥ 18.5/k`）给出
  `R = 1/(1-r') ≤ k/14`，于是 `R² ≤ k²/196`；
* 收尾两个纯算术事实（`arith_M1`、`arith_M2`，只含 `k R τ ε E` 五个变量，与巨大的
  `effQ0/effQmin/effN0End` 上下文完全隔离）给出
  `τ·M₁ ≤ 7k²ε`、`τ²·M₂ ≤ 770k⁴ε`。

由此 `collar_bound_concrete : SharpCollarFrom (effN0End K a) 7 770 a 4`，
`endgame_bound` 无条件成立。
-/
import RobustZ.Endgame

noncomputable section

namespace RobustZ

open Filter MeasureTheory
open scoped Real

set_option maxHeartbeats 2000000

/-! ## §1 有理指数辅助 -/

/-- `(x^{1/3})² = x^{2/3}`。 -/
lemma rpow_third_sq (x : ℝ) (hx : 0 ≤ x) : (x ^ (1 / 3 : ℝ)) ^ 2 = x ^ (2 / 3 : ℝ) := by
  rw [← Real.rpow_natCast (x ^ (1 / 3 : ℝ)) 2, ← Real.rpow_mul hx]; norm_num

/-- `x^{2/3} = x²·x^{-4/3}`。 -/
lemma rpow_two_thirds (x : ℝ) (hx : 0 < x) : x ^ (2 / 3 : ℝ) = x ^ 2 * x ^ (-(4 / 3) : ℝ) := by
  rw [← Real.rpow_natCast x 2, ← Real.rpow_add hx]; norm_num

/-- `x^{4/3} = x²·x^{-2/3}`。 -/
lemma rpow_four_thirds (x : ℝ) (hx : 0 < x) : x ^ (4 / 3 : ℝ) = x ^ 2 * x ^ (-(2 / 3) : ℝ) := by
  rw [← Real.rpow_natCast x 2, ← Real.rpow_add hx]; norm_num

/-- `(x^{1/3})³ = x`。 -/
lemma rpow_third_cube (x : ℝ) (hx : 0 ≤ x) : (x ^ (1 / 3 : ℝ)) ^ 3 = x := by
  rw [← Real.rpow_natCast (x ^ (1 / 3 : ℝ)) 3, ← Real.rpow_mul hx]; norm_num

/-! ## §2 纯算术核心（只含 `k R τ ε E`，与主上下文隔离，避免递归爆炸） -/

/-- 算术核心 1：`E·(2k² + 4R² + τ)·ε ≤ 7k²ε`
（`k ≥ 1000`、`R² ≤ k²/196`、`τ ≤ 2k`、`E ≤ 3`、`ε ≥ 0`）。 -/
private lemma arith_M1 {k R τ ε E : ℝ} (hk : 1000 ≤ k) (hR : 0 < R)
    (hR2 : R ^ 2 ≤ k ^ 2 / 196) (hτ0 : 0 ≤ τ) (hτ2 : τ ≤ 2 * k)
    (hε0 : 0 ≤ ε) (hE3 : E ≤ 3) :
    E * (2 * k ^ 2 + 4 * R ^ 2 + τ) * ε ≤ 7 * k ^ 2 * ε := by
  have hk0 : (0 : ℝ) < k := by linarith
  have hk2nn : (0 : ℝ) ≤ k ^ 2 := by positivity
  have hS : 2 * k ^ 2 + 4 * R ^ 2 + τ ≤ 7 / 3 * k ^ 2 := by
    have h1 : 4 * R ^ 2 ≤ 4 * (k ^ 2 / 196) := by linarith only [hR2]
    have h3 : 2 * k ≤ k ^ 2 / 500 := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 500)]
      have h := mul_le_mul_of_nonneg_right hk hk0.le
      linarith only [h]
    linarith only [h1, hτ2, h3, hk2nn]
  have hS0 : 0 ≤ 2 * k ^ 2 + 4 * R ^ 2 + τ := by
    have h1 : (0 : ℝ) ≤ 2 * k ^ 2 := by positivity
    have h2 : (0 : ℝ) ≤ 4 * R ^ 2 := by positivity
    linarith only [h1, h2, hτ0]
  have hstep : E * (2 * k ^ 2 + 4 * R ^ 2 + τ) ≤ 3 * (7 / 3 * k ^ 2) :=
    mul_le_mul hE3 hS hS0 (by norm_num)
  have hstep2 : E * (2 * k ^ 2 + 4 * R ^ 2 + τ) ≤ 7 * k ^ 2 := by linarith only [hstep]
  exact mul_le_mul_of_nonneg_right hstep2 hε0

/-- 算术核心 2：`E·(256k⁴ + 19200R⁴ + 4τk² + 8τR² + τ²)·ε ≤ 770k⁴ε`。 -/
private lemma arith_M2 {k R τ ε E : ℝ} (hk : 1000 ≤ k)
    (hR2 : R ^ 2 ≤ k ^ 2 / 196) (hτ0 : 0 ≤ τ) (hτ2 : τ ≤ 2 * k)
    (hε0 : 0 ≤ ε) (hE3 : E ≤ 3) :
    E * (256 * k ^ 4 + 19200 * R ^ 4 + 4 * τ * k ^ 2 + 8 * τ * R ^ 2 + τ ^ 2) * ε
      ≤ 770 * k ^ 4 * ε := by
  have hk0 : (0 : ℝ) < k := by linarith
  have hk2 : (0 : ℝ) < k ^ 2 := by positivity
  have hk3 : (0 : ℝ) < k ^ 3 := by positivity
  have hk4 : (0 : ℝ) ≤ k ^ 4 := by positivity
  have hR2nn : (0 : ℝ) ≤ R ^ 2 := sq_nonneg R
  have hR4 : R ^ 4 ≤ k ^ 4 / 38416 := by
    have h := pow_le_pow_left₀ hR2nn hR2 2
    rwa [show (R ^ 2) ^ 2 = R ^ 4 by ring,
      show (k ^ 2 / 196) ^ 2 = k ^ 4 / 38416 by ring] at h
  have hA : 19200 * R ^ 4 ≤ k ^ 4 / 2 := by linarith only [hR4, hk4]
  have hB : 4 * τ * k ^ 2 ≤ k ^ 4 / 100 := by
    have h1 : 4 * τ * k ^ 2 ≤ 8 * k ^ 3 := by
      have h := mul_le_mul_of_nonneg_right hτ2 (by positivity : (0 : ℝ) ≤ 4 * k ^ 2)
      linarith only [h]
    have h2 : 8 * k ^ 3 ≤ k ^ 4 / 100 := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 100)]
      have h := mul_le_mul_of_nonneg_right hk hk3.le
      linarith only [h, hk3.le]
    linarith only [h1, h2]
  have hC : 8 * τ * R ^ 2 ≤ k ^ 4 / 100 := by
    have h1 : τ * R ^ 2 ≤ (2 * k) * (k ^ 2 / 196) := mul_le_mul hτ2 hR2 hR2nn (by positivity)
    have h2 : 8 * ((2 * k) * (k ^ 2 / 196)) ≤ k ^ 4 / 100 := by
      rw [show 8 * ((2 * k) * (k ^ 2 / 196)) = 8 * k ^ 3 / 98 by ring]
      rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 98) (by norm_num : (0 : ℝ) < 100)]
      have h := mul_le_mul_of_nonneg_right hk hk3.le
      linarith only [h, hk3.le]
    have h3 : 8 * (τ * R ^ 2) ≤ 8 * ((2 * k) * (k ^ 2 / 196)) :=
      mul_le_mul_of_nonneg_left h1 (by norm_num)
    linarith only [h2, h3]
  have hD : τ ^ 2 ≤ k ^ 4 / 100 := by
    have h1 : τ ^ 2 ≤ (2 * k) ^ 2 := by
      have h := mul_le_mul hτ2 hτ2 hτ0 (by positivity)
      linarith only [h]
    have h2 : (2 * k) ^ 2 ≤ k ^ 4 / 100 := by
      rw [show (2 * k) ^ 2 = 4 * k ^ 2 by ring, le_div_iff₀ (by norm_num : (0 : ℝ) < 100)]
      have hsq : (1000 : ℝ) * 1000 ≤ k * k := mul_le_mul hk hk (by norm_num) hk0.le
      have h := mul_le_mul_of_nonneg_right hsq (by positivity : (0 : ℝ) ≤ k ^ 2)
      linarith only [h, hk2.le]
    linarith only [h1, h2]
  have hS : 256 * k ^ 4 + 19200 * R ^ 4 + 4 * τ * k ^ 2 + 8 * τ * R ^ 2 + τ ^ 2
      ≤ 770 / 3 * k ^ 4 := by
    linarith only [hA, hB, hC, hD, hk4]
  have hS0 : 0 ≤ 256 * k ^ 4 + 19200 * R ^ 4 + 4 * τ * k ^ 2 + 8 * τ * R ^ 2 + τ ^ 2 := by
    have h1 : (0 : ℝ) ≤ 256 * k ^ 4 := by positivity
    have h2 : (0 : ℝ) ≤ 19200 * R ^ 4 := by positivity
    have h3 : (0 : ℝ) ≤ 4 * τ * k ^ 2 := by positivity
    have h4 : (0 : ℝ) ≤ 8 * τ * R ^ 2 := by positivity
    have h5 : (0 : ℝ) ≤ τ ^ 2 := by positivity
    linarith only [h1, h2, h3, h4, h5]
  have hstep : E * (256 * k ^ 4 + 19200 * R ^ 4 + 4 * τ * k ^ 2 + 8 * τ * R ^ 2 + τ ^ 2)
      ≤ 3 * (770 / 3 * k ^ 4) := mul_le_mul hE3 hS hS0 (by norm_num)
  have hstep2 : E * (256 * k ^ 4 + 19200 * R ^ 4 + 4 * τ * k ^ 2 + 8 * τ * R ^ 2 + τ ^ 2)
      ≤ 770 * k ^ 4 := by linarith only [hstep]
  exact mul_le_mul_of_nonneg_right hstep2 hε0

/-! ## §3 侧条件的孤立算术引理（上下文只含所需的几个变量） -/

/-- `a·(log q / q)^{2/3} ≥ 18.5/k`（`q ≥ 10020`、`k ≥ q/2`、`a ≥ 2`、`log q ≥ 1`）。 -/
private lemma rpow_two_thirds_lower {q k a : ℝ} (hq0 : 0 < q) (hq : 10020 ≤ q)
    (hk : q / 2 ≤ k) (ha : 2 ≤ a) (hlog : 1 ≤ Real.log q) :
    (18.5 : ℝ) / k ≤ a * (Real.log q / q) ^ (2 / 3 : ℝ) := by
  have hk0 : (0 : ℝ) < k := by linarith
  have h1 : (1 : ℝ) / k ≤ 2 / q := by
    rw [div_le_div_iff₀ hk0 hq0]
    linarith only [hk]
  have h1' : (18.5 : ℝ) / k ≤ 37 / q := by
    have h := mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 18.5)
    have e1 : (18.5 : ℝ) * (1 / k) = 18.5 / k := by ring
    have e2 : (18.5 : ℝ) * (2 / q) = 37 / q := by ring
    linarith only [h, e1.le, e1.ge, e2.le, e2.ge]
  have h3 : q ^ (-(2 / 3) : ℝ) ≤ (Real.log q / q) ^ (2 / 3 : ℝ) := by
    have h4 : (1 : ℝ) / q ≤ Real.log q / q := by
      rw [div_le_div_iff_of_pos_right hq0]
      exact hlog
    have h5 := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ 1 / q) h4
      (by norm_num : (0 : ℝ) ≤ 2 / 3)
    rwa [one_div, Real.inv_rpow hq0.le, ← Real.rpow_neg hq0.le] at h5
  have h2 : (2 : ℝ) * q ^ (-(2 / 3) : ℝ) ≤ a * (Real.log q / q) ^ (2 / 3 : ℝ) := by
    have ha0 : (0 : ℝ) ≤ a := by linarith
    calc (2 : ℝ) * q ^ (-(2 / 3) : ℝ) ≤ a * q ^ (-(2 / 3) : ℝ) :=
          mul_le_mul_of_nonneg_right ha (Real.rpow_nonneg hq0.le _)
      _ ≤ a * (Real.log q / q) ^ (2 / 3 : ℝ) := mul_le_mul_of_nonneg_left h3 ha0
  have h7 : (21 : ℝ) ≤ q ^ (1 / 3 : ℝ) := by
    have hq9261 : (9261 : ℝ) ≤ q := by linarith only [hq]
    have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 9261) hq9261
      (by norm_num : (0 : ℝ) ≤ 1 / 3)
    have h8 : (9261 : ℝ) = 21 ^ 3 := by norm_num
    rw [h8, ← Real.rpow_natCast (21 : ℝ) 3, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 21)] at h
    norm_num at h
    exact h
  have h9 : q ^ (-(2 / 3) : ℝ) * q = q ^ (1 / 3 : ℝ) := by
    calc q ^ (-(2 / 3) : ℝ) * q = q ^ (-(2 / 3) : ℝ) * q ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = q ^ (-(2 / 3) + 1 : ℝ) := by rw [Real.rpow_add hq0]
      _ = q ^ (1 / 3 : ℝ) := by norm_num
  have h6 : (37 : ℝ) / q ≤ 2 * q ^ (-(2 / 3) : ℝ) := by
    rw [div_le_iff₀ hq0]
    calc (37 : ℝ) ≤ 2 * q ^ (1 / 3 : ℝ) := by linarith only [h7]
      _ = 2 * (q ^ (-(2 / 3) : ℝ) * q) := by rw [h9]
      _ = 2 * q ^ (-(2 / 3) : ℝ) * q := by ring
  linarith only [h1', h2, h6]

/-- `tailR B τ (e^{-δ'}) ≤ e^{-(t-1/k)}`（用 `2√(B/τ) ≤ 1/k` 与 `t ≤ δ'`）。 -/
private lemma tailR_le_exp {B τ δ' t k : ℝ}
    (hg : 2 * Real.sqrt (B / τ) ≤ 1 / k) (htδ : t ≤ δ') :
    tailR B τ (Real.exp (-δ')) ≤ Real.exp (-(t - 1 / k)) := by
  rw [tailR, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  linarith only [hg, htδ]

/-- `r ≤ e^{-(t-1/k)}`、`t ≥ 18.5/k`、`t ≤ 1/4` ⟹ `1/(1-r) ≤ k/14`。 -/
private lemma R_le_of_threshold {k t r : ℝ} (hk : 0 < k) (ht18 : (18.5 : ℝ) / k ≤ t)
    (ht14 : t ≤ 1 / 4) (hr : r ≤ Real.exp (-(t - 1 / k))) :
    1 / (1 - r) ≤ k / 14 := by
  set y : ℝ := t - 1 / k with hydef
  have hk1 : (0 : ℝ) < k⁻¹ := inv_pos.mpr hk
  have h14k : (0 : ℝ) < 14 / k := div_pos (by norm_num) hk
  have hB : (1 : ℝ) / k = k⁻¹ := by ring
  have hA : (18.5 : ℝ) * k⁻¹ ≤ t := by
    have e : (18.5 : ℝ) / k = 18.5 * k⁻¹ := by ring
    linarith only [ht18, e.le, e.ge]
  have hy0 : (0 : ℝ) ≤ y := by rw [hydef]; linarith only [hA, hk1, hB.le, hB.ge]
  have hy1 : y ≤ 1 / 4 := by rw [hydef]; linarith only [ht14, hk1, hB.le, hB.ge]
  have hy17 : (17.5 : ℝ) / k ≤ y := by
    rw [hydef]
    have e : (17.5 : ℝ) / k = 17.5 * k⁻¹ := by ring
    linarith only [hA, hk1, hB.le, hB.ge, e.le, e.ge]
  have hy' : (0 : ℝ) < 1 + y := by linarith only [hy0]
  have hexp : Real.exp (-y) ≤ 1 / (1 + y) := by
    rw [Real.exp_neg, one_div]
    exact (inv_le_inv₀ (Real.exp_pos _) hy').mpr (by linarith only [Real.add_one_le_exp y])
  have h2 : (14 : ℝ) / k ≤ 1 - r := by
    have h3 : (14 : ℝ) / k ≤ y / (1 + y) := by
      rw [le_div_iff₀ hy']
      have h4 : 1 + y ≤ 5 / 4 := by linarith only [hy1]
      have h5 : (14 : ℝ) / k * (1 + y) ≤ (14 : ℝ) / k * (5 / 4) :=
        mul_le_mul_of_nonneg_left h4 h14k.le
      have h6 : (14 : ℝ) / k * (5 / 4) ≤ y := by
        have e : (14 : ℝ) / k * (5 / 4) = (17.5 : ℝ) / k := by ring
        linarith only [hy17, e.le, e.ge]
      linarith only [h5, h6]
    have h7 : y / (1 + y) = 1 - 1 / (1 + y) := by
      field_simp
      ring
    linarith only [h3, hexp, h7.le, h7.ge, hr]
  calc 1 / (1 - r) ≤ 1 / ((14 : ℝ) / k) := one_div_le_one_div_of_le h14k h2
    _ = k / 14 := by field_simp

/-! ## §4 具体常数的 collar 界（`Cd1 = 7`、`Cd2 = 770`、`β = 4`） -/

/-- **具体 collar 界**：`τ·M₁ ≤ 7·k²·ε`、`τ²·M₂ ≤ 770·k⁴·ε`。

（`E := e^{k·g}`、`g := 2√(B/τ)`、`R := 1/(1-r')`、`ε_h := e^{τ sinh δ'}e^{-δ'k}`；
`SharpDerivGen` 的 honest 界乘 `ε_h ≤ ε/(2R)` 后 `R` 相消，侧条件 `k²B ≤ τ/4` 给 `E ≤ 3`、
`g ≤ 1/k`，而 `R ≤ 2^{1/3}k^{1/3}`（由 `1-r' ≥ δ'/2 ≥ q^{-1/3}`）给出 `R² ≤ k²/5000`。） -/
theorem collar_bound_concrete (K a : ℝ) (hK : K₀ ≤ K) (ha : 2 ≤ a) :
    SharpCollarFrom (effN0End K a) 7 770 a 4 := by
  intro N hN L α θ hAdm hτρ
  set q : ℝ := 2 * (N : ℝ) + 2 with hqdef
  set k : ℕ := 2 * N + 1 with hkdef
  set τ : ℝ := (∑ j, θ j) / 2 with hτdef
  set ρ : ℝ := rhoA a q with hρdef
  set δ' : ℝ := deltaOf ρ with hδ'def
  set ε : ℝ := epsOf τ δ' k with hεdef
  set B : ℝ := Real.sqrt ε with hBdef
  have hNa : Nat.ceil (256 * a ^ 3) ≤ effN0End K a :=
    le_trans (le_max_left _ _) (le_max_left _ _)
  have hNq : Nat.ceil (effQ0 7 770 K a 4 / 2) ≤ effN0End K a :=
    le_trans (le_max_right _ _) (le_max_left _ _)
  have hNmin : Nat.ceil (effQmin a / 2) ≤ effN0End K a := le_max_right _ _
  have hNa' : Nat.ceil (256 * a ^ 3) ≤ N := le_trans hNa hN
  have hNmin' : Nat.ceil (effQmin a / 2) ≤ N := le_trans hNmin hN
  have hN5 : 5000 ≤ N := by
    have h1 : (10020 : ℝ) ≤ effQmin a := le_max_left _ _
    have h2 : (5010 : ℝ) ≤ effQmin a / 2 := by linarith only [h1]
    have h3 : (5010 : ℝ) ≤ (Nat.ceil (effQmin a / 2) : ℝ) := le_trans h2 (Nat.le_ceil _)
    have h3' : (Nat.ceil (effQmin a / 2) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNmin'
    have h4 : (5010 : ℝ) ≤ (N : ℝ) := le_trans h3 h3'
    have h5 : 5010 ≤ N := by exact_mod_cast h4
    omega
  have hq512 : 512 * a ^ 3 ≤ q := by
    have h1 : (256 * a ^ 3 : ℝ) ≤ (Nat.ceil (256 * a ^ 3) : ℝ) := Nat.le_ceil _
    have h2 : (Nat.ceil (256 * a ^ 3) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNa'
    rw [hqdef]; linarith
  have hqminAll : effQmin a ≤ q := by
    have h1 : effQmin a / 2 ≤ (Nat.ceil (effQmin a / 2) : ℝ) := Nat.le_ceil _
    have h2 : (Nat.ceil (effQmin a / 2) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNmin'
    rw [hqdef]; linarith
  have hq10020 : (10020 : ℝ) ≤ q := by
    have h1 : (10020 : ℝ) ≤ effQmin a := le_max_left _ _
    have h2 : effQmin a ≤ q := hqminAll
    linarith only [h1, h2]
  have hqthr : (20 * Real.exp 1 * a ^ (-(1 / 4 : ℝ))) ^ (1 / (effS a / 2 - 7 / 6)) ≤ q :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hqminAll
  have hq4 : (10 : ℝ) ^ 4 ≤ q := by
    have h1 : (10020 : ℝ) ≤ effQmin a := le_max_left _ _
    linarith
  have hq0 : 0 < q := by linarith
  have hq1 : 1 ≤ q := by linarith
  have hexp1 : Real.exp 1 ≤ q := by
    have h1 : Real.exp 1 ≤ effQmin a := le_trans (le_max_left _ _) (le_max_right _ _)
    linarith
  have hlog1 : (1 : ℝ) ≤ Real.log q := by
    rw [Real.le_log_iff_exp_le hq0]; exact hexp1
  have hl : 0 < Real.log q := lt_of_lt_of_le one_pos hlog1
  have hk1000 : 1000 ≤ k := by
    have h1 : (5000 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN5
    rw [hkdef]; omega
  have hk1000R : (1000 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1000
  have ha0 : 0 < a := by linarith
  have hKpos : 0 < K := lt_of_lt_of_le K₀_pos hK
  clear hN hNa hNq hNmin hqminAll hNa' hNmin'
  have hat : a * (Real.log q / q) ^ (2 / 3 : ℝ) ≤ 1 / 4 := by
    have hlog : Real.log q ≤ 2 * Real.sqrt q := log_le_two_sqrt q hq1
    have hsq : 0 < Real.sqrt q := Real.sqrt_pos_of_pos hq0
    have hdiv : Real.log q / q ≤ 2 / Real.sqrt q := by
      rw [div_le_div_iff₀ hq0 hsq]
      have h := mul_le_mul_of_nonneg_right hlog (Real.sqrt_nonneg q)
      have h2 := Real.sq_sqrt hq0.le
      linarith only [h, h2]
    have ht : (Real.log q / q) ^ (2 / 3 : ℝ) ≤ (2 / Real.sqrt q) ^ (2 / 3 : ℝ) :=
      Real.rpow_le_rpow (le_of_lt (div_pos hl hq0)) hdiv (by norm_num)
    have h2 : (2 / Real.sqrt q) ^ (2 / 3 : ℝ) = 2 ^ (2 / 3 : ℝ) * q ^ (-(1 / 3 : ℝ)) := by
      rw [Real.div_rpow (by norm_num : (0 : ℝ) ≤ 2) (Real.sqrt_nonneg q), Real.sqrt_eq_rpow,
        ← Real.rpow_mul hq0.le]
      norm_num
      rw [Real.rpow_neg hq0.le, div_eq_mul_inv]
    have ha3 : (0 : ℝ) ≤ a ^ 3 := by positivity
    have hq13 : 8 * a ≤ q ^ (1 / 3 : ℝ) := by
      have h1 : (512 * a ^ 3) ^ (1 / 3 : ℝ) ≤ q ^ (1 / 3 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hq512 (by norm_num)
      have h2 : (512 * a ^ 3) ^ (1 / 3 : ℝ) = 8 * a := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 512) ha3,
          ← Real.rpow_natCast a 3, ← Real.rpow_mul ha0.le]
        norm_num
      linarith [h1, h2.le, h2.ge]
    have h3 : a * (2 ^ (2 / 3 : ℝ) * q ^ (-(1 / 3 : ℝ))) ≤ 1 / 4 := by
      rw [Real.rpow_neg hq0.le, ← div_eq_mul_inv,
        show a * (2 ^ (2 / 3 : ℝ) / q ^ (1 / 3 : ℝ)) = a * 2 ^ (2 / 3 : ℝ) / q ^ (1 / 3 : ℝ) by
          ring,
        div_le_iff₀ (Real.rpow_pos_of_pos hq0 _)]
      have h5 : (2 : ℝ) ^ (2 / 3 : ℝ) ≤ 2 := by
        calc (2 : ℝ) ^ (2 / 3 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          _ = 2 := Real.rpow_one 2
      nlinarith only [hq13, ha0, h5]
    have h4 : a * (Real.log q / q) ^ (2 / 3 : ℝ) ≤ a * (2 ^ (2 / 3 : ℝ) * q ^ (-(1 / 3 : ℝ))) := by
      rw [← h2]
      exact mul_le_mul_of_nonneg_left ht ha0.le
    linarith [h4, h3]
  obtain ⟨h34, hlt1, hρ0, hρ12⟩ := rhoA_bounds hq4 ha0 hat
  have hδ'pos : 0 < δ' := by rw [hδ'def]; exact deltaOf_pos hρ0 hlt1
  have hδ'1 : δ' ≤ 1 := by rw [hδ'def]; exact deltaOf_le_one h34 hlt1
  have hτ0 : 0 ≤ τ := by
    rw [hτdef]
    exact div_nonneg (Finset.sum_nonneg fun j _ => hAdm.1 j) (by norm_num)
  have hτpos : 0 < τ := by
    rcases lt_or_eq_of_le hτ0 with h | h
    · exact h
    · exfalso
      have hsum0 : ∑ j, θ j = 0 := by rw [hτdef] at h; linarith
      have h1 := h_zero_of_admissible_of_cost_eq_zero hAdm hsum0
      have h2 := h_zero_ge Real.pi Real.pi_pos.le le_rfl L α θ hAdm.2.1
      rw [h1] at h2
      have h3 : Real.cos (Real.pi / 2) = 0 := Real.cos_pi_div_two
      linarith
  have hτlow : q / Real.exp 1 ≤ τ := by
    have h1 := elementary_bound_pi hAdm
    have h2 := div_exp_lt_factorial_rpow (2 * N + 2) (by omega)
    have hcost : cost θ = 2 * τ := by rw [cost, hτdef]; ring
    rw [hcost] at h1
    have hq : ((2 * N + 2 : ℕ) : ℝ) = q := by rw [hqdef]; push_cast; ring
    rw [hq] at h1 h2
    linarith
  have hεpos : 0 < ε := by rw [hεdef]; exact epsOf_pos hδ'pos τ k
  have hε0 : 0 ≤ ε := hεpos.le
  have hBpos : 0 < B := by rw [hBdef]; exact Real.sqrt_pos_of_pos hεpos
  have hkB4 : (k : ℝ) ^ 2 * B ≤ τ / 4 := by
    have h := ksq_sqrt_epsOf_le_gen (a := a) (q := q) (τ := τ) (N := N) hq0 hq1 hqdef hq4
      hlog1 ha hat hqthr hτ0 hτρ hτlow
    have h2 : ((k : ℕ) : ℝ) ^ 2 * B
        = ((2 * N + 1 : ℕ) : ℝ) ^ 2
          * Real.sqrt (epsOf τ (deltaOf (rhoA a q)) (2 * N + 1)) := by
      rw [hkdef, hBdef, hεdef, hδ'def, hρdef]
    rw [h2]; exact h
  have hkB : (k : ℝ) ^ 2 * B ≤ τ := by linarith
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hksq : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
  have hksq4 : (0 : ℝ) < 4 * (k : ℝ) ^ 2 := by positivity
  have hBτ : B / τ ≤ 1 / 2 := by
    have h1 : B / τ ≤ 1 / (4 * (k : ℝ) ^ 2) := by
      rw [div_le_div_iff₀ hτpos hksq4]
      nlinarith only [hkB4]
    have h2 : (1 : ℝ) / (4 * (k : ℝ) ^ 2) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ hksq4 (by norm_num)]
      have hk2big : (2 : ℝ) ≤ 4 * (k : ℝ) ^ 2 := by
        have h3 : (1000000 : ℝ) ≤ (k : ℝ) ^ 2 := by
          have hk0' : (0 : ℝ) ≤ (k : ℝ) := by linarith only [hk1000R]
          have h := mul_le_mul hk1000R hk1000R (by norm_num : (0 : ℝ) ≤ 1000) hk0'
          linarith only [h]
        linarith only [h3]
      linarith only [hk2big]
    linarith only [h1, h2]
  have hg1 : (k : ℝ) * (2 * Real.sqrt (B / τ)) ≤ 1 := by
    have h1 : B / τ ≤ 1 / (4 * (k : ℝ) ^ 2) := by
      rw [div_le_div_iff₀ hτpos hksq4]
      nlinarith only [hkB4]
    have h2 : Real.sqrt (B / τ) ≤ 1 / (2 * (k : ℝ)) := by
      have h := Real.sqrt_le_sqrt h1
      rwa [show Real.sqrt (1 / (4 * (k : ℝ) ^ 2)) = 1 / (2 * (k : ℝ)) by
        rw [show (1 : ℝ) / (4 * (k : ℝ) ^ 2) = (1 / (2 * (k : ℝ))) ^ 2 by field_simp; ring,
          Real.sqrt_sq (by positivity)]] at h
    have hk0 : (0 : ℝ) < (k : ℝ) := hkpos
    have h3 : 2 * Real.sqrt (B / τ) ≤ 1 / (k : ℝ) := by
      have h := mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ) ≤ 2)
      have he : 2 * (1 / (2 * (k : ℝ))) = 1 / (k : ℝ) := by field_simp
      linarith only [h, he.le, he.ge]
    have h4 : 2 * Real.sqrt (B / τ) * (k : ℝ) ≤ 1 := by
      have h := mul_le_mul_of_nonneg_right h3 hk0.le
      rwa [one_div, inv_mul_cancel₀ (ne_of_gt hk0)] at h
    linarith only [h4]
  have hE3 : Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ))) ≤ 3 := by
    calc Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ))) ≤ Real.exp 1 := Real.exp_le_exp.mpr hg1
      _ ≤ 3 := le_of_lt Real.exp_one_lt_three
  have hτq : τ ≤ q := by nlinarith only [hτρ, hρ0, hlt1, hq0]
  have hq2k : q ≤ 2 * (k : ℝ) := by
    rw [hqdef, hkdef]; push_cast
    have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith only [hN0]
  -- 侧条件：`t := 1 - ρ` 的下界与 `R` 的界
  have hqhalf : q / 2 ≤ (k : ℝ) := by linarith only [hq2k]
  set t : ℝ := a * (Real.log q / q) ^ (2 / 3 : ℝ) with htdef
  have ht_one : 1 - ρ = t := by rw [htdef, hρdef, rhoA]; ring
  have ht_le : t ≤ 1 / 4 := by rw [htdef]; exact hat
  have ht_ge : (18.5 : ℝ) / (k : ℝ) ≤ t := by
    rw [htdef]
    exact rpow_two_thirds_lower hq0 hq10020 hqhalf ha hlog1
  have hδ't : t ≤ δ' := by
    rw [← ht_one, hδ'def]
    exact one_sub_le_deltaOf hρ0 hlt1
  have hδ'2 : (2 : ℝ) ≤ δ' * (k : ℝ) := by
    have h1 : t * (k : ℝ) ≤ δ' * (k : ℝ) := mul_le_mul_of_nonneg_right hδ't hkpos.le
    have h2 : (18.5 : ℝ) ≤ t * (k : ℝ) := by
      have h := mul_le_mul_of_nonneg_right ht_ge hkpos.le
      rwa [div_mul_cancel₀ _ (ne_of_gt hkpos)] at h
    linarith only [h1, h2]
  have hgle : 2 * Real.sqrt (B / τ) ≤ 1 / (k : ℝ) := by
    rw [le_div_iff₀ hkpos]
    linarith only [hg1]
  have hg2 : 2 * Real.sqrt (B / τ) ≤ δ' / 2 := by
    have h12 : (1 : ℝ) / (k : ℝ) ≤ δ' / 2 := by
      rw [div_le_div_iff₀ hkpos (by norm_num : (0 : ℝ) < 2)]
      linarith only [hδ'2]
    linarith only [hgle, h12]
  have hr1 : tailR B τ (Real.exp (-δ')) < 1 := by
    rw [tailR, ← Real.exp_add, Real.exp_lt_one_iff]
    linarith only [hg2, hδ'pos]
  -- `R := 1/(1-r')`，honest 常数相消
  set R : ℝ := 1 / (1 - tailR B τ (Real.exp (-δ'))) with hRdef
  have hRpos : 0 < R := by
    rw [hRdef]
    have : tailR B τ (Real.exp (-δ')) < 1 := hr1
    positivity
  have hεh : Real.exp (τ * Real.sinh δ') * Real.exp (-δ') ^ k ≤ ε / (2 * R) := by
    have h := honest_le_eps_mul (τ := τ) (δ' := δ') (B := B) (k := k) hδ'pos hδ'1 hg2
    rw [← hεdef] at h
    have h2 : (1 - tailR B τ (Real.exp (-δ'))) / 2 = 1 / (2 * R) := by
      rw [hRdef]; field_simp
    have h3 : ε * ((1 - tailR B τ (Real.exp (-δ'))) / 2) = ε / (2 * R) := by
      rw [h2]; ring
    linarith only [h, h3.le, h3.ge]
  -- `1 - r' ≥ 14/k`，故 `R ≤ k/14`
  have hrt : tailR B τ (Real.exp (-δ')) ≤ Real.exp (-(t - 1 / (k : ℝ))) :=
    tailR_le_exp hgle hδ't
  have hRk : R ≤ (k : ℝ) / 14 := by
    rw [hRdef]
    exact R_le_of_threshold hkpos ht_ge ht_le hrt
  have hR2 : R ^ 2 ≤ (k : ℝ) ^ 2 / 196 := by
    have h1 : R ^ 2 ≤ ((k : ℝ) / 14) ^ 2 := pow_le_pow_left₀ hRpos.le hRk 2
    have h2 : ((k : ℝ) / 14) ^ 2 = (k : ℝ) ^ 2 / 196 := by ring
    linarith only [h1, h2.le, h2.ge]
  have hR1 : (1 - tailR B τ (Real.exp (-δ')))⁻¹ = R := by rw [hRdef, one_div]
  have hR3 : ((1 - tailR B τ (Real.exp (-δ'))) ^ 3)⁻¹ = R ^ 3 := by rw [← hR1, inv_pow]
  have hR5 : ((1 - tailR B τ (Real.exp (-δ'))) ^ 5)⁻¹ = R ^ 5 := by rw [← hR1, inv_pow]
  have hεh0 : (0 : ℝ) ≤ Real.exp (τ * Real.sinh δ') * Real.exp (-δ') ^ k := by positivity
  have hτ2k : τ ≤ 2 * (k : ℝ) := le_trans hτq hq2k
  -- 应用 SharpDerivGen
  have hdec := fcoef_tail_le hτ0 hδ'pos (k := k) (by omega)
  have hM1 := norm_deriv_psiA_scaled_collar_gen τ B hτpos hBpos (k := k) (by omega)
    hεh0 (Real.exp_pos _).le hr1 hdec
  have hM2 := norm_deriv2_psiA_scaled_collar_gen τ B hτpos hBpos (k := k) (by omega)
    hεh0 (Real.exp_pos _).le hr1 hdec hBτ
  -- `M₁`、`M₂` 的显式常数（R 形式），先备好非负性与单调性所需事实
  have hS1nn : (0 : ℝ) ≤ 2 * (k : ℝ) ^ 2 * R + 4 * R ^ 3 + τ * R :=
    add_nonneg (add_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hRpos.le)
        (mul_nonneg (by norm_num) (pow_nonneg hRpos.le 3)))
      (mul_nonneg hτ0 hRpos.le)
  have hEnn : (0 : ℝ) ≤ 2 * Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ)))
      * (2 * (k : ℝ) ^ 2 * R + 4 * R ^ 3 + τ * R) :=
    mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos _).le) hS1nn
  have hS2nn : (0 : ℝ) ≤ 256 * (k : ℝ) ^ 4 * R + 19200 * R ^ 5 + 4 * τ * (k : ℝ) ^ 2 * R
      + 8 * τ * R ^ 3 + τ ^ 2 * R := by
    have f1 : (0 : ℝ) ≤ 256 * (k : ℝ) ^ 4 * R :=
      mul_nonneg (mul_nonneg (by norm_num) (by positivity)) hRpos.le
    have f2 : (0 : ℝ) ≤ 19200 * R ^ 5 := mul_nonneg (by norm_num) (pow_nonneg hRpos.le 5)
    have f3 : (0 : ℝ) ≤ 4 * τ * (k : ℝ) ^ 2 * R :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hτ0) (by positivity)) hRpos.le
    have f4 : (0 : ℝ) ≤ 8 * τ * R ^ 3 :=
      mul_nonneg (mul_nonneg (by norm_num) hτ0) (pow_nonneg hRpos.le 3)
    have f5 : (0 : ℝ) ≤ τ ^ 2 * R := mul_nonneg (pow_nonneg hτ0 2) hRpos.le
    linarith only [f1, f2, f3, f4, f5]
  have hEnn2 : (0 : ℝ) ≤ 2 * Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ)))
      * (256 * (k : ℝ) ^ 4 * R + 19200 * R ^ 5 + 4 * τ * (k : ℝ) ^ 2 * R
          + 8 * τ * R ^ 3 + τ ^ 2 * R) :=
    mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos _).le) hS2nn
  refine ⟨2 * Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ)))
        * (2 * (k : ℝ) ^ 2 * R + 4 * R ^ 3 + τ * R)
        * (Real.exp (τ * Real.sinh δ') * Real.exp (-δ') ^ k) / τ,
      2 * Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ)))
        * (256 * (k : ℝ) ^ 4 * R + 19200 * R ^ 5 + 4 * τ * (k : ℝ) ^ 2 * R
            + 8 * τ * R ^ 3 + τ ^ 2 * R)
        * (Real.exp (τ * Real.sinh δ') * Real.exp (-δ') ^ k) / τ ^ 2,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact div_nonneg (mul_nonneg hEnn hεh0) hτpos.le
  · exact div_nonneg (mul_nonneg hEnn2 hεh0) (pow_nonneg hτpos.le 2)
  · intro μ hμ
    have h := hM1 μ hμ
    have heq : (2 * (k : ℝ) ^ 2 / (1 - tailR B τ (Real.exp (-δ')))
          + 4 / (1 - tailR B τ (Real.exp (-δ'))) ^ 3
          + τ / (1 - tailR B τ (Real.exp (-δ'))))
        = 2 * (k : ℝ) ^ 2 * R + 4 * R ^ 3 + τ * R := by
      simp only [div_eq_mul_inv, hR1, hR3]
    rwa [heq] at h
  · intro μ hμ
    have h := hM2 μ hμ
    have heq : (256 * (k : ℝ) ^ 4 / (1 - tailR B τ (Real.exp (-δ')))
          + 19200 / (1 - tailR B τ (Real.exp (-δ'))) ^ 5
          + 4 * τ * (k : ℝ) ^ 2 / (1 - tailR B τ (Real.exp (-δ')))
          + 8 * τ / (1 - tailR B τ (Real.exp (-δ'))) ^ 3
          + τ ^ 2 / (1 - tailR B τ (Real.exp (-δ'))))
        = 256 * (k : ℝ) ^ 4 * R + 19200 * R ^ 5 + 4 * τ * (k : ℝ) ^ 2 * R
          + 8 * τ * R ^ 3 + τ ^ 2 * R := by
      simp only [div_eq_mul_inv, hR1, hR3, hR5]
    rwa [heq] at h
  · -- `τ·M₁ ≤ 7·k²·ε`
    calc τ * (2 * Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ)))
          * (2 * (k : ℝ) ^ 2 * R + 4 * R ^ 3 + τ * R)
          * (Real.exp (τ * Real.sinh δ') * Real.exp (-δ') ^ k) / τ)
        = 2 * Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ)))
            * (2 * (k : ℝ) ^ 2 * R + 4 * R ^ 3 + τ * R)
            * (Real.exp (τ * Real.sinh δ') * Real.exp (-δ') ^ k) := by
          field_simp
      _ ≤ 2 * Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ)))
            * (2 * (k : ℝ) ^ 2 * R + 4 * R ^ 3 + τ * R) * (ε / (2 * R)) :=
          mul_le_mul_of_nonneg_left hεh hEnn
      _ = Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ)))
            * (2 * (k : ℝ) ^ 2 + 4 * R ^ 2 + τ) * ε := by
          field_simp
      _ ≤ 7 * (k : ℝ) ^ 2 * ε :=
          arith_M1 (k := (k : ℝ)) (R := R) (τ := τ) (ε := ε)
            (E := Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ))))
            hk1000R hRpos hR2 hτ0 hτ2k hε0 hE3
  · -- `τ²·M₂ ≤ 770·k⁴·ε`
    calc τ ^ 2 * (2 * Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ)))
          * (256 * (k : ℝ) ^ 4 * R + 19200 * R ^ 5 + 4 * τ * (k : ℝ) ^ 2 * R
              + 8 * τ * R ^ 3 + τ ^ 2 * R)
          * (Real.exp (τ * Real.sinh δ') * Real.exp (-δ') ^ k) / τ ^ 2)
        = 2 * Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ)))
            * (256 * (k : ℝ) ^ 4 * R + 19200 * R ^ 5 + 4 * τ * (k : ℝ) ^ 2 * R
                + 8 * τ * R ^ 3 + τ ^ 2 * R)
            * (Real.exp (τ * Real.sinh δ') * Real.exp (-δ') ^ k) := by
          field_simp
      _ ≤ 2 * Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ)))
            * (256 * (k : ℝ) ^ 4 * R + 19200 * R ^ 5 + 4 * τ * (k : ℝ) ^ 2 * R
                + 8 * τ * R ^ 3 + τ ^ 2 * R) * (ε / (2 * R)) :=
          mul_le_mul_of_nonneg_left hεh hEnn2
      _ = Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ)))
            * (256 * (k : ℝ) ^ 4 + 19200 * R ^ 4 + 4 * τ * (k : ℝ) ^ 2 + 8 * τ * R ^ 2 + τ ^ 2)
            * ε := by
          field_simp
      _ ≤ 770 * (k : ℝ) ^ 4 * ε :=
          arith_M2 (k := (k : ℝ)) (R := R) (τ := τ) (ε := ε)
            (E := Real.exp ((k : ℝ) * (2 * Real.sqrt (B / τ))))
            hk1000R hR2 hτ0 hτ2k hε0 hE3

/-- **无条件端到端定理（具体常数 `(7, 770, 4)`）**：对一切 `a ≥ 2`、`K ≥ K₀`、
`N ≥ effN0End K a` 与一切 admissible 构造，
`4(N+1)·(1 - a(log q/q)^{2/3}) ≤ cost θ`（`q = 2N+2`）。 -/
theorem endgame_bound_of_le (K a : ℝ) (hK : K₀ ≤ K) (ha : 2 ≤ a) :
    ∀ N ≥ effN0End K a, ∀ {L : ℕ} {α θ : Fin L → ℝ}, Admissible N Real.pi L α θ →
      4 * ((N : ℝ) + 1)
        * (1 - a * (Real.log (2 * (N : ℝ) + 2) / (2 * (N : ℝ) + 2)) ^ (2 / 3 : ℝ))
        ≤ cost θ :=
  effective_bound_of_collar (effN0End K a) 7 770 K a 4
    (by norm_num) (by norm_num) hK ha (by norm_num) le_rfl
    (le_trans (le_max_left _ _) (le_max_left _ _))
    (le_trans (le_max_right _ _) (le_max_left _ _))
    (le_max_right _ _)
    (by
      have h1 : (10020 : ℝ) ≤ effQmin a := le_max_left _ _
      have h2 : (5010 : ℝ) ≤ effQmin a / 2 := by linarith
      have h3 : (5010 : ℝ) ≤ (Nat.ceil (effQmin a / 2) : ℝ) := le_trans h2 (Nat.le_ceil _)
      have h4 : (Nat.ceil (effQmin a / 2) : ℝ) ≤ (effN0End K a : ℝ) := by
        rw [effN0End]
        exact_mod_cast (le_max_right _ _)
      have h5 : (5010 : ℝ) ≤ (effN0End K a : ℝ) := le_trans h3 h4
      have h6 : 5010 ≤ effN0End K a := by exact_mod_cast h5
      omega)
    (collar_bound_concrete K a hK ha)

/-- **目标定理**：`K = K₀` 时的无条件端到端界。 -/
theorem endgame_bound (a : ℝ) (ha : 2 ≤ a) :
    ∀ N ≥ effN0End K₀ a, ∀ {L : ℕ} {α θ : Fin L → ℝ}, Admissible N Real.pi L α θ →
      4 * ((N : ℝ) + 1)
        * (1 - a * (Real.log (2 * (N : ℝ) + 2) / (2 * (N : ℝ) + 2)) ^ (2 / 3 : ℝ))
        ≤ cost θ :=
  endgame_bound_of_le K₀ a le_rfl ha

/-- `a = 2.2` 的显式推论（`N₀ = effN0End K₀ 2.2`，数值上为 `45006`）。 -/
theorem endgame_bound_2_2 :
    ∀ N ≥ effN0End K₀ 2.2, ∀ {L : ℕ} {α θ : Fin L → ℝ}, Admissible N Real.pi L α θ →
      4 * ((N : ℝ) + 1)
        * (1 - 2.2 * (Real.log (2 * (N : ℝ) + 2) / (2 * (N : ℝ) + 2)) ^ (2 / 3 : ℝ))
        ≤ cost θ :=
  endgame_bound 2.2 (by norm_num)

/-- `a = 2.3` 的显式推论（`N₀ = effN0End K₀ 2.3`，数值上为 `5010`）。 -/
theorem endgame_bound_2_3 :
    ∀ N ≥ effN0End K₀ 2.3, ∀ {L : ℕ} {α θ : Fin L → ℝ}, Admissible N Real.pi L α θ →
      4 * ((N : ℝ) + 1)
        * (1 - 2.3 * (Real.log (2 * (N : ℝ) + 2) / (2 * (N : ℝ) + 2)) ^ (2 / 3 : ℝ))
        ≤ cost θ :=
  endgame_bound 2.3 (by norm_num)

/-- **全 `N` 形式**：与初等下界合并（`ElementaryBound.elementary_bound_pi`）。 -/
theorem all_N_bound_end (a : ℝ) (ha : 2 ≤ a) :
    ∀ N ≥ 1, ∀ {L : ℕ} {α θ : Fin L → ℝ}, Admissible N Real.pi L α θ →
      max (2 * (Nat.factorial (2 * N + 2) : ℝ) ^ (1 / ((2 * N + 2 : ℕ) : ℝ)))
          (if effN0End K₀ a ≤ N
            then 4 * ((N : ℝ) + 1)
              * (1 - a * (Real.log (2 * (N : ℝ) + 2) / (2 * (N : ℝ) + 2)) ^ (2 / 3 : ℝ))
            else 0)
        ≤ cost θ := by
  intro N hN L α θ hAdm
  refine max_le ?_ ?_
  · exact elementary_bound_pi hAdm
  · by_cases hcase : effN0End K₀ a ≤ N
    · rw [if_pos hcase]
      exact endgame_bound a ha N hcase hAdm
    · rw [if_neg hcase]
      exact Finset.sum_nonneg fun j _ => hAdm.1 j


/-! ## §5 数值化阈值推论（`N₀` 显式数值化） -/


/-- `3.25833 ≤ effS 2.3`。 -/
private lemma effS_2_2_ge : (3.067 : ℝ) ≤ effS 2.2 := by
  rw [effS]
  have hsqrt : (1.4832 : ℝ) ≤ Real.sqrt 2.2 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have h : (3.2628 : ℝ) ≤ (2.2 : ℝ) ^ (3 / 2 : ℝ) := by
    have h3 : (2.2 : ℝ) ^ (3 / 2 : ℝ) = 2.2 * Real.sqrt 2.2 := by
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (by norm_num),
        Real.rpow_one, Real.sqrt_eq_rpow]
    rw [h3]
    nlinarith only [hsqrt]
  calc (3.067 : ℝ) ≤ (47 / 50) * 3.2628 := by norm_num
    _ ≤ (47 / 50) * (2.2 : ℝ) ^ (3 / 2 : ℝ) := mul_le_mul_of_nonneg_left h (by norm_num)

/-- `effK1 7 770 K₀ 2.2 ≤ 292954`。 -/
private lemma effK1_2_2_le : effK1 7 770 K₀ 2.2 ≤ 292954 := by
  rw [effK1, K₀_eq]
  have hs22 : (1.8 : ℝ) ≤ (2.2 : ℝ) ^ (3 / 4 : ℝ) := by
    have h1 : ((1.8 : ℝ) ^ 4) ≤ ((2.2 : ℝ) ^ 3) := by norm_num
    have h2 := Real.rpow_le_rpow (by positivity) h1 (by norm_num : (0 : ℝ) ≤ 1 / 4)
    rwa [show (((1.8 : ℝ) ^ 4)) ^ (1 / 4 : ℝ) = 1.8 by
          rw [← Real.rpow_natCast (1.8 : ℝ) 4, ← Real.rpow_mul (by norm_num)]; norm_num,
        show (((2.2 : ℝ) ^ 3)) ^ (1 / 4 : ℝ) = (2.2 : ℝ) ^ (3 / 4 : ℝ) by
          rw [← Real.rpow_natCast (2.2 : ℝ) 3, ← Real.rpow_mul (by norm_num)]; norm_num] at h2
  have h34 : (2.2 : ℝ) ^ (-(3 / 4) : ℝ) ≤ 1 / 1.8 := by
    have hpos : (0 : ℝ) < (2.2 : ℝ) ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
    calc (2.2 : ℝ) ^ (-(3 / 4) : ℝ) = ((2.2 : ℝ) ^ (3 / 4 : ℝ))⁻¹ :=
          Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2.2) (3 / 4)
      _ ≤ (1.8 : ℝ)⁻¹ := (inv_le_inv₀ hpos (by norm_num)).mpr hs22
      _ = 1 / 1.8 := by norm_num
  have hA : (2704 : ℝ) * 770 / 2.2 ≤ 946400 := by norm_num
  have hB : (5408 : ℝ) * 21.1 * 7 / 2.2 ≤ 363074 := by norm_num
  have hC : (752 : ℝ) * 21.1 * (2.2 : ℝ) ^ (-(3 / 4) : ℝ) ≤ 752 * 21.1 * (1 / 1.8) :=
    mul_le_mul_of_nonneg_left h34 (by norm_num)
  have hsum : (2704 : ℝ) * 770 / 2.2 + 5408 * 21.1 * 7 / 2.2
        + 752 * 21.1 * (2.2 : ℝ) ^ (-(3 / 4) : ℝ)
      ≤ 946400 + 363074 + 752 * 21.1 * (1 / 1.8) := by linarith only [hA, hB, hC]
  calc (1 / 36) * (1 + 7) * ((2704 : ℝ) * 770 / 2.2 + 5408 * 21.1 * 7 / 2.2
        + 752 * 21.1 * (2.2 : ℝ) ^ (-(3 / 4) : ℝ))
      ≤ (1 / 36) * (1 + 7) * (946400 + 363074 + 752 * 21.1 * (1 / 1.8)) :=
        mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ ≤ 292954 := by norm_num

/-- `22/15 ≤ -effE 2.2 4`。 -/
private lemma neg_effE_2_2_ge : (22 / 15 : ℝ) ≤ -(effE 2.2 4) := by
  rw [effE]
  push_cast
  have hA : (22 / 15 : ℝ) ≤ -(4 + 2 / 3 - 2 * effS 2.2) := by linarith only [effS_2_2_ge]
  have hB : (22 / 15 : ℝ) ≤ -(3 / 2 - 3 * effS 2.2 / 2) := by linarith only [effS_2_2_ge]
  rcases le_total (4 + 2 / 3 - 2 * effS 2.2) (3 / 2 - 3 * effS 2.2 / 2) with h | h
  · rw [max_eq_right h]; exact hB
  · rw [max_eq_left h]; exact hA

/-- `18749056^(15/22) ≤ 92000`。 -/
private lemma rpow_num_22 : ((18749056 : ℝ)) ^ ((15 : ℝ) / 22) ≤ 92000 := by
  have hstep : ((18749056 : ℝ) ^ ((15 : ℝ) / 22)) ^ 22 = (18749056 : ℝ) ^ 15 := by
    rw [← Real.rpow_natCast ((18749056 : ℝ) ^ ((15 : ℝ) / 22)) 22,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 18749056)]
    norm_num
  have hkey : ((18749056 : ℝ) ^ 15) ≤ (92000 : ℝ) ^ 22 := by norm_num
  refine (pow_le_pow_iff_left₀ (by positivity) (by norm_num) (by norm_num : (22 : ℕ) ≠ 0)).mp ?_
  rw [hstep]
  exact hkey

/-- `effQmin 2.2 ≤ 92000`。 -/
private lemma effQmin_2_2_le : effQmin 2.2 ≤ 92000 := by
  rw [effQmin]
  refine max_le (by norm_num) (max_le ?_ ?_)
  · exact le_trans (le_of_lt Real.exp_one_lt_three) (by norm_num)
  · have hbase : 20 * Real.exp 1 * (2.2 : ℝ) ^ (-(1 / 4) : ℝ) ≤ 60 := by
      have he : Real.exp 1 ≤ 3 := le_of_lt Real.exp_one_lt_three
      have h23 : (2.2 : ℝ) ^ (-(1 / 4) : ℝ) ≤ 1 := by
        rw [Real.rpow_neg (x := (2.2 : ℝ)) (by norm_num : (0 : ℝ) ≤ 2.2), one_div]
        exact inv_le_one_of_one_le₀ (Real.one_le_rpow (by norm_num) (by norm_num))
      have he0 : (0 : ℝ) ≤ Real.exp 1 := (Real.exp_pos 1).le
      have h230 : (0 : ℝ) ≤ (2.2 : ℝ) ^ (-(1 / 4) : ℝ) := Real.rpow_nonneg (by norm_num) _
      nlinarith only [he, h23, he0, h230]
    have hden : (4 : ℝ) / 11 ≤ effS 2.2 / 2 - 7 / 6 := by linarith only [effS_2_2_ge]
    have hexp : 1 / (effS 2.2 / 2 - 7 / 6) ≤ (11 : ℝ) / 4 := by
      refine le_trans (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4 / 11) hden) ?_
      norm_num
    have hstep : (20 * Real.exp 1 * (2.2 : ℝ) ^ (-(1 / 4) : ℝ)) ^ (1 / (effS 2.2 / 2 - 7 / 6))
        ≤ (60 : ℝ) ^ ((11 : ℝ) / 4) := by
      refine le_trans (Real.rpow_le_rpow (by positivity) hbase (by positivity)) ?_
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    refine le_trans hstep ?_
    have hstep2 : ((60 : ℝ) ^ ((11 : ℝ) / 4)) ^ 4 = (60 : ℝ) ^ 11 := by
      rw [← Real.rpow_natCast ((60 : ℝ) ^ ((11 : ℝ) / 4)) 4,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 60)]
      norm_num
    have hkey : ((60 : ℝ) ^ 11) ≤ (92000 : ℝ) ^ 4 := by norm_num
    refine (pow_le_pow_iff_left₀ (by positivity) (by norm_num) (by norm_num : (4 : ℕ) ≠ 0)).mp ?_
    rw [hstep2]
    exact hkey

/-- `effQ0 7 770 K₀ 2.2 4 ≤ 92000`。 -/
private lemma effQ0_2_2_le : effQ0 7 770 K₀ 2.2 4 ≤ 92000 := by
  rw [effQ0]
  refine max_le (by norm_num) ?_
  have hB : (64 : ℝ) * effK1 7 770 K₀ 2.2 ≤ 18749056 := by
    have h := mul_le_mul_of_nonneg_left effK1_2_2_le (by norm_num : (0 : ℝ) ≤ 64)
    linarith only [h]
  have hP : 1 / (-(effE 2.2 4)) ≤ (15 : ℝ) / 22 := by
    have h0 : (0 : ℝ) < -(effE 2.2 4) := lt_of_lt_of_le (by norm_num) neg_effE_2_2_ge
    refine le_trans (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 22 / 15) neg_effE_2_2_ge) ?_
    norm_num
  have hb0 : (0 : ℝ) ≤ 64 * effK1 7 770 K₀ 2.2 := by
    have hp := effK1_pos (Cd1 := 7) (Cd2 := 770) (K := K₀) (a := 2.2)
      (by norm_num) (by norm_num) K₀_pos (by norm_num)
    linarith only [hp]
  have h0 : (0 : ℝ) < -(effE 2.2 4) := lt_of_lt_of_le (by norm_num) neg_effE_2_2_ge
  calc (64 * effK1 7 770 K₀ 2.2) ^ (1 / (-(effE 2.2 4)))
      ≤ (18749056 : ℝ) ^ (1 / (-(effE 2.2 4))) :=
        Real.rpow_le_rpow hb0 hB (div_pos one_pos h0).le
    _ ≤ (18749056 : ℝ) ^ ((15 : ℝ) / 22) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hP
    _ ≤ 92000 := rpow_num_22

/-- `effN0End K₀ 2.2 ≤ 46000`。 -/
private lemma effN0End_2_2_le : effN0End K₀ 2.2 ≤ 46000 := by
  rw [effN0End]
  refine max_le (max_le ?_ ?_) ?_
  · exact Nat.ceil_le.mpr (by norm_num)
  · refine Nat.ceil_le.mpr ?_
    refine le_trans (div_le_div_of_nonneg_right effQ0_2_2_le (by norm_num : (0 : ℝ) ≤ 2)) ?_
    norm_num
  · refine Nat.ceil_le.mpr ?_
    refine le_trans (div_le_div_of_nonneg_right effQmin_2_2_le (by norm_num : (0 : ℝ) ≤ 2)) ?_
    norm_num

/-- **数值版**：`a = 2.2`，`N₀ = 46000`（`effN0End K₀ 2.2 = 45006` 的真值过于贴合，取 46000）。 -/
theorem endgame_bound_2_2_num :
    ∀ N ≥ 46000, ∀ {L : ℕ} {α θ : Fin L → ℝ}, Admissible N Real.pi L α θ →
      4 * ((N : ℝ) + 1)
        * (1 - 2.2 * (Real.log (2 * (N : ℝ) + 2) / (2 * (N : ℝ) + 2)) ^ (2 / 3 : ℝ))
        ≤ cost θ :=
  fun N hN => endgame_bound_2_2 N (le_trans effN0End_2_2_le hN)


/-- `3.25833 ≤ effS 2.3`。 -/
private lemma effS_2_3_ge : (3.25834 : ℝ) ≤ effS 2.3 := by
  rw [effS]
  have hsqrt : (1.514 : ℝ) ≤ Real.sqrt 2.3 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have h : (3.4704 : ℝ) ≤ (2.3 : ℝ) ^ (3 / 2 : ℝ) := by
    have h3 : (2.3 : ℝ) ^ (3 / 2 : ℝ) = 2.3 * Real.sqrt 2.3 := by
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (by norm_num),
        Real.rpow_one, Real.sqrt_eq_rpow]
    rw [h3]
    nlinarith only [hsqrt]
  calc (3.25834 : ℝ) ≤ (47 / 50) * 3.4704 := by norm_num
    _ ≤ (47 / 50) * (2.3 : ℝ) ^ (3 / 2 : ℝ) := mul_le_mul_of_nonneg_left h (by norm_num)

/-- `effK1 7 770 K₀ 2.3 ≤ 280249`。 -/
private lemma effK1_2_3_le : effK1 7 770 K₀ 2.3 ≤ 280249 := by
  rw [effK1, K₀_eq]
  have hs23 : (1.85 : ℝ) ≤ (2.3 : ℝ) ^ (3 / 4 : ℝ) := by
    have h1 : ((1.85 : ℝ) ^ 4) ≤ ((2.3 : ℝ) ^ 3) := by norm_num
    have h2 := Real.rpow_le_rpow (by positivity) h1 (by norm_num : (0 : ℝ) ≤ 1 / 4)
    rwa [show (((1.85 : ℝ) ^ 4)) ^ (1 / 4 : ℝ) = 1.85 by
          rw [← Real.rpow_natCast (1.85 : ℝ) 4, ← Real.rpow_mul (by norm_num)]; norm_num,
        show (((2.3 : ℝ) ^ 3)) ^ (1 / 4 : ℝ) = (2.3 : ℝ) ^ (3 / 4 : ℝ) by
          rw [← Real.rpow_natCast (2.3 : ℝ) 3, ← Real.rpow_mul (by norm_num)]; norm_num] at h2
  have h34 : (2.3 : ℝ) ^ (-(3 / 4) : ℝ) ≤ 1 / 1.85 := by
    have hpos : (0 : ℝ) < (2.3 : ℝ) ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
    calc (2.3 : ℝ) ^ (-(3 / 4) : ℝ) = ((2.3 : ℝ) ^ (3 / 4 : ℝ))⁻¹ :=
          Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2.3) (3 / 4)
      _ ≤ (1.85 : ℝ)⁻¹ := (inv_le_inv₀ hpos (by norm_num)).mpr hs23
      _ = 1 / 1.85 := by norm_num
  have hA : (2704 : ℝ) * 770 / 2.3 ≤ 905253 := by norm_num
  have hB : (5408 : ℝ) * 21.1 * 7 / 2.3 ≤ 347288 := by norm_num
  have hC : (752 : ℝ) * 21.1 * (2.3 : ℝ) ^ (-(3 / 4) : ℝ) ≤ 752 * 21.1 * (1 / 1.85) :=
    mul_le_mul_of_nonneg_left h34 (by norm_num)
  have hsum : (2704 : ℝ) * 770 / 2.3 + 5408 * 21.1 * 7 / 2.3
        + 752 * 21.1 * (2.3 : ℝ) ^ (-(3 / 4) : ℝ)
      ≤ 905253 + 347288 + 752 * 21.1 * (1 / 1.85) := by linarith only [hA, hB, hC]
  calc (1 / 36) * (1 + 7) * ((2704 : ℝ) * 770 / 2.3 + 5408 * 21.1 * 7 / 2.3
        + 752 * 21.1 * (2.3 : ℝ) ^ (-(3 / 4) : ℝ))
      ≤ (1 / 36) * (1 + 7) * (905253 + 347288 + 752 * 21.1 * (1 / 1.85)) :=
        mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ ≤ 280249 := by norm_num

/-- `1.85 ≤ -effE 2.3 4`。 -/
private lemma neg_effE_2_3_ge : (1.85 : ℝ) ≤ -(effE 2.3 4) := by
  rw [effE]
  push_cast
  have hA : (1.85 : ℝ) ≤ -(4 + 2 / 3 - 2 * effS 2.3) := by linarith only [effS_2_3_ge]
  have hB : (1.85 : ℝ) ≤ -(3 / 2 - 3 * effS 2.3 / 2) := by linarith only [effS_2_3_ge]
  rcases le_total (4 + 2 / 3 - 2 * effS 2.3) (3 / 2 - 3 * effS 2.3 / 2) with h | h
  · rw [max_eq_right h]; exact hB
  · rw [max_eq_left h]; exact hA

/-- `17935936^(6/11) ≤ 10020`。 -/
private lemma rpow_num_23 : ((17935936 : ℝ)) ^ ((6 : ℝ) / 11) ≤ 10020 := by
  have hstep : ((17935936 : ℝ) ^ ((6 : ℝ) / 11)) ^ 11 = (17935936 : ℝ) ^ 6 := by
    rw [← Real.rpow_natCast ((17935936 : ℝ) ^ ((6 : ℝ) / 11)) 11,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 17935936)]
    norm_num
  have hkey : ((17935936 : ℝ) ^ 6) ≤ (10020 : ℝ) ^ 11 := by norm_num
  refine (pow_le_pow_iff_left₀ (by positivity) (by norm_num) (by norm_num : (11 : ℕ) ≠ 0)).mp ?_
  rw [hstep]
  exact hkey

/-- `effQmin 2.3 ≤ 10020`。 -/
private lemma effQmin_2_3_le : effQmin 2.3 ≤ 10020 := by
  rw [effQmin]
  refine max_le le_rfl (max_le ?_ ?_)
  · exact le_trans (le_of_lt Real.exp_one_lt_three) (by norm_num)
  · have hbase : 20 * Real.exp 1 * (2.3 : ℝ) ^ (-(1 / 4) : ℝ) ≤ 60 := by
      have he : Real.exp 1 ≤ 3 := le_of_lt Real.exp_one_lt_three
      have h23 : (2.3 : ℝ) ^ (-(1 / 4) : ℝ) ≤ 1 := by
        rw [Real.rpow_neg (by norm_num), one_div]
        exact inv_le_one_of_one_le₀ (Real.one_le_rpow (by norm_num) (by norm_num))
      have he0 : (0 : ℝ) ≤ Real.exp 1 := (Real.exp_pos 1).le
      have h230 : (0 : ℝ) ≤ (2.3 : ℝ) ^ (-(1 / 4) : ℝ) := Real.rpow_nonneg (by norm_num) _
      nlinarith only [he, h23, he0, h230]
    have hden : (5 : ℝ) / 11 ≤ effS 2.3 / 2 - 7 / 6 := by linarith only [effS_2_3_ge]
    have hexp : 1 / (effS 2.3 / 2 - 7 / 6) ≤ (11 : ℝ) / 5 := by
      refine le_trans (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 5 / 11) hden) ?_
      norm_num
    have hstep : (20 * Real.exp 1 * (2.3 : ℝ) ^ (-(1 / 4) : ℝ)) ^ (1 / (effS 2.3 / 2 - 7 / 6))
        ≤ (60 : ℝ) ^ ((11 : ℝ) / 5) := by
      refine le_trans (Real.rpow_le_rpow (by positivity) hbase (by positivity)) ?_
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    refine le_trans hstep ?_
    have hstep2 : ((60 : ℝ) ^ ((11 : ℝ) / 5)) ^ 5 = (60 : ℝ) ^ 11 := by
      rw [← Real.rpow_natCast ((60 : ℝ) ^ ((11 : ℝ) / 5)) 5,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 60)]
      norm_num
    have hkey : ((60 : ℝ) ^ 11) ≤ (10020 : ℝ) ^ 5 := by norm_num
    refine (pow_le_pow_iff_left₀ (by positivity) (by norm_num) (by norm_num : (5 : ℕ) ≠ 0)).mp ?_
    rw [hstep2]
    exact hkey

/-- `effQ0 7 770 K₀ 2.3 4 ≤ 10020`。 -/
private lemma effQ0_2_3_le : effQ0 7 770 K₀ 2.3 4 ≤ 10020 := by
  rw [effQ0]
  refine max_le (by norm_num) ?_
  have hB : (64 : ℝ) * effK1 7 770 K₀ 2.3 ≤ 17935936 := by
    have h := mul_le_mul_of_nonneg_left effK1_2_3_le (by norm_num : (0 : ℝ) ≤ 64)
    linarith only [h]
  have hP : 1 / (-(effE 2.3 4)) ≤ (6 : ℝ) / 11 := by
    have h0 : (0 : ℝ) < -(effE 2.3 4) := lt_of_lt_of_le (by norm_num) neg_effE_2_3_ge
    refine le_trans (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1.85) neg_effE_2_3_ge) ?_
    norm_num
  have hb0 : (0 : ℝ) ≤ 64 * effK1 7 770 K₀ 2.3 := by
    have hp := effK1_pos (Cd1 := 7) (Cd2 := 770) (K := K₀) (a := 2.3)
      (by norm_num) (by norm_num) K₀_pos (by norm_num)
    linarith only [hp]
  have h0 : (0 : ℝ) < -(effE 2.3 4) := lt_of_lt_of_le (by norm_num) neg_effE_2_3_ge
  calc (64 * effK1 7 770 K₀ 2.3) ^ (1 / (-(effE 2.3 4)))
      ≤ (17935936 : ℝ) ^ (1 / (-(effE 2.3 4))) :=
        Real.rpow_le_rpow hb0 hB (div_pos one_pos h0).le
    _ ≤ (17935936 : ℝ) ^ ((6 : ℝ) / 11) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hP
    _ ≤ 10020 := rpow_num_23

/-- `effN0End K₀ 2.3 ≤ 5010`。 -/
private lemma effN0End_2_3_le : effN0End K₀ 2.3 ≤ 5010 := by
  rw [effN0End]
  refine max_le (max_le ?_ ?_) ?_
  · exact Nat.ceil_le.mpr (by norm_num)
  · refine Nat.ceil_le.mpr ?_
    refine le_trans (div_le_div_of_nonneg_right effQ0_2_3_le (by norm_num : (0 : ℝ) ≤ 2)) ?_
    norm_num
  · refine Nat.ceil_le.mpr ?_
    refine le_trans (div_le_div_of_nonneg_right effQmin_2_3_le (by norm_num : (0 : ℝ) ≤ 2)) ?_
    norm_num

/-- **数值版**：`a = 2.3`，`N₀ = 5010`。 -/
theorem endgame_bound_2_3_num :
    ∀ N ≥ 5010, ∀ {L : ℕ} {α θ : Fin L → ℝ}, Admissible N Real.pi L α θ →
      4 * ((N : ℝ) + 1)
        * (1 - 2.3 * (Real.log (2 * (N : ℝ) + 2) / (2 * (N : ℝ) + 2)) ^ (2 / 3 : ℝ))
        ≤ cost θ :=
  fun N hN => endgame_bound_2_3 N (le_trans effN0End_2_3_le hN)

end RobustZ
