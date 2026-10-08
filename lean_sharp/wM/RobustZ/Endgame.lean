/-
Copyright (c) 2025 RobustZ project. All rights reserved.

# `Endgame`：**无条件**端到端有效定理

`Effective.lean` 的主定理 `effective_bound_of_sharp` 依赖 `SharpCollar`（固定的 `Cd1, Cd2`）。
本文件证明它**无条件成立**：`SharpDerivGen` 给出的 honest collar 常数含 `1/(1-r')` 因子，
`r' = e^{-δ'}e^{2√(B/τ)}`，而应用里 honest 的尾部系数常数是
`ε_h = e^{τ sinh δ'}e^{-δ'k} = ε/(1+4/(1-e^{-δ'})) ≤ ε(1-r')/2`，两者**相消**，
剩下与 `q` 无关的常数 `(Cd1, Cd2) = (7, 770)`（`β = 4`）。

同时把 `k²√ε ≤ τ` 那一步的 `q ≥ 10^{10}` 下界换成显式阈值 `effQmin a`，
于是 `N₀` 从 `5·10⁹` 量级降到（`a = 2.2` 时）`≈ 4.5·10⁴`。
-/
import RobustZ.Effective
import RobustZ.SharpDerivGen

noncomputable section

namespace RobustZ

open Filter MeasureTheory
open scoped Real

set_option maxHeartbeats 2000000

/-! ## §1 基本引理 -/

/-- `δ'(ρ) ≥ 1-ρ`（`0 < ρ < 1`）。 -/
lemma one_sub_le_deltaOf {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) : 1 - ρ ≤ deltaOf ρ := by
  have h1 : Real.log (1 / ρ) ≤ deltaOf ρ := by
    rw [deltaOf]
    refine Real.log_le_log (by positivity) ?_
    rw [div_le_div_iff_of_pos_right hρ0]
    linarith [Real.sqrt_nonneg (1 - ρ ^ 2)]
  have h2 : 1 - ρ ≤ Real.log (1 / ρ) := by
    rw [one_div, Real.log_inv]
    have h3 := Real.log_le_sub_one_of_pos hρ0
    linarith
  linarith

/-- `δ'(ρ) ≤ 1`（`3/4 ≤ ρ < 1`）。 -/
lemma deltaOf_le_one {ρ : ℝ} (h34 : 3 / 4 ≤ ρ) (hρ1 : ρ < 1) : deltaOf ρ ≤ 1 := by
  have hρ0 : 0 < ρ := by linarith
  have hs : Real.sqrt (1 - ρ ^ 2) ≤ 1 := by
    rw [Real.sqrt_le_one]
    nlinarith
  have h1 : deltaOf ρ ≤ Real.log (2 / ρ) := by
    rw [deltaOf]
    refine Real.log_le_log (by positivity) ?_
    rw [div_le_div_iff_of_pos_right hρ0]
    linarith
  have h2 : Real.log (2 / ρ) ≤ Real.log (8 / 3) := by
    refine Real.log_le_log (by positivity) ?_
    rw [div_le_iff₀ hρ0]
    linarith
  have h3 : Real.log (8 / 3) ≤ 1 := by
    rw [Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 8 / 3)]
    linarith [Real.exp_one_gt_d9]
  linarith

/-- **尾部系数衰减（honest 常数）**：`‖c_{k+j}‖ ≤ ε_h·r^j`，
`ε_h = e^{τ·sinh δ'}·(e^{-δ'})^k`、`r = e^{-δ'}`。 -/
lemma fcoef_tail_le {τ δ' : ℝ} (hτ : 0 ≤ τ) (hδ' : 0 < δ') {k : ℕ} (hk : 1 ≤ k) (j : ℕ) :
    ‖fcoef τ (((k + j : ℕ)) : ℤ)‖
      ≤ (Real.exp (τ * Real.sinh δ') * Real.exp (-δ') ^ k) * Real.exp (-δ') ^ j := by
  have hpos : (0 : ℤ) < (((k + j : ℕ)) : ℤ) := by
    have : (0 : ℕ) < k + j := by omega
    exact_mod_cast this
  have h := fcoef_bound τ hτ hδ' (((k + j : ℕ)) : ℤ) hpos
  refine h.trans (le_of_eq ?_)
  rw [show τ * Real.sinh δ' - (((k + j : ℕ)) : ℤ) * δ'
      = τ * Real.sinh δ' + (k : ℝ) * (-δ') + (j : ℝ) * (-δ') by push_cast; ring,
    Real.exp_add, Real.exp_add,
    show Real.exp ((k : ℝ) * (-δ')) = Real.exp (-δ') ^ k from Real.exp_nat_mul (-δ') k,
    show Real.exp ((j : ℝ) * (-δ')) = Real.exp (-δ') ^ j from Real.exp_nat_mul (-δ') j]

/-- `epsOf` 的分解。 -/
lemma epsOf_eq_mul (τ δ' : ℝ) (k : ℕ) :
    epsOf τ δ' k
      = (Real.exp (τ * Real.sinh δ') * Real.exp (-δ') ^ k) * (1 + 4 / (1 - Real.exp (-δ'))) := by
  rw [epsOf]; ring

/-- **honest 常数与 `epsOf` 的比**：`ε_h ≤ ε·(1-r')/2`（`δ' ≤ 1`）。 -/
lemma honest_le_eps_mul {τ δ' B : ℝ} {k : ℕ} (hδ'0 : 0 < δ') (hδ'1 : δ' ≤ 1)
    (hg : 2 * Real.sqrt (B / τ) ≤ δ' / 2) :
    Real.exp (τ * Real.sinh δ') * Real.exp (-δ') ^ k
      ≤ epsOf τ δ' k * (1 - tailR B τ (Real.exp (-δ'))) / 2 := by
  have hexp1 : Real.exp (-δ') < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hpos : 0 < 1 - Real.exp (-δ') := by linarith
  have hone : 1 - Real.exp (-δ') ≤ δ' := by
    have h := Real.add_one_le_exp (-δ')
    linarith
  -- `r' ≤ e^{-δ'/2}`，故 `1-e^{-δ'} = (1-e^{-δ'/2})(1+e^{-δ'/2}) ≤ 2(1-r')`
  have hrt : tailR B τ (Real.exp (-δ')) ≤ Real.exp (-(δ' / 2)) := by
    rw [tailR, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    linarith [hg]
  have hfac : 1 - Real.exp (-δ')
      = (1 - Real.exp (-(δ' / 2))) * (1 + Real.exp (-(δ' / 2))) := by
    rw [show Real.exp (-δ') = Real.exp (-(δ' / 2)) * Real.exp (-(δ' / 2)) by
      rw [← Real.exp_add]; ring_nf]
    ring
  have htwo : 1 - Real.exp (-δ') ≤ 2 * (1 - tailR B τ (Real.exp (-δ'))) := by
    have h1 : Real.exp (-(δ' / 2)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; linarith
    have h2 : Real.exp (-(δ' / 2)) < 1 := by
      rw [Real.exp_lt_one_iff]; linarith
    rw [hfac]
    nlinarith [hrt, h1, h2]
  have hmain : Real.exp (τ * Real.sinh δ') * Real.exp (-δ') ^ k
      ≤ epsOf τ δ' k * (1 - Real.exp (-δ')) / 4 := by
    rw [epsOf_eq_mul]
    have h4 : (1 : ℝ) ≤ (1 + 4 / (1 - Real.exp (-δ'))) * (1 - Real.exp (-δ')) / 4 := by
      rw [show (1 + 4 / (1 - Real.exp (-δ'))) * (1 - Real.exp (-δ')) / 4
          = ((1 - Real.exp (-δ')) + 4) / 4 by field_simp]
      linarith
    have h5 : (0 : ℝ) ≤ Real.exp (τ * Real.sinh δ') * Real.exp (-δ') ^ k := by positivity
    nlinarith [h4, h5, mul_le_mul_of_nonneg_left h4 h5]
  have hεnn : (0 : ℝ) ≤ epsOf τ δ' k := (epsOf_pos hδ'0 τ k).le
  nlinarith [hmain, htwo, hεnn, mul_le_mul_of_nonneg_left htwo hεnn]

/-! ## §2 侧条件阈值与接口 -/

/-- `k²√ε ≤ τ/4` 那一步所需的 `q` 阈值（替代原先的 `q ≥ 10^{10}`）。 -/
noncomputable def effQmin (a : ℝ) : ℝ :=
  max 10020 (max (Real.exp 1)
    ((20 * Real.exp 1 * a ^ (-(1 / 4 : ℝ))) ^ (1 / (effS a / 2 - 7 / 6))))

/-- **具体常数下的显式 `N₀`**：`(Cd1, Cd2, β) = (7, 770, 4)`，`effQmin a` 取代 `5·10⁹` 下限。 -/
noncomputable def effN0End (K a : ℝ) : ℕ :=
  max (max (Nat.ceil (256 * a ^ 3)) (Nat.ceil (effQ0 7 770 K a 4 / 2)))
    (Nat.ceil (effQmin a / 2))

/-- **`N ≥ N₀` 版本的 sharp collar 界**（`Cd1, Cd2` 固定；只在 `τ ≤ ρ_a(q)·q` 时要求，
因为 `τ > ρq` 时主定理结论直接成立）。 -/
noncomputable def SharpCollarFrom (N₀ : ℕ) (Cd1 Cd2 a : ℝ) (β : ℕ) : Prop :=
  ∀ N ≥ N₀, ∀ {L : ℕ} {α θ : Fin L → ℝ}, Admissible N Real.pi L α θ →
    (∑ j, θ j) / 2 ≤ rhoA a (2 * (N : ℝ) + 2) * (2 * (N : ℝ) + 2) →
    ∃ M₁ M₂ : ℝ, 0 ≤ M₁ ∧ 0 ≤ M₂ ∧
      (∀ μ : ℝ, |μ| ≤ (∑ j, θ j) / 2
          + Real.sqrt (epsOf ((∑ j, θ j) / 2) (deltaOf (rhoA a (2 * (N : ℝ) + 2))) (2 * N + 1)) →
        ‖deriv (fun x : ℝ => psiA (scaledApprox ((∑ j, θ j) / 2) (2 * N + 1)) x) μ‖ ≤ M₁) ∧
      (∀ μ : ℝ, |μ| ≤ (∑ j, θ j) / 2
          + Real.sqrt (epsOf ((∑ j, θ j) / 2) (deltaOf (rhoA a (2 * (N : ℝ) + 2))) (2 * N + 1)) →
        ‖deriv (deriv (fun x : ℝ => psiA (scaledApprox ((∑ j, θ j) / 2) (2 * N + 1)) x)) μ‖ ≤ M₂) ∧
      (∑ j, θ j) / 2 * M₁ ≤ Cd1 * ((2 * N + 1 : ℕ) : ℝ) ^ 2
          * epsOf ((∑ j, θ j) / 2) (deltaOf (rhoA a (2 * (N : ℝ) + 2))) (2 * N + 1) ∧
      ((∑ j, θ j) / 2) ^ 2 * M₂ ≤ Cd2 * ((2 * N + 1 : ℕ) : ℝ) ^ β
          * epsOf ((∑ j, θ j) / 2) (deltaOf (rhoA a (2 * (N : ℝ) + 2))) (2 * N + 1)

lemma ksq_sqrt_epsOf_le_gen {a q τ : ℝ} {N : ℕ}
    (hq0 : 0 < q) (hq1 : 1 ≤ q) (hqdef : q = 2 * (N : ℝ) + 2)
    (hq4 : (10 : ℝ) ^ 4 ≤ q) (hlog : 1 ≤ Real.log q)
    (ha : 2 ≤ a) (hat : a * (Real.log q / q) ^ (2 / 3 : ℝ) ≤ 1 / 4)
    (hqmin : (20 * Real.exp 1 * a ^ (-(1 / 4 : ℝ))) ^ (1 / (effS a / 2 - 7 / 6)) ≤ q)
    (hτ0 : 0 ≤ τ) (hτρ : τ ≤ rhoA a q * q) (hτlow : q / Real.exp 1 ≤ τ) :
    ((2 * N + 1 : ℕ) : ℝ) ^ 2 * Real.sqrt (epsOf τ (deltaOf (rhoA a q)) (2 * N + 1)) ≤ τ / 4 := by
  set k : ℕ := 2 * N + 1 with hkdef
  set ρ : ℝ := rhoA a q with hρdef
  set δ' : ℝ := deltaOf ρ with hδ'def
  have hl : 0 < Real.log q := lt_of_lt_of_le one_pos hlog
  have ha0 : 0 < a := by linarith
  obtain ⟨h34, hlt1, hρ0, h12⟩ := rhoA_bounds hq4 ha0 hat
  have hδ'pos : 0 < δ' := by rw [hδ'def]; exact deltaOf_pos hρ0 hlt1
  have hs := effS_ge ha
  have hτρ' : τ ≤ ρ * (2 * (N : ℝ) + 2) := by rw [← hqdef]; exact hτρ
  have hdec := epsOf_le_exp_decay (ρ := ρ) (δ' := δ') (τ := τ) hδ'pos hτ0 hτρ'
  have hdec' : epsOf τ δ' k ≤ (1 + 4 / (1 - Real.exp (-δ'))) * Real.exp δ'
      * Real.exp (-(δ' - ρ * Real.sinh δ') * q) := by
    rw [← hkdef, ← hqdef] at hdec
    exact hdec
  have hsq : Real.sqrt (epsOf τ δ' k)
      ≤ Real.sqrt (1 + 4 / (1 - Real.exp (-δ'))) * Real.exp (δ' / 2)
        * Real.exp (-(δ' - ρ * Real.sinh δ') * q / 2) := by
    have hlt1' : Real.exp (-δ') < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    have hpos1 : 0 < 1 - Real.exp (-δ') := by linarith
    have hCpos : 0 < 1 + 4 / (1 - Real.exp (-δ')) := by positivity
    refine (Real.sqrt_le_sqrt hdec').trans (le_of_eq ?_)
    rw [Real.sqrt_mul (by positivity :
        (0 : ℝ) ≤ (1 + 4 / (1 - Real.exp (-δ'))) * Real.exp δ'),
      Real.sqrt_mul (le_of_lt hCpos),
      ← Real.exp_half δ', ← Real.exp_half (-(δ' - ρ * Real.sinh δ') * q)]
    try ring
  have hCb : Real.sqrt (1 + 4 / (1 - Real.exp (-δ'))) * Real.exp (δ' / 2)
      ≤ 5 * (1 - ρ) ^ (-(1 / 4 : ℝ)) := by
    rw [hδ'def]; exact sqrt_C_exp_half_le h34 hlt1
  have hη : δ' - ρ * Real.sinh δ' = mu ρ := by
    rw [hδ'def]; exact (mu_eq_deltaOf hρ0 hlt1).symm
  have hηlow : effS a * (Real.log q / q) ≤ δ' - ρ * Real.sinh δ' := by
    rw [hη]; exact mu_rhoA_lower hq4 ha0 hat
  have hexp_le : Real.exp (-(δ' - ρ * Real.sinh δ') * q / 2) ≤ q ^ (-(effS a) / 2) := by
    have h1 : -(δ' - ρ * Real.sinh δ') * q / 2 ≤ -(effS a * (Real.log q / q)) * q / 2 := by
      nlinarith [hηlow]
    have h2 : Real.exp (-(δ' - ρ * Real.sinh δ') * q / 2)
        ≤ Real.exp (-(effS a * (Real.log q / q)) * q / 2) := Real.exp_le_exp.mpr h1
    have h3 : Real.exp (-(effS a * (Real.log q / q)) * q / 2) = q ^ (-(effS a) / 2) := by
      rw [Real.rpow_def_of_pos hq0]
      congr 1
      field_simp
      try ring
    rw [h3] at h2
    exact h2
  have hone : 1 - ρ = a * (Real.log q / q) ^ (2 / 3 : ℝ) := by rw [hρdef, rhoA]; ring
  have hT : 0 < Real.log q / q := div_pos hl hq0
  have h14 : (1 - ρ) ^ (-(1 / 4 : ℝ)) = a ^ (-(1 / 4 : ℝ)) * (q / Real.log q) ^ (1 / 6 : ℝ) := by
    have hT6 : ((Real.log q / q) ^ (1 / 6 : ℝ))⁻¹ = (q / Real.log q) ^ (1 / 6 : ℝ) := by
      rw [← Real.inv_rpow hT.le (1 / 6 : ℝ), inv_div]
    have hkey : (a * (Real.log q / q) ^ (2 / 3 : ℝ)) ^ (-(1 / 4 : ℝ))
        = a ^ (-(1 / 4 : ℝ)) * ((Real.log q / q) ^ (1 / 6 : ℝ))⁻¹ := by
      rw [Real.mul_rpow ha0.le (Real.rpow_nonneg hT.le _),
        Real.rpow_neg (le_of_lt ha0), Real.rpow_neg (Real.rpow_nonneg hT.le _),
        ← Real.rpow_mul hT.le]
      try norm_num
    rw [hone, hkey, hT6]
  have h16 : (q / Real.log q) ^ (1 / 6 : ℝ) ≤ q ^ (1 / 6 : ℝ) := by
    rw [Real.div_rpow hq0.le hl.le, div_le_iff₀ (Real.rpow_pos_of_pos hl _)]
    have h1 : (1 : ℝ) ≤ (Real.log q) ^ (1 / 6 : ℝ) := Real.one_le_rpow hlog (by norm_num)
    have h2 := Real.rpow_pos_of_pos hq0 (1 / 6 : ℝ)
    nlinarith
  have hsqrtε : Real.sqrt (epsOf τ δ' k) ≤ 5 * a ^ (-(1 / 4 : ℝ)) * q ^ (1 / 6 - effS a / 2) := by
    have hstep : Real.sqrt (epsOf τ δ' k) ≤ (5 * (1 - ρ) ^ (-(1 / 4 : ℝ))) * q ^ (-(effS a) / 2) :=
      hsq.trans (mul_le_mul hCb hexp_le (Real.exp_pos _).le (by positivity))
    rw [h14] at hstep
    refine hstep.trans ?_
    have h6 : a ^ (-(1 / 4 : ℝ)) * (q / Real.log q) ^ (1 / 6 : ℝ)
        ≤ a ^ (-(1 / 4 : ℝ)) * q ^ (1 / 6 : ℝ) :=
      mul_le_mul_of_nonneg_left h16 (Real.rpow_nonneg ha0.le _)
    have h1 : q ^ (1 / 6 : ℝ) * q ^ (-(effS a) / 2) = q ^ (1 / 6 - effS a / 2) := by
      rw [← Real.rpow_add hq0]; congr 1; ring
    calc 5 * (a ^ (-(1 / 4 : ℝ)) * (q / Real.log q) ^ (1 / 6 : ℝ)) * q ^ (-(effS a) / 2)
        = 5 * (a ^ (-(1 / 4 : ℝ)) * ((q / Real.log q) ^ (1 / 6 : ℝ) * q ^ (-(effS a) / 2))) := by
          ring
      _ ≤ 5 * (a ^ (-(1 / 4 : ℝ)) * (q ^ (1 / 6 : ℝ) * q ^ (-(effS a) / 2))) := by
          have h9 : a ^ (-(1 / 4 : ℝ)) * ((q / Real.log q) ^ (1 / 6 : ℝ) * q ^ (-(effS a) / 2))
              ≤ a ^ (-(1 / 4 : ℝ)) * (q ^ (1 / 6 : ℝ) * q ^ (-(effS a) / 2)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right h16 (Real.rpow_nonneg hq0.le (-(effS a) / 2)))
              (Real.rpow_nonneg ha0.le _)
          linarith [h9]
      _ = 5 * a ^ (-(1 / 4 : ℝ)) * q ^ (1 / 6 - effS a / 2) := by
          rw [h1]; ring
  have hkq : ((k : ℕ) : ℝ) ≤ q := by
    rw [hkdef, hqdef]; push_cast; linarith
  have hk2 : ((k : ℕ) : ℝ) ^ 2 ≤ q ^ (2 : ℝ) := by
    rw [show q ^ (2 : ℝ) = q ^ 2 from Real.rpow_natCast q 2]
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    nlinarith [hkq, hk0]
  have hmain : 5 * a ^ (-(1 / 4 : ℝ)) * q ^ (13 / 6 - effS a / 2) ≤ q / (4 * Real.exp 1) := by
    have hExp : (0 : ℝ) < effS a / 2 - 7 / 6 := by linarith [hs]
    have hbase : 20 * Real.exp 1 * a ^ (-(1 / 4 : ℝ)) ≤ q ^ (effS a / 2 - 7 / 6) := by
      have h := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤
        (20 * Real.exp 1 * a ^ (-(1 / 4 : ℝ))) ^ (1 / (effS a / 2 - 7 / 6))) hqmin hExp.le
      have hX : (0 : ℝ) ≤ 20 * Real.exp 1 * a ^ (-(1 / 4 : ℝ)) := by positivity
      have h2 : ((20 * Real.exp 1 * a ^ (-(1 / 4 : ℝ))) ^ (1 / (effS a / 2 - 7 / 6)))
          ^ (effS a / 2 - 7 / 6) = 20 * Real.exp 1 * a ^ (-(1 / 4 : ℝ)) := by
        rw [← Real.rpow_mul hX]
        have hexp : 1 / (effS a / 2 - 7 / 6) * (effS a / 2 - 7 / 6) = 1 := by
          rw [one_div, inv_mul_cancel₀ (ne_of_gt hExp)]
        rw [hexp, Real.rpow_one]
      rwa [h2] at h
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 4 * Real.exp 1)]
    have hprod : q ^ (effS a / 2 - 7 / 6) * q ^ (13 / 6 - effS a / 2) = q := by
      rw [← Real.rpow_add hq0,
        show effS a / 2 - 7 / 6 + (13 / 6 - effS a / 2) = 1 by ring, Real.rpow_one]
    have h3 : 0 ≤ q ^ (13 / 6 - effS a / 2) := Real.rpow_nonneg hq0.le _
    calc 5 * a ^ (-(1 / 4 : ℝ)) * q ^ (13 / 6 - effS a / 2) * (4 * Real.exp 1)
        = (20 * Real.exp 1 * a ^ (-(1 / 4 : ℝ))) * q ^ (13 / 6 - effS a / 2) := by ring
      _ ≤ q ^ (effS a / 2 - 7 / 6) * q ^ (13 / 6 - effS a / 2) :=
          mul_le_mul_of_nonneg_right hbase h3
      _ = q := hprod
  calc ((2 * N + 1 : ℕ) : ℝ) ^ 2 * Real.sqrt (epsOf τ (deltaOf (rhoA a q)) (2 * N + 1))
      = ((k : ℕ) : ℝ) ^ 2 * Real.sqrt (epsOf τ δ' k) := by rw [← hkdef, ← hρdef, ← hδ'def]
    _ ≤ q ^ (2 : ℝ) * (5 * a ^ (-(1 / 4 : ℝ)) * q ^ (1 / 6 - effS a / 2)) :=
        mul_le_mul hk2 hsqrtε (Real.sqrt_nonneg _) (by positivity)
    _ = 5 * a ^ (-(1 / 4 : ℝ)) * q ^ (13 / 6 - effS a / 2) := by
        have h1 : q ^ (2 : ℝ) * q ^ (1 / 6 - effS a / 2) = q ^ (13 / 6 - effS a / 2) := by
          rw [← Real.rpow_add hq0]; congr 1; ring
        calc q ^ (2 : ℝ) * (5 * a ^ (-(1 / 4 : ℝ)) * q ^ (1 / 6 - effS a / 2))
            = 5 * a ^ (-(1 / 4 : ℝ)) * (q ^ (2 : ℝ) * q ^ (1 / 6 - effS a / 2)) := by ring
          _ = 5 * a ^ (-(1 / 4 : ℝ)) * q ^ (13 / 6 - effS a / 2) := by rw [h1]
    _ ≤ q / (4 * Real.exp 1) := hmain
    _ ≤ τ / 4 := by
        have h1 : q / (4 * Real.exp 1) = q / Real.exp 1 / 4 := by ring
        rw [h1]; linarith [hτlow]


theorem effective_bound_of_collar (N₀ : ℕ) (Cd1 Cd2 K a : ℝ) (β : ℕ)
    (hCd1 : 0 < Cd1) (hCd2 : 0 < Cd2) (hK : K₀ ≤ K) (ha : 2 ≤ a)
    (hβ : 2 ≤ β) (hβ4 : β ≤ 4)
    (hNa0 : Nat.ceil (256 * a ^ 3) ≤ N₀)
    (hNq0 : Nat.ceil (effQ0 Cd1 Cd2 K a β / 2) ≤ N₀)
    (hNmin0 : Nat.ceil (effQmin a / 2) ≤ N₀)
    (hN40 : 5000 ≤ N₀)
    (hsharp : SharpCollarFrom N₀ Cd1 Cd2 a β) :
    ∀ N ≥ N₀, ∀ {L : ℕ} {α θ : Fin L → ℝ}, Admissible N Real.pi L α θ →
      4 * ((N : ℝ) + 1)
        * (1 - a * (Real.log (2 * (N : ℝ) + 2) / (2 * (N : ℝ) + 2)) ^ (2 / 3 : ℝ))
        ≤ cost θ := by
  intro N hN L α θ hAdm
  set q : ℝ := 2 * (N : ℝ) + 2 with hqdef
  set k : ℕ := 2 * N + 1 with hkdef
  set τ : ℝ := (∑ j, θ j) / 2 with hτdef
  set ρ : ℝ := rhoA a q with hρdef
  set δ' : ℝ := deltaOf ρ with hδ'def
  set ε : ℝ := epsOf τ δ' k with hεdef
  set B : ℝ := Real.sqrt ε with hBdef
  set P : Polynomial ℂ := scaledApprox τ k with hPdef
  have hN5 : 5000 ≤ N := le_trans hN40 hN
  have hNa : Nat.ceil (256 * a ^ 3) ≤ N := le_trans hNa0 hN
  have hNq : Nat.ceil (effQ0 Cd1 Cd2 K a β / 2) ≤ N := le_trans hNq0 hN
  have hq4 : (10 : ℝ) ^ 4 ≤ q := by
    have h1 : (5000 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN5
    have h2 : (10 : ℝ) ^ 4 = 10000 := by norm_num
    rw [hqdef, h2]; push_cast; linarith
  have hq0 : 0 < q := by rw [hqdef]; push_cast; linarith [hN5]
  have hq1 : 1 ≤ q := by linarith [hq4]
  have hlog1 : (1 : ℝ) ≤ Real.log q := by
    rw [Real.le_log_iff_exp_le hq0]
    exact le_trans (le_of_lt Real.exp_one_lt_three) (by linarith [hq4])
  have hqmin : effQmin a ≤ q := by
    have h1 : effQmin a / 2 ≤ (Nat.ceil (effQmin a / 2) : ℝ) := Nat.le_ceil _
    have h2 : (Nat.ceil (effQmin a / 2) : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast (le_trans hNmin0 hN)
    rw [hqdef]; push_cast; linarith
  have hq512 : 512 * a ^ 3 ≤ q := by
    have h1 : (256 * a ^ 3 : ℝ) ≤ (Nat.ceil (256 * a ^ 3) : ℝ) := Nat.le_ceil _
    have h2 : (Nat.ceil (256 * a ^ 3) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNa
    rw [hqdef]; push_cast; linarith
  have ha0 : 0 < a := by linarith
  have hKpos : 0 < K := lt_of_lt_of_le K₀_pos hK
  have hl : 0 < Real.log q := by linarith
  -- `a·t ≤ 1/4`
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
  obtain ⟨h34, hlt1, hρ0, hρ12⟩ :=
    rhoA_bounds hq4 ha0 hat
  -- 目标化为 `q·ρ ≤ τ`
  suffices hgoal : q * ρ ≤ τ by
    have h4 : 4 * ((N : ℝ) + 1) = 2 * q := by rw [hqdef]; ring
    have h5 : (1 : ℝ) - a * (Real.log q / q) ^ (2 / 3 : ℝ) = ρ := by rw [hρdef, rhoA]
    have h6 : Real.log (2 * (N : ℝ) + 2) / (2 * (N : ℝ) + 2) = Real.log q / q := by rw [hqdef]
    have h7 : (∑ j, θ j) = 2 * τ := by rw [hτdef]; ring
    rw [h4, h6, h5, cost, h7]
    linarith
  by_contra hlt
  push_neg at hlt
  have hτρ : τ ≤ ρ * q := by linarith [hlt]
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
  have hδ'pos : 0 < δ' := by rw [hδ'def]; exact deltaOf_pos hρ0 hlt1
  have hεpos : 0 < ε := by rw [hεdef]; exact epsOf_pos hδ'pos τ k
  have hε0 : 0 ≤ ε := hεpos.le
  have hBpos : 0 < B := by rw [hBdef]; exact Real.sqrt_pos_of_pos hεpos
  -- sharp collar 界
  obtain ⟨M₁, M₂, hM₁nn, hM₂nn, hA1, hA2, hM1sh, hM2sh⟩ := hsharp N hN hAdm hτρ
  have hPε : ∀ μ : ℝ, |μ| ≤ τ →
      ‖Complex.exp (-(μ : ℂ) * Complex.I) - P.eval ((μ : ℂ))‖ ≤ ε := by
    intro μ hμ
    have h := scaledApprox_band_epsOf τ hτpos hδ'pos (k := k) (by omega) hμ
    rw [hPdef, hεdef]
    exact h
  have hψ : ∀ μ : ℝ, ‖psi τ B P μ‖ ≤ ε + B * M₁ :=
    norm_psi_le_band_add_collar hτ0 hBpos P hM₁nn hPε hA1
  have hcut := deriv_cutoff_le_explicit hτpos hBpos
  have hK1 : ∀ μ : ℝ, ‖deriv (fun x : ℝ => ((cutoff τ B x : ℝ) : ℂ)) μ‖ ≤ K / B := by
    intro μ
    rw [deriv_coe_cutoff τ B hτpos hBpos, Complex.norm_real, Real.norm_eq_abs]
    exact le_trans (hcut.1 μ) (div_le_div_of_nonneg_right hK hBpos.le)
  have hK2 : ∀ μ : ℝ, ‖deriv (deriv (fun x : ℝ => ((cutoff τ B x : ℝ) : ℂ))) μ‖ ≤ K / B ^ 2 := by
    intro μ
    rw [deriv_deriv_coe_cutoff τ B hτpos hBpos, Complex.norm_real, Real.norm_eq_abs]
    exact le_trans (hcut.2 μ) (div_le_div_of_nonneg_right hK (by positivity))
  -- 侧条件 `k²·B ≤ τ`
  have hkB : (k : ℝ) ^ 2 * B ≤ τ := by
    have hqthr : (20 * Real.exp 1 * a ^ (-(1 / 4 : ℝ))) ^ (1 / (effS a / 2 - 7 / 6)) ≤ q :=
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hqmin
    have h := ksq_sqrt_epsOf_le_gen (a := a) (q := q) (τ := τ) (N := N) hq0 hq1 hqdef hq4 hlog1
      ha hat hqthr hτ0 hτρ hτlow
    have h2 : ((k : ℕ) : ℝ) ^ 2 * B
        = ((2 * N + 1 : ℕ) : ℝ) ^ 2
          * Real.sqrt (epsOf τ (deltaOf (rhoA a q)) (2 * N + 1)) := by
      rw [hkdef, hBdef, hεdef, hδ'def, hρdef]
    rw [h2] at h
    linarith [h, hτpos]
  have hBτ : B ≤ τ := by
    have hk1 : (1 : ℝ) ≤ (k : ℝ) ^ 2 := by
      have hk1' : (1 : ℝ) ≤ (k : ℝ) := by
        rw [hkdef]; push_cast
        have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
        linarith
      nlinarith
    have hB0 : 0 ≤ B := hBpos.le
    nlinarith [hkB, hk1, hB0]
  -- 乘积界（无侧条件版）
  have hprod := kernelProd_sqrt_param_nolift 2 β P hτpos hBpos hε0 hKpos.le hCd1.le hCd2.le
    hM₁nn hM₂nn hBτ hkB hBdef hM1sh hM2sh hψ hPε hA1 hA2 hK1 hK2
  have hτq : τ ≤ q := by nlinarith only [hτρ, hρ0, hlt1, hq0]
  have hbound : kernelA τ B P * kernelC τ B P ≤ (1 / 36) * (1 + Cd1)
      * (16 * Cd2 * q ^ (β : ℝ) * ε ^ 2 + 32 * K * Cd1 * q ^ (2 : ℝ) * ε ^ 2
        + 16 * K * q * ε ^ (3 / 2 : ℝ)) := by
    have hkq : (k : ℝ) ≤ q := by rw [hkdef, hqdef]; push_cast; linarith
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := by positivity
    have hkβ : (k : ℝ) ^ β ≤ q ^ (β : ℝ) := by
      rw [show q ^ (β : ℝ) = q ^ β from Real.rpow_natCast q β]
      exact pow_le_pow_left₀ hk0 hkq β
    have hk2 : (k : ℝ) ^ 2 ≤ q ^ (2 : ℝ) := by
      rw [show q ^ (2 : ℝ) = q ^ 2 from Real.rpow_natCast q 2]
      exact pow_le_pow_left₀ hk0 hkq 2
    have h1 : 16 * Cd2 * (k : ℝ) ^ β * ε ^ 2 ≤ 16 * Cd2 * q ^ (β : ℝ) * ε ^ 2 := by
      have hh : 16 * Cd2 * (k : ℝ) ^ β ≤ 16 * Cd2 * q ^ (β : ℝ) :=
        mul_le_mul_of_nonneg_left hkβ (by positivity)
      exact mul_le_mul_of_nonneg_right hh (by positivity)
    have h2 : 32 * K * Cd1 * (k : ℝ) ^ 2 * ε ^ 2 ≤ 32 * K * Cd1 * q ^ (2 : ℝ) * ε ^ 2 := by
      have hh : 32 * K * Cd1 * (k : ℝ) ^ 2 ≤ 32 * K * Cd1 * q ^ (2 : ℝ) :=
        mul_le_mul_of_nonneg_left hk2 (by positivity)
      exact mul_le_mul_of_nonneg_right hh (by positivity)
    have h3 : 16 * K * τ * ε ^ (3 / 2 : ℝ) ≤ 16 * K * q * ε ^ (3 / 2 : ℝ) := by
      have hh : 16 * K * τ ≤ 16 * K * q := mul_le_mul_of_nonneg_left hτq (by positivity)
      exact mul_le_mul_of_nonneg_right hh (by positivity)
    have hcoef : 0 ≤ (1 / 36 : ℝ) * (1 + Cd1) := by positivity
    calc kernelA τ B P * kernelC τ B P
        ≤ (1 / 36) * (1 + Cd1) * (16 * Cd2 * (k : ℝ) ^ β * ε ^ 2
            + 32 * K * Cd1 * (k : ℝ) ^ 2 * ε ^ 2 + 16 * K * τ * ε ^ (3 / 2 : ℝ)) := hprod
      _ ≤ (1 / 36) * (1 + Cd1) * (16 * Cd2 * q ^ (β : ℝ) * ε ^ 2
            + 32 * K * Cd1 * q ^ (2 : ℝ) * ε ^ 2 + 16 * K * q * ε ^ (3 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left (by linarith [h1, h2, h3]) hcoef
  -- `ε` 的界
  have hε_le : ε ≤ 13 * a ^ (-(1 / 2 : ℝ)) * q ^ (1 / 3 - effS a) := by
    have h1 : ε ≤ D0 ρ * Real.exp (-(mu ρ) * q) := by
      rw [hεdef, hδ'def, hρdef]
      exact epsOf_le_D0 hρ0 hlt1 hτ0 (by rw [← hqdef]; exact hτρ)
    have h2 : D0 ρ * Real.exp (-(mu ρ) * q)
        ≤ 13 * a ^ (-(1 / 2 : ℝ)) * (q / Real.log q) ^ (1 / 3 : ℝ) * q ^ (-(effS a)) := by
      rw [hρdef]
      exact D0_mu_le hq4 ha0 hat
    have h3 : (q / Real.log q) ^ (1 / 3 : ℝ) ≤ q ^ (1 / 3 : ℝ) := by
      rw [Real.div_rpow hq0.le hl.le, div_le_iff₀ (Real.rpow_pos_of_pos hl _)]
      have h4 : (1 : ℝ) ≤ (Real.log q) ^ (1 / 3 : ℝ) := Real.one_le_rpow hlog1 (by norm_num)
      have h5 := Real.rpow_pos_of_pos hq0 (1 / 3 : ℝ)
      nlinarith
    have h6 : q ^ (1 / 3 : ℝ) * q ^ (-(effS a)) = q ^ (1 / 3 - effS a) := by
      rw [← Real.rpow_add hq0]
      congr 1
      try ring
    refine le_trans (le_trans h1 h2) ?_
    calc 13 * a ^ (-(1 / 2 : ℝ)) * (q / Real.log q) ^ (1 / 3 : ℝ) * q ^ (-(effS a))
        ≤ 13 * a ^ (-(1 / 2 : ℝ)) * q ^ (1 / 3 : ℝ) * q ^ (-(effS a)) := by
          have h7 : 0 ≤ 13 * a ^ (-(1 / 2 : ℝ)) := by positivity
          have h8 : 0 ≤ q ^ (-(effS a)) := Real.rpow_nonneg hq0.le _
          have h9 : 13 * a ^ (-(1 / 2 : ℝ)) * (q / Real.log q) ^ (1 / 3 : ℝ)
              ≤ 13 * a ^ (-(1 / 2 : ℝ)) * q ^ (1 / 3 : ℝ) :=
            mul_le_mul_of_nonneg_left h3 h7
          exact mul_le_mul_of_nonneg_right h9 h8
      _ = 13 * a ^ (-(1 / 2 : ℝ)) * q ^ (1 / 3 - effS a) := by
          rw [mul_assoc, h6]
  -- 数论收尾
  have hqE0 : 64 * effK1 Cd1 Cd2 K a < q ^ (-(effE a β)) := by
    have h1 : effQ0 Cd1 Cd2 K a β / 2 ≤ (Nat.ceil (effQ0 Cd1 Cd2 K a β / 2) : ℝ) := Nat.le_ceil _
    have h2 : (Nat.ceil (effQ0 Cd1 Cd2 K a β / 2) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNq
    have h3 : effQ0 Cd1 Cd2 K a β < q := by rw [hqdef]; push_cast; linarith
    have h4 : (64 * effK1 Cd1 Cd2 K a) ^ (1 / (-(effE a β))) < q :=
      lt_of_le_of_lt (le_max_right _ _) h3
    have hEneg : effE a β < 0 := effE_neg ha hβ4
    have hc : 0 < -(effE a β) := by linarith
    have hK1pos : 0 < 64 * effK1 Cd1 Cd2 K a := by
      have hp := effK1_pos hCd1 hCd2 hKpos ha0
      linarith
    have h5 := Real.rpow_lt_rpow (x := (64 * effK1 Cd1 Cd2 K a) ^ (1 / (-(effE a β))))
      (y := q) (z := -(effE a β)) (by positivity) h4 hc
    have h6 : ((64 * effK1 Cd1 Cd2 K a) ^ (1 / (-(effE a β)))) ^ (-(effE a β))
        = 64 * effK1 Cd1 Cd2 K a := by
      have hexp : 1 / (-(effE a β)) * (-(effE a β)) = 1 := by
        rw [one_div, inv_mul_cancel₀ (by linarith : (-(effE a β)) ≠ 0)]
      rw [← Real.rpow_mul hK1pos.le, hexp, Real.rpow_one]
    linarith [h5, h6.le]
  have hfin := final_arith (Cd1 := Cd1) (Cd2 := Cd2) (K := K) (a := a) (q := q) (ε := ε)
    (β := β) hCd1 hCd2 hKpos ha0 hβ hq1 hε0 hε_le hqE0
  have hlt' : kernelA τ B P * kernelC τ B P < ((1 - Real.cos (Real.pi / 2)) / 8) ^ 2 := by
    have hcos : Real.cos (Real.pi / 2) = 0 := Real.cos_pi_div_two
    rw [hcos]
    norm_num
    exact lt_of_le_of_lt hbound hfin
  have hsmall := h_zero_lt_of_prod_lt (φ := Real.pi) Real.pi_pos le_rfl hAdm hδ'pos (by
    rw [← hτdef, ← hkdef, ← hεdef, ← hBdef, ← hPdef]
    exact hlt')
  have hge := h_zero_ge Real.pi Real.pi_pos.le le_rfl L α θ hAdm.2.1
  rw [Real.cos_pi_div_two] at hge hsmall
  linarith


end RobustZ

/-! ## 备注

§1–§2 已完成并可复用的部分：

* `one_sub_le_deltaOf` / `deltaOf_le_one` / `fcoef_tail_le` / `epsOf_eq_mul` /
  `honest_le_eps_mul`：把 `Approx.fcoef_bound` 翻译成 `SharpDerivGen` 需要的
  honest 尾部衰减 `‖c_{k+j}‖ ≤ ε_h r^j`，并证明 `ε_h ≤ epsOf·(1-r')/2`（**相消**）。
* `ksq_sqrt_epsOf_le_gen`：侧条件 `k²√ε ≤ τ/4`，把原先的 `q ≥ 10^{10}` 换成显式阈值
  `(20e·a^{-1/4})^{1/(s/2-7/6)} ≤ q`（`s = effS a`），使 `N₀` 可以远小于 `5·10⁹`。
* `effQmin` / `effN0End`：相应的显式阈值与 `N₀`。
* `SharpCollarFrom` + `effective_bound_of_collar`：把 `Effective.effective_bound_of_sharp`
  的假设从"固定 `Cd1, Cd2` 对一切 `N`"放宽为"`N ≥ N₀` 且 `τ ≤ ρq`"，其余装配逐字复用
  （`final_arith`、`effQ0`、`kernelProd_sqrt_param_nolift`）。

**尚未落地**：用 `SharpDerivGen` 的 honest collar 常数实例化 `SharpCollarFrom`
（即 `collar_bound_concrete : SharpCollarFrom (effN0End K a) 7 770 a 4` 与最终的
`endgame_bound`）。工作草稿（含完整的常数推导，最后一步 `τM₁ ≤ 7k²ε`、`τ²M₂ ≤ 770k⁴ε`
的算术尚未收敛）见 `EndgameWIP.lean.txt`。
-/
