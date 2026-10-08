import RobustZ.EffKernel
import RobustZ.CutoffExplicit
import RobustZ.EffectiveCalc
import RobustZ.ElementaryBound
import RobustZ.M5Scaled
import RobustZ.FinalSmall
import RobustZ.FinalConv
import RobustZ.HTraceLower

/-!
# `Effective`：端到端的有效定理（显式 `N₀`）

本文件把三块**已完成**的零件接起来，给出论文主定理的**有效（显式 `N₀`）**版本：

* `M5Sqrt` / `EffKernel`：截断尺度 `B = √ε` 的乘积界（workstream G 的代数，
  本文件用 `EffKernel.kernelProd_sqrt_param_nolift` 的**无侧条件**形状）；
* `EffectiveCalc`（workstream N）：`mu`、`D0`、`rho` 的实分析；
* `FinalSmall.h_zero_lt_of_kernel_decay` + `HTraceLower.h_zero_ge`：端点小性与端点下界的冲突。

## 结论

对 `a ≥ 2`、`β ∈ [2,4]`、`Cd1, Cd2 > 0`、`K ≥ K₀ = 21.1`，**若** sharp collar 界
（见 `SharpCollar`，指数形状 `τM₁ ≤ Cd1·k²·ε`、`τ²M₂ ≤ Cd2·k^β·ε`，`k = 2N+1`、
`ε = epsOf τ (δ'(ρ_a(q))) k`、`ρ_a(q) = 1 - a(log q/q)^{2/3}`）成立，则

```
∀ N ≥ N₀(Cd1,Cd2,K,a,β),  ∀ admissible (L,α,θ),
  4(N+1)·(1 - a·(log q/q)^{2/3}) ≤ cost θ,      q = 2N+2,
```

其中 `N₀` 是**显式**函数（`effN0`）。

## 证明链（逐项）

1. `Admissible → τ > 0`：`τ = 0` 时 `h(0) = 0`（`h_zero_of_admissible_of_cost_eq_zero`），
   与 `h_zero_ge` 的 `1 ≤ h(0)` 冲突。
2. 反证假设 `τ < ρ_a(q)·q`；取 `δ' = deltaOf ρ`，则 `cosh δ' = 1/ρ`、
   `δ' - ρ·sinh δ' = mu ρ`、`(1+4/(1-e^{-δ'}))·e^{δ'} = D0 ρ`（§1 的三条恒等式）。
3. `epsOf_le_exp_decay` + 恒等式：`ε ≤ D0 ρ · e^{-(mu ρ)q}`；
   `mu_lower_sharp` + `D0_le_inv_sqrt` 给
   `D0 ρ · e^{-(mu ρ)q} ≤ 13·a^{-1/2}·(q/log q)^{1/3}·q^{-s}`，`s = (47/50)a^{3/2}`。
4. 侧条件 `k²√ε ≤ τ`：由 `√ε ≤ √C·e^{δ'/2}e^{-(mu ρ)q/2}`、
   `√C·e^{δ'/2} ≤ 5(1-ρ)^{-1/4}` 与初等下界 `τ ≥ q/e`（`elementary_bound_pi` +
   `div_exp_lt_factorial_rpow`）得到。
5. `EffKernel.kernelProd_sqrt_param_nolift`：`C₁C₂ ≤ (1/36)(1+Cd1)(16Cd2k^β ε² + 32KCd1k²ε² + 16Kτε^{3/2})`。
6. 数论收尾：三项分别 `≤ K₁·q^E/(log q)^{1/2}`（`E = max(β+2/3-2s, 3/2-3s/2)`），
   而 `q ≥ (64√2·K₁)^{1/(-E-1/4)}` 保证该式 `< 1/64`。
7. `h_zero_lt_of_kernel_decay`（取足够小的 `η`）给 `h(0) < 1 - cos(π/2) = 1`，与 `h_zero_ge` 冲突。

## 与论文参数的差别

* `a` 不能任意小：`s = (47/50)a^{3/2}` 必须 `> β/2 + 1/3`，故 `β = 4` 时 `a > 1.9`，
  `β = 2` 时 `a > 1.35`。本文件取 `a ≥ 2`（安全）。
* 若 A 能给出侧条件 `k^β·B ≤ τ`（等价于 `s ≥ β`，`β = 4` 时 `a ≥ 3.5`），
  则可用 `EffKernel.kernelProd_sqrt_param_gen` 把常数降回 `sqrtC0`，`N₀` 大幅变小。
-/

set_option maxHeartbeats 2000000

noncomputable section

namespace RobustZ

open Filter MeasureTheory
open scoped Real

/-! ## §1 显式半径、`δ'`、`η` 与 `D0` 的恒等式 -/

/-- `δ'(ρ) = log ((1+√(1-ρ²))/ρ)`：使 `cosh δ' = 1/ρ` 的那个 `δ'`。 -/
noncomputable def deltaOf (ρ : ℝ) : ℝ := Real.log ((1 + Real.sqrt (1 - ρ ^ 2)) / ρ)

/-- 目标半径 `ρ_a(q) = 1 - a·(log q / q)^{2/3}`。 -/
noncomputable def rhoA (a q : ℝ) : ℝ := 1 - a * (Real.log q / q) ^ (2 / 3 : ℝ)

/-- `s(a) = (47/50)·a^{3/2}`：`mu_lower_sharp` 给出的指数增益系数。 -/
noncomputable def effS (a : ℝ) : ℝ := (47 / 50) * a ^ (3 / 2 : ℝ)

/-- `log q ≤ 2√q`（`q ≥ 1`）。 -/
lemma log_le_two_sqrt (q : ℝ) (hq : 1 ≤ q) : Real.log q ≤ 2 * Real.sqrt q := by
  have hq0 : 0 < q := lt_of_lt_of_le one_pos hq
  have hs0 : 0 < Real.sqrt q := Real.sqrt_pos_of_pos hq0
  have h1 : Real.log q = 2 * Real.log (Real.sqrt q) := by
    rw [Real.log_sqrt (le_of_lt hq0)]; ring
  have h2 : Real.log (Real.sqrt q) ≤ Real.sqrt q - 1 := Real.log_le_sub_one_of_pos hs0
  linarith

lemma deltaOf_pos {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) : 0 < deltaOf ρ := by
  rw [deltaOf]
  refine Real.log_pos ?_
  rw [lt_div_iff₀ hρ0]
  have hs := Real.sqrt_nonneg (1 - ρ ^ 2)
  linarith

lemma exp_deltaOf {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    Real.exp (deltaOf ρ) = (1 + Real.sqrt (1 - ρ ^ 2)) / ρ := by
  rw [deltaOf, Real.exp_log]
  exact div_pos (by linarith [Real.sqrt_nonneg (1 - ρ ^ 2)]) hρ0

lemma exp_neg_deltaOf {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    Real.exp (-(deltaOf ρ)) = ρ / (1 + Real.sqrt (1 - ρ ^ 2)) := by
  rw [Real.exp_neg, exp_deltaOf hρ0 hρ1, inv_div]

/-- **`cosh δ' = 1/ρ`**。 -/
lemma cosh_deltaOf {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    Real.cosh (deltaOf ρ) = 1 / ρ := by
  have hs2 : Real.sqrt (1 - ρ ^ 2) ^ 2 = 1 - ρ ^ 2 := Real.sq_sqrt (by nlinarith)
  have h1s : (0 : ℝ) < 1 + Real.sqrt (1 - ρ ^ 2) := by
    linarith [Real.sqrt_nonneg (1 - ρ ^ 2)]
  rw [Real.cosh_eq, exp_deltaOf hρ0 hρ1, exp_neg_deltaOf hρ0 hρ1]
  field_simp
  nlinarith [hs2]

/-- **`sinh δ' = √(1-ρ²)/ρ`**。 -/
lemma sinh_deltaOf {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    Real.sinh (deltaOf ρ) = Real.sqrt (1 - ρ ^ 2) / ρ := by
  have hs2 : Real.sqrt (1 - ρ ^ 2) ^ 2 = 1 - ρ ^ 2 := Real.sq_sqrt (by nlinarith)
  have h1s : (0 : ℝ) < 1 + Real.sqrt (1 - ρ ^ 2) := by
    linarith [Real.sqrt_nonneg (1 - ρ ^ 2)]
  rw [Real.sinh_eq, exp_deltaOf hρ0 hρ1, exp_neg_deltaOf hρ0 hρ1]
  field_simp
  nlinarith [hs2]

/-- **`δ' - ρ·sinh δ' = mu ρ`**。 -/
lemma mu_eq_deltaOf {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    mu ρ = deltaOf ρ - ρ * Real.sinh (deltaOf ρ) := by
  have hs2 : Real.sqrt (1 - ρ ^ 2) ^ 2 = 1 - ρ ^ 2 := Real.sq_sqrt (by nlinarith)
  rw [mu, sinh_deltaOf hρ0 hρ1, deltaOf]
  field_simp

/-- **`D0 ρ = (1 + 4/(1-e^{-δ'}))·e^{δ'}`**。 -/
lemma D0_eq_deltaOf {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    D0 ρ = (1 + 4 / (1 - Real.exp (-(deltaOf ρ)))) * Real.exp (deltaOf ρ) := by
  rw [D0, exp_deltaOf hρ0 hρ1, exp_neg_deltaOf hρ0 hρ1]

/-- **`ε ≤ D0 ρ · e^{-(mu ρ)q}`**：`epsOf_le_exp_decay` 加两条恒等式。 -/
lemma epsOf_le_D0 {ρ τ : ℝ} {N : ℕ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hτ0 : 0 ≤ τ) (hτρ : τ ≤ ρ * (2 * (N : ℝ) + 2)) :
    epsOf τ (deltaOf ρ) (2 * N + 1) ≤ D0 ρ * Real.exp (-(mu ρ) * (2 * (N : ℝ) + 2)) := by
  rw [D0_eq_deltaOf hρ0 hρ1, mu_eq_deltaOf hρ0 hρ1]
  exact epsOf_le_exp_decay (deltaOf_pos hρ0 hρ1) hτ0 hτρ

/-! ## §2 数值链：`D0 ρ · e^{-(mu ρ)q} ≤ 13 a^{-1/2}(q/log q)^{1/3}q^{-s}` -/

lemma sqrt_at_eq {a q : ℝ} (ha : 0 < a) (hq : 0 < q) (hl : 0 < Real.log q) :
    Real.sqrt (a * (Real.log q / q) ^ (2 / 3 : ℝ))
      = a ^ (1 / 2 : ℝ) * (Real.log q / q) ^ (1 / 3 : ℝ) := by
  have hT : 0 < Real.log q / q := div_pos hl hq
  rw [Real.sqrt_eq_rpow, Real.mul_rpow ha.le (Real.rpow_nonneg hT.le _),
    ← Real.rpow_mul hT.le]
  norm_num

lemma inv_sqrt_at_eq {a q : ℝ} (ha : 0 < a) (hq : 0 < q) (hl : 0 < Real.log q) :
    13 / Real.sqrt (a * (Real.log q / q) ^ (2 / 3 : ℝ))
      = 13 * a ^ (-(1 / 2 : ℝ)) * (q / Real.log q) ^ (1 / 3 : ℝ) := by
  have hT : 0 < Real.log q / q := div_pos hl hq
  have hinv : q / Real.log q = (Real.log q / q)⁻¹ := by rw [inv_div]
  rw [hinv, Real.inv_rpow hT.le (1 / 3), sqrt_at_eq ha hq hl, Real.rpow_neg ha.le (1 / 2)]
  field_simp

/-- **`(1-ρ_a(q))^{3/2} = a^{3/2}·(log q/q)`**。 -/
lemma one_sub_rhoA_rpow {a q : ℝ} (ha : 0 < a) (hq : 0 < q) (hl : 0 < Real.log q) :
    (1 - rhoA a q) ^ (3 / 2 : ℝ) = a ^ (3 / 2 : ℝ) * (Real.log q / q) := by
  have hT : 0 < Real.log q / q := div_pos hl hq
  have hone : 1 - rhoA a q = a * (Real.log q / q) ^ (2 / 3 : ℝ) := by rw [rhoA]; ring
  rw [hone, Real.mul_rpow ha.le (Real.rpow_nonneg hT.le _), ← Real.rpow_mul hT.le]
  norm_num

/-- **`ρ_a(q)` 的常数下界**：`q ≥ 10^4`、`a ≥ 3/2`、`a·t ≤ 1/4` 时 `3/4 ≤ ρ_a(q) < 1`。 -/
lemma rhoA_bounds {a q : ℝ} (hq : (10 : ℝ) ^ 4 ≤ q) (ha : 0 < a)
    (hat : a * (Real.log q / q) ^ (2 / 3 : ℝ) ≤ 1 / 4) :
    3 / 4 ≤ rhoA a q ∧ rhoA a q < 1 ∧ 0 < rhoA a q ∧ 1 / 2 ≤ rhoA a q := by
  have hq0 : 0 < q := by
    have : (0 : ℝ) < (10 : ℝ) ^ 4 := by norm_num
    linarith
  have hl : 0 < Real.log q := Real.log_pos (by linarith [hq])
  have hT : 0 < Real.log q / q := div_pos hl hq0
  have ht : 0 < (Real.log q / q) ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hT _
  have hone : rhoA a q = 1 - a * (Real.log q / q) ^ (2 / 3 : ℝ) := rfl
  rw [hone]
  refine ⟨by linarith, by nlinarith [mul_pos ha ht], by linarith, by linarith⟩

/-- **`mu_lower_sharp` 的指数形式**：`mu (ρ_a(q)) ≥ s(a)·(log q/q)`。 -/
lemma mu_rhoA_lower {a q : ℝ} (hq : (10 : ℝ) ^ 4 ≤ q) (ha : 0 < a)
    (hat : a * (Real.log q / q) ^ (2 / 3 : ℝ) ≤ 1 / 4) :
    effS a * (Real.log q / q) ≤ mu (rhoA a q) := by
  obtain ⟨h34, hlt1, hpos, h12⟩ := rhoA_bounds hq ha hat
  have hq0 : 0 < q := by
    have : (0 : ℝ) < (10 : ℝ) ^ 4 := by norm_num
    linarith
  have hl : 0 < Real.log q := Real.log_pos (by linarith [hq])
  calc effS a * (Real.log q / q)
      = (47 / 50) * ((1 - rhoA a q) ^ (3 / 2 : ℝ)) := by
        rw [one_sub_rhoA_rpow ha hq0 hl, effS]; ring
    _ ≤ mu (rhoA a q) := mu_lower_sharp (rhoA a q) h12 hlt1

/-- **数值链的核心**：`D0 ρ_a(q) · e^{-(mu ρ_a(q))·q} ≤ 13 a^{-1/2}(q/log q)^{1/3} q^{-s(a)}`。 -/
lemma D0_mu_le {a q : ℝ} (hq : (10 : ℝ) ^ 4 ≤ q) (ha : 0 < a)
    (hat : a * (Real.log q / q) ^ (2 / 3 : ℝ) ≤ 1 / 4) :
    D0 (rhoA a q) * Real.exp (-(mu (rhoA a q)) * q)
      ≤ 13 * a ^ (-(1 / 2 : ℝ)) * (q / Real.log q) ^ (1 / 3 : ℝ) * q ^ (-(effS a)) := by
  obtain ⟨h34, hlt1, hpos, h12⟩ := rhoA_bounds hq ha hat
  have hq0 : 0 < q := by
    have : (0 : ℝ) < (10 : ℝ) ^ 4 := by norm_num
    linarith
  have hl : 0 < Real.log q := Real.log_pos (by linarith [hq])
  -- `D0` 的上界
  have hD0 : D0 (rhoA a q) ≤ 13 * a ^ (-(1 / 2 : ℝ)) * (q / Real.log q) ^ (1 / 3 : ℝ) := by
    have hone : 1 - rhoA a q = a * (Real.log q / q) ^ (2 / 3 : ℝ) := by rw [rhoA]; ring
    have heq : 13 / (1 - rhoA a q) ^ (1 / 2 : ℝ)
        = 13 * a ^ (-(1 / 2 : ℝ)) * (q / Real.log q) ^ (1 / 3 : ℝ) := by
      rw [hone, ← Real.sqrt_eq_rpow]
      exact inv_sqrt_at_eq ha hq0 hl
    exact (D0_le_inv_sqrt (rhoA a q) h34 hlt1).trans (le_of_eq heq)
  -- 指数的上界
  have hexp : Real.exp (-(mu (rhoA a q)) * q) ≤ q ^ (-(effS a)) := by
    have hmu := mu_rhoA_lower hq ha hat
    have h1 : -(mu (rhoA a q)) * q ≤ -(effS a) * Real.log q := by
      have : effS a * (Real.log q / q) * q = effS a * Real.log q := by field_simp
      nlinarith [hmu, hq0]
    have h2 : Real.exp (-(mu (rhoA a q)) * q) ≤ Real.exp (-(effS a) * Real.log q) :=
      Real.exp_le_exp.mpr h1
    have h3 : Real.exp (-(effS a) * Real.log q) = q ^ (-(effS a)) := by
      rw [Real.rpow_def_of_pos hq0]
      congr 1
      ring
    rw [h3] at h2
    exact h2
  have hD0nn : 0 ≤ 13 * a ^ (-(1 / 2 : ℝ)) * (q / Real.log q) ^ (1 / 3 : ℝ) := by positivity
  calc D0 (rhoA a q) * Real.exp (-(mu (rhoA a q)) * q)
      ≤ (13 * a ^ (-(1 / 2 : ℝ)) * (q / Real.log q) ^ (1 / 3 : ℝ))
          * Real.exp (-(mu (rhoA a q)) * q) :=
        mul_le_mul_of_nonneg_right hD0 (Real.exp_pos _).le
    _ ≤ (13 * a ^ (-(1 / 2 : ℝ)) * (q / Real.log q) ^ (1 / 3 : ℝ)) * q ^ (-(effS a)) :=
        mul_le_mul_of_nonneg_left hexp hD0nn
    _ = 13 * a ^ (-(1 / 2 : ℝ)) * (q / Real.log q) ^ (1 / 3 : ℝ) * q ^ (-(effS a)) := by ring


/-! ## §3 侧条件 `k²·√ε ≤ τ`（初等下界 `τ ≥ q/e`） -/

/-- **`√C·e^{δ'/2} ≤ 5(1-ρ)^{-1/4}`**，`C = 1 + 4/(1-e^{-δ'(ρ)})`。 -/
lemma sqrt_C_exp_half_le {ρ : ℝ} (hρ34 : 3 / 4 ≤ ρ) (hρ1 : ρ < 1) :
    Real.sqrt (1 + 4 / (1 - Real.exp (-(deltaOf ρ)))) * Real.exp (deltaOf ρ / 2)
      ≤ 5 * (1 - ρ) ^ (-(1 / 4 : ℝ)) := by
  have hρ0 : 0 < ρ := by linarith
  have h1mρ : 0 < 1 - ρ := by linarith
  set s := Real.sqrt (1 - ρ ^ 2) with hsdef
  have hs2 : s ^ 2 = 1 - ρ ^ 2 := Real.sq_sqrt (by nlinarith)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hspos : 0 < s := by
    rcases lt_or_eq_of_le hs0 with h | h
    · exact h
    · rw [← h] at hs2; nlinarith
  have hs1 : s ≤ 1 := by nlinarith [hs0, hs2, sq_nonneg ρ]
  have h1s : 0 < 1 + s := by linarith
  have hexp : Real.exp (deltaOf ρ) = (1 + s) / ρ := by
    rw [hsdef]; exact exp_deltaOf hρ0 hρ1
  have hexpn : Real.exp (-(deltaOf ρ)) = ρ / (1 + s) := by
    rw [hsdef]; exact exp_neg_deltaOf hρ0 hρ1
  have hone : 1 - Real.exp (-(deltaOf ρ)) = (1 + s - ρ) / (1 + s) := by
    rw [hexpn]; field_simp
  have hge : s / 2 ≤ 1 - Real.exp (-(deltaOf ρ)) := by
    rw [hone, le_div_iff₀ h1s]
    nlinarith [hρ1, hs0]
  have hpos : 0 < 1 - Real.exp (-(deltaOf ρ)) := lt_of_lt_of_le (by linarith) hge
  have hC : 1 + 4 / (1 - Real.exp (-(deltaOf ρ))) ≤ 9 / s := by
    have h1 : 4 / (1 - Real.exp (-(deltaOf ρ))) ≤ 8 / s := by
      rw [div_le_div_iff₀ hpos hspos]
      nlinarith [hge]
    have h2 : (1 : ℝ) ≤ 1 / s := by rw [le_div_iff₀ hspos]; linarith
    have h3 : (1 : ℝ) + 8 / s ≤ 1 / s + 8 / s := by linarith
    have h4 : (1 : ℝ) / s + 8 / s = 9 / s := by ring
    linarith
  have hsqrtC : Real.sqrt (1 + 4 / (1 - Real.exp (-(deltaOf ρ)))) ≤ 3 / Real.sqrt s := by
    refine (Real.sqrt_le_sqrt hC).trans (le_of_eq ?_)
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 9),
      show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3)]
  have hexp2 : Real.exp (deltaOf ρ / 2) ≤ 5 / 3 := by
    rw [Real.exp_half, hexp]
    have h : (1 + s) / ρ ≤ 25 / 9 := by
      rw [div_le_iff₀ hρ0]; nlinarith [hs1, hρ34]
    calc Real.sqrt ((1 + s) / ρ) ≤ Real.sqrt (25 / 9) := Real.sqrt_le_sqrt h
      _ = 5 / 3 := by
          rw [show (25 / 9 : ℝ) = (5 / 3) ^ 2 by norm_num,
            Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 5 / 3)]
  have hsroot : Real.sqrt (1 - ρ) ≤ s := by
    rw [hsdef]; exact Real.sqrt_le_sqrt (by nlinarith)
  have h14 : (1 - ρ) ^ (1 / 4 : ℝ) ≤ Real.sqrt s := by
    have h1 : (1 - ρ) ^ (1 / 4 : ℝ) = Real.sqrt (Real.sqrt (1 - ρ)) := by
      rw [Real.sqrt_eq_rpow (1 - ρ), Real.sqrt_eq_rpow ((1 - ρ) ^ (1 / 2 : ℝ)),
        ← Real.rpow_mul (le_of_lt h1mρ)]
      norm_num
    rw [h1]
    exact Real.sqrt_le_sqrt hsroot
  have h14pos : 0 < (1 - ρ) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos h1mρ _
  have hone_div : 1 / Real.sqrt s ≤ (1 - ρ) ^ (-(1 / 4 : ℝ)) := by
    have hsqrts : 0 < Real.sqrt s := Real.sqrt_pos_of_pos hspos
    rw [one_div, Real.rpow_neg (le_of_lt h1mρ)]
    exact (inv_le_inv₀ hsqrts h14pos).mpr h14
  calc Real.sqrt (1 + 4 / (1 - Real.exp (-(deltaOf ρ)))) * Real.exp (deltaOf ρ / 2)
      ≤ (3 / Real.sqrt s) * (5 / 3) :=
        mul_le_mul hsqrtC hexp2 (Real.exp_pos _).le (by positivity)
    _ = 5 / Real.sqrt s := by ring
    _ ≤ 5 * (1 - ρ) ^ (-(1 / 4 : ℝ)) := by
        have h := mul_le_mul_of_nonneg_left hone_div (by norm_num : (0 : ℝ) ≤ 5)
        calc 5 / Real.sqrt s = 5 * (1 / Real.sqrt s) := by ring
          _ ≤ 5 * (1 - ρ) ^ (-(1 / 4 : ℝ)) := h

/-- **`effS a ≥ 2.62`**（`a ≥ 2`）。 -/
lemma effS_ge {a : ℝ} (ha : 2 ≤ a) : 2.62 ≤ effS a := by
  have h2 : effS 2 ≤ effS a := by
    rw [effS, effS]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by norm_num) ha (by norm_num))
      (by norm_num)
  have h3 : (2.62 : ℝ) ≤ effS 2 := by
    rw [effS]
    have h : (2.8 : ℝ) ≤ (2 : ℝ) ^ (3 / 2 : ℝ) := by
      have h1 : (2 : ℝ) ^ (3 / 2 : ℝ) = 2 * Real.sqrt 2 := by
        rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (by norm_num),
          Real.rpow_one, Real.sqrt_eq_rpow]
      rw [h1]
      have h2 : (1.4 : ℝ) ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le (by norm_num)
      linarith
    nlinarith
  linarith

/-- **`21 ≤ 10^{4/3}`**。 -/
lemma twenty_one_le_ten_rpow : (21 : ℝ) ≤ (10 : ℝ) ^ (4 / 3 : ℝ) := by
  have h1 : (21 : ℝ) = ((21 : ℝ) ^ 3) ^ (1 / 3 : ℝ) := by
    rw [← Real.rpow_natCast (21 : ℝ) 3, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 21)]
    norm_num
  rw [h1]
  have h2 : ((21 : ℝ) ^ 3) ≤ (10 : ℝ) ^ 4 := by norm_num
  have h3 := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (21 : ℝ) ^ 3) h2
    (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have h4 : ((10 : ℝ) ^ 4) ^ (1 / 3 : ℝ) = (10 : ℝ) ^ (4 / 3 : ℝ) := by
    rw [← Real.rpow_natCast (10 : ℝ) 4, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 10)]
    norm_num
  rwa [h4] at h3

/-- **`1 ≤ log q`**（`q ≥ 10^{10}`）。 -/
lemma one_le_log_of_ten_pow {q : ℝ} (hq : (10 : ℝ) ^ 10 ≤ q) : 1 ≤ Real.log q := by
  have h2 : (1 : ℝ) ≤ Real.log 10 := by
    rw [Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 10)]
    exact le_of_lt (lt_trans Real.exp_one_lt_three (by norm_num))
  have h1 : (1 : ℝ) ≤ Real.log ((10 : ℝ) ^ 10) := by
    rw [Real.log_pow]
    push_cast
    linarith
  exact le_trans h1 (Real.log_le_log (by positivity) hq)

/-- **侧条件 `k²·√ε ≤ τ`**：`k = 2N+1`、`q = 2N+2 ≥ 10^{10}`、`a ≥ 2`、
`τ ≤ ρ_a(q)·q`、`τ ≥ q/e`（初等下界）时成立。 -/
lemma ksq_sqrt_epsOf_le {a q τ : ℝ} {N : ℕ}
    (hq : (10 : ℝ) ^ 10 ≤ q) (hqdef : q = 2 * (N : ℝ) + 2)
    (ha : 2 ≤ a) (hat : a * (Real.log q / q) ^ (2 / 3 : ℝ) ≤ 1 / 4)
    (hτ0 : 0 ≤ τ) (hτρ : τ ≤ rhoA a q * q) (hτlow : q / Real.exp 1 ≤ τ) :
    ((2 * N + 1 : ℕ) : ℝ) ^ 2 * Real.sqrt (epsOf τ (deltaOf (rhoA a q)) (2 * N + 1)) ≤ τ := by
  set k : ℕ := 2 * N + 1 with hkdef
  set ρ : ℝ := rhoA a q with hρdef
  set δ' : ℝ := deltaOf ρ with hδ'def
  have hq4 : (10 : ℝ) ^ 4 ≤ q := by
    have h : (0 : ℝ) < (10 : ℝ) ^ 10 := by norm_num
    linarith
  have hq0 : 0 < q := by
    have h : (0 : ℝ) < (10 : ℝ) ^ 10 := by norm_num
    linarith
  have hq1 : 1 ≤ q := by linarith
  have hl : 0 < Real.log q := Real.log_pos (by linarith)
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
  have hlog1 : (1 : ℝ) ≤ Real.log q := one_le_log_of_ten_pow hq
  have h16 : (q / Real.log q) ^ (1 / 6 : ℝ) ≤ q ^ (1 / 6 : ℝ) := by
    rw [Real.div_rpow hq0.le hl.le, div_le_iff₀ (Real.rpow_pos_of_pos hl _)]
    have h1 : (1 : ℝ) ≤ (Real.log q) ^ (1 / 6 : ℝ) := Real.one_le_rpow hlog1 (by norm_num)
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
  have hmain : 5 * a ^ (-(1 / 4 : ℝ)) * q ^ (13 / 6 - effS a / 2) ≤ q / Real.exp 1 := by
    have ha14 : a ^ (-(1 / 4 : ℝ)) ≤ 1 := by
      rw [Real.rpow_neg (by linarith : (0 : ℝ) ≤ a)]
      rw [inv_le_one₀ (Real.rpow_pos_of_pos ha0 _)]
      exact Real.one_le_rpow (by linarith) (by norm_num)
    have hexp2 : (2 : ℝ) / 15 ≤ effS a / 2 - 7 / 6 := by linarith [hs]
    have h1 : q ^ ((2 : ℝ) / 15) ≤ q ^ (effS a / 2 - 7 / 6) :=
      Real.rpow_le_rpow_of_exponent_le hq1 hexp2
    have h2 : (10 : ℝ) ^ (4 / 3 : ℝ) ≤ q ^ ((2 : ℝ) / 15) := by
      have h3 : ((10 : ℝ) ^ 10) ^ ((2 : ℝ) / 15) ≤ q ^ ((2 : ℝ) / 15) :=
        Real.rpow_le_rpow (by positivity) hq (by norm_num)
      have h4 : ((10 : ℝ) ^ 10) ^ ((2 : ℝ) / 15) = (10 : ℝ) ^ (4 / 3 : ℝ) := by
        rw [← Real.rpow_natCast (10 : ℝ) 10, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 10)]
        norm_num
      rwa [h4] at h3
    have hq15 : (15 : ℝ) ≤ q ^ (effS a / 2 - 7 / 6) :=
      le_trans (le_trans (by norm_num : (15 : ℝ) ≤ 21) (le_trans twenty_one_le_ten_rpow h2)) h1
    have hle : 5 * Real.exp 1 * a ^ (-(1 / 4 : ℝ)) ≤ q ^ (effS a / 2 - 7 / 6) := by
      have h5 : 5 * Real.exp 1 * a ^ (-(1 / 4 : ℝ)) ≤ 15 := by
        have h1 : Real.exp 1 ≤ 3 := le_of_lt Real.exp_one_lt_three
        nlinarith [ha14, Real.exp_pos 1]
      linarith
    rw [le_div_iff₀ (Real.exp_pos 1)]
    have hprod : q ^ (effS a / 2 - 7 / 6) * q ^ (13 / 6 - effS a / 2) = q := by
      rw [← Real.rpow_add hq0,
        show effS a / 2 - 7 / 6 + (13 / 6 - effS a / 2) = 1 by ring, Real.rpow_one]
    have h3 : 0 ≤ q ^ (13 / 6 - effS a / 2) := Real.rpow_nonneg hq0.le _
    have h4 : 5 * a ^ (-(1 / 4 : ℝ)) * Real.exp 1 * q ^ (13 / 6 - effS a / 2)
        ≤ q ^ (effS a / 2 - 7 / 6) * q ^ (13 / 6 - effS a / 2) := by
      calc 5 * a ^ (-(1 / 4 : ℝ)) * Real.exp 1 * q ^ (13 / 6 - effS a / 2)
          = (5 * Real.exp 1 * a ^ (-(1 / 4 : ℝ))) * q ^ (13 / 6 - effS a / 2) := by ring
        _ ≤ q ^ (effS a / 2 - 7 / 6) * q ^ (13 / 6 - effS a / 2) :=
            mul_le_mul_of_nonneg_right hle h3
    rw [hprod] at h4
    calc 5 * a ^ (-(1 / 4 : ℝ)) * q ^ (13 / 6 - effS a / 2) * Real.exp 1
        = 5 * a ^ (-(1 / 4 : ℝ)) * Real.exp 1 * q ^ (13 / 6 - effS a / 2) := by ring
      _ ≤ q := h4
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
    _ ≤ q / Real.exp 1 := hmain
    _ ≤ τ := hτlow

/-! ## §4 数论收尾：三项 `< 1/64` -/

/-- 数论收尾用的指数：`E = max(β + 2/3 - 2s, 3/2 - 3s/2)`，`s = effS a`。 -/
noncomputable def effE (a : ℝ) (β : ℕ) : ℝ :=
  max ((β : ℝ) + 2 / 3 - 2 * effS a) (3 / 2 - 3 * effS a / 2)

/-- 数论收尾用的常数。 -/
noncomputable def effK1 (Cd1 Cd2 K a : ℝ) : ℝ :=
  (1 / 36) * (1 + Cd1) * (2704 * Cd2 / a + 5408 * K * Cd1 / a + 752 * K * a ^ (-(3 / 4 : ℝ)))

/-- 半径阈值：`q` 超过它就保证三项之和 `< 1/64`。 -/
noncomputable def effQ0 (Cd1 Cd2 K a : ℝ) (β : ℕ) : ℝ :=
  max (512 * a ^ 3) ((64 * effK1 Cd1 Cd2 K a) ^ (1 / (-(effE a β))))

/-- **显式 `N₀`**（阶数阈值）。 -/
noncomputable def effN0 (Cd1 Cd2 K a : ℝ) (β : ℕ) : ℕ :=
  max 5000000000 (max (Nat.ceil (256 * a ^ 3)) (Nat.ceil (effQ0 Cd1 Cd2 K a β / 2)))

lemma effE_neg {a : ℝ} (ha : 2 ≤ a) {β : ℕ} (hβ : β ≤ 4) : effE a β < 0 := by
  have hs := effS_ge ha
  have hβ4 : (β : ℝ) ≤ 4 := by exact_mod_cast hβ
  rw [effE]
  refine max_lt ?_ ?_
  · linarith
  · linarith

lemma effK1_pos {Cd1 Cd2 K a : ℝ} (hCd1 : 0 < Cd1) (hCd2 : 0 < Cd2) (hK : 0 < K)
    (ha : 0 < a) : 0 < effK1 Cd1 Cd2 K a := by
  rw [effK1]
  have h1 : (0 : ℝ) < 2704 * Cd2 / a := by positivity
  have h2 : (0 : ℝ) < 5408 * K * Cd1 / a := by positivity
  have h3 : (0 : ℝ) < 752 * K * a ^ (-(3 / 4 : ℝ)) := by positivity
  have h4 : (0 : ℝ) < 1 + Cd1 := by linarith
  positivity

/-- **数论收尾**：三项之和乘上 `(1/36)(1+Cd1)` 后 `< 1/64`。 -/
lemma final_arith {Cd1 Cd2 K a q ε : ℝ} {β : ℕ}
    (hCd1 : 0 < Cd1) (hCd2 : 0 < Cd2) (hK : 0 < K) (ha : 0 < a) (hβ : 2 ≤ β)
    (hq1 : 1 ≤ q) (hε0 : 0 ≤ ε)
    (hε : ε ≤ 13 * a ^ (-(1 / 2 : ℝ)) * q ^ (1 / 3 - effS a))
    (hqE : 64 * effK1 Cd1 Cd2 K a < q ^ (-(effE a β))) :
    (1 / 36) * (1 + Cd1) * (16 * Cd2 * q ^ (β : ℝ) * ε ^ 2
        + 32 * K * Cd1 * q ^ (2 : ℝ) * ε ^ 2 + 16 * K * q * ε ^ (3 / 2 : ℝ)) < 1 / 64 := by
  have hq0 : 0 < q := lt_of_lt_of_le one_pos hq1
  set u : ℝ := 1 / 3 - effS a with hudef
  have hX0 : 0 ≤ 13 * a ^ (-(1 / 2 : ℝ)) * q ^ u := by positivity
  -- `ε²` 与 `ε^{3/2}` 的界
  have hε2 : ε ^ 2 ≤ 169 * a ^ (-(1 : ℝ)) * q ^ (2 * u) := by
    have h1 : ε ^ 2 ≤ (13 * a ^ (-(1 / 2 : ℝ)) * q ^ u) ^ 2 := pow_le_pow_left₀ hε0 hε 2
    have h2 : (13 * a ^ (-(1 / 2 : ℝ)) * q ^ u) ^ 2 = 169 * a ^ (-(1 : ℝ)) * q ^ (2 * u) := by
      rw [show (13 * a ^ (-(1 / 2 : ℝ)) * q ^ u) ^ 2
          = 169 * (a ^ (-(1 / 2 : ℝ))) ^ 2 * (q ^ u) ^ 2 by ring,
        show (a ^ (-(1 / 2 : ℝ))) ^ 2 = a ^ (-(1 : ℝ)) by
          rw [← Real.rpow_natCast (a ^ (-(1 / 2 : ℝ))) 2, ← Real.rpow_mul ha.le]; norm_num,
        show (q ^ u) ^ 2 = q ^ (2 * u) by
          rw [← Real.rpow_natCast (q ^ u) 2, ← Real.rpow_mul hq0.le]; ring]
    linarith [h1, h2.le]
  have hε32 : ε ^ (3 / 2 : ℝ) ≤ 47 * a ^ (-(3 / 4 : ℝ)) * q ^ (3 * u / 2) := by
    have h1 : ε ^ (3 / 2 : ℝ) ≤ (13 * a ^ (-(1 / 2 : ℝ)) * q ^ u) ^ (3 / 2 : ℝ) :=
      Real.rpow_le_rpow hε0 hε (by norm_num)
    have h2 : (13 * a ^ (-(1 / 2 : ℝ)) * q ^ u) ^ (3 / 2 : ℝ)
        = 13 ^ (3 / 2 : ℝ) * a ^ (-(3 / 4 : ℝ)) * q ^ (3 * u / 2) := by
      have hY : (0 : ℝ) ≤ 13 * a ^ (-(1 / 2 : ℝ)) := by positivity
      rw [show 13 * a ^ (-(1 / 2 : ℝ)) * q ^ u = (13 * a ^ (-(1 / 2 : ℝ))) * q ^ u by ring,
        Real.mul_rpow hY (Real.rpow_nonneg hq0.le u),
        show (13 * a ^ (-(1 / 2 : ℝ))) ^ (3 / 2 : ℝ)
            = 13 ^ (3 / 2 : ℝ) * a ^ (-(3 / 4 : ℝ)) by
          rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 13) (Real.rpow_nonneg ha.le _),
            ← Real.rpow_mul ha.le]
          norm_num,
        show (q ^ u) ^ (3 / 2 : ℝ) = q ^ (3 * u / 2) by
          rw [← Real.rpow_mul hq0.le]
          ring_nf]
    have h3 : (13 : ℝ) ^ (3 / 2 : ℝ) ≤ (47 : ℝ) := by
      have h4 : (13 : ℝ) ^ (3 / 2 : ℝ) = 13 * Real.sqrt 13 := by
        rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (by norm_num),
          Real.rpow_one, Real.sqrt_eq_rpow]
      rw [h4]
      have h5 : Real.sqrt 13 ≤ (361 : ℝ) / 100 := by
        have h6 : Real.sqrt 13 ≤ Real.sqrt (((361 : ℝ) / 100) ^ 2) :=
          Real.sqrt_le_sqrt (by norm_num)
        rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 361 / 100)] at h6
      nlinarith
    calc ε ^ (3 / 2 : ℝ) ≤ (13 : ℝ) ^ (3 / 2 : ℝ) * a ^ (-(3 / 4 : ℝ)) * q ^ (3 * u / 2) := by
          rw [← h2]; exact h1
      _ ≤ 47 * a ^ (-(3 / 4 : ℝ)) * q ^ (3 * u / 2) := by
          have h6 : 0 ≤ a ^ (-(3 / 4 : ℝ)) * q ^ (3 * u / 2) := by positivity
          nlinarith [h3, h6]
  -- 三项各自的界
  have hE1 : (β : ℝ) + 2 / 3 - 2 * effS a ≤ effE a β := le_max_left _ _
  have hE2 : (3 : ℝ) / 2 - 3 * effS a / 2 ≤ effE a β := le_max_right _ _
  have hE3 : (8 : ℝ) / 3 - 2 * effS a ≤ effE a β := by
    refine le_trans ?_ hE1
    have hβ' : (2 : ℝ) ≤ β := by exact_mod_cast hβ
    linarith
  have hexp1 : (β : ℝ) + 2 * u = (β : ℝ) + 2 / 3 - 2 * effS a := by rw [hudef]; ring
  have hexp2 : (2 : ℝ) + 2 * u = 8 / 3 - 2 * effS a := by rw [hudef]; ring
  have hexp3 : (1 : ℝ) + 3 * u / 2 = 3 / 2 - 3 * effS a / 2 := by rw [hudef]; ring
  have hterm1 : 16 * Cd2 * q ^ (β : ℝ) * ε ^ 2
      ≤ 2704 * Cd2 / a * q ^ (effE a β) := by
    have h1 : 16 * Cd2 * q ^ (β : ℝ) * ε ^ 2
        ≤ 16 * Cd2 * q ^ (β : ℝ) * (169 * a ^ (-(1 : ℝ)) * q ^ (2 * u)) := by
      have h2 : 0 ≤ 16 * Cd2 * q ^ (β : ℝ) := by positivity
      exact mul_le_mul_of_nonneg_left hε2 h2
    have h3 : 16 * Cd2 * q ^ (β : ℝ) * (169 * a ^ (-(1 : ℝ)) * q ^ (2 * u))
        = 2704 * Cd2 / a * q ^ ((β : ℝ) + 2 * u) := by
      rw [Real.rpow_add hq0, Real.rpow_neg ha.le, Real.rpow_one]
      field_simp
      ring
    rw [h3, hexp1] at h1
    refine h1.trans ?_
    have h4 : 0 ≤ 2704 * Cd2 / a := by positivity
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hq1 hE1) h4
  have hterm2 : 32 * K * Cd1 * q ^ (2 : ℝ) * ε ^ 2
      ≤ 5408 * K * Cd1 / a * q ^ (effE a β) := by
    have h1 : 32 * K * Cd1 * q ^ (2 : ℝ) * ε ^ 2
        ≤ 32 * K * Cd1 * q ^ (2 : ℝ) * (169 * a ^ (-(1 : ℝ)) * q ^ (2 * u)) := by
      have h2 : 0 ≤ 32 * K * Cd1 * q ^ (2 : ℝ) := by positivity
      exact mul_le_mul_of_nonneg_left hε2 h2
    have h3 : 32 * K * Cd1 * q ^ (2 : ℝ) * (169 * a ^ (-(1 : ℝ)) * q ^ (2 * u))
        = 5408 * K * Cd1 / a * q ^ ((2 : ℝ) + 2 * u) := by
      rw [Real.rpow_add hq0, Real.rpow_neg ha.le, Real.rpow_one]
      field_simp
      ring
    rw [h3, hexp2] at h1
    refine h1.trans ?_
    have h4 : 0 ≤ 5408 * K * Cd1 / a := by positivity
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hq1 hE3) h4
  have hterm3 : 16 * K * q * ε ^ (3 / 2 : ℝ) ≤ 752 * K * a ^ (-(3 / 4 : ℝ)) * q ^ (effE a β) := by
    have h1 : 16 * K * q * ε ^ (3 / 2 : ℝ)
        ≤ 16 * K * q * (47 * a ^ (-(3 / 4 : ℝ)) * q ^ (3 * u / 2)) := by
      have h2 : 0 ≤ 16 * K * q := by positivity
      exact mul_le_mul_of_nonneg_left hε32 h2
    have h3 : 16 * K * q * (47 * a ^ (-(3 / 4 : ℝ)) * q ^ (3 * u / 2))
        = 752 * K * a ^ (-(3 / 4 : ℝ)) * q ^ (1 + 3 * u / 2) := by
      rw [Real.rpow_add hq0, Real.rpow_one]
      ring
    rw [h3, hexp3] at h1
    refine h1.trans ?_
    have h4 : 0 ≤ 752 * K * a ^ (-(3 / 4 : ℝ)) := by positivity
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hq1 hE2) h4
  -- 合并
  have hsum : 16 * Cd2 * q ^ (β : ℝ) * ε ^ 2 + 32 * K * Cd1 * q ^ (2 : ℝ) * ε ^ 2
      + 16 * K * q * ε ^ (3 / 2 : ℝ)
      ≤ (2704 * Cd2 / a + 5408 * K * Cd1 / a + 752 * K * a ^ (-(3 / 4 : ℝ))) * q ^ (effE a β) := by
    have h5 : (0 : ℝ) ≤ q ^ (effE a β) := Real.rpow_nonneg hq0.le _
    have h6 : 2704 * Cd2 / a * q ^ (effE a β) + 5408 * K * Cd1 / a * q ^ (effE a β)
        + 752 * K * a ^ (-(3 / 4 : ℝ)) * q ^ (effE a β)
        = (2704 * Cd2 / a + 5408 * K * Cd1 / a + 752 * K * a ^ (-(3 / 4 : ℝ))) * q ^ (effE a β) := by
      ring
    linarith [hterm1, hterm2, hterm3, h6]
  have hfac : (1 / 36) * (1 + Cd1)
      * (2704 * Cd2 / a + 5408 * K * Cd1 / a + 752 * K * a ^ (-(3 / 4 : ℝ)))
      = effK1 Cd1 Cd2 K a := by
    rw [effK1]; try ring
  have hprod : (1 / 36) * (1 + Cd1)
      * ((2704 * Cd2 / a + 5408 * K * Cd1 / a + 752 * K * a ^ (-(3 / 4 : ℝ))) * q ^ (effE a β))
      = effK1 Cd1 Cd2 K a * q ^ (effE a β) := by
    rw [← hfac]; ring
  have hcoef : 0 ≤ (1 / 36 : ℝ) * (1 + Cd1) := by positivity
  have hfinal : effK1 Cd1 Cd2 K a * q ^ (effE a β) < 1 / 64 := by
    have h1 : effK1 Cd1 Cd2 K a < q ^ (-(effE a β)) / 64 := by linarith [hqE]
    have h2 : q ^ (-(effE a β)) / 64 * q ^ (effE a β) = 1 / 64 := by
      rw [div_mul_eq_mul_div, ← Real.rpow_add hq0,
        show -(effE a β) + effE a β = 0 by ring, Real.rpow_zero]
      try norm_num
    calc effK1 Cd1 Cd2 K a * q ^ (effE a β)
        < q ^ (-(effE a β)) / 64 * q ^ (effE a β) :=
          mul_lt_mul_of_pos_right h1 (Real.rpow_pos_of_pos hq0 _)
      _ = 1 / 64 := h2
  calc (1 / 36) * (1 + Cd1) * (16 * Cd2 * q ^ (β : ℝ) * ε ^ 2
        + 32 * K * Cd1 * q ^ (2 : ℝ) * ε ^ 2 + 16 * K * q * ε ^ (3 / 2 : ℝ))
      ≤ (1 / 36) * (1 + Cd1)
        * ((2704 * Cd2 / a + 5408 * K * Cd1 / a + 752 * K * a ^ (-(3 / 4 : ℝ))) * q ^ (effE a β)) :=
        mul_le_mul_of_nonneg_left hsum hcoef
    _ = effK1 Cd1 Cd2 K a * q ^ (effE a β) := hprod
    _ < 1 / 64 := hfinal

/-! ## §5 sharp collar 界的接口 -/

/-- **workstream A 的 sharp collar 界**（作为接口假设）：

对每个 admissible 构造（`τ = (Σθ)/2`、`q = 2N+2`、`k = 2N+1`、`ρ = ρ_a(q)`、
`δ' = δ'(ρ)`、`ε = epsOf τ δ' k`、`B = √ε`、`P = scaledApprox τ k`），
存在 `M₁, M₂ ≥ 0` 使 `‖Ψ'‖ ≤ M₁`、`‖Ψ''‖ ≤ M₂` 在 collar `|μ| ≤ τ + B` 上成立，且

```
τ·M₁ ≤ Cd1·k²·ε,        τ²·M₂ ≤ Cd2·k^β·ε.
``` -/
noncomputable def SharpCollar (Cd1 Cd2 a : ℝ) (β : ℕ) : Prop :=
  ∀ {N : ℕ} {L : ℕ} {α θ : Fin L → ℝ}, Admissible N Real.pi L α θ →
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

/-! ## §6 端点小性：由 `C₁C₂ < ((1-cos(φ/2))/8)²` 得 `h(0) < 1-cos(φ/2)` -/

/-- **端点小性（严格版）**：`C₁C₂ < ((1-cos(φ/2))/8)²` 即可 —— `FinalSmall` 的 `η` 是自由的，
取足够小即可。 -/
lemma h_zero_lt_of_prod_lt {N : ℕ} {φ : ℝ} {L : ℕ} {α θ : Fin L → ℝ}
    (hφ0 : 0 < φ) (hφπ : φ ≤ Real.pi) (hAdm : Admissible N φ L α θ) {δ' : ℝ} (hδ' : 0 < δ')
    (hprod : kernelA ((∑ j, θ j) / 2) (Real.sqrt (epsOf ((∑ j, θ j) / 2) δ' (2 * N + 1)))
        (scaledApprox ((∑ j, θ j) / 2) (2 * N + 1))
      * kernelC ((∑ j, θ j) / 2) (Real.sqrt (epsOf ((∑ j, θ j) / 2) δ' (2 * N + 1)))
        (scaledApprox ((∑ j, θ j) / 2) (2 * N + 1))
      < ((1 - Real.cos (φ / 2)) / 8) ^ 2) :
    h L α θ 0 < 1 - Real.cos (φ / 2) := by
  set δc : ℝ := 1 - Real.cos (φ / 2) with hδc
  have hδcpos : 0 < δc := one_sub_cos_half_pos hφ0 hφπ
  set A : ℝ := kernelA ((∑ j, θ j) / 2) (Real.sqrt (epsOf ((∑ j, θ j) / 2) δ' (2 * N + 1)))
        (scaledApprox ((∑ j, θ j) / 2) (2 * N + 1))
      * kernelC ((∑ j, θ j) / 2) (Real.sqrt (epsOf ((∑ j, θ j) / 2) δ' (2 * N + 1)))
        (scaledApprox ((∑ j, θ j) / 2) (2 * N + 1)) with hA
  have hden : 0 < (δc / 8) ^ 2 := by positivity
  have hAδ : A < (δc / 8) ^ 2 := by rw [hA, hδc]; exact hprod
  set r : ℝ := A / (δc / 8) ^ 2 with hr
  have hr1 : r < 1 := (div_lt_one hden).mpr hAδ
  set q : ℝ := 2 * (N : ℝ) + 2 with hq
  have hqpos : 0 < q := by rw [hq]; positivity
  set η : ℝ := (1 - r) / (2 * q) with hη
  have hηpos : 0 < η := by rw [hη]; positivity
  have hexp : r ≤ Real.exp (-η * q) := by
    have h1 : -η * q = -((1 - r) / 2) := by rw [hη]; field_simp
    rw [h1]
    have h2 : r ≤ 1 - (1 - r) / 2 := by linarith
    have h3 : 1 - (1 - r) / 2 ≤ Real.exp (-((1 - r) / 2)) := by
      have h4 : -((1 - r) / 2) ≠ 0 := by
        intro hh
        have : r = 1 := by linarith
        linarith
      have h5 := Real.add_one_lt_exp h4
      linarith
    linarith
  have hker : A ≤ (δc / 8) ^ 2 * Real.exp (-η * (2 * (N : ℝ) + 2)) := by
    have h1 : r * (δc / 8) ^ 2 = A := by rw [hr]; field_simp
    have h2 := mul_le_mul_of_nonneg_right hexp hden.le
    rw [h1] at h2
    simpa [hq, mul_comm] using h2
  have hmain := h_zero_lt_of_kernel_decay hφ0 hφπ hAdm hδ' hηpos ?_
  · rwa [← hδc] at hmain
  · have hk := hker
    rw [hδc] at hk
    exact hk

/-! ## §7 主定理（显式 `N₀`） -/

/-- **端到端有效定理（显式 `N₀`）**：`a ≥ 2`、`β ∈ [2,4]`、`K ≥ K₀ = 21.1`，
sharp collar 界成立时，对一切 `N ≥ effN0 Cd1 Cd2 K a β` 与一切 admissible 构造，
`4(N+1)(1 - a(log q/q)^{2/3}) ≤ cost θ`（`q = 2N+2`）。 -/
theorem effective_bound_of_sharp (Cd1 Cd2 K a : ℝ) (β : ℕ)
    (hCd1 : 0 < Cd1) (hCd2 : 0 < Cd2) (hK : K₀ ≤ K) (ha : 2 ≤ a)
    (hβ : 2 ≤ β) (hβ4 : β ≤ 4) (hsharp : SharpCollar Cd1 Cd2 a β) :
    ∀ N ≥ effN0 Cd1 Cd2 K a β, ∀ {L : ℕ} {α θ : Fin L → ℝ}, Admissible N Real.pi L α θ →
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
  have hN5 : 5000000000 ≤ N := le_trans (le_max_left _ _) hN
  have hNa : Nat.ceil (256 * a ^ 3) ≤ N :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hN)
  have hNq : Nat.ceil (effQ0 Cd1 Cd2 K a β / 2) ≤ N :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hN)
  have hq10 : (10 : ℝ) ^ 10 ≤ q := by
    have h1 : (5000000000 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN5
    have h2 : (10 : ℝ) ^ 10 = 10000000000 := by norm_num
    rw [hqdef, h2]; push_cast; linarith
  have hq512 : 512 * a ^ 3 ≤ q := by
    have h1 : (256 * a ^ 3 : ℝ) ≤ (Nat.ceil (256 * a ^ 3) : ℝ) := Nat.le_ceil _
    have h2 : (Nat.ceil (256 * a ^ 3) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNa
    rw [hqdef]; push_cast; linarith
  have hq0 : 0 < q := by linarith [hq10]
  have hq1 : 1 ≤ q := by linarith [hq10]
  have ha0 : 0 < a := by linarith
  have hKpos : 0 < K := lt_of_lt_of_le K₀_pos hK
  have hlog1 : (1 : ℝ) ≤ Real.log q := one_le_log_of_ten_pow hq10
  have hl : 0 < Real.log q := by linarith
  -- `a·t ≤ 1/4`
  have hat : a * (Real.log q / q) ^ (2 / 3 : ℝ) ≤ 1 / 4 := by
    have hlog : Real.log q ≤ 2 * Real.sqrt q := log_le_two_sqrt q hq1
    have hsq : 0 < Real.sqrt q := Real.sqrt_pos_of_pos hq0
    have hdiv : Real.log q / q ≤ 2 / Real.sqrt q := by
      rw [div_le_div_iff₀ hq0 hsq]
      have h := mul_le_mul_of_nonneg_right hlog (Real.sqrt_nonneg q)
      nlinarith [Real.sq_sqrt hq0.le]
    have ht : (Real.log q / q) ^ (2 / 3 : ℝ) ≤ (2 / Real.sqrt q) ^ (2 / 3 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hdiv (by norm_num)
    have h2 : (2 / Real.sqrt q) ^ (2 / 3 : ℝ) = 2 ^ (2 / 3 : ℝ) * q ^ (-(1 / 3 : ℝ)) := by
      rw [Real.div_rpow (by norm_num : (0 : ℝ) ≤ 2) (Real.sqrt_nonneg q), Real.sqrt_eq_rpow,
        ← Real.rpow_mul hq0.le]
      norm_num
      rw [Real.rpow_neg hq0.le, div_eq_mul_inv]
    have hq13 : 8 * a ≤ q ^ (1 / 3 : ℝ) := by
      have h1 : (512 * a ^ 3) ^ (1 / 3 : ℝ) ≤ q ^ (1 / 3 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hq512 (by norm_num)
      have h2 : (512 * a ^ 3) ^ (1 / 3 : ℝ) = 8 * a := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 512) (by positivity : (0 : ℝ) ≤ a ^ 3),
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
      nlinarith [hq13, ha0, h5]
    have h4 : a * (Real.log q / q) ^ (2 / 3 : ℝ) ≤ a * (2 ^ (2 / 3 : ℝ) * q ^ (-(1 / 3 : ℝ))) := by
      rw [← h2]
      exact mul_le_mul_of_nonneg_left ht ha0.le
    linarith [h4, h3]
  obtain ⟨h34, hlt1, hρ0, hρ12⟩ :=
    rhoA_bounds (by linarith [hq10] : (10 : ℝ) ^ 4 ≤ q) ha0 hat
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
  obtain ⟨M₁, M₂, hM₁nn, hM₂nn, hA1, hA2, hM1sh, hM2sh⟩ := hsharp hAdm
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
    have h := ksq_sqrt_epsOf_le (a := a) (q := q) (τ := τ) (N := N) hq10 hqdef ha hat hτ0 hτρ hτlow
    have h2 : ((k : ℕ) : ℝ) ^ 2 * B
        = ((2 * N + 1 : ℕ) : ℝ) ^ 2
          * Real.sqrt (epsOf τ (deltaOf (rhoA a q)) (2 * N + 1)) := by
      rw [hkdef, hBdef, hεdef, hδ'def, hρdef]
    rw [h2]; exact h
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
  have hτq : τ ≤ q := by nlinarith [hτρ, hρ0, hlt1, hq0]
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
      exact D0_mu_le (by linarith [hq10] : (10 : ℝ) ^ 4 ≤ q) ha0 hat
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

/-- **`∃ N₀` 形式**（题目要求的签名形状）。 -/
theorem effective_bound_of_sharp_exists (Cd1 Cd2 K a : ℝ) (β : ℕ)
    (hCd1 : 0 < Cd1) (hCd2 : 0 < Cd2) (hK : K₀ ≤ K) (ha : 2 ≤ a)
    (hβ : 2 ≤ β) (hβ4 : β ≤ 4) (hsharp : SharpCollar Cd1 Cd2 a β) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {L : ℕ} {α θ : Fin L → ℝ}, Admissible N Real.pi L α θ →
      4 * ((N : ℝ) + 1)
        * (1 - a * (Real.log (2 * (N : ℝ) + 2) / (2 * (N : ℝ) + 2)) ^ (2 / 3 : ℝ))
        ≤ cost θ :=
  ⟨effN0 Cd1 Cd2 K a β,
    effective_bound_of_sharp Cd1 Cd2 K a β hCd1 hCd2 hK ha hβ hβ4 hsharp⟩

/-! ## §8 全 `N` 形式（与初等下界合并） -/

/-- **全 `N` 形式**：对一切 `N ≥ 1`，admissible 构造的代价不小于
`max (2(q!)^{1/q}) (若 q ≥ q₀ 则 4(N+1)(1-a(log q/q)^{2/3}) 否则 0)`，
`q = 2N+2`、`q₀ = 2·effN0 + 2`。 -/
theorem all_N_bound (Cd1 Cd2 K a : ℝ) (β : ℕ)
    (hCd1 : 0 < Cd1) (hCd2 : 0 < Cd2) (hK : K₀ ≤ K) (ha : 2 ≤ a)
    (hβ : 2 ≤ β) (hβ4 : β ≤ 4) (hsharp : SharpCollar Cd1 Cd2 a β) :
    ∀ N ≥ 1, ∀ {L : ℕ} {α θ : Fin L → ℝ}, Admissible N Real.pi L α θ →
      max (2 * (Nat.factorial (2 * N + 2) : ℝ) ^ (1 / ((2 * N + 2 : ℕ) : ℝ)))
          (if 2 * (effN0 Cd1 Cd2 K a β : ℝ) + 2 ≤ 2 * (N : ℝ) + 2
            then 4 * ((N : ℝ) + 1)
              * (1 - a * (Real.log (2 * (N : ℝ) + 2) / (2 * (N : ℝ) + 2)) ^ (2 / 3 : ℝ))
            else 0)
        ≤ cost θ := by
  intro N hN L α θ hAdm
  refine max_le ?_ ?_
  · exact elementary_bound_pi hAdm
  · by_cases hcase : 2 * (effN0 Cd1 Cd2 K a β : ℝ) + 2 ≤ 2 * (N : ℝ) + 2
    · rw [if_pos hcase]
      have hle : effN0 Cd1 Cd2 K a β ≤ N := by
        by_contra hc
        push_neg at hc
        have hc' : (N : ℝ) < (effN0 Cd1 Cd2 K a β : ℝ) := by exact_mod_cast hc
        linarith
      exact effective_bound_of_sharp Cd1 Cd2 K a β hCd1 hCd2 hK ha hβ hβ4 hsharp N hle hAdm
    · rw [if_neg hcase]
      exact Finset.sum_nonneg fun j _ => hAdm.1 j

end RobustZ
