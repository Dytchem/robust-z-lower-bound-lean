import RobustZ.KernelDecay
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# `CollarTail`：collar 上「误差 + 一阶导 + 二阶导」的尾部估计

本文件把 `KernelDecay.hasSum_fcoef_cosh`（collar 上的 Jacobi–Anger 尾部恒等式）

`e^{-iτ cosh w} = Σ_{n∈ℤ} c_n e^{-nw}`  （`0 < w < δ`）

整理成**有抵消**的尾部估计（`Approx.norm_tail_le` 的 collar 版）。
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RobustZ

open Filter MeasureTheory
open scoped Real Topology

/-! ## 1. 记号 -/

/-- 第 `j` 阶导数级数的项 `(-n)^j c_n e^{-nw}`（`c_n = fcoef τ n`）。 -/
def Gcoef (τ : ℝ) (j : ℕ) (w : ℝ) (n : ℤ) : ℂ :=
  (-(n : ℂ)) ^ j * fcoef τ n * Complex.exp (-(n : ℂ) * (w : ℂ))

/-- 频率 `{0,…,k-1} ∪ {-1,…,-k}` 上的有限和。 -/
def finitePart (τ : ℝ) (j : ℕ) (w : ℝ) (k : ℕ) : ℂ :=
  ∑ n ∈ Finset.range k, (Gcoef τ j w (n : ℤ) + Gcoef τ j w (-(n : ℤ) - 1))

/-- 频率 `|n| ≥ k` 上的尾部。 -/
def tailPart (τ : ℝ) (j : ℕ) (w : ℝ) (k : ℕ) : ℂ :=
  ∑' n : ℕ, (Gcoef τ j w (((n + k : ℕ)) : ℤ) + Gcoef τ j w (-(((n + k : ℕ)) : ℤ) - 1))

@[simp] lemma Gcoef_zero_apply (τ : ℝ) (w : ℝ) (n : ℤ) :
    Gcoef τ 0 w n = fcoef τ n * Complex.exp (-(n : ℂ) * (w : ℂ)) := by
  simp [Gcoef]

@[simp] lemma Gcoef_one_apply (τ : ℝ) (w : ℝ) (n : ℤ) :
    Gcoef τ 1 w n = -(n : ℂ) * fcoef τ n * Complex.exp (-(n : ℂ) * (w : ℂ)) := by
  simp [Gcoef]

@[simp] lemma Gcoef_two_apply (τ : ℝ) (w : ℝ) (n : ℤ) :
    Gcoef τ 2 w n = (n : ℂ) ^ 2 * fcoef τ n * Complex.exp (-(n : ℂ) * (w : ℂ)) := by
  simp only [Gcoef, pow_two]
  ring

/-- 负指标的改写（用 `fcoef` 的偶性）。 -/
lemma Gcoef_neg_eq (τ : ℝ) (j : ℕ) (w : ℝ) (M : ℤ) :
    Gcoef τ j w (-M) = (M : ℂ) ^ j * fcoef τ M * Complex.exp ((M : ℂ) * (w : ℂ)) := by
  simp only [Gcoef, fcoef_neg]
  rw [show -(((-M : ℤ)) : ℂ) = (M : ℂ) from by push_cast; ring]

/-! ## 2. 一般工具 -/

lemma norm_exp_neg_mul (n : ℤ) (w : ℝ) :
    ‖Complex.exp (-(n : ℂ) * (w : ℂ))‖ = Real.exp (-(n : ℝ) * w) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]

lemma norm_exp_mul (z : ℂ) (w : ℝ) :
    ‖Complex.exp (z * (w : ℂ))‖ = Real.exp (z.re * w) := by
  rw [Complex.norm_exp, Complex.mul_re]
  simp

lemma exp_neg_mul_eq_pow (k : ℕ) (x : ℝ) :
    Real.exp (-(k : ℝ) * x) = Real.exp (-x) ^ k := by
  rw [← Real.exp_nat_mul]
  congr 1
  ring

/-- 衰减型：`e^{τ sinh δ - Xδ}·e^{-Xw} = e^{τ sinh δ}·e^{-X(δ+w)}`。 -/
lemma exp_decay_split (τ δ w X : ℝ) :
    Real.exp (τ * Real.sinh δ - X * δ) * Real.exp (-X * w)
      = Real.exp (τ * Real.sinh δ) * Real.exp (-X * (δ + w)) := by
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-- 增长型：`e^{τ sinh δ - Xδ}·e^{Xw} = e^{τ sinh δ}·e^{-X(δ-w)}`。 -/
lemma exp_growth_split (τ δ w X : ℝ) :
    Real.exp (τ * Real.sinh δ - X * δ) * Real.exp (X * w)
      = Real.exp (τ * Real.sinh δ) * Real.exp (-X * (δ - w)) := by
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

lemma exp_neg_nat_add_split (k n : ℕ) (x : ℝ) :
    Real.exp (-(((n + k : ℕ)) : ℝ) * x)
      = Real.exp (-((k : ℕ) : ℝ) * x) * Real.exp (-((n : ℕ) : ℝ) * x) := by
  rw [← Real.exp_add]
  congr 1
  push_cast
  ring

/-- 若 `‖F n‖ ≤ C rⁿ`（`0 ≤ r < 1`），则 `‖Σ' F‖ ≤ C/(1-r)`。 -/
lemma norm_tsum_le_of_geometric {F : ℕ → ℂ} {C r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hF : ∀ n, ‖F n‖ ≤ C * r ^ n) : ‖∑' n : ℕ, F n‖ ≤ C / (1 - r) := by
  have hsum : Summable fun n : ℕ => C * r ^ n :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hnorm : Summable fun n : ℕ => ‖F n‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hF hsum
  refine (norm_tsum_le_tsum_norm hnorm).trans ((Summable.tsum_le_tsum hF hnorm hsum).trans ?_)
  rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1, div_eq_mul_inv]

/-- 两个几何尾部之和。 -/
lemma norm_tsum_pair_le_of_geometric {F G : ℕ → ℂ} {C D r s : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hF : ∀ n, ‖F n‖ ≤ C * r ^ n) (hG : ∀ n, ‖G n‖ ≤ D * s ^ n) :
    ‖∑' n : ℕ, (F n + G n)‖ ≤ C / (1 - r) + D / (1 - s) := by
  have hsumr : Summable fun n : ℕ => C * r ^ n :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hsums : Summable fun n : ℕ => D * s ^ n :=
    (summable_geometric_of_lt_one hs0 hs1).mul_left _
  have hnormF : Summable fun n : ℕ => ‖F n‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hF hsumr
  have hnormG : Summable fun n : ℕ => ‖G n‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hG hsums
  rw [Summable.tsum_add hnormF.of_norm hnormG.of_norm]
  exact (norm_add_le _ _).trans
    (add_le_add (norm_tsum_le_of_geometric hr0 hr1 hF) (norm_tsum_le_of_geometric hs0 hs1 hG))

/-! ## 3. 单项界 -/

/-- 正指标单项的界（指数带负号）。 -/
lemma norm_Gcoef_nat_le (τ : ℝ) (hτ : 0 ≤ τ) {δ : ℝ} (hδ : 0 < δ) (j : ℕ) (w : ℝ) (m : ℕ) :
    ‖Gcoef τ j w ((m : ℕ) : ℤ)‖
      ≤ (m : ℝ) ^ j * Real.exp (τ * Real.sinh δ - (m : ℝ) * δ) * Real.exp (-(m : ℝ) * w) := by
  have hb := norm_fcoef_le τ hτ hδ ((m : ℕ) : ℤ)
  have hm : |(((((m : ℕ)) : ℤ)) : ℝ)| = (m : ℝ) := by
    push_cast
    exact abs_of_nonneg (Nat.cast_nonneg m)
  rw [hm] at hb
  rw [Gcoef, norm_mul, norm_mul, norm_pow, norm_neg, norm_exp_neg_mul, Complex.norm_intCast, hm]
  have hre : ((((m : ℕ)) : ℤ) : ℝ) = (m : ℝ) := by push_cast; ring
  rw [hre]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hb (pow_nonneg (Nat.cast_nonneg m) j)) (Real.exp_nonneg _)

/-- 正指标单项的界（指数带正号，来自 `fcoef` 的偶性）。 -/
lemma norm_fcoef_exp_pos_le (τ : ℝ) (hτ : 0 ≤ τ) {δ : ℝ} (hδ : 0 < δ) (w : ℝ) (m : ℕ) :
    ‖fcoef τ (((m : ℕ)) : ℤ) * Complex.exp (((((m : ℕ)) : ℤ) : ℂ) * (w : ℂ))‖
      ≤ Real.exp (τ * Real.sinh δ - (m : ℝ) * δ) * Real.exp ((m : ℝ) * w) := by
  have hb := norm_fcoef_le τ hτ hδ (((m : ℕ)) : ℤ)
  have hm : |(((((m : ℕ)) : ℤ)) : ℝ)| = (m : ℝ) := by
    push_cast
    exact abs_of_nonneg (Nat.cast_nonneg m)
  rw [hm] at hb
  rw [norm_mul, norm_exp_mul]
  have hre : (((((m : ℕ)) : ℤ) : ℂ)).re = (m : ℝ) := by simp
  rw [hre]
  exact mul_le_mul_of_nonneg_right hb (Real.exp_nonneg _)

/-- 负指标项的界（用 `fcoef` 的偶性）。 -/
lemma norm_Gcoef_neg_le (τ : ℝ) (hτ : 0 ≤ τ) {δ : ℝ} (hδ : 0 < δ) (w : ℝ) (j : ℕ) (m : ℕ) :
    ‖Gcoef τ j w (-(((m : ℕ)) : ℤ))‖
      ≤ (m : ℝ) ^ j * Real.exp (τ * Real.sinh δ - (m : ℝ) * δ) * Real.exp ((m : ℝ) * w) := by
  rw [Gcoef_neg_eq τ j w ((m : ℕ) : ℤ),
    show (((m : ℕ) : ℤ) : ℂ) ^ j * fcoef τ (((m : ℕ)) : ℤ)
        * Complex.exp (((((m : ℕ)) : ℤ) : ℂ) * (w : ℂ))
      = (((m : ℕ) : ℤ) : ℂ) ^ j
        * (fcoef τ (((m : ℕ)) : ℤ) * Complex.exp (((((m : ℕ)) : ℤ) : ℂ) * (w : ℂ))) from by ring,
    norm_mul, norm_pow]
  have hb := norm_fcoef_exp_pos_le τ hτ hδ w m
  have hc : ‖((((m : ℕ)) : ℤ) : ℂ)‖ = (m : ℝ) := by
    rw [Complex.norm_intCast]
    push_cast
    exact abs_of_nonneg (by positivity)
  rw [hc]
  exact (mul_le_mul_of_nonneg_left hb (pow_nonneg (Nat.cast_nonneg m) j)).trans
    (le_of_eq (by ring))

/-! ## 4. 级数拆分 -/

/-- 把 `Σ'_{n:ℤ}` 劈成「有限部分 + 两条尾部」。 -/
lemma tsum_Gcoef_split (τ : ℝ) (j : ℕ) {w : ℝ} (hs : Summable (Gcoef τ j w)) (k : ℕ) :
    ∑' n : ℤ, Gcoef τ j w n = finitePart τ j w k + tailPart τ j w k := by
  have hs_nat : Summable (fun n : ℕ => Gcoef τ j w (n : ℤ)) :=
    hs.comp_injective (fun a b hab => Nat.cast_injective hab)
  have hs_neg : Summable (fun n : ℕ => Gcoef τ j w (-(n : ℤ) - 1)) :=
    hs.comp_injective (fun a b hab => by
      have h2 : -((a : ℤ)) - 1 = -((b : ℤ)) - 1 := hab
      omega)
  have hpair : Summable (fun n : ℕ => Gcoef τ j w (n : ℤ) + Gcoef τ j w (-(n : ℤ) - 1)) :=
    hs_nat.add hs_neg
  have h1 : ∑' n : ℕ, (Gcoef τ j w (n : ℤ) + Gcoef τ j w (-(n : ℤ) - 1)) = ∑' n : ℤ, Gcoef τ j w n := by
    rw [← tsum_nat_add_neg_add_one hs]
    refine tsum_congr fun n => ?_
    congr 1
    rw [show -((n : ℤ) + 1) = -(n : ℤ) - 1 from by ring]
  rw [← h1, ← hpair.sum_add_tsum_nat_add k]
  rfl

/-! ## 5. 尾部界（`j = 0, 1, 2`） -/

/-- 尾部（`n ≥ k` 的两条尾巴）的几何界（`j = 0`）。 -/
lemma norm_tail_cosh_le (τ : ℝ) (hτ : 0 ≤ τ) {δ : ℝ} (hδ : 0 < δ) {w : ℝ} (hw : 0 < w)
    (hwδ : w < δ) (k : ℕ) :
    ‖tailPart τ 0 w k‖
      ≤ Real.exp (τ * Real.sinh δ) *
          (Real.exp (-(k : ℝ) * (δ + w)) / (1 - Real.exp (-(δ + w)))
            + Real.exp (-((k : ℝ) + 1) * (δ - w)) / (1 - Real.exp (-(δ - w)))) := by
  rw [tailPart]
  set r : ℝ := Real.exp (-(δ + w)) with hr
  set s : ℝ := Real.exp (-(δ - w)) with hs
  have hr0 : 0 ≤ r := Real.exp_nonneg _
  have hr1 : r < 1 := by rw [hr, Real.exp_lt_one_iff]; linarith
  have hs0 : 0 ≤ s := Real.exp_nonneg _
  have hs1 : s < 1 := by rw [hs, Real.exp_lt_one_iff]; linarith
  have hA : ∀ n : ℕ,
      ‖Gcoef τ 0 w (((n + k : ℕ)) : ℤ)‖ ≤ (Real.exp (τ * Real.sinh δ) * r ^ k) * r ^ n := by
    intro n
    refine (norm_Gcoef_nat_le τ hτ hδ 0 w (n + k)).trans (le_of_eq ?_)
    rw [pow_zero, one_mul,
      exp_decay_split τ δ w (((n + k : ℕ)) : ℝ), hr,
      exp_neg_nat_add_split k n (δ + w), exp_neg_mul_eq_pow k (δ + w),
      exp_neg_mul_eq_pow n (δ + w), ← hr]
    ring
  have hB : ∀ n : ℕ,
      ‖Gcoef τ 0 w (-(((n + k : ℕ)) : ℤ) - 1)‖
        ≤ (Real.exp (τ * Real.sinh δ) * s ^ (k + 1)) * s ^ n := by
    intro n
    have hneg : -(((n + k : ℕ)) : ℤ) - 1 = -((((n + (k + 1) : ℕ)) : ℤ)) := by push_cast; ring
    have hidx : n + (k + 1) = n + k + 1 := by omega
    rw [hneg, Gcoef_neg_eq]
    rw [show (((((n + (k + 1) : ℕ)) : ℤ)) : ℂ) ^ 0 = 1 from by simp, one_mul]
    refine (norm_fcoef_exp_pos_le τ hτ hδ w (n + k + 1)).trans (le_of_eq ?_)
    rw [← hidx, exp_growth_split τ δ w (((n + (k + 1) : ℕ)) : ℝ), hs,
      exp_neg_nat_add_split (k + 1) n (δ - w), exp_neg_mul_eq_pow (k + 1) (δ - w),
      exp_neg_mul_eq_pow n (δ - w), ← hs]
    ring
  have hmain := norm_tsum_pair_le_of_geometric hr0 hr1 hs0 hs1 hA hB
  rw [hr, ← exp_neg_mul_eq_pow k (δ + w), hs, ← exp_neg_mul_eq_pow (k + 1) (δ - w)] at hmain
  have hcast2 : Real.exp (-(((k + 1 : ℕ)) : ℝ) * (δ - w))
      = Real.exp (-((k : ℝ) + 1) * (δ - w)) := by
    congr 1
    push_cast
    ring
  rw [hcast2] at hmain
  refine hmain.trans (le_of_eq ?_)
  rw [div_eq_mul_inv, div_eq_mul_inv]
  ring

/-! ## 6. 有限部分与 `approxPoly` 的差 -/

/-- 有限和的一半（同 `KernelDecay.sum_range_pairs`，但用 `finitePart`）。 -/
lemma finitePart_eq_approxPoly_add (τ : ℝ) (w : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    finitePart τ 0 w k = (approxPoly τ k).eval ((Real.cosh w : ℝ) : ℂ)
      + fcoef τ (k : ℤ) * Complex.exp (((k : ℤ) : ℂ) * (w : ℂ)) := by
  rw [finitePart, ← sum_range_pairs τ w hk]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [Gcoef_zero_apply]
  congr 1
  · congr 1
    · rw [show -((n : ℤ)) - 1 = -(((n : ℤ) + 1)) from by ring, fcoef_neg]
    · rw [show -((n : ℤ)) - 1 = -(((n : ℤ) + 1)) from by ring]
      congr 1
      push_cast
      ring

/-- `‖有限部分 - P_k(cosh w)‖ ≤ ‖c_k‖e^{kw}`（`k = 0` 时为 `‖c_0‖`）。 -/
lemma norm_finitePart_sub_approxPoly_le (τ : ℝ) (w : ℝ) (k : ℕ) :
    ‖finitePart τ 0 w k - (approxPoly τ k).eval ((Real.cosh w : ℝ) : ℂ)‖
      ≤ ‖fcoef τ (k : ℤ)‖ * Real.exp ((k : ℝ) * w) := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have h0 : finitePart τ 0 w 0 = 0 := by simp [finitePart]
    have hp : (approxPoly τ 0).eval ((Real.cosh w : ℝ) : ℂ) = fcoef τ 0 := by
      rw [approxPoly_eval_cosh τ 0 w]
      simp
    rw [h0, hp, zero_sub, norm_neg]
    simp
  · rw [finitePart_eq_approxPoly_add τ w hk, add_sub_cancel_left, norm_mul, norm_exp_mul]
    simp

/-- `‖c_k‖e^{kw} ≤ e^{τ sinh δ}·e^{-k(δ-w)}`。 -/
lemma norm_fcoef_k_mul_exp_le (τ : ℝ) (hτ : 0 ≤ τ) {δ : ℝ} (hδ : 0 < δ) {w : ℝ} (hw : 0 < w)
    (hwδ : w < δ) (k : ℕ) :
    ‖fcoef τ (k : ℤ)‖ * Real.exp ((k : ℝ) * w)
      ≤ Real.exp (τ * Real.sinh δ) * Real.exp (-(k : ℝ) * (δ - w)) := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    simp only [Nat.cast_zero, zero_mul, neg_zero, Real.exp_zero, mul_one]
    exact norm_fcoef_zero τ hτ hδ
  · refine (mul_le_mul_of_nonneg_right (fcoef_bound τ hτ hδ (k : ℤ) (by exact_mod_cast hk))
      (Real.exp_nonneg _)).trans (le_of_eq ?_)
    exact exp_growth_split τ δ w (k : ℝ)

/-! ## 7. 主定理：值 -/

/-- **collar 上的误差尾部估计**（有抵消）。 -/
theorem norm_exp_sub_approxPoly_cosh_le {τ δ w : ℝ} (hτ : 0 < τ) (hw0 : 0 < w) (hwδ : w < δ)
    (k : ℕ) :
    ‖Complex.exp (-(τ : ℂ) * Complex.I * Complex.cosh w)
        - (approxPoly τ k).eval ((Real.cosh w : ℝ) : ℂ)‖
      ≤ Real.exp (τ * Real.sinh δ) *
        (Real.exp (-(k : ℝ) * (δ - w))
          + Real.exp (-(k : ℝ) * (δ + w)) / (1 - Real.exp (-(δ + w)))
          + Real.exp (-((k : ℝ) + 1) * (δ - w)) / (1 - Real.exp (-(δ - w)))) := by
  have hδ : 0 < δ := lt_trans hw0 hwδ
  have hτ0 : 0 ≤ τ := hτ.le
  rw [← Complex.ofReal_cosh]
  have hHas := hasSum_fcoef_cosh τ hτ0 hδ hw0 hwδ
  have hfun : (fun n : ℤ => fcoef τ n * Complex.exp (-(n : ℂ) * (w : ℂ))) = Gcoef τ 0 w :=
    funext fun n => (Gcoef_zero_apply τ w n).symm
  have hs : Summable (Gcoef τ 0 w) := by
    rw [← hfun]
    exact hHas.summable
  have hval : Complex.exp (-(τ : ℂ) * Complex.I * ((Real.cosh w : ℝ) : ℂ))
      = finitePart τ 0 w k + tailPart τ 0 w k := by
    rw [← hHas.tsum_eq, hfun]
    exact tsum_Gcoef_split τ 0 hs k
  have hfin := (norm_finitePart_sub_approxPoly_le τ w k).trans
    (norm_fcoef_k_mul_exp_le τ hτ0 hδ hw0 hwδ k)
  have htail := norm_tail_cosh_le τ hτ0 hδ hw0 hwδ k
  calc ‖Complex.exp (-(τ : ℂ) * Complex.I * ((Real.cosh w : ℝ) : ℂ))
        - (approxPoly τ k).eval ((Real.cosh w : ℝ) : ℂ)‖
      = ‖(finitePart τ 0 w k - (approxPoly τ k).eval ((Real.cosh w : ℝ) : ℂ))
          + tailPart τ 0 w k‖ := by
        rw [hval]
        congr 1
        ring
    _ ≤ ‖finitePart τ 0 w k - (approxPoly τ k).eval ((Real.cosh w : ℝ) : ℂ)‖
          + ‖tailPart τ 0 w k‖ := norm_add_le _ _
    _ ≤ Real.exp (τ * Real.sinh δ) * Real.exp (-(k : ℝ) * (δ - w))
          + Real.exp (τ * Real.sinh δ) *
            (Real.exp (-(k : ℝ) * (δ + w)) / (1 - Real.exp (-(δ + w)))
              + Real.exp (-((k : ℝ) + 1) * (δ - w)) / (1 - Real.exp (-(δ - w)))) :=
        add_le_add hfin htail
    _ = Real.exp (τ * Real.sinh δ) *
        (Real.exp (-(k : ℝ) * (δ - w))
          + Real.exp (-(k : ℝ) * (δ + w)) / (1 - Real.exp (-(δ + w)))
          + Real.exp (-((k : ℝ) + 1) * (δ - w)) / (1 - Real.exp (-(δ - w)))) := by
        ring

/-! ## 5b. `j = 1, 2` 的尾部界 -/

/-- choose 型几何尾部（单侧）。 -/
lemma norm_tsum_le_of_geometric_choose {F : ℕ → ℂ} {C r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (J : ℕ) (hF : ∀ n, ‖F n‖ ≤ C * (((n + J).choose J : ℝ) * r ^ n)) :
    ‖∑' n : ℕ, F n‖ ≤ C / (1 - r) ^ (J + 1) := by
  have hr : ‖r‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hr0]
  have hsum : Summable fun n : ℕ => C * (((n + J).choose J : ℝ) * r ^ n) :=
    (summable_choose_mul_geometric_of_norm_lt_one J hr).mul_left C
  have hnorm : Summable fun n : ℕ => ‖F n‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hF hsum
  refine (norm_tsum_le_tsum_norm hnorm).trans ((Summable.tsum_le_tsum hF hnorm hsum).trans ?_)
  rw [tsum_mul_left, tsum_choose_mul_geometric_of_norm_lt_one J hr]
  refine le_of_eq ?_
  rw [div_eq_mul_inv]
  ring

/-- choose 型几何尾部（成对）。 -/
lemma norm_tsum_pair_le_of_geometric_choose {F G : ℕ → ℂ} {C D r s : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hs0 : 0 ≤ s) (hs1 : s < 1) (J : ℕ)
    (hF : ∀ n, ‖F n‖ ≤ C * (((n + J).choose J : ℝ) * r ^ n))
    (hG : ∀ n, ‖G n‖ ≤ D * (((n + J).choose J : ℝ) * s ^ n)) :
    ‖∑' n : ℕ, (F n + G n)‖ ≤ C / (1 - r) ^ (J + 1) + D / (1 - s) ^ (J + 1) := by
  have hr : ‖r‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hr0]
  have hs' : ‖s‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hs0]
  have hsumr : Summable fun n : ℕ => C * (((n + J).choose J : ℝ) * r ^ n) :=
    (summable_choose_mul_geometric_of_norm_lt_one J hr).mul_left C
  have hsums : Summable fun n : ℕ => D * (((n + J).choose J : ℝ) * s ^ n) :=
    (summable_choose_mul_geometric_of_norm_lt_one J hs').mul_left D
  have hnormF : Summable fun n : ℕ => ‖F n‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hF hsumr
  have hnormG : Summable fun n : ℕ => ‖G n‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hG hsums
  rw [Summable.tsum_add hnormF.of_norm hnormG.of_norm]
  exact (norm_add_le _ _).trans
    (add_le_add (norm_tsum_le_of_geometric_choose hr0 hr1 J hF)
      (norm_tsum_le_of_geometric_choose hs0 hs1 J hG))

/-- `((n:ℝ)+1)^2 ≤ 2·(n+2).choose 2`。 -/
lemma real_add_one_sq_le_two_choose (n : ℕ) :
    ((n : ℝ) + 1) ^ 2 ≤ 2 * (((n + 2).choose 2 : ℕ) : ℝ) := by
  have h : 2 * (n + 2).choose 2 = (n + 2) * (n + 1) := by
    rw [Nat.choose_two_right]
    exact Nat.mul_div_cancel' (Nat.even_mul_pred_self (n + 2)).two_dvd
  have h2 : ((2 * (n + 2).choose 2 : ℕ) : ℝ) = (((n + 2) * (n + 1) : ℕ) : ℝ) := by rw [h]
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] at h2
  nlinarith [h2, (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]

/-- `(n+k:ℕ) ≤ k(n+1)`（`1 ≤ k`）。 -/
lemma nat_add_le_mul_add_one {n k : ℕ} (hk : 1 ≤ k) : n + k ≤ k * (n + 1) := by
  nlinarith [hk]

/-- `((n+k:ℕ):ℝ)^2 ≤ k²·2·(n+2).choose 2`（`1 ≤ k`）。 -/
lemma real_add_sq_le (n k : ℕ) (hk : 1 ≤ k) :
    (((n + k : ℕ)) : ℝ) ^ 2
      ≤ (k : ℝ) ^ 2 * (2 * (((n + 2).choose 2 : ℕ) : ℝ)) := by
  have h1 : (((n + k : ℕ)) : ℝ) ≤ (k : ℝ) * ((n : ℝ) + 1) := by
    have h := nat_add_le_mul_add_one (n := n) hk
    push_cast
    exact_mod_cast h
  have h2 := real_add_one_sq_le_two_choose n
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  nlinarith [h1, h2, hk0, hn0, sq_nonneg ((n : ℝ) - (k : ℝ)), mul_nonneg hk0 hn0]

/-- 尾部（`j = 1`）。 -/
lemma norm_tail_deriv_cosh_le (τ : ℝ) (hτ : 0 ≤ τ) {δ : ℝ} (hδ : 0 < δ) {w : ℝ} (hw : 0 < w)
    (hwδ : w < δ) {k : ℕ} (hk : 1 ≤ k) :
    ‖tailPart τ 1 w k‖
      ≤ Real.exp (τ * Real.sinh δ) *
          ((k : ℝ) * Real.exp (-(k : ℝ) * (δ + w)) / (1 - Real.exp (-(δ + w))) ^ 2
            + ((k : ℝ) + 1) * Real.exp (-((k : ℝ) + 1) * (δ - w))
              / (1 - Real.exp (-(δ - w))) ^ 2) := by
  rw [tailPart]
  set r : ℝ := Real.exp (-(δ + w)) with hr
  set s : ℝ := Real.exp (-(δ - w)) with hs
  have hr0 : 0 ≤ r := Real.exp_nonneg _
  have hr1 : r < 1 := by rw [hr, Real.exp_lt_one_iff]; linarith
  have hs0 : 0 ≤ s := Real.exp_nonneg _
  have hs1 : s < 1 := by rw [hs, Real.exp_lt_one_iff]; linarith
  have hA : ∀ n : ℕ, ‖Gcoef τ 1 w (((n + k : ℕ)) : ℤ)‖
      ≤ (Real.exp (τ * Real.sinh δ) * (k : ℝ) * r ^ k) * (((n + 1).choose 1 : ℝ) * r ^ n) := by
    intro n
    have hcast : (((n + k : ℕ)) : ℝ) ≤ (k : ℝ) * (((n + 1).choose 1 : ℕ) : ℝ) := by
      have h1 : (n + 1).choose 1 = n + 1 := Nat.choose_one_right (n + 1)
      rw [h1]
      have h := nat_add_le_mul_add_one (n := n) hk
      push_cast
      exact_mod_cast h
    calc ‖Gcoef τ 1 w (((n + k : ℕ)) : ℤ)‖
        ≤ (((n + k : ℕ)) : ℝ) ^ 1
            * Real.exp (τ * Real.sinh δ - (((n + k : ℕ)) : ℝ) * δ)
            * Real.exp (-(((n + k : ℕ)) : ℝ) * w) :=
          norm_Gcoef_nat_le τ hτ hδ 1 w (n + k)
      _ = (((n + k : ℕ)) : ℝ)
            * (Real.exp (τ * Real.sinh δ - (((n + k : ℕ)) : ℝ) * δ)
              * Real.exp (-(((n + k : ℕ)) : ℝ) * w)) := by rw [pow_one]; ring
      _ = (((n + k : ℕ)) : ℝ)
            * (Real.exp (τ * Real.sinh δ) * Real.exp (-(((n + k : ℕ)) : ℝ) * (δ + w))) := by
          rw [exp_decay_split]
      _ = (((n + k : ℕ)) : ℝ) * (Real.exp (τ * Real.sinh δ) * (r ^ k * r ^ n)) := by
          rw [exp_neg_nat_add_split k n (δ + w), exp_neg_mul_eq_pow k (δ + w),
            exp_neg_mul_eq_pow n (δ + w), ← hr]
      _ ≤ ((k : ℝ) * (((n + 1).choose 1 : ℕ) : ℝ))
            * (Real.exp (τ * Real.sinh δ) * (r ^ k * r ^ n)) :=
          mul_le_mul_of_nonneg_right hcast (by positivity)
      _ = (Real.exp (τ * Real.sinh δ) * (k : ℝ) * r ^ k)
            * (((n + 1).choose 1 : ℝ) * r ^ n) := by ring
  have hB : ∀ n : ℕ, ‖Gcoef τ 1 w (-(((n + k : ℕ)) : ℤ) - 1)‖
      ≤ (Real.exp (τ * Real.sinh δ) * s ^ (k + 1) * ((k : ℝ) + 1))
          * (((n + 1).choose 1 : ℝ) * s ^ n) := by
    intro n
    have hcast : (((n + (k + 1) : ℕ)) : ℝ) ≤ ((k : ℝ) + 1) * (((n + 1).choose 1 : ℕ) : ℝ) := by
      have h1 : (n + 1).choose 1 = n + 1 := Nat.choose_one_right (n + 1)
      rw [h1]
      have h := nat_add_le_mul_add_one (n := n) (Nat.le_add_left 1 k)
      push_cast
      exact_mod_cast h
    have hneg : -(((n + k : ℕ)) : ℤ) - 1 = -((((n + (k + 1) : ℕ)) : ℤ)) := by push_cast; ring
    rw [hneg, Gcoef_neg_eq, pow_one]
    rw [show ((((n + (k + 1) : ℕ)) : ℤ) : ℂ) * fcoef τ ((((n + (k + 1) : ℕ)) : ℤ))
          * Complex.exp (((((n + (k + 1) : ℕ)) : ℤ) : ℂ) * (w : ℂ))
        = ((((n + (k + 1) : ℕ)) : ℤ) : ℂ)
          * (fcoef τ ((((n + (k + 1) : ℕ)) : ℤ))
            * Complex.exp (((((n + (k + 1) : ℕ)) : ℤ) : ℂ) * (w : ℂ))) from by ring,
      norm_mul]
    have hb := norm_fcoef_exp_pos_le τ hτ hδ w (n + (k + 1))
    have hnormM : ‖((((n + (k + 1) : ℕ)) : ℤ) : ℂ)‖ = (((n + (k + 1) : ℕ)) : ℝ) := by
      rw [Complex.norm_intCast]
      push_cast
      exact abs_of_nonneg (by positivity)
    rw [hnormM]
    calc (((n + (k + 1) : ℕ)) : ℝ)
          * ‖fcoef τ ((((n + (k + 1) : ℕ)) : ℤ))
            * Complex.exp (((((n + (k + 1) : ℕ)) : ℤ) : ℂ) * (w : ℂ))‖
        ≤ (((n + (k + 1) : ℕ)) : ℝ)
            * (Real.exp (τ * Real.sinh δ - (((n + (k + 1) : ℕ)) : ℝ) * δ)
              * Real.exp ((((n + (k + 1) : ℕ)) : ℝ) * w)) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = (((n + (k + 1) : ℕ)) : ℝ)
            * (Real.exp (τ * Real.sinh δ) * Real.exp (-(((n + (k + 1) : ℕ)) : ℝ) * (δ - w))) := by
          rw [exp_growth_split]
      _ = (((n + (k + 1) : ℕ)) : ℝ) * (Real.exp (τ * Real.sinh δ) * (s ^ (k + 1) * s ^ n)) := by
          rw [exp_neg_nat_add_split (k + 1) n (δ - w), exp_neg_mul_eq_pow (k + 1) (δ - w),
            exp_neg_mul_eq_pow n (δ - w), ← hs]
      _ ≤ (((k : ℝ) + 1) * (((n + 1).choose 1 : ℕ) : ℝ))
            * (Real.exp (τ * Real.sinh δ) * (s ^ (k + 1) * s ^ n)) :=
          mul_le_mul_of_nonneg_right hcast (by positivity)
      _ = (Real.exp (τ * Real.sinh δ) * s ^ (k + 1) * ((k : ℝ) + 1))
            * (((n + 1).choose 1 : ℝ) * s ^ n) := by ring
  have hmain := norm_tsum_pair_le_of_geometric_choose hr0 hr1 hs0 hs1 1 hA hB
  rw [hr, ← exp_neg_mul_eq_pow k (δ + w), hs, ← exp_neg_mul_eq_pow (k + 1) (δ - w)] at hmain
  have hcast2 : Real.exp (-(((k + 1 : ℕ)) : ℝ) * (δ - w))
      = Real.exp (-((k : ℝ) + 1) * (δ - w)) := by
    congr 1
    push_cast
    ring
  rw [hcast2] at hmain
  refine hmain.trans (le_of_eq ?_)
  rw [hr, hs]
  ring_nf

/-- 尾部（`j = 2`）。 -/
lemma norm_tail_deriv2_cosh_le (τ : ℝ) (hτ : 0 ≤ τ) {δ : ℝ} (hδ : 0 < δ) {w : ℝ} (hw : 0 < w)
    (hwδ : w < δ) {k : ℕ} (hk : 1 ≤ k) :
    ‖tailPart τ 2 w k‖
      ≤ Real.exp (τ * Real.sinh δ) *
          (2 * (k : ℝ) ^ 2 * Real.exp (-(k : ℝ) * (δ + w)) / (1 - Real.exp (-(δ + w))) ^ 3
            + 2 * ((k : ℝ) + 1) ^ 2 * Real.exp (-((k : ℝ) + 1) * (δ - w))
              / (1 - Real.exp (-(δ - w))) ^ 3) := by
  rw [tailPart]
  set r : ℝ := Real.exp (-(δ + w)) with hr
  set s : ℝ := Real.exp (-(δ - w)) with hs
  have hr0 : 0 ≤ r := Real.exp_nonneg _
  have hr1 : r < 1 := by rw [hr, Real.exp_lt_one_iff]; linarith
  have hs0 : 0 ≤ s := Real.exp_nonneg _
  have hs1 : s < 1 := by rw [hs, Real.exp_lt_one_iff]; linarith
  have hA : ∀ n : ℕ, ‖Gcoef τ 2 w (((n + k : ℕ)) : ℤ)‖
      ≤ (Real.exp (τ * Real.sinh δ) * (k : ℝ) ^ 2 * r ^ k * 2)
          * (((n + 2).choose 2 : ℝ) * r ^ n) := by
    intro n
    have hcast := real_add_sq_le n k hk
    calc ‖Gcoef τ 2 w (((n + k : ℕ)) : ℤ)‖
        ≤ (((n + k : ℕ)) : ℝ) ^ 2
            * Real.exp (τ * Real.sinh δ - (((n + k : ℕ)) : ℝ) * δ)
            * Real.exp (-(((n + k : ℕ)) : ℝ) * w) :=
          norm_Gcoef_nat_le τ hτ hδ 2 w (n + k)
      _ = (((n + k : ℕ)) : ℝ) ^ 2
            * (Real.exp (τ * Real.sinh δ - (((n + k : ℕ)) : ℝ) * δ)
              * Real.exp (-(((n + k : ℕ)) : ℝ) * w)) := by ring
      _ = (((n + k : ℕ)) : ℝ) ^ 2
            * (Real.exp (τ * Real.sinh δ) * Real.exp (-(((n + k : ℕ)) : ℝ) * (δ + w))) := by
          rw [exp_decay_split]
      _ = (((n + k : ℕ)) : ℝ) ^ 2 * (Real.exp (τ * Real.sinh δ) * (r ^ k * r ^ n)) := by
          rw [exp_neg_nat_add_split k n (δ + w), exp_neg_mul_eq_pow k (δ + w),
            exp_neg_mul_eq_pow n (δ + w), ← hr]
      _ ≤ ((k : ℝ) ^ 2 * (2 * (((n + 2).choose 2 : ℕ) : ℝ)))
            * (Real.exp (τ * Real.sinh δ) * (r ^ k * r ^ n)) :=
          mul_le_mul_of_nonneg_right hcast (by positivity)
      _ = (Real.exp (τ * Real.sinh δ) * (k : ℝ) ^ 2 * r ^ k * 2)
            * (((n + 2).choose 2 : ℝ) * r ^ n) := by ring
  have hB : ∀ n : ℕ, ‖Gcoef τ 2 w (-(((n + k : ℕ)) : ℤ) - 1)‖
      ≤ (Real.exp (τ * Real.sinh δ) * s ^ (k + 1) * ((k : ℝ) + 1) ^ 2 * 2)
          * (((n + 2).choose 2 : ℝ) * s ^ n) := by
    intro n
    have hcast : (((n + (k + 1) : ℕ)) : ℝ) ^ 2
        ≤ ((k : ℝ) + 1) ^ 2 * (2 * (((n + 2).choose 2 : ℕ) : ℝ)) := by
      have h3 : (((k + 1 : ℕ)) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
      have := real_add_sq_le n (k + 1) (Nat.le_add_left 1 k)
      rwa [h3] at this
    have hneg : -(((n + k : ℕ)) : ℤ) - 1 = -((((n + (k + 1) : ℕ)) : ℤ)) := by push_cast; ring
    have hidx : n + (k + 1) = n + k + 1 := by omega
    rw [hneg, Gcoef_neg_eq]
    rw [show ((((n + (k + 1) : ℕ)) : ℤ) : ℂ) ^ 2 * fcoef τ ((((n + (k + 1) : ℕ)) : ℤ))
          * Complex.exp (((((n + (k + 1) : ℕ)) : ℤ) : ℂ) * (w : ℂ))
        = ((((n + (k + 1) : ℕ)) : ℤ) : ℂ) ^ 2
          * (fcoef τ ((((n + (k + 1) : ℕ)) : ℤ))
            * Complex.exp (((((n + (k + 1) : ℕ)) : ℤ) : ℂ) * (w : ℂ))) from by ring,
      norm_mul, norm_pow]
    have hb := norm_fcoef_exp_pos_le τ hτ hδ w (n + (k + 1))
    have hnormM : ‖((((n + (k + 1) : ℕ)) : ℤ) : ℂ)‖ = (((n + (k + 1) : ℕ)) : ℝ) := by
      rw [Complex.norm_intCast]
      push_cast
      exact abs_of_nonneg (by positivity)
    rw [hnormM]
    calc (((n + (k + 1) : ℕ)) : ℝ) ^ 2
          * ‖fcoef τ ((((n + (k + 1) : ℕ)) : ℤ))
            * Complex.exp (((((n + (k + 1) : ℕ)) : ℤ) : ℂ) * (w : ℂ))‖
        ≤ (((n + (k + 1) : ℕ)) : ℝ) ^ 2
            * (Real.exp (τ * Real.sinh δ - (((n + (k + 1) : ℕ)) : ℝ) * δ)
              * Real.exp ((((n + (k + 1) : ℕ)) : ℝ) * w)) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = (((n + (k + 1) : ℕ)) : ℝ) ^ 2
            * (Real.exp (τ * Real.sinh δ) * Real.exp (-(((n + (k + 1) : ℕ)) : ℝ) * (δ - w))) := by
          rw [exp_growth_split]
      _ = (((n + (k + 1) : ℕ)) : ℝ) ^ 2
            * (Real.exp (τ * Real.sinh δ) * (s ^ (k + 1) * s ^ n)) := by
          rw [exp_neg_nat_add_split (k + 1) n (δ - w), exp_neg_mul_eq_pow (k + 1) (δ - w),
            exp_neg_mul_eq_pow n (δ - w), ← hs]
      _ ≤ (((k : ℝ) + 1) ^ 2 * (2 * (((n + 2).choose 2 : ℕ) : ℝ)))
            * (Real.exp (τ * Real.sinh δ) * (s ^ (k + 1) * s ^ n)) :=
          mul_le_mul_of_nonneg_right hcast (by positivity)
      _ = (Real.exp (τ * Real.sinh δ) * s ^ (k + 1) * ((k : ℝ) + 1) ^ 2 * 2)
            * (((n + 2).choose 2 : ℝ) * s ^ n) := by ring
  have hmain := norm_tsum_pair_le_of_geometric_choose hr0 hr1 hs0 hs1 2 hA hB
  rw [hr, ← exp_neg_mul_eq_pow k (δ + w), hs, ← exp_neg_mul_eq_pow (k + 1) (δ - w)] at hmain
  have hcast2 : Real.exp (-(((k + 1 : ℕ)) : ℝ) * (δ - w))
      = Real.exp (-((k : ℝ) + 1) * (δ - w)) := by
    congr 1
    push_cast
    ring
  rw [hcast2] at hmain
  refine hmain.trans (le_of_eq ?_)
  rw [show (2 + 1 : ℕ) = 3 from rfl, hr, hs]
  ring

/-! ## 6. 逐项求导 -/

/-- 单项对 `w` 求导：`d/dw [G_j(w) n] = G_{j+1}(w) n`。 -/
lemma hasDerivAt_Gcoef (τ : ℝ) (j : ℕ) (n : ℤ) (z : ℝ) :
    HasDerivAt (fun y : ℝ => Gcoef τ j y n) (Gcoef τ (j+1) z n) z := by
  have hlin : HasDerivAt (fun y : ℝ => -(n : ℂ) * (y : ℂ)) (-(n : ℂ)) z := by
    have h := ((hasDerivAt_id z).ofReal_comp).const_mul (-(n : ℂ))
    simpa using h
  have hmain : HasDerivAt
      (fun y : ℝ => (-(n : ℂ)) ^ j * fcoef τ n * Complex.exp (-(n : ℂ) * (y : ℂ)))
      ((-(n : ℂ)) ^ j * fcoef τ n * (Complex.exp (-(n : ℂ) * (z : ℂ)) * (-(n : ℂ)))) z :=
    (hlin.cexp).const_mul _
  refine hmain.congr_deriv ?_
  rw [Gcoef, pow_succ]
  ring

/-- 有限部分的逐项求导。 -/
lemma hasDerivAt_finitePart (τ : ℝ) (j : ℕ) (w : ℝ) (k : ℕ) :
    HasDerivAt (fun z : ℝ => finitePart τ j z k) (finitePart τ (j+1) w k) w := by
  simp only [finitePart]
  exact HasDerivAt.fun_sum fun n _ =>
    (hasDerivAt_Gcoef τ j (n : ℤ) w).add (hasDerivAt_Gcoef τ j (-(n : ℤ) - 1) w)

/-- 尾部函数族可和。 -/
lemma summable_tail_family (τ : ℝ) (j : ℕ) {w : ℝ} (hs : Summable (Gcoef τ j w)) (k : ℕ) :
    Summable (fun n : ℕ =>
      Gcoef τ j w (((n + k : ℕ)) : ℤ) + Gcoef τ j w (-(((n + k : ℕ)) : ℤ) - 1)) := by
  have hs_nat : Summable (fun n : ℕ => Gcoef τ j w (n : ℤ)) :=
    hs.comp_injective (fun a b hab => Nat.cast_injective hab)
  have hs_neg : Summable (fun n : ℕ => Gcoef τ j w (-(n : ℤ) - 1)) :=
    hs.comp_injective (fun a b hab => by
      have h2 : -((a : ℤ)) - 1 = -((b : ℤ)) - 1 := hab
      omega)
  exact ((summable_nat_add_iff k).mpr hs_nat).add ((summable_nat_add_iff k).mpr hs_neg)

/-- 一般项的界（`|z| ≤ M`、`c + M ≤ δ`）。 -/
lemma norm_Gcoef_le_of_abs_le (τ : ℝ) (hτ : 0 ≤ τ) {δ : ℝ} (hδ : 0 < δ) (J : ℕ) {z M c : ℝ}
    (hz : |z| ≤ M) (hc : 0 ≤ c) (hcM : c + M ≤ δ) (m : ℤ) :
    ‖Gcoef τ J z m‖
      ≤ (|((m : ℤ) : ℝ)| + 1) ^ J * Real.exp (τ * Real.sinh δ)
        * Real.exp (-c) ^ m.natAbs := by
  have habs : |((m : ℤ) : ℝ)| = (m.natAbs : ℝ) := by
    rcases Int.eq_nat_or_neg m with ⟨k, rfl⟩ | ⟨k, rfl⟩ <;> simp
  have hb := norm_fcoef_le τ hτ hδ m
  rw [habs] at hb
  rw [Gcoef, norm_mul, norm_mul, norm_pow, norm_neg, norm_exp_neg_mul, Complex.norm_intCast, habs]
  have hstep1 : (m.natAbs : ℝ) ^ J ≤ ((m.natAbs : ℝ) + 1) ^ J :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith) J
  have hstep2 : -(m : ℝ) * z ≤ (m.natAbs : ℝ) * M := by
    have h1 : -(m : ℝ) * z = -((m : ℝ) * z) := by ring
    rw [h1, ← habs]
    refine (neg_le_abs _).trans ?_
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hz (abs_nonneg _)
  have hexp : Real.exp (τ * Real.sinh δ - (m.natAbs : ℝ) * δ) * Real.exp (-(m : ℝ) * z)
      ≤ Real.exp (τ * Real.sinh δ) * Real.exp (-c) ^ m.natAbs := by
    rw [← Real.exp_add]
    have hle : τ * Real.sinh δ - (m.natAbs : ℝ) * δ + -(m : ℝ) * z
        ≤ τ * Real.sinh δ + (-c) * (m.natAbs : ℝ) := by
      nlinarith [hstep2, hcM, hc, (Nat.cast_nonneg (m.natAbs) : (0 : ℝ) ≤ (m.natAbs : ℝ))]
    refine (Real.exp_le_exp.mpr hle).trans (le_of_eq ?_)
    rw [show τ * Real.sinh δ + (-c) * (m.natAbs : ℝ)
        = τ * Real.sinh δ + -((m.natAbs : ℝ)) * c from by ring,
      Real.exp_add, exp_neg_mul_eq_pow]
  calc (m.natAbs : ℝ) ^ J * ‖fcoef τ m‖ * Real.exp (-(m : ℝ) * z)
      ≤ (m.natAbs : ℝ) ^ J * Real.exp (τ * Real.sinh δ - (m.natAbs : ℝ) * δ)
          * Real.exp (-(m : ℝ) * z) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.exp_nonneg _)
        exact mul_le_mul_of_nonneg_left hb (pow_nonneg (Nat.cast_nonneg _) J)
    _ ≤ ((m.natAbs : ℝ) + 1) ^ J * Real.exp (τ * Real.sinh δ - (m.natAbs : ℝ) * δ)
          * Real.exp (-(m : ℝ) * z) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.exp_nonneg _)
        exact mul_le_mul_of_nonneg_right hstep1 (Real.exp_nonneg _)
    _ = ((m.natAbs : ℝ) + 1) ^ J
          * (Real.exp (τ * Real.sinh δ - (m.natAbs : ℝ) * δ) * Real.exp (-(m : ℝ) * z)) := by
        ring
    _ ≤ ((m.natAbs : ℝ) + 1) ^ J
          * (Real.exp (τ * Real.sinh δ) * Real.exp (-c) ^ m.natAbs) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = ((m.natAbs : ℝ) + 1) ^ J * Real.exp (τ * Real.sinh δ) * Real.exp (-c) ^ m.natAbs := by
        ring

/-- 移位项的界（`j = 1`，正指标）。 -/
lemma norm_Gcoef_one_shift_le (τ : ℝ) (hτ : 0 ≤ τ) {δ w : ℝ} (hδ : 0 < δ) (hwδ : w < δ)
    {k n : ℕ} {z : ℝ} (hz : |z| ≤ (w + δ) / 2) :
    ‖Gcoef τ 1 z (((n + k : ℕ)) : ℤ)‖
      ≤ ((k : ℝ) + 3) * Real.exp (τ * Real.sinh δ)
        * (((n : ℝ) + 1) * Real.exp (-((δ - w) / 2)) ^ n) := by
  have h := norm_Gcoef_le_of_abs_le τ hτ hδ 1 hz (by linarith : 0 ≤ (δ - w) / 2)
    (le_of_eq (by ring : (δ - w) / 2 + (w + δ) / 2 = δ)) (((n + k : ℕ)) : ℤ)
  rw [pow_one] at h
  have habs : |((((n + k : ℕ)) : ℤ) : ℝ)| = (((n + k : ℕ)) : ℝ) := by
    rw [Int.cast_natCast]
    exact abs_of_nonneg (Nat.cast_nonneg _)
  have hnat : ((((n + k : ℕ)) : ℤ)).natAbs = n + k := Int.natAbs_natCast _
  rw [habs, hnat] at h
  have hr0lt : Real.exp (-((δ - w) / 2)) < 1 := by
    rw [Real.exp_lt_one_iff]; linarith
  have hr0le : Real.exp (-((δ - w) / 2)) ^ (n + k) ≤ Real.exp (-((δ - w) / 2)) ^ n := by
    rw [pow_add]
    exact mul_le_of_le_one_right (pow_nonneg (Real.exp_nonneg _) n)
      (pow_le_one₀ (Real.exp_nonneg _) (le_of_lt hr0lt))
  have hnk : (((n + k : ℕ)) : ℝ) + 1 ≤ ((k : ℝ) + 3) * ((n : ℝ) + 1) := by
    push_cast
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ)), (Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℝ))]
  refine h.trans ?_
  calc ((((n + k : ℕ)) : ℝ) + 1) * Real.exp (τ * Real.sinh δ)
        * Real.exp (-((δ - w) / 2)) ^ (n + k)
      ≤ ((((n + k : ℕ)) : ℝ) + 1) * Real.exp (τ * Real.sinh δ)
          * Real.exp (-((δ - w) / 2)) ^ n :=
        mul_le_mul_of_nonneg_left hr0le
          (mul_nonneg (by positivity) (Real.exp_nonneg _))
    _ ≤ (((k : ℝ) + 3) * ((n : ℝ) + 1)) * Real.exp (τ * Real.sinh δ)
          * Real.exp (-((δ - w) / 2)) ^ n :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hnk (Real.exp_nonneg _))
          (pow_nonneg (Real.exp_nonneg _) n)
    _ = ((k : ℝ) + 3) * Real.exp (τ * Real.sinh δ)
          * (((n : ℝ) + 1) * Real.exp (-((δ - w) / 2)) ^ n) := by ring

/-- 移位项的界（`j = 1`，负指标）。 -/
lemma norm_Gcoef_one_shift_neg_le (τ : ℝ) (hτ : 0 ≤ τ) {δ w : ℝ} (hδ : 0 < δ) (hwδ : w < δ)
    {k n : ℕ} {z : ℝ} (hz : |z| ≤ (w + δ) / 2) :
    ‖Gcoef τ 1 z (-(((n + k : ℕ)) : ℤ) - 1)‖
      ≤ ((k : ℝ) + 3) * Real.exp (τ * Real.sinh δ)
        * (((n : ℝ) + 1) * Real.exp (-((δ - w) / 2)) ^ n) := by
  set m : ℤ := -(((n + k : ℕ)) : ℤ) - 1 with hm
  have hm1 : m = -((((n + k + 1 : ℕ)) : ℤ)) := by rw [hm]; push_cast; ring
  have hmabs : |((m : ℤ) : ℝ)| = (((n + k : ℕ)) : ℝ) + 1 := by
    rw [hm1, Int.cast_neg, Int.cast_natCast, abs_neg]
    push_cast
    exact abs_of_nonneg (by positivity)
  have hmnat : m.natAbs = n + k + 1 := by
    rw [hm1, Int.natAbs_neg, Int.natAbs_natCast]
  have h := norm_Gcoef_le_of_abs_le τ hτ hδ 1 hz (by linarith : 0 ≤ (δ - w) / 2)
    (le_of_eq (by ring : (δ - w) / 2 + (w + δ) / 2 = δ)) m
  rw [pow_one, hmabs, hmnat] at h
  have hr0lt : Real.exp (-((δ - w) / 2)) < 1 := by
    rw [Real.exp_lt_one_iff]; linarith
  have hr0le : Real.exp (-((δ - w) / 2)) ^ (n + k + 1) ≤ Real.exp (-((δ - w) / 2)) ^ n := by
    rw [show n + k + 1 = n + (k + 1) by omega, pow_add]
    exact mul_le_of_le_one_right (pow_nonneg (Real.exp_nonneg _) n)
      (pow_le_one₀ (Real.exp_nonneg _) (le_of_lt hr0lt))
  have hnk : (((n + k : ℕ)) : ℝ) + 1 + 1 ≤ ((k : ℝ) + 3) * ((n : ℝ) + 1) := by
    push_cast
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ)), (Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℝ))]
  refine h.trans ?_
  calc ((((n + k : ℕ)) : ℝ) + 1 + 1) * Real.exp (τ * Real.sinh δ)
        * Real.exp (-((δ - w) / 2)) ^ (n + k + 1)
      ≤ ((((n + k : ℕ)) : ℝ) + 1 + 1) * Real.exp (τ * Real.sinh δ)
          * Real.exp (-((δ - w) / 2)) ^ n :=
        mul_le_mul_of_nonneg_left hr0le
          (mul_nonneg (by positivity) (Real.exp_nonneg _))
    _ ≤ (((k : ℝ) + 3) * ((n : ℝ) + 1)) * Real.exp (τ * Real.sinh δ)
          * Real.exp (-((δ - w) / 2)) ^ n :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hnk (Real.exp_nonneg _))
          (pow_nonneg (Real.exp_nonneg _) n)
    _ = ((k : ℝ) + 3) * Real.exp (τ * Real.sinh δ)
          * (((n : ℝ) + 1) * Real.exp (-((δ - w) / 2)) ^ n) := by ring

/-- 移位项的界（`j = 2`，正指标）。 -/
lemma norm_Gcoef_two_shift_le (τ : ℝ) (hτ : 0 ≤ τ) {δ w : ℝ} (hδ : 0 < δ) (hwδ : w < δ)
    {k n : ℕ} {z : ℝ} (hz : |z| ≤ (w + δ) / 2) :
    ‖Gcoef τ 2 z (((n + k : ℕ)) : ℤ)‖
      ≤ ((k : ℝ) + 3) ^ 2 * Real.exp (τ * Real.sinh δ)
        * (((n : ℝ) + 1) ^ 2 * Real.exp (-((δ - w) / 2)) ^ n) := by
  have h := norm_Gcoef_le_of_abs_le τ hτ hδ 2 hz (by linarith : 0 ≤ (δ - w) / 2)
    (le_of_eq (by ring : (δ - w) / 2 + (w + δ) / 2 = δ)) (((n + k : ℕ)) : ℤ)
  have habs : |((((n + k : ℕ)) : ℤ) : ℝ)| = (((n + k : ℕ)) : ℝ) := by
    rw [Int.cast_natCast]
    exact abs_of_nonneg (Nat.cast_nonneg _)
  have hnat : ((((n + k : ℕ)) : ℤ)).natAbs = n + k := Int.natAbs_natCast _
  rw [habs, hnat] at h
  have hr0lt : Real.exp (-((δ - w) / 2)) < 1 := by
    rw [Real.exp_lt_one_iff]; linarith
  have hr0le : Real.exp (-((δ - w) / 2)) ^ (n + k) ≤ Real.exp (-((δ - w) / 2)) ^ n := by
    rw [pow_add]
    exact mul_le_of_le_one_right (pow_nonneg (Real.exp_nonneg _) n)
      (pow_le_one₀ (Real.exp_nonneg _) (le_of_lt hr0lt))
  have hnk : ((((n + k : ℕ)) : ℝ) + 1) ^ 2 ≤ (((k : ℝ) + 3) * ((n : ℝ) + 1)) ^ 2 := by
    refine pow_le_pow_left₀ (by positivity) ?_ 2
    push_cast
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ)), (Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℝ))]
  refine h.trans ?_
  calc ((((n + k : ℕ)) : ℝ) + 1) ^ 2 * Real.exp (τ * Real.sinh δ)
        * Real.exp (-((δ - w) / 2)) ^ (n + k)
      ≤ ((((n + k : ℕ)) : ℝ) + 1) ^ 2 * Real.exp (τ * Real.sinh δ)
          * Real.exp (-((δ - w) / 2)) ^ n :=
        mul_le_mul_of_nonneg_left hr0le
          (mul_nonneg (by positivity) (Real.exp_nonneg _))
    _ ≤ (((k : ℝ) + 3) * ((n : ℝ) + 1)) ^ 2 * Real.exp (τ * Real.sinh δ)
          * Real.exp (-((δ - w) / 2)) ^ n :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hnk (Real.exp_nonneg _))
          (pow_nonneg (Real.exp_nonneg _) n)
    _ = ((k : ℝ) + 3) ^ 2 * Real.exp (τ * Real.sinh δ)
          * (((n : ℝ) + 1) ^ 2 * Real.exp (-((δ - w) / 2)) ^ n) := by ring

/-- 移位项的界（`j = 2`，负指标）。 -/
lemma norm_Gcoef_two_shift_neg_le (τ : ℝ) (hτ : 0 ≤ τ) {δ w : ℝ} (hδ : 0 < δ) (hwδ : w < δ)
    {k n : ℕ} {z : ℝ} (hz : |z| ≤ (w + δ) / 2) :
    ‖Gcoef τ 2 z (-(((n + k : ℕ)) : ℤ) - 1)‖
      ≤ ((k : ℝ) + 3) ^ 2 * Real.exp (τ * Real.sinh δ)
        * (((n : ℝ) + 1) ^ 2 * Real.exp (-((δ - w) / 2)) ^ n) := by
  set m : ℤ := -(((n + k : ℕ)) : ℤ) - 1 with hm
  have hm1 : m = -((((n + k + 1 : ℕ)) : ℤ)) := by rw [hm]; push_cast; ring
  have hmabs : |((m : ℤ) : ℝ)| = (((n + k : ℕ)) : ℝ) + 1 := by
    rw [hm1, Int.cast_neg, Int.cast_natCast, abs_neg]
    push_cast
    exact abs_of_nonneg (by positivity)
  have hmnat : m.natAbs = n + k + 1 := by
    rw [hm1, Int.natAbs_neg, Int.natAbs_natCast]
  have h := norm_Gcoef_le_of_abs_le τ hτ hδ 2 hz (by linarith : 0 ≤ (δ - w) / 2)
    (le_of_eq (by ring : (δ - w) / 2 + (w + δ) / 2 = δ)) m
  rw [hmabs, hmnat] at h
  have hr0lt : Real.exp (-((δ - w) / 2)) < 1 := by
    rw [Real.exp_lt_one_iff]; linarith
  have hr0le : Real.exp (-((δ - w) / 2)) ^ (n + k + 1) ≤ Real.exp (-((δ - w) / 2)) ^ n := by
    rw [show n + k + 1 = n + (k + 1) by omega, pow_add]
    exact mul_le_of_le_one_right (pow_nonneg (Real.exp_nonneg _) n)
      (pow_le_one₀ (Real.exp_nonneg _) (le_of_lt hr0lt))
  have hnk : ((((n + k : ℕ)) : ℝ) + 1 + 1) ^ 2 ≤ (((k : ℝ) + 3) * ((n : ℝ) + 1)) ^ 2 := by
    refine pow_le_pow_left₀ (by positivity) ?_ 2
    push_cast
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ)), (Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℝ))]
  refine h.trans ?_
  calc ((((n + k : ℕ)) : ℝ) + 1 + 1) ^ 2 * Real.exp (τ * Real.sinh δ)
        * Real.exp (-((δ - w) / 2)) ^ (n + k + 1)
      ≤ ((((n + k : ℕ)) : ℝ) + 1 + 1) ^ 2 * Real.exp (τ * Real.sinh δ)
          * Real.exp (-((δ - w) / 2)) ^ n :=
        mul_le_mul_of_nonneg_left hr0le
          (mul_nonneg (by positivity) (Real.exp_nonneg _))
    _ ≤ (((k : ℝ) + 3) * ((n : ℝ) + 1)) ^ 2 * Real.exp (τ * Real.sinh δ)
          * Real.exp (-((δ - w) / 2)) ^ n :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hnk (Real.exp_nonneg _))
          (pow_nonneg (Real.exp_nonneg _) n)
    _ = ((k : ℝ) + 3) ^ 2 * Real.exp (τ * Real.sinh δ)
          * (((n : ℝ) + 1) ^ 2 * Real.exp (-((δ - w) / 2)) ^ n) := by ring

/-- `Σ (n+1)^j r^n` 可和（`j ≤ 2`）。 -/
lemma summable_add_one_pow_mul_geometric (j : ℕ) (hj : j ≤ 2) {r : ℝ} (hr0 : 0 ≤ r)
    (hr1 : r < 1) : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ j * r ^ n) := by
  have hr : ‖r‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hr0]
  have hA : Summable (fun n : ℕ => (n : ℝ) ^ 2 * r ^ n) :=
    Summable.of_norm (summable_norm_pow_mul_geometric_of_norm_lt_one 2 (r := r) hr)
  have hB : Summable (fun n : ℕ => r ^ n) := summable_geometric_of_lt_one hr0 hr1
  have h2 : Summable (fun n : ℕ => ((n : ℝ) ^ 2 + 1) * r ^ n) := by
    refine Summable.congr (hA.add hB) fun n => ?_
    ring
  interval_cases j
  · simpa using summable_geometric_of_lt_one hr0 hr1
  · refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) (h2.mul_left 2)
    have h : ((n : ℝ) + 1) ^ 1 ≤ 2 * ((n : ℝ) ^ 2 + 1) := by
      rw [pow_one]
      nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]
    exact (mul_le_mul_of_nonneg_right h (pow_nonneg hr0 n)).trans (le_of_eq (by ring))
  · refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) (h2.mul_left 2)
    have h : ((n : ℝ) + 1) ^ 2 ≤ 2 * ((n : ℝ) ^ 2 + 1) :=
      by nlinarith [sq_nonneg ((n : ℝ) - 1)]
    exact (mul_le_mul_of_nonneg_right h (pow_nonneg hr0 n)).trans (le_of_eq (by ring))

/-- 逐项求导用的几何优级数：`C·((n+1)^q r^n)`。 -/
def geomMajorant (C r : ℝ) (q : ℕ) (n : ℕ) : ℝ :=
  C * (((n : ℝ) + 1) ^ q * r ^ n)

lemma summable_geomMajorant {C r : ℝ} {q : ℕ} (hq : q ≤ 2) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (geomMajorant C r q) := by
  rw [show geomMajorant C r q = fun n : ℕ => C * (((n : ℝ) + 1) ^ q * r ^ n) from rfl]
  exact (summable_add_one_pow_mul_geometric q hq hr0 hr1).mul_left C

/-- 尾部逐项求导（`j = 0`）。 -/
lemma hasDerivAt_tailPart (τ : ℝ) (hτ : 0 ≤ τ) {δ : ℝ} (hδ : 0 < δ) {w : ℝ} (hw : 0 < w)
    (hwδ : w < δ) {k : ℕ} (hs : Summable (Gcoef τ 0 w)) :
    HasDerivAt (fun z : ℝ => tailPart τ 0 z k) (tailPart τ 1 w k) w := by
  rw [tailPart]
  have hmem : w ∈ Set.Ioo (w / 2) ((w + δ) / 2) := ⟨by linarith, by linarith⟩
  have hsub : ∀ z ∈ Set.Ioo (w / 2) ((w + δ) / 2), |z| ≤ (w + δ) / 2 := by
    intro z hz
    rw [abs_of_pos (by linarith [hz.1, hw] : (0 : ℝ) < z)]
    exact le_of_lt hz.2
  have hr0 : 0 ≤ Real.exp (-((δ - w) / 2)) := Real.exp_nonneg _
  have hr1 : Real.exp (-((δ - w) / 2)) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have hbase : Summable (geomMajorant (2 * ((k : ℝ) + 3) * Real.exp (τ * Real.sinh δ))
      (Real.exp (-((δ - w) / 2))) 1) :=
    summable_geomMajorant (C := 2 * ((k : ℝ) + 3) * Real.exp (τ * Real.sinh δ))
      (q := 1) (by norm_num) hr0 hr1
  refine hasDerivAt_tsum_of_isPreconnected
    (u := geomMajorant (2 * ((k : ℝ) + 3) * Real.exp (τ * Real.sinh δ))
      (Real.exp (-((δ - w) / 2))) 1)
    (g := fun n z => Gcoef τ 0 z (((n + k : ℕ)) : ℤ) + Gcoef τ 0 z (-(((n + k : ℕ)) : ℤ) - 1))
    (g' := fun n z => Gcoef τ 1 z (((n + k : ℕ)) : ℤ) + Gcoef τ 1 z (-(((n + k : ℕ)) : ℤ) - 1))
    (t := Set.Ioo (w / 2) ((w + δ) / 2)) ?_ isOpen_Ioo isPreconnected_Ioo ?_ ?_ hmem ?_ hmem
  · exact hbase
  · intro n z hz
    exact (hasDerivAt_Gcoef τ 0 _ z).add (hasDerivAt_Gcoef τ 0 _ z)
  · intro n z hz
    have hzM := hsub z hz
    have hA := norm_Gcoef_one_shift_le τ hτ hδ hwδ hzM (k := k) (n := n)
    have hB := norm_Gcoef_one_shift_neg_le τ hτ hδ hwδ hzM (k := k) (n := n)
    simp only [geomMajorant]
    refine (norm_add_le _ _).trans ?_
    calc ‖Gcoef τ 1 z (((n + k : ℕ)) : ℤ)‖ + ‖Gcoef τ 1 z (-(((n + k : ℕ)) : ℤ) - 1)‖
        ≤ ((k : ℝ) + 3) * Real.exp (τ * Real.sinh δ)
            * (((n : ℝ) + 1) * Real.exp (-((δ - w) / 2)) ^ n)
          + ((k : ℝ) + 3) * Real.exp (τ * Real.sinh δ)
            * (((n : ℝ) + 1) * Real.exp (-((δ - w) / 2)) ^ n) := add_le_add hA hB
      _ = (2 * ((k : ℝ) + 3) * Real.exp (τ * Real.sinh δ))
            * (((n : ℝ) + 1) ^ 1 * Real.exp (-((δ - w) / 2)) ^ n) := by ring
  · exact summable_tail_family τ 0 hs k

/-- 尾部逐项求导（`j = 1`）。 -/
lemma hasDerivAt_tailPart' (τ : ℝ) (hτ : 0 ≤ τ) {δ : ℝ} (hδ : 0 < δ) {w : ℝ} (hw : 0 < w)
    (hwδ : w < δ) {k : ℕ} (hs : Summable (Gcoef τ 1 w)) :
    HasDerivAt (fun z : ℝ => tailPart τ 1 z k) (tailPart τ 2 w k) w := by
  rw [tailPart]
  have hmem : w ∈ Set.Ioo (w / 2) ((w + δ) / 2) := ⟨by linarith, by linarith⟩
  have hsub : ∀ z ∈ Set.Ioo (w / 2) ((w + δ) / 2), |z| ≤ (w + δ) / 2 := by
    intro z hz
    rw [abs_of_pos (by linarith [hz.1, hw] : (0 : ℝ) < z)]
    exact le_of_lt hz.2
  have hr0 : 0 ≤ Real.exp (-((δ - w) / 2)) := Real.exp_nonneg _
  have hr1 : Real.exp (-((δ - w) / 2)) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have hbase : Summable (geomMajorant (2 * ((k : ℝ) + 3) ^ 2 * Real.exp (τ * Real.sinh δ))
      (Real.exp (-((δ - w) / 2))) 2) :=
    summable_geomMajorant (C := 2 * ((k : ℝ) + 3) ^ 2 * Real.exp (τ * Real.sinh δ))
      (q := 2) (by norm_num) hr0 hr1
  refine hasDerivAt_tsum_of_isPreconnected
    (u := geomMajorant (2 * ((k : ℝ) + 3) ^ 2 * Real.exp (τ * Real.sinh δ))
      (Real.exp (-((δ - w) / 2))) 2)
    (g := fun n z => Gcoef τ 1 z (((n + k : ℕ)) : ℤ) + Gcoef τ 1 z (-(((n + k : ℕ)) : ℤ) - 1))
    (g' := fun n z => Gcoef τ 2 z (((n + k : ℕ)) : ℤ) + Gcoef τ 2 z (-(((n + k : ℕ)) : ℤ) - 1))
    (t := Set.Ioo (w / 2) ((w + δ) / 2)) ?_ isOpen_Ioo isPreconnected_Ioo ?_ ?_ hmem ?_ hmem
  · exact hbase
  · intro n z hz
    exact (hasDerivAt_Gcoef τ 1 _ z).add (hasDerivAt_Gcoef τ 1 _ z)
  · intro n z hz
    have hzM := hsub z hz
    have hA := norm_Gcoef_two_shift_le τ hτ hδ hwδ hzM (k := k) (n := n)
    have hB := norm_Gcoef_two_shift_neg_le τ hτ hδ hwδ hzM (k := k) (n := n)
    simp only [geomMajorant]
    refine (norm_add_le _ _).trans ?_
    calc ‖Gcoef τ 2 z (((n + k : ℕ)) : ℤ)‖ + ‖Gcoef τ 2 z (-(((n + k : ℕ)) : ℤ) - 1)‖
        ≤ ((k : ℝ) + 3) ^ 2 * Real.exp (τ * Real.sinh δ)
            * (((n : ℝ) + 1) ^ 2 * Real.exp (-((δ - w) / 2)) ^ n)
          + ((k : ℝ) + 3) ^ 2 * Real.exp (τ * Real.sinh δ)
            * (((n : ℝ) + 1) ^ 2 * Real.exp (-((δ - w) / 2)) ^ n) := add_le_add hA hB
      _ = (2 * ((k : ℝ) + 3) ^ 2 * Real.exp (τ * Real.sinh δ))
            * (((n : ℝ) + 1) ^ 2 * Real.exp (-((δ - w) / 2)) ^ n) := by ring
  · exact summable_tail_family τ 1 hs k

/-! ## 7. `Gcoef` 级数的可和性 -/

/-- `j ≤ 2` 时 `Gcoef τ j w` 可和。 -/
lemma summable_Gcoef (τ : ℝ) (hτ : 0 ≤ τ) {δ : ℝ} (hδ : 0 < δ) {w : ℝ} (hw : 0 < w)
    (hwδ : w < δ) (j : ℕ) (hj : j ≤ 2) : Summable (Gcoef τ j w) := by
  have hP : 0 ≤ Real.exp (-(δ + w)) := Real.exp_nonneg _
  have hP1 : Real.exp (-(δ + w)) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have hN : 0 ≤ Real.exp (-(δ - w)) := Real.exp_nonneg _
  have hN1 : Real.exp (-(δ - w)) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have hE : 0 ≤ Real.exp (τ * Real.sinh δ) := Real.exp_nonneg _
  have hbaseP := summable_add_one_pow_mul_geometric j hj hP hP1
  have hbaseN := summable_add_one_pow_mul_geometric j hj hN hN1
  refine Summable.of_nat_of_neg_add_one ?_ ?_
  · refine Summable.of_norm_bounded (hbaseP.mul_left (Real.exp (τ * Real.sinh δ))) fun n => ?_
    have h := norm_Gcoef_nat_le τ hτ hδ j w n
    calc ‖Gcoef τ j w ((n : ℕ) : ℤ)‖
        ≤ (n : ℝ) ^ j * Real.exp (τ * Real.sinh δ - (n : ℝ) * δ)
            * Real.exp (-(n : ℝ) * w) := h
      _ = (n : ℝ) ^ j * (Real.exp (τ * Real.sinh δ) * Real.exp (-(δ + w)) ^ n) := by
          rw [mul_assoc, exp_decay_split, exp_neg_mul_eq_pow]
      _ ≤ ((n : ℝ) + 1) ^ j
            * (Real.exp (τ * Real.sinh δ) * Real.exp (-(δ + w)) ^ n) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg n) (by linarith) j)
            (mul_nonneg hE (pow_nonneg hP n))
      _ = Real.exp (τ * Real.sinh δ) * (((n : ℝ) + 1) ^ j * Real.exp (-(δ + w)) ^ n) := by
          ring
  · refine Summable.of_norm_bounded (hbaseN.mul_left (Real.exp (τ * Real.sinh δ))) fun n => ?_
    have h := norm_Gcoef_neg_le τ hτ hδ w j (n + 1)
    rw [← show -((n : ℤ) + 1) = -((((n + 1 : ℕ)) : ℤ)) by push_cast; ring] at h
    calc ‖Gcoef τ j w (-((n : ℤ) + 1))‖
        ≤ (((n + 1 : ℕ)) : ℝ) ^ j * Real.exp (τ * Real.sinh δ - (((n + 1 : ℕ)) : ℝ) * δ)
            * Real.exp ((((n + 1 : ℕ)) : ℝ) * w) := h
      _ = (((n + 1 : ℕ)) : ℝ) ^ j
            * (Real.exp (τ * Real.sinh δ) * Real.exp (-(δ - w)) ^ (n + 1)) := by
          rw [mul_assoc, exp_growth_split, exp_neg_mul_eq_pow]
      _ ≤ (((n + 1 : ℕ)) : ℝ) ^ j
            * (Real.exp (τ * Real.sinh δ) * Real.exp (-(δ - w)) ^ n) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hE) (by positivity)
          rw [pow_succ]
          exact mul_le_of_le_one_right (pow_nonneg hN n) (le_of_lt hN1)
      _ = Real.exp (τ * Real.sinh δ) * ((((n : ℝ)) + 1) ^ j * Real.exp (-(δ - w)) ^ n) := by
          push_cast
          ring

/-! ## 8. 主定理：一阶导与二阶导 -/


/-- `approxPoly` 在 `cosh` 上的复合的导数（避开 `Polynomial.hasDerivAt` 的模结构钻石）。 -/
lemma hasDerivAt_approxPoly_cosh (τ : ℝ) (k : ℕ) (w : ℝ) :
    HasDerivAt (fun z : ℝ => (approxPoly τ k).eval ((Real.cosh z : ℝ) : ℂ))
      (∑ m ∈ Finset.range (k - 1), 2 * fcoef τ ((m : ℤ) + 1)
        * ((((m : ℤ) + 1 : ℤ) : ℂ) * ((Real.sinh (((m : ℤ) + 1) * w) : ℝ) : ℂ))) w := by
  have hfun : (fun z : ℝ => (approxPoly τ k).eval ((Real.cosh z : ℝ) : ℂ))
      = fun z : ℝ => fcoef τ 0 + ∑ m ∈ Finset.range (k - 1), 2 * fcoef τ ((m : ℤ) + 1)
          * ((Real.cosh (((m : ℤ) + 1) * z) : ℝ) : ℂ) := by
    funext z
    rw [approxPoly_eval_cosh]
  rw [hfun]
  refine HasDerivAt.const_add _ ?_
  refine HasDerivAt.fun_sum fun m _ => ?_
  have hj : HasDerivAt (fun z : ℝ => ((((m : ℤ) : ℝ)) + 1) * z) ((((m : ℤ) : ℝ)) + 1) w := by
    simpa using (hasDerivAt_id w).const_mul (((((m : ℤ) : ℝ)) + 1))
  have hcosh : HasDerivAt (fun z : ℝ => Real.cosh ((((m : ℤ) : ℝ) + 1) * z))
      (Real.sinh ((((m : ℤ) : ℝ) + 1) * w) * ((((m : ℤ) : ℝ)) + 1)) w :=
    (Real.hasDerivAt_cosh _).comp w hj
  have hC : HasDerivAt (fun z : ℝ => ((Real.cosh ((((m : ℤ) : ℝ) + 1) * z) : ℝ) : ℂ))
      (((Real.sinh ((((m : ℤ) : ℝ) + 1) * w) * ((((m : ℤ) : ℝ)) + 1) : ℝ)) : ℂ) w :=
    hcosh.ofReal_comp
  refine (hC.const_mul (2 * fcoef τ ((m : ℤ) + 1))).congr_deriv ?_
  push_cast
  ring
/-- 有限部分一阶导的显式值。 -/
lemma finitePart_one_eq (τ : ℝ) (w : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    finitePart τ 1 w k
      = (∑ m ∈ Finset.range (k - 1), 2 * fcoef τ ((m : ℤ) + 1)
          * ((((m : ℤ) + 1 : ℤ) : ℂ) * ((Real.sinh (((m : ℤ) + 1) * w) : ℝ) : ℂ)))
        + (k : ℂ) * fcoef τ (k : ℤ) * Complex.exp (((k : ℤ) : ℂ) * (w : ℂ)) := by
  have h1 : HasDerivAt (fun z : ℝ => finitePart τ 0 z k) (finitePart τ 1 w k) w :=
    hasDerivAt_finitePart τ 0 w k
  have hexp : HasDerivAt
      (fun z : ℝ => fcoef τ (k : ℤ) * Complex.exp (((k : ℤ) : ℂ) * (z : ℂ)))
      ((k : ℂ) * fcoef τ (k : ℤ) * Complex.exp (((k : ℤ) : ℂ) * (w : ℂ))) w := by
    have hlin : HasDerivAt (fun z : ℝ => ((k : ℤ) : ℂ) * (z : ℂ)) (((k : ℤ) : ℂ)) w := by
      have h := ((hasDerivAt_id w).ofReal_comp).const_mul (((k : ℤ) : ℂ))
      simpa using h
    refine ((hlin.cexp).const_mul (fcoef τ (k : ℤ))).congr_deriv ?_
    push_cast
    ring
  have h2 : HasDerivAt (fun z : ℝ => (approxPoly τ k).eval ((Real.cosh z : ℝ) : ℂ)
      + fcoef τ (k : ℤ) * Complex.exp (((k : ℤ) : ℂ) * (z : ℂ)))
      ((∑ m ∈ Finset.range (k - 1), 2 * fcoef τ ((m : ℤ) + 1)
          * ((((m : ℤ) + 1 : ℤ) : ℂ) * ((Real.sinh (((m : ℤ) + 1) * w) : ℝ) : ℂ)))
        + (k : ℂ) * fcoef τ (k : ℤ) * Complex.exp (((k : ℤ) : ℂ) * (w : ℂ))) w :=
    (hasDerivAt_approxPoly_cosh τ k w).add hexp
  have heq : (fun z : ℝ => finitePart τ 0 z k)
      = fun z : ℝ => (approxPoly τ k).eval ((Real.cosh z : ℝ) : ℂ)
          + fcoef τ (k : ℤ) * Complex.exp (((k : ℤ) : ℂ) * (z : ℂ)) :=
    funext fun z => finitePart_eq_approxPoly_add τ z hk
  rw [heq] at h1
  exact h1.unique h2

/-- 误差函数的一阶导（collar 恒等式的导数形式）。 -/
lemma deriv_exp_sub_eq (τ : ℝ) (hτ : 0 < τ) {δ : ℝ} (hδ : 0 < δ) {z : ℝ} (hz0 : 0 < z)
    (hzδ : z < δ) {k : ℕ} (hk : 1 ≤ k) :
    deriv (fun y : ℝ => Complex.exp (-(τ : ℂ) * Complex.I * Complex.cosh y)
        - (approxPoly τ k).eval ((Real.cosh y : ℝ) : ℂ)) z
      = (k : ℂ) * fcoef τ (k : ℤ) * Complex.exp (((k : ℤ) : ℂ) * (z : ℂ))
        + tailPart τ 1 z k := by
  have hτ0 : 0 ≤ τ := hτ.le
  have hs0 : Summable (Gcoef τ 0 z) := summable_Gcoef τ hτ0 hδ hz0 hzδ 0 (by norm_num)
  have hG : HasDerivAt (fun y : ℝ => finitePart τ 0 y k + tailPart τ 0 y k)
      (finitePart τ 1 z k + tailPart τ 1 z k) z :=
    (hasDerivAt_finitePart τ 0 z k).add (hasDerivAt_tailPart τ hτ0 hδ hz0 hzδ hs0)
  have hQ := hasDerivAt_approxPoly_cosh τ k z
  have hGQ := hG.sub hQ
  have heq : (fun y : ℝ => Complex.exp (-(τ : ℂ) * Complex.I * Complex.cosh y)
        - (approxPoly τ k).eval ((Real.cosh y : ℝ) : ℂ))
      =ᶠ[𝓝 z] (fun y : ℝ => (finitePart τ 0 y k + tailPart τ 0 y k)
        - (approxPoly τ k).eval ((Real.cosh y : ℝ) : ℂ)) := by
    filter_upwards [isOpen_Ioo.mem_nhds ⟨hz0, hzδ⟩] with y hy
    have hy' := hasSum_fcoef_cosh τ hτ0 hδ hy.1 hy.2
    have hs : Summable (Gcoef τ 0 y) := summable_Gcoef τ hτ0 hδ hy.1 hy.2 0 (by norm_num)
    have hfun : (fun n : ℤ => fcoef τ n * Complex.exp (-(n : ℂ) * (y : ℂ))) = Gcoef τ 0 y :=
      funext fun n => (Gcoef_zero_apply τ y n).symm
    rw [← Complex.ofReal_cosh, ← hy'.tsum_eq, hfun, tsum_Gcoef_split τ 0 hs k]
  calc deriv (fun y : ℝ => Complex.exp (-(τ : ℂ) * Complex.I * Complex.cosh y)
        - (approxPoly τ k).eval ((Real.cosh y : ℝ) : ℂ)) z
      = deriv (fun y : ℝ => (finitePart τ 0 y k + tailPart τ 0 y k)
          - (approxPoly τ k).eval ((Real.cosh y : ℝ) : ℂ)) z := heq.deriv_eq
    _ = (finitePart τ 1 z k + tailPart τ 1 z k)
          - (∑ m ∈ Finset.range (k - 1), 2 * fcoef τ ((m : ℤ) + 1)
              * ((((m : ℤ) + 1 : ℤ) : ℂ) * ((Real.sinh (((m : ℤ) + 1) * z) : ℝ) : ℂ))) :=
        hGQ.deriv
    _ = (k : ℂ) * fcoef τ (k : ℤ) * Complex.exp (((k : ℤ) : ℂ) * (z : ℂ))
          + tailPart τ 1 z k := by
        rw [finitePart_one_eq τ z hk]
        ring

/-- 误差函数的二阶导（collar 恒等式的二阶导数形式）。 -/
lemma deriv2_exp_sub_eq (τ : ℝ) (hτ : 0 < τ) {δ : ℝ} (hδ : 0 < δ) {z : ℝ} (hz0 : 0 < z)
    (hzδ : z < δ) {k : ℕ} (hk : 1 ≤ k) :
    deriv (deriv (fun y : ℝ => Complex.exp (-(τ : ℂ) * Complex.I * Complex.cosh y)
        - (approxPoly τ k).eval ((Real.cosh y : ℝ) : ℂ))) z
      = (k : ℂ) ^ 2 * fcoef τ (k : ℤ) * Complex.exp (((k : ℤ) : ℂ) * (z : ℂ))
        + tailPart τ 2 z k := by
  have hτ0 : 0 ≤ τ := hτ.le
  have hs1 : Summable (Gcoef τ 1 z) := summable_Gcoef τ hτ0 hδ hz0 hzδ 1 (by norm_num)
  have hlin : HasDerivAt
      (fun y : ℝ => (k : ℂ) * fcoef τ (k : ℤ) * Complex.exp (((k : ℤ) : ℂ) * (y : ℂ)))
      ((k : ℂ) ^ 2 * fcoef τ (k : ℤ) * Complex.exp (((k : ℤ) : ℂ) * (z : ℂ))) z := by
    have hlin' : HasDerivAt (fun y : ℝ => ((k : ℤ) : ℂ) * (y : ℂ)) (((k : ℤ) : ℂ)) z := by
      have h := ((hasDerivAt_id z).ofReal_comp).const_mul (((k : ℤ) : ℂ))
      simpa using h
    refine ((hlin'.cexp).const_mul ((k : ℂ) * fcoef τ (k : ℤ))).congr_deriv ?_
    push_cast
    ring
  have hR : HasDerivAt
      (fun y : ℝ => (k : ℂ) * fcoef τ (k : ℤ) * Complex.exp (((k : ℤ) : ℂ) * (y : ℂ))
        + tailPart τ 1 y k)
      ((k : ℂ) ^ 2 * fcoef τ (k : ℤ) * Complex.exp (((k : ℤ) : ℂ) * (z : ℂ))
        + tailPart τ 2 z k) z :=
    hlin.add (hasDerivAt_tailPart' τ hτ0 hδ hz0 hzδ hs1)
  have heq : deriv (fun y : ℝ => Complex.exp (-(τ : ℂ) * Complex.I * Complex.cosh y)
        - (approxPoly τ k).eval ((Real.cosh y : ℝ) : ℂ))
      =ᶠ[𝓝 z] fun y : ℝ => (k : ℂ) * fcoef τ (k : ℤ) * Complex.exp (((k : ℤ) : ℂ) * (y : ℂ))
          + tailPart τ 1 y k := by
    filter_upwards [isOpen_Ioo.mem_nhds ⟨hz0, hzδ⟩] with y hy
    exact deriv_exp_sub_eq τ hτ hδ hy.1 hy.2 hk
  rw [heq.deriv_eq, hR.deriv]

/-- **collar 上一阶导的尾部估计**（`1 ≤ k`）。 -/
theorem norm_deriv_exp_sub_approxPoly_cosh_le {τ δ w : ℝ} (hτ : 0 < τ) (hw0 : 0 < w)
    (hwδ : w < δ) {k : ℕ} (hk : 1 ≤ k) :
    ‖deriv (fun z : ℝ => Complex.exp (-(τ : ℂ) * Complex.I * Complex.cosh z)
        - (approxPoly τ k).eval ((Real.cosh z : ℝ) : ℂ)) w‖
      ≤ Real.exp (τ * Real.sinh δ) *
          ((k : ℝ) * Real.exp (-(k : ℝ) * (δ - w))
            + (k : ℝ) * Real.exp (-(k : ℝ) * (δ + w)) / (1 - Real.exp (-(δ + w))) ^ 2
            + ((k : ℝ) + 1) * Real.exp (-((k : ℝ) + 1) * (δ - w))
              / (1 - Real.exp (-(δ - w))) ^ 2) := by
  have hδ : 0 < δ := lt_trans hw0 hwδ
  have hτ0 : 0 ≤ τ := hτ.le
  have hd := deriv_exp_sub_eq τ hτ hδ hw0 hwδ hk
  have hck : ‖(k : ℂ) * fcoef τ (k : ℤ) * Complex.exp (((k : ℤ) : ℂ) * (w : ℂ))‖
      ≤ Real.exp (τ * Real.sinh δ) * ((k : ℝ) * Real.exp (-(k : ℝ) * (δ - w))) := by
    have hre : (((k : ℤ) : ℂ)).re = (k : ℝ) := by
      rw [Complex.intCast_re]
      push_cast
      ring
    rw [norm_mul, norm_mul, Complex.norm_natCast, norm_exp_mul, hre]
    have hb := fcoef_bound τ hτ0 hδ (k : ℤ) (by exact_mod_cast hk)
    calc (k : ℝ) * ‖fcoef τ (k : ℤ)‖ * Real.exp ((k : ℝ) * w)
        = (k : ℝ) * (‖fcoef τ (k : ℤ)‖ * Real.exp ((k : ℝ) * w)) := by ring
      _ ≤ (k : ℝ)
            * (Real.exp (τ * Real.sinh δ - (k : ℝ) * δ) * Real.exp ((k : ℝ) * w)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hb (Real.exp_nonneg _)) (Nat.cast_nonneg k)
      _ = Real.exp (τ * Real.sinh δ) * ((k : ℝ) * Real.exp (-(k : ℝ) * (δ - w))) := by
          rw [exp_growth_split τ δ w (k : ℝ)]
          ring
  have htail := norm_tail_deriv_cosh_le τ hτ0 hδ hw0 hwδ hk
  rw [hd]
  refine (norm_add_le _ _).trans ((add_le_add hck htail).trans (le_of_eq ?_))
  ring

/-- **collar 上二阶导的尾部估计**（`1 ≤ k`）。 -/
theorem norm_deriv2_exp_sub_approxPoly_cosh_le {τ δ w : ℝ} (hτ : 0 < τ) (hw0 : 0 < w)
    (hwδ : w < δ) {k : ℕ} (hk : 1 ≤ k) :
    ‖deriv (deriv (fun z : ℝ => Complex.exp (-(τ : ℂ) * Complex.I * Complex.cosh z)
        - (approxPoly τ k).eval ((Real.cosh z : ℝ) : ℂ))) w‖
      ≤ Real.exp (τ * Real.sinh δ) *
          ((k : ℝ) ^ 2 * Real.exp (-(k : ℝ) * (δ - w))
            + 2 * (k : ℝ) ^ 2 * Real.exp (-(k : ℝ) * (δ + w))
              / (1 - Real.exp (-(δ + w))) ^ 3
            + 2 * ((k : ℝ) + 1) ^ 2 * Real.exp (-((k : ℝ) + 1) * (δ - w))
              / (1 - Real.exp (-(δ - w))) ^ 3) := by
  have hδ : 0 < δ := lt_trans hw0 hwδ
  have hτ0 : 0 ≤ τ := hτ.le
  have hd := deriv2_exp_sub_eq τ hτ hδ hw0 hwδ hk
  have hck : ‖(k : ℂ) ^ 2 * fcoef τ (k : ℤ) * Complex.exp (((k : ℤ) : ℂ) * (w : ℂ))‖
      ≤ Real.exp (τ * Real.sinh δ) * ((k : ℝ) ^ 2 * Real.exp (-(k : ℝ) * (δ - w))) := by
    have hre : (((k : ℤ) : ℂ)).re = (k : ℝ) := by
      rw [Complex.intCast_re]
      push_cast
      ring
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_natCast, norm_exp_mul, hre]
    have hb := fcoef_bound τ hτ0 hδ (k : ℤ) (by exact_mod_cast hk)
    calc (k : ℝ) ^ 2 * ‖fcoef τ (k : ℤ)‖ * Real.exp ((k : ℝ) * w)
        = (k : ℝ) ^ 2 * (‖fcoef τ (k : ℤ)‖ * Real.exp ((k : ℝ) * w)) := by ring
      _ ≤ (k : ℝ) ^ 2
            * (Real.exp (τ * Real.sinh δ - (k : ℝ) * δ) * Real.exp ((k : ℝ) * w)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hb (Real.exp_nonneg _)) (by positivity)
      _ = Real.exp (τ * Real.sinh δ) * ((k : ℝ) ^ 2 * Real.exp (-(k : ℝ) * (δ - w))) := by
          rw [exp_growth_split τ δ w (k : ℝ)]
          ring
  have htail := norm_tail_deriv2_cosh_le τ hτ0 hδ hw0 hwδ hk
  rw [hd]
  refine (norm_add_le _ _).trans ((add_le_add hck htail).trans (le_of_eq ?_))
  rw [mul_add, mul_add]
  ring

end RobustZ
