import RobustZ.Smearing
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# M3（显式常数）：截断函数导数的一致数值界

`RobustZ/CutoffDeriv.lean` 用紧性给出了一个**不透明**的常数 `K`，使得对一切 `τ, B > 0` 与一切 `μ`

* `|deriv (cutoff τ B) μ| ≤ K / B`
* `|deriv (deriv (cutoff τ B)) μ| ≤ K / B ^ 2`

本文件把它替换成**显式数值** `K₀ = 21.1`：证明

* `∀ x, |deriv Real.smoothTransition x| ≤ 21.1`
* `∀ x, |deriv (deriv Real.smoothTransition x)| ≤ 21.1`（即二阶导）

然后把链式法则的缩放（`RobustZ/CutoffDeriv.lean` 中的 `K / B`、`K / B ^ 2`）原样搬过来，
得到 `deriv_cutoff_le_explicit` 与 `exists_deriv_cutoff_bound_explicit`。

## 证明要点

在 `(0,1)` 上（`cutoff` 只用到 `smoothTransition` 的 `(0,1)` 段）有**显式**表达式

`σ x = 1 / (1 + e^{v x})`，`v x = 1/x - 1/(1-x)`，

于是（记 `z = e^{-|v|}`，`u = |v|`）

* `σ' = σ(1-σ)·v'`，`σ'' = σ(1-σ)·((1-2σ)·(v')² + v'')`
* `σ(1-σ) = z/(1+z)² ≤ min(1/4, z)`
* `σ(1-σ)|1-2σ| = z(1-z)/(1+z)³`
* `v' = u²+2(2+√(4+u²)) ≤ U2 u = (3/2)u²+8`
* `|v''| ≤ 2u·W2 u`，`W2 u = (3/2)u²+u+12`

数值部分：

* 一阶导：`|σ'| ≤ min(1/4,e^{-u})·U2 u ≤ 3`（在 `u = 7/5` 处劈开，两段都 ≤ `(1/4)U2(7/5) = 2.735`）。
* 二阶导：`(1-2σ)(v')²` 与 `v''` 反号，故
  `|σ''| ≤ max{ σ(1-σ)|1-2σ|(v')², σ(1-σ)|v''| }`；
  再对 `z` 用 `(1+z)³ ≥ 1+3z+3z²`，并对 `u` 在 `7/5, 2, 5/2, 3, 7/2` 处六段劈开：
  每段用显式有理指数界（`e^{1/2}, e², e³, e^{11/5}, e^{5/2}, e^{7/2}` 的有理上下界）
  与 `z ↦ (1-z)/(1+3z+3z²)` 的单调性，得到
  `σ(1-σ)|1-2σ|(v')² ≤ 21.1`、`σ(1-σ)|v''| ≤ 20`。

（真实上确界 `sup|σ'| = 2`、`sup|σ''| ≈ 9.8410`；`21.1` 是本文件用初等分段估计能达到的值。）
-/

noncomputable section

namespace RobustZ

open scoped Real Topology
open Filter

/-! ## 1. `smoothTransition` 在 `(0,1)` 上的显式表达式与导数 -/

/-- `v(x) = 1/(1-x) - 1/x`。在 `(0,1)` 上 `smoothTransition x = 1/(1+e^{-v x})`。 -/
def sigmaV (x : ℝ) : ℝ := (1 - x)⁻¹ - x⁻¹

/-- `v'(x) = 1/x² + 1/(1-x)²`。 -/
def sigmaV1 (x : ℝ) : ℝ := (x ^ 2)⁻¹ + ((1 - x) ^ 2)⁻¹

/-- `v''(x) = 2/(1-x)³ - 2/x³`（= `-(v')'`）。 -/
def sigmaV2 (x : ℝ) : ℝ := -2 * (x ^ 3)⁻¹ + 2 * ((1 - x) ^ 3)⁻¹

/-- `x ∈ (0,1)` 时 `smoothTransition x = 1/(1+e^{1/x-1/(1-x)})`。 -/
lemma smoothTransition_eq_inv_one_add_exp {x : ℝ} (hx : x ∈ Set.Ioo 0 1) :
    Real.smoothTransition x = 1 / (1 + Real.exp (x⁻¹ - (1 - x)⁻¹)) := by
  have hx0 : 0 < x := hx.1
  have hx1 : x < 1 := hx.2
  have h1 : expNegInvGlue x = Real.exp (-x⁻¹) := by
    simp [expNegInvGlue, hx0.not_ge]
  have h2 : expNegInvGlue (1 - x) = Real.exp (-(1 - x)⁻¹) := by
    simp [expNegInvGlue, (by linarith : (0 : ℝ) < 1 - x).not_ge]
  have hE : Real.exp (x⁻¹ - (1 - x)⁻¹)
      = Real.exp (-(1 - x)⁻¹) / Real.exp (-x⁻¹) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  rw [Real.smoothTransition, h1, h2, hE]
  have hA : Real.exp (-x⁻¹) ≠ 0 := Real.exp_ne_zero _
  have hB : Real.exp (-(1 - x)⁻¹) ≠ 0 := Real.exp_ne_zero _
  field_simp

/-- `smoothTransition` 的导数的显式公式（`(0,1)` 上）。 -/
lemma deriv_smoothTransition_eq {x : ℝ} (hx : x ∈ Set.Ioo 0 1) :
    deriv Real.smoothTransition x
      = Real.smoothTransition x * (1 - Real.smoothTransition x) * sigmaV1 x := by
  have hx0 : 0 < x := hx.1
  have hx1 : x < 1 := hx.2
  have hx0' : x ≠ 0 := ne_of_gt hx0
  have hx1' : x ≠ 1 := ne_of_lt hx1
  have hev : Real.smoothTransition =ᶠ[nhds x]
      fun y : ℝ => 1 / (1 + Real.exp (y⁻¹ - (1 - y)⁻¹)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact smoothTransition_eq_inv_one_add_exp hy
  rw [hev.deriv_eq]
  have hV : HasDerivAt (fun y : ℝ => y⁻¹ - (1 - y)⁻¹) (-(sigmaV1 x)) x := by
    have h1 : HasDerivAt (fun y : ℝ => y⁻¹) (-(x ^ 2)⁻¹) x := hasDerivAt_inv hx0'
    have h2 : HasDerivAt (fun y : ℝ => (1 - y)⁻¹) ((1 - x) ^ 2)⁻¹ x := by
      have h : HasDerivAt (fun y : ℝ => 1 - y) (0 - 1) x :=
        (hasDerivAt_const (x := x) (c := (1 : ℝ))).sub (hasDerivAt_id x)
      have h3 := h.inv (by simp only [sub_ne_zero]; exact Ne.symm hx1')
      convert h3 using 1
      ring
    have h4 := h1.sub h2
    convert h4 using 1
    simp only [sigmaV1]
    ring
  have hExp : HasDerivAt (fun y : ℝ => Real.exp (y⁻¹ - (1 - y)⁻¹))
      (Real.exp (x⁻¹ - (1 - x)⁻¹) * (-(sigmaV1 x))) x := hV.exp
  have hDen : HasDerivAt (fun y : ℝ => 1 + Real.exp (y⁻¹ - (1 - y)⁻¹))
      (Real.exp (x⁻¹ - (1 - x)⁻¹) * (-(sigmaV1 x))) x := hExp.const_add 1
  have hInv : HasDerivAt (fun y : ℝ => (1 + Real.exp (y⁻¹ - (1 - y)⁻¹))⁻¹)
      (-(Real.exp (x⁻¹ - (1 - x)⁻¹) * (-(sigmaV1 x)))
        / (1 + Real.exp (x⁻¹ - (1 - x)⁻¹)) ^ 2) x :=
    hDen.inv (by positivity)
  have hone : deriv (fun y : ℝ => 1 / (1 + Real.exp (y⁻¹ - (1 - y)⁻¹))) x
      = deriv (fun y : ℝ => (1 + Real.exp (y⁻¹ - (1 - y)⁻¹))⁻¹) x := by
    simp only [one_div]
  rw [hone, hInv.deriv, smoothTransition_eq_inv_one_add_exp hx]
  have hpos : (0 : ℝ) < 1 + Real.exp (x⁻¹ - (1 - x)⁻¹) := by positivity
  field_simp
  ring

/-- `v'` 的导数（`(0,1)` 上）。 -/
lemma hasDerivAt_sigmaV1 {x : ℝ} (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    HasDerivAt sigmaV1 (sigmaV2 x) x := by
  have h1 : HasDerivAt (fun y : ℝ => y ^ 2) ((2 : ℕ) * x ^ (2 - 1)) x := hasDerivAt_pow 2 x
  have h2 : HasDerivAt (fun y : ℝ => (y ^ 2)⁻¹) (-((2 : ℕ) * x ^ (2 - 1)) / (x ^ 2) ^ 2) x :=
    h1.inv (by positivity)
  have h3 : HasDerivAt (fun y : ℝ => (1 - y) ^ 2)
      ((2 : ℕ) * (1 - x) ^ (2 - 1) * (0 - 1)) x :=
    ((hasDerivAt_const (x := x) (c := (1 : ℝ))).sub (hasDerivAt_id x)).pow 2
  have h4 : HasDerivAt (fun y : ℝ => ((1 - y) ^ 2)⁻¹)
      (-((2 : ℕ) * (1 - x) ^ (2 - 1) * (0 - 1)) / ((1 - x) ^ 2) ^ 2) x :=
    h3.inv (by positivity)
  have h5 : HasDerivAt (fun y : ℝ => (y ^ 2)⁻¹ + ((1 - y) ^ 2)⁻¹) (sigmaV2 x) x := by
    rw [show sigmaV2 x = -((2 : ℕ) * x ^ (2 - 1)) / (x ^ 2) ^ 2
        + (-((2 : ℕ) * (1 - x) ^ (2 - 1) * (0 - 1)) / ((1 - x) ^ 2) ^ 2) by
      simp only [sigmaV2]
      field_simp
      ring]
    exact h2.add h4
  exact h5

/-- `smoothTransition` 的二阶导数的显式公式（`(0,1)` 上）。 -/
lemma deriv2_smoothTransition_eq {x : ℝ} (hx : x ∈ Set.Ioo 0 1) :
    deriv (deriv Real.smoothTransition) x
      = Real.smoothTransition x * (1 - Real.smoothTransition x)
        * ((1 - 2 * Real.smoothTransition x) * (sigmaV1 x) ^ 2 + sigmaV2 x) := by
  have hev : deriv Real.smoothTransition =ᶠ[nhds x]
      fun y : ℝ => Real.smoothTransition y * (1 - Real.smoothTransition y) * sigmaV1 y := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact deriv_smoothTransition_eq hy
  rw [hev.deriv_eq]
  have hσ : HasDerivAt Real.smoothTransition
      (Real.smoothTransition x * (1 - Real.smoothTransition x) * sigmaV1 x) x := by
    have h : DifferentiableAt ℝ Real.smoothTransition x :=
      (Real.smoothTransition.contDiff (n := 2)).differentiable (by norm_num) x
    rw [← deriv_smoothTransition_eq hx]
    exact h.hasDerivAt
  have h2 : HasDerivAt sigmaV1 (sigmaV2 x) x :=
    hasDerivAt_sigmaV1 (ne_of_gt hx.1) (ne_of_lt hx.2)
  have h3 := (hσ.mul (hσ.const_sub 1)).mul h2
  change deriv ((Real.smoothTransition * fun y : ℝ => 1 - Real.smoothTransition y) * sigmaV1) x
      = Real.smoothTransition x * (1 - Real.smoothTransition x)
        * ((1 - 2 * Real.smoothTransition x) * (sigmaV1 x) ^ 2 + sigmaV2 x)
  rw [h3.deriv]
  simp only [Pi.mul_apply]
  ring

/-! ## 2. `(0,1)` 之外导数恒为零 -/

lemma deriv_smoothTransition_eq_zero_of_neg {y : ℝ} (hy : y < 0) :
    deriv Real.smoothTransition y = 0 := by
  have hev : Real.smoothTransition =ᶠ[nhds y] fun _ : ℝ => (0 : ℝ) := by
    filter_upwards [isOpen_Iio.mem_nhds hy] with z hz
    exact Real.smoothTransition.zero_of_nonpos hz.le
  rw [hev.deriv_eq]
  exact deriv_const y 0

lemma deriv_smoothTransition_eq_zero_of_one_lt {y : ℝ} (hy : 1 < y) :
    deriv Real.smoothTransition y = 0 := by
  have hev : Real.smoothTransition =ᶠ[nhds y] fun _ : ℝ => (1 : ℝ) := by
    filter_upwards [isOpen_Ioi.mem_nhds hy] with z hz
    exact Real.smoothTransition.one_of_one_le hz.le
  rw [hev.deriv_eq]
  exact deriv_const y 1

lemma continuous_deriv_smoothTransition : Continuous (deriv Real.smoothTransition) :=
  ((Real.smoothTransition.contDiff (n := 2)).continuous_deriv (by norm_num))

lemma deriv_smoothTransition_eq_zero_of_nonpos {y : ℝ} (hy : y ≤ 0) :
    deriv Real.smoothTransition y = 0 := by
  rcases lt_or_eq_of_le hy with h | rfl
  · exact deriv_smoothTransition_eq_zero_of_neg h
  · have h1 : Tendsto (deriv Real.smoothTransition) (𝓝[Set.Iio (0 : ℝ)] 0)
        (𝓝 (deriv Real.smoothTransition 0)) :=
      continuous_deriv_smoothTransition.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (deriv Real.smoothTransition) (𝓝[Set.Iio (0 : ℝ)] 0) (𝓝 0) := by
      have hev : (deriv Real.smoothTransition) =ᶠ[𝓝[Set.Iio (0 : ℝ)] 0] fun _ => (0 : ℝ) := by
        filter_upwards [self_mem_nhdsWithin] with z hz
        exact deriv_smoothTransition_eq_zero_of_neg hz
      exact tendsto_const_nhds.congr' hev.symm
    exact tendsto_nhds_unique h1 h2

lemma deriv_smoothTransition_eq_zero_of_one_le {y : ℝ} (hy : 1 ≤ y) :
    deriv Real.smoothTransition y = 0 := by
  rcases lt_or_eq_of_le hy with h | rfl
  · exact deriv_smoothTransition_eq_zero_of_one_lt h
  · have h1 : Tendsto (deriv Real.smoothTransition) (𝓝[Set.Ioi (1 : ℝ)] 1)
        (𝓝 (deriv Real.smoothTransition 1)) :=
      continuous_deriv_smoothTransition.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (deriv Real.smoothTransition) (𝓝[Set.Ioi (1 : ℝ)] 1) (𝓝 0) := by
      have hev : (deriv Real.smoothTransition) =ᶠ[𝓝[Set.Ioi (1 : ℝ)] 1] fun _ => (0 : ℝ) := by
        filter_upwards [self_mem_nhdsWithin] with z hz
        exact deriv_smoothTransition_eq_zero_of_one_lt hz
      exact tendsto_const_nhds.congr' hev.symm
    exact tendsto_nhds_unique h1 h2

lemma continuous_deriv2_smoothTransition : Continuous (deriv (deriv Real.smoothTransition)) := by
  have h1 : ContDiff ℝ 2 (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := (2 : ℕ∞) + 1)).deriv'
  have h2 : ContDiff ℝ 1 (deriv (deriv Real.smoothTransition)) := h1.deriv'
  exact h2.continuous

lemma deriv2_smoothTransition_eq_zero_of_lt_zero {y : ℝ} (hy : y < 0) :
    deriv (deriv Real.smoothTransition) y = 0 := by
  have hev : deriv Real.smoothTransition =ᶠ[nhds y] fun _ : ℝ => (0 : ℝ) := by
    filter_upwards [isOpen_Iio.mem_nhds hy] with z hz
    exact deriv_smoothTransition_eq_zero_of_neg hz
  rw [hev.deriv_eq]
  exact deriv_const y 0

lemma deriv2_smoothTransition_eq_zero_of_one_lt {y : ℝ} (hy : 1 < y) :
    deriv (deriv Real.smoothTransition) y = 0 := by
  have hev : deriv Real.smoothTransition =ᶠ[nhds y] fun _ : ℝ => (0 : ℝ) := by
    filter_upwards [isOpen_Ioi.mem_nhds hy] with z hz
    exact deriv_smoothTransition_eq_zero_of_one_lt hz
  rw [hev.deriv_eq]
  exact deriv_const y 0

/-- `(0,1)` 之外（含端点 `0`、`1`）二阶导数为零。 -/
lemma deriv2_smoothTransition_eq_zero_of_notMem {y : ℝ} (hy : y ∉ Set.Ioo 0 1) :
    deriv (deriv Real.smoothTransition) y = 0 := by
  rw [Set.mem_Ioo, not_and_or, not_lt, not_lt] at hy
  rcases hy with hy | hy
  · rcases lt_or_eq_of_le hy with h | rfl
    · exact deriv2_smoothTransition_eq_zero_of_lt_zero h
    · have h1 : Tendsto (deriv (deriv Real.smoothTransition)) (𝓝[Set.Iio (0 : ℝ)] 0)
          (𝓝 (deriv (deriv Real.smoothTransition) 0)) :=
        continuous_deriv2_smoothTransition.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      have h2 : Tendsto (deriv (deriv Real.smoothTransition)) (𝓝[Set.Iio (0 : ℝ)] 0) (𝓝 0) := by
        have hev : (deriv (deriv Real.smoothTransition)) =ᶠ[𝓝[Set.Iio (0 : ℝ)] 0]
            fun _ => (0 : ℝ) := by
          filter_upwards [self_mem_nhdsWithin] with z hz
          exact deriv2_smoothTransition_eq_zero_of_lt_zero hz
        exact tendsto_const_nhds.congr' hev.symm
      exact tendsto_nhds_unique h1 h2
  · rcases lt_or_eq_of_le hy with h | rfl
    · exact deriv2_smoothTransition_eq_zero_of_one_lt h
    · have h1 : Tendsto (deriv (deriv Real.smoothTransition)) (𝓝[Set.Ioi (1 : ℝ)] 1)
          (𝓝 (deriv (deriv Real.smoothTransition) 1)) :=
        continuous_deriv2_smoothTransition.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      have h2 : Tendsto (deriv (deriv Real.smoothTransition)) (𝓝[Set.Ioi (1 : ℝ)] 1) (𝓝 0) := by
        have hev : (deriv (deriv Real.smoothTransition)) =ᶠ[𝓝[Set.Ioi (1 : ℝ)] 1]
            fun _ => (0 : ℝ) := by
          filter_upwards [self_mem_nhdsWithin] with z hz
          exact deriv2_smoothTransition_eq_zero_of_one_lt hz
        exact tendsto_const_nhds.congr' hev.symm
      exact tendsto_nhds_unique h1 h2

/-! ## 3. 数值引理：多项式 × 指数的一致界 -/

/-- `U(u) = (3/2)u²+8`：`sigmaV1` 的上界。 -/
def U2 (u : ℝ) : ℝ := (3 / 2) * u ^ 2 + 8

/-- `W(u) = (3/2)u²+u+12`：`t²+ts+s²` 的上界。 -/
def W2 (u : ℝ) : ℝ := (3 / 2) * u ^ 2 + u + 12

lemma hasDerivAt_U2 (v : ℝ) : HasDerivAt U2 (3 * v) v := by
  have h' : HasDerivAt (fun u : ℝ => (3 / 2) * u ^ 2) ((3 / 2) * ((2 : ℕ) * v ^ (2 - 1))) v :=
    (hasDerivAt_pow 2 v).const_mul (3 / 2)
  have h'' : HasDerivAt (fun u : ℝ => (3 / 2) * u ^ 2 + 8)
      ((3 / 2) * ((2 : ℕ) * v ^ (2 - 1))) v := h'.add_const 8
  have hval : (3 / 2) * ((2 : ℕ) * v ^ (2 - 1)) = 3 * v := by ring
  rw [hval] at h''
  exact h''

lemma exp_neg_mul_U2_antitoneOn :
    AntitoneOn (fun u : ℝ => Real.exp (-u) * U2 u) (Set.Ici 0) := by
  refine antitoneOn_of_deriv_nonpos (convex_Ici 0) ?_ ?_ ?_
  · have hc : Continuous fun u : ℝ => Real.exp (-u) * U2 u := by
      simp only [U2]
      fun_prop
    exact hc.continuousOn
  · intro x _
    have hd : DifferentiableAt ℝ (fun u : ℝ => Real.exp (-u) * U2 u) x := by
      simp only [U2]
      fun_prop
    exact hd.differentiableWithinAt
  · intro u _
    have hderiv : deriv (fun t : ℝ => Real.exp (-t) * U2 t) u
        = Real.exp (-u) * (3 * u - U2 u) := by
      have h : HasDerivAt (fun t : ℝ => Real.exp (-t) * U2 t)
          (Real.exp (-u) * (-1) * U2 u + Real.exp (-u) * (3 * u)) u :=
        ((hasDerivAt_neg u).exp).mul (hasDerivAt_U2 u)
      rw [h.deriv]
      ring
    rw [hderiv]
    have hneg : 3 * u - U2 u < 0 := by
      simp only [U2]
      nlinarith [sq_nonneg (u - 1)]
    nlinarith [Real.exp_pos (-u)]

lemma exp_neg_mul_U2_sq_antitoneOn :
    AntitoneOn (fun u : ℝ => Real.exp (-u) * (U2 u) ^ 2) (Set.Ici 0) := by
  refine antitoneOn_of_deriv_nonpos (convex_Ici 0) ?_ ?_ ?_
  · have hc : Continuous fun u : ℝ => Real.exp (-u) * (U2 u) ^ 2 := by
      simp only [U2]
      fun_prop
    exact hc.continuousOn
  · intro x _
    have hd : DifferentiableAt ℝ (fun u : ℝ => Real.exp (-u) * (U2 u) ^ 2) x := by
      simp only [U2]
      fun_prop
    exact hd.differentiableWithinAt
  · intro u _
    have hderiv : deriv (fun t : ℝ => Real.exp (-t) * (U2 t) ^ 2) u
        = Real.exp (-u) * (2 * U2 u * (3 * u) - (U2 u) ^ 2) := by
      have h1 : HasDerivAt (fun t : ℝ => Real.exp (-t)) (Real.exp (-u) * (-1)) u := by
        simpa using (hasDerivAt_neg u).exp
      have h2 : HasDerivAt (fun t : ℝ => (U2 t) ^ 2) (2 * (U2 u) ^ (2 - 1) * (3 * u)) u :=
        (hasDerivAt_U2 u).pow 2
      have h := h1.mul h2
      rw [show (fun t : ℝ => Real.exp (-t) * (U2 t) ^ 2)
          = (fun t : ℝ => Real.exp (-t)) * (fun t : ℝ => (U2 t) ^ 2) from rfl, h.deriv]
      ring
    rw [hderiv]
    have hU : 0 < U2 u := by
      simp only [U2]
      positivity
    have h6 : 6 * u - U2 u < 0 := by
      simp only [U2]
      nlinarith [sq_nonneg (u - 2)]
    have hprod : U2 u * (6 * u - U2 u) < 0 := mul_neg_of_pos_of_neg hU h6
    have heq : 2 * U2 u * (3 * u) - (U2 u) ^ 2 = U2 u * (6 * u - U2 u) := by ring
    rw [heq]
    exact le_of_lt (mul_neg_of_pos_of_neg (Real.exp_pos (-u)) hprod)

lemma exp_seven_fifths_bounds : (4 : ℝ) ≤ Real.exp (7 / 5) ∧ Real.exp (7 / 5) ≤ 5 := by
  have hsum := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 7 / 5) 7
  have h4 : (4 : ℝ) ≤ ∑ i ∈ Finset.range 7, (7 / 5 : ℝ) ^ i / ((i.factorial : ℕ) : ℝ) := by
    norm_num [Finset.sum_range_succ]
  have hle : Real.exp (7 / 5) ≤ 5 := by
    have hsplit : Real.exp (7 / 5) = Real.exp 1 * Real.exp (2 / 5) := by
      rw [← Real.exp_add]
      norm_num
    have h3 : (1 : ℝ) - 2 / 5 ≤ Real.exp (-(2 / 5)) := by
      linarith [Real.add_one_le_exp (-(2 / 5))]
    rw [Real.exp_neg] at h3
    have hpos : (0 : ℝ) < Real.exp (2 / 5) := Real.exp_pos _
    have h4' : (3 / 5) * Real.exp (2 / 5) ≤ 1 := by
      have hh := mul_le_mul_of_nonneg_right h3 hpos.le
      rw [inv_mul_cancel₀ (ne_of_gt hpos)] at hh
      linarith
    have h5 : Real.exp (2 / 5) ≤ 5 / 3 := by linarith
    have h6 : Real.exp 1 ≤ 3 := Real.exp_one_lt_three.le
    calc Real.exp (7 / 5) = Real.exp 1 * Real.exp (2 / 5) := hsplit
      _ ≤ 3 * (5 / 3) := by
          exact mul_le_mul h6 h5 (Real.exp_pos _).le (by norm_num)
      _ = 5 := by norm_num
  exact ⟨by linarith, hle⟩

lemma exp_neg_seven_fifths_le : Real.exp (-(7 / 5)) ≤ 1 / 4 := by
  have h := exp_seven_fifths_bounds.1
  have h' : (Real.exp (7 / 5))⁻¹ ≤ (4 : ℝ)⁻¹ :=
    (inv_le_inv₀ (Real.exp_pos _) (by norm_num)).mpr h
  rw [Real.exp_neg]
  simpa only [one_div] using h'

lemma le_exp_neg_seven_fifths : (1 : ℝ) / 5 ≤ Real.exp (-(7 / 5)) := by
  have h := exp_seven_fifths_bounds.2
  have h' : (5 : ℝ)⁻¹ ≤ (Real.exp (7 / 5))⁻¹ :=
    (inv_le_inv₀ (by norm_num) (Real.exp_pos _)).mpr h
  rw [Real.exp_neg]
  simpa only [one_div] using h'

/-- `t^n e^{-t} ≤ n^n e^{-n}`（`t ≥ 0`）。 -/
lemma pow_mul_exp_neg_le (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    t ^ n * Real.exp (-t) ≤ (n : ℝ) ^ n * Real.exp (-(n : ℝ)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h1 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    simpa using h1
  · have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hnne : (n : ℝ) ≠ 0 := ne_of_gt hn'
    have h1 : t / n ≤ Real.exp (t / n - 1) := by
      have hh := Real.add_one_le_exp (t / n - 1)
      linarith
    have h2 : (t / n) ^ n ≤ (Real.exp (t / n - 1)) ^ n :=
      pow_le_pow_left₀ (by positivity) h1 n
    have h3 : (Real.exp (t / n - 1)) ^ n = Real.exp (t - (n : ℝ)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      field_simp
    have h4 : (t / n) ^ n * (n : ℝ) ^ n = t ^ n := by
      rw [← mul_pow]
      field_simp
    have h5 : t ^ n ≤ (n : ℝ) ^ n * Real.exp (t - (n : ℝ)) := by
      rw [← h4]
      calc (t / n) ^ n * (n : ℝ) ^ n = (n : ℝ) ^ n * (t / n) ^ n := by ring
        _ ≤ (n : ℝ) ^ n * Real.exp (t - (n : ℝ)) :=
            mul_le_mul_of_nonneg_left (h2.trans_eq h3) (by positivity)
    calc t ^ n * Real.exp (-t)
        ≤ (n : ℝ) ^ n * Real.exp (t - (n : ℝ)) * Real.exp (-t) :=
          mul_le_mul_of_nonneg_right h5 (Real.exp_pos _).le
      _ = (n : ℝ) ^ n * Real.exp (-(n : ℝ)) := by
          rw [mul_assoc, ← Real.exp_add, show t - (n : ℝ) + -t = -(n : ℝ) by ring]

/-! ## 4. `min(1/4, e^{-u})` 型数值界 -/

lemma min_exp_neg_mul_U2_le (u : ℝ) (hu : 0 ≤ u) :
    min (1 / 4) (Real.exp (-u)) * U2 u ≤ 3 := by
  have hU2 : U2 (7 / 5) = 10.94 := by norm_num [U2]
  have hUpos : ∀ v : ℝ, 0 ≤ U2 v := by intro v; simp only [U2]; positivity
  rcases le_or_gt u (7 / 5) with h | h
  · have h1 : min (1 / 4) (Real.exp (-u)) ≤ 1 / 4 := min_le_left _ _
    have h2 : U2 u ≤ U2 (7 / 5) := by simp only [U2]; nlinarith
    nlinarith [h1, h2, hU2, hUpos u]
  · have h1 : min (1 / 4) (Real.exp (-u)) ≤ Real.exp (-u) := min_le_right _ _
    have h2 : Real.exp (-u) * U2 u ≤ Real.exp (-(7 / 5)) * U2 (7 / 5) :=
      exp_neg_mul_U2_antitoneOn (by norm_num) hu (le_of_lt h)
    have h3 : Real.exp (-(7 / 5)) ≤ 1 / 4 := exp_neg_seven_fifths_le
    nlinarith [h1, h2, h3, hU2, hUpos u, Real.exp_pos (-u)]

/-! ## 5. `sigmaV x` 与 `sigmaV1 x`、`sigmaV2 x` 的大小关系 -/

lemma smoothTransition_eq_inv_exp_neg_sigmaV {x : ℝ} (hx : x ∈ Set.Ioo 0 1) :
    Real.smoothTransition x = 1 / (1 + Real.exp (-(sigmaV x))) := by
  rw [smoothTransition_eq_inv_one_add_exp hx]
  congr 2
  simp only [sigmaV]
  ring_nf

lemma sigmaV1_pos {x : ℝ} (hx : x ∈ Set.Ioo 0 1) : 0 < sigmaV1 x := by
  have h1 : sigmaV1 x = (x⁻¹) ^ 2 + ((1 - x)⁻¹) ^ 2 := by
    simp only [sigmaV1, ← inv_pow]
  rw [h1]
  have : 0 < x⁻¹ := inv_pos.mpr hx.1
  positivity

/-- `v'(x) = (x⁻¹)² + ((1-x)⁻¹)²`。 -/
lemma sigmaV1_eq_inv {x : ℝ} :
    sigmaV1 x = (x⁻¹) ^ 2 + ((1 - x)⁻¹) ^ 2 := by
  simp only [sigmaV1, ← inv_pow]

/-- `sigmaV2 x = 2·(s³-t³) = 2·v·(t²+ts+s²)`。 -/
lemma sigmaV2_eq {x : ℝ} :
    sigmaV2 x = 2 * sigmaV x * ((x⁻¹) ^ 2 + x⁻¹ * (1 - x)⁻¹ + ((1 - x)⁻¹) ^ 2) := by
  simp only [sigmaV2, sigmaV, ← inv_pow]
  ring

/-- `t·s = t+s`（`t = 1/x`，`s = 1/(1-x)`）。 -/
lemma inv_mul_inv_eq_add {x : ℝ} (hx0 : x ≠ 0) (hx1 : 1 - x ≠ 0) :
    x⁻¹ * (1 - x)⁻¹ = x⁻¹ + (1 - x)⁻¹ := by
  field_simp
  ring

/-- `sigmaV1 x ≤ U2 |sigmaV x|`。 -/
lemma sigmaV1_le_U2 {x : ℝ} (hx : x ∈ Set.Ioo 0 1) :
    sigmaV1 x ≤ U2 |sigmaV x| := by
  have hx0 : x ≠ 0 := ne_of_gt hx.1
  have hx1 : 1 - x ≠ 0 := by linarith [hx.2]
  have hts : x⁻¹ * (1 - x)⁻¹ = x⁻¹ + (1 - x)⁻¹ := inv_mul_inv_eq_add hx0 hx1
  rw [sigmaV1_eq_inv, U2, sq_abs]
  have h2 : sigmaV x = (1 - x)⁻¹ - x⁻¹ := rfl
  rw [h2]
  nlinarith [sq_nonneg ((1 - x)⁻¹ + x⁻¹ - 4), hts]

/-- `1/x + 1/(1-x) ≤ |v x| + 4`。 -/
lemma inv_add_inv_le {x : ℝ} (hx : x ∈ Set.Ioo 0 1) :
    x⁻¹ + (1 - x)⁻¹ ≤ |sigmaV x| + 4 := by
  have hx0 : x ≠ 0 := ne_of_gt hx.1
  have hx1 : 1 - x ≠ 0 := by linarith [hx.2]
  have hts : x⁻¹ * (1 - x)⁻¹ = x⁻¹ + (1 - x)⁻¹ := inv_mul_inv_eq_add hx0 hx1
  have hpos : 0 < x⁻¹ + (1 - x)⁻¹ := by
    have h1 : 0 < x⁻¹ := inv_pos.mpr hx.1
    have h2 : 0 < (1 - x)⁻¹ := inv_pos.mpr (by linarith [hx.2])
    linarith
  have hkey : (x⁻¹ + (1 - x)⁻¹) * (x⁻¹ + (1 - x)⁻¹ - 4) = ((1 - x)⁻¹ - x⁻¹) ^ 2 := by
    nlinarith [hts]
  have hw4 : 4 ≤ x⁻¹ + (1 - x)⁻¹ := by
    by_contra hcon
    push_neg at hcon
    nlinarith [hkey, hpos, hcon]
  have hsq : ((1 - x)⁻¹ - x⁻¹) ^ 2 = |sigmaV x| ^ 2 := by
    rw [sigmaV, sq_abs]
  have hle : (x⁻¹ + (1 - x)⁻¹ - 4) ^ 2 ≤ |sigmaV x| ^ 2 := by
    rw [← hsq]
    nlinarith [hkey, hw4]
  have habs := sq_le_sq.mp hle
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ x⁻¹ + (1 - x)⁻¹ - 4)] at habs
  simpa using habs

/-- `t²+ts+s² ≤ W2 |v x|`。 -/
lemma sigmaV_quad_le_W2 {x : ℝ} (hx : x ∈ Set.Ioo 0 1) :
    (x⁻¹) ^ 2 + x⁻¹ * (1 - x)⁻¹ + ((1 - x)⁻¹) ^ 2 ≤ W2 |sigmaV x| := by
  have hU := sigmaV1_le_U2 hx
  have hw := inv_add_inv_le hx
  have hts : x⁻¹ * (1 - x)⁻¹ = x⁻¹ + (1 - x)⁻¹ :=
    inv_mul_inv_eq_add (ne_of_gt hx.1) (by linarith [hx.2])
  rw [sigmaV1_eq_inv] at hU
  simp only [U2] at hU
  simp only [W2]
  nlinarith [hU, hw, hts]

/-- `|sigmaV2 x| ≤ 2|v x|·W2 |v x|`。 -/
lemma abs_sigmaV2_le {x : ℝ} (hx : x ∈ Set.Ioo 0 1) :
    |sigmaV2 x| ≤ 2 * |sigmaV x| * W2 |sigmaV x| := by
  have h1 : 0 < x⁻¹ := inv_pos.mpr hx.1
  have h2 : 0 < (1 - x)⁻¹ := inv_pos.mpr (by linarith [hx.2])
  have hQ : 0 ≤ (x⁻¹) ^ 2 + x⁻¹ * (1 - x)⁻¹ + ((1 - x)⁻¹) ^ 2 := by positivity
  have hquad := sigmaV_quad_le_W2 hx
  rw [sigmaV2_eq, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    abs_of_nonneg hQ]
  exact mul_le_mul_of_nonneg_left hquad (by positivity)


/-! ## 6. `σ(1-σ)`、`σ(1-σ)|1-2σ|` 的指数型界 -/

/-- 纯代数：`t > 0` 时 `t/(1+t)² ≤ t`。 -/
lemma div_sq_le_self {t : ℝ} (ht : 0 < t) : t / (1 + t) ^ 2 ≤ t := by
  rw [div_le_iff₀ (by positivity)]
  have h2 : 0 < t ^ 2 * (2 + t) := by positivity
  nlinarith [h2]

/-- 纯代数：`t > 0` 时 `t/(1+t)² ≤ 1/4`。 -/
lemma div_sq_le_quarter {t : ℝ} (ht : 0 < t) : t / (1 + t) ^ 2 ≤ 1 / 4 := by
  rw [div_le_iff₀ (by positivity)]
  nlinarith [sq_nonneg (1 - t)]

/-- 纯代数：`t/(1+t)² = t⁻¹/(1+t⁻¹)²`。 -/
lemma div_sq_eq_inv {t : ℝ} (ht : 0 < t) : t / (1 + t) ^ 2 = t⁻¹ / (1 + t⁻¹) ^ 2 := by
  field_simp
  ring

/-- 纯代数：`0 < t ≤ 1` 时 `t|t-1|/(1+t)³ ≤ t(1-t)`。 -/
lemma mul_abs_div_cube_le {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    t * |t - 1| / (1 + t) ^ 3 ≤ t * (1 - t) := by
  rw [abs_of_nonpos (by linarith)]
  rw [div_le_iff₀ (by positivity)]
  have h2 : 0 ≤ t * (1 - t) := mul_nonneg ht0.le (by linarith)
  have h3 : 1 ≤ (1 + t) ^ 3 := by nlinarith [ht0]
  nlinarith [h2, h3]

/-- 纯代数：`t > 1` 时 `t|t-1|/(1+t)³ ≤ t⁻¹(1-t⁻¹)`。 -/
lemma mul_abs_div_cube_le_inv {t : ℝ} (ht : 1 < t) :
    t * |t - 1| / (1 + t) ^ 3 ≤ t⁻¹ * (1 - t⁻¹) := by
  have h0 : 0 < t := by linarith
  rw [abs_of_pos (by linarith)]
  have hle : t⁻¹ ≤ 1 := by rw [inv_le_one₀ h0]; linarith
  have hthis : t⁻¹ * (1 - t⁻¹) / (1 + t⁻¹) ^ 3 ≤ t⁻¹ * (1 - t⁻¹) := by
    have h := mul_abs_div_cube_le (t := t⁻¹) (inv_pos.mpr h0) hle
    rwa [abs_of_nonpos (by linarith : t⁻¹ - 1 ≤ 0),
      show -(t⁻¹ - 1) = 1 - t⁻¹ by ring] at h
  have h1 : t * (t - 1) / (1 + t) ^ 3 = t⁻¹ * (1 - t⁻¹) / (1 + t⁻¹) ^ 3 := by
    field_simp
    ring
  rw [h1]
  exact hthis

/-- 记 `E = e^{-v x}`：`σ x = 1/(1+E)`，故 `σ(1-σ) = E/(1+E)²`。 -/
lemma smoothTransition_mul_one_sub_eq_exp {x : ℝ} (hx : x ∈ Set.Ioo 0 1) :
    Real.smoothTransition x * (1 - Real.smoothTransition x)
      = Real.exp (-(sigmaV x)) / (1 + Real.exp (-(sigmaV x))) ^ 2 := by
  rw [smoothTransition_eq_inv_exp_neg_sigmaV hx]
  have hE : (0 : ℝ) < 1 + Real.exp (-(sigmaV x)) := by positivity
  field_simp
  ring

/-- `σ(1-σ) ≤ e^{-|v x|}`。 -/
lemma smoothTransition_mul_one_sub_le_exp_neg_abs {x : ℝ} (hx : x ∈ Set.Ioo 0 1) :
    Real.smoothTransition x * (1 - Real.smoothTransition x) ≤ Real.exp (-|sigmaV x|) := by
  rw [smoothTransition_mul_one_sub_eq_exp hx]
  rcases le_or_gt 0 (sigmaV x) with hv | hv
  · rw [abs_of_nonneg hv]
    exact div_sq_le_self (Real.exp_pos _)
  · have hz : Real.exp (-|sigmaV x|) = (Real.exp (-(sigmaV x)))⁻¹ := by
      rw [abs_of_neg hv, neg_neg, Real.exp_neg, inv_inv]
    rw [hz, div_sq_eq_inv (Real.exp_pos _)]
    exact div_sq_le_self (inv_pos.mpr (Real.exp_pos _))

/-- `σ(1-σ) ≤ 1/4`。 -/
lemma smoothTransition_mul_one_sub_le_quarter {x : ℝ} (hx : x ∈ Set.Ioo 0 1) :
    Real.smoothTransition x * (1 - Real.smoothTransition x) ≤ 1 / 4 := by
  rw [smoothTransition_mul_one_sub_eq_exp hx]
  exact div_sq_le_quarter (Real.exp_pos _)

/-- `σ(1-σ)|1-2σ| ≤ z(1-z)`，`z = e^{-|v x|}`。 -/
lemma smoothTransition_mul_one_sub_mul_abs_le {x : ℝ} (hx : x ∈ Set.Ioo 0 1) :
    Real.smoothTransition x * (1 - Real.smoothTransition x) * |1 - 2 * Real.smoothTransition x|
      ≤ Real.exp (-|sigmaV x|) * (1 - Real.exp (-|sigmaV x|)) := by
  have h1 : (0 : ℝ) < 1 + Real.exp (-(sigmaV x)) := by positivity
  have h3 : 1 / (1 + Real.exp (-(sigmaV x))) * (1 - 1 / (1 + Real.exp (-(sigmaV x))))
      = Real.exp (-(sigmaV x)) / (1 + Real.exp (-(sigmaV x))) ^ 2 := by
    field_simp
    ring
  have h2 : |1 - 2 * (1 / (1 + Real.exp (-(sigmaV x))))|
      = |Real.exp (-(sigmaV x)) - 1| / (1 + Real.exp (-(sigmaV x))) := by
    rw [show 1 - 2 * (1 / (1 + Real.exp (-(sigmaV x))))
        = (Real.exp (-(sigmaV x)) - 1) / (1 + Real.exp (-(sigmaV x))) by
      field_simp
      ring]
    rw [abs_div, abs_of_pos h1]
  have hid : Real.smoothTransition x * (1 - Real.smoothTransition x)
      * |1 - 2 * Real.smoothTransition x|
      = Real.exp (-(sigmaV x)) * |Real.exp (-(sigmaV x)) - 1|
        / (1 + Real.exp (-(sigmaV x))) ^ 3 := by
    rw [smoothTransition_eq_inv_exp_neg_sigmaV hx, h3, h2]
    field_simp
  rw [hid]
  rcases le_or_gt 0 (sigmaV x) with hv | hv
  · have hE1 : Real.exp (-(sigmaV x)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hz : Real.exp (-|sigmaV x|) = Real.exp (-(sigmaV x)) := by rw [abs_of_nonneg hv]
    rw [hz]
    exact mul_abs_div_cube_le (Real.exp_pos _) hE1
  · have hE1 : 1 < Real.exp (-(sigmaV x)) := Real.one_lt_exp_iff.mpr (by linarith)
    have hz : Real.exp (-|sigmaV x|) = (Real.exp (-(sigmaV x)))⁻¹ := by
      rw [abs_of_neg hv, neg_neg, Real.exp_neg, inv_inv]
    rw [hz]
    exact mul_abs_div_cube_le_inv hE1

/-! ## 7. 辅助数值引理（`max` 技巧与符号） -/

/-- 纯代数：`a·b ≤ 0` 时 `|a+b| ≤ max |a| |b|`。 -/
lemma abs_add_le_max_of_mul_nonpos {a b : ℝ} (h : a * b ≤ 0) : |a + b| ≤ max |a| |b| := by
  rcases le_or_gt 0 a with ha | ha
  · rcases le_or_gt 0 b with hb | hb
    · have h0 : a * b = 0 := le_antisymm h (mul_nonneg ha hb)
      rcases eq_zero_or_eq_zero_of_mul_eq_zero h0 with h1 | h1
      · rw [h1, zero_add, abs_of_nonneg hb]
        exact le_max_right _ _
      · rw [h1, add_zero, abs_of_nonneg ha]
        exact le_max_left _ _
    · rw [abs_of_nonneg ha, abs_of_neg hb, abs_le]
      exact ⟨by linarith [le_max_right a (-b)], by linarith [le_max_left a (-b)]⟩
  · rcases le_or_gt 0 b with hb | hb
    · rw [abs_of_neg ha, abs_of_nonneg hb, abs_le]
      exact ⟨by linarith [le_max_left (-a) b], by linarith [le_max_right (-a) b]⟩
    · exact absurd h (not_le.mpr (mul_pos_of_neg_of_neg ha hb))

/-- `(1-2σ x)·v x ≤ 0`（`x ∈ (0,1)`）。 -/
lemma one_sub_two_mul_smoothTransition_mul_sigmaV_nonpos {x : ℝ} (hx : x ∈ Set.Ioo 0 1) :
    (1 - 2 * Real.smoothTransition x) * sigmaV x ≤ 0 := by
  have h1 : (0 : ℝ) < 1 + Real.exp (-(sigmaV x)) := by positivity
  have h2 : 1 - 2 * (1 / (1 + Real.exp (-(sigmaV x))))
      = (Real.exp (-(sigmaV x)) - 1) / (1 + Real.exp (-(sigmaV x))) := by
    field_simp
    ring
  rw [smoothTransition_eq_inv_exp_neg_sigmaV hx, h2]
  have h3 : 0 ≤ sigmaV x * (1 - Real.exp (-(sigmaV x))) := by
    rcases le_or_gt 0 (sigmaV x) with hv | hv
    · have hv' : Real.exp (-(sigmaV x)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      nlinarith [hv]
    · have hv' : 1 ≤ Real.exp (-(sigmaV x)) := by
        rw [← Real.exp_zero, Real.exp_le_exp]
        linarith
      nlinarith [hv]
  have h4 : (Real.exp (-(sigmaV x)) - 1) / (1 + Real.exp (-(sigmaV x))) * sigmaV x
      = -(sigmaV x * (1 - Real.exp (-(sigmaV x))) / (1 + Real.exp (-(sigmaV x)))) := by
    ring
  rw [h4]
  exact neg_nonpos.mpr (div_nonneg h3 h1.le)

/-! ## 8. 显式常数 `K₀ = 21.1` 与导数的一致界

`K₀ = 21.1` 由下述分支估计得到（真实上确界约为 `9.8410`）：

* `(1+z)³ ≥ 1+3z+3z²`（`z = e^{-u}`）把二阶导数中的分母 `(1+z)³` 换成更小的 `1+3z+3z²`；
* 对 `u` 用 `7/5, 2, 5/2, 3, 7/2` 六个分支点做分段估计，每段用显式有理指数界；
* 一阶导数用 `min(1/4, e^{-u})·U2(u) ≤ 3`。
-/

/-- **显式常数**：`K₀ = 21.1` 同时控制 `|σ'|` 与 `|σ''|` 的一致界。 -/
def K₀ : ℝ := 21.1

lemma K₀_pos : 0 < K₀ := by norm_num [K₀]

lemma K₀_eq : K₀ = 21.1 := rfl

lemma one_add_cube_ge (z : ℝ) (hz : 0 ≤ z) : 1 + 3 * z + 3 * z ^ 2 ≤ (1 + z) ^ 3 := by
  nlinarith [pow_nonneg hz 3]

/-- `e^{1/2} ∈ [1.6487, 1.65]`。 -/
lemma exp_half_bounds : (1.6487 : ℝ) ≤ Real.exp (1 / 2) ∧ Real.exp (1 / 2) ≤ 1.65 := by
  constructor
  · have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) 10
    norm_num [Finset.sum_range_succ] at h
    linarith
  · have h2 : (Real.exp (1 / 2)) ^ 2 = Real.exp 1 := by
      rw [← Real.exp_nat_mul]
      norm_num
    have h1 : Real.exp 1 ≤ 2.7225 := by linarith [Real.exp_one_lt_d9]
    have h3 : (Real.exp (1 / 2)) ^ 2 ≤ (1.65 : ℝ) ^ 2 := by
      rw [h2]
      norm_num
      linarith
    have h4 := sq_le_sq.mp h3
    rw [abs_le, abs_of_pos (by norm_num : (0:ℝ) < 1.65)] at h4
    exact h4.2

/-- `e² ∈ [7, 8]`。 -/
lemma exp_two_bounds : (7.389 : ℝ) ≤ Real.exp 2 ∧ Real.exp 2 ≤ 7.39 := by
  have hsq : Real.exp 2 = (Real.exp 1) ^ 2 := by
    rw [← Real.exp_nat_mul]
    norm_num
  constructor
  · rw [hsq]
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7182818283) Real.exp_one_gt_d9.le 2
    norm_num at h
    linarith
  · rw [hsq]
    have h := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 2
    norm_num at h
    linarith

/-- `e³ ∈ [20, 21]`。 -/
lemma exp_three_bounds : (20.08 : ℝ) ≤ Real.exp 3 ∧ Real.exp 3 ≤ 21 := by
  have hc : Real.exp 3 = (Real.exp 1) ^ 3 := by
    rw [← Real.exp_nat_mul]
    norm_num
  constructor
  · rw [hc]
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7182818283) Real.exp_one_gt_d9.le 3
    norm_num at h
    linarith
  · rw [hc]
    have h := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 3
    norm_num at h
    linarith

/-- `e^{11/5} ∈ [9, 10]`。 -/
lemma exp_eleven_fifths_bounds : (9 : ℝ) ≤ Real.exp (11 / 5) ∧ Real.exp (11 / 5) ≤ 10 := by
  constructor
  · have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 11 / 5) 10
    norm_num [Finset.sum_range_succ] at h
    linarith
  · have hsplit : Real.exp (11 / 5) = Real.exp 2 * Real.exp (1 / 5) := by
      rw [← Real.exp_add]
      norm_num
    have h2 : Real.exp 2 ≤ 7.39 := exp_two_bounds.2
    have h3 : Real.exp (1 / 5) ≤ 5 / 4 := by
      have h : (4 : ℝ) / 5 ≤ (Real.exp (1 / 5))⁻¹ := by
        have hh := Real.add_one_le_exp (-(1 / 5))
        rw [Real.exp_neg] at hh
        linarith
      have hpos : (0 : ℝ) < Real.exp (1 / 5) := Real.exp_pos _
      have h4 : (4 / 5) * Real.exp (1 / 5) ≤ 1 := by
        have := mul_le_mul_of_nonneg_right h hpos.le
        rwa [inv_mul_cancel₀ (ne_of_gt hpos)] at this
      linarith
    rw [hsplit]
    have hb : Real.exp 2 * Real.exp (1 / 5) ≤ 7.39 * (5 / 4) :=
      mul_le_mul h2 h3 (Real.exp_pos _).le (by norm_num)
    linarith [hb]

/-- `e^{5/2} ∈ [12, 13]`。 -/
lemma exp_five_halves_bounds : (12 : ℝ) ≤ Real.exp (5 / 2) ∧ Real.exp (5 / 2) ≤ 13 := by
  have hsplit : Real.exp (5 / 2) = Real.exp 2 * Real.exp (1 / 2) := by
    rw [← Real.exp_add]
    norm_num
  have h2 := exp_two_bounds
  have hh := exp_half_bounds
  rw [hsplit]
  constructor
  · have hb : 7.389 * 1.6487 ≤ Real.exp 2 * Real.exp (1 / 2) :=
      mul_le_mul h2.1 hh.1 (by norm_num) (by linarith [h2.2])
    linarith [hb]
  · have hb : Real.exp 2 * Real.exp (1 / 2) ≤ 7.39 * 1.65 :=
      mul_le_mul h2.2 hh.2 (Real.exp_pos _).le (by norm_num)
    linarith [hb]

/-- `e^{7/2} ∈ [33, 42]`。 -/
lemma exp_seven_halves_bounds : (33 : ℝ) ≤ Real.exp (7 / 2) ∧ Real.exp (7 / 2) ≤ 42 := by
  have hsplit : Real.exp (7 / 2) = Real.exp 3 * Real.exp (1 / 2) := by
    rw [← Real.exp_add]
    norm_num
  have h3 := exp_three_bounds
  have hh := exp_half_bounds
  rw [hsplit]
  constructor
  · have hb : 20.08 * 1.6487 ≤ Real.exp 3 * Real.exp (1 / 2) :=
      mul_le_mul h3.1 hh.1 (by norm_num) (by linarith [h3.2])
    linarith [hb]
  · have h4 : Real.exp (1 / 2) ≤ 2 := by linarith [hh.2]
    have hb : Real.exp 3 * Real.exp (1 / 2) ≤ 21 * 2 :=
      mul_le_mul h3.2 h4 (Real.exp_pos _).le (by norm_num)
    linarith [hb]

/-- 辅助：`e^{-a} ≤ 1/c`（当 `c ≤ e^a`）。 -/
lemma exp_neg_le_inv_of_le (a c : ℝ) (hc : 0 < c) (h : c ≤ Real.exp a) :
    Real.exp (-a) ≤ 1 / c := by
  rw [Real.exp_neg]
  have h2 := (inv_le_inv₀ (Real.exp_pos a) hc).mpr h
  simpa using h2

/-- 辅助：`1/c ≤ e^{-a}`（当 `e^a ≤ c`）。 -/
lemma inv_le_exp_neg_of_le (a c : ℝ) (hc : 0 < c) (h : Real.exp a ≤ c) :
    1 / c ≤ Real.exp (-a) := by
  rw [Real.exp_neg]
  have h2 := (inv_le_inv₀ hc (Real.exp_pos a)).mpr h
  simpa using h2

/-- **更紧的数值界**：`e^{-u}(1-e^{-u})U2(u)²/(1+3e^{-u}+3e^{-2u}) ≤ 21.1`（`u ≥ 0`）。 -/
lemma exp_neg_mul_one_sub_mul_U2_sq_div_le (u : ℝ) (hu : 0 ≤ u) :
    Real.exp (-u) * (1 - Real.exp (-u)) * (U2 u) ^ 2
      / (1 + 3 * Real.exp (-u) + 3 * Real.exp (-u) ^ 2) ≤ 21.1 := by
  set z : ℝ := Real.exp (-u) with hz
  have hzpos : 0 < z := by rw [hz]; exact Real.exp_pos _
  have hz1 : z ≤ 1 := by rw [hz]; exact Real.exp_le_one_iff.mpr (by linarith)
  have hU2pos : ∀ v : ℝ, 0 ≤ U2 v := by intro v; simp only [U2]; positivity
  have hM7 : (0 : ℝ) ≤ (1 / 4) * (U2 (7 / 5)) ^ 2 := by norm_num [U2]
  have heq : z * (1 - z) * (U2 u) ^ 2 / (1 + 3 * z + 3 * z ^ 2)
      = z * (U2 u) ^ 2 * ((1 - z) / (1 + 3 * z + 3 * z ^ 2)) := by
    field_simp
  have hHnn : 0 ≤ (1 - z) / (1 + 3 * z + 3 * z ^ 2) :=
    div_nonneg (by linarith) (by positivity)
  have hg2 : ∀ a : ℝ, a ≤ u → 0 ≤ a → z * (U2 u) ^ 2 ≤ Real.exp (-a) * (U2 a) ^ 2 := by
    intro a hau ha
    have h := exp_neg_mul_U2_sq_antitoneOn (show a ∈ Set.Ici (0 : ℝ) from ha)
      (show u ∈ Set.Ici (0 : ℝ) from hu) hau
    rw [hz]
    exact h
  have hz_ge : ∀ a c : ℝ, 0 < c → u ≤ a → 1 / c ≤ Real.exp (-a) → 1 / c ≤ z := by
    intro a c hc hua h
    have h1 : Real.exp (-a) ≤ Real.exp (-u) := Real.exp_le_exp.mpr (by linarith)
    rw [hz]
    linarith
  have hU2mono : ∀ a : ℝ, u ≤ a → U2 u ≤ U2 a := by
    intro a ha
    simp only [U2]
    nlinarith [hu, ha]
  rcases le_or_gt u (7 / 5) with h | h
  · -- 分支 1：`u ≤ 7/5`
    have hzlo : (1 : ℝ) / 5 ≤ z :=
      hz_ge (7 / 5) 5 (by norm_num) (by linarith) le_exp_neg_seven_fifths
    have hN : z * (1 - z) * (U2 u) ^ 2 ≤ (1 / 4) * (U2 (7 / 5)) ^ 2 := by
      have h1 : z * (1 - z) ≤ 1 / 4 := by nlinarith [hzpos, hz1, sq_nonneg (z - 1 / 2)]
      have h2 : U2 u ≤ U2 (7 / 5) := hU2mono (7 / 5) (by linarith)
      have h3 : (U2 u) ^ 2 ≤ (U2 (7 / 5)) ^ 2 := pow_le_pow_left₀ (hU2pos u) h2 2
      exact mul_le_mul h1 h3 (sq_nonneg _) (by norm_num)
    have hNnn : 0 ≤ z * (1 - z) * (U2 u) ^ 2 :=
      mul_nonneg (mul_nonneg hzpos.le (by linarith)) (sq_nonneg _)
    have hD : (43 : ℝ) / 25 ≤ 1 + 3 * z + 3 * z ^ 2 := by nlinarith [hzlo, sq_nonneg z]
    have hA : z * (1 - z) * (U2 u) ^ 2 / (1 + 3 * z + 3 * z ^ 2)
        ≤ ((1 / 4) * (U2 (7 / 5)) ^ 2) / (43 / 25) := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [hN, hD, hNnn, hM7]
    have hfin : ((1 / 4) * (U2 (7 / 5)) ^ 2) / (43 / 25) ≤ 21.1 := by norm_num [U2]
    exact hA.trans hfin
  · rcases le_or_gt u 2 with h2 | h2
    · -- 分支 2：`7/5 ≤ u ≤ 2`
      have hzlo : (1 : ℝ) / 8 ≤ z :=
        hz_ge 2 8 (by norm_num) (by linarith)
          (inv_le_exp_neg_of_le 2 8 (by norm_num) (by linarith [exp_two_bounds.2]))
      have hg : z * (U2 u) ^ 2 ≤ (1 / 4) * (U2 (7 / 5)) ^ 2 := by
        have h1 := hg2 (7 / 5) (by linarith) (by norm_num)
        have h2 : Real.exp (-(7 / 5)) ≤ 1 / 4 := exp_neg_seven_fifths_le
        nlinarith [h1, h2, sq_nonneg (U2 (7 / 5))]
      have hH : (1 - z) / (1 + 3 * z + 3 * z ^ 2) ≤ 8 / 13 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [hzlo, hzpos, sq_nonneg (z - 1 / 8)]
      rw [heq]
      calc z * (U2 u) ^ 2 * ((1 - z) / (1 + 3 * z + 3 * z ^ 2))
          ≤ ((1 / 4) * (U2 (7 / 5)) ^ 2) * (8 / 13) := mul_le_mul hg hH hHnn hM7
        _ ≤ 21.1 := by norm_num [U2]
    · rcases le_or_gt u (5 / 2) with h3 | h3
      · -- 分支 3：`2 ≤ u ≤ 5/2`
        have hzlo : (1 : ℝ) / 13 ≤ z :=
          hz_ge (5 / 2) 13 (by norm_num) (by linarith)
            (inv_le_exp_neg_of_le (5 / 2) 13 (by norm_num) (by linarith [exp_five_halves_bounds.2]))
        have hg : z * (U2 u) ^ 2 ≤ (1 / 7) * (U2 2) ^ 2 := by
          have h1 := hg2 2 (by linarith) (by norm_num)
          have h2 : Real.exp (-2) ≤ 1 / 7 :=
            exp_neg_le_inv_of_le 2 7 (by norm_num) (by linarith [exp_two_bounds.1])
          nlinarith [h1, h2, sq_nonneg (U2 2)]
        have hH : (1 - z) / (1 + 3 * z + 3 * z ^ 2) ≤ 156 / 211 := by
          rw [div_le_iff₀ (by positivity)]
          nlinarith [hzlo, hzpos, sq_nonneg (z - 1 / 13)]
        rw [heq]
        calc z * (U2 u) ^ 2 * ((1 - z) / (1 + 3 * z + 3 * z ^ 2))
            ≤ ((1 / 7) * (U2 2) ^ 2) * (156 / 211) :=
              mul_le_mul hg hH hHnn (by norm_num [U2])
          _ ≤ 21.1 := by norm_num [U2]
      · rcases le_or_gt u 3 with h4 | h4
        · -- 分支 4：`5/2 ≤ u ≤ 3`
          have hzlo : (1 : ℝ) / 21 ≤ z :=
            hz_ge 3 21 (by norm_num) (by linarith)
              (inv_le_exp_neg_of_le 3 21 (by norm_num) (by linarith [exp_three_bounds.2]))
          have hg : z * (U2 u) ^ 2 ≤ (1 / 12) * (U2 (5 / 2)) ^ 2 := by
            have h1 := hg2 (5 / 2) (by linarith) (by norm_num)
            have h2 : Real.exp (-(5 / 2)) ≤ 1 / 12 :=
              exp_neg_le_inv_of_le (5 / 2) 12 (by norm_num) (by linarith [exp_five_halves_bounds.1])
            nlinarith [h1, h2, sq_nonneg (U2 (5 / 2))]
          have hH : (1 - z) / (1 + 3 * z + 3 * z ^ 2) ≤ 140 / 169 := by
            rw [div_le_iff₀ (by positivity)]
            nlinarith [hzlo, hzpos, sq_nonneg (z - 1 / 21)]
          rw [heq]
          calc z * (U2 u) ^ 2 * ((1 - z) / (1 + 3 * z + 3 * z ^ 2))
              ≤ ((1 / 12) * (U2 (5 / 2)) ^ 2) * (140 / 169) :=
                mul_le_mul hg hH hHnn (by norm_num [U2])
            _ ≤ 21.1 := by norm_num [U2]
        · rcases le_or_gt u (7 / 2) with h5 | h5
          · -- 分支 5：`3 ≤ u ≤ 7/2`
            have hzlo : (1 : ℝ) / 42 ≤ z :=
              hz_ge (7 / 2) 42 (by norm_num) (by linarith)
                (inv_le_exp_neg_of_le (7 / 2) 42 (by norm_num) (by linarith [exp_seven_halves_bounds.2]))
            have hg : z * (U2 u) ^ 2 ≤ (1 / 20) * (U2 3) ^ 2 := by
              have h1 := hg2 3 (by linarith) (by norm_num)
              have h2 : Real.exp (-3) ≤ 1 / 20 :=
                exp_neg_le_inv_of_le 3 20 (by norm_num) (by linarith [exp_three_bounds.1])
              nlinarith [h1, h2, sq_nonneg (U2 3)]
            have hH : (1 - z) / (1 + 3 * z + 3 * z ^ 2) ≤ 574 / 631 := by
              rw [div_le_iff₀ (by positivity)]
              nlinarith [hzlo, hzpos, sq_nonneg (z - 1 / 42)]
            rw [heq]
            calc z * (U2 u) ^ 2 * ((1 - z) / (1 + 3 * z + 3 * z ^ 2))
                ≤ ((1 / 20) * (U2 3) ^ 2) * (574 / 631) :=
                  mul_le_mul hg hH hHnn (by norm_num [U2])
              _ ≤ 21.1 := by norm_num [U2]
          · -- 分支 6：`7/2 ≤ u`
            have hH : (1 - z) / (1 + 3 * z + 3 * z ^ 2) ≤ 1 := by
              rw [div_le_one (by positivity)]
              nlinarith [hzpos]
            have hg : z * (U2 u) ^ 2 ≤ (1 / 33) * (U2 (7 / 2)) ^ 2 := by
              have h1 := hg2 (7 / 2) (by linarith) (by norm_num)
              have h2 : Real.exp (-(7 / 2)) ≤ 1 / 33 :=
                exp_neg_le_inv_of_le (7 / 2) 33 (by norm_num) (by linarith [exp_seven_halves_bounds.1])
              nlinarith [h1, h2, sq_nonneg (U2 (7 / 2))]
            rw [heq]
            calc z * (U2 u) ^ 2 * ((1 - z) / (1 + 3 * z + 3 * z ^ 2))
                ≤ ((1 / 33) * (U2 (7 / 2)) ^ 2) * 1 :=
                  mul_le_mul hg hH hHnn (by norm_num [U2])
              _ ≤ 21.1 := by norm_num [U2]

/-- 更紧的 `B` 界：`e^{-u}·2u·W2(u) ≤ 20`（`u ≥ 0`）。 -/
lemma exp_neg_mul_W2_le_twenty (u : ℝ) (hu : 0 ≤ u) :
    Real.exp (-u) * (2 * u * W2 u) ≤ 20 := by
  have he1 : Real.exp (-1) ≤ 1 / 2 := by
    rw [Real.exp_neg]
    have h := (inv_le_inv₀ (Real.exp_pos 1) (by norm_num : (0 : ℝ) < 2)).mpr Real.exp_one_gt_two.le
    simpa using h
  have he2 : Real.exp (-2) ≤ 1 / 7 :=
    exp_neg_le_inv_of_le 2 7 (by norm_num) (by linarith [exp_two_bounds.1])
  have he3 : Real.exp (-3) ≤ 1 / 20 :=
    exp_neg_le_inv_of_le 3 20 (by norm_num) (by linarith [exp_three_bounds.1])
  have hu1 : u * Real.exp (-u) ≤ Real.exp (-1) := by
    have h := pow_mul_exp_neg_le 1 hu
    simpa using h
  have hu2 : u ^ 2 * Real.exp (-u) ≤ 4 * Real.exp (-2) := by
    have h := pow_mul_exp_neg_le 2 hu
    norm_num at h
    exact h
  have hu3 : u ^ 3 * Real.exp (-u) ≤ 27 * Real.exp (-3) := by
    have h := pow_mul_exp_neg_le 3 hu
    norm_num at h
    exact h
  simp only [W2]
  nlinarith [hu1, hu2, hu3, he1, he2, he3, Real.exp_pos (-u), hu,
    mul_nonneg hu (Real.exp_pos (-u)).le]

/-- `σ(1-σ)|1-2σ| = z(1-z)/(1+z)³`（`z = e^{-|v x|}`）。 -/
lemma smoothTransition_mul_one_sub_mul_abs_eq {x : ℝ} (hx : x ∈ Set.Ioo 0 1) :
    Real.smoothTransition x * (1 - Real.smoothTransition x) * |1 - 2 * Real.smoothTransition x|
      = Real.exp (-|sigmaV x|) * (1 - Real.exp (-|sigmaV x|))
        / (1 + Real.exp (-|sigmaV x|)) ^ 3 := by
  have h1 : (0 : ℝ) < 1 + Real.exp (-(sigmaV x)) := by positivity
  have h3 : 1 / (1 + Real.exp (-(sigmaV x))) * (1 - 1 / (1 + Real.exp (-(sigmaV x))))
      = Real.exp (-(sigmaV x)) / (1 + Real.exp (-(sigmaV x))) ^ 2 := by
    field_simp
    ring
  have h2 : |1 - 2 * (1 / (1 + Real.exp (-(sigmaV x))))|
      = |Real.exp (-(sigmaV x)) - 1| / (1 + Real.exp (-(sigmaV x))) := by
    rw [show 1 - 2 * (1 / (1 + Real.exp (-(sigmaV x))))
        = (Real.exp (-(sigmaV x)) - 1) / (1 + Real.exp (-(sigmaV x))) by
      field_simp
      ring]
    rw [abs_div, abs_of_pos h1]
  have hid : Real.smoothTransition x * (1 - Real.smoothTransition x)
      * |1 - 2 * Real.smoothTransition x|
      = Real.exp (-(sigmaV x)) * |Real.exp (-(sigmaV x)) - 1|
        / (1 + Real.exp (-(sigmaV x))) ^ 3 := by
    rw [smoothTransition_eq_inv_exp_neg_sigmaV hx, h3, h2]
    field_simp
  rw [hid]
  rcases le_or_gt 0 (sigmaV x) with hv | hv
  · have hE1 : Real.exp (-(sigmaV x)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hz : Real.exp (-|sigmaV x|) = Real.exp (-(sigmaV x)) := by rw [abs_of_nonneg hv]
    rw [hz, abs_of_nonpos (by linarith : Real.exp (-(sigmaV x)) - 1 ≤ 0)]
    ring
  · have hE1 : 1 ≤ Real.exp (-(sigmaV x)) := by
      rw [← Real.exp_zero, Real.exp_le_exp]
      linarith
    have hz : Real.exp (-|sigmaV x|) = (Real.exp (-(sigmaV x)))⁻¹ := by
      rw [abs_of_neg hv, neg_neg, Real.exp_neg, inv_inv]
    rw [hz, abs_of_nonneg (by linarith : (0 : ℝ) ≤ Real.exp (-(sigmaV x)) - 1)]
    field_simp
    ring

/-- 二阶导数分解中 `A = σ(1-σ)|1-2σ|(v')²` 的一致界。 -/
lemma smoothTransition_A_le (x : ℝ) (hx : x ∈ Set.Ioo 0 1) :
    Real.smoothTransition x * (1 - Real.smoothTransition x) * |1 - 2 * Real.smoothTransition x|
      * (sigmaV1 x) ^ 2 ≤ K₀ := by
  set z : ℝ := Real.exp (-|sigmaV x|) with hz
  have hzpos : 0 < z := by rw [hz]; exact Real.exp_pos _
  have hz1 : z ≤ 1 := by
    rw [hz]; exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (abs_nonneg _))
  have h1 := smoothTransition_mul_one_sub_mul_abs_eq hx
  have h2 := sigmaV1_le_U2 hx
  have h3 : (sigmaV1 x) ^ 2 ≤ (U2 |sigmaV x|) ^ 2 :=
    pow_le_pow_left₀ (sigmaV1_pos hx).le h2 2
  have hnum : 0 ≤ z * (1 - z) := mul_nonneg hzpos.le (by linarith)
  have hden : 0 < 1 + 3 * z + 3 * z ^ 2 := by positivity
  have hcube : 1 + 3 * z + 3 * z ^ 2 ≤ (1 + z) ^ 3 := one_add_cube_ge z hzpos.le
  have hnum' : 0 ≤ z * (1 - z) / (1 + z) ^ 3 :=
    div_nonneg hnum (by positivity)
  calc Real.smoothTransition x * (1 - Real.smoothTransition x)
        * |1 - 2 * Real.smoothTransition x| * (sigmaV1 x) ^ 2
      = (z * (1 - z) / (1 + z) ^ 3) * (sigmaV1 x) ^ 2 := by rw [h1, ← hz]
    _ ≤ (z * (1 - z) / (1 + z) ^ 3) * (U2 |sigmaV x|) ^ 2 :=
        mul_le_mul_of_nonneg_left h3 hnum'
    _ ≤ (z * (1 - z) / (1 + 3 * z + 3 * z ^ 2)) * (U2 |sigmaV x|) ^ 2 :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left hnum hden hcube) (sq_nonneg _)
    _ ≤ K₀ := by
        have h := exp_neg_mul_one_sub_mul_U2_sq_div_le |sigmaV x| (abs_nonneg _)
        rw [← hz] at h
        rw [K₀_eq]
        calc z * (1 - z) / (1 + 3 * z + 3 * z ^ 2) * (U2 |sigmaV x|) ^ 2
            = z * (1 - z) * (U2 |sigmaV x|) ^ 2 / (1 + 3 * z + 3 * z ^ 2) := by ring
          _ ≤ 21.1 := h

/-- 一阶导数的一致界：`∀ x, |σ'(x)| ≤ K₀`。 -/
lemma abs_deriv_smoothTransition_le (x : ℝ) : |deriv Real.smoothTransition x| ≤ K₀ := by
  rcases lt_or_ge x 0 with h | h
  · rw [deriv_smoothTransition_eq_zero_of_neg h, abs_zero]; norm_num [K₀]
  · rcases le_or_gt 1 x with h1 | h1
    · rw [deriv_smoothTransition_eq_zero_of_one_le h1, abs_zero]; norm_num [K₀]
    · rcases eq_or_lt_of_le h with rfl | hx0
      · rw [deriv_smoothTransition_eq_zero_of_nonpos le_rfl, abs_zero]; norm_num [K₀]
      · have hx : x ∈ Set.Ioo 0 1 := ⟨hx0, h1⟩
        rw [deriv_smoothTransition_eq hx]
        have hσ1 := smoothTransition_mul_one_sub_le_exp_neg_abs hx
        have hσ2 := smoothTransition_mul_one_sub_le_quarter hx
        have hv := sigmaV1_le_U2 hx
        have hσnn : 0 ≤ Real.smoothTransition x * (1 - Real.smoothTransition x) :=
          mul_nonneg (Real.smoothTransition.nonneg x)
            (by linarith [Real.smoothTransition.le_one x])
        have hvnn : 0 ≤ sigmaV1 x := (sigmaV1_pos hx).le
        rw [abs_of_nonneg (mul_nonneg hσnn hvnn)]
        calc Real.smoothTransition x * (1 - Real.smoothTransition x) * sigmaV1 x
            ≤ min (1 / 4) (Real.exp (-|sigmaV x|)) * U2 |sigmaV x| :=
              mul_le_mul (le_min hσ2 hσ1) hv hvnn
                (le_min (by norm_num) (Real.exp_pos _).le)
          _ ≤ K₀ := (min_exp_neg_mul_U2_le _ (abs_nonneg _)).trans (by norm_num [K₀])

/-- 二阶导数的一致界：`∀ x, |σ''(x)| ≤ K₀`。 -/
lemma abs_deriv2_smoothTransition_le (x : ℝ) :
    |deriv (deriv Real.smoothTransition) x| ≤ K₀ := by
  rcases lt_or_ge x 0 with h | h
  · rw [deriv2_smoothTransition_eq_zero_of_lt_zero h, abs_zero]; norm_num [K₀]
  · rcases le_or_gt 1 x with h1 | h1
    · rw [deriv2_smoothTransition_eq_zero_of_notMem (by
        rw [Set.mem_Ioo]; rintro ⟨-, h2⟩; linarith), abs_zero]
      norm_num [K₀]
    · rcases eq_or_lt_of_le h with rfl | hx0
      · rw [deriv2_smoothTransition_eq_zero_of_notMem (by simp), abs_zero]; norm_num [K₀]
      · have hx : x ∈ Set.Ioo 0 1 := ⟨hx0, h1⟩
        rw [deriv2_smoothTransition_eq hx]
        have hσnn : 0 ≤ Real.smoothTransition x * (1 - Real.smoothTransition x) :=
          mul_nonneg (Real.smoothTransition.nonneg x)
            (by linarith [Real.smoothTransition.le_one x])
        have hQ : 0 ≤ (x⁻¹) ^ 2 + x⁻¹ * (1 - x)⁻¹ + ((1 - x)⁻¹) ^ 2 := by
          have h1' : 0 < x⁻¹ := inv_pos.mpr hx.1
          have h2' : 0 < (1 - x)⁻¹ := inv_pos.mpr (by linarith [hx.2])
          positivity
        have hsign : ((1 - 2 * Real.smoothTransition x) * (sigmaV1 x) ^ 2) * sigmaV2 x ≤ 0 := by
          have h0 := one_sub_two_mul_smoothTransition_mul_sigmaV_nonpos hx
          have hprod : 0 ≤ (sigmaV1 x) ^ 2
              * (2 * ((x⁻¹) ^ 2 + x⁻¹ * (1 - x)⁻¹ + ((1 - x)⁻¹) ^ 2)) :=
            mul_nonneg (sq_nonneg _) (by linarith)
          rw [sigmaV2_eq]
          nlinarith [h0, hprod]
        have hmax := abs_add_le_max_of_mul_nonpos hsign
        rw [abs_mul, abs_of_nonneg hσnn]
        have hmax' : Real.smoothTransition x * (1 - Real.smoothTransition x)
              * |(1 - 2 * Real.smoothTransition x) * (sigmaV1 x) ^ 2 + sigmaV2 x|
            ≤ max (Real.smoothTransition x * (1 - Real.smoothTransition x)
                * |(1 - 2 * Real.smoothTransition x) * (sigmaV1 x) ^ 2|)
              (Real.smoothTransition x * (1 - Real.smoothTransition x) * |sigmaV2 x|) := by
          rw [← mul_max_of_nonneg _ _ hσnn]
          exact mul_le_mul_of_nonneg_left hmax hσnn
        refine hmax'.trans (max_le ?_ ?_)
        · rw [abs_mul, abs_of_nonneg (sq_nonneg (sigmaV1 x))]
          calc Real.smoothTransition x * (1 - Real.smoothTransition x)
                * (|1 - 2 * Real.smoothTransition x| * (sigmaV1 x) ^ 2)
              = Real.smoothTransition x * (1 - Real.smoothTransition x)
                * |1 - 2 * Real.smoothTransition x| * (sigmaV1 x) ^ 2 := by ring
            _ ≤ K₀ := smoothTransition_A_le x hx
        · have hB := abs_sigmaV2_le hx
          have hσ1 := smoothTransition_mul_one_sub_le_exp_neg_abs hx
          have hσ2 := smoothTransition_mul_one_sub_le_quarter hx
          have h2u : 0 ≤ 2 * |sigmaV x| * W2 |sigmaV x| := by
            have := abs_nonneg (sigmaV x)
            simp only [W2]
            positivity
          calc Real.smoothTransition x * (1 - Real.smoothTransition x) * |sigmaV2 x|
              ≤ min (1 / 4) (Real.exp (-|sigmaV x|)) * (2 * |sigmaV x| * W2 |sigmaV x|) :=
                mul_le_mul (le_min hσ2 hσ1) hB (abs_nonneg _)
                  (le_min (by norm_num) (Real.exp_pos _).le)
            _ ≤ Real.exp (-|sigmaV x|) * (2 * |sigmaV x| * W2 |sigmaV x|) :=
                mul_le_mul_of_nonneg_right (min_le_right _ _) h2u
            _ ≤ K₀ := (exp_neg_mul_W2_le_twenty _ (abs_nonneg _)).trans (by norm_num [K₀])

/-! ## 9. 截断函数导数的显式标度界（链式法则缩放） -/

private lemma differentiable_smoothTransition : Differentiable ℝ Real.smoothTransition :=
  (Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num)

private lemma differentiable_deriv_smoothTransition :
    Differentiable ℝ (deriv Real.smoothTransition) :=
  ContDiff.differentiable_deriv_two (Real.smoothTransition.contDiff (n := 2))

private lemma deriv_comp_sub_div {F : ℝ → ℝ} (dF : Differentiable ℝ F) (c B x : ℝ) :
    deriv (fun y : ℝ => F ((c - y) / B)) x = deriv F ((c - x) / B) * (-(1 / B)) := by
  have h1 : deriv (fun y : ℝ => (c - y) / B) x = -(1 / B) := by
    rw [deriv_div_const B, deriv_const_sub c, deriv_id'']
    ring
  have h4 : DifferentiableAt ℝ (fun y : ℝ => (c - y) / B) x := by fun_prop
  have h5 : deriv (fun y : ℝ => F ((c - y) / B)) x
      = deriv F ((c - x) / B) * deriv (fun y : ℝ => (c - y) / B) x := by
    simpa only [Function.comp_def] using deriv_comp x (dF.differentiableAt) h4
  rw [h5, h1]

private lemma deriv_comp_add_div {F : ℝ → ℝ} (dF : Differentiable ℝ F) (c B x : ℝ) :
    deriv (fun y : ℝ => F ((c + y) / B)) x = deriv F ((c + x) / B) * (1 / B) := by
  have h1 : deriv (fun y : ℝ => (c + y) / B) x = (1 / B) := by
    rw [deriv_div_const B, deriv_const_add c, deriv_id'']
  have h4 : DifferentiableAt ℝ (fun y : ℝ => (c + y) / B) x := by fun_prop
  have h5 : deriv (fun y : ℝ => F ((c + y) / B)) x
      = deriv F ((c + x) / B) * deriv (fun y : ℝ => (c + y) / B) x := by
    simpa only [Function.comp_def] using deriv_comp x (dF.differentiableAt) h4
  rw [h5, h1]

private lemma deriv_cutoff_of_pos {τ B μ : ℝ} (hμ : 0 < μ) :
    deriv (cutoff τ B) μ
      = deriv Real.smoothTransition ((τ + B - μ) / B) * (-(1 / B)) := by
  have hev : cutoff τ B =ᶠ[nhds μ] fun y : ℝ => Real.smoothTransition ((τ + B - y) / B) := by
    filter_upwards [isOpen_Ioi.mem_nhds hμ] with y hy
    simp only [cutoff]
    rw [abs_of_pos hy]
  rw [hev.deriv_eq]
  exact deriv_comp_sub_div differentiable_smoothTransition (τ + B) B μ

private lemma deriv_cutoff_of_neg {τ B μ : ℝ} (hμ : μ < 0) :
    deriv (cutoff τ B) μ
      = deriv Real.smoothTransition ((τ + B + μ) / B) * (1 / B) := by
  have hev : cutoff τ B =ᶠ[nhds μ] fun y : ℝ => Real.smoothTransition ((τ + B + y) / B) := by
    filter_upwards [isOpen_Iio.mem_nhds hμ] with y hy
    simp only [cutoff]
    rw [abs_of_neg hy]
    ring_nf
  rw [hev.deriv_eq]
  exact deriv_comp_add_div differentiable_smoothTransition (τ + B) B μ

private lemma deriv2_cutoff_of_pos {τ B μ : ℝ} (hμ : 0 < μ) :
    deriv (deriv (cutoff τ B)) μ
      = deriv (deriv Real.smoothTransition) ((τ + B - μ) / B) * ((1 / B) * (1 / B)) := by
  have hpt : deriv (cutoff τ B) =ᶠ[nhds μ]
      fun x : ℝ => deriv Real.smoothTransition ((τ + B - x) / B) * (-(1 / B)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hμ] with x hx
    exact deriv_cutoff_of_pos hx
  rw [hpt.deriv_eq]
  have hdiff : DifferentiableAt ℝ (fun x : ℝ => deriv Real.smoothTransition ((τ + B - x) / B))
      μ := differentiable_deriv_smoothTransition.differentiableAt.comp μ (by fun_prop)
  rw [deriv_mul_const hdiff (-(1 / B)),
    deriv_comp_sub_div differentiable_deriv_smoothTransition (τ + B) B μ]
  ring

private lemma deriv2_cutoff_of_neg {τ B μ : ℝ} (hμ : μ < 0) :
    deriv (deriv (cutoff τ B)) μ
      = deriv (deriv Real.smoothTransition) ((τ + B + μ) / B) * ((1 / B) * (1 / B)) := by
  have hpt : deriv (cutoff τ B) =ᶠ[nhds μ]
      fun x : ℝ => deriv Real.smoothTransition ((τ + B + x) / B) * (1 / B) := by
    filter_upwards [isOpen_Iio.mem_nhds hμ] with x hx
    exact deriv_cutoff_of_neg hx
  rw [hpt.deriv_eq]
  have hdiff : DifferentiableAt ℝ (fun x : ℝ => deriv Real.smoothTransition ((τ + B + x) / B))
      μ := differentiable_deriv_smoothTransition.differentiableAt.comp μ (by fun_prop)
  rw [deriv_mul_const hdiff (1 / B),
    deriv_comp_add_div differentiable_deriv_smoothTransition (τ + B) B μ]
  ring

/-- **显式常数版本**：`τ, B > 0` 时截断函数的一阶、二阶导数分别被 `K₀ / B`、`K₀ / B ^ 2` 控制。 -/
lemma deriv_cutoff_le_explicit {τ B : ℝ} (hτ : 0 < τ) (hB : 0 < B) :
    (∀ μ : ℝ, |deriv (cutoff τ B) μ| ≤ (K₀ : ℝ) / B) ∧
      (∀ μ : ℝ, |deriv (deriv (cutoff τ B)) μ| ≤ (K₀ : ℝ) / B ^ 2) := by
  have hK : (0 : ℝ) < K₀ := K₀_pos
  refine ⟨fun μ => ?_, fun μ => ?_⟩
  · rcases eq_or_ne μ 0 with rfl | hne
    · have hev : cutoff τ B =ᶠ[nhds (0 : ℝ)] fun _ : ℝ => (1 : ℝ) := by
        filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hτ] with x hx
        refine cutoff_eq_one hB ?_
        rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hx
        exact le_of_lt (by simpa using hx)
      rw [hev.deriv_eq, deriv_const (0 : ℝ) 1, abs_zero]
      exact div_nonneg hK.le hB.le
    · rcases lt_or_gt_of_ne hne with hneg | hpos
      · rw [deriv_cutoff_of_neg hneg, abs_mul, abs_of_pos (one_div_pos.mpr hB)]
        calc |deriv Real.smoothTransition ((τ + B + μ) / B)| * (1 / B)
            ≤ K₀ * (1 / B) :=
              mul_le_mul_of_nonneg_right (abs_deriv_smoothTransition_le _) (by positivity)
          _ = K₀ / B := by ring
      · rw [deriv_cutoff_of_pos hpos, abs_mul, abs_neg, abs_of_pos (one_div_pos.mpr hB)]
        calc |deriv Real.smoothTransition ((τ + B - μ) / B)| * (1 / B)
            ≤ K₀ * (1 / B) :=
              mul_le_mul_of_nonneg_right (abs_deriv_smoothTransition_le _) (by positivity)
          _ = K₀ / B := by ring
  · rcases eq_or_ne μ 0 with rfl | hne
    · have hball : ∀ x ∈ Metric.ball (0 : ℝ) τ, cutoff τ B x = 1 := fun x hx => by
        refine cutoff_eq_one hB ?_
        rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hx
        exact le_of_lt (by simpa using hx)
      have hz : deriv (cutoff τ B) =ᶠ[nhds (0 : ℝ)] fun _ : ℝ => (0 : ℝ) := by
        filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hτ] with x hx
        have hx' : cutoff τ B =ᶠ[nhds x] fun _ : ℝ => (1 : ℝ) := by
          filter_upwards [Metric.isOpen_ball.mem_nhds hx] with y hy
          exact hball y hy
        rw [hx'.deriv_eq, deriv_const x 1]
      rw [hz.deriv_eq, deriv_const (0 : ℝ) 0, abs_zero]
      exact div_nonneg hK.le (by positivity)
    · rcases lt_or_gt_of_ne hne with hneg | hpos
      · rw [deriv2_cutoff_of_neg hneg, abs_mul,
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 / B) * (1 / B))]
        calc |deriv (deriv Real.smoothTransition) ((τ + B + μ) / B)| * ((1 / B) * (1 / B))
            ≤ K₀ * ((1 / B) * (1 / B)) :=
              mul_le_mul_of_nonneg_right (abs_deriv2_smoothTransition_le _) (by positivity)
          _ = K₀ / B ^ 2 := by rw [one_div_mul_one_div, pow_two]; ring
      · rw [deriv2_cutoff_of_pos hpos, abs_mul,
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 / B) * (1 / B))]
        calc |deriv (deriv Real.smoothTransition) ((τ + B - μ) / B)| * ((1 / B) * (1 / B))
            ≤ K₀ * ((1 / B) * (1 / B)) :=
              mul_le_mul_of_nonneg_right (abs_deriv2_smoothTransition_le _) (by positivity)
          _ = K₀ / B ^ 2 := by rw [one_div_mul_one_div, pow_two]; ring

/-- **主定理（显式常数）**：`K₀ = 21.1` 对一切 `τ, B > 0` 一致成立。 -/
lemma exists_deriv_cutoff_bound_explicit :
    ∀ (τ B : ℝ), 0 < τ → 0 < B →
      (∀ μ : ℝ, |deriv (cutoff τ B) μ| ≤ (K₀ : ℝ) / B) ∧
      (∀ μ : ℝ, |deriv (deriv (cutoff τ B)) μ| ≤ (K₀ : ℝ) / B ^ 2) :=
  fun _ _ hτ hB => deriv_cutoff_le_explicit hτ hB

end RobustZ
