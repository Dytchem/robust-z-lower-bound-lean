import RobustZ.FinalSmall
import RobustZ.FinalConv
import RobustZ.SmearingMain
import RobustZ.CutoffDeriv
import RobustZ.CollarBound

/-!
# M5′（`M5Scaled`）：**τ-一致**（论文尺度 `B = ετ/q²`）的核衰减

## 背景：为什么需要这个文件

`M5Apply.h_zero_le_of_admissible_twoN_add_one` 用的是 M3 的**旧**形式
`norm_sum_le_of_moments`（`B = √ε` 写死）。这个 `B` 与 `τ` 无关，于是 `τ → 0` 时
collar 的**相对**宽度 `√ε/τ → ∞`，`CollarBound` 那套 Chebyshev 界在 collar 上指数增长，
`C₁C₂` 的上界发散（见 `FinalSmall.lean` §6 的定量诊断）。

论文用的是与 `τ` 成正比的宽度 `B = ετ/q²`（`q = 2N+2`）。此时 `B/τ = ε/q²`
**与 τ 无关**，`SmearingMain.norm_sum_le_of_moments_tau_scaled` 已经把这个尺度接进 M3。

## 本文件的内容

1. `h_zero_le_of_admissible_tau_scaled`：把 M3′ + M4 应用到 `h(0)`，得到
   `h(0) ≤ 8√(kernelA τ B P · kernelC τ B P)`，`B = epsOf τ δ' (2N+1)·τ/q²`。
2. `abs_deriv2_chebyshevT_le_exp`：**collar 上 Chebyshev 二阶导的增长界**
   `|T_n''(u)| ≤ 32|n|⁴e^{|n|·2√δ}`（`|u| ≤ 1+δ`、`δ ≤ 1/2`）。
   这是 `CollarBound` 缺失的第三块（它只有 `T` 与 `T'` 的 collar 界）；证明用
   Mathlib 已有的 Chebyshev 微分方程 `(1-X²)T_n'' = X T_n' - n²T_n` 加上
   「`W = uT_n' - n²T_n` 在 `u = ±1` 处为零」的中值定理论证。
3. 由 (2) 与 `FinalSmall.norm_fcoef_le_min`（`√` 技巧）得到**不带 `E` 因子**的
   collar 界 `approxPoly_collar_le`、`approxPoly_deriv_collar_le`、
   `approxPoly_deriv2_collar_le`。
4. 由 (3) 得到 `Ψ_A` 在 collar 上的一阶、二阶导数界 `M₁`、`M₂`（`§4`）。
5. 由 (4) + 支撑感知的 `L¹` 界得到**锐化的** `C₁`、`C₂` 界与最终的
   `∀ᶠ N` 衰减结论（`§5`、`§6`）。
-/

noncomputable section

namespace RobustZ

open Filter MeasureTheory
open scoped Real Topology

/-! ## §1 第 1 步：把 M3′（τ-一致尺度）应用到 `h(0)`

与 `M5Apply.h_zero_le_of_admissible_pos` 逐行相同，只是把 M3 的调用换成
`norm_sum_le_of_moments_tau_scaled`（`q := 2N+2`、`k := 2N+1`、`B = ετ/q²`）。 -/

/-- **M3′ + M4 应用到 `h(0)`（论文尺度 `B = ε·τ/q²`，`τ = (Σθ)/2 > 0`）**。

`ε := epsOf τ δ' (2N+1)`、`q := 2(N:ℝ)+2`；右端两个积分区间为
`±(τ + ετ/q² + 1)`，核常数为 `kernelA τ (ετ/q²) P`、`kernelC τ (ετ/q²) P`。 -/
lemma h_zero_le_of_admissible_tau_scaled {N : ℕ} {φ : ℝ} {L : ℕ} {α θ : Fin L → ℝ}
    (hAdm : Admissible N φ L α θ) {δ' : ℝ} (hδ' : 0 < δ')
    (hτ : 0 < (∑ j, θ j) / 2) :
    h L α θ 0 ≤ 8 * Real.sqrt
      (kernelA ((∑ j, θ j) / 2)
          (epsOf ((∑ j, θ j) / 2) δ' (2 * N + 1) * ((∑ j, θ j) / 2)
            / (2 * (N : ℝ) + 2) ^ 2)
          (scaledApprox ((∑ j, θ j) / 2) (2 * N + 1))
       * kernelC ((∑ j, θ j) / 2)
          (epsOf ((∑ j, θ j) / 2) δ' (2 * N + 1) * ((∑ j, θ j) / 2)
            / (2 * (N : ℝ) + 2) ^ 2)
          (scaledApprox ((∑ j, θ j) / 2) (2 * N + 1))) := by
  obtain ⟨ι, hι, c, ν, hν, hf, hmom, h0⟩ := exists_expSum_data N φ L α θ hAdm
  letI : Fintype ι := hι
  have hεpos : 0 < epsOf ((∑ j, θ j) / 2) δ' (2 * N + 1) := epsOf_pos hδ' _ (2 * N + 1)
  have hq : 0 < 2 * (N : ℝ) + 2 := by positivity
  -- 次数条件：`natDegree (scaledApprox τ (2N+1)) < 2N+2`
  have hPdeg : (scaledApprox ((∑ j, θ j) / 2) (2 * N + 1)).natDegree < 2 * N + 2 :=
    scaledApprox_natDegree_lt _ (2 * N + 1)
  -- 矩条件
  have hmom' : ∑ i, Complex.exp ((ν i : ℂ) * Complex.I)
      * (scaledApprox ((∑ j, θ j) / 2) (2 * N + 1)).eval ((ν i : ℂ)) * c i = 0 :=
    hmom (scaledApprox ((∑ j, θ j) / 2) (2 * N + 1)) hPdeg
  -- 带内逼近（M4）
  have hPε : ∀ μ : ℝ, |μ| ≤ (∑ j, θ j) / 2 →
      ‖Complex.exp (-(μ : ℂ) * Complex.I)
          - (scaledApprox ((∑ j, θ j) / 2) (2 * N + 1)).eval ((μ : ℂ))‖
        ≤ epsOf ((∑ j, θ j) / 2) δ' (2 * N + 1) :=
    fun μ hμ => scaledApprox_band_epsOf _ hτ hδ' (by omega) hμ
  -- 指数和的一致界（由 `‖h‖ ≤ 2` 反推）
  have hbdd : ∀ lam : ℝ,
      ‖∑ i, Complex.exp ((((ν i * lam : ℝ)) : ℂ) * Complex.I) * c i‖ ≤ 2 := by
    intro lam
    rw [← (hf lam).2]
    exact (hf lam).1
  -- M3′（`B = ετ/q²` 已由 `integrable_kernel` 消解）
  have hmain := norm_sum_le_of_moments_tau_scaled c ν hτ hεpos hq hν
    (scaledApprox ((∑ j, θ j) / 2) (2 * N + 1)) hPε hmom' hbdd
  -- 左端换算 `‖Σᵢcᵢ‖ = h(0)`
  have hnorm : ‖∑ i, c i‖ = h L α θ 0 := by
    rw [← h0, Complex.norm_def, Complex.normSq_ofReal,
      Real.sqrt_mul_self (h_bounds L α θ 0).1]
  simp only [kernelA, kernelC] at hmain ⊢
  rw [hnorm] at hmain
  exact hmain

/-! ## §2 collar 上 Chebyshev 二阶导的增长界

`CollarBound` 提供了 `|T_n(u)| ≤ e^{|n|2√δ}` 与 `|T_n'(u)| ≤ n²e^{|n|2√δ}`
（`|u| ≤ 1+δ`），但**没有**二阶导版本，而 `∫‖Ψ''‖` 需要它。

本节的证明思路（用 Mathlib 的 `one_sub_X_sq_mul_derivative_derivative_T_eq_poly_in_T`，
即 Chebyshev 微分方程 `(1-X²)T_n'' = X T_n' - n²T_n`）：

* 记 `W(u) := u T_n'(u) - n²T_n(u)`。微分方程给出 `W(u) = (1-u²)T_n''(u)`，
  特别地 `W(1) = W(-1) = 0`（**不需要**知道 `T_n(1) = 1`、`T_n'(1) = n²`）；
* `W'(v) = -(n²-1)T_n'(v) + v T_n''(v)`，于是 `|W'(v)| ≤ (n²+1)·sup|T_n'| + (1+δ)·sup|T_n''|`；
* 在 `|T_n''|` 于 collar 上的最大值点 `u₀` 处用中值定理（`u₀ ≥ 1` 时从 `1` 出发、
  `u₀ ≤ -1` 时从 `-1` 出发）：`|W(u₀)| ≤ |u₀ ∓ 1|·sup|W'|`，而
  `|W(u₀)| = |1-u₀²|·M ≥ 2|u₀ ∓ 1|·M`，两式相消 `1/|u₀ ∓ 1|` 的奇性，得
  `M ≤ (n²+1)·sup|T_n'|/(1-δ)`。 -/


/-- **Chebyshev 微分方程（逐点形式）**：`(1-u²)·T_n''(u) = u·T_n'(u) - n²·T_n(u)`。 -/
lemma chebyshevT_ode_eval (n : ℤ) (u : ℝ) :
    (1 - u ^ 2) * (Polynomial.Chebyshev.T ℝ n).derivative.derivative.eval u
      = u * (Polynomial.Chebyshev.T ℝ n).derivative.eval u
        - ((n : ℝ) ^ 2) * (Polynomial.Chebyshev.T ℝ n).eval u := by
  have h := congrArg (fun p : Polynomial ℝ => Polynomial.eval u p)
    (Polynomial.Chebyshev.one_sub_X_sq_mul_derivative_derivative_T_eq_poly_in_T (R := ℝ) n)
  simp only [Function.iterate_succ, Function.comp_apply, Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_intCast] at h
  exact h

/-- `|n| = n.natAbs`（实数嵌入）。 -/
lemma abs_intCast_eq_natAbs' (n : ℤ) : |((n : ℤ) : ℝ)| = (n.natAbs : ℝ) := by
  obtain ⟨k, hk | hk⟩ := Int.eq_nat_or_neg n
  · rw [hk]; simp
  · rw [hk]; simp

/-- **collar 上 `T_n''` 的增长界**：`|u| ≤ 1+δ`、`0 ≤ δ ≤ 1/2` 时
`|T_n''(u)| ≤ 32·|n|⁴·e^{|n|·2√δ}`。 -/
lemma abs_deriv2_chebyshevT_le_exp (n : ℤ) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2)
    {u : ℝ} (hu : |u| ≤ 1 + δ) :
    |(Polynomial.Chebyshev.T ℝ n).derivative.derivative.eval u|
      ≤ 32 * |((n : ℤ) : ℝ)| ^ 4 * Real.exp (|((n : ℤ) : ℝ)| * 2 * Real.sqrt δ) := by
  rcases eq_or_ne n 0 with h0 | hn0
  · subst h0
    simp [Polynomial.Chebyshev.T_zero]
  have hnabs1 : (1 : ℝ) ≤ |((n : ℤ) : ℝ)| := by
    rw [abs_intCast_eq_natAbs']
    exact_mod_cast Int.natAbs_pos.mpr hn0
  set T : Polynomial ℝ := Polynomial.Chebyshev.T ℝ n with hT
  set E : ℝ := Real.exp (|((n : ℤ) : ℝ)| * 2 * Real.sqrt δ) with hE
  have hE1 : (1 : ℝ) ≤ E := by rw [hE]; exact Real.one_le_exp (by positivity)
  set W : ℝ → ℝ := fun v => v * T.derivative.eval v - ((n : ℝ) ^ 2) * T.eval v with hW
  -- `W` 的导数公式
  have hWderiv : ∀ v : ℝ, HasDerivAt W (-(((n : ℝ) ^ 2) - 1) * T.derivative.eval v
      + v * T.derivative.derivative.eval v) v := by
    intro v
    have h1 : HasDerivAt (fun y : ℝ => y * T.derivative.eval y)
        (T.derivative.eval v + v * T.derivative.derivative.eval v) v := by
      have hh := (hasDerivAt_id v).mul (Polynomial.hasDerivAt T.derivative v)
      have hfun : (id * fun x : ℝ => T.derivative.eval x)
          = fun y : ℝ => y * T.derivative.eval y := rfl
      rw [hfun] at hh
      simpa using hh
    have h2 : HasDerivAt (fun y : ℝ => ((n : ℝ) ^ 2) * T.eval y)
        (((n : ℝ) ^ 2) * T.derivative.eval v) v :=
      (Polynomial.hasDerivAt T v).const_mul _
    have h3 := h1.sub h2
    rw [hW]
    convert h3 using 1
    ring
  have hW1 : W 1 = 0 := by
    have h := chebyshevT_ode_eval n 1
    rw [hW]; nlinarith [h]
  have hWm1 : W (-1) = 0 := by
    have h := chebyshevT_ode_eval n (-1)
    rw [hW]; nlinarith [h]
  -- 最大值点
  obtain ⟨u₀, hu₀mem, hu₀max⟩ := isCompact_Icc.exists_isMaxOn
    (s := Set.Icc (-(1 + δ)) (1 + δ))
    (show (Set.Icc (-(1 + δ)) (1 + δ)).Nonempty from
      ⟨0, by simp only [Set.mem_Icc]; constructor <;> linarith⟩)
    ((Polynomial.continuous T.derivative.derivative).abs.continuousOn)
  rw [Set.mem_Icc] at hu₀mem
  set M : ℝ := |T.derivative.derivative.eval u₀| with hM
  have hMnn : 0 ≤ M := abs_nonneg _
  have hMub : ∀ v ∈ Set.Icc (-(1 + δ)) (1 + δ), |T.derivative.derivative.eval v| ≤ M :=
    fun v hv => hu₀max hv
  have hT' : ∀ v : ℝ, |v| ≤ 1 + δ → |T.derivative.eval v| ≤ ((n : ℝ) ^ 2) * E := by
    intro v hv
    have h := abs_deriv_chebyshevT_le_exp n hδ0 hv
    rw [hE]
    exact h
  -- 情形 B/C 的公共算术：`2M ≤ C₀ ⟹ M ≤ 32|n|⁴E`，其中 `C₀ = (n²+1)·(n²E) + (1+δ)·M`
  have harith : 2 * M ≤ ((n : ℝ) ^ 2 + 1) * (((n : ℝ) ^ 2) * E) + (1 + δ) * M →
      M ≤ 32 * |((n : ℤ) : ℝ)| ^ 4 * E := by
    intro h2M
    have h5 : M * (1 - δ) ≤ ((n : ℝ) ^ 2 + 1) * (((n : ℝ) ^ 2) * E) := by nlinarith [h2M]
    have h7 : M * (1 / 2) ≤ ((n : ℝ) ^ 2 + 1) * (((n : ℝ) ^ 2) * E) := by
      have h8 : M * (1 / 2) ≤ M * (1 - δ) := mul_le_mul_of_nonneg_left (by linarith) hMnn
      linarith
    have h6 : M ≤ 2 * (((n : ℝ) ^ 2 + 1) * (((n : ℝ) ^ 2) * E)) := by
      rw [show (2 : ℝ) * (((n : ℝ) ^ 2 + 1) * (((n : ℝ) ^ 2) * E))
          = (((n : ℝ) ^ 2 + 1) * (((n : ℝ) ^ 2) * E)) / (1 / 2) by ring]
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 1 / 2)]
      linarith [h7]
    have h8 : 2 * (((n : ℝ) ^ 2 + 1) * ((n : ℝ) ^ 2)) ≤ 32 * |((n : ℤ) : ℝ)| ^ 4 := by
      have h9 : ((n : ℝ) ^ 2) = |((n : ℤ) : ℝ)| ^ 2 := (sq_abs _).symm
      rw [h9]
      set A : ℝ := |((n : ℤ) : ℝ)| with hA
      have hA2 : 1 ≤ A ^ 2 := by nlinarith [hnabs1, hA]
      have hA4 : A ^ 2 ≤ A ^ 4 := by nlinarith [hA2, sq_nonneg (A ^ 2)]
      nlinarith [hA2, hA4]
    calc M ≤ 2 * (((n : ℝ) ^ 2 + 1) * (((n : ℝ) ^ 2) * E)) := h6
      _ = (2 * (((n : ℝ) ^ 2 + 1) * ((n : ℝ) ^ 2))) * E := by ring
      _ ≤ (32 * |((n : ℤ) : ℝ)| ^ 4) * E := mul_le_mul_of_nonneg_right h8 (Real.exp_pos _).le
      _ = 32 * |((n : ℤ) : ℝ)| ^ 4 * E := by ring
  -- 主论证：分三种情形
  have hmain : M ≤ 32 * |((n : ℤ) : ℝ)| ^ 4 * E := by
    by_cases hsmall : |u₀| ≤ 1
    · -- 情形 A：`|u₀| ≤ 1`
      have h16 : M ≤ 16 * ((n.natAbs : ℝ)) ^ 4 := by
        have hab : -(1 : ℝ) ≤ u₀ ∧ u₀ ≤ 1 := by
          have h := abs_le.mp hsmall
          exact ⟨h.1, h.2⟩
        have h := abs_deriv2_chebyshevT_le n (u := u₀) (by rw [Set.mem_Icc]; exact hab)
        rw [hM]
        exact h
      have hcast : ((n.natAbs : ℝ)) ^ 4 = |((n : ℤ) : ℝ)| ^ 4 := by
        rw [abs_intCast_eq_natAbs']
      rw [hcast] at h16
      nlinarith [h16, hE1, abs_nonneg ((n : ℤ) : ℝ)]
    · -- 情形 B/C：`|u₀| > 1`
      have hbig : 1 < |u₀| := lt_of_not_ge hsmall
      have hu₀ne : u₀ ≠ 0 := by
        intro h; rw [h, abs_zero] at hbig; norm_num at hbig
      have hu₀sq : 1 < u₀ ^ 2 := by
        have h := sq_abs u₀
        nlinarith [hbig, abs_nonneg u₀]
      have hWval : |W u₀| = (u₀ ^ 2 - 1) * M := by
        have h := chebyshevT_ode_eval n u₀
        have hWu : W u₀ = u₀ * T.derivative.eval u₀ - ((n : ℝ) ^ 2) * T.eval u₀ := rfl
        rw [hWu, ← h, abs_mul, abs_of_nonpos (by linarith : (1 - u₀ ^ 2) ≤ 0), neg_sub, hM]
      have hC0 : ∀ v ∈ Set.Icc (-(1 + δ)) (1 + δ),
          |deriv W v| ≤ ((n : ℝ) ^ 2 + 1) * (((n : ℝ) ^ 2) * E) + (1 + δ) * M := by
        intro v hv
        rw [Set.mem_Icc] at hv
        have hvabs : |v| ≤ 1 + δ := abs_le.mpr ⟨by linarith [hv.1], hv.2⟩
        have h1 : |T.derivative.eval v| ≤ ((n : ℝ) ^ 2) * E := hT' v hvabs
        have h2 : |T.derivative.derivative.eval v| ≤ M := hMub v (by rw [Set.mem_Icc]; exact hv)
        have hd : deriv W v = -(((n : ℝ) ^ 2) - 1) * T.derivative.eval v
            + v * T.derivative.derivative.eval v := (hWderiv v).deriv
        have hcoef : |((n : ℝ) ^ 2) - 1| ≤ (n : ℝ) ^ 2 + 1 := by
          have h := abs_sub_le ((n : ℝ) ^ 2) 0 1
          simpa using h
        calc |deriv W v| = |(-(((n : ℝ) ^ 2) - 1)) * T.derivative.eval v
              + v * T.derivative.derivative.eval v| := by rw [hd]
          _ ≤ |(-(((n : ℝ) ^ 2) - 1)) * T.derivative.eval v|
              + |v * T.derivative.derivative.eval v| := abs_add_le _ _
          _ = |((n : ℝ) ^ 2) - 1| * |T.derivative.eval v|
              + |v| * |T.derivative.derivative.eval v| := by rw [abs_mul, abs_mul, abs_neg]
          _ ≤ (((n : ℝ) ^ 2) + 1) * (((n : ℝ) ^ 2) * E) + (1 + δ) * M :=
              add_le_add (mul_le_mul hcoef h1 (abs_nonneg _) (by positivity))
                (mul_le_mul hvabs h2 (abs_nonneg _) (by linarith))
      have hmvt : ∀ s : ℝ, s ∈ Set.Icc (-(1 + δ)) (1 + δ) →
          |W u₀ - W s| ≤ (((n : ℝ) ^ 2 + 1) * (((n : ℝ) ^ 2) * E) + (1 + δ) * M) * |u₀ - s| := by
        intro s hs
        have hsub : Set.uIcc s u₀ ⊆ Set.Icc (-(1 + δ)) (1 + δ) := by
          intro x hx
          rw [Set.mem_uIcc] at hx
          rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact ⟨by linarith [hs.1, h1], by linarith [h2, hu₀mem.2]⟩
          · exact ⟨by linarith [hu₀mem.1, h1], by linarith [h2, hs.2]⟩
        have h := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (f := W)
          (s := Set.uIcc s u₀)
          (C := ((n : ℝ) ^ 2 + 1) * (((n : ℝ) ^ 2) * E) + (1 + δ) * M)
          (x := s) (y := u₀)
          (fun x _ => (hWderiv x).differentiableAt)
          (fun x hx => by rw [Real.norm_eq_abs]; exact hC0 x (hsub hx))
          (convex_uIcc s u₀) Set.left_mem_uIcc Set.right_mem_uIcc
        simpa only [Real.norm_eq_abs] using h
      rcases lt_or_gt_of_ne hu₀ne with hneg | hpos
      · -- `u₀ < 0`：从 `-1` 出发
        have hu₀1 : u₀ < -1 := by
          rw [abs_of_neg hneg] at hbig
          linarith
        have hmem : (-1 : ℝ) ∈ Set.Icc (-(1 + δ)) (1 + δ) :=
          ⟨by linarith, by linarith [hδ0]⟩
        have hm := hmvt (-1) hmem
        rw [hWm1, sub_zero] at hm
        have h1 : (u₀ ^ 2 - 1) * M
            ≤ (((n : ℝ) ^ 2 + 1) * (((n : ℝ) ^ 2) * E) + (1 + δ) * M) * (-(u₀ + 1)) := by
          rw [← hWval]
          refine hm.trans (le_of_eq ?_)
          rw [show u₀ - -1 = u₀ + 1 by ring, abs_of_nonpos (by linarith : u₀ + 1 ≤ 0)]
        have h2 : (u₀ ^ 2 - 1) * M = (-(u₀ + 1)) * ((-(u₀ - 1)) * M) := by ring
        rw [h2] at h1
        have hfac : 0 < -(u₀ + 1) := by linarith
        have h1' : (-(u₀ + 1)) * ((-(u₀ - 1)) * M)
            ≤ (-(u₀ + 1)) * (((n : ℝ) ^ 2 + 1) * (((n : ℝ) ^ 2) * E) + (1 + δ) * M) := by
          rw [mul_comm (-(u₀ + 1))
            (((n : ℝ) ^ 2 + 1) * (((n : ℝ) ^ 2) * E) + (1 + δ) * M)]
          exact h1
        have h3 : (-(u₀ - 1)) * M
            ≤ ((n : ℝ) ^ 2 + 1) * (((n : ℝ) ^ 2) * E) + (1 + δ) * M :=
          le_of_mul_le_mul_left h1' hfac
        have h4 : 2 * M ≤ ((n : ℝ) ^ 2 + 1) * (((n : ℝ) ^ 2) * E) + (1 + δ) * M := by
          nlinarith [h3, hMnn, hu₀1]
        exact harith h4
      · -- `u₀ > 0`：从 `1` 出发
        have hu₀1 : 1 < u₀ := by
          rw [abs_of_pos hpos] at hbig
          linarith
        have hmem : (1 : ℝ) ∈ Set.Icc (-(1 + δ)) (1 + δ) :=
          ⟨by linarith [hδ0], by linarith [hδ0]⟩
        have hm := hmvt 1 hmem
        rw [hW1, sub_zero] at hm
        have h1 : (u₀ ^ 2 - 1) * M
            ≤ (((n : ℝ) ^ 2 + 1) * (((n : ℝ) ^ 2) * E) + (1 + δ) * M) * (u₀ - 1) := by
          rw [← hWval]
          refine hm.trans (le_of_eq ?_)
          rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ u₀ - 1)]
        have h2 : (u₀ ^ 2 - 1) * M = (u₀ - 1) * ((u₀ + 1) * M) := by ring
        rw [h2] at h1
        have hfac : 0 < u₀ - 1 := by linarith only [hu₀1]
        have h1' : (u₀ - 1) * ((u₀ + 1) * M)
            ≤ (u₀ - 1) * (((n : ℝ) ^ 2 + 1) * (((n : ℝ) ^ 2) * E) + (1 + δ) * M) := by
          rw [mul_comm (u₀ - 1)
            (((n : ℝ) ^ 2 + 1) * (((n : ℝ) ^ 2) * E) + (1 + δ) * M)]
          exact h1
        have h3 : (u₀ + 1) * M
            ≤ ((n : ℝ) ^ 2 + 1) * (((n : ℝ) ^ 2) * E) + (1 + δ) * M :=
          le_of_mul_le_mul_left h1' hfac
        have h4 : 2 * M ≤ ((n : ℝ) ^ 2 + 1) * (((n : ℝ) ^ 2) * E) + (1 + δ) * M := by
          nlinarith [h3, hMnn, hu₀1]
        exact harith h4
  have hMu : |T.derivative.derivative.eval u| ≤ M :=
    hMub u (by
      rw [Set.mem_Icc]
      exact ⟨by linarith [neg_abs_le u, hu], by linarith [le_abs_self u, hu]⟩)
  rw [hE] at hmain
  linarith [hMu, hmain]

/-! ## §3 τ-一致的 collar 界（用 `FinalSmall.norm_fcoef_le_min` 的 `√` 技巧去掉 `E` 因子）

`CollarBound` 的 collar 界对**整个** Chebyshev 和用了同一个椭圆参数 `δ'`，于是系数界
`‖fcoef τ n‖ ≤ e^{τ sinh δ' - nδ'}` 里的 `e^{τ sinh δ'}`（在 `τ ≍ q` 时是 `e^{ρq sinh δ'}`）
被原样带出。本节的修正是：对**每个** `n` 各取一次 `δ`，并利用

`min(1, e^{τ sinh δ - nδ}) ≤ e^{(τ sinh δ - nδ)/2}`（`min 1 x ≤ √x`）

把它变成同一个 `δ` 下的「半指数」界；取 `δ := 2s + 1/(4(1+τ))`（`s := 2√(B/τ)`）后
* 系数衰减 `e^{-n(δ/2-s)} = e^{-n/(8(1+τ))}`；
* collar 上 `|T_n(u)| ≤ e^{n·s}`（`u ≤ 1+B/τ`），两者抵消，只剩 `e^{τ sinh δ/2}`；
* 而 `τ sinh δ ≤ (2τs + τ/(4(1+τ)))·cosh(2s)cosh(λ) ≤ 0.6`（`τs`、`s` 小时），**与 `q` 无关**。

于是 `Σ_n |c_n||T_n(u)| = O(poly(k))` 而不带任何指数因子。 -/

/-- `min 1 x ≤ √x`（`x ≥ 0`）。 -/
lemma min_one_le_sqrt {x : ℝ} (hx : 0 ≤ x) : min 1 x ≤ Real.sqrt x := by
  rcases le_or_gt x 1 with h | h
  · rw [min_eq_right h]
    exact Real.le_sqrt_of_sq_le (by nlinarith)
  · rw [min_eq_left h.le]
    exact Real.one_le_sqrt.mpr h.le

/-- **系数界（`√` 技巧）**：`‖fcoef τ n‖ ≤ e^{(τ sinh δ - nδ)/2}`（`δ > 0`、`n > 0`、`τ ≥ 0`）。 -/
lemma norm_fcoef_le_sqrt_min (τ : ℝ) (hτ : 0 ≤ τ) {δ : ℝ} (hδ : 0 < δ) {n : ℤ} (hn : 0 < n) :
    ‖fcoef τ n‖ ≤ Real.exp ((τ * Real.sinh δ - n * δ) / 2) := by
  refine (norm_fcoef_le_min τ hτ hδ hn).trans ?_
  have hx : 0 ≤ Real.exp (τ * Real.sinh δ - n * δ) := (Real.exp_pos _).le
  refine (min_one_le_sqrt hx).trans (le_of_eq ?_)
  rw [← Real.exp_half]

/-- `‖fcoef τ 0‖ ≤ 1`：由 `norm_fcoef_le`（`n = 0`）令 `δ → 0⁺` 得到。 -/
lemma norm_fcoef_zero_le_one (τ : ℝ) (hτ : 0 ≤ τ) : ‖fcoef τ 0‖ ≤ 1 := by
  have hcont : Continuous fun δ : ℝ => Real.exp (τ * Real.sinh δ) :=
    Real.continuous_exp.comp (continuous_const.mul Real.continuous_sinh)
  have h1 : Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1)) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h2 : Tendsto (fun k : ℕ => Real.exp (τ * Real.sinh ((1 : ℝ) / ((k : ℝ) + 1))))
      atTop (nhds 1) := by
    have h := (hcont.tendsto 0).comp h1
    have h0 : Real.exp (τ * Real.sinh 0) = 1 := by simp [Real.sinh_zero]
    rwa [h0] at h
  refine le_of_tendsto_of_tendsto tendsto_const_nhds h2 ?_
  filter_upwards with k
  have := norm_fcoef_le τ hτ (by positivity : (0 : ℝ) < 1 / ((k : ℝ) + 1)) 0
  simpa using this

/-- collar 参数 `δ := 2s + 1/(4(1+τ))`，其中 `s := 2√(B/τ)`。 -/
noncomputable def collarDelta (τ B : ℝ) : ℝ := 2 * (2 * Real.sqrt (B / τ)) + 1 / (4 * (1 + τ))

/-- collar 常数 `E := e^{τ sinh δ/2}` —— 本文件中它**只**依赖 `√(Bτ)` 与 `τ`，不含 `k`/`q`。 -/
noncomputable def collarE (τ B : ℝ) : ℝ := Real.exp (τ * Real.sinh (collarDelta τ B) / 2)

lemma collarDelta_pos (τ B : ℝ) (hτ : 0 < τ) (hB : 0 < B) : 0 < collarDelta τ B := by
  rw [collarDelta]
  have h1 : (0 : ℝ) ≤ 2 * (2 * Real.sqrt (B / τ)) := by positivity
  have h2 : (0 : ℝ) < 1 / (4 * (1 + τ)) := by positivity
  linarith

/-- `s = 2√(B/τ) ≤ δ/2`（`δ/2 - s = 1/(8(1+τ)) > 0`）。 -/
lemma collar_sqrt_le_half_delta (τ B : ℝ) (hτ : 0 < τ) :
    2 * Real.sqrt (B / τ) ≤ collarDelta τ B / 2 := by
  rw [collarDelta]
  have h1 : (0 : ℝ) ≤ 1 / (4 * (1 + τ)) := by positivity
  linarith

/-- `B/τ ≤ δ`（`s ≤ 1/8` 时）。 -/
lemma div_le_collarDelta (τ B : ℝ) (hτ : 0 < τ) (hB : 0 < B) (hs : 2 * Real.sqrt (B / τ) ≤ 1 / 8) :
    B / τ ≤ collarDelta τ B := by
  have hs0 : 0 ≤ B / τ := by positivity
  have hspos : (0 : ℝ) ≤ 2 * Real.sqrt (B / τ) := by positivity
  have hsq : B / τ = (2 * Real.sqrt (B / τ)) ^ 2 / 4 := by
    rw [mul_pow, Real.sq_sqrt hs0]; ring
  rw [hsq, collarDelta]
  have h1 : (0 : ℝ) ≤ 1 / (4 * (1 + τ)) := by positivity
  nlinarith [hs, hspos, h1]

/-- `sinh x ≤ x·cosh x`（`x ≥ 0`）。 -/
lemma sinh_le_mul_cosh {x : ℝ} (hx : 0 ≤ x) : Real.sinh x ≤ x * Real.cosh x := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (f := Real.sinh)
    (s := Set.Icc 0 x) (C := Real.cosh x) (x := 0) (y := x)
    (fun y _ => Real.differentiableAt_sinh)
    (fun y hy => by
      rw [Real.deriv_sinh, Real.norm_eq_abs, abs_of_nonneg (Real.cosh_pos y).le]
      exact Real.cosh_le_cosh.mpr (by
        rw [abs_of_nonneg hy.1, abs_of_nonneg hx]
        exact hy.2))
    (convex_Icc 0 x) (Set.left_mem_Icc.mpr hx) (Set.right_mem_Icc.mpr hx)
  have hsinh0 : 0 ≤ Real.sinh x := Real.sinh_nonneg_iff.mpr hx
  have h' : Real.sinh x ≤ Real.cosh x * x := by
    simpa [Real.sinh_zero, Real.norm_eq_abs, abs_of_nonneg hx, abs_of_nonneg hsinh0] using h
  simpa [mul_comm] using h'

/-- `e^y ≤ 1/(1-y)`（`0 ≤ y < 1`）：由中值定理 `e^y - 1 ≤ y·e^y`。 -/
lemma exp_le_one_div_one_sub {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) :
    Real.exp y ≤ 1 / (1 - y) := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (f := Real.exp)
    (s := Set.Icc 0 y) (C := Real.exp y) (x := 0) (y := y)
    (fun t _ => Real.differentiableAt_exp)
    (fun t ht => by
      rw [Real.deriv_exp, Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos t).le]
      exact Real.exp_le_exp.mpr ht.2)
    (convex_Icc 0 y) (Set.left_mem_Icc.mpr hy0) (Set.right_mem_Icc.mpr hy0)
  have h' : Real.exp y - 1 ≤ Real.exp y * y := by
    have h2 : |Real.exp y - 1| ≤ Real.exp y * |y| := by
      simpa [Real.norm_eq_abs, Real.exp_zero] using h
    rw [abs_of_nonneg hy0,
      abs_of_nonneg (by linarith [Real.one_le_exp hy0] : (0 : ℝ) ≤ Real.exp y - 1)] at h2
    exact h2
  have h3 : 0 < 1 - y := by linarith
  rw [le_div_iff₀ h3]
  linarith

/-- `cosh (1/4) ≤ 1.1`：由中值定理 `cosh(1/4) - 1 ≤ (1/4)·sinh(1/4) ≤ (1/16)·cosh(1/4)`。 -/
lemma cosh_quarter_le : Real.cosh (1 / 4) ≤ 1.1 := by
  have h1 : Real.cosh (1 / 4) ≤ (1 / 4) * Real.sinh (1 / 4) + 1 := by
    have h := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (f := Real.cosh)
      (s := Set.Icc 0 (1 / 4)) (C := Real.sinh (1 / 4)) (x := 0) (y := 1 / 4)
      (fun t _ => Real.differentiableAt_cosh)
      (fun t ht => by
        rw [Real.deriv_cosh, Real.norm_eq_abs, abs_of_nonneg (Real.sinh_nonneg_iff.mpr ht.1)]
        exact Real.sinh_le_sinh.mpr ht.2)
      (convex_Icc 0 (1 / 4)) (Set.left_mem_Icc.mpr (by norm_num))
      (Set.right_mem_Icc.mpr (by norm_num))
    have h' : Real.cosh (1 / 4) - 1 ≤ Real.sinh (1 / 4) * (1 / 4) := by
      have h2 : |Real.cosh (1 / 4) - 1| ≤ Real.sinh (1 / 4) * (1 / 4) := by
        simpa [Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4),
          Real.cosh_zero] using h
      rwa [abs_of_nonneg (by linarith [Real.one_le_cosh (1 / 4)] :
        (0 : ℝ) ≤ Real.cosh (1 / 4) - 1)] at h2
    linarith
  have h2 : Real.sinh (1 / 4) ≤ (1 / 4) * Real.cosh (1 / 4) :=
    sinh_le_mul_cosh (by norm_num)
  have h3 : 0 < Real.cosh (1 / 4) := Real.cosh_pos _
  nlinarith [h1, h2, h3]

lemma cosh_le_cosh_quarter {x : ℝ} (hx : |x| ≤ 1 / 4) : Real.cosh x ≤ 1.1 :=
  (Real.cosh_le_cosh.mpr (by rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4)]; exact hx)).trans
    cosh_quarter_le

/-- `collarE τ B ≤ 2`：由 `s ≤ 1/8`、`τ s ≤ 1/8` 得 `τ sinh δ ≤ 0.61`。 -/
lemma collarE_le_two (τ B : ℝ) (hτ : 0 < τ) (hB : 0 < B) (hs : 2 * Real.sqrt (B / τ) ≤ 1 / 8)
    (hst : τ * (2 * Real.sqrt (B / τ)) ≤ 1 / 8) : collarE τ B ≤ 2 := by
  set s : ℝ := 2 * Real.sqrt (B / τ) with hsd
  set lam : ℝ := 1 / (4 * (1 + τ)) with hlam
  have hs0 : 0 ≤ s := by rw [hsd]; positivity
  have hlam0 : 0 < lam := by rw [hlam]; positivity
  have hlamle : lam ≤ 1 / 4 := by
    rw [hlam, div_le_iff₀ (by positivity : (0 : ℝ) < 4 * (1 + τ))]
    linarith
  have hsle : s ≤ 1 / 8 := hs
  have h2s : 2 * s ≤ 1 / 4 := by linarith
  have hsinh : Real.sinh (2 * s + lam) ≤ (2 * s + lam) * Real.cosh (2 * s) * Real.cosh lam := by
    have h1 : Real.sinh (2 * s + lam)
        = Real.sinh (2 * s) * Real.cosh lam + Real.cosh (2 * s) * Real.sinh lam :=
      Real.sinh_add _ _
    have h2 : Real.sinh (2 * s) ≤ (2 * s) * Real.cosh (2 * s) :=
      sinh_le_mul_cosh (by linarith)
    have h3 : Real.sinh lam ≤ lam * Real.cosh lam := sinh_le_mul_cosh hlam0.le
    have hc0 : 0 < Real.cosh lam := Real.cosh_pos lam
    have hc1 : 0 < Real.cosh (2 * s) := Real.cosh_pos _
    nlinarith [h1, h2, h3, hc0, hc1, hs0, hlam0.le]
  have hcosh2s : Real.cosh (2 * s) ≤ 1.1 := by
    refine cosh_le_cosh_quarter ?_
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * s)]
    linarith
  have hcoshlam : Real.cosh lam ≤ 1.1 := cosh_le_cosh_quarter (by rw [abs_of_nonneg hlam0.le]; exact hlamle)
  have htau : τ * (2 * s + lam) ≤ 1 / 2 := by
    have hτlam : τ * lam = τ / (4 * (1 + τ)) := by rw [hlam]; ring
    have hτlamle : τ / (4 * (1 + τ)) ≤ 1 / 4 := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 4 * (1 + τ))]
      linarith
    have hτs : τ * s ≤ 1 / 8 := hst
    linarith [hτlam, hτlamle, hτs]
  have hmain : τ * Real.sinh (2 * s + lam) ≤ 1 := by
    have h1 : τ * Real.sinh (2 * s + lam)
        ≤ τ * ((2 * s + lam) * Real.cosh (2 * s) * Real.cosh lam) :=
      mul_le_mul_of_nonneg_left hsinh hτ.le
    have h2 : τ * ((2 * s + lam) * Real.cosh (2 * s) * Real.cosh lam)
        = (τ * (2 * s + lam)) * Real.cosh (2 * s) * Real.cosh lam := by ring
    have h3 : (τ * (2 * s + lam)) * Real.cosh (2 * s) * Real.cosh lam ≤ 0.61 := by
      have h1 : (τ * (2 * s + lam)) * Real.cosh (2 * s) ≤ (1 / 2) * 1.1 :=
        mul_le_mul htau hcosh2s (Real.cosh_pos _).le (by norm_num)
      have h2 : (τ * (2 * s + lam)) * Real.cosh (2 * s) * Real.cosh lam
          ≤ ((1 / 2) * 1.1) * 1.1 :=
        mul_le_mul h1 hcoshlam (Real.cosh_pos _).le (by norm_num)
      linarith
    linarith
  have hE : collarE τ B = Real.exp (τ * Real.sinh (2 * s + lam) / 2) := by
    rw [collarE, collarDelta, hsd, hlam]
  have hhalf : τ * Real.sinh (2 * s + lam) / 2 ≤ 1 / 2 :=
    div_le_div_of_nonneg_right hmain (by norm_num)
  have hexp : Real.exp (1 / 2 : ℝ) ≤ 2 := by
    have h := exp_le_one_div_one_sub (y := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
    norm_num at h
    exact h
  rw [hE]
  exact (Real.exp_le_exp.mpr hhalf).trans hexp

/-! ### T 的复/实对应（一阶、二阶导） -/

lemma chebT_complex_deriv_eval' (n : ℤ) (u : ℝ) :
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

lemma chebT_complex_deriv2_eval' (n : ℤ) (u : ℝ) :
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
    funext fun y => (chebT_complex_deriv_eval' n y).symm
  rw [hfun] at hB
  exact hA.unique hB

/-- **collar 上 `approxPoly` 的值界（无 `E` 因子）**：`|u| ≤ 1+B/τ` 时
`‖approxPoly τ k (u)‖ ≤ 1 + 2k·E`。 -/
lemma norm_approxPoly_le_collar_sharp (τ B : ℝ) (hτ : 0 < τ) (hB : 0 < B) (k : ℕ)
    {u : ℝ} (hu : |u| ≤ 1 + B / τ) :
    ‖(approxPoly τ k).eval (u : ℂ)‖ ≤ 1 + 2 * (k : ℝ) * collarE τ B := by
  set δ := collarDelta τ B with hδ
  set E := collarE τ B with hE
  have hEpos : 0 < E := by rw [hE, collarE]; positivity
  have hs0 : 0 ≤ B / τ := by positivity
  have hδ0 : 0 < δ := collarDelta_pos τ B hτ hB
  have hsd : 2 * Real.sqrt (B / τ) ≤ δ / 2 := collar_sqrt_le_half_delta τ B hτ
  have hsplit : (approxPoly τ k).eval (u : ℂ)
      = fcoef τ 0 + ∑ m ∈ Finset.range (k - 1),
          2 * fcoef τ ((m : ℤ) + 1) * (Polynomial.Chebyshev.T ℂ ((m : ℤ) + 1)).eval (u : ℂ) := by
    rw [approxPoly, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_finsetSum]
    congr 1
    exact Finset.sum_congr rfl fun m _ => by rw [Polynomial.eval_mul, Polynomial.eval_C]
  have hterm : ∀ m ∈ Finset.range (k - 1),
      ‖2 * fcoef τ ((m : ℤ) + 1) * (Polynomial.Chebyshev.T ℂ ((m : ℤ) + 1)).eval (u : ℂ)‖
        ≤ 2 * E := by
    intro m _
    have hjpos : 0 < ((m : ℤ) + 1) := by omega
    have hcast : |((((m : ℤ) + 1 : ℤ)) : ℝ)| = ((m + 1 : ℕ) : ℝ) := by
      have h0 : (0 : ℤ) ≤ (m : ℤ) + 1 := by omega
      rw [abs_of_nonneg (by exact_mod_cast h0)]
      push_cast
      ring
    have hcastZ : ((((m : ℤ) + 1 : ℤ)) : ℝ) = ((m + 1 : ℕ) : ℝ) := by push_cast; ring
    have hf : ‖fcoef τ ((m : ℤ) + 1)‖
        ≤ Real.exp ((τ * Real.sinh δ - ((m + 1 : ℕ) : ℝ) * δ) / 2) := by
      have h := norm_fcoef_le_sqrt_min τ hτ.le hδ0 hjpos
      rwa [hcastZ] at h
    have hT : ‖(Polynomial.Chebyshev.T ℂ ((m : ℤ) + 1)).eval (u : ℂ)‖
        ≤ Real.exp (((m + 1 : ℕ) : ℝ) * (2 * Real.sqrt (B / τ))) := by
      have h1 : ‖(Polynomial.Chebyshev.T ℂ ((m : ℤ) + 1)).eval (u : ℂ)‖
          = |(Polynomial.Chebyshev.T ℝ ((m : ℤ) + 1)).eval u| := by
        rw [← Polynomial.Chebyshev.complex_ofReal_eval_T u ((m : ℤ) + 1)]
        exact Complex.norm_real _
      rw [h1]
      have h2 := abs_chebyshevT_le_exp ((m : ℤ) + 1) hs0 hu
      rw [hcast] at h2
      simpa only [mul_assoc] using h2
    have hexp : Real.exp ((τ * Real.sinh δ - ((m + 1 : ℕ) : ℝ) * δ) / 2)
        * Real.exp (((m + 1 : ℕ) : ℝ) * (2 * Real.sqrt (B / τ))) ≤ E := by
      rw [← Real.exp_add, hE, collarE, ← hδ]
      refine Real.exp_le_exp.mpr ?_
      have h1 : ((m + 1 : ℕ) : ℝ) * (2 * Real.sqrt (B / τ)) ≤ ((m + 1 : ℕ) : ℝ) * (δ / 2) :=
        mul_le_mul_of_nonneg_left hsd (by positivity)
      linarith
    calc ‖2 * fcoef τ ((m : ℤ) + 1) * (Polynomial.Chebyshev.T ℂ ((m : ℤ) + 1)).eval (u : ℂ)‖
        = 2 * ‖fcoef τ ((m : ℤ) + 1)‖
          * ‖(Polynomial.Chebyshev.T ℂ ((m : ℤ) + 1)).eval (u : ℂ)‖ := by
          rw [norm_mul, norm_mul]
          norm_num
      _ ≤ 2 * Real.exp ((τ * Real.sinh δ - ((m + 1 : ℕ) : ℝ) * δ) / 2)
          * Real.exp (((m + 1 : ℕ) : ℝ) * (2 * Real.sqrt (B / τ))) := by
          have h1 : (0 : ℝ) ≤ ‖fcoef τ ((m : ℤ) + 1)‖ := norm_nonneg _
          have h2 : (0 : ℝ) ≤ ‖(Polynomial.Chebyshev.T ℂ ((m : ℤ) + 1)).eval (u : ℂ)‖ :=
            norm_nonneg _
          nlinarith [hf, hT, h1, h2]
      _ = 2 * (Real.exp ((τ * Real.sinh δ - ((m + 1 : ℕ) : ℝ) * δ) / 2)
          * Real.exp (((m + 1 : ℕ) : ℝ) * (2 * Real.sqrt (B / τ)))) := by ring
      _ ≤ 2 * E := mul_le_mul_of_nonneg_left hexp (by norm_num)
  have hc0 : ‖fcoef τ 0‖ ≤ 1 := norm_fcoef_zero_le_one τ hτ.le
  have hsum : ‖∑ m ∈ Finset.range (k - 1),
        2 * fcoef τ ((m : ℤ) + 1) * (Polynomial.Chebyshev.T ℂ ((m : ℤ) + 1)).eval (u : ℂ)‖
      ≤ 2 * (k : ℝ) * E := by
    refine (norm_sum_le (Finset.range (k - 1)) _).trans ?_
    have h1 : ∑ m ∈ Finset.range (k - 1),
        ‖2 * fcoef τ ((m : ℤ) + 1) * (Polynomial.Chebyshev.T ℂ ((m : ℤ) + 1)).eval (u : ℂ)‖
        ≤ ∑ _m ∈ Finset.range (k - 1), 2 * E := Finset.sum_le_sum hterm
    have h2 : ∑ _m ∈ Finset.range (k - 1), (2 * E : ℝ) = ((k - 1 : ℕ) : ℝ) * (2 * E) := by
      simp
    have h3 : (((k - 1 : ℕ) : ℝ)) * (2 * E) ≤ (k : ℝ) * (2 * E) := by
      have : (((k - 1 : ℕ) : ℝ)) ≤ (k : ℝ) := by
        exact_mod_cast Nat.sub_le k 1
      exact mul_le_mul_of_nonneg_right this (by linarith [hEpos])
    calc ∑ m ∈ Finset.range (k - 1),
          ‖2 * fcoef τ ((m : ℤ) + 1) * (Polynomial.Chebyshev.T ℂ ((m : ℤ) + 1)).eval (u : ℂ)‖
        ≤ ∑ _m ∈ Finset.range (k - 1), (2 * E : ℝ) := h1
      _ = ((k - 1 : ℕ) : ℝ) * (2 * E) := h2
      _ ≤ (k : ℝ) * (2 * E) := h3
      _ = 2 * (k : ℝ) * E := by ring
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  linarith

/-- **collar 上 `approxPoly'` 的值界（无 `E` 因子）**：`‖(approxPoly τ k)'‖ ≤ 2k³·E`。 -/
lemma norm_deriv_approxPoly_le_collar_sharp (τ B : ℝ) (hτ : 0 < τ) (hB : 0 < B) (k : ℕ)
    {u : ℝ} (hu : |u| ≤ 1 + B / τ) :
    ‖deriv (fun x : ℝ => (approxPoly τ k).eval (x : ℂ)) u‖ ≤ 2 * (k : ℝ) ^ 3 * collarE τ B := by
  set δ := collarDelta τ B with hδ
  set E := collarE τ B with hE
  have hEpos : 0 < E := by rw [hE, collarE]; positivity
  have hs0 : 0 ≤ B / τ := by positivity
  have hδ0 : 0 < δ := collarDelta_pos τ B hτ hB
  have hsd : 2 * Real.sqrt (B / τ) ≤ δ / 2 := collar_sqrt_le_half_delta τ B hτ
  rw [deriv_poly_ofReal, eval_derivative_approxPoly]
  refine (norm_sum_le (Finset.range (k - 1)) _).trans ?_
  have hterm : ∀ m ∈ Finset.range (k - 1),
      ‖2 * fcoef τ ((m : ℤ) + 1)
        * (Polynomial.Chebyshev.T ℂ ((m : ℤ) + 1)).derivative.eval (u : ℂ)‖
        ≤ 2 * E * (k : ℝ) ^ 2 := by
    intro m hm
    have hmk : m + 1 ≤ k := by
      have h := Finset.mem_range.mp hm
      omega
    have hkc : (((m + 1 : ℕ)) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hmk
    have hjpos : 0 < ((m : ℤ) + 1) := by omega
    have hcast : |((((m : ℤ) + 1 : ℤ)) : ℝ)| = ((m + 1 : ℕ) : ℝ) := by
      have h0 : (0 : ℤ) ≤ (m : ℤ) + 1 := by omega
      rw [abs_of_nonneg (by exact_mod_cast h0)]
      push_cast
      ring
    have hcastZ : ((((m : ℤ) + 1 : ℤ)) : ℝ) = ((m + 1 : ℕ) : ℝ) := by push_cast; ring
    have hf : ‖fcoef τ ((m : ℤ) + 1)‖
        ≤ Real.exp ((τ * Real.sinh δ - ((m + 1 : ℕ) : ℝ) * δ) / 2) := by
      have h := norm_fcoef_le_sqrt_min τ hτ.le hδ0 hjpos
      rwa [hcastZ] at h
    have hT : ‖(Polynomial.Chebyshev.T ℂ ((m : ℤ) + 1)).derivative.eval (u : ℂ)‖
        ≤ (k : ℝ) ^ 2 * Real.exp (((m + 1 : ℕ) : ℝ) * (2 * Real.sqrt (B / τ))) := by
      have h1 : ‖(Polynomial.Chebyshev.T ℂ ((m : ℤ) + 1)).derivative.eval (u : ℂ)‖
          = |(Polynomial.Chebyshev.T ℝ ((m : ℤ) + 1)).derivative.eval u| := by
        rw [chebT_complex_deriv_eval' ((m : ℤ) + 1) u]
        exact Complex.norm_real _
      rw [h1]
      have h2 := abs_deriv_chebyshevT_le_exp ((m : ℤ) + 1) hs0 hu
      rw [hcast] at h2
      refine h2.trans ?_
      have h3 : (((m + 1 : ℕ)) : ℝ) ^ 2 ≤ (k : ℝ) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hkc 2
      calc (((m + 1 : ℕ)) : ℝ) ^ 2
            * Real.exp (((m + 1 : ℕ) : ℝ) * 2 * Real.sqrt (B / τ))
          ≤ (k : ℝ) ^ 2 * Real.exp (((m + 1 : ℕ) : ℝ) * 2 * Real.sqrt (B / τ)) :=
            mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
        _ = (k : ℝ) ^ 2 * Real.exp (((m + 1 : ℕ) : ℝ) * (2 * Real.sqrt (B / τ))) := by
            rw [show ((m + 1 : ℕ) : ℝ) * 2 * Real.sqrt (B / τ)
              = ((m + 1 : ℕ) : ℝ) * (2 * Real.sqrt (B / τ)) from by ring]
    have hexp : Real.exp ((τ * Real.sinh δ - ((m + 1 : ℕ) : ℝ) * δ) / 2)
        * Real.exp (((m + 1 : ℕ) : ℝ) * (2 * Real.sqrt (B / τ))) ≤ E := by
      rw [← Real.exp_add, hE, collarE, ← hδ]
      refine Real.exp_le_exp.mpr ?_
      have h1 : ((m + 1 : ℕ) : ℝ) * (2 * Real.sqrt (B / τ)) ≤ ((m + 1 : ℕ) : ℝ) * (δ / 2) :=
        mul_le_mul_of_nonneg_left hsd (by positivity)
      linarith
    calc ‖2 * fcoef τ ((m : ℤ) + 1)
          * (Polynomial.Chebyshev.T ℂ ((m : ℤ) + 1)).derivative.eval (u : ℂ)‖
        = 2 * ‖fcoef τ ((m : ℤ) + 1)‖
          * ‖(Polynomial.Chebyshev.T ℂ ((m : ℤ) + 1)).derivative.eval (u : ℂ)‖ := by
          rw [norm_mul, norm_mul]
          norm_num
      _ ≤ 2 * Real.exp ((τ * Real.sinh δ - ((m + 1 : ℕ) : ℝ) * δ) / 2)
          * ((k : ℝ) ^ 2 * Real.exp (((m + 1 : ℕ) : ℝ) * (2 * Real.sqrt (B / τ)))) := by
          have h1 : (0 : ℝ) ≤ ‖fcoef τ ((m : ℤ) + 1)‖ := norm_nonneg _
          have h2 : (0 : ℝ) ≤
            ‖(Polynomial.Chebyshev.T ℂ ((m : ℤ) + 1)).derivative.eval (u : ℂ)‖ := norm_nonneg _
          nlinarith [hf, hT, h1, h2]
      _ = 2 * (Real.exp ((τ * Real.sinh δ - ((m + 1 : ℕ) : ℝ) * δ) / 2)
          * Real.exp (((m + 1 : ℕ) : ℝ) * (2 * Real.sqrt (B / τ)))) * (k : ℝ) ^ 2 := by ring
      _ ≤ 2 * E * (k : ℝ) ^ 2 := by
          have h := mul_le_mul_of_nonneg_right hexp (by positivity : (0 : ℝ) ≤ (k : ℝ) ^ 2)
          linarith
  have hsum : ∑ m ∈ Finset.range (k - 1),
        ‖2 * fcoef τ ((m : ℤ) + 1)
          * (Polynomial.Chebyshev.T ℂ ((m : ℤ) + 1)).derivative.eval (u : ℂ)‖
      ≤ 2 * (k : ℝ) ^ 3 * E := by
    have h1 : ∑ m ∈ Finset.range (k - 1),
        ‖2 * fcoef τ ((m : ℤ) + 1)
          * (Polynomial.Chebyshev.T ℂ ((m : ℤ) + 1)).derivative.eval (u : ℂ)‖
        ≤ ∑ _m ∈ Finset.range (k - 1), (2 * E * (k : ℝ) ^ 2 : ℝ) := Finset.sum_le_sum hterm
    have h2 : ∑ _m ∈ Finset.range (k - 1), (2 * E * (k : ℝ) ^ 2 : ℝ)
        = ((k - 1 : ℕ) : ℝ) * (2 * E * (k : ℝ) ^ 2) := by simp
    have h3 : (((k - 1 : ℕ) : ℝ)) * (2 * E * (k : ℝ) ^ 2) ≤ 2 * (k : ℝ) ^ 3 * E := by
      have hk1 : (((k - 1 : ℕ) : ℝ)) ≤ (k : ℝ) := by exact_mod_cast Nat.sub_le k 1
      have h4 : (((k - 1 : ℕ) : ℝ)) * (2 * E * (k : ℝ) ^ 2) ≤ (k : ℝ) * (2 * E * (k : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right hk1 (by positivity)
      have h5 : (k : ℝ) * (2 * E * (k : ℝ) ^ 2) = 2 * (k : ℝ) ^ 3 * E := by ring
      linarith [h4, h5]
    linarith
  exact hsum

/-- **collar 上 `approxPoly''` 的值界（无 `E` 因子）**：`‖(approxPoly τ k)''‖ ≤ 64k⁵·E`
（`B/τ ≤ 1/2`；用 `§2` 的 `abs_deriv2_chebyshevT_le_exp`）。 -/
lemma norm_deriv2_approxPoly_le_collar_sharp (τ B : ℝ) (hτ : 0 < τ) (hB : 0 < B) (k : ℕ)
    (hBτ : B / τ ≤ 1 / 2) {u : ℝ} (hu : |u| ≤ 1 + B / τ) :
    ‖deriv (fun x : ℝ => deriv (fun y : ℝ => (approxPoly τ k).eval (y : ℂ)) x) u‖
      ≤ 64 * (k : ℝ) ^ 5 * collarE τ B := by
  set δ := collarDelta τ B with hδ
  set E := collarE τ B with hE
  have hEpos : 0 < E := by rw [hE, collarE]; positivity
  have hs0 : 0 ≤ B / τ := by positivity
  have hδ0 : 0 < δ := collarDelta_pos τ B hτ hB
  have hsd : 2 * Real.sqrt (B / τ) ≤ δ / 2 := collar_sqrt_le_half_delta τ B hτ
  rw [deriv2_poly_ofReal, eval_derivative2_approxPoly]
  refine (norm_sum_le (Finset.range (k - 1)) _).trans ?_
  have hterm : ∀ m ∈ Finset.range (k - 1),
      ‖2 * fcoef τ ((m : ℤ) + 1)
        * (Polynomial.Chebyshev.T ℂ ((m : ℤ) + 1)).derivative.derivative.eval (u : ℂ)‖
        ≤ 64 * E * (k : ℝ) ^ 4 := by
    intro m hm
    have hmk : m + 1 ≤ k := by
      have h := Finset.mem_range.mp hm
      omega
    have hkc : (((m + 1 : ℕ)) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hmk
    have hjpos : 0 < ((m : ℤ) + 1) := by omega
    have hcast : |((((m : ℤ) + 1 : ℤ)) : ℝ)| = ((m + 1 : ℕ) : ℝ) := by
      have h0 : (0 : ℤ) ≤ (m : ℤ) + 1 := by omega
      rw [abs_of_nonneg (by exact_mod_cast h0)]
      push_cast
      ring
    have hcastZ : ((((m : ℤ) + 1 : ℤ)) : ℝ) = ((m + 1 : ℕ) : ℝ) := by push_cast; ring
    have hf : ‖fcoef τ ((m : ℤ) + 1)‖
        ≤ Real.exp ((τ * Real.sinh δ - ((m + 1 : ℕ) : ℝ) * δ) / 2) := by
      have h := norm_fcoef_le_sqrt_min τ hτ.le hδ0 hjpos
      rwa [hcastZ] at h
    have hT : ‖(Polynomial.Chebyshev.T ℂ ((m : ℤ) + 1)).derivative.derivative.eval (u : ℂ)‖
        ≤ 32 * (k : ℝ) ^ 4 * Real.exp (((m + 1 : ℕ) : ℝ) * (2 * Real.sqrt (B / τ))) := by
      have h1 : ‖(Polynomial.Chebyshev.T ℂ ((m : ℤ) + 1)).derivative.derivative.eval (u : ℂ)‖
          = |(Polynomial.Chebyshev.T ℝ ((m : ℤ) + 1)).derivative.derivative.eval u| := by
        rw [chebT_complex_deriv2_eval' ((m : ℤ) + 1) u]
        exact Complex.norm_real _
      rw [h1]
      have h2 := abs_deriv2_chebyshevT_le_exp ((m : ℤ) + 1) hs0 hBτ hu
      rw [hcast] at h2
      refine h2.trans ?_
      have h3 : (((m + 1 : ℕ)) : ℝ) ^ 4 ≤ (k : ℝ) ^ 4 :=
        pow_le_pow_left₀ (by positivity) hkc 4
      calc 32 * (((m + 1 : ℕ)) : ℝ) ^ 4
            * Real.exp (((m + 1 : ℕ) : ℝ) * 2 * Real.sqrt (B / τ))
          ≤ 32 * (k : ℝ) ^ 4 * Real.exp (((m + 1 : ℕ) : ℝ) * 2 * Real.sqrt (B / τ)) := by
            have h4 : (0 : ℝ) ≤ 32 * Real.exp (((m + 1 : ℕ) : ℝ) * 2 * Real.sqrt (B / τ)) := by
              positivity
            nlinarith [h3, h4]
        _ = 32 * (k : ℝ) ^ 4 * Real.exp (((m + 1 : ℕ) : ℝ) * (2 * Real.sqrt (B / τ))) := by
            rw [show ((m + 1 : ℕ) : ℝ) * 2 * Real.sqrt (B / τ)
              = ((m + 1 : ℕ) : ℝ) * (2 * Real.sqrt (B / τ)) from by ring]
    have hexp : Real.exp ((τ * Real.sinh δ - ((m + 1 : ℕ) : ℝ) * δ) / 2)
        * Real.exp (((m + 1 : ℕ) : ℝ) * (2 * Real.sqrt (B / τ))) ≤ E := by
      rw [← Real.exp_add, hE, collarE, ← hδ]
      refine Real.exp_le_exp.mpr ?_
      have h1 : ((m + 1 : ℕ) : ℝ) * (2 * Real.sqrt (B / τ)) ≤ ((m + 1 : ℕ) : ℝ) * (δ / 2) :=
        mul_le_mul_of_nonneg_left hsd (by positivity)
      linarith
    calc ‖2 * fcoef τ ((m : ℤ) + 1)
          * (Polynomial.Chebyshev.T ℂ ((m : ℤ) + 1)).derivative.derivative.eval (u : ℂ)‖
        = 2 * ‖fcoef τ ((m : ℤ) + 1)‖
          * ‖(Polynomial.Chebyshev.T ℂ ((m : ℤ) + 1)).derivative.derivative.eval (u : ℂ)‖ := by
          rw [norm_mul, norm_mul]
          norm_num
      _ ≤ 2 * Real.exp ((τ * Real.sinh δ - ((m + 1 : ℕ) : ℝ) * δ) / 2)
          * (32 * (k : ℝ) ^ 4
            * Real.exp (((m + 1 : ℕ) : ℝ) * (2 * Real.sqrt (B / τ)))) := by
          have h1 : (0 : ℝ) ≤ ‖fcoef τ ((m : ℤ) + 1)‖ := norm_nonneg _
          have h2 : (0 : ℝ) ≤
            ‖(Polynomial.Chebyshev.T ℂ ((m : ℤ) + 1)).derivative.derivative.eval (u : ℂ)‖ :=
            norm_nonneg _
          nlinarith [hf, hT, h1, h2]
      _ = 64 * (Real.exp ((τ * Real.sinh δ - ((m + 1 : ℕ) : ℝ) * δ) / 2)
          * Real.exp (((m + 1 : ℕ) : ℝ) * (2 * Real.sqrt (B / τ)))) * (k : ℝ) ^ 4 := by ring
      _ ≤ 64 * E * (k : ℝ) ^ 4 := by
          have h := mul_le_mul_of_nonneg_right hexp (by positivity : (0 : ℝ) ≤ (k : ℝ) ^ 4)
          linarith
  have hsum : ∑ m ∈ Finset.range (k - 1),
        ‖2 * fcoef τ ((m : ℤ) + 1)
          * (Polynomial.Chebyshev.T ℂ ((m : ℤ) + 1)).derivative.derivative.eval (u : ℂ)‖
      ≤ 64 * (k : ℝ) ^ 5 * E := by
    have h1 : ∑ m ∈ Finset.range (k - 1),
        ‖2 * fcoef τ ((m : ℤ) + 1)
          * (Polynomial.Chebyshev.T ℂ ((m : ℤ) + 1)).derivative.derivative.eval (u : ℂ)‖
        ≤ ∑ _m ∈ Finset.range (k - 1), (64 * E * (k : ℝ) ^ 4 : ℝ) := Finset.sum_le_sum hterm
    have h2 : ∑ _m ∈ Finset.range (k - 1), (64 * E * (k : ℝ) ^ 4 : ℝ)
        = ((k - 1 : ℕ) : ℝ) * (64 * E * (k : ℝ) ^ 4) := by simp
    have h3 : (((k - 1 : ℕ) : ℝ)) * (64 * E * (k : ℝ) ^ 4) ≤ 64 * (k : ℝ) ^ 5 * E := by
      have hk1 : (((k - 1 : ℕ) : ℝ)) ≤ (k : ℝ) := by exact_mod_cast Nat.sub_le k 1
      have h4 : (((k - 1 : ℕ) : ℝ)) * (64 * E * (k : ℝ) ^ 4)
          ≤ (k : ℝ) * (64 * E * (k : ℝ) ^ 4) :=
        mul_le_mul_of_nonneg_right hk1 (by positivity)
      have h5 : (k : ℝ) * (64 * E * (k : ℝ) ^ 4) = 64 * (k : ℝ) ^ 5 * E := by ring
      linarith [h4, h5]
    linarith
  exact hsum

/-! ## §4 `scaledApprox` 的链式法则与 `Ψ_A` 在 collar 上的 `M₁`、`M₂` -/

/-- `scaledApprox` 的一阶导数多项式。 -/
lemma scaledApprox_derivative (τ : ℝ) (k : ℕ) :
    (scaledApprox τ k).derivative
      = ((approxPoly τ k).derivative.comp (Polynomial.C ((τ⁻¹ : ℝ) : ℂ) * Polynomial.X))
        * Polynomial.C ((τ⁻¹ : ℝ) : ℂ) := by
  rw [scaledApprox, Polynomial.derivative_comp, Polynomial.derivative_C_mul,
    Polynomial.derivative_X]
  ring

/-- **链式法则（一阶）**：`P'(μ) = Q'(μ/τ)/τ`（`P = scaledApprox τ k`、`Q = approxPoly τ k`）。 -/
lemma scaledApprox_deriv_eval (τ : ℝ) (hτ : τ ≠ 0) (k : ℕ) (μ : ℝ) :
    (scaledApprox τ k).derivative.eval (μ : ℂ)
      = (approxPoly τ k).derivative.eval (((μ / τ : ℝ)) : ℂ) * ((τ⁻¹ : ℝ) : ℂ) := by
  have harg : ((τ⁻¹ : ℝ) : ℂ) * (μ : ℂ) = ((μ / τ : ℝ) : ℂ) := by
    push_cast
    field_simp
  simp only [scaledApprox_derivative, Polynomial.eval_mul, Polynomial.eval_comp,
    Polynomial.eval_C, Polynomial.eval_X, harg]

/-- `scaledApprox` 的二阶导数多项式。 -/
lemma scaledApprox_derivative2 (τ : ℝ) (k : ℕ) :
    (scaledApprox τ k).derivative.derivative
      = (((approxPoly τ k).derivative.derivative.comp
            (Polynomial.C ((τ⁻¹ : ℝ) : ℂ) * Polynomial.X))
          * Polynomial.C ((τ⁻¹ : ℝ) : ℂ)) * Polynomial.C ((τ⁻¹ : ℝ) : ℂ) := by
  rw [scaledApprox_derivative, Polynomial.derivative_mul, Polynomial.derivative_comp,
    Polynomial.derivative_C_mul, Polynomial.derivative_X, Polynomial.derivative_C, mul_zero,
    add_zero]
  ring

/-- **链式法则（二阶）**：`P''(μ) = Q''(μ/τ)/τ²`。 -/
lemma scaledApprox_deriv2_eval (τ : ℝ) (hτ : τ ≠ 0) (k : ℕ) (μ : ℝ) :
    (scaledApprox τ k).derivative.derivative.eval (μ : ℂ)
      = (approxPoly τ k).derivative.derivative.eval (((μ / τ : ℝ)) : ℂ)
        * ((τ⁻¹ : ℝ) : ℂ) ^ 2 := by
  have harg : ((τ⁻¹ : ℝ) : ℂ) * (μ : ℂ) = ((μ / τ : ℝ) : ℂ) := by
    push_cast
    field_simp
  simp only [scaledApprox_derivative2, Polynomial.eval_mul, Polynomial.eval_comp,
    Polynomial.eval_C, Polynomial.eval_X, harg]
  ring

/-- `‖Ψ_A'‖ ≤ ‖P'‖ + ‖P‖`。 -/
lemma norm_deriv_psiA_le (P : Polynomial ℂ) (μ : ℝ) :
    ‖deriv (fun x : ℝ => psiA P x) μ‖ ≤ ‖P.derivative.eval (μ : ℂ)‖ + ‖P.eval (μ : ℂ)‖ := by
  have hE : ‖Complex.exp ((μ : ℂ) * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp]
    have h : (((μ : ℂ) * Complex.I)).re = 0 := by simp [Complex.mul_re]
    rw [h, Real.exp_zero]
  have hI : ‖Complex.I‖ = 1 := Complex.norm_I
  rw [deriv_psiA, dpsiA]
  calc ‖-(P.derivative.eval (μ : ℂ) * Complex.exp ((μ : ℂ) * Complex.I)
        + P.eval (μ : ℂ) * (Complex.exp ((μ : ℂ) * Complex.I) * Complex.I))‖
      = ‖P.derivative.eval (μ : ℂ) * Complex.exp ((μ : ℂ) * Complex.I)
        + P.eval (μ : ℂ) * (Complex.exp ((μ : ℂ) * Complex.I) * Complex.I)‖ := norm_neg _
    _ ≤ ‖P.derivative.eval (μ : ℂ) * Complex.exp ((μ : ℂ) * Complex.I)‖
        + ‖P.eval (μ : ℂ) * (Complex.exp ((μ : ℂ) * Complex.I) * Complex.I)‖ := norm_add_le _ _
    _ = ‖P.derivative.eval (μ : ℂ)‖ + ‖P.eval (μ : ℂ)‖ := by
        rw [norm_mul, norm_mul, norm_mul, hE, hI]
        ring

/-- `‖Ψ_A''‖ ≤ ‖P''‖ + 2‖P'‖ + ‖P‖`。 -/
lemma norm_deriv2_psiA_le (P : Polynomial ℂ) (μ : ℝ) :
    ‖deriv (deriv (fun x : ℝ => psiA P x)) μ‖
      ≤ ‖P.derivative.derivative.eval (μ : ℂ)‖ + 2 * ‖P.derivative.eval (μ : ℂ)‖
        + ‖P.eval (μ : ℂ)‖ := by
  set F : ℝ → ℂ := fun x => P.eval (x : ℂ) with hF
  set G : ℝ → ℂ := fun x => Complex.exp ((x : ℂ) * Complex.I) with hG
  have hFd : Differentiable ℝ F := fun x => (hasDerivAt_poly_eval_real P x).differentiableAt
  have hGd : Differentiable ℝ G := fun x => (hasDerivAt_exp_mul_I x).differentiableAt
  have hdFfun : deriv F = fun x : ℝ => P.derivative.eval (x : ℂ) := by
    rw [hF]; exact funext fun x => deriv_poly_ofReal P x
  have hdGfun : deriv G = fun x : ℝ => Complex.exp ((x : ℂ) * Complex.I) * Complex.I := by
    rw [hG]; exact funext fun x => (hasDerivAt_exp_mul_I x).deriv
  have hF'd : Differentiable ℝ (deriv F) := by
    rw [hdFfun]; exact fun x => (hasDerivAt_poly_eval_real P.derivative x).differentiableAt
  have hG'd : Differentiable ℝ (deriv G) := by
    rw [hdGfun]
    exact fun x => ((hasDerivAt_exp_mul_I x).mul_const Complex.I).differentiableAt
  have hmul := deriv_deriv_mul F G hFd hGd hF'd hG'd μ
  have hdF : deriv F μ = P.derivative.eval (μ : ℂ) := deriv_poly_ofReal P μ
  have hdG : deriv G μ = Complex.exp ((μ : ℂ) * Complex.I) * Complex.I :=
    (hasDerivAt_exp_mul_I μ).deriv
  have hddF : deriv (deriv F) μ = P.derivative.derivative.eval (μ : ℂ) := deriv2_poly_ofReal P μ
  have hddG : deriv (deriv G) μ = -(Complex.exp ((μ : ℂ) * Complex.I)) := by
    rw [hdGfun, deriv_mul_const ((hasDerivAt_exp_mul_I μ).differentiableAt) Complex.I,
      (hasDerivAt_exp_mul_I μ).deriv, mul_assoc, Complex.I_mul_I]
    ring
  have hpsi : (fun x : ℝ => psiA P x) = fun x : ℝ => (1 : ℂ) - (F * G) x := by
    funext x
    rw [psiA, hF, hG]
    rfl
  have hkey : deriv (deriv (fun x : ℝ => psiA P x)) μ = -deriv (deriv (F * G)) μ := by
    rw [hpsi]
    have heq : (fun x : ℝ => (1 : ℂ) - (F * G) x) = (fun x : ℝ => -1 * (F * G) x + 1) := by
      funext x; ring
    rw [heq]
    have h2 : deriv (fun x : ℝ => -1 * (F * G) x + 1) = fun x : ℝ => -1 * deriv (F * G) x := by
      funext x
      rw [deriv_add_const, deriv_const_mul_field]
    rw [h2, deriv_const_mul_field]
    ring
  have hE : ‖Complex.exp ((μ : ℂ) * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp]
    have h : (((μ : ℂ) * Complex.I)).re = 0 := by simp [Complex.mul_re]
    rw [h, Real.exp_zero]
  have hI : ‖Complex.I‖ = 1 := Complex.norm_I
  have hdGnorm : ‖deriv G μ‖ = 1 := by rw [hdG, norm_mul, hE, hI, mul_one]
  have hddGnorm : ‖deriv (deriv G) μ‖ = 1 := by rw [hddG, norm_neg, hE]
  rw [hkey, norm_neg, hmul, hdF, hdG, hddF, hddG]
  calc ‖P.derivative.derivative.eval (μ : ℂ) * Complex.exp ((μ : ℂ) * Complex.I)
        + 2 * (P.derivative.eval (μ : ℂ) * (Complex.exp ((μ : ℂ) * Complex.I) * Complex.I))
        + P.eval (μ : ℂ) * -(Complex.exp ((μ : ℂ) * Complex.I))‖
      ≤ ‖P.derivative.derivative.eval (μ : ℂ) * Complex.exp ((μ : ℂ) * Complex.I)
          + 2 * (P.derivative.eval (μ : ℂ)
            * (Complex.exp ((μ : ℂ) * Complex.I) * Complex.I))‖
        + ‖P.eval (μ : ℂ) * -(Complex.exp ((μ : ℂ) * Complex.I))‖ := norm_add_le _ _
    _ ≤ (‖P.derivative.derivative.eval (μ : ℂ) * Complex.exp ((μ : ℂ) * Complex.I)‖
          + ‖2 * (P.derivative.eval (μ : ℂ)
            * (Complex.exp ((μ : ℂ) * Complex.I) * Complex.I))‖)
        + ‖P.eval (μ : ℂ) * -(Complex.exp ((μ : ℂ) * Complex.I))‖ := by
        have := norm_add_le (P.derivative.derivative.eval (μ : ℂ)
          * Complex.exp ((μ : ℂ) * Complex.I))
          (2 * (P.derivative.eval (μ : ℂ) * (Complex.exp ((μ : ℂ) * Complex.I) * Complex.I)))
        linarith
    _ = ‖P.derivative.derivative.eval (μ : ℂ)‖ + 2 * ‖P.derivative.eval (μ : ℂ)‖
        + ‖P.eval (μ : ℂ)‖ := by
        simp only [norm_mul, norm_neg, hE, hI, Complex.norm_ofNat, mul_one]

/-- **collar 上 `Ψ_A'` 的显式界**（`P = scaledApprox τ k`、`|μ| ≤ τ+B`）：
`M₁ = 2k³E/τ + 1 + 2kE`。 -/
lemma norm_deriv_psiA_scaled_collar_le (τ B : ℝ) (hτ : 0 < τ) (hB : 0 < B) (k : ℕ) {μ : ℝ}
    (hμ : |μ| ≤ τ + B) :
    ‖deriv (fun x : ℝ => psiA (scaledApprox τ k) x) μ‖
      ≤ 2 * (k : ℝ) ^ 3 * collarE τ B / τ + 1 + 2 * (k : ℝ) * collarE τ B := by
  refine (norm_deriv_psiA_le _ _).trans ?_
  have hμ' : |μ / τ| ≤ 1 + B / τ := by
    rw [abs_div, abs_of_pos hτ, div_le_iff₀ hτ]
    have hm := abs_le.mp hμ
    have hfac : (1 + B / τ) * τ = τ + B := by field_simp
    rw [hfac]
    exact abs_le.mpr hm
  have hE0 : (0 : ℝ) ≤ collarE τ B := (Real.exp_pos _).le
  have h1 : ‖(scaledApprox τ k).derivative.eval (μ : ℂ)‖ ≤ 2 * (k : ℝ) ^ 3 * collarE τ B / τ := by
    rw [scaledApprox_deriv_eval τ (ne_of_gt hτ) k μ, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h2 : ‖(approxPoly τ k).derivative.eval (((μ / τ : ℝ)) : ℂ)‖
        ≤ 2 * (k : ℝ) ^ 3 * collarE τ B := by
      rw [← deriv_poly_ofReal (approxPoly τ k) (μ / τ)]
      exact norm_deriv_approxPoly_le_collar_sharp τ B hτ hB k hμ'
    have h3 : |(τ⁻¹ : ℝ)| = τ⁻¹ := abs_of_pos (by positivity)
    rw [h3]
    calc ‖(approxPoly τ k).derivative.eval (((μ / τ : ℝ)) : ℂ)‖ * τ⁻¹
        ≤ (2 * (k : ℝ) ^ 3 * collarE τ B) * τ⁻¹ :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = 2 * (k : ℝ) ^ 3 * collarE τ B / τ := by rw [inv_eq_one_div]; ring
  have h4 : ‖(scaledApprox τ k).eval (μ : ℂ)‖ ≤ 1 + 2 * (k : ℝ) * collarE τ B := by
    rw [scaledApprox_eval τ (ne_of_gt hτ) k μ]
    exact norm_approxPoly_le_collar_sharp τ B hτ hB k hμ'
  linarith

/-- **collar 上 `Ψ_A''` 的显式界**（`P = scaledApprox τ k`、`|μ| ≤ τ+B`）：
`M₂ = 64k⁵E/τ² + 4k³E/τ + 1 + 2kE`（需 `B/τ ≤ 1/2`）。 -/
lemma norm_deriv2_psiA_scaled_collar_le (τ B : ℝ) (hτ : 0 < τ) (hB : 0 < B) (k : ℕ)
    (hBτ : B / τ ≤ 1 / 2) {μ : ℝ} (hμ : |μ| ≤ τ + B) :
    ‖deriv (deriv (fun x : ℝ => psiA (scaledApprox τ k) x)) μ‖
      ≤ 64 * (k : ℝ) ^ 5 * collarE τ B / τ ^ 2 + 4 * (k : ℝ) ^ 3 * collarE τ B / τ
        + (1 + 2 * (k : ℝ) * collarE τ B) := by
  have hμ' : |μ / τ| ≤ 1 + B / τ := by
    rw [abs_div, abs_of_pos hτ, div_le_iff₀ hτ]
    have hm := abs_le.mp hμ
    have hfac : (1 + B / τ) * τ = τ + B := by field_simp
    rw [hfac]
    exact abs_le.mpr hm
  have hE0 : (0 : ℝ) ≤ collarE τ B := (Real.exp_pos _).le
  have h1 : ‖(scaledApprox τ k).derivative.derivative.eval (μ : ℂ)‖
      ≤ 64 * (k : ℝ) ^ 5 * collarE τ B / τ ^ 2 := by
    rw [scaledApprox_deriv2_eval τ (ne_of_gt hτ) k μ, norm_mul]
    have h2 : ‖(approxPoly τ k).derivative.derivative.eval (((μ / τ : ℝ)) : ℂ)‖
        ≤ 64 * (k : ℝ) ^ 5 * collarE τ B := by
      rw [← deriv2_poly_ofReal (approxPoly τ k) (μ / τ)]
      exact norm_deriv2_approxPoly_le_collar_sharp τ B hτ hB k hBτ hμ'
    have h3 : ‖(((τ⁻¹ : ℝ) : ℂ)) ^ 2‖ = τ⁻¹ ^ 2 := by
      rw [← Complex.ofReal_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ τ⁻¹ ^ 2)]
    rw [h3]
    calc ‖(approxPoly τ k).derivative.derivative.eval (((μ / τ : ℝ)) : ℂ)‖ * τ⁻¹ ^ 2
        ≤ (64 * (k : ℝ) ^ 5 * collarE τ B) * τ⁻¹ ^ 2 :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = 64 * (k : ℝ) ^ 5 * collarE τ B / τ ^ 2 := by rw [inv_pow, inv_eq_one_div]; ring
  have h4 : ‖(scaledApprox τ k).derivative.eval (μ : ℂ)‖ ≤ 2 * (k : ℝ) ^ 3 * collarE τ B / τ := by
    rw [scaledApprox_deriv_eval τ (ne_of_gt hτ) k μ, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h2 : ‖(approxPoly τ k).derivative.eval (((μ / τ : ℝ)) : ℂ)‖
        ≤ 2 * (k : ℝ) ^ 3 * collarE τ B := by
      rw [← deriv_poly_ofReal (approxPoly τ k) (μ / τ)]
      exact norm_deriv_approxPoly_le_collar_sharp τ B hτ hB k hμ'
    have h3 : |(τ⁻¹ : ℝ)| = τ⁻¹ := abs_of_pos (by positivity)
    rw [h3]
    calc ‖(approxPoly τ k).derivative.eval (((μ / τ : ℝ)) : ℂ)‖ * τ⁻¹
        ≤ (2 * (k : ℝ) ^ 3 * collarE τ B) * τ⁻¹ :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = 2 * (k : ℝ) ^ 3 * collarE τ B / τ := by rw [inv_eq_one_div]; ring
  have h5 : ‖(scaledApprox τ k).eval (μ : ℂ)‖ ≤ 1 + 2 * (k : ℝ) * collarE τ B := by
    rw [scaledApprox_eval τ (ne_of_gt hτ) k μ]
    exact norm_approxPoly_le_collar_sharp τ B hτ hB k hμ'
  have h6 : 2 * ‖(scaledApprox τ k).derivative.eval (μ : ℂ)‖
      ≤ 4 * (k : ℝ) ^ 3 * collarE τ B / τ := by
    have h := mul_le_mul_of_nonneg_left h4 (by norm_num : (0 : ℝ) ≤ 2)
    calc 2 * ‖(scaledApprox τ k).derivative.eval (μ : ℂ)‖
        ≤ 2 * (2 * (k : ℝ) ^ 3 * collarE τ B / τ) := h
      _ = 4 * (k : ℝ) ^ 3 * collarE τ B / τ := by ring
  calc ‖deriv (deriv (fun x : ℝ => psiA (scaledApprox τ k) x)) μ‖
      ≤ ‖(scaledApprox τ k).derivative.derivative.eval (μ : ℂ)‖
        + 2 * ‖(scaledApprox τ k).derivative.eval (μ : ℂ)‖
        + ‖(scaledApprox τ k).eval (μ : ℂ)‖ := norm_deriv2_psiA_le _ _
    _ ≤ 64 * (k : ℝ) ^ 5 * collarE τ B / τ ^ 2 + 4 * (k : ℝ) ^ 3 * collarE τ B / τ
        + (1 + 2 * (k : ℝ) * collarE τ B) := add_le_add (add_le_add h1 h6) h5

/-- **`∫‖Ψ''‖` 的界（`M₂` 项用真支撑）**：与 `PsiBounds.integral_norm_deriv2_psi_le_sharp_gen`
逐字相同，只把第一项从 `2(τ+B+1)·M2` 缩到 `2(τ+B)·M2`（`‖Ψ_A''·χ‖` 的支撑是 `|μ| ≤ τ+B`）。
这一步在 `τ → 0` 时是关键：`(τ+B+1)` 会让 `C₁C₂` 的界带出 `1/τ` 而发散。 -/
lemma integral_norm_deriv2_psi_le_support (τ B : ℝ) (hτ : 0 < τ) (hB : 0 < B)
    (P : Polynomial ℂ) {ε M1 M2 L1 L2 : ℝ} (hε : 0 ≤ ε)
    (hPε : ∀ μ : ℝ, |μ| ≤ τ → ‖Complex.exp (-(μ : ℂ) * Complex.I) - P.eval ((μ : ℂ))‖ ≤ ε)
    (hA1 : ∀ μ : ℝ, |μ| ≤ τ + B → ‖deriv (fun x : ℝ => psiA P x) μ‖ ≤ M1)
    (hA2 : ∀ μ : ℝ, |μ| ≤ τ + B → ‖deriv (deriv (fun x : ℝ => psiA P x)) μ‖ ≤ M2)
    (hL1 : ∫ μ in (-(τ + B + 1))..(τ + B + 1),
      ‖deriv (fun x : ℝ => ((cutoff τ B x : ℝ) : ℂ)) μ‖ ≤ L1)
    (hL2 : ∫ μ in (-(τ + B + 1))..(τ + B + 1),
      ‖deriv (deriv (fun x : ℝ => ((cutoff τ B x : ℝ) : ℂ))) μ‖ ≤ L2) :
    ∫ μ in (-(τ + B + 1))..(τ + B + 1), ‖deriv (deriv (psi τ B P)) μ‖
      ≤ 2 * (τ + B) * M2 + 2 * (M1 * L1) + (ε + B * M1) * L2 := by
  have hM1nn : 0 ≤ M1 := le_trans (norm_nonneg _) (hA1 0 (by rw [abs_zero]; linarith))
  have hM2nn : 0 ≤ M2 := le_trans (norm_nonneg _) (hA2 0 (by rw [abs_zero]; linarith))
  have hεM1 : 0 ≤ ε + B * M1 := by linarith [mul_nonneg hB.le hM1nn]
  have hcontA : Continuous (fun z : ℝ => psiA P z) := (contDiffPsiA P).continuous
  have hcontA1 : Continuous (deriv (fun z : ℝ => psiA P z)) := by
    have h2 : ContDiff ℝ ((1 : WithTop ℕ∞) + 1) (fun z : ℝ => psiA P z) :=
      (contDiffPsiA P).of_le (m := (1 : WithTop ℕ∞) + 1) le_top
    exact h2.deriv'.continuous
  have hcontA2 : Continuous (deriv (deriv (fun z : ℝ => psiA P z))) := by
    have h2 : ContDiff ℝ ((1 : WithTop ℕ∞) + 1) (fun z : ℝ => psiA P z) :=
      (contDiffPsiA P).of_le (m := (1 : WithTop ℕ∞) + 1) le_top
    exact h2.deriv'.continuous_deriv le_rfl
  have hcontK : Continuous (fun z : ℝ => ((cutoff τ B z : ℝ) : ℂ)) :=
    (contDiff_coe_cutoff τ B hτ hB).continuous
  have hcontK1 : Continuous (deriv (fun z : ℝ => ((cutoff τ B z : ℝ) : ℂ))) := by
    rw [deriv_coe_cutoff τ B hτ hB]
    exact Complex.continuous_ofReal.comp
      ((contDiff_cutoff τ B hτ hB).continuous_deriv (by norm_num))
  have hcontK2 : Continuous (deriv (deriv (fun z : ℝ => ((cutoff τ B z : ℝ) : ℂ)))) := by
    rw [deriv_deriv_coe_cutoff τ B hτ hB]
    refine Complex.continuous_ofReal.comp ?_
    have h2 : ContDiff ℝ ((1 : WithTop ℕ∞) + 1) (cutoff τ B) := by
      rw [show ((1 : WithTop ℕ∞) + 1) = 2 from by norm_num]
      exact contDiff_cutoff τ B hτ hB
    exact h2.deriv'.continuous_deriv le_rfl
  have hcontψ2 : Continuous (deriv (deriv (psi τ B P))) := continuous_deriv2_psi τ B hτ hB P
  set G1 : ℝ → ℝ := fun μ => ‖deriv (deriv (fun z : ℝ => psiA P z)) μ * ((cutoff τ B μ : ℝ) : ℂ)‖
    with hG1
  set G2 : ℝ → ℝ := fun μ => ‖2 * (deriv (fun z : ℝ => psiA P z) μ
    * deriv (fun z : ℝ => ((cutoff τ B z : ℝ) : ℂ)) μ)‖ with hG2
  set G3 : ℝ → ℝ := fun μ => ‖psiA P μ
    * deriv (deriv (fun z : ℝ => ((cutoff τ B z : ℝ) : ℂ))) μ‖ with hG3
  have hcontG1 : Continuous G1 := by
    rw [hG1]
    exact (hcontA2.mul hcontK).norm
  have hcontG2 : Continuous G2 := by
    rw [hG2]
    exact (continuous_const.mul (hcontA1.mul hcontK1)).norm
  have hcontG3 : Continuous G3 := by
    rw [hG3]
    exact (hcontA.mul hcontK2).norm
  have hK0 : ∀ μ : ℝ, ‖((cutoff τ B μ : ℝ) : ℂ)‖ ≤ 1 := by
    intro μ
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (cutoff_nonneg τ B μ)]
    exact cutoff_le_one τ B μ
  have hb1 : ∀ μ : ℝ, G1 μ ≤ M2 := by
    intro μ
    simp only [hG1]
    rcases le_or_gt |μ| (τ + B) with h | h
    · rw [norm_mul]
      simpa using mul_le_mul (hA2 μ h) (hK0 μ) (norm_nonneg _) hM2nn
    · have hz : ((cutoff τ B μ : ℝ) : ℂ) = 0 := by
        rw [cutoff_eq_zero hB (le_of_lt h), Complex.ofReal_zero]
      rw [hz, mul_zero, norm_zero]
      exact hM2nn
  have hb2 : ∀ μ : ℝ, G2 μ
      ≤ 2 * (M1 * ‖deriv (fun z : ℝ => ((cutoff τ B z : ℝ) : ℂ)) μ‖) := by
    intro μ
    simp only [hG2]
    rw [norm_mul, Complex.norm_ofNat, norm_mul]
    rcases le_or_gt |μ| (τ + B) with h | h
    · have hmul : ‖deriv (fun z : ℝ => psiA P z) μ‖
          * ‖deriv (fun z : ℝ => ((cutoff τ B z : ℝ) : ℂ)) μ‖
          ≤ M1 * ‖deriv (fun z : ℝ => ((cutoff τ B z : ℝ) : ℂ)) μ‖ :=
        mul_le_mul (hA1 μ h) le_rfl (norm_nonneg _) hM1nn
      linarith
    · have hz : deriv (fun z : ℝ => ((cutoff τ B z : ℝ) : ℂ)) μ = 0 := by
        rw [deriv_coe_cutoff τ B hτ hB]
        simp only [deriv_cutoff_eq_zero_of_lt_abs hB h, Complex.ofReal_zero]
      rw [hz]
      simp
  have hb3 : ∀ μ : ℝ, G3 μ ≤ (ε + B * M1)
      * ‖deriv (deriv (fun z : ℝ => ((cutoff τ B z : ℝ) : ℂ))) μ‖ := by
    intro μ
    simp only [hG3]
    rw [norm_mul]
    rcases le_or_gt |μ| (τ + B) with h | h
    · exact mul_le_mul (norm_psiA_le τ B hτ.le hB P hPε hA1 μ h) le_rfl (norm_nonneg _) hεM1
    · have hz : deriv (deriv (fun z : ℝ => ((cutoff τ B z : ℝ) : ℂ))) μ = 0 := by
        rw [deriv_deriv_coe_cutoff τ B hτ hB]
        simp only [deriv_deriv_cutoff_eq_zero_of_lt_abs hB h, Complex.ofReal_zero]
      rw [hz]
      simp
  have I1 : ∫ μ in (-(τ + B + 1))..(τ + B + 1), G1 μ ≤ 2 * (τ + B) * M2 := by
    have hmain := intervalIntegral_le_two_mul_mul_of_support (τ := 0) (B := τ + B) (C := M2)
      (le_refl 0) (by linarith) hcontG1 hb1 (fun μ => norm_nonneg _)
      (fun μ hμ => absurd hμ (not_lt.mpr (abs_nonneg μ)))
      (fun μ hμ => by
        have hz : ((cutoff τ B μ : ℝ) : ℂ) = 0 := by
          rw [cutoff_eq_zero hB (le_of_lt (by simpa using hμ)), Complex.ofReal_zero]
        simp only [hG1, hz, mul_zero, norm_zero])
    simpa using hmain
  have I2 : ∫ μ in (-(τ + B + 1))..(τ + B + 1), G2 μ ≤ 2 * (M1 * L1) := by
    have hmaj : Continuous (fun μ : ℝ => 2 * (M1
        * ‖deriv (fun z : ℝ => ((cutoff τ B z : ℝ) : ℂ)) μ‖)) :=
      (hcontK1.norm.const_mul M1).const_mul 2
    have hmono : ∫ μ in (-(τ + B + 1))..(τ + B + 1), G2 μ
        ≤ ∫ μ in (-(τ + B + 1))..(τ + B + 1), (fun μ : ℝ => 2 * (M1
            * ‖deriv (fun z : ℝ => ((cutoff τ B z : ℝ) : ℂ)) μ‖)) μ :=
      intervalIntegral.integral_mono (by linarith) (hcontG2.intervalIntegrable _ _)
        (hmaj.intervalIntegrable _ _) (fun μ => hb2 μ)
    have heq : ∫ μ in (-(τ + B + 1))..(τ + B + 1), (fun μ : ℝ => 2 * (M1
            * ‖deriv (fun z : ℝ => ((cutoff τ B z : ℝ) : ℂ)) μ‖)) μ
        = 2 * (M1 * ∫ μ in (-(τ + B + 1))..(τ + B + 1),
            ‖deriv (fun z : ℝ => ((cutoff τ B z : ℝ) : ℂ)) μ‖) := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    refine le_trans (le_trans hmono (le_of_eq heq)) ?_
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hL1 hM1nn)
      (by norm_num : (0 : ℝ) ≤ 2)
  have I3 : ∫ μ in (-(τ + B + 1))..(τ + B + 1), G3 μ ≤ (ε + B * M1) * L2 := by
    have hmaj : Continuous (fun μ : ℝ => (ε + B * M1)
        * ‖deriv (deriv (fun z : ℝ => ((cutoff τ B z : ℝ) : ℂ))) μ‖) :=
      hcontK2.norm.const_mul (ε + B * M1)
    have hmono : ∫ μ in (-(τ + B + 1))..(τ + B + 1), G3 μ
        ≤ ∫ μ in (-(τ + B + 1))..(τ + B + 1), (fun μ : ℝ => (ε + B * M1)
            * ‖deriv (deriv (fun z : ℝ => ((cutoff τ B z : ℝ) : ℂ))) μ‖) μ :=
      intervalIntegral.integral_mono (by linarith) (hcontG3.intervalIntegrable _ _)
        (hmaj.intervalIntegrable _ _) (fun μ => hb3 μ)
    have heq : ∫ μ in (-(τ + B + 1))..(τ + B + 1), (fun μ : ℝ => (ε + B * M1)
            * ‖deriv (deriv (fun z : ℝ => ((cutoff τ B z : ℝ) : ℂ))) μ‖) μ
        = (ε + B * M1) * ∫ μ in (-(τ + B + 1))..(τ + B + 1),
            ‖deriv (deriv (fun z : ℝ => ((cutoff τ B z : ℝ) : ℂ))) μ‖ := by
      rw [intervalIntegral.integral_const_mul]
    exact le_trans (le_trans hmono (le_of_eq heq))
      (mul_le_mul_of_nonneg_left hL2 hεM1)
  have hpoint : ∀ μ : ℝ, ‖deriv (deriv (psi τ B P)) μ‖ ≤ G1 μ + G2 μ + G3 μ := by
    intro μ
    rw [deriv2_psi_eq τ B hτ hB P μ]
    simp only [hG1, hG2, hG3]
    have h12 := norm_add_le
      (deriv (deriv (fun z : ℝ => psiA P z)) μ * ((cutoff τ B μ : ℝ) : ℂ))
      (2 * (deriv (fun z : ℝ => psiA P z) μ
        * deriv (fun z : ℝ => ((cutoff τ B z : ℝ) : ℂ)) μ))
    have h3 := norm_add_le
      (deriv (deriv (fun z : ℝ => psiA P z)) μ * ((cutoff τ B μ : ℝ) : ℂ)
        + 2 * (deriv (fun z : ℝ => psiA P z) μ
          * deriv (fun z : ℝ => ((cutoff τ B z : ℝ) : ℂ)) μ))
      (psiA P μ * deriv (deriv (fun z : ℝ => ((cutoff τ B z : ℝ) : ℂ))) μ)
    linarith
  have hmono : ∫ μ in (-(τ + B + 1))..(τ + B + 1), ‖deriv (deriv (psi τ B P)) μ‖
      ≤ ∫ μ in (-(τ + B + 1))..(τ + B + 1), (G1 μ + G2 μ + G3 μ) :=
    intervalIntegral.integral_mono (by linarith) (hcontψ2.norm.intervalIntegrable _ _)
      (((hcontG1.add hcontG2).add hcontG3).intervalIntegrable _ _) (fun μ => hpoint μ)
  have hsplit : ∫ μ in (-(τ + B + 1))..(τ + B + 1), (G1 μ + G2 μ + G3 μ)
      = (∫ μ in (-(τ + B + 1))..(τ + B + 1), G1 μ)
        + (∫ μ in (-(τ + B + 1))..(τ + B + 1), G2 μ)
        + ∫ μ in (-(τ + B + 1))..(τ + B + 1), G3 μ := by
    rw [intervalIntegral.integral_add (f := fun μ : ℝ => G1 μ + G2 μ) (g := G3)
        ((hcontG1.add hcontG2).intervalIntegrable _ _) (hcontG3.intervalIntegrable _ _),
      intervalIntegral.integral_add (f := G1) (g := G2)
        (hcontG1.intervalIntegrable _ _) (hcontG2.intervalIntegrable _ _)]
  calc ∫ μ in (-(τ + B + 1))..(τ + B + 1), ‖deriv (deriv (psi τ B P)) μ‖
      ≤ ∫ μ in (-(τ + B + 1))..(τ + B + 1), (G1 μ + G2 μ + G3 μ) := hmono
    _ = (∫ μ in (-(τ + B + 1))..(τ + B + 1), G1 μ)
        + (∫ μ in (-(τ + B + 1))..(τ + B + 1), G2 μ)
        + ∫ μ in (-(τ + B + 1))..(τ + B + 1), G3 μ := hsplit
    _ ≤ 2 * (τ + B) * M2 + 2 * (M1 * L1) + (ε + B * M1) * L2 := by
        linarith [I1, I2, I3]


/-! ## §5 锐化的核常数界（支撑感知 + 与 `τ` 无关的截断常数） -/

/-- `cutoff` 的**尺度不变性**：`cutoff τ B μ = cutoff 1 (B/τ) (μ/τ)`（`τ > 0`）。 -/
lemma cutoff_scale (τ B μ : ℝ) (hτ : 0 < τ) :
    cutoff τ B μ = cutoff 1 (B / τ) (μ / τ) := by
  rw [cutoff, cutoff, abs_div, abs_of_pos hτ]
  congr 1
  field_simp

/-- **与 `τ` 无关的截断常数**：存在绝对常数 `K > 0`，使得对**一切** `τ, B > 0`
`|χ'| ≤ K/B`、`|χ''| ≤ K/B²`。

（`CutoffDeriv.exists_deriv_cutoff_bound` 给出的 `K` 形式上依赖 `τ`；这里用尺度不变性
`cutoff τ B μ = cutoff 1 (B/τ) (μ/τ)` 把它降到 `τ = 1` 的一个绝对常数。） -/
lemma exists_deriv_cutoff_bound_uniform :
    ∃ K : ℝ, 0 < K ∧ ∀ (τ B : ℝ), 0 < τ → 0 < B →
      (∀ μ : ℝ, |deriv (cutoff τ B) μ| ≤ K / B) ∧
      (∀ μ : ℝ, |deriv (deriv (cutoff τ B)) μ| ≤ K / B ^ 2) := by
  obtain ⟨K, hK0, hK⟩ := exists_deriv_cutoff_bound 1 one_pos
  refine ⟨K, hK0, fun τ B hτ hB => ?_⟩
  have hB' : 0 < B / τ := div_pos hB hτ
  obtain ⟨hK1, hK2⟩ := hK (B / τ) hB'
  have hdiff : Differentiable ℝ (cutoff 1 (B / τ)) :=
    (contDiff_cutoff 1 (B / τ) one_pos hB').differentiable (by norm_num)
  have hscale : ∀ μ : ℝ, cutoff τ B μ = cutoff 1 (B / τ) (μ / τ) := fun μ => cutoff_scale τ B μ hτ
  constructor
  · intro μ
    have h1 : deriv (cutoff τ B) μ
        = deriv (cutoff 1 (B / τ)) (μ / τ) * (1 / τ) := by
      have hev : cutoff τ B =ᶠ[nhds μ] fun y : ℝ => cutoff 1 (B / τ) (y / τ) :=
        Eventually.of_forall fun y => hscale y
      rw [hev.deriv_eq]
      have h2 : deriv (fun y : ℝ => cutoff 1 (B / τ) (y / τ)) μ
          = deriv (cutoff 1 (B / τ)) (μ / τ) * deriv (fun y : ℝ => y / τ) μ :=
        deriv_comp μ (hdiff.differentiableAt) (by fun_prop)
      rw [h2, deriv_div_const, deriv_id'']
    rw [h1, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / τ)]
    calc |deriv (cutoff 1 (B / τ)) (μ / τ)| * (1 / τ)
        ≤ (K / (B / τ)) * (1 / τ) := mul_le_mul_of_nonneg_right (hK1 (μ / τ)) (by positivity)
      _ = K / B := by field_simp
  · intro μ
    have h1 : deriv (deriv (cutoff τ B)) μ
        = deriv (deriv (cutoff 1 (B / τ))) (μ / τ) * ((1 / τ) * (1 / τ)) := by
      have hpt : deriv (cutoff τ B)
          = fun y : ℝ => deriv (cutoff 1 (B / τ)) (y / τ) * (1 / τ) := by
        funext y
        have hev : cutoff τ B =ᶠ[nhds y] fun z : ℝ => cutoff 1 (B / τ) (z / τ) :=
          Eventually.of_forall fun z => hscale z
        rw [hev.deriv_eq]
        have h2 : deriv (fun z : ℝ => cutoff 1 (B / τ) (z / τ)) y
            = deriv (cutoff 1 (B / τ)) (y / τ) * deriv (fun z : ℝ => z / τ) y :=
          deriv_comp y (hdiff.differentiableAt) (by fun_prop)
        rw [h2, deriv_div_const, deriv_id'']
      rw [hpt]
      have hd : Differentiable ℝ (deriv (cutoff 1 (B / τ))) :=
        ContDiff.differentiable_deriv_two (contDiff_cutoff 1 (B / τ) one_pos hB')
      have hd' : DifferentiableAt ℝ (fun y : ℝ => deriv (cutoff 1 (B / τ)) (y / τ)) μ :=
        hd.differentiableAt.comp μ (by fun_prop)
      have h2 : deriv (fun y : ℝ => deriv (cutoff 1 (B / τ)) (y / τ) * (1 / τ)) μ
          = deriv (fun y : ℝ => deriv (cutoff 1 (B / τ)) (y / τ)) μ * (1 / τ) :=
        deriv_mul_const hd' _
      rw [h2]
      have h3 : deriv (fun y : ℝ => deriv (cutoff 1 (B / τ)) (y / τ)) μ
          = deriv (deriv (cutoff 1 (B / τ))) (μ / τ) * (1 / τ) := by
        have h4 : deriv (fun y : ℝ => deriv (cutoff 1 (B / τ)) (y / τ)) μ
            = deriv (deriv (cutoff 1 (B / τ))) (μ / τ)
              * deriv (fun y : ℝ => y / τ) μ := by
          simpa only [Function.comp_def] using deriv_comp μ (hd.differentiableAt) (by fun_prop)
        rw [h4, deriv_div_const, deriv_id'']
      rw [h3]
      ring
    rw [h1, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 / τ) * (1 / τ))]
    calc |deriv (deriv (cutoff 1 (B / τ))) (μ / τ)| * ((1 / τ) * (1 / τ))
        ≤ (K / (B / τ) ^ 2) * ((1 / τ) * (1 / τ)) :=
          mul_le_mul_of_nonneg_right (hK2 (μ / τ)) (by positivity)
      _ = K / B ^ 2 := by field_simp

/-- **`C₁` 的支撑感知界**：`kernelA τ B P ≤ (2π)⁻¹·2(τ+B)·S`
（`‖Ψ‖ ≤ S` 且 `Ψ` 的支撑是 `|μ| ≤ τ+B`）。 -/
lemma kernelA_le_support {τ B : ℝ} (hτ : 0 < τ) (hB : 0 < B) (P : Polynomial ℂ) {S : ℝ}
    (hψ : ∀ μ : ℝ, ‖psi τ B P μ‖ ≤ S) :
    kernelA τ B P ≤ (2 * Real.pi)⁻¹ * (2 * (τ + B)) * S := by
  rw [kernelA]
  have hcont : Continuous (fun μ : ℝ => ‖psi τ B P μ‖) :=
    ((contDiffPsi τ B hτ hB P).continuous).norm
  have hmain := intervalIntegral_le_two_mul_mul_of_support (τ := 0) (B := τ + B) (C := S)
    (le_refl 0) (by linarith) hcont (fun μ => hψ μ) (fun μ => norm_nonneg _)
    (fun μ hμ => absurd hμ (not_lt.mpr (abs_nonneg μ)))
    (fun μ hμ => by
      rw [psi_eq_zero P hB (le_of_lt (by simpa using hμ)), norm_zero])
  have hmain' : ∫ μ in (-(τ + B + 1))..(τ + B + 1), ‖psi τ B P μ‖ ≤ 2 * (τ + B) * S := by
    simpa only [zero_add, Function.comp_apply] using hmain
  calc (2 * Real.pi)⁻¹ * ∫ μ in (-(τ + B + 1))..(τ + B + 1), ‖psi τ B P μ‖
      ≤ (2 * Real.pi)⁻¹ * (2 * (τ + B) * S) :=
        mul_le_mul_of_nonneg_left hmain' (by positivity)
    _ = (2 * Real.pi)⁻¹ * (2 * (τ + B)) * S := by ring

/-- **`C₂` 的支撑感知界（`K` 形式）**：
`kernelC τ B P ≤ (2π)⁻¹·(2(τ+B)·M₂ + 2·M₁·(2K) + (ε+B·M₁)·(4K/B))`。 -/
lemma kernelC_le_support {τ B : ℝ} (hτ : 0 < τ) (hB : 0 < B) (P : Polynomial ℂ)
    {ε M₁ M₂ K : ℝ} (hε : 0 ≤ ε)
    (hPε : ∀ μ : ℝ, |μ| ≤ τ →
      ‖Complex.exp (-(μ : ℂ) * Complex.I) - P.eval ((μ : ℂ))‖ ≤ ε)
    (hA1 : ∀ μ : ℝ, |μ| ≤ τ + B → ‖deriv (fun x : ℝ => psiA P x) μ‖ ≤ M₁)
    (hA2 : ∀ μ : ℝ, |μ| ≤ τ + B → ‖deriv (deriv (fun x : ℝ => psiA P x)) μ‖ ≤ M₂)
    (hK1 : ∀ μ : ℝ, ‖deriv (fun x : ℝ => ((cutoff τ B x : ℝ) : ℂ)) μ‖ ≤ K / B)
    (hK2 : ∀ μ : ℝ, ‖deriv (deriv (fun x : ℝ => ((cutoff τ B x : ℝ) : ℂ))) μ‖ ≤ K / B ^ 2) :
    kernelC τ B P ≤ (2 * Real.pi)⁻¹ *
      (2 * (τ + B) * M₂ + 2 * (M₁ * (2 * K)) + (ε + B * M₁) * (4 * K / B)) := by
  rw [kernelC]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hK1' : ∀ μ : ℝ, |deriv (cutoff τ B) μ| ≤ K / B := by
    intro μ
    have h := hK1 μ
    rwa [deriv_coe_cutoff τ B hτ hB, Complex.norm_real, Real.norm_eq_abs] at h
  have hK2' : ∀ μ : ℝ, |deriv (deriv (cutoff τ B)) μ| ≤ K / B ^ 2 := by
    intro μ
    have h := hK2 μ
    rwa [deriv_deriv_coe_cutoff τ B hτ hB, Complex.norm_real, Real.norm_eq_abs] at h
  have hL1 : ∫ μ in (-(τ + B + 1))..(τ + B + 1),
      ‖deriv (fun x : ℝ => ((cutoff τ B x : ℝ) : ℂ)) μ‖ ≤ 2 * K :=
    integral_norm_deriv_cutoff_le τ B hτ hB hK1'
  have hL2 : ∫ μ in (-(τ + B + 1))..(τ + B + 1),
      ‖deriv (deriv (fun x : ℝ => ((cutoff τ B x : ℝ) : ℂ))) μ‖ ≤ 4 * K / B :=
    integral_norm_deriv2_cutoff_le τ B hτ hB hK2'
  exact integral_norm_deriv2_psi_le_support τ B hτ hB P hε hPε hA1 hA2 hL1 hL2

/-! ## §6 组装：`C₁C₂` 的多项式界 → `ε` 的指数衰减 → 端点小性 -/

/-- **算术核心**：把 `C₁`、`C₂` 的支撑感知界与 `M₁`、`M₂` 的显式界相乘。

`B = ετ/q²` 时 `B·M₁ ≤ 9εq`、`τ²M₂ ≤ 141q⁵`、`ε/B = q²/τ`；`C₁` 里的 `2(τ+B) ≍ 2τ`
正好把 `C₂` 里 `M₂` 的 `1/τ²`、`ε/B` 的 `1/τ` 全部抵消，最终只剩**一次** `ε`：
`C₁C₂ ≤ 3000(1+K)·ε·q⁸`。 -/
lemma kernelProd_le_poly {τ B ε M₁ M₂ K : ℝ} {k : ℕ} {q : ℝ} (P : Polynomial ℂ)
    (hτ : 0 < τ) (hB : 0 < B) (hε : 0 ≤ ε) (hK : 0 ≤ K)
    (hM₁nn : 0 ≤ M₁) (hM₂nn : 0 ≤ M₂)
    (hq1 : 1 ≤ q) (hkq : (k : ℝ) ≤ q) (hτq : τ ≤ q) (hBτ : B ≤ τ)
    (hBval : B = ε * τ / q ^ 2)
    (hM1 : τ * M₁ ≤ 4 * (k : ℝ) ^ 3 + τ + 4 * (k : ℝ) * τ)
    (hM2 : τ ^ 2 * M₂ ≤ 128 * (k : ℝ) ^ 5 + 8 * (k : ℝ) ^ 3 * τ + τ ^ 2
      + 4 * (k : ℝ) * τ ^ 2)
    (hψ : ∀ μ : ℝ, ‖psi τ B P μ‖ ≤ ε + B * M₁)
    (hPε : ∀ μ : ℝ, |μ| ≤ τ →
      ‖Complex.exp (-(μ : ℂ) * Complex.I) - P.eval ((μ : ℂ))‖ ≤ ε)
    (hA1 : ∀ μ : ℝ, |μ| ≤ τ + B → ‖deriv (fun x : ℝ => psiA P x) μ‖ ≤ M₁)
    (hA2 : ∀ μ : ℝ, |μ| ≤ τ + B → ‖deriv (deriv (fun x : ℝ => psiA P x)) μ‖ ≤ M₂)
    (hK1 : ∀ μ : ℝ, ‖deriv (fun x : ℝ => ((cutoff τ B x : ℝ) : ℂ)) μ‖ ≤ K / B)
    (hK2 : ∀ μ : ℝ, ‖deriv (deriv (fun x : ℝ => ((cutoff τ B x : ℝ) : ℂ))) μ‖ ≤ K / B ^ 2) :
    kernelA τ B P * kernelC τ B P ≤ 3000 * (1 + K) * ε * q ^ 8 := by
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le one_pos hq1
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := by positivity
  have hεpos : 0 < ε := by
    rcases lt_or_eq_of_le hε with h | h
    · exact h
    · exfalso
      rw [← h, zero_mul, zero_div] at hBval
      rw [hBval] at hB
      exact lt_irrefl 0 hB
  have hεB : ε / B = q ^ 2 / τ := by
    rw [hBval]
    field_simp
  -- ### 小工具：`τ * M₁ ≤ 9q³`、`B * M₁ ≤ 9εq`
  have hk3 : (k : ℝ) ^ 3 ≤ q ^ 3 := pow_le_pow_left₀ hk0 hkq 3
  have hk5 : (k : ℝ) ^ 5 ≤ q ^ 5 := pow_le_pow_left₀ hk0 hkq 5
  have hkτ : (k : ℝ) * τ ≤ q * q := mul_le_mul hkq hτq hτ.le hq0.le
  have hττ : τ * τ ≤ q * q := mul_le_mul hτq hτq hτ.le hq0.le
  have hτM₁ : τ * M₁ ≤ 9 * q ^ 3 := by
    have h4 : (4 : ℝ) * (k : ℝ) ^ 3 ≤ 4 * q ^ 3 := by linarith
    have h5 : (4 : ℝ) * ((k : ℝ) * τ) ≤ 4 * (q * q) := by linarith
    have h6 : (4 : ℝ) * (k : ℝ) * τ = 4 * ((k : ℝ) * τ) := by ring
    have h7 : (4 : ℝ) * q * q = 4 * (q * q) := by ring
    have h8 : (4 : ℝ) * q ^ 3 + q + 4 * (q * q) ≤ 9 * q ^ 3 := by nlinarith [hq1]
    have hM1' : τ * M₁ ≤ 4 * (k : ℝ) ^ 3 + τ + 4 * ((k : ℝ) * τ) := by
      rw [← h6]; exact hM1
    have h9 : (4 : ℝ) * q * q = 4 * (q * q) := h7
    linarith [hM1', h4, h5, h8, hτq]
  have hBM : B * M₁ = (ε / q ^ 2) * (τ * M₁) := by
    rw [hBval]
    field_simp
  have hBMle : B * M₁ ≤ 9 * ε * q := by
    have h1 : (ε / q ^ 2) * (τ * M₁) ≤ (ε / q ^ 2) * (9 * q ^ 3) :=
      mul_le_mul_of_nonneg_left hτM₁ (by positivity)
    have h2 : (ε / q ^ 2) * (9 * q ^ 3) = 9 * ε * q := by field_simp
    linarith [hBM ▸ h1, h2]
  have hSle : ε + B * M₁ ≤ 10 * ε * q := by
    nlinarith [hBMle, hε, hq1]
  -- ### `C₁`
  have hC1 : kernelA τ B P ≤ (2 * Real.pi)⁻¹ * (40 * ε * q * τ) := by
    refine (kernelA_le_support hτ hB P hψ).trans ?_
    have hcoef : (0 : ℝ) < (2 * Real.pi)⁻¹ := by positivity
    have h1 : 2 * (τ + B) ≤ 4 * τ := by linarith
    have h3 : 0 ≤ ε + B * M₁ := by linarith [hε, mul_nonneg hB.le hM₁nn]
    have h4 : (0 : ℝ) ≤ (2 * Real.pi)⁻¹ * (4 * τ) := by positivity
    have h5 : (2 * Real.pi)⁻¹ * (2 * (τ + B)) ≤ (2 * Real.pi)⁻¹ * (4 * τ) :=
      mul_le_mul_of_nonneg_left h1 hcoef.le
    have h6 := mul_le_mul h5 hSle h3 h4
    calc (2 * Real.pi)⁻¹ * (2 * (τ + B)) * (ε + B * M₁)
        ≤ (2 * Real.pi)⁻¹ * (4 * τ) * (10 * ε * q) := h6
      _ = (2 * Real.pi)⁻¹ * (40 * ε * q * τ) := by ring
  -- ### `C₂`
  have hC2 : kernelC τ B P ≤ (2 * Real.pi)⁻¹ * (4 * τ * M₂ + 8 * K * M₁ + 4 * K * q ^ 2 / τ) := by
    refine (kernelC_le_support hτ hB P hε hPε hA1 hA2 hK1 hK2).trans ?_
    have hcoef : (0 : ℝ) < (2 * Real.pi)⁻¹ := by positivity
    have h1 : 2 * (τ + B) * M₂ ≤ 4 * τ * M₂ := by nlinarith [hBτ, hM₂nn, hτ]
    have h2 : 2 * (M₁ * (2 * K)) ≤ 8 * K * M₁ := by nlinarith [hM₁nn, hK]
    have h3 : (ε + B * M₁) * (4 * K / B) ≤ 4 * K * q ^ 2 / τ + 4 * K * M₁ := by
      have h4 : (ε + B * M₁) * (4 * K / B) = ε * (4 * K / B) + B * M₁ * (4 * K / B) := by ring
      have h5 : ε * (4 * K / B) = 4 * K * (ε / B) := by ring
      have h6 : B * M₁ * (4 * K / B) = 4 * K * M₁ := by
        field_simp
      have h7 : 4 * K * q ^ 2 / τ = 4 * K * (q ^ 2 / τ) := by ring
      rw [h4, h5, hεB, h6, h7]
    have hsum : 2 * (τ + B) * M₂ + 2 * (M₁ * (2 * K)) + (ε + B * M₁) * (4 * K / B)
        ≤ 4 * τ * M₂ + 8 * K * M₁ + 4 * K * q ^ 2 / τ := by linarith [h1, h2, h3]
    exact mul_le_mul_of_nonneg_left hsum hcoef.le
  -- ### 相乘
  have hbr : (0 : ℝ) ≤ 4 * τ * M₂ + 8 * K * M₁ + 4 * K * q ^ 2 / τ := by positivity
  have hC2nn : 0 ≤ kernelC τ B P := kernelC_nonneg hτ hB P
  have hC1rhs : 0 ≤ (2 * Real.pi)⁻¹ * (40 * ε * q * τ) :=
    mul_nonneg (by positivity) (by positivity)
  have hprod : kernelA τ B P * kernelC τ B P
      ≤ (2 * Real.pi)⁻¹ * (40 * ε * q * τ) * ((2 * Real.pi)⁻¹ * (4 * τ * M₂ + 8 * K * M₁ + 4 * K * q ^ 2 / τ)) :=
    mul_le_mul hC1 hC2 hC2nn hC1rhs
  refine hprod.trans ?_
  -- ### 展开与收尾
  have hstep1 : (2 * Real.pi)⁻¹ * (40 * ε * q * τ)
        * ((2 * Real.pi)⁻¹ * (4 * τ * M₂ + 8 * K * M₁ + 4 * K * q ^ 2 / τ))
      = (2 * Real.pi)⁻¹ * (2 * Real.pi)⁻¹
        * ((40 * ε * q * τ) * (4 * τ * M₂ + 8 * K * M₁ + 4 * K * q ^ 2 / τ)) := by ring
  have hstep2 : (40 * ε * q * τ) * (4 * τ * M₂ + 8 * K * M₁ + 4 * K * q ^ 2 / τ)
      = 160 * ε * q * (τ ^ 2 * M₂) + 320 * K * ε * q * (τ * M₁) + 160 * K * ε * q ^ 3 := by
    field_simp
    ring
  rw [hstep1, hstep2]
  have hcoef : (2 * Real.pi)⁻¹ * (2 * Real.pi)⁻¹ ≤ 1 / 36 := by
    have hpi : (6 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
    have h1 : (2 * Real.pi)⁻¹ ≤ (6 : ℝ)⁻¹ := by
      rw [inv_le_inv₀ (by positivity : (0 : ℝ) < 2 * Real.pi) (by norm_num : (0 : ℝ) < 6)]
      exact hpi
    calc (2 * Real.pi)⁻¹ * (2 * Real.pi)⁻¹ ≤ (6 : ℝ)⁻¹ * (6 : ℝ)⁻¹ :=
          mul_le_mul h1 h1 (by positivity) (by positivity)
      _ = 1 / 36 := by norm_num
  have hτ2M₂ : τ ^ 2 * M₂ ≤ 141 * q ^ 5 := by
    have h1a : (k : ℝ) ^ 3 * τ ≤ q ^ 3 * q :=
      mul_le_mul hk3 hτq hτ.le (by positivity : (0 : ℝ) ≤ q ^ 3)
    have h1 : 8 * (k : ℝ) ^ 3 * τ ≤ 8 * q ^ 4 := by
      calc 8 * (k : ℝ) ^ 3 * τ = 8 * ((k : ℝ) ^ 3 * τ) := by ring
        _ ≤ 8 * (q ^ 3 * q) := by linarith [h1a]
        _ = 8 * q ^ 4 := by ring
    have h2a : ((k : ℝ) * τ) * τ ≤ (q * q) * q :=
      mul_le_mul hkτ hτq hτ.le (by positivity : (0 : ℝ) ≤ q * q)
    have h2 : 4 * (k : ℝ) * τ ^ 2 ≤ 4 * q ^ 3 := by
      calc 4 * (k : ℝ) * τ ^ 2 = 4 * (((k : ℝ) * τ) * τ) := by ring
        _ ≤ 4 * ((q * q) * q) := by linarith [h2a]
        _ = 4 * q ^ 3 := by ring
    have h3 : τ ^ 2 ≤ q ^ 2 := by rw [pow_two, pow_two]; exact hττ
    have h4 : 128 * (k : ℝ) ^ 5 ≤ 128 * q ^ 5 := by linarith only [hk5]
    have h5 : 128 * (k : ℝ) ^ 5 + 8 * (k : ℝ) ^ 3 * τ + τ ^ 2 + 4 * (k : ℝ) * τ ^ 2
        ≤ 128 * q ^ 5 + 8 * q ^ 4 + q ^ 2 + 4 * q ^ 3 := by linarith only [h1, h2, h3, h4]
    have h6 : 128 * q ^ 5 + 8 * q ^ 4 + q ^ 2 + 4 * q ^ 3 ≤ 141 * q ^ 5 := by
      have h7 : q ^ 2 ≤ q ^ 5 := pow_le_pow_right₀ hq1 (by norm_num)
      have h8 : q ^ 3 ≤ q ^ 5 := pow_le_pow_right₀ hq1 (by norm_num)
      have h9 : q ^ 4 ≤ q ^ 5 := pow_le_pow_right₀ hq1 (by norm_num)
      linarith only [h7, h8, h9]
    linarith only [hM2, h5, h6]
  have hq3 : q ^ 3 ≤ q ^ 6 := pow_le_pow_right₀ hq1 (by norm_num)
  have hq4 : q ^ 4 ≤ q ^ 6 := pow_le_pow_right₀ hq1 (by norm_num)
  have hq6 : q ^ 6 ≤ q ^ 8 := pow_le_pow_right₀ hq1 (by norm_num)
  have hinner : 160 * ε * q * (τ ^ 2 * M₂) + 320 * K * ε * q * (τ * M₁) + 160 * K * ε * q ^ 3
      ≤ 30000 * (1 + K) * ε * q ^ 6 := by
    have h1 : 160 * ε * q * (τ ^ 2 * M₂) ≤ 22560 * ε * q ^ 6 := by
      have h := mul_le_mul_of_nonneg_left hτ2M₂ (by positivity : (0 : ℝ) ≤ 160 * ε * q)
      have hz : 160 * ε * q * (141 * q ^ 5) = 22560 * ε * q ^ 6 := by ring
      linarith only [h, hz]
    have h2 : 320 * K * ε * q * (τ * M₁) ≤ 2880 * K * ε * q ^ 6 := by
      have h := mul_le_mul_of_nonneg_left hτM₁ (by positivity : (0 : ℝ) ≤ 320 * K * ε * q)
      have hz : 320 * K * ε * q * (9 * q ^ 3) = 2880 * K * ε * q ^ 4 := by ring
      have h4 : 2880 * K * ε * q ^ 4 ≤ 2880 * K * ε * q ^ 6 :=
        mul_le_mul_of_nonneg_left hq4 (by positivity : (0 : ℝ) ≤ 2880 * K * ε)
      linarith only [h, hz, h4]
    have h3 : 160 * K * ε * q ^ 3 ≤ 160 * K * ε * q ^ 6 :=
      mul_le_mul_of_nonneg_left hq3 (by positivity : (0 : ℝ) ≤ 160 * K * ε)
    have h4 : 22560 * (ε * q ^ 6) + 3040 * (K * (ε * q ^ 6))
        ≤ 30000 * (ε * q ^ 6) + 30000 * (K * (ε * q ^ 6)) := by
      have h0 : (0 : ℝ) ≤ ε * q ^ 6 := by positivity
      have h1' : (0 : ℝ) ≤ K * (ε * q ^ 6) := mul_nonneg hK h0
      linarith only [h0, h1']
    calc 160 * ε * q * (τ ^ 2 * M₂) + 320 * K * ε * q * (τ * M₁) + 160 * K * ε * q ^ 3
        ≤ 22560 * ε * q ^ 6 + 2880 * K * ε * q ^ 6 + 160 * K * ε * q ^ 6 := by
          linarith only [h1, h2, h3]
      _ = 22560 * (ε * q ^ 6) + 3040 * (K * (ε * q ^ 6)) := by ring
      _ ≤ 30000 * (ε * q ^ 6) + 30000 * (K * (ε * q ^ 6)) := h4
      _ = 30000 * (1 + K) * ε * q ^ 6 := by ring
  have hstep3 : (2 * Real.pi)⁻¹ * (2 * Real.pi)⁻¹
        * (160 * ε * q * (τ ^ 2 * M₂) + 320 * K * ε * q * (τ * M₁) + 160 * K * ε * q ^ 3)
      ≤ (1 / 36) * (30000 * (1 + K) * ε * q ^ 6) := by
    have h0 : (0 : ℝ) ≤ 160 * ε * q * (τ ^ 2 * M₂) + 320 * K * ε * q * (τ * M₁)
        + 160 * K * ε * q ^ 3 := by positivity
    have hstep1 : (2 * Real.pi)⁻¹ * (2 * Real.pi)⁻¹
          * (160 * ε * q * (τ ^ 2 * M₂) + 320 * K * ε * q * (τ * M₁) + 160 * K * ε * q ^ 3)
        ≤ (1 / 36) * (160 * ε * q * (τ ^ 2 * M₂) + 320 * K * ε * q * (τ * M₁) + 160 * K * ε * q ^ 3) :=
      mul_le_mul_of_nonneg_right hcoef h0
    have hstep2 : (1 / 36 : ℝ)
          * (160 * ε * q * (τ ^ 2 * M₂) + 320 * K * ε * q * (τ * M₁) + 160 * K * ε * q ^ 3)
        ≤ (1 / 36) * (30000 * (1 + K) * ε * q ^ 6) :=
      mul_le_mul_of_nonneg_left hinner (by norm_num)
    exact hstep1.trans hstep2
  refine hstep3.trans ?_
  have hfinal : (1 / 36) * (30000 * (1 + K) * ε * q ^ 6) ≤ 3000 * (1 + K) * ε * q ^ 8 := by
    have h7 : (1 / 36 : ℝ) * 30000 * (1 + K) * ε * q ^ 6 ≤ 3000 * (1 + K) * ε * q ^ 6 := by
      have h0 : (0 : ℝ) ≤ (1 + K) * ε * q ^ 6 := by positivity
      linarith only [h0]
    have h8 : (3000 : ℝ) * (1 + K) * ε * q ^ 6 ≤ 3000 * (1 + K) * ε * q ^ 8 :=
      mul_le_mul_of_nonneg_left hq6 (by positivity : (0 : ℝ) ≤ 3000 * (1 + K) * ε)
    calc (1 / 36) * (30000 * (1 + K) * ε * q ^ 6)
        = (1 / 36 : ℝ) * 30000 * (1 + K) * ε * q ^ 6 := by ring
      _ ≤ 3000 * (1 + K) * ε * q ^ 6 := h7
      _ ≤ 3000 * (1 + K) * ε * q ^ 8 := h8
  exact hfinal

/-! ### §6.1 与 `τ` 无关的截断常数（`cutoffK`）与 `ε` 的事件性小性 -/

/-- `CutoffDeriv.exists_deriv_cutoff_bound` 的**与 `τ` 无关**的选择
（由 `exists_deriv_cutoff_bound_uniform` 保证存在）。 -/
noncomputable def cutoffK : ℝ := Classical.choose exists_deriv_cutoff_bound_uniform

lemma cutoffK_pos : 0 < cutoffK :=
  (Classical.choose_spec exists_deriv_cutoff_bound_uniform).1

lemma deriv_cutoff_le_cutoffK {τ B : ℝ} (hτ : 0 < τ) (hB : 0 < B) :
    (∀ μ : ℝ, |deriv (cutoff τ B) μ| ≤ cutoffK / B) ∧
      (∀ μ : ℝ, |deriv (deriv (cutoff τ B)) μ| ≤ cutoffK / B ^ 2) :=
  (Classical.choose_spec exists_deriv_cutoff_bound_uniform).2 τ B hτ hB

/-- **`ε = epsOf τ δ' (2N+1)` 的事件性小性**：对一切 `τ ≤ ρq`（`q = 2N+2`）
最终 `epsOf τ δ' (2N+1) ≤ c`（任意 `c > 0`）。 -/
lemma eventually_epsOf_le {ρ δ' : ℝ} (hρ0 : 0 < ρ) (hδ' : 0 < δ')
    (hη : 0 < δ' - ρ * Real.sinh δ') {c : ℝ} (hc : 0 < c) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ {τ : ℝ}, 0 < τ → τ ≤ ρ * (2 * (N : ℝ) + 2) →
      epsOf τ δ' (2 * N + 1) ≤ c := by
  have hc0 : (0 : ℝ) < 1 + 4 / (1 - Real.exp (-δ')) := by
    have hlt1 : Real.exp (-δ') < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    have h1 : 0 < 1 - Real.exp (-δ') := by linarith
    positivity
  have htend : Tendsto (fun N : ℕ => (1 + 4 / (1 - Real.exp (-δ'))) * Real.exp δ'
      * Real.exp (-(δ' - ρ * Real.sinh δ') * (2 * (N : ℝ) + 2))) atTop (nhds 0) := by
    have h := (tendsto_exp_decay_atTop hη).const_mul
      ((1 + 4 / (1 - Real.exp (-δ'))) * Real.exp δ')
    simpa using h
  filter_upwards [htend.eventually (eventually_lt_nhds hc)] with N hN τ hτ0 hτρ
  have hmono : epsOf τ δ' (2 * N + 1) ≤ epsOf (ρ * (2 * (N : ℝ) + 2)) δ' (2 * N + 1) := by
    rw [epsOf, epsOf]
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hc0.le) (by positivity)
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hτρ (Real.sinh_pos_iff.mpr hδ').le)
  have hdec := epsOf_le_exp_decay (ρ := ρ) (δ' := δ') (τ := ρ * (2 * (N : ℝ) + 2)) hδ'
    (by positivity) le_rfl
  linarith only [hmono, hdec, hN]

/-! ### §6.2 主衰减定理（τ-一致尺度） -/

/-- **核常数积的指数衰减（`B = ετ/q²` 尺度）**：对一切 admissible 且 `τ = (Σθ)/2 ≤ ρq`、
`τ > 0` 的构造（`q = 2N+2`、`ε = epsOf τ δ' (2N+1)`），

`C₁·C₂ ≤ 3000(1+K)·(1+4/(1−e^{−δ'}))·e^{δ'}·q⁸·e^{−ηq}`，`η = δ' − ρ·sinh δ' > 0`。

（`K = cutoffK` 是 `§6.1` 里与 `τ` 无关的截断常数。） -/
theorem kernel_decay_tau_scaled {φ : ℝ} (hφ0 : 0 < φ) (hφπ : φ ≤ Real.pi)
    {ρ δ' : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hδ' : 0 < δ')
    (hη : 0 < δ' - ρ * Real.sinh δ') :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ {L : ℕ} {α θ : Fin L → ℝ}, Admissible N φ L α θ →
      (∑ j, θ j) / 2 ≤ ρ * (2 * (N : ℝ) + 2) → 0 < (∑ j, θ j) / 2 →
      kernelA ((∑ j, θ j) / 2)
          (epsOf ((∑ j, θ j) / 2) δ' (2 * N + 1) * ((∑ j, θ j) / 2)
            / (2 * (N : ℝ) + 2) ^ 2)
          (scaledApprox ((∑ j, θ j) / 2) (2 * N + 1))
        * kernelC ((∑ j, θ j) / 2)
          (epsOf ((∑ j, θ j) / 2) δ' (2 * N + 1) * ((∑ j, θ j) / 2)
            / (2 * (N : ℝ) + 2) ^ 2)
          (scaledApprox ((∑ j, θ j) / 2) (2 * N + 1))
        ≤ 3000 * (1 + cutoffK) * (1 + 4 / (1 - Real.exp (-δ'))) * Real.exp δ'
          * (2 * (N : ℝ) + 2) ^ 8
          * Real.exp (-(δ' - ρ * Real.sinh δ') * (2 * (N : ℝ) + 2)) := by
  have hsmall := eventually_epsOf_le (ρ := ρ) (δ' := δ') hρ0 hδ' hη (c := 1 / 256) (by norm_num)
  filter_upwards [hsmall] with N hN L α θ hAdm hτρ hτ
  set q : ℝ := 2 * (N : ℝ) + 2 with hqdef
  set τ : ℝ := (∑ j, θ j) / 2 with hτdef
  set ε : ℝ := epsOf τ δ' (2 * N + 1) with hεdef
  set B : ℝ := ε * τ / q ^ 2 with hBdef
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hq2 : (2 : ℝ) ≤ q := by
    rw [hqdef]
    push_cast
    linarith only [hN0]
  have hq1 : (1 : ℝ) ≤ q := by linarith only [hq2]
  have hq0 : (0 : ℝ) < q := by linarith only [hq1]
  have hτq : τ ≤ q := by
    have h1 : ρ * q ≤ q := by
      calc ρ * q ≤ 1 * q := mul_le_mul_of_nonneg_right hρ1.le hq0.le
        _ = q := one_mul q
    linarith only [hτρ, h1]
  have hεle : ε ≤ 1 / 256 := by
    rw [hεdef]
    exact hN hτ hτρ
  have hε0 : (0 : ℝ) < ε := by rw [hεdef]; exact epsOf_pos hδ' τ (2 * N + 1)
  have hSq : Real.sqrt (B / τ) = Real.sqrt ε / q := by
    have h1 : B / τ = ε / q ^ 2 := by
      rw [hBdef]; field_simp
    rw [h1, Real.sqrt_div (le_of_lt hε0), Real.sqrt_sq hq0.le]
  have hsqε : Real.sqrt ε ≤ 1 / 16 := by
    have h1 : Real.sqrt ε ≤ Real.sqrt (1 / 256) := Real.sqrt_le_sqrt hεle
    have h2 : Real.sqrt (1 / 256 : ℝ) = 1 / 16 := by
      rw [show (1 / 256 : ℝ) = (1 / 16) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    linarith only [h1, h2]
  have hs : 2 * Real.sqrt (B / τ) ≤ 1 / 8 := by
    rw [hSq]
    have h1 : Real.sqrt ε / q ≤ 1 / 32 := by
      rw [div_le_iff₀ hq0]
      nlinarith only [hsqε, hq2]
    linarith only [h1]
  have hst : τ * (2 * Real.sqrt (B / τ)) ≤ 1 / 8 := by
    rw [hSq]
    have h1 : τ * (2 * (Real.sqrt ε / q)) = (2 * τ / q) * Real.sqrt ε := by ring
    rw [h1]
    have h2 : 2 * τ / q ≤ 2 / 1 := by
      rw [div_le_iff₀ hq0]; linarith only [hτq]
    have h4 : (2 * τ / q) * Real.sqrt ε ≤ 2 * (1 / 16) := by
      have h5 : (0 : ℝ) ≤ Real.sqrt ε := Real.sqrt_nonneg _
      have h6 : (0 : ℝ) ≤ 2 * τ / q := by positivity
      nlinarith only [h2, hsqε, h5, h6]
    linarith only [h4]
  have hBpos : 0 < B := by rw [hBdef]; positivity
  have hτpos : 0 < τ := hτ
  have hBhalf : B / τ ≤ 1 / 2 := by
    rw [hBdef]
    have h1 : ε * τ / q ^ 2 / τ = ε / q ^ 2 := by field_simp
    rw [h1, div_le_iff₀ (by positivity : (0 : ℝ) < q ^ 2)]
    nlinarith only [hεle, hq2]
  have hBτ : B ≤ τ := by
    rw [hBdef]
    have h1 : ε * τ / q ^ 2 = (ε / q ^ 2) * τ := by ring
    rw [h1]
    have h2 : ε / q ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity : (0 : ℝ) < q ^ 2)]
      nlinarith only [hεle, hq2]
    calc (ε / q ^ 2) * τ ≤ 1 * τ := mul_le_mul_of_nonneg_right h2 hτ.le
      _ = τ := one_mul τ
  have hkq : ((2 * N + 1 : ℕ) : ℝ) ≤ q := by
    rw [hqdef]; push_cast; linarith
  have hE2 : collarE τ B ≤ 2 := collarE_le_two τ B hτpos hBpos hs hst
  have hEpos : (0 : ℝ) < collarE τ B := Real.exp_pos _
  -- ### `M₁`、`M₂`
  set M₁ : ℝ := 2 * ((2 * N + 1 : ℕ) : ℝ) ^ 3 * collarE τ B / τ + 1
    + 2 * ((2 * N + 1 : ℕ) : ℝ) * collarE τ B with hM₁def
  set M₂ : ℝ := 64 * ((2 * N + 1 : ℕ) : ℝ) ^ 5 * collarE τ B / τ ^ 2
    + 4 * ((2 * N + 1 : ℕ) : ℝ) ^ 3 * collarE τ B / τ
    + (1 + 2 * ((2 * N + 1 : ℕ) : ℝ) * collarE τ B) with hM₂def
  have hM₁nn : 0 ≤ M₁ := by rw [hM₁def]; positivity
  have hM₂nn : 0 ≤ M₂ := by rw [hM₂def]; positivity
  have hM1 : τ * M₁ ≤ 4 * ((2 * N + 1 : ℕ) : ℝ) ^ 3 + τ
      + 4 * ((2 * N + 1 : ℕ) : ℝ) * τ := by
    have h1 : τ * M₁ = 2 * ((2 * N + 1 : ℕ) : ℝ) ^ 3 * collarE τ B + τ
        + 2 * ((2 * N + 1 : ℕ) : ℝ) * τ * collarE τ B := by
      rw [hM₁def]; field_simp
    rw [h1]
    have h2 : 2 * ((2 * N + 1 : ℕ) : ℝ) ^ 3 * collarE τ B
        ≤ 4 * ((2 * N + 1 : ℕ) : ℝ) ^ 3 := by
      have h := mul_le_mul_of_nonneg_left hE2
        (by positivity : (0 : ℝ) ≤ 2 * ((2 * N + 1 : ℕ) : ℝ) ^ 3)
      linarith only [h]
    have h3 : 2 * ((2 * N + 1 : ℕ) : ℝ) * τ * collarE τ B
        ≤ 4 * ((2 * N + 1 : ℕ) : ℝ) * τ := by
      have h := mul_le_mul_of_nonneg_left hE2
        (by positivity : (0 : ℝ) ≤ 2 * ((2 * N + 1 : ℕ) : ℝ) * τ)
      linarith only [h]
    linarith only [h2, h3]
  have hM2 : τ ^ 2 * M₂ ≤ 128 * ((2 * N + 1 : ℕ) : ℝ) ^ 5
      + 8 * ((2 * N + 1 : ℕ) : ℝ) ^ 3 * τ + τ ^ 2
      + 4 * ((2 * N + 1 : ℕ) : ℝ) * τ ^ 2 := by
    have h1 : τ ^ 2 * M₂ = 64 * ((2 * N + 1 : ℕ) : ℝ) ^ 5 * collarE τ B
        + 4 * ((2 * N + 1 : ℕ) : ℝ) ^ 3 * collarE τ B * τ + τ ^ 2
        + 2 * ((2 * N + 1 : ℕ) : ℝ) * τ ^ 2 * collarE τ B := by
      rw [hM₂def]; field_simp; ring
    rw [h1]
    have hkN : (0:ℝ) ≤ ((2 * N + 1 : ℕ) : ℝ) := by positivity
    have h2 : 64 * ((2 * N + 1 : ℕ) : ℝ) ^ 5 * collarE τ B
        ≤ 128 * ((2 * N + 1 : ℕ) : ℝ) ^ 5 := by
      have h := mul_le_mul_of_nonneg_left hE2
        (by positivity : (0 : ℝ) ≤ 64 * ((2 * N + 1 : ℕ) : ℝ) ^ 5)
      linarith only [h]
    have h3 : 4 * ((2 * N + 1 : ℕ) : ℝ) ^ 3 * collarE τ B * τ
        ≤ 8 * ((2 * N + 1 : ℕ) : ℝ) ^ 3 * τ := by
      have h := mul_le_mul_of_nonneg_left hE2
        (by positivity : (0 : ℝ) ≤ 4 * ((2 * N + 1 : ℕ) : ℝ) ^ 3 * τ)
      linarith only [h]
    have h4 : 2 * ((2 * N + 1 : ℕ) : ℝ) * τ ^ 2 * collarE τ B
        ≤ 4 * ((2 * N + 1 : ℕ) : ℝ) * τ ^ 2 := by
      have h := mul_le_mul_of_nonneg_left hE2
        (by positivity : (0 : ℝ) ≤ 2 * ((2 * N + 1 : ℕ) : ℝ) * τ ^ 2)
      linarith only [h]
    linarith only [h2, h3, h4]
  -- ### 应用 §5、§6.1 的界
  have hA1 : ∀ μ : ℝ, |μ| ≤ τ + B →
      ‖deriv (fun x : ℝ => psiA (scaledApprox τ (2 * N + 1)) x) μ‖ ≤ M₁ := by
    intro μ hμ
    rw [hM₁def]
    exact norm_deriv_psiA_scaled_collar_le τ B hτpos hBpos (2 * N + 1) hμ
  have hA2 : ∀ μ : ℝ, |μ| ≤ τ + B →
      ‖deriv (deriv (fun x : ℝ => psiA (scaledApprox τ (2 * N + 1)) x)) μ‖ ≤ M₂ := by
    intro μ hμ
    rw [hM₂def]
    exact norm_deriv2_psiA_scaled_collar_le τ B hτpos hBpos (2 * N + 1) hBhalf hμ
  have hPε : ∀ μ : ℝ, |μ| ≤ τ →
      ‖Complex.exp (-(μ : ℂ) * Complex.I)
        - (scaledApprox τ (2 * N + 1)).eval ((μ : ℂ))‖ ≤ ε := by
    intro μ hμ
    rw [hεdef]
    exact scaledApprox_band_epsOf τ hτpos hδ' (by omega) hμ
  have hψ : ∀ μ : ℝ, ‖psi τ B (scaledApprox τ (2 * N + 1)) μ‖ ≤ ε + B * M₁ :=
    norm_psi_le_band_add_collar hτ.le hBpos _ hM₁nn hPε hA1
  have hcut := deriv_cutoff_le_cutoffK hτpos hBpos
  have hK1 : ∀ μ : ℝ, ‖deriv (fun x : ℝ => ((cutoff τ B x : ℝ) : ℂ)) μ‖
      ≤ cutoffK / B := by
    intro μ
    rw [deriv_coe_cutoff τ B hτpos hBpos, Complex.norm_real, Real.norm_eq_abs]
    exact hcut.1 μ
  have hK2 : ∀ μ : ℝ, ‖deriv (deriv (fun x : ℝ => ((cutoff τ B x : ℝ) : ℂ))) μ‖
      ≤ cutoffK / B ^ 2 := by
    intro μ
    rw [deriv_deriv_coe_cutoff τ B hτpos hBpos, Complex.norm_real, Real.norm_eq_abs]
    exact hcut.2 μ
  have hmain := kernelProd_le_poly (scaledApprox τ (2 * N + 1)) hτpos hBpos hε0.le
    (le_of_lt cutoffK_pos) hM₁nn hM₂nn hq1 hkq hτq hBτ rfl hM1 hM2 hψ hPε hA1 hA2 hK1 hK2
  refine hmain.trans ?_
  -- ### 把 `ε` 换成指数衰减
  have hεdec : ε ≤ (1 + 4 / (1 - Real.exp (-δ'))) * Real.exp δ'
      * Real.exp (-(δ' - ρ * Real.sinh δ') * q) := by
    rw [hεdef]
    have h := epsOf_le_exp_decay (ρ := ρ) (δ' := δ') (τ := τ) hδ' hτ.le hτρ
    simpa only [hqdef] using h
  have hcoef0 : (0 : ℝ) ≤ 3000 * (1 + cutoffK) :=
    mul_nonneg (by norm_num) (by linarith only [cutoffK_pos])
  have hq8 : (0 : ℝ) ≤ q ^ 8 := pow_nonneg hq0.le 8
  have h1 : ε * q ^ 8 ≤ ((1 + 4 / (1 - Real.exp (-δ'))) * Real.exp δ'
      * Real.exp (-(δ' - ρ * Real.sinh δ') * q)) * q ^ 8 :=
    mul_le_mul_of_nonneg_right hεdec hq8
  have h2 : 3000 * (1 + cutoffK) * (ε * q ^ 8)
      ≤ 3000 * (1 + cutoffK) * (((1 + 4 / (1 - Real.exp (-δ'))) * Real.exp δ'
      * Real.exp (-(δ' - ρ * Real.sinh δ') * q)) * q ^ 8) :=
    mul_le_mul_of_nonneg_left h1 hcoef0
  calc 3000 * (1 + cutoffK) * ε * q ^ 8
      = 3000 * (1 + cutoffK) * (ε * q ^ 8) := by ring
    _ ≤ 3000 * (1 + cutoffK) * (((1 + 4 / (1 - Real.exp (-δ'))) * Real.exp δ'
        * Real.exp (-(δ' - ρ * Real.sinh δ') * q)) * q ^ 8) := h2
    _ = 3000 * (1 + cutoffK) * (1 + 4 / (1 - Real.exp (-δ'))) * Real.exp δ'
        * q ^ 8 * Real.exp (-(δ' - ρ * Real.sinh δ') * q) := by ring

/-! ### §6.3 第 3 步：`τ ≤ ρq` 的端点小性（**无附加假设**） -/

/-- **`h_zero_small_of_tau_le_scaled`**：对一切 admissible 构造，若 `τ = (Σθ)/2 ≤ ρ(2N+2)`
（`0 < ρ < 1`），则最终 `h(0) < 1 − cos(φ/2)`。于是**不存在**满足 `τ ≤ ρ(2N+2)` 的 N 阶构造。

证明：取 `δ' > 0` 使 `η = δ' − ρ sinh δ' > 0`；`kernel_decay_tau_scaled` 给
`C₁C₂ ≤ D·q⁸·e^{−ηq} =: A N`；`A N → 0`（`tendsto_pow_const_mul_const_pow_of_lt_one`），
故最终 `8√(A N) < 1 − cos(φ/2)`，配合 M3′（`h_zero_le_of_admissible_tau_scaled`）即得。 -/
theorem h_zero_small_of_tau_le_scaled {φ : ℝ} (hφ0 : 0 < φ) (hφπ : φ ≤ Real.pi)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ {L : ℕ} {α θ : Fin L → ℝ},
      Admissible N φ L α θ → (∑ j, θ j) / 2 ≤ ρ * (2 * (N : ℝ) + 2) →
      h L α θ 0 < 1 - Real.cos (φ / 2) := by
  obtain ⟨δ', hδ'0, hη⟩ := exists_delta_sub_mul_sinh_pos hρ0 hρ1
  have hdecay := kernel_decay_tau_scaled hφ0 hφπ hρ0 hρ1 hδ'0 hη
  set D : ℝ := 3000 * (1 + cutoffK) * (1 + 4 / (1 - Real.exp (-δ'))) * Real.exp δ' with hDdef
  have hη' : (0 : ℝ) < δ' - ρ * Real.sinh δ' := hη
  set r : ℝ := Real.exp (-2 * (δ' - ρ * Real.sinh δ')) with hrdef
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by linarith only [hη'])
  have hbase : Tendsto (fun N : ℕ => ((N : ℝ) + 1) ^ 8 * r ^ (N + 1)) atTop (nhds 0) := by
    have h1 : Tendsto (fun n : ℕ => (n : ℝ) ^ 8 * r ^ n) atTop (nhds 0) :=
      tendsto_pow_const_mul_const_pow_of_lt_one 8 hr0 hr1
    have h2 : Tendsto (fun N : ℕ => (((N + 1 : ℕ)) : ℝ) ^ 8 * r ^ (N + 1)) atTop (nhds 0) :=
      h1.comp (tendsto_add_atTop_nat 1)
    simpa using h2
  have hexp : ∀ N : ℕ,
      Real.exp (-(δ' - ρ * Real.sinh δ') * (2 * (N : ℝ) + 2)) = r ^ (N + 1) := by
    intro N
    rw [hrdef, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hA0 : Tendsto (fun N : ℕ => D * (2 * (N : ℝ) + 2) ^ 8
      * Real.exp (-(δ' - ρ * Real.sinh δ') * (2 * (N : ℝ) + 2))) atTop (nhds 0) := by
    have h1 : Tendsto (fun N : ℕ => (D * 2 ^ 8) * (((N : ℝ) + 1) ^ 8 * r ^ (N + 1)))
        atTop (nhds 0) := by
      have := hbase.const_mul (D * 2 ^ 8)
      simpa using this
    refine h1.congr' ?_
    filter_upwards with N
    rw [hexp N]
    have h2 : (2 * ((N : ℝ)) + 2) = 2 * ((N : ℝ) + 1) := by ring
    rw [h2]
    ring
  have hc : 0 < 1 - Real.cos (φ / 2) := one_sub_cos_half_pos hφ0 hφπ
  have hc8 : 0 < (1 - Real.cos (φ / 2)) / 8 := by linarith only [hc]
  have hev : ∀ᶠ N : ℕ in Filter.atTop, D * (2 * (N : ℝ) + 2) ^ 8
      * Real.exp (-(δ' - ρ * Real.sinh δ') * (2 * (N : ℝ) + 2))
      < ((1 - Real.cos (φ / 2)) / 8) ^ 2 :=
    hA0.eventually (eventually_lt_nhds (by positivity))
  filter_upwards [hdecay, hev] with N hN hAN L α θ hAdm hτρ
  by_cases hτ0 : (∑ j, θ j) / 2 = 0
  · rw [h_zero_of_admissible_of_cost_eq_zero hAdm (by linarith only [hτ0])]
    exact hc
  · have hτ : 0 < (∑ j, θ j) / 2 :=
      lt_of_le_of_ne (div_nonneg (Finset.sum_nonneg fun j _ => hAdm.1 j) (by norm_num))
        (Ne.symm hτ0)
    have h1 := h_zero_le_of_admissible_tau_scaled hAdm hδ'0 hτ
    have h2 := hN hAdm hτρ hτ
    have hs : Real.sqrt (D * (2 * (N : ℝ) + 2) ^ 8
        * Real.exp (-(δ' - ρ * Real.sinh δ') * (2 * (N : ℝ) + 2)))
        < (1 - Real.cos (φ / 2)) / 8 := by
      rw [Real.sqrt_lt' hc8]
      exact hAN
    have h3 : 8 * Real.sqrt (D * (2 * (N : ℝ) + 2) ^ 8
        * Real.exp (-(δ' - ρ * Real.sinh δ') * (2 * (N : ℝ) + 2))) < 1 - Real.cos (φ / 2) := by
      linarith only [hs, hc]
    refine lt_of_le_of_lt ?_ h3
    exact h1.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h2) (by norm_num))

end RobustZ
