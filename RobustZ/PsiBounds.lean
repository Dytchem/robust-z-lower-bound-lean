import RobustZ.Smearing

noncomputable section

namespace RobustZ

open scoped Real
open Filter MeasureTheory

/-!
# M4：`Ψ_A` 与 `Ψ` 的显式界
-/

/-! ### 辅助：`psiA` 的一阶导数 -/

/-- 多项式（复系数）沿实轴的导数。 -/
lemma hasDerivAt_poly_eval_real (Q : Polynomial ℂ) (μ : ℝ) :
    HasDerivAt (fun x : ℝ => Q.eval ((x : ℂ))) (Q.derivative.eval ((μ : ℂ))) μ := by
  simpa using (Polynomial.hasStrictDerivAt Q (μ : ℂ)).hasDerivAt.comp_ofReal

/-- `d/dμ exp(iμ) = exp(iμ)·i`。 -/
lemma hasDerivAt_exp_mul_I (μ : ℝ) :
    HasDerivAt (fun x : ℝ => Complex.exp ((x : ℂ) * Complex.I))
      (Complex.exp ((μ : ℂ) * Complex.I) * Complex.I) μ := by
  have h1 : HasDerivAt (fun x : ℝ => (x : ℂ) * Complex.I) ((1 : ℂ) * Complex.I) μ :=
    (HasDerivAt.ofReal_comp (hasDerivAt_id μ : HasDerivAt (fun x : ℝ => x) 1 μ)).mul_const
      Complex.I
  simpa using h1.cexp

/-- `psiA P` 的（形式）导数：`d/dμ (1 − P(μ)e^{iμ}) = −(P'(μ)e^{iμ} + P(μ)·i·e^{iμ})`。 -/
noncomputable def dpsiA (P : Polynomial ℂ) (μ : ℝ) : ℂ :=
  -(P.derivative.eval ((μ : ℂ)) * Complex.exp ((μ : ℂ) * Complex.I)
    + P.eval ((μ : ℂ)) * (Complex.exp ((μ : ℂ) * Complex.I) * Complex.I))

lemma hasDerivAt_psiA (P : Polynomial ℂ) (μ : ℝ) :
    HasDerivAt (fun x : ℝ => psiA P x) (dpsiA P μ) μ := by
  have hd : (0 : ℂ) - (P.derivative.eval ((μ : ℂ)) * Complex.exp ((μ : ℂ) * Complex.I)
      + P.eval ((μ : ℂ)) * (Complex.exp ((μ : ℂ) * Complex.I) * Complex.I)) = dpsiA P μ := by
    rw [dpsiA]
    ring
  rw [← hd]
  exact (hasDerivAt_const μ (1 : ℂ)).sub
    ((hasDerivAt_poly_eval_real P μ).mul (hasDerivAt_exp_mul_I μ))

lemma differentiableAt_psiA (P : Polynomial ℂ) (μ : ℝ) :
    DifferentiableAt ℝ (fun x : ℝ => psiA P x) μ :=
  (hasDerivAt_psiA P μ).differentiableAt

lemma deriv_psiA (P : Polynomial ℂ) :
    deriv (fun x : ℝ => psiA P x) = dpsiA P :=
  funext fun μ => (hasDerivAt_psiA P μ).deriv

/-- `psiA P` 的导函数仍处处可导（多项式乘指数，光滑）。 -/
lemma differentiableAt_dpsiA (P : Polynomial ℂ) (μ : ℝ) :
    DifferentiableAt ℝ (dpsiA P) μ := by
  have h1 : DifferentiableAt ℝ (fun x : ℝ => P.derivative.eval ((x : ℂ))) μ :=
    (hasDerivAt_poly_eval_real P.derivative μ).differentiableAt
  have h2 : DifferentiableAt ℝ (fun x : ℝ => P.eval ((x : ℂ))) μ :=
    (hasDerivAt_poly_eval_real P μ).differentiableAt
  have h3 : DifferentiableAt ℝ (fun x : ℝ => Complex.exp ((x : ℂ) * Complex.I)) μ :=
    (hasDerivAt_exp_mul_I μ).differentiableAt
  have h4 : DifferentiableAt ℝ (fun x : ℝ => Complex.exp ((x : ℂ) * Complex.I) * Complex.I) μ :=
    h3.mul (differentiableAt_const Complex.I)
  have hgoal : DifferentiableAt ℝ (fun x : ℝ =>
      -(P.derivative.eval ((x : ℂ)) * Complex.exp ((x : ℂ) * Complex.I)
        + P.eval ((x : ℂ)) * (Complex.exp ((x : ℂ) * Complex.I) * Complex.I))) μ :=
    ((h1.mul h3).add (h2.mul h4)).neg
  rw [show dpsiA P = fun x : ℝ =>
      -(P.derivative.eval ((x : ℂ)) * Complex.exp ((x : ℂ) * Complex.I)
        + P.eval ((x : ℂ)) * (Complex.exp ((x : ℂ) * Complex.I) * Complex.I)) from rfl]
  exact hgoal

/-- `‖1 − P(μ)e^{iμ}‖ = ‖e^{−iμ} − P(μ)‖`（乘上模为 1 的因子）。 -/
lemma norm_psiA_eq (P : Polynomial ℂ) (μ : ℝ) :
    ‖psiA P μ‖ = ‖Complex.exp (-(μ : ℂ) * Complex.I) - P.eval ((μ : ℂ))‖ := by
  have hfac : psiA P μ
      = Complex.exp ((μ : ℂ) * Complex.I)
        * (Complex.exp (-(μ : ℂ) * Complex.I) - P.eval ((μ : ℂ))) := by
    have h1 : Complex.exp ((μ : ℂ) * Complex.I) * Complex.exp (-(μ : ℂ) * Complex.I) = 1 := by
      rw [← Complex.exp_add]
      have h2 : (μ : ℂ) * Complex.I + -(μ : ℂ) * Complex.I = 0 := by ring
      rw [h2, Complex.exp_zero]
    rw [psiA, mul_sub, h1]
    ring
  have hexp : ‖Complex.exp ((μ : ℂ) * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp]
    have hre : ((μ : ℂ) * Complex.I).re = 0 := by
      simp [Complex.mul_re]
    rw [hre, Real.exp_zero]
  rw [hfac, norm_mul, hexp, one_mul]

/-! ### (1) taper 区上 `Ψ_A` 的界 -/

/-- **中值定理搬运**：带内 `‖e^{−iμ} − P(μ)‖ ≤ ε`、且 `‖Ψ_A'‖ ≤ M`（在 `|μ| ≤ τ + B` 上），
则在整个 taper 区上 `‖Ψ_A(μ)‖ ≤ ε + B·M`。

（注：题面没有 `τ ≥ 0` 的假设，但 `τ < 0` 时带 `|μ| ≤ τ` 为空，命题不成立，
例如 `P = 0, τ = −1, B = 1, ε = M = 0` 时 `μ = 0` 处 `‖Ψ_A(0)‖ = 1 > 0`。
故这里需要 `0 ≤ τ`；`τ = 0` 允许。） -/
lemma norm_psiA_le (τ B : ℝ) (hτ : 0 ≤ τ) (hB : 0 < B) (P : Polynomial ℂ) {ε M : ℝ}
    (hPε : ∀ μ : ℝ, |μ| ≤ τ → ‖Complex.exp (-(μ : ℂ) * Complex.I) - P.eval ((μ : ℂ))‖ ≤ ε)
    (hM : ∀ μ : ℝ, |μ| ≤ τ + B → ‖deriv (fun x : ℝ => psiA P x) μ‖ ≤ M) :
    ∀ μ : ℝ, |μ| ≤ τ + B → ‖psiA P μ‖ ≤ ε + B * M := by
  have hMnn : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 (by rw [abs_zero]; linarith))
  -- 带内一点 `ν₀`（`|ν₀| ≤ τ`）到 `ν` 的中值定理
  have key : ∀ ν ν₀ : ℝ, |ν₀| ≤ τ → |ν - ν₀| ≤ B → ‖psiA P ν‖ ≤ ε + B * M := by
    intro ν ν₀ hν₀ hdist
    have hb : ‖psiA P ν₀‖ ≤ ε := by
      rw [norm_psiA_eq]
      exact hPε ν₀ hν₀
    have hν : |ν| ≤ τ + B := by
      calc |ν| = |ν₀ + (ν - ν₀)| := by ring_nf
        _ ≤ |ν₀| + |ν - ν₀| := abs_add_le _ _
        _ ≤ τ + B := by linarith
    have hmvt : ‖psiA P ν - psiA P ν₀‖ ≤ M * |ν - ν₀| := by
      have h := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ)
        (f := fun x : ℝ => psiA P x) (s := Set.uIcc ν₀ ν) (C := M) (x := ν₀) (y := ν)
        (fun x _ => differentiableAt_psiA P x) ?_ (convex_uIcc ν₀ ν) Set.left_mem_uIcc
        Set.right_mem_uIcc
      · simpa [Real.norm_eq_abs] using h
      · intro x hx
        refine hM x ?_
        have hx' := Set.mem_uIcc.mp hx
        have hν₀' := abs_le.mp hν₀
        have hν' := abs_le.mp hν
        rw [abs_le]
        rcases hx' with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨by linarith, by linarith⟩
        · exact ⟨by linarith, by linarith⟩
    calc ‖psiA P ν‖ = ‖psiA P ν₀ + (psiA P ν - psiA P ν₀)‖ := by
          congr 1
          ring
      _ ≤ ‖psiA P ν₀‖ + ‖psiA P ν - psiA P ν₀‖ := norm_add_le _ _
      _ ≤ ε + M * B := add_le_add hb (le_trans hmvt (mul_le_mul_of_nonneg_left hdist hMnn))
      _ = ε + B * M := by ring
  intro μ hμ
  rcases le_or_gt 0 μ with hμ0 | hμ0
  · -- `μ ≥ 0`：取 `μ₀ = min μ τ`
    refine key μ (min μ τ) ?_ ?_
    · rw [abs_le]
      exact ⟨le_min (by linarith) (by linarith), min_le_right μ τ⟩
    · have hle : μ - min μ τ ≤ B := by
        rcases min_choice μ τ with h | h
        · rw [h, sub_self]; linarith
        · rw [h]; linarith [abs_le.mp hμ]
      rw [abs_of_nonneg (by linarith [min_le_left μ τ])]
      exact hle
  · -- `μ < 0`：取 `μ₀ = max μ (−τ)`
    refine key μ (max μ (-τ)) ?_ ?_
    · rw [abs_le]
      exact ⟨le_max_right μ (-τ), max_le (by linarith) (by linarith)⟩
    · have hle : max μ (-τ) - μ ≤ B := by
        rcases max_choice μ (-τ) with h | h
        · rw [h, sub_self]; linarith
        · rw [h]; linarith [abs_le.mp hμ]
      have hnonpos : μ - max μ (-τ) ≤ 0 := by linarith [le_max_left μ (-τ)]
      rw [abs_of_nonpos hnonpos]
      linarith


/-! ### (2) `∫‖Ψ''‖` 的显式界 -/

/-- 乘积的二阶导数：`(fg)'' = f''g + 2f'g' + fg''`。 -/
lemma deriv_deriv_mul (f g : ℝ → ℂ) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (hf' : Differentiable ℝ (deriv f)) (hg' : Differentiable ℝ (deriv g)) (x : ℝ) :
    deriv (deriv (f * g)) x
      = deriv (deriv f) x * g x + 2 * (deriv f x * deriv g x) + f x * deriv (deriv g) x := by
  have h1 : deriv (f * g) = fun y : ℝ => deriv f y * g y + f y * deriv g y :=
    funext fun y => deriv_mul (hf y) (hg y)
  rw [h1]
  have e1 : deriv (fun y : ℝ => deriv f y * g y + f y * deriv g y) x
      = deriv (fun y : ℝ => deriv f y * g y) x + deriv (fun y : ℝ => f y * deriv g y) x := by
    rw [show (fun y : ℝ => deriv f y * g y + f y * deriv g y)
        = (fun y : ℝ => deriv f y * g y) + (fun y : ℝ => f y * deriv g y) from rfl]
    exact deriv_add ((hf' x).mul (hg x)) ((hf x).mul (hg' x))
  have e2 : deriv (fun y : ℝ => deriv f y * g y) x
      = deriv (deriv f) x * g x + deriv f x * deriv g x :=
    deriv_mul (hf' x) (hg x)
  have e3 : deriv (fun y : ℝ => f y * deriv g y) x
      = deriv f x * deriv g x + f x * deriv (deriv g) x :=
    deriv_mul (hf x) (hg' x)
  rw [e1, e2, e3]
  ring

/-- `K(μ) = (χ(μ) : ℂ)` 是 `C²` 的（`χ = cutoff τ B`，`τ > 0`）。 -/
lemma contDiff_coe_cutoff (τ B : ℝ) (hτ : 0 < τ) (hB : 0 < B) :
    ContDiff ℝ 2 (fun μ : ℝ => ((cutoff τ B μ : ℝ) : ℂ)) :=
  (ContinuousLinearMap.contDiff Complex.ofRealCLM).comp (contDiff_cutoff τ B hτ hB)

lemma differentiableAt_cutoff (τ B : ℝ) (hτ : 0 < τ) (hB : 0 < B) (x : ℝ) :
    DifferentiableAt ℝ (cutoff τ B) x :=
  ((contDiff_cutoff τ B hτ hB).contDiffAt (x := x)).differentiableAt (by norm_num)

lemma differentiableAt_deriv_cutoff (τ B : ℝ) (hτ : 0 < τ) (hB : 0 < B) (x : ℝ) :
    DifferentiableAt ℝ (deriv (cutoff τ B)) x :=
  ((contDiff_cutoff τ B hτ hB).differentiable_deriv_two.differentiableAt (x := x))

lemma differentiableAt_coe_cutoff (τ B : ℝ) (hτ : 0 < τ) (hB : 0 < B) (x : ℝ) :
    DifferentiableAt ℝ (fun μ : ℝ => ((cutoff τ B μ : ℝ) : ℂ)) x :=
  ((contDiff_coe_cutoff τ B hτ hB).contDiffAt (x := x)).differentiableAt (by norm_num)

/-- `K` 的导数：`(χ(μ) : ℂ)' = (χ'(μ) : ℂ)`。 -/
lemma deriv_coe_cutoff (τ B : ℝ) (hτ : 0 < τ) (hB : 0 < B) :
    deriv (fun μ : ℝ => ((cutoff τ B μ : ℝ) : ℂ))
      = fun μ : ℝ => ((deriv (cutoff τ B) μ : ℝ) : ℂ) := by
  funext x
  exact (HasDerivAt.ofReal_comp ((differentiableAt_cutoff τ B hτ hB x).hasDerivAt)).deriv

/-- `K` 的二阶导数。 -/
lemma deriv_deriv_coe_cutoff (τ B : ℝ) (hτ : 0 < τ) (hB : 0 < B) :
    deriv (deriv (fun μ : ℝ => ((cutoff τ B μ : ℝ) : ℂ)))
      = fun μ : ℝ => ((deriv (deriv (cutoff τ B)) μ : ℝ) : ℂ) := by
  rw [deriv_coe_cutoff τ B hτ hB]
  funext x
  exact (HasDerivAt.ofReal_comp
    ((differentiableAt_deriv_cutoff τ B hτ hB x).hasDerivAt)).deriv

/-- `|μ| > τ + B` 时 `Ψ ≡ 0`（在一个邻域上），故一阶导数为零。 -/
lemma deriv_psi_eq_zero_of_lt_abs {τ B : ℝ} (hB : 0 < B) (P : Polynomial ℂ) {x : ℝ}
    (h : τ + B < |x|) : deriv (psi τ B P) x = 0 := by
  have hopen : IsOpen {y : ℝ | τ + B < |y|} := isOpen_lt continuous_const continuous_abs
  have hx : psi τ B P =ᶠ[nhds x] fun _ => (0 : ℂ) := by
    filter_upwards [hopen.mem_nhds h] with y hy
    exact psi_eq_zero P hB (le_of_lt hy)
  rw [Filter.EventuallyEq.deriv_eq hx]
  simp

/-- `|μ| > τ + B` 时 `Ψ'' ≡ 0`。 -/
lemma deriv2_psi_eq_zero_of_lt_abs {τ B : ℝ} (hB : 0 < B) (P : Polynomial ℂ) {x : ℝ}
    (h : τ + B < |x|) : deriv (deriv (psi τ B P)) x = 0 := by
  have hopen : IsOpen {y : ℝ | τ + B < |y|} := isOpen_lt continuous_const continuous_abs
  have hx : deriv (psi τ B P) =ᶠ[nhds x] fun _ => (0 : ℂ) := by
    filter_upwards [hopen.mem_nhds h] with y hy
    exact deriv_psi_eq_zero_of_lt_abs hB P hy
  rw [Filter.EventuallyEq.deriv_eq hx]
  simp
/-- **(2) 点态界（一般常数）**。带内 `|μ| ≤ τ + B` 上
`‖Ψ''(μ)‖ ≤ M2 + 2·M1·N1 + (ε + B·M1)·N2`，其中
`N1` 是 `χ'` 的界、`N2` 是 `χ''` 的界（与 `M1 = ‖Ψ_A'‖`、`M2 = ‖Ψ_A''‖` 独立）。

乘积法则 `Ψ'' = Ψ_A''·χ + 2·Ψ_A'·χ' + Ψ_A·χ''`，逐项放缩即可。 -/
lemma norm_deriv2_psi_le_gen (τ B : ℝ) (hτ : 0 < τ) (hB : 0 < B) (P : Polynomial ℂ)
    {ε M1 M2 N1 N2 : ℝ} (hε : 0 ≤ ε)
    (hPε : ∀ μ : ℝ, |μ| ≤ τ → ‖Complex.exp (-(μ : ℂ) * Complex.I) - P.eval ((μ : ℂ))‖ ≤ ε)
    (hA1 : ∀ μ : ℝ, |μ| ≤ τ + B → ‖deriv (fun x : ℝ => psiA P x) μ‖ ≤ M1)
    (hA2 : ∀ μ : ℝ, |μ| ≤ τ + B → ‖deriv (deriv (fun x : ℝ => psiA P x)) μ‖ ≤ M2)
    (hK1 : ∀ μ : ℝ, ‖deriv (cutoff τ B) μ‖ ≤ N1)
    (hK2 : ∀ μ : ℝ, ‖deriv (deriv (cutoff τ B)) μ‖ ≤ N2) :
    ∀ μ : ℝ, |μ| ≤ τ + B →
      ‖deriv (deriv (psi τ B P)) μ‖ ≤ M2 + 2 * (M1 * N1) + (ε + B * M1) * N2 := by
  have hM1nn : 0 ≤ M1 := le_trans (norm_nonneg _) (hA1 0 (by rw [abs_zero]; linarith))
  have hM2nn : 0 ≤ M2 := le_trans (norm_nonneg _) (hA2 0 (by rw [abs_zero]; linarith))
  have hAall : Differentiable ℝ (fun z : ℝ => psiA P z) := fun z => differentiableAt_psiA P z
  have hA'all : Differentiable ℝ (deriv (fun z : ℝ => psiA P z)) := by
    rw [deriv_psiA P]
    exact fun z => differentiableAt_dpsiA P z
  have hKall : Differentiable ℝ (fun z : ℝ => ((cutoff τ B z : ℝ) : ℂ)) :=
    fun z => differentiableAt_coe_cutoff τ B hτ hB z
  have hK'all : Differentiable ℝ (deriv (fun z : ℝ => ((cutoff τ B z : ℝ) : ℂ))) := by
    rw [deriv_coe_cutoff τ B hτ hB]
    exact fun z => (Complex.differentiable_ofReal.differentiableAt (x := (deriv (cutoff τ B) z))).comp
      z (differentiableAt_deriv_cutoff τ B hτ hB z)
  have hpsiK : psi τ B P
      = (fun z : ℝ => psiA P z) * (fun z : ℝ => ((cutoff τ B z : ℝ) : ℂ)) := by
    funext x
    rw [psi]
    rfl
  intro μ hμ
  have hd2 : deriv (deriv (psi τ B P)) μ
      = deriv (deriv (fun z : ℝ => psiA P z)) μ * ((cutoff τ B μ : ℝ) : ℂ)
        + 2 * (deriv (fun z : ℝ => psiA P z) μ
            * deriv (fun z : ℝ => ((cutoff τ B z : ℝ) : ℂ)) μ)
        + psiA P μ * deriv (deriv (fun z : ℝ => ((cutoff τ B z : ℝ) : ℂ))) μ := by
    rw [hpsiK]
    exact deriv_deriv_mul (fun z : ℝ => psiA P z) (fun z : ℝ => ((cutoff τ B z : ℝ) : ℂ))
      hAall hKall hA'all hK'all μ
  have hK0μ : ‖((cutoff τ B μ : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (cutoff_nonneg τ B μ)]
    exact cutoff_le_one τ B μ
  have hK1μ : ‖deriv (fun z : ℝ => ((cutoff τ B z : ℝ) : ℂ)) μ‖ ≤ N1 := by
    rw [deriv_coe_cutoff τ B hτ hB]
    simpa only [Complex.norm_real] using hK1 μ
  have hK2μ : ‖deriv (deriv (fun z : ℝ => ((cutoff τ B z : ℝ) : ℂ))) μ‖ ≤ N2 := by
    rw [deriv_deriv_coe_cutoff τ B hτ hB]
    simpa only [Complex.norm_real] using hK2 μ
  have hεM1 : 0 ≤ ε + B * M1 := by linarith [mul_nonneg hB.le hM1nn]
  have t1 : ‖deriv (deriv (fun z : ℝ => psiA P z)) μ * ((cutoff τ B μ : ℝ) : ℂ)‖ ≤ M2 * 1 := by
    rw [norm_mul]
    exact mul_le_mul (hA2 μ hμ) hK0μ (norm_nonneg _) hM2nn
  have t2 : ‖deriv (fun z : ℝ => psiA P z) μ
      * deriv (fun z : ℝ => ((cutoff τ B z : ℝ) : ℂ)) μ‖ ≤ M1 * N1 := by
    rw [norm_mul]
    exact mul_le_mul (hA1 μ hμ) hK1μ (norm_nonneg _) hM1nn
  have t2' : ‖2 * (deriv (fun z : ℝ => psiA P z) μ
      * deriv (fun z : ℝ => ((cutoff τ B z : ℝ) : ℂ)) μ)‖ ≤ 2 * (M1 * N1) := by
    rw [norm_mul, Complex.norm_ofNat]
    exact mul_le_mul_of_nonneg_left t2 (by norm_num)
  have t3 : ‖psiA P μ * deriv (deriv (fun z : ℝ => ((cutoff τ B z : ℝ) : ℂ))) μ‖
      ≤ (ε + B * M1) * N2 := by
    rw [norm_mul]
    exact mul_le_mul (norm_psiA_le τ B hτ.le hB P hPε hA1 μ hμ) hK2μ (norm_nonneg _) hεM1
  rw [hd2]
  calc ‖(deriv (deriv (fun z : ℝ => psiA P z)) μ * ((cutoff τ B μ : ℝ) : ℂ)
        + 2 * (deriv (fun z : ℝ => psiA P z) μ
            * deriv (fun z : ℝ => ((cutoff τ B z : ℝ) : ℂ)) μ))
      + psiA P μ * deriv (deriv (fun z : ℝ => ((cutoff τ B z : ℝ) : ℂ))) μ‖
      ≤ ‖deriv (deriv (fun z : ℝ => psiA P z)) μ * ((cutoff τ B μ : ℝ) : ℂ)
          + 2 * (deriv (fun z : ℝ => psiA P z) μ
              * deriv (fun z : ℝ => ((cutoff τ B z : ℝ) : ℂ)) μ)‖
        + ‖psiA P μ * deriv (deriv (fun z : ℝ => ((cutoff τ B z : ℝ) : ℂ))) μ‖ :=
        norm_add_le _ _
    _ ≤ (‖deriv (deriv (fun z : ℝ => psiA P z)) μ * ((cutoff τ B μ : ℝ) : ℂ)‖
          + ‖2 * (deriv (fun z : ℝ => psiA P z) μ
              * deriv (fun z : ℝ => ((cutoff τ B z : ℝ) : ℂ)) μ)‖)
        + ‖psiA P μ * deriv (deriv (fun z : ℝ => ((cutoff τ B z : ℝ) : ℂ))) μ‖ :=
        add_le_add (norm_add_le _ _) le_rfl
    _ ≤ (M2 * 1 + 2 * (M1 * N1)) + (ε + B * M1) * N2 :=
        add_le_add (add_le_add t1 t2') t3
    _ = M2 + 2 * (M1 * N1) + (ε + B * M1) * N2 := by ring

/-- **(2) 点态界（全体实数，一般常数）**：`|μ| > τ + B` 时 `Ψ ≡ 0` 从而 `Ψ''(μ) = 0`，
故带内点态界其实对所有 `μ` 成立。 -/
lemma norm_deriv2_psi_le_gen_all (τ B : ℝ) (hτ : 0 < τ) (hB : 0 < B) (P : Polynomial ℂ)
    {ε M1 M2 N1 N2 : ℝ} (hε : 0 ≤ ε)
    (hPε : ∀ μ : ℝ, |μ| ≤ τ → ‖Complex.exp (-(μ : ℂ) * Complex.I) - P.eval ((μ : ℂ))‖ ≤ ε)
    (hA1 : ∀ μ : ℝ, |μ| ≤ τ + B → ‖deriv (fun x : ℝ => psiA P x) μ‖ ≤ M1)
    (hA2 : ∀ μ : ℝ, |μ| ≤ τ + B → ‖deriv (deriv (fun x : ℝ => psiA P x)) μ‖ ≤ M2)
    (hK1 : ∀ μ : ℝ, ‖deriv (cutoff τ B) μ‖ ≤ N1)
    (hK2 : ∀ μ : ℝ, ‖deriv (deriv (cutoff τ B)) μ‖ ≤ N2) :
    ∀ μ : ℝ, ‖deriv (deriv (psi τ B P)) μ‖ ≤ M2 + 2 * (M1 * N1) + (ε + B * M1) * N2 := by
  have hM1nn : 0 ≤ M1 := le_trans (norm_nonneg _) (hA1 0 (by rw [abs_zero]; linarith))
  have hN1nn : 0 ≤ N1 := le_trans (norm_nonneg _) (hK1 0)
  have hN2nn : 0 ≤ N2 := le_trans (norm_nonneg _) (hK2 0)
  have hCnn : 0 ≤ M2 + 2 * (M1 * N1) + (ε + B * M1) * N2 := by
    have h1 : 0 ≤ M1 * N1 := mul_nonneg hM1nn hN1nn
    have h3 : 0 ≤ ε + B * M1 := by linarith [mul_nonneg hB.le hM1nn]
    linarith [mul_nonneg h3 hN2nn, mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) h1,
      le_trans (norm_nonneg _) (hA2 0 (by rw [abs_zero]; linarith))]
  intro μ
  rcases le_or_gt |μ| (τ + B) with h | h
  · exact norm_deriv2_psi_le_gen τ B hτ hB P hε hPε hA1 hA2 hK1 hK2 μ h
  · rw [deriv2_psi_eq_zero_of_lt_abs hB P h, norm_zero]
    exact hCnn

/-- 题面所给形式的点态界（`N1 := M1/B`、`N2 := M2/B²`），对**所有** `μ` 成立。 -/
lemma norm_deriv2_psi_le_all (τ B : ℝ) (hτ : 0 < τ) (hB : 0 < B) (P : Polynomial ℂ)
    {ε M1 M2 : ℝ} (hε : 0 ≤ ε)
    (hPε : ∀ μ : ℝ, |μ| ≤ τ → ‖Complex.exp (-(μ : ℂ) * Complex.I) - P.eval ((μ : ℂ))‖ ≤ ε)
    (hA1 : ∀ μ : ℝ, |μ| ≤ τ + B → ‖deriv (fun x : ℝ => psiA P x) μ‖ ≤ M1)
    (hA2 : ∀ μ : ℝ, |μ| ≤ τ + B → ‖deriv (deriv (fun x : ℝ => psiA P x)) μ‖ ≤ M2)
    (hK1 : ∀ μ : ℝ, ‖deriv (cutoff τ B) μ‖ ≤ M1 / B)
    (hK2 : ∀ μ : ℝ, ‖deriv (deriv (cutoff τ B)) μ‖ ≤ M2 / B ^ 2) :
    ∀ μ : ℝ, ‖deriv (deriv (psi τ B P)) μ‖
      ≤ M2 + 2 * (M1 * (M1 / B)) + (ε + B * M1) * (M2 / B ^ 2) :=
  norm_deriv2_psi_le_gen_all τ B hτ hB P hε hPε hA1 hA2 hK1 hK2

/-- **(2) 点态界（题面签名）**：`|μ| ≤ τ + B` 时
`‖Ψ''(μ)‖ ≤ M2 + 2·M1·(M1/B) + (ε + B·M1)·(M2/B²)`。

（常数说明：乘积法则给出 `‖Ψ''‖ ≤ ‖Ψ_A''‖·‖χ‖ + 2‖Ψ_A'‖·‖χ'‖ + ‖Ψ_A‖·‖χ''‖`；
在题面假设 `‖χ'‖ ≤ M1/B`、`‖χ''‖ ≤ M2/B²` 下逐项放缩得
`M2·1 + 2·M1·(M1/B) + (ε + B·M1)·(M2/B²)`。它与题面写的 `M2 + 2M1/B + ε/B²` 不同：
这些假设下真实系数必然是乘积项 `M1·(M1/B)` 与 `(ε + B·M1)·(M2/B²)`。
若需要「干净」常数，请用 `norm_deriv2_psi_le_gen_all`（`N1, N2` 与 `M1, M2` 独立）。） -/
lemma norm_deriv2_psi_le (τ B : ℝ) (hτ : 0 < τ) (hB : 0 < B) (P : Polynomial ℂ)
    {ε M1 M2 : ℝ} (hε : 0 ≤ ε)
    (hPε : ∀ μ : ℝ, |μ| ≤ τ → ‖Complex.exp (-(μ : ℂ) * Complex.I) - P.eval ((μ : ℂ))‖ ≤ ε)
    (hA1 : ∀ μ : ℝ, |μ| ≤ τ + B → ‖deriv (fun x : ℝ => psiA P x) μ‖ ≤ M1)
    (hA2 : ∀ μ : ℝ, |μ| ≤ τ + B → ‖deriv (deriv (fun x : ℝ => psiA P x)) μ‖ ≤ M2)
    (hK1 : ∀ μ : ℝ, ‖deriv (cutoff τ B) μ‖ ≤ M1 / B)
    (hK2 : ∀ μ : ℝ, ‖deriv (deriv (cutoff τ B)) μ‖ ≤ M2 / B ^ 2) :
    ∀ μ : ℝ, |μ| ≤ τ + B →
      ‖deriv (deriv (psi τ B P)) μ‖
        ≤ M2 + 2 * (M1 * (M1 / B)) + (ε + B * M1) * (M2 / B ^ 2) :=
  fun μ _ => norm_deriv2_psi_le_all τ B hτ hB P hε hPε hA1 hA2 hK1 hK2 μ

/-- **(2) 积分界（一般常数）**：`∫_{-(τ+B+1)}^{τ+B+1} ‖Ψ''‖ ≤ (区间长)·sup‖Ψ''‖`。 -/
lemma integral_norm_deriv2_psi_le_gen (τ B : ℝ) (hτ : 0 < τ) (hB : 0 < B) (P : Polynomial ℂ)
    {ε M1 M2 N1 N2 : ℝ} (hε : 0 ≤ ε)
    (hPε : ∀ μ : ℝ, |μ| ≤ τ → ‖Complex.exp (-(μ : ℂ) * Complex.I) - P.eval ((μ : ℂ))‖ ≤ ε)
    (hA1 : ∀ μ : ℝ, |μ| ≤ τ + B → ‖deriv (fun x : ℝ => psiA P x) μ‖ ≤ M1)
    (hA2 : ∀ μ : ℝ, |μ| ≤ τ + B → ‖deriv (deriv (fun x : ℝ => psiA P x)) μ‖ ≤ M2)
    (hK1 : ∀ μ : ℝ, ‖deriv (cutoff τ B) μ‖ ≤ N1)
    (hK2 : ∀ μ : ℝ, ‖deriv (deriv (cutoff τ B)) μ‖ ≤ N2) :
    ∫ μ in (-(τ + B + 1))..(τ + B + 1), ‖deriv (deriv (psi τ B P)) μ‖
      ≤ 2 * (τ + B + 1) * (M2 + 2 * (M1 * N1) + (ε + B * M1) * N2) := by
  have hpoint := norm_deriv2_psi_le_gen_all τ B hτ hB P hε hPε hA1 hA2 hK1 hK2
  have hnn : 0 ≤ ∫ μ in (-(τ + B + 1))..(τ + B + 1), ‖deriv (deriv (psi τ B P)) μ‖ :=
    intervalIntegral.integral_nonneg (by linarith) (fun u _ => norm_nonneg _)
  have hle : ‖∫ μ in (-(τ + B + 1))..(τ + B + 1), ‖deriv (deriv (psi τ B P)) μ‖‖
      ≤ (M2 + 2 * (M1 * N1) + (ε + B * M1) * N2) * |(τ + B + 1) - (-(τ + B + 1))| :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun μ : ℝ => ‖deriv (deriv (psi τ B P)) μ‖)
      (a := -(τ + B + 1)) (b := τ + B + 1)
      (C := M2 + 2 * (M1 * N1) + (ε + B * M1) * N2)
      (fun x _ => by simpa using hpoint x)
  calc ∫ μ in (-(τ + B + 1))..(τ + B + 1), ‖deriv (deriv (psi τ B P)) μ‖
      = ‖∫ μ in (-(τ + B + 1))..(τ + B + 1), ‖deriv (deriv (psi τ B P)) μ‖‖ :=
        (Real.norm_of_nonneg hnn).symm
    _ ≤ (M2 + 2 * (M1 * N1) + (ε + B * M1) * N2) * |(τ + B + 1) - (-(τ + B + 1))| := hle
    _ = 2 * (τ + B + 1) * (M2 + 2 * (M1 * N1) + (ε + B * M1) * N2) := by
        rw [abs_of_nonneg (by linarith)]
        ring

/-- **(2) 积分界（题面签名）**：
`∫_{-(τ+B+1)}^{τ+B+1} ‖Ψ''‖ ≤ 2(τ+B+1)·(M2 + 2·M1·(M1/B) + (ε + B·M1)·(M2/B²))`，
端点 `±(τ+B+1)` 严格包住 `Ψ` 的支撑 `±(τ+B)`。 -/
lemma integral_norm_deriv2_psi_le (τ B : ℝ) (hτ : 0 < τ) (hB : 0 < B) (P : Polynomial ℂ)
    {ε M1 M2 : ℝ} (hε : 0 ≤ ε)
    (hPε : ∀ μ : ℝ, |μ| ≤ τ → ‖Complex.exp (-(μ : ℂ) * Complex.I) - P.eval ((μ : ℂ))‖ ≤ ε)
    (hA1 : ∀ μ : ℝ, |μ| ≤ τ + B → ‖deriv (fun x : ℝ => psiA P x) μ‖ ≤ M1)
    (hA2 : ∀ μ : ℝ, |μ| ≤ τ + B → ‖deriv (deriv (fun x : ℝ => psiA P x)) μ‖ ≤ M2)
    (hK1 : ∀ μ : ℝ, ‖deriv (cutoff τ B) μ‖ ≤ M1 / B)
    (hK2 : ∀ μ : ℝ, ‖deriv (deriv (cutoff τ B)) μ‖ ≤ M2 / B ^ 2) :
    ∫ μ in (-(τ + B + 1))..(τ + B + 1), ‖deriv (deriv (psi τ B P)) μ‖
      ≤ 2 * (τ + B + 1) * (M2 + 2 * (M1 * (M1 / B)) + (ε + B * M1) * (M2 / B ^ 2)) :=
  integral_norm_deriv2_psi_le_gen τ B hτ hB P hε hPε hA1 hA2 hK1 hK2
/-! ### (2′) 支撑感知的 `L¹` 估计（修正 `∫‖Ψ''‖`）

`χ'`、`χ''` 只在两条长度 `B` 的 taper 带 `[τ, τ+B] ∪ [−τ−B, −τ]` 上非零
（`|μ| < τ` 上 `χ ≡ 1`，`|μ| > τ + B` 上 `χ ≡ 0`），所以
`∫‖χ'‖ = O(K)`、`∫‖χ''‖ = O(K/B)`。把 `‖χ'‖ ≤ K/B` 在整个 `[-(τ+B+1), τ+B+1]`
（长度 `2(τ+B+1)`）上直接积分会多出 `(τ+B)/B` 的因子，取 `B = √ε` 后不趋于 0，
因此支撑感知的估计是 M3 组装所必需的。 -/

/-- 辅助：`|y - x| < τ - |x|` 时 `|y| < τ`。 -/
lemma abs_lt_of_abs_sub_lt {x y τ : ℝ} (h : |y - x| < τ - |x|) : |y| < τ := by
  have h2 : |y| ≤ |x| + |y - x| := by
    calc |y| = |x + (y - x)| := by
          congr 1
          ring
      _ ≤ |x| + |y - x| := abs_add_le x (y - x)
  linarith

/-- `|x| < τ` 时 `χ ≡ 1`（在 `x` 的一个邻域上），故 `χ'(x) = 0`。 -/
lemma deriv_cutoff_eq_zero_of_abs_lt {τ B x : ℝ} (hB : 0 < B) (h : |x| < τ) :
    deriv (cutoff τ B) x = 0 := by
  have hx : cutoff τ B =ᶠ[nhds x] fun _ => (1 : ℝ) := by
    filter_upwards [Metric.ball_mem_nhds x (by linarith : 0 < τ - |x|)] with y hy
    rw [Metric.mem_ball, Real.dist_eq] at hy
    exact cutoff_eq_one hB (le_of_lt (abs_lt_of_abs_sub_lt hy))
  rw [Filter.EventuallyEq.deriv_eq hx]
  simp

/-- `τ + B < |x|` 时 `χ ≡ 0`（在 `x` 的一个邻域上），故 `χ'(x) = 0`。 -/
lemma deriv_cutoff_eq_zero_of_lt_abs {τ B x : ℝ} (hB : 0 < B) (h : τ + B < |x|) :
    deriv (cutoff τ B) x = 0 := by
  have hopen : IsOpen {y : ℝ | τ + B < |y|} := isOpen_lt continuous_const continuous_abs
  have hx : cutoff τ B =ᶠ[nhds x] fun _ => (0 : ℝ) := by
    filter_upwards [hopen.mem_nhds h] with y hy
    exact cutoff_eq_zero hB (le_of_lt hy)
  rw [Filter.EventuallyEq.deriv_eq hx]
  simp

/-- `|x| < τ` 时 `χ''(x) = 0`。 -/
lemma deriv_deriv_cutoff_eq_zero_of_abs_lt {τ B x : ℝ} (hB : 0 < B) (h : |x| < τ) :
    deriv (deriv (cutoff τ B)) x = 0 := by
  have hx : deriv (cutoff τ B) =ᶠ[nhds x] fun _ => (0 : ℝ) := by
    filter_upwards [Metric.ball_mem_nhds x (by linarith : 0 < τ - |x|)] with y hy
    rw [Metric.mem_ball, Real.dist_eq] at hy
    exact deriv_cutoff_eq_zero_of_abs_lt hB (abs_lt_of_abs_sub_lt hy)
  rw [Filter.EventuallyEq.deriv_eq hx]
  simp

/-- `τ + B < |x|` 时 `χ''(x) = 0`。 -/
lemma deriv_deriv_cutoff_eq_zero_of_lt_abs {τ B x : ℝ} (hB : 0 < B) (h : τ + B < |x|) :
    deriv (deriv (cutoff τ B)) x = 0 := by
  have hopen : IsOpen {y : ℝ | τ + B < |y|} := isOpen_lt continuous_const continuous_abs
  have hx : deriv (cutoff τ B) =ᶠ[nhds x] fun _ => (0 : ℝ) := by
    filter_upwards [hopen.mem_nhds h] with y hy
    exact deriv_cutoff_eq_zero_of_lt_abs hB hy
  rw [Filter.EventuallyEq.deriv_eq hx]
  simp

/-- **支撑估计**：`f ≥ 0`、`f ≤ C`，且在 `|μ| < τ` 与 `|μ| > τ + B` 上 `f = 0`；
则 `∫_{-(τ+B+1)}^{τ+B+1} f ≤ 2·B·C`（只有两条长度 `B` 的 taper 带有贡献）。 -/
lemma intervalIntegral_le_two_mul_mul_of_support {τ B C : ℝ} (hτ : 0 ≤ τ) (hB : 0 < B)
    {f : ℝ → ℝ} (hcont : Continuous f) (hbound : ∀ μ, f μ ≤ C)
    (hnonneg : ∀ μ, 0 ≤ f μ) (hzero_in : ∀ μ, |μ| < τ → f μ = 0)
    (hzero_out : ∀ μ, τ + B < |μ| → f μ = 0) :
    ∫ μ in (-(τ + B + 1))..(τ + B + 1), f μ ≤ 2 * B * C := by
  have h1 : ∫ μ in (-(τ + B + 1))..(-(τ + B)), f μ = 0 := by
    rw [intervalIntegral.integral_congr_uIoo (g := fun _ : ℝ => (0 : ℝ)) ?_,
      intervalIntegral.integral_zero]
    intro x hx
    rw [Set.uIoo_of_le (by linarith : -(τ + B + 1) ≤ -(τ + B)), Set.mem_Ioo] at hx
    refine hzero_out x ?_
    rw [abs_of_neg (by linarith [hx.2])]
    linarith [hx.2]
  have h2 : ∫ μ in (-(τ + B))..(-τ), f μ ≤ C * B := by
    have hle := intervalIntegral.norm_integral_le_of_norm_le_const (f := f)
      (a := -(τ + B)) (b := -τ) (C := C) (fun x _ => by
        rw [Real.norm_of_nonneg (hnonneg x)]
        exact hbound x)
    have hnn : 0 ≤ ∫ μ in (-(τ + B))..(-τ), f μ :=
      intervalIntegral.integral_nonneg (by linarith) (fun u _ => hnonneg u)
    rw [Real.norm_of_nonneg hnn] at hle
    refine le_trans hle (le_of_eq ?_)
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ -τ - (-(τ + B)))]
    ring
  have h3 : ∫ μ in (-τ)..τ, f μ = 0 := by
    rw [intervalIntegral.integral_congr_uIoo (g := fun _ : ℝ => (0 : ℝ)) ?_,
      intervalIntegral.integral_zero]
    intro x hx
    rw [Set.uIoo_of_le (by linarith : -τ ≤ τ), Set.mem_Ioo] at hx
    exact hzero_in x (by rw [abs_lt]; exact hx)
  have h4 : ∫ μ in τ..(τ + B), f μ ≤ C * B := by
    have hle := intervalIntegral.norm_integral_le_of_norm_le_const (f := f)
      (a := τ) (b := τ + B) (C := C) (fun x _ => by
        rw [Real.norm_of_nonneg (hnonneg x)]
        exact hbound x)
    have hnn : 0 ≤ ∫ μ in τ..(τ + B), f μ :=
      intervalIntegral.integral_nonneg (by linarith) (fun u _ => hnonneg u)
    rw [Real.norm_of_nonneg hnn] at hle
    refine le_trans hle (le_of_eq ?_)
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ τ + B - τ)]
    ring
  have h5 : ∫ μ in (τ + B)..(τ + B + 1), f μ = 0 := by
    rw [intervalIntegral.integral_congr_uIoo (g := fun _ : ℝ => (0 : ℝ)) ?_,
      intervalIntegral.integral_zero]
    intro x hx
    rw [Set.uIoo_of_le (by linarith : τ + B ≤ τ + B + 1), Set.mem_Ioo] at hx
    refine hzero_out x ?_
    rw [abs_of_pos (by linarith [hx.1])]
    linarith [hx.1]
  have hI1 : IntervalIntegrable f volume (-(τ + B + 1)) (-(τ + B)) := hcont.intervalIntegrable _ _
  have hI2 : IntervalIntegrable f volume (-(τ + B)) (-τ) := hcont.intervalIntegrable _ _
  have hI3 : IntervalIntegrable f volume (-τ) τ := hcont.intervalIntegrable _ _
  have hI4 : IntervalIntegrable f volume τ (τ + B) := hcont.intervalIntegrable _ _
  have hI5 : IntervalIntegrable f volume (τ + B) (τ + B + 1) := hcont.intervalIntegrable _ _
  have hI25 : IntervalIntegrable f volume (-(τ + B)) (τ + B + 1) :=
    hcont.intervalIntegrable _ _
  have hI35 : IntervalIntegrable f volume (-τ) (τ + B + 1) := hcont.intervalIntegrable _ _
  have hI45 : IntervalIntegrable f volume τ (τ + B + 1) := hcont.intervalIntegrable _ _
  have hI15 : IntervalIntegrable f volume (-(τ + B + 1)) (τ + B + 1) :=
    hcont.intervalIntegrable _ _
  have A1 := intervalIntegral.integral_add_adjacent_intervals hI1 hI25
  have A2 := intervalIntegral.integral_add_adjacent_intervals hI2 hI35
  have A3 := intervalIntegral.integral_add_adjacent_intervals hI3 hI45
  have A4 := intervalIntegral.integral_add_adjacent_intervals hI4 hI5
  have hsum : ∫ μ in (-(τ + B + 1))..(τ + B + 1), f μ
      = (∫ μ in (-(τ + B + 1))..(-(τ + B)), f μ) + (∫ μ in (-(τ + B))..(-τ), f μ)
        + (∫ μ in (-τ)..τ, f μ) + (∫ μ in τ..(τ + B), f μ)
        + ∫ μ in (τ + B)..(τ + B + 1), f μ := by linarith
  linarith [h1, h2, h3, h4, h5, hsum, abs_nonneg (0 : ℝ)]

/-- `χ'` 的 `L¹` 范数只有 `O(K)`（与 `B` 无关）：支撑只有总长 `2B` 的两条 taper 带。 -/
lemma integral_norm_deriv_cutoff_le (τ B : ℝ) (hτ : 0 < τ) (hB : 0 < B) {K : ℝ}
    (hK : ∀ μ, |deriv (cutoff τ B) μ| ≤ K / B) :
    ∫ μ in (-(τ + B + 1))..(τ + B + 1), ‖deriv (fun x : ℝ => ((cutoff τ B x : ℝ) : ℂ)) μ‖ ≤ 2 * K := by
  have hcont : Continuous (fun μ : ℝ => ‖deriv (fun x : ℝ => ((cutoff τ B x : ℝ) : ℂ)) μ‖) := by
    have h1 : Continuous (deriv (cutoff τ B)) :=
      (contDiff_cutoff τ B hτ hB).continuous_deriv (by norm_num)
    have h2 : Continuous (fun μ : ℝ => ((deriv (cutoff τ B) μ : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp h1
    have h3 := h2.norm
    simpa only [deriv_coe_cutoff τ B hτ hB] using h3
  have hbound : ∀ μ : ℝ,
      ‖deriv (fun x : ℝ => ((cutoff τ B x : ℝ) : ℂ)) μ‖ ≤ K / B := by
    intro μ
    rw [deriv_coe_cutoff τ B hτ hB, Complex.norm_real, Real.norm_eq_abs]
    exact hK μ
  have hzero_in : ∀ μ : ℝ, |μ| < τ →
      ‖deriv (fun x : ℝ => ((cutoff τ B x : ℝ) : ℂ)) μ‖ = 0 := by
    intro μ hμ
    rw [deriv_coe_cutoff τ B hτ hB, Complex.norm_real, Real.norm_eq_abs,
      deriv_cutoff_eq_zero_of_abs_lt hB hμ, abs_zero]
  have hzero_out : ∀ μ : ℝ, τ + B < |μ| →
      ‖deriv (fun x : ℝ => ((cutoff τ B x : ℝ) : ℂ)) μ‖ = 0 := by
    intro μ hμ
    rw [deriv_coe_cutoff τ B hτ hB, Complex.norm_real, Real.norm_eq_abs,
      deriv_cutoff_eq_zero_of_lt_abs hB hμ, abs_zero]
  have hmain := intervalIntegral_le_two_mul_mul_of_support hτ.le hB hcont hbound
    (fun μ => norm_nonneg _) hzero_in hzero_out
  refine le_trans hmain (le_of_eq ?_)
  field_simp

/-- `χ''` 的 `L¹` 范数只有 `O(K/B)`：同样只有总长 `2B` 的两条 taper 带。 -/
lemma integral_norm_deriv2_cutoff_le (τ B : ℝ) (hτ : 0 < τ) (hB : 0 < B) {K : ℝ}
    (hK : ∀ μ, |deriv (deriv (cutoff τ B)) μ| ≤ K / B ^ 2) :
    ∫ μ in (-(τ + B + 1))..(τ + B + 1),
      ‖deriv (deriv (fun x : ℝ => ((cutoff τ B x : ℝ) : ℂ))) μ‖ ≤ 4 * K / B := by
  have hC : 0 ≤ K / B ^ 2 := le_trans (abs_nonneg _) (hK 0)
  have hKnn : 0 ≤ K := by
    have hB2 : (0 : ℝ) < B ^ 2 := by positivity
    have h := mul_nonneg hC hB2.le
    rwa [div_mul_cancel₀ _ (ne_of_gt hB2)] at h
  have hcont : Continuous
      (fun μ : ℝ => ‖deriv (deriv (fun x : ℝ => ((cutoff τ B x : ℝ) : ℂ))) μ‖) := by
    have h1 : Continuous (deriv (deriv (cutoff τ B))) := by
      have h2 : ContDiff ℝ ((1 : WithTop ℕ∞) + 1) (cutoff τ B) := by
        rw [show ((1 : WithTop ℕ∞) + 1) = 2 from by norm_num]
        exact contDiff_cutoff τ B hτ hB
      exact h2.deriv'.continuous_deriv le_rfl
    have h2 : Continuous (fun μ : ℝ => ((deriv (deriv (cutoff τ B)) μ : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp h1
    have h3 := h2.norm
    simpa only [deriv_deriv_coe_cutoff τ B hτ hB] using h3
  have hbound : ∀ μ : ℝ,
      ‖deriv (deriv (fun x : ℝ => ((cutoff τ B x : ℝ) : ℂ))) μ‖ ≤ K / B ^ 2 := by
    intro μ
    rw [deriv_deriv_coe_cutoff τ B hτ hB, Complex.norm_real, Real.norm_eq_abs]
    exact hK μ
  have hzero_in : ∀ μ : ℝ, |μ| < τ →
      ‖deriv (deriv (fun x : ℝ => ((cutoff τ B x : ℝ) : ℂ))) μ‖ = 0 := by
    intro μ hμ
    rw [deriv_deriv_coe_cutoff τ B hτ hB, Complex.norm_real, Real.norm_eq_abs,
      deriv_deriv_cutoff_eq_zero_of_abs_lt hB hμ, abs_zero]
  have hzero_out : ∀ μ : ℝ, τ + B < |μ| →
      ‖deriv (deriv (fun x : ℝ => ((cutoff τ B x : ℝ) : ℂ))) μ‖ = 0 := by
    intro μ hμ
    rw [deriv_deriv_coe_cutoff τ B hτ hB, Complex.norm_real, Real.norm_eq_abs,
      deriv_deriv_cutoff_eq_zero_of_lt_abs hB hμ, abs_zero]
  have hmain := intervalIntegral_le_two_mul_mul_of_support hτ.le hB hcont hbound
    (fun μ => norm_nonneg _) hzero_in hzero_out
  refine le_trans hmain ?_
  calc 2 * B * (K / B ^ 2) = 2 * K / B := by field_simp
    _ ≤ 4 * K / B := by
        apply div_le_div_of_nonneg_right _ hB.le
        linarith

/-! #### `Ψ` 的 `C²` 性（用于积分可积性） -/

/-- 多项式（复系数）沿实轴求值是 `C^∞` 的。 -/
lemma contDiff_poly_eval_real (P : Polynomial ℂ) :
    ContDiff ℝ ⊤ (fun μ : ℝ => P.eval ((μ : ℂ))) := by
  have hfun : (fun μ : ℝ => P.eval ((μ : ℂ)))
      = fun μ : ℝ => ∑ e ∈ P.support, P.coeff e * (μ : ℂ) ^ e := by
    funext μ
    rw [Polynomial.eval_eq_sum]
    rfl
  rw [hfun]
  exact ContDiff.sum fun e _ => contDiff_const.mul ((Complex.ofRealCLM.contDiff (n := ⊤)).pow e)

lemma contDiff_exp_mul_I :
    ContDiff ℝ ⊤ (fun μ : ℝ => Complex.exp ((μ : ℂ) * Complex.I)) :=
  ((Complex.ofRealCLM.contDiff (n := ⊤)).mul contDiff_const).cexp

lemma contDiffPsiA (P : Polynomial ℂ) : ContDiff ℝ ⊤ (fun μ : ℝ => psiA P μ) := by
  have hfun : (fun μ : ℝ => psiA P μ)
      = fun μ : ℝ => 1 - P.eval ((μ : ℂ)) * Complex.exp ((μ : ℂ) * Complex.I) := by
    funext μ
    rw [psiA]
  rw [hfun]
  exact contDiff_const.sub ((contDiff_poly_eval_real P).mul contDiff_exp_mul_I)

lemma contDiffPsi (τ B : ℝ) (hτ : 0 < τ) (hB : 0 < B) (P : Polynomial ℂ) :
    ContDiff ℝ 2 (psi τ B P) := by
  have hfun : psi τ B P
      = (fun μ : ℝ => psiA P μ) * (fun μ : ℝ => ((cutoff τ B μ : ℝ) : ℂ)) := by
    funext x
    rw [psi]
    rfl
  rw [hfun]
  exact ((contDiffPsiA P).of_le le_top).mul (contDiff_coe_cutoff τ B hτ hB)

lemma continuous_deriv2_psi (τ B : ℝ) (hτ : 0 < τ) (hB : 0 < B) (P : Polynomial ℂ) :
    Continuous (deriv (deriv (psi τ B P))) := by
  have h2 : ContDiff ℝ ((1 : WithTop ℕ∞) + 1) (psi τ B P) := by
    rw [show ((1 : WithTop ℕ∞) + 1) = 2 from by norm_num]
    exact contDiffPsi τ B hτ hB P
  exact h2.deriv'.continuous_deriv le_rfl

/-- `(Ψ_A·χ)'' = Ψ_A''·χ + 2·Ψ_A'·χ' + Ψ_A·χ''`（逐点恒等式）。 -/
lemma deriv2_psi_eq (τ B : ℝ) (hτ : 0 < τ) (hB : 0 < B) (P : Polynomial ℂ) (μ : ℝ) :
    deriv (deriv (psi τ B P)) μ
      = deriv (deriv (fun z : ℝ => psiA P z)) μ * ((cutoff τ B μ : ℝ) : ℂ)
        + 2 * (deriv (fun z : ℝ => psiA P z) μ
            * deriv (fun z : ℝ => ((cutoff τ B z : ℝ) : ℂ)) μ)
        + psiA P μ * deriv (deriv (fun z : ℝ => ((cutoff τ B z : ℝ) : ℂ))) μ := by
  have hA : Differentiable ℝ (fun z : ℝ => psiA P z) := fun z => differentiableAt_psiA P z
  have hK : Differentiable ℝ (fun z : ℝ => ((cutoff τ B z : ℝ) : ℂ)) :=
    fun z => differentiableAt_coe_cutoff τ B hτ hB z
  have hA1 : Differentiable ℝ (deriv (fun z : ℝ => psiA P z)) := by
    rw [deriv_psiA P]
    exact fun z => differentiableAt_dpsiA P z
  have hK1 : Differentiable ℝ (deriv (fun z : ℝ => ((cutoff τ B z : ℝ) : ℂ))) := by
    rw [deriv_coe_cutoff τ B hτ hB]
    exact Complex.differentiable_ofReal.comp
      ((contDiff_cutoff τ B hτ hB).differentiable_deriv_two)
  have hpsiK : psi τ B P
      = (fun z : ℝ => psiA P z) * (fun z : ℝ => ((cutoff τ B z : ℝ) : ℂ)) := by
    funext x
    rw [psi]
    rfl
  rw [hpsiK]
  exact deriv_deriv_mul _ _ hA hK hA1 hK1 μ

/-- **(2″) 支撑感知的 `∫‖Ψ''‖` 界（一般 `L¹` 常数版）**：
三项分别按各自支撑积分，
`∫‖Ψ_A''·χ‖ ≤ 2(τ+B+1)·M2`、`∫‖2Ψ_A'·χ'‖ ≤ 2·M1·L1`、`∫‖Ψ_A·χ''‖ ≤ (ε+B·M1)·L2`。 -/
lemma integral_norm_deriv2_psi_le_sharp_gen (τ B : ℝ) (hτ : 0 < τ) (hB : 0 < B)
    (P : Polynomial ℂ) {ε M1 M2 L1 L2 : ℝ} (hε : 0 ≤ ε)
    (hPε : ∀ μ : ℝ, |μ| ≤ τ → ‖Complex.exp (-(μ : ℂ) * Complex.I) - P.eval ((μ : ℂ))‖ ≤ ε)
    (hA1 : ∀ μ : ℝ, |μ| ≤ τ + B → ‖deriv (fun x : ℝ => psiA P x) μ‖ ≤ M1)
    (hA2 : ∀ μ : ℝ, |μ| ≤ τ + B → ‖deriv (deriv (fun x : ℝ => psiA P x)) μ‖ ≤ M2)
    (hL1 : ∫ μ in (-(τ + B + 1))..(τ + B + 1),
      ‖deriv (fun x : ℝ => ((cutoff τ B x : ℝ) : ℂ)) μ‖ ≤ L1)
    (hL2 : ∫ μ in (-(τ + B + 1))..(τ + B + 1),
      ‖deriv (deriv (fun x : ℝ => ((cutoff τ B x : ℝ) : ℂ))) μ‖ ≤ L2) :
    ∫ μ in (-(τ + B + 1))..(τ + B + 1), ‖deriv (deriv (psi τ B P)) μ‖
      ≤ 2 * (τ + B + 1) * M2 + 2 * (M1 * L1) + (ε + B * M1) * L2 := by
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
  have I1 : ∫ μ in (-(τ + B + 1))..(τ + B + 1), G1 μ ≤ 2 * (τ + B + 1) * M2 := by
    have hle := intervalIntegral.norm_integral_le_of_norm_le_const (f := G1)
      (a := -(τ + B + 1)) (b := τ + B + 1) (C := M2) (fun x _ => by
        rw [Real.norm_of_nonneg (norm_nonneg _)]
        exact hb1 x)
    have hnn : 0 ≤ ∫ μ in (-(τ + B + 1))..(τ + B + 1), G1 μ :=
      intervalIntegral.integral_nonneg (by linarith) (fun u _ => norm_nonneg _)
    rw [Real.norm_of_nonneg hnn] at hle
    refine le_trans hle (le_of_eq ?_)
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ τ + B + 1 - (-(τ + B + 1)))]
    ring
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
    _ ≤ 2 * (τ + B + 1) * M2 + 2 * (M1 * L1) + (ε + B * M1) * L2 := by
        linarith [I1, I2, I3]

/-- **(2‴) 修正版 `∫‖Ψ''‖` 界（`K` 形式）**：`χ'`、`χ''` 的导数界为 `K/B`、`K/B²` 时，
`∫‖Ψ''‖ ≤ 2(τ+B+1)·M2 + 2·M1·(2K) + (ε + B·M1)·(4K/B)`。

与旧版 `integral_norm_deriv2_psi_le` 的区别：`χ` 的导数只在总长 `2B` 的 taper 带上积分，
因此不出现 `K/B²` 量级的损失（在 `B = √ε` 时 `K/B² = K/ε` 是致命的）。 -/
lemma integral_norm_deriv2_psi_le_sharp (τ B : ℝ) (hτ : 0 < τ) (hB : 0 < B) (P : Polynomial ℂ)
    {ε M1 M2 K : ℝ} (hε : 0 ≤ ε)
    (hPε : ∀ μ : ℝ, |μ| ≤ τ → ‖Complex.exp (-(μ : ℂ) * Complex.I) - P.eval ((μ : ℂ))‖ ≤ ε)
    (hA1 : ∀ μ : ℝ, |μ| ≤ τ + B → ‖deriv (fun x : ℝ => psiA P x) μ‖ ≤ M1)
    (hA2 : ∀ μ : ℝ, |μ| ≤ τ + B → ‖deriv (deriv (fun x : ℝ => psiA P x)) μ‖ ≤ M2)
    (hK1 : ∀ μ : ℝ, ‖deriv (fun x : ℝ => ((cutoff τ B x : ℝ) : ℂ)) μ‖ ≤ K / B)
    (hK2 : ∀ μ : ℝ, ‖deriv (deriv (fun x : ℝ => ((cutoff τ B x : ℝ) : ℂ))) μ‖ ≤ K / B ^ 2) :
    ∫ μ in (-(τ + B + 1))..(τ + B + 1), ‖deriv (deriv (psi τ B P)) μ‖
      ≤ 2 * (τ + B + 1) * M2 + 2 * (M1 * (2 * K)) + (ε + B * M1) * (4 * K / B) := by
  have hK1' : ∀ μ : ℝ, |deriv (cutoff τ B) μ| ≤ K / B := by
    intro μ
    have h := hK1 μ
    rwa [deriv_coe_cutoff τ B hτ hB, Complex.norm_real, Real.norm_eq_abs] at h
  have hK2' : ∀ μ : ℝ, |deriv (deriv (cutoff τ B)) μ| ≤ K / B ^ 2 := by
    intro μ
    have h := hK2 μ
    rwa [deriv_deriv_coe_cutoff τ B hτ hB, Complex.norm_real, Real.norm_eq_abs] at h
  exact integral_norm_deriv2_psi_le_sharp_gen τ B hτ hB P hε hPε hA1 hA2
    (integral_norm_deriv_cutoff_le τ B hτ hB hK1')
    (integral_norm_deriv2_cutoff_le τ B hτ hB hK2')

end RobustZ
