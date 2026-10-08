/-
# Realization lemma (Theorem 2.1 / L3): Hermite-collar extension + L¹ kernel bound.

Self-contained real-analysis lemma.  Given a `C²` band function `Ψ` with
`‖Ψ‖ ≤ ε`, `‖Ψ'‖ ≤ D₁`, `‖Ψ''‖ ≤ D₂` on `[−τ, τ]` and a `C²` cutoff `χ`
(`χ ≡ 1` on the band, `χ ≡ 0` outside `[−(τ+B), τ+B]`, `|χ'| ≤ K/B`,
`|χ''| ≤ K/B²`, `|χ| ≤ 1` — taken as a hypothesis bundle, never constructed),
we build the Hermite-cubic extension `Ψ_ext` on the two collars

  `η(s) = 1 − 3s² + 2s³`,  `η₁(s) = s(1−s)²`,

set `κ̂ := Ψ_ext · χ` and `κ(t) := (2π)⁻¹ ∫ κ̂(μ) e^{−iμt} dμ`, and prove

  `κ̂ = Ψ` on the band,  `κ ∈ L¹`,  `‖κ‖₁ ≤ (2/π) √(A·C)`

with the EXPLICIT majorants (derived from scratch; every collar integral is
counted TWICE — one term per collar)

  `A := 2(τ+B)(ε + (4/27)·B·D₁)`,
  `C := 2τ·D₂ + 2·((6+4K)·ε/B + (4+2K+4K/27)·D₁)`.

Deviations from the report glosses (see also LEAN_READY.md L3):
* The proof uses only the sup bounds on `Ψ`; the polynomial origin of `Ψ`
  (`Ψ = e^{−i·} − P`) and the side condition `q ≥ 4` play no role and are not
  assumed.  No `S = ∑|c_k|` / `κ₀` quantities appear.
* `κ̂ = Ψ` on the band is proved as an identity of the constructed `κ̂`
  (by construction `χ ≡ 1` there).  The restated form
  `∫ κ(t) e^{iμt} dt = Ψ(μ)` (Fourier inversion) is NOT formalized.
* `K` is kept symbolic (only `0 ≤ K` is used); `K = 4` is the admissible value.
-/
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Calculus.ContDiff.Deriv

noncomputable section

namespace RobustZ
namespace Realize

open Filter MeasureTheory Classical

/-! ## 1. Hermite cubics and their explicit bounds on `[0, 1]`. -/

/-- Hermite cubic `η(s) = 1 − 3s² + 2s³` (value part). -/
def eta (s : ℝ) : ℝ := 1 - 3 * s ^ 2 + 2 * s ^ 3

/-- Hermite cubic `η₁(s) = s(1−s)²` (slope part), expanded form. -/
def eta1 (s : ℝ) : ℝ := s - 2 * s ^ 2 + s ^ 3

/-- `η'(s)`. -/
def etaD (s : ℝ) : ℝ := -6 * s + 6 * s ^ 2

/-- `η₁'(s)`. -/
def eta1D (s : ℝ) : ℝ := 1 - 4 * s + 3 * s ^ 2

/-- `η''(s)`. -/
def etaDD (s : ℝ) : ℝ := -6 + 12 * s

/-- `η₁''(s)`. -/
def eta1DD (s : ℝ) : ℝ := -4 + 6 * s

/-! ### Endpoint values (the Hermite matching conditions). -/

lemma eta_zero : eta 0 = 1 := by simp only [eta]; norm_num

lemma eta_one : eta 1 = 0 := by simp only [eta]; norm_num

lemma eta1_zero : eta1 0 = 0 := by simp only [eta1]; norm_num

lemma eta1_one : eta1 1 = 0 := by simp only [eta1]; norm_num

lemma etaD_zero : etaD 0 = 0 := by simp only [etaD]; norm_num

lemma etaD_one : etaD 1 = 0 := by simp only [etaD]; norm_num

lemma eta1D_zero : eta1D 0 = 1 := by simp only [eta1D]; norm_num

lemma eta1D_one : eta1D 1 = 0 := by simp only [eta1D]; norm_num

/-! ### Sup bounds on `[0, 1]` (each verified from an explicit factorisation). -/

/-- `|η| ≤ 1`: from `1 − η = s²(3−2s)` and `η = (1−s)²(1+2s)`. -/
lemma eta_le_one {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) : eta s ≤ 1 := by
  have h : 1 - eta s = s ^ 2 * (3 - 2 * s) := by simp only [eta]; ring
  have hnn : 0 ≤ s ^ 2 * (3 - 2 * s) :=
    mul_nonneg (sq_nonneg s) (by linarith)
  linarith

lemma eta_nonneg {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) : 0 ≤ eta s := by
  have h : eta s = (1 - s) ^ 2 * (1 + 2 * s) := by simp only [eta]; ring
  rw [h]
  exact mul_nonneg (sq_nonneg _) (by linarith)

lemma eta_abs_le {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) : |eta s| ≤ 1 := by
  rw [abs_le]
  exact ⟨by linarith [eta_nonneg h0 h1], eta_le_one h0 h1⟩

/-- `|η'| ≤ 3/2`: `|η'| = 6s(1−s) ≤ 6/4`, since `s(1−s) ≤ 1/4`. -/
lemma etaD_abs_le {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) : |etaD s| ≤ 3 / 2 := by
  have hnn : 0 ≤ s * (1 - s) := mul_nonneg h0 (by linarith)
  have hub : s * (1 - s) ≤ 1 / 4 := by nlinarith [sq_nonneg (s - 1 / 2)]
  have heq : etaD s = -(6 * (s * (1 - s))) := by simp only [etaD]; ring
  rw [heq, abs_neg]
  have h6 : |6 * (s * (1 - s))| = 6 * (s * (1 - s)) :=
    abs_of_nonneg (by positivity)
  rw [h6]
  linarith

/-- `|η''| ≤ 6` on `[0,1]` (linear). -/
lemma etaDD_abs_le {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) : |etaDD s| ≤ 6 := by
  rw [abs_le]
  constructor <;> (simp only [etaDD]; linarith)

/-- `0 ≤ η₁`: `η₁ = s(1−s)²`. -/
lemma eta1_nonneg {s : ℝ} (h0 : 0 ≤ s) (_h1 : s ≤ 1) : 0 ≤ eta1 s := by
  have h : eta1 s = s * (1 - s) ^ 2 := by simp only [eta1]; ring
  rw [h]
  exact mul_nonneg h0 (sq_nonneg _)

/-- `η₁ ≤ 4/27`: `4/27 − η₁ = (s−1/3)²(4−3s)/3 ≥ 0`. -/
lemma eta1_le {s : ℝ} (_h0 : 0 ≤ s) (h1 : s ≤ 1) : eta1 s ≤ 4 / 27 := by
  have h : 4 / 27 - eta1 s = (s - 1 / 3) ^ 2 * ((4 - 3 * s) / 3) := by
    simp only [eta1]; ring
  have hnn : 0 ≤ (s - 1 / 3) ^ 2 * ((4 - 3 * s) / 3) :=
    mul_nonneg (sq_nonneg _) (by linarith)
  linarith

lemma eta1_abs_le {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) : |eta1 s| ≤ 4 / 27 := by
  rw [abs_le]
  exact ⟨by linarith [eta1_nonneg h0 h1], eta1_le h0 h1⟩

/-- `|η₁'| ≤ 1`: `η₁' − 1 = s(3s−4) ≤ 0`, `η₁' + 1 = 3(s−2/3)² + 2/3 ≥ 0`. -/
lemma eta1D_abs_le {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) : |eta1D s| ≤ 1 := by
  rw [abs_le]
  constructor
  · have h : eta1D s + 1 = 3 * (s - 2 / 3) ^ 2 + 2 / 3 := by
      simp only [eta1D]; ring
    have hnn : 0 ≤ 3 * (s - 2 / 3) ^ 2 + 2 / 3 :=
      add_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (by norm_num)
    linarith
  · have h : eta1D s - 1 = s * (3 * s - 4) := by simp only [eta1D]; ring
    have hnn : s * (3 * s - 4) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos h0 (by linarith)
    linarith

/-- `|η₁''| ≤ 4` on `[0,1]` (linear). -/
lemma eta1DD_abs_le {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) : |eta1DD s| ≤ 4 := by
  rw [abs_le]
  constructor <;> (simp only [eta1DD]; linarith)

/-! ## 2. Derivatives of the Hermite cubics (explicit `HasDerivAt`). -/

private lemma pow2_at (s : ℝ) : HasDerivAt (fun x : ℝ => x ^ 2) (2 * s) s := by
  have h := hasDerivAt_pow 2 s
  simpa using h

private lemma pow3_at (s : ℝ) : HasDerivAt (fun x : ℝ => x ^ 3) (3 * s ^ 2) s := by
  have h := hasDerivAt_pow 3 s
  simpa using h

lemma hasDerivAt_eta (s : ℝ) : HasDerivAt eta (etaD s) s := by
  have hA : HasDerivAt (fun x : ℝ => 1 - 3 * x ^ 2) (0 - 3 * (2 * s)) s :=
    (hasDerivAt_const s (1 : ℝ)).sub ((pow2_at s).const_mul 3)
  have hB : HasDerivAt (fun x : ℝ => 2 * x ^ 3) (2 * (3 * s ^ 2)) s :=
    (pow3_at s).const_mul 2
  have h := hA.add hB
  have hv : (0 - 3 * (2 * s)) + 2 * (3 * s ^ 2) = etaD s := by
    simp only [etaD]; ring
  rw [hv] at h
  exact h

lemma hasDerivAt_eta1 (s : ℝ) : HasDerivAt eta1 (eta1D s) s := by
  have hA : HasDerivAt (fun x : ℝ => x - 2 * x ^ 2) (1 - 2 * (2 * s)) s :=
    (hasDerivAt_id s).sub ((pow2_at s).const_mul 2)
  have hB : HasDerivAt (fun x : ℝ => x ^ 3) (3 * s ^ 2) s := pow3_at s
  have h := hA.add hB
  have hv : (1 - 2 * (2 * s)) + 3 * s ^ 2 = eta1D s := by
    simp only [eta1D]; ring
  rw [hv] at h
  exact h

lemma hasDerivAt_etaD (s : ℝ) : HasDerivAt etaD (etaDD s) s := by
  have hA : HasDerivAt (fun x : ℝ => -6 * x) (-6 * 1) s :=
    (hasDerivAt_id s).const_mul (-6)
  have hB : HasDerivAt (fun x : ℝ => 6 * x ^ 2) (6 * (2 * s)) s :=
    (pow2_at s).const_mul 6
  have h := hA.add hB
  have hv : (-6 * 1) + 6 * (2 * s) = etaDD s := by
    simp only [etaDD]; ring
  rw [hv] at h
  exact h

lemma hasDerivAt_eta1D (s : ℝ) : HasDerivAt eta1D (eta1DD s) s := by
  have hA : HasDerivAt (fun x : ℝ => 1 - 4 * x) (0 - 4 * 1) s :=
    (hasDerivAt_const s (1 : ℝ)).sub ((hasDerivAt_id s).const_mul 4)
  have hB : HasDerivAt (fun x : ℝ => 3 * x ^ 2) (3 * (2 * s)) s :=
    (pow2_at s).const_mul 3
  have h := hA.add hB
  have hv : (0 - 4 * 1) + 3 * (2 * s) = eta1DD s := by
    simp only [eta1DD]; ring
  rw [hv] at h
  exact h

/-! ## 3. Collar extensions (right and left).

Right collar `μ ∈ [τ, τ+B]`, `s = (μ−τ)/B ∈ [0,1]`:
  `E(μ) = p₀·η(s) + p₁·B·η₁(s)`.
Left collar `μ ∈ [−(τ+B), −τ]`, `v = (−μ−τ)/B ∈ [0,1]`:
  `E(μ) = q₀·η(v) − q₁·B·η₁(v)`
(the minus sign keeps `E'(−τ) = q₁`: `dv/dμ = −1/B`).
-/

section Collar

variable {τ B ε D₁ : ℝ}

noncomputable def ER (p₀ p₁ : ℂ) (τ B : ℝ) (μ : ℝ) : ℂ :=
  p₀ * (eta ((μ - τ) / B) : ℂ) + p₁ * ((B * eta1 ((μ - τ) / B) : ℝ) : ℂ)

noncomputable def ER1 (p₀ p₁ : ℂ) (τ B : ℝ) (μ : ℝ) : ℂ :=
  p₀ * ((etaD ((μ - τ) / B) * (1 / B) : ℝ) : ℂ)
    + p₁ * ((B * (eta1D ((μ - τ) / B) * (1 / B)) : ℝ) : ℂ)

noncomputable def ER2 (p₀ p₁ : ℂ) (τ B : ℝ) (μ : ℝ) : ℂ :=
  p₀ * ((etaDD ((μ - τ) / B) * ((1 / B) * (1 / B)) : ℝ) : ℂ)
    + p₁ * ((eta1DD ((μ - τ) / B) * (1 / B) : ℝ) : ℂ)

noncomputable def EL (q₀ q₁ : ℂ) (τ B : ℝ) (μ : ℝ) : ℂ :=
  q₀ * (eta ((-μ - τ) / B) : ℂ) - q₁ * ((B * eta1 ((-μ - τ) / B) : ℝ) : ℂ)

noncomputable def EL1 (q₀ q₁ : ℂ) (τ B : ℝ) (μ : ℝ) : ℂ :=
  q₀ * ((etaD ((-μ - τ) / B) * (-1 / B) : ℝ) : ℂ)
    - q₁ * ((B * (eta1D ((-μ - τ) / B) * (-1 / B)) : ℝ) : ℂ)

noncomputable def EL2 (q₀ q₁ : ℂ) (τ B : ℝ) (μ : ℝ) : ℂ :=
  q₀ * ((etaDD ((-μ - τ) / B) * ((1 / B) * (1 / B)) : ℝ) : ℂ)
    - q₁ * ((eta1DD ((-μ - τ) / B) * (1 / B) : ℝ) : ℂ)

/-- `B ≠ 0`. -/
private lemma hBne (hB0 : 0 < B) : B ≠ 0 := ne_of_gt hB0

/-- Real bridge: `B * (y * (1/B)) = y`. -/
private lemma B_cancel (hB0 : 0 < B) (y : ℝ) : B * (y * (1 / B)) = y := by
  have h := hBne hB0
  field_simp

/-- Real bridge: `B * (y * (−1/B)) = −y`. -/
private lemma B_cancel_neg (hB0 : 0 < B) (y : ℝ) : B * (y * (-1 / B)) = -y := by
  have h := hBne hB0
  field_simp

/-- The collar parameter `s = (μ−τ)/B` lies in `[0,1]` on the right collar. -/
lemma mem_collar_R (hB0 : 0 < B) {μ : ℝ} (hm : μ ∈ Set.Icc τ (τ + B)) :
    0 ≤ (μ - τ) / B ∧ (μ - τ) / B ≤ 1 := by
  obtain ⟨hlo, hhi⟩ := Set.mem_Icc.mp hm
  refine ⟨div_nonneg (by linarith) hB0.le, ?_⟩
  rw [div_le_one hB0]
  linarith

/-- The collar parameter `v = (−μ−τ)/B` lies in `[0,1]` on the left collar. -/
lemma mem_collar_L (hB0 : 0 < B) {μ : ℝ} (hm : μ ∈ Set.Icc (-(τ + B)) (-τ)) :
    0 ≤ (-μ - τ) / B ∧ (-μ - τ) / B ≤ 1 := by
  obtain ⟨hlo, hhi⟩ := Set.mem_Icc.mp hm
  refine ⟨div_nonneg (by linarith) hB0.le, ?_⟩
  rw [div_le_one hB0]
  linarith

/-- `|E| ≤ ε + (4/27)·B·D₁` on the right collar. -/
lemma norm_ER_le (hB0 : 0 < B) (hε0 : 0 < ε) (hD₁ : 0 ≤ D₁) (p₀ p₁ : ℂ) (hp₀ : ‖p₀‖ ≤ ε) (hp₁ : ‖p₁‖ ≤ D₁)
    {μ : ℝ} (hm : μ ∈ Set.Icc τ (τ + B)) :
    ‖ER p₀ p₁ τ B μ‖ ≤ ε + 4 / 27 * B * D₁ := by
  obtain ⟨hs0, hs1⟩ := mem_collar_R hB0 hm
  have eη : ‖(eta ((μ - τ) / B) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real]
    exact eta_abs_le hs0 hs1
  have eη1 : ‖((B * eta1 ((μ - τ) / B) : ℝ) : ℂ)‖ ≤ B * (4 / 27) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg hB0.le]
    exact mul_le_mul_of_nonneg_left (eta1_abs_le hs0 hs1) hB0.le
  have t1 : ‖p₀ * (eta ((μ - τ) / B) : ℂ)‖ ≤ ε := by
    calc ‖p₀ * (eta ((μ - τ) / B) : ℂ)‖ = ‖p₀‖ * ‖(eta ((μ - τ) / B) : ℂ)‖ :=
          norm_mul _ _
      _ ≤ ε * 1 := mul_le_mul hp₀ eη (norm_nonneg _) hε0.le
      _ = ε := mul_one _
  have t2 : ‖p₁ * ((B * eta1 ((μ - τ) / B) : ℝ) : ℂ)‖ ≤ 4 / 27 * B * D₁ := by
    calc ‖p₁ * ((B * eta1 ((μ - τ) / B) : ℝ) : ℂ)‖
          = ‖p₁‖ * ‖((B * eta1 ((μ - τ) / B) : ℝ) : ℂ)‖ := norm_mul _ _
      _ ≤ D₁ * (B * (4 / 27)) := mul_le_mul hp₁ eη1 (norm_nonneg _) hD₁
      _ = 4 / 27 * B * D₁ := by ring
  refine (norm_add_le _ _).trans ?_
  calc ‖p₀ * _‖ + ‖p₁ * _‖ ≤ ε + 4 / 27 * B * D₁ := add_le_add t1 t2

/-- `|E'| ≤ (3/2)·ε/B + D₁` on the right collar. -/
lemma norm_ER1_le (hB0 : 0 < B) (hε0 : 0 < ε) (hD₁ : 0 ≤ D₁) (p₀ p₁ : ℂ) (hp₀ : ‖p₀‖ ≤ ε) (hp₁ : ‖p₁‖ ≤ D₁)
    {μ : ℝ} (hm : μ ∈ Set.Icc τ (τ + B)) :
    ‖ER1 p₀ p₁ τ B μ‖ ≤ 3 / 2 * ε / B + D₁ := by
  obtain ⟨hs0, hs1⟩ := mem_collar_R hB0 hm
  have eη : |etaD ((μ - τ) / B) * (1 / B)| ≤ 3 / 2 * (1 / B) := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / B)]
    exact mul_le_mul_of_nonneg_right (etaD_abs_le hs0 hs1) (by positivity)
  have eη1 : |B * (eta1D ((μ - τ) / B) * (1 / B))| ≤ 1 := by
    rw [B_cancel hB0]
    exact eta1D_abs_le hs0 hs1
  have t1 : ‖p₀ * ((etaD ((μ - τ) / B) * (1 / B) : ℝ) : ℂ)‖ ≤ 3 / 2 * ε / B := by
    calc ‖p₀ * _‖ = ‖p₀‖ * |etaD ((μ - τ) / B) * (1 / B)| := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ ε * (3 / 2 * (1 / B)) := mul_le_mul hp₀ eη (abs_nonneg _) hε0.le
      _ = 3 / 2 * ε / B := by ring
  have t2 : ‖p₁ * ((B * (eta1D ((μ - τ) / B) * (1 / B)) : ℝ) : ℂ)‖ ≤ D₁ := by
    calc ‖p₁ * _‖ = ‖p₁‖ * |B * (eta1D ((μ - τ) / B) * (1 / B))| := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ D₁ * 1 := mul_le_mul hp₁ eη1 (abs_nonneg _) hD₁
      _ = D₁ := mul_one _
  refine (norm_add_le _ _).trans ?_
  calc ‖_‖ + ‖_‖ ≤ 3 / 2 * ε / B + D₁ := add_le_add t1 t2

/-- `|E''| ≤ 6·ε/B² + 4·D₁/B` on the right collar. -/
lemma norm_ER2_le (hB0 : 0 < B) (hε0 : 0 < ε) (hD₁ : 0 ≤ D₁) (p₀ p₁ : ℂ) (hp₀ : ‖p₀‖ ≤ ε) (hp₁ : ‖p₁‖ ≤ D₁)
    {μ : ℝ} (hm : μ ∈ Set.Icc τ (τ + B)) :
    ‖ER2 p₀ p₁ τ B μ‖ ≤ 6 * ε / B ^ 2 + 4 * D₁ / B := by
  obtain ⟨hs0, hs1⟩ := mem_collar_R hB0 hm
  have eη : |etaDD ((μ - τ) / B) * ((1 / B) * (1 / B))| ≤ 6 * (1 / B ^ 2) := by
    have hB2 : (0 : ℝ) ≤ (1 / B) * (1 / B) := by positivity
    have hsq : (1 / B) * (1 / B) = 1 / B ^ 2 := by ring
    rw [abs_mul, abs_of_nonneg hB2, hsq]
    exact mul_le_mul (etaDD_abs_le hs0 hs1) (le_refl _) (by positivity) (by norm_num)
  have eη1 : |eta1DD ((μ - τ) / B) * (1 / B)| ≤ 4 / B := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / B)]
    calc |eta1DD ((μ - τ) / B)| * (1 / B) ≤ 4 * (1 / B) :=
          mul_le_mul_of_nonneg_right (eta1DD_abs_le hs0 hs1) (by positivity)
      _ = 4 / B := by ring
  have t1 : ‖p₀ * ((etaDD ((μ - τ) / B) * ((1 / B) * (1 / B)) : ℝ) : ℂ)‖
      ≤ 6 * ε / B ^ 2 := by
    calc ‖p₀ * _‖ = ‖p₀‖ * |etaDD ((μ - τ) / B) * ((1 / B) * (1 / B))| := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ ε * (6 * (1 / B ^ 2)) := mul_le_mul hp₀ eη (abs_nonneg _) hε0.le
      _ = 6 * ε / B ^ 2 := by ring
  have t2 : ‖p₁ * ((eta1DD ((μ - τ) / B) * (1 / B) : ℝ) : ℂ)‖ ≤ 4 * D₁ / B := by
    calc ‖p₁ * _‖ = ‖p₁‖ * |eta1DD ((μ - τ) / B) * (1 / B)| := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ D₁ * (4 / B) := mul_le_mul hp₁ eη1 (abs_nonneg _) hD₁
      _ = 4 * D₁ / B := by ring
  refine (norm_add_le _ _).trans ?_
  calc ‖_‖ + ‖_‖ ≤ 6 * ε / B ^ 2 + 4 * D₁ / B := add_le_add t1 t2

/-- `|E| ≤ ε + (4/27)·B·D₁` on the left collar. -/
lemma norm_EL_le (hB0 : 0 < B) (hε0 : 0 < ε) (hD₁ : 0 ≤ D₁) (q₀ q₁ : ℂ) (hq₀ : ‖q₀‖ ≤ ε) (hq₁ : ‖q₁‖ ≤ D₁)
    {μ : ℝ} (hm : μ ∈ Set.Icc (-(τ + B)) (-τ)) :
    ‖EL q₀ q₁ τ B μ‖ ≤ ε + 4 / 27 * B * D₁ := by
  obtain ⟨hs0, hs1⟩ := mem_collar_L hB0 hm
  have eη : ‖(eta ((-μ - τ) / B) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real]
    exact eta_abs_le hs0 hs1
  have eη1 : ‖((B * eta1 ((-μ - τ) / B) : ℝ) : ℂ)‖ ≤ B * (4 / 27) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg hB0.le]
    exact mul_le_mul_of_nonneg_left (eta1_abs_le hs0 hs1) hB0.le
  have t1 : ‖q₀ * (eta ((-μ - τ) / B) : ℂ)‖ ≤ ε := by
    calc ‖q₀ * (eta ((-μ - τ) / B) : ℂ)‖ = ‖q₀‖ * ‖(eta ((-μ - τ) / B) : ℂ)‖ :=
          norm_mul _ _
      _ ≤ ε * 1 := mul_le_mul hq₀ eη (norm_nonneg _) hε0.le
      _ = ε := mul_one _
  have t2 : ‖q₁ * ((B * eta1 ((-μ - τ) / B) : ℝ) : ℂ)‖ ≤ 4 / 27 * B * D₁ := by
    calc ‖q₁ * ((B * eta1 ((-μ - τ) / B) : ℝ) : ℂ)‖
          = ‖q₁‖ * ‖((B * eta1 ((-μ - τ) / B) : ℝ) : ℂ)‖ := norm_mul _ _
      _ ≤ D₁ * (B * (4 / 27)) := mul_le_mul hq₁ eη1 (norm_nonneg _) hD₁
      _ = 4 / 27 * B * D₁ := by ring
  refine (norm_sub_le _ _).trans ?_
  calc ‖_‖ + ‖_‖ ≤ ε + 4 / 27 * B * D₁ := add_le_add t1 t2

/-- `|E'| ≤ (3/2)·ε/B + D₁` on the left collar. -/
lemma norm_EL1_le (hB0 : 0 < B) (hε0 : 0 < ε) (hD₁ : 0 ≤ D₁) (q₀ q₁ : ℂ) (hq₀ : ‖q₀‖ ≤ ε) (hq₁ : ‖q₁‖ ≤ D₁)
    {μ : ℝ} (hm : μ ∈ Set.Icc (-(τ + B)) (-τ)) :
    ‖EL1 q₀ q₁ τ B μ‖ ≤ 3 / 2 * ε / B + D₁ := by
  obtain ⟨hs0, hs1⟩ := mem_collar_L hB0 hm
  have eη : |etaD ((-μ - τ) / B) * (-1 / B)| ≤ 3 / 2 * (1 / B) := by
    have hneg : |-1 / B| = 1 / B := by
      rw [abs_div, abs_neg, abs_one, abs_of_pos hB0]
    rw [abs_mul, hneg]
    exact mul_le_mul_of_nonneg_right (etaD_abs_le hs0 hs1) (by positivity)
  have eη1 : |B * (eta1D ((-μ - τ) / B) * (-1 / B))| ≤ 1 := by
    rw [B_cancel_neg hB0, abs_neg]
    exact eta1D_abs_le hs0 hs1
  have t1 : ‖q₀ * ((etaD ((-μ - τ) / B) * (-1 / B) : ℝ) : ℂ)‖ ≤ 3 / 2 * ε / B := by
    calc ‖q₀ * _‖ = ‖q₀‖ * |etaD ((-μ - τ) / B) * (-1 / B)| := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ ε * (3 / 2 * (1 / B)) := mul_le_mul hq₀ eη (abs_nonneg _) hε0.le
      _ = 3 / 2 * ε / B := by ring
  have t2 : ‖q₁ * ((B * (eta1D ((-μ - τ) / B) * (-1 / B)) : ℝ) : ℂ)‖ ≤ D₁ := by
    calc ‖q₁ * _‖ = ‖q₁‖ * |B * (eta1D ((-μ - τ) / B) * (-1 / B))| := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ D₁ * 1 := mul_le_mul hq₁ eη1 (abs_nonneg _) hD₁
      _ = D₁ := mul_one _
  refine (norm_sub_le _ _).trans ?_
  calc ‖_‖ + ‖_‖ ≤ 3 / 2 * ε / B + D₁ := add_le_add t1 t2

/-- `|E''| ≤ 6·ε/B² + 4·D₁/B` on the left collar. -/
lemma norm_EL2_le (hB0 : 0 < B) (hε0 : 0 < ε) (hD₁ : 0 ≤ D₁) (q₀ q₁ : ℂ) (hq₀ : ‖q₀‖ ≤ ε) (hq₁ : ‖q₁‖ ≤ D₁)
    {μ : ℝ} (hm : μ ∈ Set.Icc (-(τ + B)) (-τ)) :
    ‖EL2 q₀ q₁ τ B μ‖ ≤ 6 * ε / B ^ 2 + 4 * D₁ / B := by
  obtain ⟨hs0, hs1⟩ := mem_collar_L hB0 hm
  have eη : |etaDD ((-μ - τ) / B) * ((1 / B) * (1 / B))| ≤ 6 * (1 / B ^ 2) := by
    have hB2 : (0 : ℝ) ≤ (1 / B) * (1 / B) := by positivity
    have hsq : (1 / B) * (1 / B) = 1 / B ^ 2 := by ring
    rw [abs_mul, abs_of_nonneg hB2, hsq]
    exact mul_le_mul (etaDD_abs_le hs0 hs1) (le_refl _) (by positivity) (by norm_num)
  have eη1 : |eta1DD ((-μ - τ) / B) * (1 / B)| ≤ 4 / B := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / B)]
    calc |eta1DD ((-μ - τ) / B)| * (1 / B) ≤ 4 * (1 / B) :=
          mul_le_mul_of_nonneg_right (eta1DD_abs_le hs0 hs1) (by positivity)
      _ = 4 / B := by ring
  have t1 : ‖q₀ * ((etaDD ((-μ - τ) / B) * ((1 / B) * (1 / B)) : ℝ) : ℂ)‖
      ≤ 6 * ε / B ^ 2 := by
    calc ‖q₀ * _‖ = ‖q₀‖ * |etaDD ((-μ - τ) / B) * ((1 / B) * (1 / B))| := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ ε * (6 * (1 / B ^ 2)) := mul_le_mul hq₀ eη (abs_nonneg _) hε0.le
      _ = 6 * ε / B ^ 2 := by ring
  have t2 : ‖q₁ * ((eta1DD ((-μ - τ) / B) * (1 / B) : ℝ) : ℂ)‖
      ≤ 4 * D₁ / B := by
    calc ‖q₁ * _‖ = ‖q₁‖ * |eta1DD ((-μ - τ) / B) * (1 / B)| := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ D₁ * (4 / B) := mul_le_mul hq₁ eη1 (abs_nonneg _) hD₁
      _ = 4 * D₁ / B := by ring
  refine (norm_sub_le _ _).trans ?_
  calc ‖_‖ + ‖_‖ ≤ 6 * ε / B ^ 2 + 4 * D₁ / B := add_le_add t1 t2

/-! ## 4. Derivatives of the collar extensions (chain rule). -/

private lemma affR_at (τ B μ : ℝ) :
    HasDerivAt (fun ν : ℝ => (ν - τ) / B) ((1 : ℝ) / B) μ :=
  ((hasDerivAt_id μ).sub_const τ).div_const B

private lemma affL_at (τ B μ : ℝ) :
    HasDerivAt (fun ν : ℝ => (-ν - τ) / B) ((-1 : ℝ) / B) μ :=
  (((hasDerivAt_id μ).neg).sub_const τ).div_const B

lemma hasDerivAt_ER (p₀ p₁ : ℂ) {μ : ℝ} :
    HasDerivAt (ER p₀ p₁ τ B) (ER1 p₀ p₁ τ B μ) μ := by
  have he : HasDerivAt (fun ν : ℝ => eta ((ν - τ) / B))
      (etaD ((μ - τ) / B) * (1 / B)) μ :=
    HasDerivAt.comp μ (hasDerivAt_eta _) (affR_at τ B μ)
  have he1 : HasDerivAt (fun ν : ℝ => eta1 ((ν - τ) / B))
      (eta1D ((μ - τ) / B) * (1 / B)) μ :=
    HasDerivAt.comp μ (hasDerivAt_eta1 _) (affR_at τ B μ)
  have hc1 : HasDerivAt (fun ν : ℝ => ((eta ((ν - τ) / B) : ℝ) : ℂ))
      (((etaD ((μ - τ) / B) * (1 / B) : ℝ)) : ℂ) μ := he.ofReal_comp
  have hc2 : HasDerivAt (fun ν : ℝ => ((B * eta1 ((ν - τ) / B) : ℝ) : ℂ))
      (((B * (eta1D ((μ - τ) / B) * (1 / B)) : ℝ)) : ℂ) μ :=
    (he1.const_mul B).ofReal_comp
  have h := (hc1.const_mul p₀).add (hc2.const_mul p₁)
  exact h

lemma hasDerivAt_ER1 (hB0 : 0 < B) (p₀ p₁ : ℂ) {μ : ℝ} :
    HasDerivAt (ER1 p₀ p₁ τ B) (ER2 p₀ p₁ τ B μ) μ := by
  have hBne : B ≠ 0 := hBne hB0
  have he : HasDerivAt (fun ν : ℝ => etaD ((ν - τ) / B))
      (etaDD ((μ - τ) / B) * (1 / B)) μ :=
    HasDerivAt.comp μ (hasDerivAt_etaD _) (affR_at τ B μ)
  have he1 : HasDerivAt (fun ν : ℝ => eta1D ((ν - τ) / B))
      (eta1DD ((μ - τ) / B) * (1 / B)) μ :=
    HasDerivAt.comp μ (hasDerivAt_eta1D _) (affR_at τ B μ)
  have hc1 : HasDerivAt
      (fun ν : ℝ => ((etaD ((ν - τ) / B) * (1 / B) : ℝ) : ℂ))
      (((etaDD ((μ - τ) / B) * (1 / B) * (1 / B) : ℝ)) : ℂ) μ :=
    (he.mul_const (1 / B)).ofReal_comp
  have hc2 : HasDerivAt
      (fun ν : ℝ => ((B * (eta1D ((ν - τ) / B) * (1 / B)) : ℝ) : ℂ))
      (((B * ((eta1DD ((μ - τ) / B) * (1 / B)) * (1 / B)) : ℝ)) : ℂ) μ :=
    ((he1.mul_const (1 / B)).const_mul B).ofReal_comp
  have h := (hc1.const_mul p₀).add (hc2.const_mul p₁)
  have hv1 : etaDD ((μ - τ) / B) * (1 / B) * (1 / B)
      = etaDD ((μ - τ) / B) * ((1 / B) * (1 / B)) := by ring
  have hv2 : B * ((eta1DD ((μ - τ) / B) * (1 / B)) * (1 / B))
      = eta1DD ((μ - τ) / B) * (1 / B) :=
    B_cancel hB0 _
  have hv : p₀ * (((etaDD ((μ - τ) / B) * (1 / B) * (1 / B) : ℝ)) : ℂ)
        + p₁ * (((B * ((eta1DD ((μ - τ) / B) * (1 / B)) * (1 / B)) : ℝ)) : ℂ)
      = ER2 p₀ p₁ τ B μ := by
    simp only [ER2, hv1, hv2]
  rw [hv] at h
  exact h

lemma hasDerivAt_EL (q₀ q₁ : ℂ) {μ : ℝ} :
    HasDerivAt (EL q₀ q₁ τ B) (EL1 q₀ q₁ τ B μ) μ := by
  have he : HasDerivAt (fun ν : ℝ => eta ((-ν - τ) / B))
      (etaD ((-μ - τ) / B) * (-1 / B)) μ :=
    HasDerivAt.comp μ (hasDerivAt_eta _) (affL_at τ B μ)
  have he1 : HasDerivAt (fun ν : ℝ => eta1 ((-ν - τ) / B))
      (eta1D ((-μ - τ) / B) * (-1 / B)) μ :=
    HasDerivAt.comp μ (hasDerivAt_eta1 _) (affL_at τ B μ)
  have hc1 : HasDerivAt (fun ν : ℝ => ((eta ((-ν - τ) / B) : ℝ) : ℂ))
      (((etaD ((-μ - τ) / B) * (-1 / B) : ℝ)) : ℂ) μ := he.ofReal_comp
  have hc2 : HasDerivAt (fun ν : ℝ => ((B * eta1 ((-ν - τ) / B) : ℝ) : ℂ))
      (((B * (eta1D ((-μ - τ) / B) * (-1 / B)) : ℝ)) : ℂ) μ :=
    (he1.const_mul B).ofReal_comp
  have h := (hc1.const_mul q₀).sub (hc2.const_mul q₁)
  exact h

lemma hasDerivAt_EL1 (hB0 : 0 < B) (q₀ q₁ : ℂ) {μ : ℝ} :
    HasDerivAt (EL1 q₀ q₁ τ B) (EL2 q₀ q₁ τ B μ) μ := by
  have hBne : B ≠ 0 := hBne hB0
  have he : HasDerivAt (fun ν : ℝ => etaD ((-ν - τ) / B))
      (etaDD ((-μ - τ) / B) * (-1 / B)) μ :=
    HasDerivAt.comp μ (hasDerivAt_etaD _) (affL_at τ B μ)
  have he1 : HasDerivAt (fun ν : ℝ => eta1D ((-ν - τ) / B))
      (eta1DD ((-μ - τ) / B) * (-1 / B)) μ :=
    HasDerivAt.comp μ (hasDerivAt_eta1D _) (affL_at τ B μ)
  have hc1 : HasDerivAt
      (fun ν : ℝ => ((etaD ((-ν - τ) / B) * (-1 / B) : ℝ) : ℂ))
      (((etaDD ((-μ - τ) / B) * (-1 / B) * (-1 / B) : ℝ)) : ℂ) μ :=
    (he.mul_const (-1 / B)).ofReal_comp
  have hc2 : HasDerivAt
      (fun ν : ℝ => ((B * (eta1D ((-ν - τ) / B) * (-1 / B)) : ℝ) : ℂ))
      (((B * ((eta1DD ((-μ - τ) / B) * (-1 / B)) * (-1 / B)) : ℝ)) : ℂ) μ :=
    ((he1.mul_const (-1 / B)).const_mul B).ofReal_comp
  have h := (hc1.const_mul q₀).sub (hc2.const_mul q₁)
  have hv1 : etaDD ((-μ - τ) / B) * (-1 / B) * (-1 / B)
      = etaDD ((-μ - τ) / B) * ((1 / B) * (1 / B)) := by ring
  have hv2 : B * ((eta1DD ((-μ - τ) / B) * (-1 / B)) * (-1 / B))
      = eta1DD ((-μ - τ) / B) * (1 / B) := by
    have hBne : B ≠ 0 := ne_of_gt hB0
    field_simp
  have hv : q₀ * (((etaDD ((-μ - τ) / B) * (-1 / B) * (-1 / B) : ℝ)) : ℂ)
        - q₁ * (((B * ((eta1DD ((-μ - τ) / B) * (-1 / B)) * (-1 / B)) : ℝ)) : ℂ)
      = EL2 q₀ q₁ τ B μ := by
    simp only [EL2, hv1, hv2]
  rw [hv] at h
  exact h

/-! ### Endpoint values (vanishing / matching). -/

/-- Right extension matches `(p₀, p₁)` at `τ`. -/
lemma ER_at_left (hB0 : 0 < B) (p₀ p₁ : ℂ) :
    ER p₀ p₁ τ B τ = p₀ ∧ ER1 p₀ p₁ τ B τ = p₁ := by
  have hs : (τ - τ) / B = 0 := by simp
  constructor
  · simp only [ER, hs, eta_zero, eta1_zero, Complex.ofReal_one, Complex.ofReal_zero,
      mul_one, mul_zero, add_zero]
  · simp only [ER1, hs, etaD_zero, eta1D_zero]
    rw [B_cancel hB0]
    simp

/-- Right extension vanishes to first order at `τ+B`. -/
lemma ER_at_right (hB0 : 0 < B) (p₀ p₁ : ℂ) :
    ER p₀ p₁ τ B (τ + B) = 0 ∧ ER1 p₀ p₁ τ B (τ + B) = 0 := by
  have hBne : B ≠ 0 := hBne hB0
  have hs : (τ + B - τ) / B = 1 := by
    rw [show τ + B - τ = B by ring, div_self hBne]
  constructor
  · simp only [ER, hs, eta_one, eta1_one, Complex.ofReal_zero, mul_zero, add_zero]
  · show p₀ * ((etaD ((τ + B - τ) / B) * (1 / B) : ℝ) : ℂ)
        + p₁ * ((B * (eta1D ((τ + B - τ) / B) * (1 / B)) : ℝ) : ℂ) = 0
    rw [hs, etaD_one, eta1D_one]
    simp

/-- Left extension matches `(q₀, q₁)` at `−τ`. -/
lemma EL_at_right (hB0 : 0 < B) (q₀ q₁ : ℂ) :
    EL q₀ q₁ τ B (-τ) = q₀ ∧ EL1 q₀ q₁ τ B (-τ) = q₁ := by
  have hs : (- -τ - τ) / B = 0 := by simp
  constructor
  · simp only [EL, hs, eta_zero, eta1_zero, Complex.ofReal_one, Complex.ofReal_zero,
      mul_one, mul_zero, sub_zero]
  · simp only [EL1, hs, etaD_zero, eta1D_zero]
    have hneg : B * (1 * (-1 / B)) = -1 := by
      have h := B_cancel_neg hB0 (1 : ℝ)
      simpa using h
    rw [hneg]
    simp

/-- Left extension vanishes to first order at `−(τ+B)`. -/
lemma EL_at_left (hB0 : 0 < B) (q₀ q₁ : ℂ) :
    EL q₀ q₁ τ B (-(τ + B)) = 0 ∧ EL1 q₀ q₁ τ B (-(τ + B)) = 0 := by
  have hBne : B ≠ 0 := hBne hB0
  have hs : (- -(τ + B) - τ) / B = 1 := by
    rw [show - -(τ + B) - τ = B by ring, div_self hBne]
  constructor
  · simp only [EL, hs, eta_one, eta1_one, Complex.ofReal_zero, mul_zero, sub_zero]
  · show q₀ * ((etaD ((- -(τ + B) - τ) / B) * (-1 / B) : ℝ) : ℂ)
        - q₁ * ((B * (eta1D ((- -(τ + B) - τ) / B) * (-1 / B)) : ℝ) : ℂ) = 0
    rw [hs, etaD_one, eta1D_one]
    simp

end Collar

/-! ## 5. The three smooth pieces `H_mid`, `H_right`, `H_left`.

`H = Ψ·χ` on the band, `H = E·χ` on each collar.  All estimates and both
integrations by parts are proved on these globally-smooth functions; the
piecewise `κ̂` is only used to state `κ̂ = Ψ` on the band and to define `κ`.
-/

section Hat

variable {τ B ε D₁ D₂ K : ℝ}
variable {Ψ : ℝ → ℂ} {χ : ℝ → ℝ}

noncomputable def HatM (Ψ : ℝ → ℂ) (χ : ℝ → ℝ) (μ : ℝ) : ℂ := Ψ μ * ((χ μ : ℝ) : ℂ)

noncomputable def HatM1 (Ψ : ℝ → ℂ) (χ : ℝ → ℝ) (μ : ℝ) : ℂ :=
  deriv Ψ μ * ((χ μ : ℝ) : ℂ) + Ψ μ * ((deriv χ μ : ℝ) : ℂ)

noncomputable def HatM2 (Ψ : ℝ → ℂ) (χ : ℝ → ℝ) (μ : ℝ) : ℂ :=
  deriv (deriv Ψ) μ * ((χ μ : ℝ) : ℂ)
    + 2 * deriv Ψ μ * ((deriv χ μ : ℝ) : ℂ)
    + Ψ μ * ((deriv (deriv χ) μ : ℝ) : ℂ)

noncomputable def HatR (τ B : ℝ) (Ψ : ℝ → ℂ) (χ : ℝ → ℝ) (μ : ℝ) : ℂ :=
  ER (Ψ τ) (deriv Ψ τ) τ B μ * ((χ μ : ℝ) : ℂ)

noncomputable def HatR1 (τ B : ℝ) (Ψ : ℝ → ℂ) (χ : ℝ → ℝ) (μ : ℝ) : ℂ :=
  ER1 (Ψ τ) (deriv Ψ τ) τ B μ * ((χ μ : ℝ) : ℂ)
    + ER (Ψ τ) (deriv Ψ τ) τ B μ * ((deriv χ μ : ℝ) : ℂ)

noncomputable def HatR2 (τ B : ℝ) (Ψ : ℝ → ℂ) (χ : ℝ → ℝ) (μ : ℝ) : ℂ :=
  ER2 (Ψ τ) (deriv Ψ τ) τ B μ * ((χ μ : ℝ) : ℂ)
    + 2 * ER1 (Ψ τ) (deriv Ψ τ) τ B μ * ((deriv χ μ : ℝ) : ℂ)
    + ER (Ψ τ) (deriv Ψ τ) τ B μ * ((deriv (deriv χ) μ : ℝ) : ℂ)

noncomputable def HatL (τ B : ℝ) (Ψ : ℝ → ℂ) (χ : ℝ → ℝ) (μ : ℝ) : ℂ :=
  EL (Ψ (-τ)) (deriv Ψ (-τ)) τ B μ * ((χ μ : ℝ) : ℂ)

noncomputable def HatL1 (τ B : ℝ) (Ψ : ℝ → ℂ) (χ : ℝ → ℝ) (μ : ℝ) : ℂ :=
  EL1 (Ψ (-τ)) (deriv Ψ (-τ)) τ B μ * ((χ μ : ℝ) : ℂ)
    + EL (Ψ (-τ)) (deriv Ψ (-τ)) τ B μ * ((deriv χ μ : ℝ) : ℂ)

noncomputable def HatL2 (τ B : ℝ) (Ψ : ℝ → ℂ) (χ : ℝ → ℝ) (μ : ℝ) : ℂ :=
  EL2 (Ψ (-τ)) (deriv Ψ (-τ)) τ B μ * ((χ μ : ℝ) : ℂ)
    + 2 * EL1 (Ψ (-τ)) (deriv Ψ (-τ)) τ B μ * ((deriv χ μ : ℝ) : ℂ)
    + EL (Ψ (-τ)) (deriv Ψ (-τ)) τ B μ * ((deriv (deriv χ) μ : ℝ) : ℂ)

/-! ### Pointwise derivative identities. -/

private lemma psi_at (hΨ : ContDiff ℝ 2 Ψ) (μ : ℝ) : HasDerivAt Ψ (deriv Ψ μ) μ :=
  (hΨ.differentiable (by norm_num)).differentiableAt.hasDerivAt

private lemma dpsi_at (hΨ : ContDiff ℝ 2 Ψ) (μ : ℝ) : HasDerivAt (deriv Ψ) (deriv (deriv Ψ) μ) μ :=
  hΨ.differentiable_deriv_two.differentiableAt.hasDerivAt

private lemma chi_at (hχ : ContDiff ℝ 2 χ) (μ : ℝ) : HasDerivAt χ (deriv χ μ) μ :=
  (hχ.differentiable (by norm_num)).differentiableAt.hasDerivAt

private lemma dchi_at (hχ : ContDiff ℝ 2 χ) (μ : ℝ) : HasDerivAt (deriv χ) (deriv (deriv χ) μ) μ :=
  hχ.differentiable_deriv_two.differentiableAt.hasDerivAt

private lemma chiC_at (hχ : ContDiff ℝ 2 χ) (μ : ℝ) :
    HasDerivAt (fun ν : ℝ => ((χ ν : ℝ) : ℂ)) (((deriv χ μ : ℝ)) : ℂ) μ :=
  ((chi_at hχ) μ).ofReal_comp

private lemma dchiC_at (hχ : ContDiff ℝ 2 χ) (μ : ℝ) :
    HasDerivAt (fun ν : ℝ => ((deriv χ ν : ℝ) : ℂ)) (((deriv (deriv χ) μ : ℝ)) : ℂ) μ :=
  ((dchi_at hχ) μ).ofReal_comp

lemma hasDerivAt_HatM (hΨ : ContDiff ℝ 2 Ψ) (hχ : ContDiff ℝ 2 χ) (μ : ℝ) : HasDerivAt (HatM Ψ χ) ((HatM1 Ψ χ) μ) μ := by
  have h := ((psi_at hΨ) μ).mul ((chiC_at hχ) μ)
  exact h

lemma hasDerivAt_HatM1 (hΨ : ContDiff ℝ 2 Ψ) (hχ : ContDiff ℝ 2 χ) (μ : ℝ) : HasDerivAt (HatM1 Ψ χ) ((HatM2 Ψ χ) μ) μ := by
  have h := (((dpsi_at hΨ) μ).mul ((chiC_at hχ) μ)).add
    (((psi_at hΨ) μ).mul ((dchiC_at hχ) μ))
  have hv : (deriv (deriv Ψ) μ * ((χ μ : ℝ) : ℂ) + deriv Ψ μ * ((deriv χ μ : ℝ) : ℂ))
        + (deriv Ψ μ * ((deriv χ μ : ℝ) : ℂ) + Ψ μ * ((deriv (deriv χ) μ : ℝ) : ℂ))
      = (HatM2 Ψ χ) μ := by
    simp only [HatM2]; ring
  rw [hv] at h
  exact h

lemma hasDerivAt_HatR (hΨ : ContDiff ℝ 2 Ψ) (hχ : ContDiff ℝ 2 χ) (μ : ℝ) : HasDerivAt (HatR τ B Ψ χ) ((HatR1 τ B Ψ χ) μ) μ := by
  have h := (hasDerivAt_ER (τ := τ) (B := B) (Ψ τ) (deriv Ψ τ)).mul ((chiC_at hχ) μ)
  exact h

lemma hasDerivAt_HatR1 (hB0 : 0 < B) (hΨ : ContDiff ℝ 2 Ψ) (hχ : ContDiff ℝ 2 χ) (μ : ℝ) : HasDerivAt (HatR1 τ B Ψ χ) ((HatR2 τ B Ψ χ) μ) μ := by
  have h := ((hasDerivAt_ER1 (τ := τ) (B := B) hB0 (Ψ τ) (deriv Ψ τ)).mul ((chiC_at hχ) μ)).add
    ((hasDerivAt_ER (τ := τ) (B := B) (Ψ τ) (deriv Ψ τ)).mul ((dchiC_at hχ) μ))
  have hv : (ER2 (Ψ τ) (deriv Ψ τ) τ B μ * ((χ μ : ℝ) : ℂ)
          + ER1 (Ψ τ) (deriv Ψ τ) τ B μ * ((deriv χ μ : ℝ) : ℂ))
        + (ER1 (Ψ τ) (deriv Ψ τ) τ B μ * ((deriv χ μ : ℝ) : ℂ)
          + ER (Ψ τ) (deriv Ψ τ) τ B μ * ((deriv (deriv χ) μ : ℝ) : ℂ))
      = (HatR2 τ B Ψ χ) μ := by
    simp only [HatR2]; ring
  rw [hv] at h
  exact h

lemma hasDerivAt_HatL (hΨ : ContDiff ℝ 2 Ψ) (hχ : ContDiff ℝ 2 χ) (μ : ℝ) : HasDerivAt (HatL τ B Ψ χ) ((HatL1 τ B Ψ χ) μ) μ := by
  have h := (hasDerivAt_EL (τ := τ) (B := B) (Ψ (-τ)) (deriv Ψ (-τ))).mul ((chiC_at hχ) μ)
  exact h

lemma hasDerivAt_HatL1 (hB0 : 0 < B) (hΨ : ContDiff ℝ 2 Ψ) (hχ : ContDiff ℝ 2 χ) (μ : ℝ) : HasDerivAt (HatL1 τ B Ψ χ) ((HatL2 τ B Ψ χ) μ) μ := by
  have h := ((hasDerivAt_EL1 (τ := τ) (B := B) hB0 (Ψ (-τ)) (deriv Ψ (-τ))).mul ((chiC_at hχ) μ)).add
    ((hasDerivAt_EL (τ := τ) (B := B) (Ψ (-τ)) (deriv Ψ (-τ))).mul ((dchiC_at hχ) μ))
  have hv : (EL2 (Ψ (-τ)) (deriv Ψ (-τ)) τ B μ * ((χ μ : ℝ) : ℂ)
          + EL1 (Ψ (-τ)) (deriv Ψ (-τ)) τ B μ * ((deriv χ μ : ℝ) : ℂ))
        + (EL1 (Ψ (-τ)) (deriv Ψ (-τ)) τ B μ * ((deriv χ μ : ℝ) : ℂ)
          + EL (Ψ (-τ)) (deriv Ψ (-τ)) τ B μ * ((deriv (deriv χ) μ : ℝ) : ℂ))
      = (HatL2 τ B Ψ χ) μ := by
    simp only [HatL2]; ring
  rw [hv] at h
  exact h

/-! ### Boundary matching (values and first derivatives agree at junctions,
vanish at the outer ends). -/

lemma HatR_eq_HatM (hB0 : 0 < B) : (HatR τ B Ψ χ) τ = (HatM Ψ χ) τ := by
  have h := (ER_at_left (τ := τ) (B := B) hB0 (Ψ τ) (deriv Ψ τ)).1
  simp only [HatR, HatM, h]

lemma HatR1_eq_HatM1 (hB0 : 0 < B) : (HatR1 τ B Ψ χ) τ = (HatM1 Ψ χ) τ := by
  have h := (ER_at_left (τ := τ) (B := B) hB0 (Ψ τ) (deriv Ψ τ)).2
  have h0 := (ER_at_left (τ := τ) (B := B) hB0 (Ψ τ) (deriv Ψ τ)).1
  simp only [HatR1, HatM1, h, h0]

lemma HatL_eq_HatM (hB0 : 0 < B) : (HatL τ B Ψ χ) (-τ) = (HatM Ψ χ) (-τ) := by
  have h := (EL_at_right (τ := τ) (B := B) hB0 (Ψ (-τ)) (deriv Ψ (-τ))).1
  simp only [HatL, HatM, h]

lemma HatL1_eq_HatM1 (hB0 : 0 < B) : (HatL1 τ B Ψ χ) (-τ) = (HatM1 Ψ χ) (-τ) := by
  have h := (EL_at_right (τ := τ) (B := B) hB0 (Ψ (-τ)) (deriv Ψ (-τ))).2
  have h0 := (EL_at_right (τ := τ) (B := B) hB0 (Ψ (-τ)) (deriv Ψ (-τ))).1
  simp only [HatL1, HatM1, h, h0]

lemma HatR_outer (hB0 : 0 < B) : (HatR τ B Ψ χ) (τ + B) = 0 ∧ (HatR1 τ B Ψ χ) (τ + B) = 0 := by
  obtain ⟨h0, h1⟩ := ER_at_right (τ := τ) (B := B) hB0 (Ψ τ) (deriv Ψ τ)
  constructor
  · simp only [HatR, h0, zero_mul]
  · simp only [HatR1, h0, h1, zero_mul, add_zero]

lemma HatL_outer (hB0 : 0 < B) : (HatL τ B Ψ χ) (-(τ + B)) = 0 ∧ (HatL1 τ B Ψ χ) (-(τ + B)) = 0 := by
  obtain ⟨h0, h1⟩ := EL_at_left (τ := τ) (B := B) hB0 (Ψ (-τ)) (deriv Ψ (-τ))
  constructor
  · simp only [HatL, h0, zero_mul]
  · simp only [HatL1, h0, h1, zero_mul, add_zero]

/-! ### Sup bounds for the three pieces. -/

/-- `χ` is locally `1` near interior band points. -/
lemma chi_eq_one_nhds (hχ1 : ∀ μ : ℝ, |μ| ≤ τ → χ μ = 1) {μ : ℝ} (hm : μ ∈ Set.Ioo (-τ) τ) :
    χ =ᶠ[nhds μ] fun _ => 1 := by
  have hmem : Set.Ioo (-τ) τ ∈ nhds μ := Ioo_mem_nhds hm.1 hm.2
  filter_upwards [hmem] with x hx
  obtain ⟨hlo, hhi⟩ := Set.mem_Ioo.mp hx
  exact hχ1 x (by rw [abs_le]; constructor <;> linarith)

/-- `χ' = 0` at interior band points. -/
lemma deriv_chi_interior (hχ1 : ∀ μ : ℝ, |μ| ≤ τ → χ μ = 1) {μ : ℝ} (hm : μ ∈ Set.Ioo (-τ) τ) : deriv χ μ = 0 := by
  have h := ((chi_eq_one_nhds hχ1) hm).deriv_eq
  simpa using h

/-- `χ'' = 0` at interior band points. -/
lemma dderiv_chi_interior (hχ1 : ∀ μ : ℝ, |μ| ≤ τ → χ μ = 1) {μ : ℝ} (hm : μ ∈ Set.Ioo (-τ) τ) :
    deriv (deriv χ) μ = 0 := by
  have hmem : Set.Ioo (-τ) τ ∈ nhds μ := Ioo_mem_nhds hm.1 hm.2
  have h0 : deriv χ =ᶠ[nhds μ] fun _ => 0 := by
    filter_upwards [hmem] with x hx
    exact (deriv_chi_interior hχ1) hx
  have h := h0.deriv_eq
  simpa using h

private lemma abs_le_tau_of_Icc {μ : ℝ} (hm : μ ∈ Set.Icc (-τ) τ) : |μ| ≤ τ := by
  obtain ⟨hlo, hhi⟩ := Set.mem_Icc.mp hm
  rw [abs_le]
  exact ⟨hlo, hhi⟩

private lemma abs_le_tau_of_Ioo {μ : ℝ} (hm : μ ∈ Set.Ioo (-τ) τ) : |μ| ≤ τ := by
  obtain ⟨hlo, hhi⟩ := Set.mem_Ioo.mp hm
  rw [abs_le]
  constructor <;> linarith

/-- `‖2‖ = 2` in `ℂ`. -/
private lemma norm_two_C : ‖(2 : ℂ)‖ = 2 := by
  have h2 : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_cast
  rw [h2, Complex.norm_real]
  norm_num

/-- Coerced cutoff bounds. -/
private lemma norm_coe_chi (hχb : ∀ μ : ℝ, |χ μ| ≤ 1) (μ : ℝ) : ‖((χ μ : ℝ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real]
  exact hχb μ

private lemma norm_coe_dchi (hχd1 : ∀ μ : ℝ, ‖deriv χ μ‖ ≤ K / B) (μ : ℝ) : ‖((deriv χ μ : ℝ) : ℂ)‖ ≤ K / B := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact hχd1 μ

private lemma norm_coe_ddchi (hχd2 : ∀ μ : ℝ, ‖deriv (deriv χ) μ‖ ≤ K / B ^ 2) (μ : ℝ) : ‖((deriv (deriv χ) μ : ℝ) : ℂ)‖ ≤ K / B ^ 2 := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact hχd2 μ

/-- `‖H_mid‖ ≤ ε` on the band. -/
lemma norm_HatM_band (hΨ0 : ∀ μ : ℝ, |μ| ≤ τ → ‖Ψ μ‖ ≤ ε) (hχ1 : ∀ μ : ℝ, |μ| ≤ τ → χ μ = 1) {μ : ℝ} (hm : μ ∈ Set.Icc (-τ) τ) : ‖(HatM Ψ χ) μ‖ ≤ ε := by
  have habs := abs_le_tau_of_Icc hm
  have h1 : χ μ = 1 := hχ1 μ habs
  have h : (HatM Ψ χ) μ = Ψ μ := by simp only [HatM, h1, Complex.ofReal_one, mul_one]
  rw [h]
  exact hΨ0 μ habs

/-- `‖H_mid''‖ ≤ D₂` on the open band (cutoff derivatives vanish there). -/
lemma norm_HatM2_band (hΨ2 : ∀ μ : ℝ, |μ| ≤ τ → ‖deriv (deriv Ψ) μ‖ ≤ D₂) (hχ1 : ∀ μ : ℝ, |μ| ≤ τ → χ μ = 1) {μ : ℝ} (hm : μ ∈ Set.Ioo (-τ) τ) : ‖(HatM2 Ψ χ) μ‖ ≤ D₂ := by
  have habs := abs_le_tau_of_Ioo hm
  have e1 : ((χ μ : ℝ) : ℂ) = 1 := by
    rw [hχ1 μ habs]; exact Complex.ofReal_one
  have e2 : ((deriv χ μ : ℝ) : ℂ) = 0 := by
    rw [(deriv_chi_interior hχ1) hm]; exact Complex.ofReal_zero
  have e3 : ((deriv (deriv χ) μ : ℝ) : ℂ) = 0 := by
    rw [(dderiv_chi_interior hχ1) hm]; exact Complex.ofReal_zero
  have h : (HatM2 Ψ χ) μ = deriv (deriv Ψ) μ := by
    simp only [HatM2, e1, e2, e3, mul_one, mul_zero, add_zero]
  rw [h]
  exact hΨ2 μ habs

/-- Per-collar second-derivative sup bound (right). -/
lemma norm_HatR2_collar (hτ : 1 ≤ τ) (hB0 : 0 < B) (hε0 : 0 < ε) (hD₁ : 0 ≤ D₁) (hΨ0 : ∀ μ : ℝ, |μ| ≤ τ → ‖Ψ μ‖ ≤ ε) (hΨ1 : ∀ μ : ℝ, |μ| ≤ τ → ‖deriv Ψ μ‖ ≤ D₁) (hχb : ∀ μ : ℝ, |χ μ| ≤ 1) (hχd1 : ∀ μ : ℝ, ‖deriv χ μ‖ ≤ K / B) (hχd2 : ∀ μ : ℝ, ‖deriv (deriv χ) μ‖ ≤ K / B ^ 2) {μ : ℝ} (hm : μ ∈ Set.Icc τ (τ + B)) :
    ‖(HatR2 τ B Ψ χ) μ‖ ≤ (6 + 4 * K) * ε / B ^ 2 + (4 + 2 * K + 4 * K / 27) * D₁ / B := by
  have hp₀ : ‖Ψ τ‖ ≤ ε := hΨ0 τ (by rw [abs_le]; constructor <;> linarith [hτ])
  have hp₁ : ‖deriv Ψ τ‖ ≤ D₁ := hΨ1 τ (by rw [abs_le]; constructor <;> linarith [hτ])
  have b0 := norm_ER_le (τ := τ) (B := B) hB0 hε0 hD₁ (Ψ τ) (deriv Ψ τ) hp₀ hp₁ hm
  have b1 := norm_ER1_le (τ := τ) (B := B) hB0 hε0 hD₁ (Ψ τ) (deriv Ψ τ) hp₀ hp₁ hm
  have b2 := norm_ER2_le (τ := τ) (B := B) hB0 hε0 hD₁ (Ψ τ) (deriv Ψ τ) hp₀ hp₁ hm
  have c0 := (norm_coe_chi hχb) μ
  have c1 := (norm_coe_dchi hχd1) μ
  have c2 := (norm_coe_ddchi hχd2) μ
  have t1 : ‖ER2 (Ψ τ) (deriv Ψ τ) τ B μ * ((χ μ : ℝ) : ℂ)‖
      ≤ (6 * ε / B ^ 2 + 4 * D₁ / B) * 1 := by
    calc ‖_ * _‖ = ‖ER2 (Ψ τ) (deriv Ψ τ) τ B μ‖ * ‖((χ μ : ℝ) : ℂ)‖ :=
          norm_mul _ _
      _ ≤ (6 * ε / B ^ 2 + 4 * D₁ / B) * 1 :=
          mul_le_mul b2 c0 (norm_nonneg _) (by positivity)
  have t2 : ‖2 * ER1 (Ψ τ) (deriv Ψ τ) τ B μ * ((deriv χ μ : ℝ) : ℂ)‖
      ≤ 2 * (3 / 2 * ε / B + D₁) * (K / B) := by
    have h2 : ‖2 * ER1 (Ψ τ) (deriv Ψ τ) τ B μ * ((deriv χ μ : ℝ) : ℂ)‖
        = (2 * ‖ER1 (Ψ τ) (deriv Ψ τ) τ B μ‖) * ‖((deriv χ μ : ℝ) : ℂ)‖ := by
      rw [mul_assoc, norm_mul, norm_mul, norm_two_C, mul_assoc]
    rw [h2]
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left b1 (by norm_num)) c1 (norm_nonneg _) (by positivity)
  have t3 : ‖ER (Ψ τ) (deriv Ψ τ) τ B μ * ((deriv (deriv χ) μ : ℝ) : ℂ)‖
      ≤ (ε + 4 / 27 * B * D₁) * (K / B ^ 2) := by
    calc ‖_ * _‖
          = ‖ER (Ψ τ) (deriv Ψ τ) τ B μ‖ * ‖((deriv (deriv χ) μ : ℝ) : ℂ)‖ :=
          norm_mul _ _
      _ ≤ (ε + 4 / 27 * B * D₁) * (K / B ^ 2) :=
          mul_le_mul b0 c2 (norm_nonneg _) (by positivity)
  have htri : ‖(HatR2 τ B Ψ χ) μ‖
      ≤ ‖ER2 (Ψ τ) (deriv Ψ τ) τ B μ * ((χ μ : ℝ) : ℂ)‖
        + ‖2 * ER1 (Ψ τ) (deriv Ψ τ) τ B μ * ((deriv χ μ : ℝ) : ℂ)‖
        + ‖ER (Ψ τ) (deriv Ψ τ) τ B μ * ((deriv (deriv χ) μ : ℝ) : ℂ)‖ := by
    simp only [HatR2]
    exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  refine htri.trans ((add_le_add (add_le_add t1 t2) t3).trans (le_of_eq ?_))
  have hBne : B ≠ 0 := ne_of_gt hB0
  field_simp
  ring

/-- Per-collar function sup bound (right, for `A`). -/
lemma norm_HatR_collar (hτ : 1 ≤ τ) (hB0 : 0 < B) (hε0 : 0 < ε) (hD₁ : 0 ≤ D₁) (hΨ0 : ∀ μ : ℝ, |μ| ≤ τ → ‖Ψ μ‖ ≤ ε) (hΨ1 : ∀ μ : ℝ, |μ| ≤ τ → ‖deriv Ψ μ‖ ≤ D₁) (hχb : ∀ μ : ℝ, |χ μ| ≤ 1) {μ : ℝ} (hm : μ ∈ Set.Icc τ (τ + B)) :
    ‖(HatR τ B Ψ χ) μ‖ ≤ ε + 4 / 27 * B * D₁ := by
  have hp₀ : ‖Ψ τ‖ ≤ ε := hΨ0 τ (by rw [abs_le]; constructor <;> linarith [hτ])
  have hp₁ : ‖deriv Ψ τ‖ ≤ D₁ := hΨ1 τ (by rw [abs_le]; constructor <;> linarith [hτ])
  have b0 := norm_ER_le (τ := τ) (B := B) hB0 hε0 hD₁ (Ψ τ) (deriv Ψ τ) hp₀ hp₁ hm
  have c0 := (norm_coe_chi hχb) μ
  calc ‖(HatR τ B Ψ χ) μ‖ = ‖ER (Ψ τ) (deriv Ψ τ) τ B μ‖ * ‖((χ μ : ℝ) : ℂ)‖ := by
          simp only [HatR, norm_mul]
    _ ≤ (ε + 4 / 27 * B * D₁) * 1 :=
        mul_le_mul b0 c0 (norm_nonneg _) (by positivity)
    _ = ε + 4 / 27 * B * D₁ := mul_one _

/-- Per-collar second-derivative sup bound (left). -/
lemma norm_HatL2_collar (hτ : 1 ≤ τ) (hB0 : 0 < B) (hε0 : 0 < ε) (hD₁ : 0 ≤ D₁) (hΨ0 : ∀ μ : ℝ, |μ| ≤ τ → ‖Ψ μ‖ ≤ ε) (hΨ1 : ∀ μ : ℝ, |μ| ≤ τ → ‖deriv Ψ μ‖ ≤ D₁) (hχb : ∀ μ : ℝ, |χ μ| ≤ 1) (hχd1 : ∀ μ : ℝ, ‖deriv χ μ‖ ≤ K / B) (hχd2 : ∀ μ : ℝ, ‖deriv (deriv χ) μ‖ ≤ K / B ^ 2) {μ : ℝ} (hm : μ ∈ Set.Icc (-(τ + B)) (-τ)) :
    ‖(HatL2 τ B Ψ χ) μ‖ ≤ (6 + 4 * K) * ε / B ^ 2 + (4 + 2 * K + 4 * K / 27) * D₁ / B := by
  have hnt : |(-τ)| ≤ τ := by
    rw [abs_neg, abs_le]
    refine ⟨by linarith [hτ], le_rfl⟩
  have hq₀ : ‖Ψ (-τ)‖ ≤ ε := hΨ0 (-τ) hnt
  have hq₁ : ‖deriv Ψ (-τ)‖ ≤ D₁ := hΨ1 (-τ) hnt
  have b0 := norm_EL_le (τ := τ) (B := B) hB0 hε0 hD₁ (Ψ (-τ)) (deriv Ψ (-τ)) hq₀ hq₁ hm
  have b1 := norm_EL1_le (τ := τ) (B := B) hB0 hε0 hD₁ (Ψ (-τ)) (deriv Ψ (-τ)) hq₀ hq₁ hm
  have b2 := norm_EL2_le (τ := τ) (B := B) hB0 hε0 hD₁ (Ψ (-τ)) (deriv Ψ (-τ)) hq₀ hq₁ hm
  have c0 := (norm_coe_chi hχb) μ
  have c1 := (norm_coe_dchi hχd1) μ
  have c2 := (norm_coe_ddchi hχd2) μ
  have t1 : ‖EL2 (Ψ (-τ)) (deriv Ψ (-τ)) τ B μ * ((χ μ : ℝ) : ℂ)‖
      ≤ (6 * ε / B ^ 2 + 4 * D₁ / B) * 1 := by
    calc ‖_ * _‖ = ‖EL2 (Ψ (-τ)) (deriv Ψ (-τ)) τ B μ‖ * ‖((χ μ : ℝ) : ℂ)‖ :=
          norm_mul _ _
      _ ≤ (6 * ε / B ^ 2 + 4 * D₁ / B) * 1 :=
          mul_le_mul b2 c0 (norm_nonneg _) (by positivity)
  have t2 : ‖2 * EL1 (Ψ (-τ)) (deriv Ψ (-τ)) τ B μ * ((deriv χ μ : ℝ) : ℂ)‖
      ≤ 2 * (3 / 2 * ε / B + D₁) * (K / B) := by
    have h2 : ‖2 * EL1 (Ψ (-τ)) (deriv Ψ (-τ)) τ B μ * ((deriv χ μ : ℝ) : ℂ)‖
        = (2 * ‖EL1 (Ψ (-τ)) (deriv Ψ (-τ)) τ B μ‖) * ‖((deriv χ μ : ℝ) : ℂ)‖ := by
      rw [mul_assoc, norm_mul, norm_mul, norm_two_C, mul_assoc]
    rw [h2]
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left b1 (by norm_num)) c1 (norm_nonneg _) (by positivity)
  have t3 : ‖EL (Ψ (-τ)) (deriv Ψ (-τ)) τ B μ * ((deriv (deriv χ) μ : ℝ) : ℂ)‖
      ≤ (ε + 4 / 27 * B * D₁) * (K / B ^ 2) := by
    calc ‖_ * _‖
          = ‖EL (Ψ (-τ)) (deriv Ψ (-τ)) τ B μ‖ * ‖((deriv (deriv χ) μ : ℝ) : ℂ)‖ :=
          norm_mul _ _
      _ ≤ (ε + 4 / 27 * B * D₁) * (K / B ^ 2) :=
          mul_le_mul b0 c2 (norm_nonneg _) (by positivity)
  have htri : ‖(HatL2 τ B Ψ χ) μ‖
      ≤ ‖EL2 (Ψ (-τ)) (deriv Ψ (-τ)) τ B μ * ((χ μ : ℝ) : ℂ)‖
        + ‖2 * EL1 (Ψ (-τ)) (deriv Ψ (-τ)) τ B μ * ((deriv χ μ : ℝ) : ℂ)‖
        + ‖EL (Ψ (-τ)) (deriv Ψ (-τ)) τ B μ * ((deriv (deriv χ) μ : ℝ) : ℂ)‖ := by
    simp only [HatL2]
    exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  refine htri.trans ((add_le_add (add_le_add t1 t2) t3).trans (le_of_eq ?_))
  have hBne : B ≠ 0 := ne_of_gt hB0
  field_simp
  ring

/-- Per-collar function sup bound (left, for `A`). -/
lemma norm_HatL_collar (hτ : 1 ≤ τ) (hB0 : 0 < B) (hε0 : 0 < ε) (hD₁ : 0 ≤ D₁) (hΨ0 : ∀ μ : ℝ, |μ| ≤ τ → ‖Ψ μ‖ ≤ ε) (hΨ1 : ∀ μ : ℝ, |μ| ≤ τ → ‖deriv Ψ μ‖ ≤ D₁) (hχb : ∀ μ : ℝ, |χ μ| ≤ 1) {μ : ℝ} (hm : μ ∈ Set.Icc (-(τ + B)) (-τ)) :
    ‖(HatL τ B Ψ χ) μ‖ ≤ ε + 4 / 27 * B * D₁ := by
  have hnt : |(-τ)| ≤ τ := by
    rw [abs_neg, abs_le]
    refine ⟨by linarith [hτ], le_rfl⟩
  have hq₀ : ‖Ψ (-τ)‖ ≤ ε := hΨ0 (-τ) hnt
  have hq₁ : ‖deriv Ψ (-τ)‖ ≤ D₁ := hΨ1 (-τ) hnt
  have b0 := norm_EL_le (τ := τ) (B := B) hB0 hε0 hD₁ (Ψ (-τ)) (deriv Ψ (-τ)) hq₀ hq₁ hm
  have c0 := (norm_coe_chi hχb) μ
  calc ‖(HatL τ B Ψ χ) μ‖ = ‖EL (Ψ (-τ)) (deriv Ψ (-τ)) τ B μ‖ * ‖((χ μ : ℝ) : ℂ)‖ := by
          simp only [HatL, norm_mul]
    _ ≤ (ε + 4 / 27 * B * D₁) * 1 :=
        mul_le_mul b0 c0 (norm_nonneg _) (by positivity)
    _ = ε + 4 / 27 * B * D₁ := mul_one _

/-! ### Continuity (from `HasDerivAt` for first-order pieces, from `ContDiff`
for second derivatives, `fun_prop` for the real polynomials). -/

private lemma cont_Psi (hΨ : ContDiff ℝ 2 Ψ) : Continuous Ψ :=
  (hΨ.differentiable (by norm_num)).continuous

private lemma cont_dPsi (hΨ : ContDiff ℝ 2 Ψ) : Continuous (deriv Ψ) :=
  hΨ.differentiable_deriv_two.continuous

private lemma cont_d2Psi (hΨ : ContDiff ℝ 2 Ψ) : Continuous (deriv (deriv Ψ)) := by
  have h1 : ContDiff ℝ 1 (deriv Ψ) := by simpa using hΨ.deriv'
  exact h1.continuous_deriv (by norm_num)

private lemma cont_Chi (hχ : ContDiff ℝ 2 χ) : Continuous χ :=
  (hχ.differentiable (by norm_num)).continuous

private lemma cont_dChi (hχ : ContDiff ℝ 2 χ) : Continuous (deriv χ) :=
  hχ.differentiable_deriv_two.continuous

private lemma cont_d2Chi (hχ : ContDiff ℝ 2 χ) : Continuous (deriv (deriv χ)) := by
  have h1 : ContDiff ℝ 1 (deriv χ) := by simpa using hχ.deriv'
  exact h1.continuous_deriv (by norm_num)

private lemma cont_ChiC (hχ : ContDiff ℝ 2 χ) : Continuous fun μ : ℝ => ((χ μ : ℝ) : ℂ) :=
  Complex.continuous_ofReal.comp ((cont_Chi hχ))

private lemma cont_dChiC (hχ : ContDiff ℝ 2 χ) : Continuous fun μ : ℝ => ((deriv χ μ : ℝ) : ℂ) :=
  Complex.continuous_ofReal.comp ((cont_dChi hχ))

private lemma cont_d2ChiC (hχ : ContDiff ℝ 2 χ) :
    Continuous fun μ : ℝ => ((deriv (deriv χ) μ : ℝ) : ℂ) :=
  Complex.continuous_ofReal.comp ((cont_d2Chi hχ))

private lemma cont_eta : Continuous eta := by
  show Continuous fun s : ℝ => 1 - 3 * s ^ 2 + 2 * s ^ 3
  fun_prop

private lemma cont_eta1 : Continuous eta1 := by
  show Continuous fun s : ℝ => s - 2 * s ^ 2 + s ^ 3
  fun_prop

private lemma cont_etaD : Continuous etaD := by
  show Continuous fun s : ℝ => -6 * s + 6 * s ^ 2
  fun_prop

private lemma cont_eta1D : Continuous eta1D := by
  show Continuous fun s : ℝ => 1 - 4 * s + 3 * s ^ 2
  fun_prop

private lemma cont_etaDD : Continuous etaDD := by
  show Continuous fun s : ℝ => -6 + 12 * s
  fun_prop

private lemma cont_eta1DD : Continuous eta1DD := by
  show Continuous fun s : ℝ => -4 + 6 * s
  fun_prop

private lemma cont_affR : Continuous fun ν : ℝ => (ν - τ) / B := by fun_prop

private lemma cont_affL : Continuous fun ν : ℝ => (-ν - τ) / B := by fun_prop

lemma cont_ER (p₀ p₁ : ℂ) : Continuous (ER p₀ p₁ τ B) :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_ER (τ := τ) (B := B) p₀ p₁).continuousAt

lemma cont_ER1 (hB0 : 0 < B) (p₀ p₁ : ℂ) : Continuous (ER1 p₀ p₁ τ B) :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_ER1 (τ := τ) (B := B) hB0 p₀ p₁).continuousAt

lemma cont_EL (q₀ q₁ : ℂ) : Continuous (EL q₀ q₁ τ B) :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_EL (τ := τ) (B := B) q₀ q₁).continuousAt

lemma cont_EL1 (hB0 : 0 < B) (q₀ q₁ : ℂ) : Continuous (EL1 q₀ q₁ τ B) :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_EL1 (τ := τ) (B := B) hB0 q₀ q₁).continuousAt

lemma cont_ER2 (p₀ p₁ : ℂ) : Continuous (ER2 p₀ p₁ τ B) := by
  show Continuous fun μ : ℝ => p₀ * ((etaDD ((μ - τ) / B) * ((1 / B) * (1 / B)) : ℝ) : ℂ)
    + p₁ * ((eta1DD ((μ - τ) / B) * (1 / B) : ℝ) : ℂ)
  exact (continuous_const.mul (Complex.continuous_ofReal.comp
      ((cont_etaDD.comp cont_affR).mul continuous_const))).add
    (continuous_const.mul (Complex.continuous_ofReal.comp
      ((cont_eta1DD.comp cont_affR).mul continuous_const)))

lemma cont_EL2 (q₀ q₁ : ℂ) : Continuous (EL2 q₀ q₁ τ B) := by
  show Continuous fun μ : ℝ => q₀ * ((etaDD ((-μ - τ) / B) * ((1 / B) * (1 / B)) : ℝ) : ℂ)
    - q₁ * ((eta1DD ((-μ - τ) / B) * (1 / B) : ℝ) : ℂ)
  exact (continuous_const.mul (Complex.continuous_ofReal.comp
      ((cont_etaDD.comp cont_affL).mul continuous_const))).sub
    (continuous_const.mul (Complex.continuous_ofReal.comp
      ((cont_eta1DD.comp cont_affL).mul continuous_const)))

lemma cont_HatM (hΨ : ContDiff ℝ 2 Ψ) (hχ : ContDiff ℝ 2 χ) : Continuous (HatM Ψ χ) := (cont_Psi hΨ).mul (cont_ChiC hχ)

lemma cont_HatM1 (hΨ : ContDiff ℝ 2 Ψ) (hχ : ContDiff ℝ 2 χ) : Continuous (HatM1 Ψ χ) :=
  ((cont_dPsi hΨ).mul (cont_ChiC hχ)).add ((cont_Psi hΨ).mul (cont_dChiC hχ))

lemma cont_HatM2 (hΨ : ContDiff ℝ 2 Ψ) (hχ : ContDiff ℝ 2 χ) : Continuous (HatM2 Ψ χ) :=
  (((cont_d2Psi hΨ).mul (cont_ChiC hχ)).add
    ((continuous_const.mul (cont_dPsi hΨ)).mul (cont_dChiC hχ))).add
    ((cont_Psi hΨ).mul (cont_d2ChiC hχ))

lemma cont_HatR (hχ : ContDiff ℝ 2 χ) : Continuous (HatR τ B Ψ χ) :=
  (cont_ER _ _).mul (cont_ChiC hχ)

lemma cont_HatR1 (hB0 : 0 < B) (hχ : ContDiff ℝ 2 χ) : Continuous (HatR1 τ B Ψ χ) :=
  ((cont_ER1 hB0 _ _).mul (cont_ChiC hχ)).add ((cont_ER _ _).mul (cont_dChiC hχ))

lemma cont_HatR2 (hB0 : 0 < B) (hχ : ContDiff ℝ 2 χ) : Continuous (HatR2 τ B Ψ χ) :=
  (((cont_ER2 _ _).mul (cont_ChiC hχ)).add
    (((continuous_const.mul (cont_ER1 hB0 _ _)).mul (cont_dChiC hχ)))).add
    ((cont_ER _ _).mul (cont_d2ChiC hχ))

lemma cont_HatL (hχ : ContDiff ℝ 2 χ) : Continuous (HatL τ B Ψ χ) :=
  (cont_EL _ _).mul (cont_ChiC hχ)

lemma cont_HatL1 (hB0 : 0 < B) (hχ : ContDiff ℝ 2 χ) : Continuous (HatL1 τ B Ψ χ) :=
  ((cont_EL1 hB0 _ _).mul (cont_ChiC hχ)).add ((cont_EL _ _).mul (cont_dChiC hχ))

lemma cont_HatL2 (hB0 : 0 < B) (hχ : ContDiff ℝ 2 χ) : Continuous (HatL2 τ B Ψ χ) :=
  (((cont_EL2 _ _).mul (cont_ChiC hχ)).add
    (((continuous_const.mul (cont_EL1 hB0 _ _)).mul (cont_dChiC hχ)))).add
    ((cont_EL _ _).mul (cont_d2ChiC hχ))

/-! ## 6. Fourier weight and one-step integration by parts with boundary. -/

/-- Fourier weight `E(t, μ) = e^{−iμt}`. -/
noncomputable def Efun (t μ : ℝ) : ℂ :=
  Complex.exp (-((μ : ℂ) * Complex.I * (t : ℂ)))

lemma norm_Efun (t μ : ℝ) : ‖Efun t μ‖ = 1 := by
  simp only [Efun, Complex.norm_exp]
  have hre : (-((μ : ℂ) * Complex.I * (t : ℂ))).re = 0 := by
    simp [Complex.mul_re]
  rw [hre, Real.exp_zero]

lemma hasDerivAt_Efun (t μ : ℝ) :
    HasDerivAt (fun ν : ℝ => Efun t ν) (Efun t μ * (-(Complex.I * (t : ℂ)))) μ := by
  have h1 : HasDerivAt (fun ν : ℝ => (ν : ℂ) * Complex.I * (t : ℂ))
      (Complex.I * (t : ℂ)) μ := by
    have h0 : HasDerivAt (fun ν : ℝ => (ν : ℂ)) (1 : ℂ) μ := by
      simpa using HasDerivAt.ofReal_comp (hasDerivAt_id μ)
    simpa only [mul_assoc, one_mul] using h0.mul_const (Complex.I * (t : ℂ))
  exact h1.neg.cexp

lemma cont_Efun (t : ℝ) : Continuous fun μ : ℝ => Efun t μ := by
  unfold Efun
  fun_prop

lemma cont_Efun_t (μ : ℝ) : Continuous fun t : ℝ => Efun t μ := by
  unfold Efun
  fun_prop

/-- One integration by parts against the Fourier weight, keeping boundary terms:
`∫_a^b f' E = [fE]_a^b + it ∫_a^b fE`. -/
lemma ibp_once (f f₁ : ℝ → ℂ) (a b t : ℝ)
    (hf : ∀ x ∈ Set.uIcc a b, HasDerivAt f (f₁ x) x)
    (hfcont : Continuous f)
    (hA : IntervalIntegrable (fun x => f₁ x * Efun t x) volume a b)
    (hB : IntervalIntegrable (fun x => f x * Efun t x) volume a b) :
    ∫ x in a..b, f₁ x * Efun t x =
      (f b * Efun t b - f a * Efun t a)
        + (t : ℂ) * Complex.I * ∫ x in a..b, f x * Efun t x := by
  have hE : ∀ x : ℝ,
      HasDerivAt (fun ν : ℝ => Efun t ν) (Efun t x * (-(Complex.I * (t : ℂ)))) x :=
    fun x => hasDerivAt_Efun t x
  have hprod : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun μ : ℝ => f μ * Efun t μ)
      (f₁ x * Efun t x + f x * (Efun t x * (-(Complex.I * (t : ℂ))))) x :=
    fun x hx => (hf x hx).mul (hE x)
  have hC : IntervalIntegrable
      (fun x => f x * (Efun t x * (-(Complex.I * (t : ℂ))))) volume a b :=
    (hfcont.mul ((cont_Efun t).mul continuous_const)).intervalIntegrable _ _
  have hsum := hA.add hC
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hprod hsum
  have hsplit := intervalIntegral.integral_add hA hC
  have hval : ∫ x in a..b, f x * (Efun t x * (-(Complex.I * (t : ℂ))))
      = (-(Complex.I * (t : ℂ))) * ∫ x in a..b, f x * Efun t x := by
    have h1 : ∫ x in a..b, f x * (Efun t x * (-(Complex.I * (t : ℂ))))
        = ∫ x in a..b, (-(Complex.I * (t : ℂ))) * (f x * Efun t x) := by
      refine intervalIntegral.integral_congr (fun x _ => by ring)
    rw [h1, intervalIntegral.integral_const_mul]
  have key : (∫ x in a..b, f₁ x * Efun t x)
        + (-(Complex.I * (t : ℂ))) * ∫ x in a..b, f x * Efun t x
      = (f b * Efun t b - f a * Efun t a) := by
    linear_combination hFTC - hsplit - hval
  calc ∫ x in a..b, f₁ x * Efun t x
      = (((∫ x in a..b, f₁ x * Efun t x)
          + (-(Complex.I * (t : ℂ))) * ∫ x in a..b, f x * Efun t x)
        - (-(Complex.I * (t : ℂ))) * ∫ x in a..b, f x * Efun t x) := by ring
    _ = (f b * Efun t b - f a * Efun t a)
        - (-(Complex.I * (t : ℂ))) * ∫ x in a..b, f x * Efun t x := by rw [key]
    _ = (f b * Efun t b - f a * Efun t a)
        + (t : ℂ) * Complex.I * ∫ x in a..b, f x * Efun t x := by ring

/-! ## 7. The global `κ̂`, the kernel `κ`, and the two pointwise bounds. -/

/-- Hermite-cubic extension: `Ψ` on the band, Hermite cubics on the collars,
`0` outside. -/
noncomputable def PsiExt (τ B : ℝ) (Ψ : ℝ → ℂ) (μ : ℝ) : ℂ :=
  if μ ∈ Set.Icc (-τ) τ then Ψ μ
  else if μ ∈ Set.Ioc τ (τ + B) then ER (Ψ τ) (deriv Ψ τ) τ B μ
  else if μ ∈ Set.Ico (-(τ + B)) (-τ) then EL (Ψ (-τ)) (deriv Ψ (-τ)) τ B μ
  else 0

/-- `κ̂ := Ψ_ext · χ`. -/
noncomputable def HatK (τ B : ℝ) (Ψ : ℝ → ℂ) (χ : ℝ → ℝ) (μ : ℝ) : ℂ := PsiExt τ B Ψ μ * ((χ μ : ℝ) : ℂ)

/-- `κ(t) := (2π)⁻¹ ∫ κ̂(μ) e^{−iμt} dμ` (inverse Fourier transform). -/
noncomputable def kap (τ B : ℝ) (Ψ : ℝ → ℂ) (χ : ℝ → ℝ) (t : ℝ) : ℂ :=
  ((2 * Real.pi)⁻¹ : ℝ) • (∫ μ in (-(τ + B))..(τ + B), (HatK τ B Ψ χ) μ * Efun t μ)

/-- Explicit majorant `A := 2(τ+B)(ε + (4/27)·B·D₁)`. -/
noncomputable def RealizeA (τ B ε D₁ : ℝ) : ℝ := 2 * (τ + B) * (ε + 4 / 27 * B * D₁)

/-- Explicit majorant `C := 2τ·D₂ + 2·((6+4K)·ε/B + (4+2K+4K/27)·D₁)`
(two collar terms — one per collar). -/
noncomputable def RealizeC (τ B ε D₁ D₂ K : ℝ) : ℝ :=
  2 * τ * D₂ + 2 * ((6 + 4 * K) * ε / B + (4 + 2 * K + 4 * K / 27) * D₁)

lemma PsiExt_band {μ : ℝ} (hm : μ ∈ Set.Icc (-τ) τ) : (PsiExt τ B Ψ) μ = Ψ μ := by
  unfold PsiExt
  rw [if_pos hm]

lemma PsiExt_collarR (hτ : 1 ≤ τ) {μ : ℝ} (hm : μ ∈ Set.Ioc τ (τ + B)) :
    (PsiExt τ B Ψ) μ = ER (Ψ τ) (deriv Ψ τ) τ B μ := by
  have h1 : μ ∉ Set.Icc (-τ) τ := by
    intro hc
    obtain ⟨-, hhi⟩ := Set.mem_Icc.mp hc
    obtain ⟨hlt, -⟩ := Set.mem_Ioc.mp hm
    linarith
  unfold PsiExt
  rw [if_neg h1, if_pos hm]

lemma PsiExt_collarL (hτ : 1 ≤ τ) {μ : ℝ} (hm : μ ∈ Set.Ico (-(τ + B)) (-τ)) :
    (PsiExt τ B Ψ) μ = EL (Ψ (-τ)) (deriv Ψ (-τ)) τ B μ := by
  have h1 : μ ∉ Set.Icc (-τ) τ := by
    intro hc
    obtain ⟨hlo, -⟩ := Set.mem_Icc.mp hc
    obtain ⟨-, hhi⟩ := Set.mem_Ico.mp hm
    linarith
  have h2 : μ ∉ Set.Ioc τ (τ + B) := by
    intro hc
    obtain ⟨hlt, -⟩ := Set.mem_Ioc.mp hc
    obtain ⟨-, hhi⟩ := Set.mem_Ico.mp hm
    linarith [hτ]
  unfold PsiExt
  rw [if_neg h1, if_neg h2, if_pos hm]

/-- `κ̂ = Ψ` on the band. -/
lemma HatK_band (hχ1 : ∀ μ : ℝ, |μ| ≤ τ → χ μ = 1) {μ : ℝ} (habs : |μ| ≤ τ) : (HatK τ B Ψ χ) μ = Ψ μ := by
  have hm : μ ∈ Set.Icc (-τ) τ := Set.mem_Icc.mpr (abs_le.mp habs)
  have h1 : χ μ = 1 := hχ1 μ habs
  simp only [HatK, PsiExt_band hm, h1, Complex.ofReal_one, mul_one]

lemma HatK_eq_HatM_on (hτ : 1 ≤ τ) : Set.EqOn (HatK τ B Ψ χ) (HatM Ψ χ) (Set.uIcc (-τ) τ) := by
  have hle : -τ ≤ τ := by linarith [hτ]
  intro x hx
  rw [Set.uIcc_of_le hle] at hx
  obtain ⟨hlo, hhi⟩ := Set.mem_Icc.mp hx
  have hxI : x ∈ Set.Icc (-τ) τ := Set.mem_Icc.mpr ⟨hlo, hhi⟩
  simp only [HatK, HatM, PsiExt_band hxI]

lemma HatK_eq_HatR_on (hτ : 1 ≤ τ) (hB0 : 0 < B) : Set.EqOn (HatK τ B Ψ χ) (HatR τ B Ψ χ) (Set.uIcc τ (τ + B)) := by
  have hle : τ ≤ τ + B := by linarith [hB0.le]
  intro x hx
  rw [Set.uIcc_of_le hle] at hx
  obtain ⟨hlo, hhi⟩ := Set.mem_Icc.mp hx
  rcases eq_or_lt_of_le hlo with rfl | hlt
  · have hb : τ ∈ Set.Icc (-τ) τ := Set.mem_Icc.mpr ⟨by linarith [hτ], le_rfl⟩
    simp only [HatK, HatR, PsiExt_band hb, (ER_at_left (τ := τ) (B := B) hB0 (Ψ τ) (deriv Ψ τ)).1]
  · have hm : x ∈ Set.Ioc τ (τ + B) := Set.mem_Ioc.mpr ⟨hlt, hhi⟩
    simp only [HatK, HatR, PsiExt_collarR hτ hm]

lemma HatK_eq_HatL_on (hτ : 1 ≤ τ) (hB0 : 0 < B) : Set.EqOn (HatK τ B Ψ χ) (HatL τ B Ψ χ) (Set.uIcc (-(τ + B)) (-τ)) := by
  have hle : -(τ + B) ≤ -τ := by linarith [hB0.le]
  intro x hx
  rw [Set.uIcc_of_le hle] at hx
  obtain ⟨hlo, hhi⟩ := Set.mem_Icc.mp hx
  rcases eq_or_lt_of_le hhi with rfl | hlt
  · have hb : (-τ) ∈ Set.Icc (-τ) τ :=
      Set.mem_Icc.mpr ⟨le_rfl, by linarith [hτ]⟩
    simp only [HatK, HatL, PsiExt_band hb, (EL_at_right (τ := τ) (B := B) hB0 (Ψ (-τ)) (deriv Ψ (-τ))).1]
  · have hm : x ∈ Set.Ico (-(τ + B)) (-τ) := Set.mem_Ico.mpr ⟨hlo, hlt⟩
    simp only [HatK, HatL, PsiExt_collarL hτ hm]

/-- Split `κ`'s integral into the three smooth pieces. -/
lemma kap_eq_sum (hτ : 1 ≤ τ) (hB0 : 0 < B) (hΨ : ContDiff ℝ 2 Ψ) (hχ : ContDiff ℝ 2 χ) (t : ℝ) : (kap τ B Ψ χ) t
    = ((2 * Real.pi)⁻¹ : ℝ) • ((∫ μ in (-(τ + B))..(-τ), (HatL τ B Ψ χ) μ * Efun t μ)
      + ((∫ μ in (-τ)..τ, (HatM Ψ χ) μ * Efun t μ)
      + (∫ μ in τ..(τ + B), (HatR τ B Ψ χ) μ * Efun t μ))) := by
  have hL : IntervalIntegrable (fun μ => (HatL τ B Ψ χ) μ * Efun t μ) volume (-(τ + B)) (-τ) :=
    ((cont_HatL hχ).mul (cont_Efun t)).intervalIntegrable _ _
  have hM : IntervalIntegrable (fun μ => (HatM Ψ χ) μ * Efun t μ) volume (-τ) τ :=
    ((cont_HatM hΨ hχ).mul (cont_Efun t)).intervalIntegrable _ _
  have hR : IntervalIntegrable (fun μ => (HatR τ B Ψ χ) μ * Efun t μ) volume τ (τ + B) :=
    ((cont_HatR hχ).mul (cont_Efun t)).intervalIntegrable _ _
  have eL : Set.EqOn (fun μ => (HatK τ B Ψ χ) μ * Efun t μ) (fun μ => (HatL τ B Ψ χ) μ * Efun t μ)
      (Set.uIcc (-(τ + B)) (-τ)) := fun x hx => by
    show (HatK τ B Ψ χ) x * Efun t x = (HatL τ B Ψ χ) x * Efun t x
    rw [HatK_eq_HatL_on hτ hB0 hx]
  have eM : Set.EqOn (fun μ => (HatK τ B Ψ χ) μ * Efun t μ) (fun μ => (HatM Ψ χ) μ * Efun t μ)
      (Set.uIcc (-τ) τ) := fun x hx => by
    show (HatK τ B Ψ χ) x * Efun t x = (HatM Ψ χ) x * Efun t x
    rw [HatK_eq_HatM_on hτ hx]
  have eR : Set.EqOn (fun μ => (HatK τ B Ψ χ) μ * Efun t μ) (fun μ => (HatR τ B Ψ χ) μ * Efun t μ)
      (Set.uIcc τ (τ + B)) := fun x hx => by
    show (HatK τ B Ψ χ) x * Efun t x = (HatR τ B Ψ χ) x * Efun t x
    rw [HatK_eq_HatR_on hτ hB0 hx]
  have hKL : IntervalIntegrable (fun μ => (HatK τ B Ψ χ) μ * Efun t μ) volume (-(τ + B)) (-τ) :=
    IntervalIntegrable.congr (Set.EqOn.mono Set.uIoc_subset_uIcc eL.symm) hL
  have hKM : IntervalIntegrable (fun μ => (HatK τ B Ψ χ) μ * Efun t μ) volume (-τ) τ :=
    IntervalIntegrable.congr (Set.EqOn.mono Set.uIoc_subset_uIcc eM.symm) hM
  have hKR : IntervalIntegrable (fun μ => (HatK τ B Ψ χ) μ * Efun t μ) volume τ (τ + B) :=
    IntervalIntegrable.congr (Set.EqOn.mono Set.uIoc_subset_uIcc eR.symm) hR
  have e1 : (∫ μ in (-(τ + B))..(τ + B), (HatK τ B Ψ χ) μ * Efun t μ)
      = (∫ μ in (-(τ + B))..(-τ), (HatK τ B Ψ χ) μ * Efun t μ)
        + (∫ μ in (-τ)..(τ + B), (HatK τ B Ψ χ) μ * Efun t μ) :=
    (intervalIntegral.integral_add_adjacent_intervals hKL (hKM.trans hKR)).symm
  have e2 : (∫ μ in (-τ)..(τ + B), (HatK τ B Ψ χ) μ * Efun t μ)
      = (∫ μ in (-τ)..τ, (HatK τ B Ψ χ) μ * Efun t μ)
        + (∫ μ in τ..(τ + B), (HatK τ B Ψ χ) μ * Efun t μ) :=
    (intervalIntegral.integral_add_adjacent_intervals hKM hKR).symm
  simp only [kap]
  have esplit : (∫ μ in (-(τ + B))..(τ + B), (HatK τ B Ψ χ) μ * Efun t μ)
      = (∫ μ in (-(τ + B))..(-τ), (HatK τ B Ψ χ) μ * Efun t μ)
        + ((∫ μ in (-τ)..τ, (HatK τ B Ψ χ) μ * Efun t μ)
        + (∫ μ in τ..(τ + B), (HatK τ B Ψ χ) μ * Efun t μ)) := by
    rw [e1, e2]
  rw [esplit,
    intervalIntegral.integral_congr eL,
    intervalIntegral.integral_congr eM,
    intervalIntegral.integral_congr eR]

/-! ### Piece integral bounds (function values: for `A`). -/

/-- `‖a * Efun‖ ≤ M` from `‖a‖ ≤ M` (pure; avoids Pi.mul display issues). -/
lemma norm_mul_Efun_le (a : ℂ) (M : ℝ) (t μ : ℝ) (h : ‖a‖ ≤ M) :
    ‖a * Efun t μ‖ ≤ M := by
  rw [norm_mul, norm_Efun, mul_one]
  exact h

private lemma int_piece_le (f : ℝ → ℂ) (M : ℝ) (a b : ℝ) (hab : a ≤ b)
    (hf : Continuous f) (hM : ∀ x ∈ Set.Icc a b, ‖f x‖ ≤ M) :
    ‖∫ x in a..b, f x‖ ≤ (b - a) * M := by
  refine (intervalIntegral.norm_integral_le_integral_norm hab).trans ?_
  have hmono : ∫ x in a..b, ‖f x‖ ≤ ∫ _ in a..b, M := by
    apply intervalIntegral.integral_mono_on hab
      (hf.norm.intervalIntegrable a b) (continuous_const.intervalIntegrable a b)
    intro x hx
    exact hM x hx
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  exact hmono

lemma int_HatM_le (hτ : 1 ≤ τ) (hΨ : ContDiff ℝ 2 Ψ) (hΨ0 : ∀ μ : ℝ, |μ| ≤ τ → ‖Ψ μ‖ ≤ ε) (hχ : ContDiff ℝ 2 χ) (hχ1 : ∀ μ : ℝ, |μ| ≤ τ → χ μ = 1) (t : ℝ) : ‖(∫ μ in (-τ)..τ, (HatM Ψ χ) μ * Efun t μ)‖ ≤ 2 * τ * ε := by
  have h := int_piece_le (fun μ => (HatM Ψ χ) μ * Efun t μ) ε (-τ) τ (by linarith [hτ])
    ((cont_HatM hΨ hχ).mul (cont_Efun t)) (fun x hx => by
      exact norm_mul_Efun_le _ _ _ _ ((norm_HatM_band hΨ0 hχ1) hx))
  rwa [show τ - -τ = 2 * τ by ring] at h

lemma int_HatR_le (hτ : 1 ≤ τ) (hB0 : 0 < B) (hε0 : 0 < ε) (hD₁ : 0 ≤ D₁) (hΨ : ContDiff ℝ 2 Ψ) (hΨ0 : ∀ μ : ℝ, |μ| ≤ τ → ‖Ψ μ‖ ≤ ε) (hΨ1 : ∀ μ : ℝ, |μ| ≤ τ → ‖deriv Ψ μ‖ ≤ D₁) (hχ : ContDiff ℝ 2 χ) (hχb : ∀ μ : ℝ, |χ μ| ≤ 1) (t : ℝ) :
    ‖(∫ μ in τ..(τ + B), (HatR τ B Ψ χ) μ * Efun t μ)‖ ≤ B * (ε + 4 / 27 * B * D₁) := by
  have h := int_piece_le (fun μ => (HatR τ B Ψ χ) μ * Efun t μ) (ε + 4 / 27 * B * D₁)
    τ (τ + B) (by linarith [hB0.le])
    ((cont_HatR hχ).mul (cont_Efun t)) (fun x hx => by
      exact norm_mul_Efun_le _ _ _ _ ((norm_HatR_collar hτ hB0 hε0 hD₁ hΨ0 hΨ1 hχb) hx))
  rwa [show τ + B - τ = B by ring] at h

lemma int_HatL_le (hτ : 1 ≤ τ) (hB0 : 0 < B) (hε0 : 0 < ε) (hD₁ : 0 ≤ D₁) (hΨ : ContDiff ℝ 2 Ψ) (hΨ0 : ∀ μ : ℝ, |μ| ≤ τ → ‖Ψ μ‖ ≤ ε) (hΨ1 : ∀ μ : ℝ, |μ| ≤ τ → ‖deriv Ψ μ‖ ≤ D₁) (hχ : ContDiff ℝ 2 χ) (hχb : ∀ μ : ℝ, |χ μ| ≤ 1) (t : ℝ) :
    ‖(∫ μ in (-(τ + B))..(-τ), (HatL τ B Ψ χ) μ * Efun t μ)‖ ≤ B * (ε + 4 / 27 * B * D₁) := by
  have h := int_piece_le (fun μ => (HatL τ B Ψ χ) μ * Efun t μ) (ε + 4 / 27 * B * D₁)
    (-(τ + B)) (-τ) (by linarith [hB0.le])
    ((cont_HatL hχ).mul (cont_Efun t)) (fun x hx => by
      exact norm_mul_Efun_le _ _ _ _ ((norm_HatL_collar hτ hB0 hε0 hD₁ hΨ0 hΨ1 hχb) hx))
  rwa [show -τ - -(τ + B) = B by ring] at h

/-! ### Piece integral bounds (second derivatives: for `C`). -/

lemma int_HatM2_le (hτ : 1 ≤ τ) (hΨ : ContDiff ℝ 2 Ψ) (hΨ2 : ∀ μ : ℝ, |μ| ≤ τ → ‖deriv (deriv Ψ) μ‖ ≤ D₂) (hχ : ContDiff ℝ 2 χ) (hχ1 : ∀ μ : ℝ, |μ| ≤ τ → χ μ = 1) (t : ℝ) :
    ‖(∫ μ in (-τ)..τ, (HatM2 Ψ χ) μ * Efun t μ)‖ ≤ 2 * τ * D₂ := by
  refine (intervalIntegral.norm_integral_le_integral_norm (by linarith [hτ])).trans ?_
  have hmono : ∫ μ in (-τ)..τ, ‖(HatM2 Ψ χ) μ * Efun t μ‖ ≤ ∫ _ in (-τ)..τ, D₂ := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo (by linarith [hτ])
      ((((cont_HatM2 hΨ hχ).mul (cont_Efun t)).norm).intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _)
    intro x hx
    exact norm_mul_Efun_le _ _ _ _ ((norm_HatM2_band hΨ2 hχ1) hx)
  rw [intervalIntegral.integral_const, smul_eq_mul, show τ - -τ = 2 * τ by ring] at hmono
  exact hmono

lemma int_HatR2_le (hτ : 1 ≤ τ) (hB0 : 0 < B) (hε0 : 0 < ε) (hD₁ : 0 ≤ D₁) (hΨ : ContDiff ℝ 2 Ψ) (hΨ0 : ∀ μ : ℝ, |μ| ≤ τ → ‖Ψ μ‖ ≤ ε) (hΨ1 : ∀ μ : ℝ, |μ| ≤ τ → ‖deriv Ψ μ‖ ≤ D₁) (hχ : ContDiff ℝ 2 χ) (hχb : ∀ μ : ℝ, |χ μ| ≤ 1) (hχd1 : ∀ μ : ℝ, ‖deriv χ μ‖ ≤ K / B) (hχd2 : ∀ μ : ℝ, ‖deriv (deriv χ) μ‖ ≤ K / B ^ 2) (t : ℝ) : ‖(∫ μ in τ..(τ + B), (HatR2 τ B Ψ χ) μ * Efun t μ)‖
    ≤ B * ((6 + 4 * K) * ε / B ^ 2 + (4 + 2 * K + 4 * K / 27) * D₁ / B) := by
  refine (intervalIntegral.norm_integral_le_integral_norm (by linarith [hB0.le])).trans ?_
  have hmono : ∫ μ in τ..(τ + B), ‖(HatR2 τ B Ψ χ) μ * Efun t μ‖
      ≤ ∫ _ in τ..(τ + B), ((6 + 4 * K) * ε / B ^ 2
        + (4 + 2 * K + 4 * K / 27) * D₁ / B) := by
    apply intervalIntegral.integral_mono_on (by linarith [hB0.le])
      ((((cont_HatR2 hB0 hχ).mul (cont_Efun t)).norm).intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _)
    intro x hx
    exact norm_mul_Efun_le _ _ _ _ ((norm_HatR2_collar hτ hB0 hε0 hD₁ hΨ0 hΨ1 hχb hχd1 hχd2) hx)
  rw [intervalIntegral.integral_const, smul_eq_mul,
    show τ + B - τ = B by ring] at hmono
  exact hmono

lemma int_HatL2_le (hτ : 1 ≤ τ) (hB0 : 0 < B) (hε0 : 0 < ε) (hD₁ : 0 ≤ D₁) (hΨ : ContDiff ℝ 2 Ψ) (hΨ0 : ∀ μ : ℝ, |μ| ≤ τ → ‖Ψ μ‖ ≤ ε) (hΨ1 : ∀ μ : ℝ, |μ| ≤ τ → ‖deriv Ψ μ‖ ≤ D₁) (hχ : ContDiff ℝ 2 χ) (hχb : ∀ μ : ℝ, |χ μ| ≤ 1) (hχd1 : ∀ μ : ℝ, ‖deriv χ μ‖ ≤ K / B) (hχd2 : ∀ μ : ℝ, ‖deriv (deriv χ) μ‖ ≤ K / B ^ 2) (t : ℝ) : ‖(∫ μ in (-(τ + B))..(-τ), (HatL2 τ B Ψ χ) μ * Efun t μ)‖
    ≤ B * ((6 + 4 * K) * ε / B ^ 2 + (4 + 2 * K + 4 * K / 27) * D₁ / B) := by
  refine (intervalIntegral.norm_integral_le_integral_norm (by linarith [hB0.le])).trans ?_
  have hmono : ∫ μ in (-(τ + B))..(-τ), ‖(HatL2 τ B Ψ χ) μ * Efun t μ‖
      ≤ ∫ _ in (-(τ + B))..(-τ), ((6 + 4 * K) * ε / B ^ 2
        + (4 + 2 * K + 4 * K / 27) * D₁ / B) := by
    apply intervalIntegral.integral_mono_on (by linarith [hB0.le])
      ((((cont_HatL2 hB0 hχ).mul (cont_Efun t)).norm).intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _)
    intro x hx
    exact norm_mul_Efun_le _ _ _ _ ((norm_HatL2_collar hτ hB0 hε0 hD₁ hΨ0 hΨ1 hχb hχd1 hχd2) hx)
  rw [intervalIntegral.integral_const, smul_eq_mul,
    show -τ - -(τ + B) = B by ring] at hmono
  exact hmono

/-! ### Double integration by parts per piece. -/

/-- Two integrations by parts on one piece:
`(it)²∫fE = ∫f''E − ([f'E] + it[fE])`. -/
lemma piece_ibp (f f₁ f₂ : ℝ → ℂ) (a b t : ℝ)
    (hf1 : ∀ x ∈ Set.uIcc a b, HasDerivAt f (f₁ x) x)
    (hf2 : ∀ x ∈ Set.uIcc a b, HasDerivAt f₁ (f₂ x) x)
    (hc0 : Continuous f) (hc1 : Continuous f₁) (hc2 : Continuous f₂) :
    ((t : ℂ) * Complex.I * ((t : ℂ) * Complex.I)) * ∫ x in a..b, f x * Efun t x
      = (∫ x in a..b, f₂ x * Efun t x)
        - ((f₁ b * Efun t b - f₁ a * Efun t a)
          + (t : ℂ) * Complex.I * (f b * Efun t b - f a * Efun t a)) := by
  have hA1 : IntervalIntegrable (fun x => f₁ x * Efun t x) volume a b :=
    (hc1.mul (cont_Efun t)).intervalIntegrable _ _
  have hB1 : IntervalIntegrable (fun x => f x * Efun t x) volume a b :=
    (hc0.mul (cont_Efun t)).intervalIntegrable _ _
  have hA2 : IntervalIntegrable (fun x => f₂ x * Efun t x) volume a b :=
    (hc2.mul (cont_Efun t)).intervalIntegrable _ _
  have e1 := ibp_once f f₁ a b t hf1 hc0 hA1 hB1
  have e2 := ibp_once f₁ f₂ a b t hf2 hc1 hA2 hA1
  have h1 : (t : ℂ) * Complex.I * (∫ x in a..b, f x * Efun t x)
      = (∫ x in a..b, f₁ x * Efun t x) - (f b * Efun t b - f a * Efun t a) := by
    rw [e1]; ring
  have h2 : (t : ℂ) * Complex.I * (∫ x in a..b, f₁ x * Efun t x)
      = (∫ x in a..b, f₂ x * Efun t x)
        - (f₁ b * Efun t b - f₁ a * Efun t a) := by
    rw [e2]; ring
  calc ((t : ℂ) * Complex.I * ((t : ℂ) * Complex.I)) * ∫ x in a..b, f x * Efun t x
      = (t : ℂ) * Complex.I
        * ((∫ x in a..b, f₁ x * Efun t x) - (f b * Efun t b - f a * Efun t a)) := by
          rw [mul_assoc, h1]
    _ = _ := by rw [mul_sub, h2]; ring

/-! ### Pointwise kernel bounds. -/

private lemma hc0nn : (0 : ℝ) ≤ (2 * Real.pi)⁻¹ :=
  inv_nonneg.mpr (by linarith [Real.pi_pos])

/-- Uniform bound `‖κ(t)‖ ≤ A/(2π)`. -/
lemma kap_bound_A (hτ : 1 ≤ τ) (hB0 : 0 < B) (hε0 : 0 < ε) (hD₁ : 0 ≤ D₁) (hΨ : ContDiff ℝ 2 Ψ) (hΨ0 : ∀ μ : ℝ, |μ| ≤ τ → ‖Ψ μ‖ ≤ ε) (hΨ1 : ∀ μ : ℝ, |μ| ≤ τ → ‖deriv Ψ μ‖ ≤ D₁) (hχ : ContDiff ℝ 2 χ) (hχ1 : ∀ μ : ℝ, |μ| ≤ τ → χ μ = 1) (hχb : ∀ μ : ℝ, |χ μ| ≤ 1) (t : ℝ) : ‖(kap τ B Ψ χ) t‖ ≤ (RealizeA τ B ε D₁) / (2 * Real.pi) := by
  have hG : ‖(∫ μ in (-(τ + B))..(-τ), (HatL τ B Ψ χ) μ * Efun t μ)
        + ((∫ μ in (-τ)..τ, (HatM Ψ χ) μ * Efun t μ)
        + (∫ μ in τ..(τ + B), (HatR τ B Ψ χ) μ * Efun t μ))‖ ≤ (RealizeA τ B ε D₁) := by
    refine ((norm_add_le _ _).trans
      (add_le_add le_rfl (norm_add_le _ _))).trans ?_
    refine (add_le_add ((int_HatL_le hτ hB0 hε0 hD₁ hΨ hΨ0 hΨ1 hχ hχb) t)
      (add_le_add ((int_HatM_le hτ hΨ hΨ0 hχ hχ1) t) ((int_HatR_le hτ hB0 hε0 hD₁ hΨ hΨ0 hΨ1 hχ hχb) t))).trans ?_
    have hnn : 0 ≤ 4 / 27 * B * D₁ :=
      mul_nonneg (mul_nonneg (by norm_num) hB0.le) hD₁
    have hS : ε ≤ ε + 4 / 27 * B * D₁ := by linarith
    have hSnn : 0 ≤ ε + 4 / 27 * B * D₁ := by linarith [hε0.le]
    have hBB : B * (ε + 4 / 27 * B * D₁) ≤ (τ + B) * (ε + 4 / 27 * B * D₁) :=
      mul_le_mul_of_nonneg_right (by linarith [hτ]) hSnn
    have h2 : 2 * τ * ε ≤ 2 * τ * (ε + 4 / 27 * B * D₁) :=
      mul_le_mul_of_nonneg_left hS (by linarith [hτ])
    simp only [RealizeA]
    linarith [hBB, h2]
  calc ‖(kap τ B Ψ χ) t‖
        = ((2 * Real.pi)⁻¹) * ‖(∫ μ in (-(τ + B))..(-τ), (HatL τ B Ψ χ) μ * Efun t μ)
          + ((∫ μ in (-τ)..τ, (HatM Ψ χ) μ * Efun t μ)
          + (∫ μ in τ..(τ + B), (HatR τ B Ψ χ) μ * Efun t μ))‖ := by
          simp only [(kap_eq_sum hτ hB0 hΨ hχ) t, norm_smul, Real.norm_of_nonneg hc0nn]
    _ ≤ ((2 * Real.pi)⁻¹) * (RealizeA τ B ε D₁) :=
        mul_le_mul_of_nonneg_left hG hc0nn
    _ = (RealizeA τ B ε D₁) / (2 * Real.pi) := by rw [div_eq_mul_inv, mul_comm]

/-- Quadratic-decay bound `‖κ(t)‖ ≤ C/(2πt²)` for `t ≠ 0`. -/
lemma kap_bound_C (hτ : 1 ≤ τ) (hB0 : 0 < B) (hε0 : 0 < ε) (hK : 1 ≤ K) (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂) (hΨ : ContDiff ℝ 2 Ψ) (hΨ0 : ∀ μ : ℝ, |μ| ≤ τ → ‖Ψ μ‖ ≤ ε) (hΨ1 : ∀ μ : ℝ, |μ| ≤ τ → ‖deriv Ψ μ‖ ≤ D₁) (hΨ2 : ∀ μ : ℝ, |μ| ≤ τ → ‖deriv (deriv Ψ) μ‖ ≤ D₂) (hχ : ContDiff ℝ 2 χ) (hχ1 : ∀ μ : ℝ, |μ| ≤ τ → χ μ = 1) (hχb : ∀ μ : ℝ, |χ μ| ≤ 1) (hχd1 : ∀ μ : ℝ, ‖deriv χ μ‖ ≤ K / B) (hχd2 : ∀ μ : ℝ, ‖deriv (deriv χ) μ‖ ≤ K / B ^ 2) {t : ℝ} (ht : t ≠ 0) :
    ‖(kap τ B Ψ χ) t‖ ≤ (RealizeC τ B ε D₁ D₂ K) / (2 * Real.pi * t ^ 2) := by

  have htC : (t : ℂ) ≠ 0 :=
    fun h => ht (Complex.ofReal_injective (by simpa using h))
  have hw0 : ((t : ℂ) * Complex.I) ≠ 0 := mul_ne_zero htC Complex.I_ne_zero
  have hww : ((t : ℂ) * Complex.I) * ((t : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero htC Complex.I_ne_zero) (mul_ne_zero htC Complex.I_ne_zero)
  have hw_norm : ‖((t : ℂ) * Complex.I)‖ = |t| := by
    simp only [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
  have eL := piece_ibp (HatL τ B Ψ χ) (HatL1 τ B Ψ χ) (HatL2 τ B Ψ χ) (-(τ + B)) (-τ) t
    (fun x _ => (hasDerivAt_HatL hΨ hχ) x) (fun x _ => (hasDerivAt_HatL1 hB0 hΨ hχ) x)
    (cont_HatL hχ) (cont_HatL1 hB0 hχ) (cont_HatL2 hB0 hχ)
  have eM := piece_ibp (HatM Ψ χ) (HatM1 Ψ χ) (HatM2 Ψ χ) (-τ) τ t
    (fun x _ => (hasDerivAt_HatM hΨ hχ) x) (fun x _ => (hasDerivAt_HatM1 hΨ hχ) x)
    (cont_HatM hΨ hχ) (cont_HatM1 hΨ hχ) (cont_HatM2 hΨ hχ)
  have eR := piece_ibp (HatR τ B Ψ χ) (HatR1 τ B Ψ χ) (HatR2 τ B Ψ χ) τ (τ + B) t
    (fun x _ => (hasDerivAt_HatR hΨ hχ) x) (fun x _ => (hasDerivAt_HatR1 hB0 hΨ hχ) x)
    (cont_HatR hχ) (cont_HatR1 hB0 hχ) (cont_HatR2 hB0 hχ)

  -- boundary telescoping (values and first derivatives match; outer ends vanish)
  have tel0 : ((HatL τ B Ψ χ) (-τ) * Efun t (-τ) - (HatL τ B Ψ χ) (-(τ + B)) * Efun t (-(τ + B)))
      + ((HatM Ψ χ) τ * Efun t τ - (HatM Ψ χ) (-τ) * Efun t (-τ))
      + ((HatR τ B Ψ χ) (τ + B) * Efun t (τ + B) - (HatR τ B Ψ χ) τ * Efun t τ) = 0 := by
    rw [(HatL_eq_HatM hB0), (HatR_eq_HatM hB0), ((HatL_outer hB0)).1, ((HatR_outer hB0)).1]
    ring
  have tel1 : ((HatL1 τ B Ψ χ) (-τ) * Efun t (-τ) - (HatL1 τ B Ψ χ) (-(τ + B)) * Efun t (-(τ + B)))
      + ((HatM1 Ψ χ) τ * Efun t τ - (HatM1 Ψ χ) (-τ) * Efun t (-τ))
      + ((HatR1 τ B Ψ χ) (τ + B) * Efun t (τ + B) - (HatR1 τ B Ψ χ) τ * Efun t τ) = 0 := by
    rw [(HatL1_eq_HatM1 hB0), (HatR1_eq_HatM1 hB0), ((HatL_outer hB0)).2, ((HatR_outer hB0)).2]
    ring
  have hsum : (((t : ℂ) * Complex.I) * ((t : ℂ) * Complex.I))
        * ((∫ μ in (-(τ + B))..(-τ), (HatL τ B Ψ χ) μ * Efun t μ)
          + ((∫ μ in (-τ)..τ, (HatM Ψ χ) μ * Efun t μ)
          + (∫ μ in τ..(τ + B), (HatR τ B Ψ χ) μ * Efun t μ)))
      = (∫ μ in (-(τ + B))..(-τ), (HatL2 τ B Ψ χ) μ * Efun t μ)
        + ((∫ μ in (-τ)..τ, (HatM2 Ψ χ) μ * Efun t μ)
        + (∫ μ in τ..(τ + B), (HatR2 τ B Ψ χ) μ * Efun t μ)) := by
    linear_combination eL + eM + eR - tel1 - ((t : ℂ) * Complex.I) * tel0
  have hG2 : ‖(∫ μ in (-(τ + B))..(-τ), (HatL2 τ B Ψ χ) μ * Efun t μ)
        + ((∫ μ in (-τ)..τ, (HatM2 Ψ χ) μ * Efun t μ)
        + (∫ μ in τ..(τ + B), (HatR2 τ B Ψ χ) μ * Efun t μ))‖ ≤ (RealizeC τ B ε D₁ D₂ K) := by
    refine ((norm_add_le _ _).trans
      (add_le_add le_rfl (norm_add_le _ _))).trans ?_
    refine (add_le_add ((int_HatL2_le hτ hB0 hε0 hD₁ hΨ hΨ0 hΨ1 hχ hχb hχd1 hχd2) t)
      (add_le_add ((int_HatM2_le hτ hΨ hΨ2 hχ hχ1) t) ((int_HatR2_le hτ hB0 hε0 hD₁ hΨ hΨ0 hΨ1 hχ hχb hχd1 hχd2) t))).trans ?_
    have hBne : B ≠ 0 := ne_of_gt hB0
    have hBB : B * ((6 + 4 * K) * ε / B ^ 2 + (4 + 2 * K + 4 * K / 27) * D₁ / B)
        = (6 + 4 * K) * ε / B + (4 + 2 * K + 4 * K / 27) * D₁ := by
      have hBne : B ≠ 0 := ne_of_gt hB0
      field_simp
    rw [hBB]
    simp only [RealizeC]
    exact le_of_eq (by ring)
  have hGeq : ((∫ μ in (-(τ + B))..(-τ), (HatL τ B Ψ χ) μ * Efun t μ)
        + ((∫ μ in (-τ)..τ, (HatM Ψ χ) μ * Efun t μ)
        + (∫ μ in τ..(τ + B), (HatR τ B Ψ χ) μ * Efun t μ)))
      = (((t : ℂ) * Complex.I) * ((t : ℂ) * Complex.I))⁻¹ * ((∫ μ in (-(τ + B))..(-τ), (HatL2 τ B Ψ χ) μ * Efun t μ)
        + ((∫ μ in (-τ)..τ, (HatM2 Ψ χ) μ * Efun t μ)
        + (∫ μ in τ..(τ + B), (HatR2 τ B Ψ χ) μ * Efun t μ))) := by
    rw [← hsum, inv_mul_cancel_left₀ hww]
  have hww_inv : ‖(((t : ℂ) * Complex.I) * ((t : ℂ) * Complex.I))⁻¹‖ = (t ^ 2)⁻¹ := by
    rw [norm_inv, norm_mul, hw_norm, ← pow_two, sq_abs]
  calc ‖(kap τ B Ψ χ) t‖
        = ((2 * Real.pi)⁻¹) * ‖(∫ μ in (-(τ + B))..(-τ), (HatL τ B Ψ χ) μ * Efun t μ)
          + ((∫ μ in (-τ)..τ, (HatM Ψ χ) μ * Efun t μ)
          + (∫ μ in τ..(τ + B), (HatR τ B Ψ χ) μ * Efun t μ))‖ := by
          simp only [(kap_eq_sum hτ hB0 hΨ hχ) t, norm_smul, Real.norm_of_nonneg hc0nn]
    _ ≤ ((2 * Real.pi)⁻¹) * ((t ^ 2)⁻¹ * (RealizeC τ B ε D₁ D₂ K)) := by
          refine mul_le_mul_of_nonneg_left ?_ hc0nn
          rw [hGeq, norm_mul, hww_inv]
          exact mul_le_mul_of_nonneg_left hG2 (by positivity)
    _ = (RealizeC τ B ε D₁ D₂ K) / (2 * Real.pi * t ^ 2) := by
          rw [div_eq_mul_inv, mul_inv]; ring

/-! ## 8. Integrability and the optimized L¹ bound. -/

/-- `t ↦ (t²)⁻¹` is integrable on `(R, ∞)`. -/
lemma integrableOn_inv_sq_Ioi {R : ℝ} (hR : 0 < R) :
    IntegrableOn (fun t : ℝ => (t ^ 2)⁻¹) (Set.Ioi R) := by
  refine (integrableOn_Ioi_rpow_of_lt (a := -2) (by norm_num) hR).congr_fun ?_
    measurableSet_Ioi
  intro t ht
  show t ^ (-2 : ℝ) = (t ^ 2)⁻¹
  rw [Real.rpow_neg (le_of_lt (hR.trans (Set.mem_Ioi.mp ht))), Real.rpow_two]

/-- `∫_{R}^{∞} t⁻² dt = 1/R`. -/
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

/-- `t ↦ (t²)⁻¹` is integrable on `(−∞, −R]`. -/
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

/-- `∫_{−∞}^{−R} t⁻² dt = 1/R`. -/
lemma integral_inv_sq_Iic {R : ℝ} (hR : 0 < R) :
    ∫ t in Set.Iic (-R), (t ^ 2)⁻¹ = R⁻¹ := by
  have hswap : ∫ t in Set.Iic (-R), (t ^ 2)⁻¹ = ∫ t in Set.Ioi R, ((-t) ^ 2)⁻¹ :=
    (integral_comp_neg_Ioi R (fun t : ℝ => (t ^ 2)⁻¹)).symm
  have hcongr : ∫ t in Set.Ioi R, ((-t) ^ 2)⁻¹ = ∫ t in Set.Ioi R, (t ^ 2)⁻¹ := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    show ((-t) ^ 2)⁻¹ = (t ^ 2)⁻¹
    rw [show (-t) ^ 2 = t ^ 2 by ring]
  rw [hswap, hcongr, integral_inv_sq_Ioi hR]

/-- `κ` is continuous in `t` (parameter integral of a compactly supported
continuous integrand). -/
lemma kap_continuous (hτ : 1 ≤ τ) (hB0 : 0 < B) (hΨ : ContDiff ℝ 2 Ψ) (hχ : ContDiff ℝ 2 χ) : Continuous (kap τ B Ψ χ) := by
  have hL : Continuous fun t : ℝ => (∫ μ in (-(τ + B))..(-τ), (HatL τ B Ψ χ) μ * Efun t μ) := by
    refine intervalIntegral.continuous_of_dominated_interval (X := ℝ)
      (F := fun t μ => (HatL τ B Ψ χ) μ * Efun t μ) (bound := fun μ => ‖(HatL τ B Ψ χ) μ‖)
      (μ := volume) ?_ ?_ ?_ ?_
    · intro x
      exact ((cont_HatL hχ).mul (cont_Efun x)).aestronglyMeasurable
    · intro x
      refine Eventually.of_forall fun μ _ => norm_mul_Efun_le _ _ _ _ (le_refl _)
    · exact ((cont_HatL hχ).norm.intervalIntegrable _ _)
    · refine Eventually.of_forall fun μ _ => ?_
      exact continuous_const.mul (cont_Efun_t μ)
  have hM : Continuous fun t : ℝ => (∫ μ in (-τ)..τ, (HatM Ψ χ) μ * Efun t μ) := by
    refine intervalIntegral.continuous_of_dominated_interval (X := ℝ)
      (F := fun t μ => (HatM Ψ χ) μ * Efun t μ) (bound := fun μ => ‖(HatM Ψ χ) μ‖)
      (μ := volume) ?_ ?_ ?_ ?_
    · intro x
      exact ((cont_HatM hΨ hχ).mul (cont_Efun x)).aestronglyMeasurable
    · intro x
      refine Eventually.of_forall fun μ _ => norm_mul_Efun_le _ _ _ _ (le_refl _)
    · exact ((cont_HatM hΨ hχ).norm.intervalIntegrable _ _)
    · refine Eventually.of_forall fun μ _ => ?_
      exact continuous_const.mul (cont_Efun_t μ)
  have hR : Continuous fun t : ℝ => (∫ μ in τ..(τ + B), (HatR τ B Ψ χ) μ * Efun t μ) := by
    refine intervalIntegral.continuous_of_dominated_interval (X := ℝ)
      (F := fun t μ => (HatR τ B Ψ χ) μ * Efun t μ) (bound := fun μ => ‖(HatR τ B Ψ χ) μ‖)
      (μ := volume) ?_ ?_ ?_ ?_
    · intro x
      exact ((cont_HatR hχ).mul (cont_Efun x)).aestronglyMeasurable
    · intro x
      refine Eventually.of_forall fun μ _ => norm_mul_Efun_le _ _ _ _ (le_refl _)
    · exact ((cont_HatR hχ).norm.intervalIntegrable _ _)
    · refine Eventually.of_forall fun μ _ => ?_
      exact continuous_const.mul (cont_Efun_t μ)
  have hsum : Continuous fun t : ℝ => ((∫ μ in (-(τ + B))..(-τ), (HatL τ B Ψ χ) μ * Efun t μ)
      + ((∫ μ in (-τ)..τ, (HatM Ψ χ) μ * Efun t μ)
      + (∫ μ in τ..(τ + B), (HatR τ B Ψ χ) μ * Efun t μ))) :=
    hL.add (hM.add hR)
  have heq : (kap τ B Ψ χ) = fun t : ℝ => ((2 * Real.pi)⁻¹ : ℝ) •
      (((∫ μ in (-(τ + B))..(-τ), (HatL τ B Ψ χ) μ * Efun t μ)
      + ((∫ μ in (-τ)..τ, (HatM Ψ χ) μ * Efun t μ)
      + (∫ μ in τ..(τ + B), (HatR τ B Ψ χ) μ * Efun t μ)))) := by
    funext t
    rw [(kap_eq_sum hτ hB0 hΨ hχ) t]
  rw [heq]
  exact Continuous.const_smul hsum ((2 * Real.pi)⁻¹ : ℝ)

/-- `κ ∈ L¹`. -/
lemma kap_integrable (hτ : 1 ≤ τ) (hB0 : 0 < B) (hε0 : 0 < ε) (hK : 1 ≤ K) (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂) (hΨ : ContDiff ℝ 2 Ψ) (hΨ0 : ∀ μ : ℝ, |μ| ≤ τ → ‖Ψ μ‖ ≤ ε) (hΨ1 : ∀ μ : ℝ, |μ| ≤ τ → ‖deriv Ψ μ‖ ≤ D₁) (hΨ2 : ∀ μ : ℝ, |μ| ≤ τ → ‖deriv (deriv Ψ) μ‖ ≤ D₂) (hχ : ContDiff ℝ 2 χ) (hχ1 : ∀ μ : ℝ, |μ| ≤ τ → χ μ = 1) (hχb : ∀ μ : ℝ, |χ μ| ≤ 1) (hχd1 : ∀ μ : ℝ, ‖deriv χ μ‖ ≤ K / B) (hχd2 : ∀ μ : ℝ, ‖deriv (deriv χ) μ‖ ≤ K / B ^ 2) : Integrable (kap τ B Ψ χ) := by
  have hmeas : AEStronglyMeasurable (kap τ B Ψ χ) volume :=
    (kap_continuous hτ hB0 hΨ hχ).aestronglyMeasurable
  have hmeas' : ∀ s : Set ℝ,
      AEStronglyMeasurable (kap τ B Ψ χ) (volume.restrict s) :=
    fun s => hmeas.mono_measure (Measure.restrict_le_self)
  have hboundA : ∀ t : ℝ, ‖(kap τ B Ψ χ) t‖ ≤ (RealizeA τ B ε D₁) / (2 * Real.pi) :=
    fun t => (kap_bound_A hτ hB0 hε0 hD₁ hΨ hΨ0 hΨ1 hχ hχ1 hχb) t
  have hboundC : ∀ t : ℝ, t ≠ 0 → ‖(kap τ B Ψ χ) t‖ ≤ (RealizeC τ B ε D₁ D₂ K) / (2 * Real.pi * t ^ 2) :=
    fun t ht => (kap_bound_C hτ hB0 hε0 hK hD₁ hD₂ hΨ hΨ0 hΨ1 hΨ2 hχ hχ1 hχb hχd1 hχd2) ht
  have hmid : IntegrableOn (kap τ B Ψ χ) (Set.Ioc (-1) 1) volume :=
    IntegrableOn.of_bound (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top)
      (hmeas' _) ((RealizeA τ B ε D₁) / (2 * Real.pi)) (Eventually.of_forall hboundA)
  have hright : IntegrableOn (kap τ B Ψ χ) (Set.Ioi 1) volume := by
    refine Integrable.mono' (μ := volume.restrict (Set.Ioi 1))
      (f := fun t : ℝ => (kap τ B Ψ χ) t)
      (g := fun t : ℝ => (RealizeC τ B ε D₁ D₂ K) / (2 * Real.pi) * (t ^ 2)⁻¹)
      ((integrableOn_inv_sq_Ioi (R := 1) one_pos).const_mul ((RealizeC τ B ε D₁ D₂ K) / (2 * Real.pi)))
      (hmeas' _) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : t ≠ 0 := by
      rintro rfl
      linarith [Set.mem_Ioi.mp ht]
    rw [← div_eq_mul_inv, div_div]
    exact hboundC t ht0
  have hleft : IntegrableOn (kap τ B Ψ χ) (Set.Iic (-1)) volume := by
    refine Integrable.mono' (μ := volume.restrict (Set.Iic (-1)))
      (f := fun t : ℝ => (kap τ B Ψ χ) t)
      (g := fun t : ℝ => (RealizeC τ B ε D₁ D₂ K) / (2 * Real.pi) * (t ^ 2)⁻¹)
      ((integrableOn_inv_sq_Iic (R := 1) one_pos).const_mul ((RealizeC τ B ε D₁ D₂ K) / (2 * Real.pi)))
      (hmeas' _) ?_
    filter_upwards [ae_restrict_mem measurableSet_Iic] with t ht
    have ht0 : t ≠ 0 := by
      rintro rfl
      linarith [Set.mem_Iic.mp ht]
    rw [← div_eq_mul_inv, div_div]
    exact hboundC t ht0
  have huniv : (Set.Ioc (-1) 1 ∪ (Set.Iic (-1) ∪ Set.Ioi 1) : Set ℝ) = Set.univ := by
    rw [← Set.compl_Ioc (a := (-1)) (b := 1), Set.union_compl_self]
  rw [← integrableOn_univ, ← huniv]
  exact hmid.union (hleft.union hright)

/-- Positivity of the majorants. -/
lemma RealizeA_pos (hτ : 1 ≤ τ) (hB0 : 0 < B) (hε0 : 0 < ε) (hD₁ : 0 ≤ D₁) : 0 < (RealizeA τ B ε D₁) := by
  have hTB : (0 : ℝ) < τ + B := by linarith [hτ, hB0]
  have hnn : 0 ≤ 4 / 27 * B * D₁ :=
    mul_nonneg (mul_nonneg (by norm_num) hB0.le) hD₁
  have hS : (0 : ℝ) < ε + 4 / 27 * B * D₁ := by linarith [hε0]
  simp only [RealizeA]
  exact mul_pos (mul_pos (by norm_num) hTB) hS

lemma RealizeC_pos (hτ : 1 ≤ τ) (hB0 : 0 < B) (hε0 : 0 < ε) (hK : 1 ≤ K) (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂) : 0 < (RealizeC τ B ε D₁ D₂ K) := by
  have hK' : (0 : ℝ) < 6 + 4 * K := by linarith [hK]
  have h1 : (0 : ℝ) < (6 + 4 * K) * ε / B :=
    div_pos (mul_pos hK' hε0) hB0
  have hY : 0 ≤ (4 + 2 * K + 4 * K / 27) * D₁ :=
    mul_nonneg (by linarith [hK]) hD₁
  have h2τ : 0 ≤ 2 * τ * D₂ :=
    mul_nonneg (mul_nonneg (by norm_num) (by linarith [hτ])) hD₂
  have hX : 0 < (6 + 4 * K) * ε / B + (4 + 2 * K + 4 * K / 27) * D₁ := by
    linarith [h1, hY]
  simp only [RealizeC]
  linarith [h2τ, hX]

/-- The optimized L¹ bound `‖κ‖₁ ≤ (2/π)√(AC)`. -/
theorem kap_L1_le (hτ : 1 ≤ τ) (hB0 : 0 < B) (hε0 : 0 < ε) (hK : 1 ≤ K) (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂) (hΨ : ContDiff ℝ 2 Ψ) (hΨ0 : ∀ μ : ℝ, |μ| ≤ τ → ‖Ψ μ‖ ≤ ε) (hΨ1 : ∀ μ : ℝ, |μ| ≤ τ → ‖deriv Ψ μ‖ ≤ D₁) (hΨ2 : ∀ μ : ℝ, |μ| ≤ τ → ‖deriv (deriv Ψ) μ‖ ≤ D₂) (hχ : ContDiff ℝ 2 χ) (hχ1 : ∀ μ : ℝ, |μ| ≤ τ → χ μ = 1) (hχb : ∀ μ : ℝ, |χ μ| ≤ 1) (hχd1 : ∀ μ : ℝ, ‖deriv χ μ‖ ≤ K / B) (hχd2 : ∀ μ : ℝ, ‖deriv (deriv χ) μ‖ ≤ K / B ^ 2) :
    ∫ t : ℝ, ‖(kap τ B Ψ χ) t‖ ≤ (2 / Real.pi) * Real.sqrt ((RealizeA τ B ε D₁) * (RealizeC τ B ε D₁ D₂ K)) := by
  set C₁ : ℝ := (RealizeA τ B ε D₁) / (2 * Real.pi) with hC1
  set C₂ : ℝ := (RealizeC τ B ε D₁ D₂ K) / (2 * Real.pi) with hC2
  have hC1pos : 0 < C₁ := div_pos (RealizeA_pos hτ hB0 hε0 hD₁) (by linarith [Real.pi_pos])
  have hC2pos : 0 < C₂ := div_pos (RealizeC_pos hτ hB0 hε0 hK hD₁ hD₂) (by linarith [Real.pi_pos])
  have hC1nn : 0 ≤ C₁ := hC1pos.le
  have hC2nn : 0 ≤ C₂ := hC2pos.le
  have h1 : ∀ t : ℝ, ‖(kap τ B Ψ χ) t‖ ≤ C₁ := fun t => (kap_bound_A hτ hB0 hε0 hD₁ hΨ hΨ0 hΨ1 hχ hχ1 hχb) t
  have h2 : ∀ t : ℝ, t ≠ 0 → ‖(kap τ B Ψ χ) t‖ ≤ C₂ / t ^ 2 := by
    intro t ht
    have h := (kap_bound_C hτ hB0 hε0 hK hD₁ hD₂ hΨ hΨ0 hΨ1 hΨ2 hχ hχ1 hχb hχd1 hχd2) ht
    rw [hC2, div_div]
    exact h
  have hint : Integrable fun t : ℝ => ‖(kap τ B Ψ χ) t‖ := ((kap_integrable hτ hB0 hε0 hK hD₁ hD₂ hΨ hΨ0 hΨ1 hΨ2 hχ hχ1 hχb hχd1 hχd2)).norm
  have hq : (0 : ℝ) ≤ C₂ / C₁ := div_nonneg hC2nn hC1nn
  have hs : (0 : ℝ) ≤ C₁ * C₂ := mul_nonneg hC1nn hC2nn
  set R : ℝ := Real.sqrt (C₂ / C₁) with hR
  have hRpos : 0 < R := Real.sqrt_pos.mpr (div_pos hC2pos hC1pos)
  -- `R * C₁ = √(C₁ * C₂)`
  have g1 : R * C₁ = Real.sqrt (C₁ * C₂) := by
    rw [hR, eq_comm, Real.sqrt_eq_iff_eq_sq hs
      (mul_nonneg (Real.sqrt_nonneg _) hC1nn), mul_pow, Real.sq_sqrt hq]
    field_simp
  -- `C₂ / R = √(C₁ * C₂)`
  have g2 : C₂ / R = Real.sqrt (C₁ * C₂) := by
    rw [hR, eq_comm, Real.sqrt_eq_iff_eq_sq hs (by positivity), div_pow,
      Real.sq_sqrt hq]
    field_simp
  -- split bound at `R`
  have hsplit : ∫ t : ℝ, ‖(kap τ B Ψ χ) t‖ ≤ 2 * R * C₁ + 2 * C₂ / R := by
    have hmid : ∫ t in Set.Ioc (-R) R, ‖(kap τ B Ψ χ) t‖ ≤ 2 * R * C₁ := by
      have hmono : ∫ t in Set.Ioc (-R) R, ‖(kap τ B Ψ χ) t‖ ≤ ∫ t in Set.Ioc (-R) R, C₁ :=
        setIntegral_mono_on hint.integrableOn
          (integrableOn_const (C := C₁) (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top))
          measurableSet_Ioc (fun t _ => h1 t)
      calc ∫ t in Set.Ioc (-R) R, ‖(kap τ B Ψ χ) t‖ ≤ ∫ t in Set.Ioc (-R) R, C₁ := hmono
        _ = volume.real (Set.Ioc (-R) R) * C₁ := by rw [setIntegral_const, smul_eq_mul]
        _ = 2 * R * C₁ := by rw [Real.volume_real_Ioc_of_le (by linarith)]; ring
    have hright : ∫ t in Set.Ioi R, ‖(kap τ B Ψ χ) t‖ ≤ C₂ * R⁻¹ := by
      have hmono : ∫ t in Set.Ioi R, ‖(kap τ B Ψ χ) t‖ ≤ ∫ t in Set.Ioi R, C₂ * (t ^ 2)⁻¹ :=
        setIntegral_mono_on hint.integrableOn
          ((integrableOn_inv_sq_Ioi hRpos).const_mul C₂) measurableSet_Ioi
          (fun t ht => by
            have ht0 : t ≠ 0 := ne_of_gt (hRpos.trans (Set.mem_Ioi.mp ht))
            simpa only [div_eq_mul_inv] using h2 t ht0)
      calc ∫ t in Set.Ioi R, ‖(kap τ B Ψ χ) t‖ ≤ ∫ t in Set.Ioi R, C₂ * (t ^ 2)⁻¹ := hmono
        _ = C₂ * ∫ t in Set.Ioi R, (t ^ 2)⁻¹ := by rw [integral_const_mul]
        _ = C₂ * R⁻¹ := by rw [integral_inv_sq_Ioi hRpos]
    have hleft : ∫ t in Set.Iic (-R), ‖(kap τ B Ψ χ) t‖ ≤ C₂ * R⁻¹ := by
      have hmono : ∫ t in Set.Iic (-R), ‖(kap τ B Ψ χ) t‖ ≤ ∫ t in Set.Iic (-R), C₂ * (t ^ 2)⁻¹ :=
        setIntegral_mono_on hint.integrableOn
          ((integrableOn_inv_sq_Iic hRpos).const_mul C₂) measurableSet_Iic
          (fun t ht => by
            have ht0 : t ≠ 0 := ne_of_lt (by linarith [Set.mem_Iic.mp ht, hRpos])
            simpa only [div_eq_mul_inv] using h2 t ht0)
      calc ∫ t in Set.Iic (-R), ‖(kap τ B Ψ χ) t‖ ≤ ∫ t in Set.Iic (-R), C₂ * (t ^ 2)⁻¹ := hmono
        _ = C₂ * ∫ t in Set.Iic (-R), (t ^ 2)⁻¹ := by rw [integral_const_mul]
        _ = C₂ * R⁻¹ := by rw [integral_inv_sq_Iic hRpos]
    have hsplit0 : (∫ t : ℝ, ‖(kap τ B Ψ χ) t‖)
        = (∫ t in Set.Ioc (-R) R, ‖(kap τ B Ψ χ) t‖) + (∫ t in (Set.Ioc (-R) R)ᶜ, ‖(kap τ B Ψ χ) t‖) :=
      (integral_add_compl (s := Set.Ioc (-R) R) measurableSet_Ioc hint).symm
    have hcompl : (∫ t in (Set.Ioc (-R) R)ᶜ, ‖(kap τ B Ψ χ) t‖)
        = (∫ t in Set.Iic (-R), ‖(kap τ B Ψ χ) t‖) + (∫ t in Set.Ioi R, ‖(kap τ B Ψ χ) t‖) := by
      rw [Set.compl_Ioc]
      exact setIntegral_union (s := Set.Iic (-R)) (t := Set.Ioi R)
        (Set.Iic_disjoint_Ioi (by linarith)) measurableSet_Ioi
        hint.integrableOn hint.integrableOn
    calc (∫ t : ℝ, ‖(kap τ B Ψ χ) t‖)
        = (∫ t in Set.Ioc (-R) R, ‖(kap τ B Ψ χ) t‖) + (∫ t in (Set.Ioc (-R) R)ᶜ, ‖(kap τ B Ψ χ) t‖) := hsplit0
      _ = (∫ t in Set.Ioc (-R) R, ‖(kap τ B Ψ χ) t‖)
            + ((∫ t in Set.Iic (-R), ‖(kap τ B Ψ χ) t‖) + (∫ t in Set.Ioi R, ‖(kap τ B Ψ χ) t‖)) := by
          rw [hcompl]
      _ ≤ 2 * R * C₁ + (C₂ * R⁻¹ + C₂ * R⁻¹) :=
          add_le_add hmid (add_le_add hleft hright)
      _ = 2 * R * C₁ + 2 * C₂ / R := by rw [div_eq_mul_inv]; ring
  -- convert `4√(C₁C₂)` to `(2/π)√(AC)`
  have hCC : C₁ * C₂ = ((RealizeA τ B ε D₁) * (RealizeC τ B ε D₁ D₂ K)) / (2 * Real.pi) ^ 2 := by
    rw [hC1, hC2]; ring
  have hsqrt : Real.sqrt (C₁ * C₂)
      = Real.sqrt ((RealizeA τ B ε D₁) * (RealizeC τ B ε D₁ D₂ K)) / (2 * Real.pi) := by
    rw [hCC, Real.sqrt_div (mul_nonneg (RealizeA_pos hτ hB0 hε0 hD₁).le (RealizeC_pos hτ hB0 hε0 hK hD₁ hD₂).le),
      Real.sqrt_sq (by linarith [Real.pi_pos])]
  calc ∫ t : ℝ, ‖(kap τ B Ψ χ) t‖ ≤ 2 * R * C₁ + 2 * C₂ / R := hsplit
    _ = 2 * (R * C₁) + 2 * (C₂ / R) := by ring
    _ = 2 * Real.sqrt (C₁ * C₂) + 2 * Real.sqrt (C₁ * C₂) := by rw [g1, g2]
    _ = 4 * Real.sqrt (C₁ * C₂) := by ring
    _ = (2 / Real.pi) * Real.sqrt ((RealizeA τ B ε D₁) * (RealizeC τ B ε D₁ D₂ K)) := by rw [hsqrt]; ring

/-! ## 9. Main theorem (L3 realization lemma). -/

/-- **Realization lemma (L3).** With `κ̂ := Ψ_ext·χ` (`κ̂ = Ψ` on the band) and
`κ` its inverse Fourier transform: `κ ∈ L¹` and `‖κ‖₁ ≤ (2/π)√(AC)` with
`A := 2(τ+B)(ε + (4/27)·B·D₁)` and
`C := 2τ·D₂ + 2·((6+4K)·ε/B + (4+2K+4K/27)·D₁)`
(the collar contributes two identical terms, one per collar).
The hypotheses `ε ≤ 1` and `B ≤ τ` are recorded for fidelity with L3 but are
not needed for the estimate. -/
theorem realize_L1 (hτ : 1 ≤ τ) (hBτ : B ≤ τ) (hB0 : 0 < B)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hK : 1 ≤ K)
    (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂)
    (hΨ : ContDiff ℝ 2 Ψ)
    (hΨ0 : ∀ μ : ℝ, |μ| ≤ τ → ‖Ψ μ‖ ≤ ε)
    (hΨ1 : ∀ μ : ℝ, |μ| ≤ τ → ‖deriv Ψ μ‖ ≤ D₁)
    (hΨ2 : ∀ μ : ℝ, |μ| ≤ τ → ‖deriv (deriv Ψ) μ‖ ≤ D₂)
    (hχ : ContDiff ℝ 2 χ)
    (hχ1 : ∀ μ : ℝ, |μ| ≤ τ → χ μ = 1)
    (hχ0 : ∀ μ : ℝ, τ + B ≤ |μ| → χ μ = 0)
    (hχb : ∀ μ : ℝ, |χ μ| ≤ 1)
    (hχd1 : ∀ μ : ℝ, ‖deriv χ μ‖ ≤ K / B)
    (hχd2 : ∀ μ : ℝ, ‖deriv (deriv χ) μ‖ ≤ K / B ^ 2) :
    (∀ μ : ℝ, |μ| ≤ τ → (HatK τ B Ψ χ) μ = Ψ μ)
    ∧ Integrable (kap τ B Ψ χ)
    ∧ (∀ t : ℝ, ‖(kap τ B Ψ χ) t‖ ≤ (RealizeA τ B ε D₁) / (2 * Real.pi))
    ∧ (∀ t : ℝ, t ≠ 0 → ‖(kap τ B Ψ χ) t‖ ≤ (RealizeC τ B ε D₁ D₂ K) / (2 * Real.pi * t ^ 2))
    ∧ ∫ t : ℝ, ‖(kap τ B Ψ χ) t‖ ≤ (2 / Real.pi) * Real.sqrt ((RealizeA τ B ε D₁) * (RealizeC τ B ε D₁ D₂ K)) := by
  exact ⟨fun μ hm => (HatK_band hχ1) hm, (kap_integrable hτ hB0 hε0 hK hD₁ hD₂ hΨ hΨ0 hΨ1 hΨ2 hχ hχ1 hχb hχd1 hχd2), (kap_bound_A hτ hB0 hε0 hD₁ hΨ hΨ0 hΨ1 hχ hχ1 hχb),
    fun t ht => (kap_bound_C hτ hB0 hε0 hK hD₁ hD₂ hΨ hΨ0 hΨ1 hΨ2 hχ hχ1 hχb hχd1 hχd2) ht, (kap_L1_le hτ hB0 hε0 hK hD₁ hD₂ hΨ hΨ0 hΨ1 hΨ2 hχ hχ1 hχb hχd1 hχd2)⟩

end Hat

end Realize
end RobustZ





