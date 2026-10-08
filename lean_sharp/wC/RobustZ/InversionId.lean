import RobustZ.RealizeLemma
import Mathlib.Analysis.Fourier.Inversion

/-
# Inversion identity for the RealizeLemma kernel (gap discharge).

Using EXACTLY the `κ̂` (`HatK`) and `κ` (`kap`) constructed in
`RobustZ.RealizeLemma`, we prove the pointwise Fourier inversion identity on
the band:

  `∀ μ, |μ| ≤ τ → ∫ t, κ t * exp (i*μ*t) = Ψ μ`.

Route: Mathlib's Fourier inversion on `ℝ`
(`MeasureTheory.Integrable.fourierInv_fourier_eq`, via the `𝓕`/`𝓕⁻`
normalization with `2π` in the exponent) applied to the rescaled profile
`Φ(ν) := κ̂(2πν)`.  The bridge `𝓕 Φ = κ` is the change of variables
`μ = 2πν` (as in `RobustZ.Inversion.kernel_eq_fourier`); the hypotheses
(`Φ` continuous with compact support, hence integrable; `𝓕 Φ = κ`
integrable by `kap_integrable`) are discharged from the `RealizeLemma`
bundle.  No Schwartz-class hypotheses are needed.
-/

noncomputable section

namespace RobustZ
namespace Realize

open Filter MeasureTheory

open scoped Real FourierTransform RealInnerProductSpace

variable {τ B ε D₁ D₂ K : ℝ}
variable {Ψ : ℝ → ℂ} {χ : ℝ → ℝ}

/-! ## 1. Vanishing of `κ̂` outside the support. -/

/-- `Ψ_ext` vanishes outside `[−(τ+B), τ+B]`. -/
lemma PsiExt_eq_zero_outside (hB0 : 0 < B) (hτ : 1 ≤ τ) {μ : ℝ}
    (hout : μ ∉ Set.Icc (-(τ + B)) (τ + B)) : PsiExt τ B Ψ μ = 0 := by
  have hmem : μ < -(τ + B) ∨ τ + B < μ := by
    by_cases h : μ < -(τ + B)
    · exact Or.inl h
    · right
      push Not at h
      have hle : ¬ μ ≤ τ + B := by
        intro hle
        exact hout (Set.mem_Icc.mpr ⟨h, hle⟩)
      exact lt_of_not_ge hle
  have h1 : μ ∉ Set.Icc (-τ) τ := by
    intro hc
    obtain ⟨hlo, hhi⟩ := Set.mem_Icc.mp hc
    rcases hmem with h | h <;> linarith
  have h2 : μ ∉ Set.Ioc τ (τ + B) := by
    intro hc
    obtain ⟨hlt, hle⟩ := Set.mem_Ioc.mp hc
    rcases hmem with h | h <;> linarith
  have h3 : μ ∉ Set.Ico (-(τ + B)) (-τ) := by
    intro hc
    obtain ⟨hle, hlt⟩ := Set.mem_Ico.mp hc
    rcases hmem with h | h <;> linarith
  unfold PsiExt
  simp only [h1, h2, h3, ite_false]

/-- `κ̂` vanishes outside `[−(τ+B), τ+B]`. -/
lemma HatK_eq_zero_outside (hB0 : 0 < B) (hτ : 1 ≤ τ) {μ : ℝ}
    (hout : μ ∉ Set.Icc (-(τ + B)) (τ + B)) : HatK τ B Ψ χ μ = 0 := by
  simp only [HatK, PsiExt_eq_zero_outside hB0 hτ hout, zero_mul]

/-- Support of `κ̂`. -/
lemma support_HatK_subset (hB0 : 0 < B) (hτ : 1 ≤ τ) :
    Function.support (HatK τ B Ψ χ) ⊆ Set.Icc (-(τ + B)) (τ + B) := by
  intro μ hμ
  by_contra hout
  exact hμ (HatK_eq_zero_outside hB0 hτ hout)

/-- `κ̂` has compact support. -/
lemma hasCompactSupport_HatK (hB0 : 0 < B) (hτ : 1 ≤ τ) :
    HasCompactSupport (HatK τ B Ψ χ) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (support_HatK_subset hB0 hτ)

/-- `κ̂ = 0` on `Ici (τ+B)` (endpoint via the right-collar vanishing). -/
lemma HatK_eq_zero_on_Ici (hB0 : 0 < B) (hτ : 1 ≤ τ)
    {x : ℝ} (hx : x ∈ Set.Ici (τ + B)) : HatK τ B Ψ χ x = 0 := by
  have hle : τ + B ≤ x := hx
  rcases eq_or_lt_of_le hle with rfl | hlt
  · have hle : τ ≤ τ + B := by linarith [hB0.le]
    have hmem : τ + B ∈ Set.uIcc τ (τ + B) := by
      rw [Set.uIcc_of_le hle]
      exact Set.mem_Icc.mpr ⟨hle, le_rfl⟩
    have heq := HatK_eq_HatR_on (τ := τ) (B := B) (Ψ := Ψ) (χ := χ) hτ hB0 hmem
    have h0 := (HatR_outer (τ := τ) (B := B) (Ψ := Ψ) (χ := χ) hB0).1
    rw [heq, h0]
  · have hout : x ∉ Set.Icc (-(τ + B)) (τ + B) := by
      intro hc
      obtain ⟨-, hhi⟩ := Set.mem_Icc.mp hc
      linarith
    exact HatK_eq_zero_outside hB0 hτ hout

/-- `κ̂ = 0` on `Iic (−(τ+B))` (endpoint via the left-collar vanishing). -/
lemma HatK_eq_zero_on_Iic (hB0 : 0 < B) (hτ : 1 ≤ τ)
    {x : ℝ} (hx : x ∈ Set.Iic (-(τ + B))) : HatK τ B Ψ χ x = 0 := by
  have hle : x ≤ -(τ + B) := hx
  rcases eq_or_lt_of_le hle with rfl | hlt
  · have hle : -(τ + B) ≤ -τ := by linarith [hB0.le]
    have hmem : -(τ + B) ∈ Set.uIcc (-(τ + B)) (-τ) := by
      rw [Set.uIcc_of_le hle]
      exact Set.mem_Icc.mpr ⟨le_rfl, hle⟩
    have heq := HatK_eq_HatL_on (τ := τ) (B := B) (Ψ := Ψ) (χ := χ) hτ hB0 hmem
    have h0 := (HatL_outer (τ := τ) (B := B) (Ψ := Ψ) (χ := χ) hB0).1
    rw [heq, h0]
  · have hout : x ∉ Set.Icc (-(τ + B)) (τ + B) := by
      intro hc
      obtain ⟨hlo, -⟩ := Set.mem_Icc.mp hc
      linarith
    exact HatK_eq_zero_outside hB0 hτ hout

/-! ## 2. Continuity of `κ̂` (gluing the three smooth pieces). -/

private lemma uIcc_band (hτ : 1 ≤ τ) : Set.uIcc (-τ) τ = Set.Icc (-τ) τ := by
  rw [Set.uIcc_of_le (by linarith [hτ] : -τ ≤ τ)]

private lemma uIcc_collarR (hB0 : 0 < B) : Set.uIcc τ (τ + B) = Set.Icc τ (τ + B) := by
  rw [Set.uIcc_of_le (by linarith [hB0.le] : τ ≤ τ + B)]

private lemma uIcc_collarL (hB0 : 0 < B) :
    Set.uIcc (-(τ + B)) (-τ) = Set.Icc (-(τ + B)) (-τ) := by
  rw [Set.uIcc_of_le (by linarith [hB0.le] : -(τ + B) ≤ -τ)]

private lemma HatK_at_band_point (hτ : 1 ≤ τ) (hB0 : 0 < B)
    {x : ℝ} (hx : x ∈ Set.Icc (-τ) τ) : HatK τ B Ψ χ x = HatM Ψ χ x :=
  HatK_eq_HatM_on (τ := τ) (B := B) (Ψ := Ψ) (χ := χ) hτ
    (by rw [uIcc_band hτ]; exact hx)

private lemma HatK_at_collarR_point (hτ : 1 ≤ τ) (hB0 : 0 < B)
    {x : ℝ} (hx : x ∈ Set.Icc τ (τ + B)) : HatK τ B Ψ χ x = HatR τ B Ψ χ x :=
  HatK_eq_HatR_on (τ := τ) (B := B) (Ψ := Ψ) (χ := χ) hτ hB0
    (by rw [uIcc_collarR hB0]; exact hx)

private lemma HatK_at_collarL_point (hτ : 1 ≤ τ) (hB0 : 0 < B)
    {x : ℝ} (hx : x ∈ Set.Icc (-(τ + B)) (-τ)) :
    HatK τ B Ψ χ x = HatL τ B Ψ χ x :=
  HatK_eq_HatL_on (τ := τ) (B := B) (Ψ := Ψ) (χ := χ) hτ hB0
    (by rw [uIcc_collarL hB0]; exact hx)

/-- Continuity at band-interior points. -/
private lemma continuousAt_HatK_band (hτ : 1 ≤ τ) (hB0 : 0 < B)
    (hΨ : ContDiff ℝ 2 Ψ) (hχ : ContDiff ℝ 2 χ)
    {x : ℝ} (hx : x ∈ Set.Ioo (-τ) τ) : ContinuousAt (HatK τ B Ψ χ) x := by
  have hmem : Set.Ioo (-τ) τ ∈ nhds x := Ioo_mem_nhds hx.1 hx.2
  have heq : (HatM Ψ χ) =ᶠ[nhds x] (HatK τ B Ψ χ) := by
    filter_upwards [hmem] with y hy
    exact (HatK_at_band_point hτ hB0 (Set.Ioo_subset_Icc_self hy)).symm
  exact ((cont_HatM hΨ hχ).continuousAt).congr heq

/-- Continuity at right-collar-interior points. -/
private lemma continuousAt_HatK_collarR (hτ : 1 ≤ τ) (hB0 : 0 < B)
    (hχ : ContDiff ℝ 2 χ)
    {x : ℝ} (hx : x ∈ Set.Ioo τ (τ + B)) : ContinuousAt (HatK τ B Ψ χ) x := by
  have hmem : Set.Ioo τ (τ + B) ∈ nhds x := Ioo_mem_nhds hx.1 hx.2
  have heq : (HatR τ B Ψ χ) =ᶠ[nhds x] (HatK τ B Ψ χ) := by
    filter_upwards [hmem] with y hy
    exact (HatK_at_collarR_point hτ hB0 (Set.Ioo_subset_Icc_self hy)).symm
  exact ((cont_HatR hχ).continuousAt).congr heq

/-- Continuity at left-collar-interior points. -/
private lemma continuousAt_HatK_collarL (hτ : 1 ≤ τ) (hB0 : 0 < B)
    (hχ : ContDiff ℝ 2 χ)
    {x : ℝ} (hx : x ∈ Set.Ioo (-(τ + B)) (-τ)) :
    ContinuousAt (HatK τ B Ψ χ) x := by
  have hmem : Set.Ioo (-(τ + B)) (-τ) ∈ nhds x := Ioo_mem_nhds hx.1 hx.2
  have heq : (HatL τ B Ψ χ) =ᶠ[nhds x] (HatK τ B Ψ χ) := by
    filter_upwards [hmem] with y hy
    exact (HatK_at_collarL_point hτ hB0 (Set.Ioo_subset_Icc_self hy)).symm
  exact ((cont_HatL hχ).continuousAt).congr heq

/-- Continuity at exterior points. -/
private lemma continuousAt_HatK_outside (hτ : 1 ≤ τ) (hB0 : 0 < B)
    {x : ℝ} (hx : x ∉ Set.Icc (-(τ + B)) (τ + B)) :
    ContinuousAt (HatK τ B Ψ χ) x := by
  have hopen : (Set.Icc (-(τ + B)) (τ + B))ᶜ ∈ nhds x :=
    isClosed_Icc.compl_mem_nhds hx
  have heq : (fun _ : ℝ => (0 : ℂ)) =ᶠ[nhds x] (HatK τ B Ψ χ) := by
    filter_upwards [hopen] with y hy
    simp only [Set.mem_compl_iff] at hy
    exact (HatK_eq_zero_outside hB0 hτ hy).symm
  exact continuous_const.continuousAt.congr heq

/-- Continuity at the right band junction `τ` (two-sided gluing). -/
private lemma continuousAt_HatK_tau (hτ : 1 ≤ τ) (hB0 : 0 < B)
    (hΨ : ContDiff ℝ 2 Ψ) (hχ : ContDiff ℝ 2 χ) :
    ContinuousAt (HatK τ B Ψ χ) τ := by
  have hMτ : HatM Ψ χ τ = HatK τ B Ψ χ τ :=
    (HatK_at_band_point hτ hB0 (Set.mem_Icc.mpr ⟨by linarith [hτ], le_rfl⟩)).symm
  have hRτ : HatR τ B Ψ χ τ = HatK τ B Ψ χ τ :=
    (HatK_at_collarR_point hτ hB0 (Set.mem_Icc.mpr ⟨le_rfl, by linarith [hB0.le]⟩)).symm
  have hg : Tendsto (HatM Ψ χ) (nhds τ) (nhds (HatK τ B Ψ χ τ)) := by
    rw [← hMτ]; exact (cont_HatM hΨ hχ).continuousAt
  have hh : Tendsto (HatR τ B Ψ χ) (nhds τ) (nhds (HatK τ B Ψ χ τ)) := by
    rw [← hRτ]; exact (cont_HatR hχ).continuousAt
  set d := min B 1 with hd
  have hdpos : 0 < d := lt_min hB0 one_pos
  have hdB : d ≤ B := min_le_left _ _
  have hd1 : d ≤ 1 := min_le_right _ _
  have hU : Set.Ioo (τ - d) (τ + d) ∈ nhds τ :=
    Ioo_mem_nhds (by linarith) (by linarith)
  show Tendsto _ _ _
  intro s hs
  rw [Filter.mem_map]
  have h1 : ∀ᶠ y in nhds τ, HatM Ψ χ y ∈ s :=
    hg.eventually (eventually_of_mem hs fun _ h => h)
  have h2 : ∀ᶠ y in nhds τ, HatR τ B Ψ χ y ∈ s :=
    hh.eventually (eventually_of_mem hs fun _ h => h)
  filter_upwards [h1, h2, hU] with y hyM hyR hyU
  show HatK τ B Ψ χ y ∈ s
  rcases le_total y τ with hle | hle2
  · have hyM' : y ∈ Set.Icc (-τ) τ := by
      obtain ⟨hlo, -⟩ := Set.mem_Ioo.mp hyU
      constructor <;> linarith [hτ]
    have hKy : HatK τ B Ψ χ y = HatM Ψ χ y := HatK_at_band_point hτ hB0 hyM'
    rw [hKy]; exact hyM
  · have hyR' : y ∈ Set.Icc τ (τ + B) := by
      obtain ⟨-, hhi⟩ := Set.mem_Ioo.mp hyU
      constructor <;> linarith
    have hKy : HatK τ B Ψ χ y = HatR τ B Ψ χ y := HatK_at_collarR_point hτ hB0 hyR'
    rw [hKy]; exact hyR

/-- Continuity at the left band junction `−τ` (two-sided gluing). -/
private lemma continuousAt_HatK_neg_tau (hτ : 1 ≤ τ) (hB0 : 0 < B)
    (hΨ : ContDiff ℝ 2 Ψ) (hχ : ContDiff ℝ 2 χ) :
    ContinuousAt (HatK τ B Ψ χ) (-τ) := by
  have hMτ : HatM Ψ χ (-τ) = HatK τ B Ψ χ (-τ) :=
    (HatK_at_band_point hτ hB0 (Set.mem_Icc.mpr ⟨le_rfl, by linarith [hτ]⟩)).symm
  have hLτ : HatL τ B Ψ χ (-τ) = HatK τ B Ψ χ (-τ) :=
    (HatK_at_collarL_point hτ hB0 (Set.mem_Icc.mpr ⟨by linarith [hB0.le], le_rfl⟩)).symm
  have hg : Tendsto (HatM Ψ χ) (nhds (-τ)) (nhds (HatK τ B Ψ χ (-τ))) := by
    rw [← hMτ]; exact (cont_HatM hΨ hχ).continuousAt
  have hh : Tendsto (HatL τ B Ψ χ) (nhds (-τ)) (nhds (HatK τ B Ψ χ (-τ))) := by
    rw [← hLτ]; exact (cont_HatL hχ).continuousAt
  set d := min B 1 with hd
  have hdpos : 0 < d := lt_min hB0 one_pos
  have hdB : d ≤ B := min_le_left _ _
  have hd1 : d ≤ 1 := min_le_right _ _
  have hU : Set.Ioo (-τ - d) (-τ + d) ∈ nhds (-τ) :=
    Ioo_mem_nhds (by linarith) (by linarith)
  show Tendsto _ _ _
  intro s hs
  rw [Filter.mem_map]
  have h1 : ∀ᶠ y in nhds (-τ), HatM Ψ χ y ∈ s :=
    hg.eventually (eventually_of_mem hs fun _ h => h)
  have h2 : ∀ᶠ y in nhds (-τ), HatL τ B Ψ χ y ∈ s :=
    hh.eventually (eventually_of_mem hs fun _ h => h)
  filter_upwards [h1, h2, hU] with y hyM hyL hyU
  show HatK τ B Ψ χ y ∈ s
  rcases le_total (-τ) y with hle | hle2
  · have hyM' : y ∈ Set.Icc (-τ) τ := by
      obtain ⟨-, hhi⟩ := Set.mem_Ioo.mp hyU
      constructor <;> linarith [hτ]
    have hKy : HatK τ B Ψ χ y = HatM Ψ χ y := HatK_at_band_point hτ hB0 hyM'
    rw [hKy]; exact hyM
  · have hyL' : y ∈ Set.Icc (-(τ + B)) (-τ) := by
      obtain ⟨hlo, -⟩ := Set.mem_Ioo.mp hyU
      constructor <;> linarith
    have hKy : HatK τ B Ψ χ y = HatL τ B Ψ χ y := HatK_at_collarL_point hτ hB0 hyL'
    rw [hKy]; exact hyL

/-- Continuity at the outer right end `τ+B` (two-sided gluing with `0`). -/
private lemma continuousAt_HatK_outerR (hτ : 1 ≤ τ) (hB0 : 0 < B)
    (hχ : ContDiff ℝ 2 χ) :
    ContinuousAt (HatK τ B Ψ χ) (τ + B) := by
  have hR0 : HatR τ B Ψ χ (τ + B) = HatK τ B Ψ χ (τ + B) := by
    have hmem : τ + B ∈ Set.Icc τ (τ + B) :=
      Set.mem_Icc.mpr ⟨by linarith [hB0.le], le_rfl⟩
    exact (HatK_at_collarR_point hτ hB0 hmem).symm
  have hZ0 : (0 : ℂ) = HatK τ B Ψ χ (τ + B) := by
    have hmem : τ + B ∈ Set.Ici (τ + B) := Set.mem_Ici.mpr le_rfl
    exact (HatK_eq_zero_on_Ici hB0 hτ hmem).symm
  have hg : Tendsto (HatR τ B Ψ χ) (nhds (τ + B)) (nhds (HatK τ B Ψ χ (τ + B))) := by
    rw [← hR0]; exact (cont_HatR hχ).continuousAt
  have hh : Tendsto (fun _ : ℝ => (0 : ℂ)) (nhds (τ + B)) (nhds (HatK τ B Ψ χ (τ + B))) := by
    rw [← hZ0]; exact continuous_const.continuousAt
  set d := min B 1 with hd
  have hdpos : 0 < d := lt_min hB0 one_pos
  have hdB : d ≤ B := min_le_left _ _
  have hU : Set.Ioo (τ + B - d) (τ + B + d) ∈ nhds (τ + B) :=
    Ioo_mem_nhds (by linarith) (by linarith)
  show Tendsto _ _ _
  intro s hs
  rw [Filter.mem_map]
  have h1 : ∀ᶠ y in nhds (τ + B), HatR τ B Ψ χ y ∈ s :=
    hg.eventually (eventually_of_mem hs fun _ h => h)
  have h2 : ∀ᶠ _ in nhds (τ + B), (0 : ℂ) ∈ s :=
    hh.eventually (eventually_of_mem hs fun _ h => h)
  filter_upwards [h1, h2, hU] with y hyR hyZ hyU
  show HatK τ B Ψ χ y ∈ s
  rcases le_total y (τ + B) with hle | hle2
  · have hyR' : y ∈ Set.Icc τ (τ + B) := by
      obtain ⟨hlo, -⟩ := Set.mem_Ioo.mp hyU
      constructor <;> linarith
    have hKy : HatK τ B Ψ χ y = HatR τ B Ψ χ y := HatK_at_collarR_point hτ hB0 hyR'
    rw [hKy]; exact hyR
  · have hyI : y ∈ Set.Ici (τ + B) := Set.mem_Ici.mpr hle2
    have hKy : HatK τ B Ψ χ y = 0 := HatK_eq_zero_on_Ici hB0 hτ hyI
    rw [hKy]; exact hyZ

/-- Continuity at the outer left end `−(τ+B)` (two-sided gluing with `0`). -/
private lemma continuousAt_HatK_outerL (hτ : 1 ≤ τ) (hB0 : 0 < B)
    (hχ : ContDiff ℝ 2 χ) :
    ContinuousAt (HatK τ B Ψ χ) (-(τ + B)) := by
  have hL0 : HatL τ B Ψ χ (-(τ + B)) = HatK τ B Ψ χ (-(τ + B)) := by
    have hmem : -(τ + B) ∈ Set.Icc (-(τ + B)) (-τ) :=
      Set.mem_Icc.mpr ⟨le_rfl, by linarith [hB0.le]⟩
    exact (HatK_at_collarL_point hτ hB0 hmem).symm
  have hZ0 : (0 : ℂ) = HatK τ B Ψ χ (-(τ + B)) := by
    have hmem : -(τ + B) ∈ Set.Iic (-(τ + B)) := Set.mem_Iic.mpr le_rfl
    exact (HatK_eq_zero_on_Iic hB0 hτ hmem).symm
  have hg : Tendsto (HatL τ B Ψ χ) (nhds (-(τ + B))) (nhds (HatK τ B Ψ χ (-(τ + B)))) := by
    rw [← hL0]; exact (cont_HatL hχ).continuousAt
  have hh : Tendsto (fun _ : ℝ => (0 : ℂ)) (nhds (-(τ + B))) (nhds (HatK τ B Ψ χ (-(τ + B)))) := by
    rw [← hZ0]; exact continuous_const.continuousAt
  set d := min B 1 with hd
  have hdpos : 0 < d := lt_min hB0 one_pos
  have hdB : d ≤ B := min_le_left _ _
  have hU : Set.Ioo (-(τ + B) - d) (-(τ + B) + d) ∈ nhds (-(τ + B)) :=
    Ioo_mem_nhds (by linarith) (by linarith)
  show Tendsto _ _ _
  intro s hs
  rw [Filter.mem_map]
  have h1 : ∀ᶠ y in nhds (-(τ + B)), HatL τ B Ψ χ y ∈ s :=
    hg.eventually (eventually_of_mem hs fun _ h => h)
  have h2 : ∀ᶠ _ in nhds (-(τ + B)), (0 : ℂ) ∈ s :=
    hh.eventually (eventually_of_mem hs fun _ h => h)
  filter_upwards [h1, h2, hU] with y hyL hyZ hyU
  show HatK τ B Ψ χ y ∈ s
  rcases le_total (-(τ + B)) y with hle | hle2
  · have hyL' : y ∈ Set.Icc (-(τ + B)) (-τ) := by
      obtain ⟨-, hhi⟩ := Set.mem_Ioo.mp hyU
      constructor <;> linarith
    have hKy : HatK τ B Ψ χ y = HatL τ B Ψ χ y := HatK_at_collarL_point hτ hB0 hyL'
    rw [hKy]; exact hyL
  · have hyI : y ∈ Set.Iic (-(τ + B)) := hle2
    have hKy : HatK τ B Ψ χ y = 0 := HatK_eq_zero_on_Iic hB0 hτ hyI
    rw [hKy]; exact hyZ

/-- Global continuity of `κ̂`. -/
theorem continuous_HatK (hτ : 1 ≤ τ) (hB0 : 0 < B)
    (hΨ : ContDiff ℝ 2 Ψ) (hχ : ContDiff ℝ 2 χ) :
    Continuous (HatK τ B Ψ χ) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hxτ : x = τ
  · subst hxτ; exact continuousAt_HatK_tau hτ hB0 hΨ hχ
  by_cases hxnτ : x = -τ
  · subst hxnτ; exact continuousAt_HatK_neg_tau hτ hB0 hΨ hχ
  by_cases hxR : x = τ + B
  · subst hxR; exact continuousAt_HatK_outerR hτ hB0 hχ
  by_cases hxL : x = -(τ + B)
  · subst hxL; exact continuousAt_HatK_outerL hτ hB0 hχ
  by_cases hout : x ∉ Set.Icc (-(τ + B)) (τ + B)
  · exact continuousAt_HatK_outside hτ hB0 hout
  · push Not at hout
    have hxI : x ∈ Set.Icc (-(τ + B)) (τ + B) := hout
    obtain ⟨hlo, hhi⟩ := Set.mem_Icc.mp hxI
    rcases lt_trichotomy x (-τ) with h1 | h1 | h1
    · have hlo' : -(τ + B) < x := lt_of_le_of_ne hlo (Ne.symm hxL)
      have hx : x ∈ Set.Ioo (-(τ + B)) (-τ) :=
        Set.mem_Ioo.mpr ⟨hlo', h1⟩
      exact continuousAt_HatK_collarL hτ hB0 hχ hx
    · exact absurd h1 hxnτ
    · rcases lt_trichotomy x τ with h2 | h2 | h2
      · have hx : x ∈ Set.Ioo (-τ) τ := Set.mem_Ioo.mpr ⟨h1, h2⟩
        exact continuousAt_HatK_band hτ hB0 hΨ hχ hx
      · exact absurd h2 hxτ
      · rcases lt_trichotomy x (τ + B) with h3 | h3 | h3
        · have hx : x ∈ Set.Ioo τ (τ + B) := Set.mem_Ioo.mpr ⟨h2, h3⟩
          exact continuousAt_HatK_collarR hτ hB0 hχ hx
        · exact absurd h3 hxR
        · linarith

/-! ## 3. The rescaled profile `Φ(ν) := κ̂(2πν)`. -/

/-- `Φ` is continuous. -/
theorem continuous_Phi (hτ : 1 ≤ τ) (hB0 : 0 < B)
    (hΨ : ContDiff ℝ 2 Ψ) (hχ : ContDiff ℝ 2 χ) :
    Continuous (fun ν : ℝ => HatK τ B Ψ χ (2 * Real.pi * ν)) :=
  (continuous_HatK hτ hB0 hΨ hχ).comp (by fun_prop)

/-- `Φ` has compact support. -/
theorem hasCompactSupport_Phi (hτ : 1 ≤ τ) (hB0 : 0 < B) :
    HasCompactSupport (fun ν : ℝ => HatK τ B Ψ χ (2 * Real.pi * ν)) := by
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  intro ν hν
  rw [Function.mem_support] at hν
  have hpos : (0 : ℝ) < 2 * Real.pi := by positivity
  have hmem : (2 * Real.pi * ν) ∈ Set.Icc (-(τ + B)) (τ + B) := by
    by_contra hout
    exact hν (HatK_eq_zero_outside hB0 hτ hout)
  obtain ⟨hlo, hhi⟩ := Set.mem_Icc.mp hmem
  rw [Set.mem_Icc]
  constructor
  · exact (div_le_iff₀' hpos).mpr hlo
  · exact (le_div_iff₀' hpos).mpr hhi

/-- `Φ` is integrable. -/
theorem integrable_Phi (hτ : 1 ≤ τ) (hB0 : 0 < B)
    (hΨ : ContDiff ℝ 2 Ψ) (hχ : ContDiff ℝ 2 χ) :
    Integrable (fun ν : ℝ => HatK τ B Ψ χ (2 * Real.pi * ν)) :=
  (continuous_Phi hτ hB0 hΨ hχ).integrable_of_hasCompactSupport
    (hasCompactSupport_Phi hτ hB0)

/-! ## 4. Bridge: `κ = 𝓕 Φ` (change of variables `μ = 2πν`). -/

/-- Full-line integral of `κ̂·E` equals the defining interval integral. -/
theorem integral_full_eq_interval (hτ : 1 ≤ τ) (hB0 : 0 < B) (t : ℝ) :
    (∫ μ : ℝ, HatK τ B Ψ χ μ * Efun t μ)
      = ∫ μ in (-(τ + B))..(τ + B), HatK τ B Ψ χ μ * Efun t μ := by
  have hzero : ∀ μ ∉ Set.Icc (-(τ + B)) (τ + B),
      HatK τ B Ψ χ μ * Efun t μ = 0 := by
    intro μ hμ
    rw [HatK_eq_zero_outside hB0 hτ hμ, zero_mul]
  have hle : -(τ + B) ≤ τ + B := by
    have hpos : (0 : ℝ) < τ + B := by linarith [hτ, hB0]
    linarith
  calc (∫ μ : ℝ, HatK τ B Ψ χ μ * Efun t μ)
      = ∫ μ in Set.Icc (-(τ + B)) (τ + B), HatK τ B Ψ χ μ * Efun t μ :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
    _ = ∫ μ in Set.Ioc (-(τ + B)) (τ + B), HatK τ B Ψ χ μ * Efun t μ :=
        MeasureTheory.integral_Icc_eq_integral_Ioc
    _ = ∫ μ in (-(τ + B))..(τ + B), HatK τ B Ψ χ μ * Efun t μ :=
        (intervalIntegral.integral_of_le hle).symm

/-- `κ` is the Mathlib Fourier transform of the rescaled profile. -/
theorem kap_eq_fourier (hτ : 1 ≤ τ) (hB0 : 0 < B) :
    (fun t : ℝ => kap τ B Ψ χ t)
      = 𝓕 (fun ν : ℝ => HatK τ B Ψ χ (2 * Real.pi * ν)) := by
  funext t
  have h2pi : (2 * Real.pi) ≠ 0 := by positivity
  have hg : ∀ x : ℝ,
      (fun ν : ℝ => Complex.exp (↑(-2 * Real.pi * ν * t) * Complex.I)
        • HatK τ B Ψ χ (2 * Real.pi * ν)) ((2 * Real.pi)⁻¹ * x)
      = HatK τ B Ψ χ x * Efun t x := by
    intro x
    have h2 : 2 * Real.pi * ((2 * Real.pi)⁻¹ * x) = x := by
      rw [← mul_assoc, mul_inv_cancel₀ h2pi, one_mul]
    have hexp : -2 * Real.pi * ((2 * Real.pi)⁻¹ * x) * t = -(x * t) := by
      have hrr : -2 * Real.pi * ((2 * Real.pi)⁻¹ * x) * t
          = -((2 * Real.pi * ((2 * Real.pi)⁻¹ * x)) * t) := by ring
      rw [hrr, h2]
    have harg : ((↑(-(x * t)) : ℂ)) * Complex.I
        = -((x : ℂ) * Complex.I * (t : ℂ)) := by
      push_cast
      ring
    simp only [smul_eq_mul, Efun]
    rw [hexp, h2, harg, mul_comm]
  have hleft : (∫ x : ℝ, (fun ν : ℝ => Complex.exp (↑(-2 * Real.pi * ν * t) * Complex.I)
        • HatK τ B Ψ χ (2 * Real.pi * ν)) ((2 * Real.pi)⁻¹ * x))
      = ∫ x : ℝ, HatK τ B Ψ χ x * Efun t x :=
    integral_congr_ae (Filter.Eventually.of_forall hg)
  have hscale : (∫ x : ℝ, (fun ν : ℝ => Complex.exp (↑(-2 * Real.pi * ν * t) * Complex.I)
        • HatK τ B Ψ χ (2 * Real.pi * ν)) ((2 * Real.pi)⁻¹ * x))
      = (2 * Real.pi) • ∫ y : ℝ, Complex.exp (↑(-2 * Real.pi * y * t) * Complex.I)
        • HatK τ B Ψ χ (2 * Real.pi * y) := by
    have h := MeasureTheory.Measure.integral_comp_mul_left
      (g := fun ν : ℝ => Complex.exp (↑(-2 * Real.pi * ν * t) * Complex.I)
        • HatK τ B Ψ χ (2 * Real.pi * ν)) ((2 * Real.pi)⁻¹)
    rwa [inv_inv, abs_of_pos (show (0 : ℝ) < 2 * Real.pi by positivity)] at h
  have hB' : (∫ y : ℝ, Complex.exp (↑(-2 * Real.pi * y * t) * Complex.I)
        • HatK τ B Ψ χ (2 * Real.pi * y))
      = ((2 * Real.pi)⁻¹ : ℝ) • ∫ x : ℝ,
          (fun ν : ℝ => Complex.exp (↑(-2 * Real.pi * ν * t) * Complex.I)
            • HatK τ B Ψ χ (2 * Real.pi * ν)) ((2 * Real.pi)⁻¹ * x) := by
    rw [hscale, smul_smul, inv_mul_cancel₀ h2pi, one_smul]
  rw [Real.fourier_real_eq_integral_exp_smul, hB', hleft,
    integral_full_eq_interval hτ hB0 t, kap]

/-! ## 5. Pointwise inversion on the band. -/

/-- **Inversion identity on the band.**
`∫ t, κ t * exp (i*μ*t) = Ψ μ` for `|μ| ≤ τ`, using exactly the
`κ̂ = HatK` and `κ = kap` of `RealizeLemma`. -/
theorem inversion_on_band (hτ : 1 ≤ τ) (hB0 : 0 < B)
    (hε0 : 0 < ε) (hK : 1 ≤ K) (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂)
    (hΨ : ContDiff ℝ 2 Ψ)
    (hΨ0 : ∀ μ : ℝ, |μ| ≤ τ → ‖Ψ μ‖ ≤ ε)
    (hΨ1 : ∀ μ : ℝ, |μ| ≤ τ → ‖deriv Ψ μ‖ ≤ D₁)
    (hΨ2 : ∀ μ : ℝ, |μ| ≤ τ → ‖deriv (deriv Ψ) μ‖ ≤ D₂)
    (hχ : ContDiff ℝ 2 χ)
    (hχ1 : ∀ μ : ℝ, |μ| ≤ τ → χ μ = 1)
    (hχb : ∀ μ : ℝ, |χ μ| ≤ 1)
    (hχd1 : ∀ μ : ℝ, ‖deriv χ μ‖ ≤ K / B)
    (hχd2 : ∀ μ : ℝ, ‖deriv (deriv χ) μ‖ ≤ K / B ^ 2) :
    ∀ μ : ℝ, |μ| ≤ τ →
      ∫ t : ℝ, kap τ B Ψ χ t
        * Complex.exp ((μ : ℂ) * Complex.I * (t : ℂ)) = Ψ μ := by
  intro μ hμ
  have h2pi : (2 * Real.pi) ≠ 0 := by positivity
  have h2lam : 2 * Real.pi * (μ / (2 * Real.pi)) = μ := by
    rw [mul_comm (2 * Real.pi) (μ / (2 * Real.pi))]
    exact div_mul_cancel₀ μ h2pi
  have hΦcont : Continuous (fun ν : ℝ => HatK τ B Ψ χ (2 * Real.pi * ν)) :=
    continuous_Phi hτ hB0 hΨ hχ
  have hΦint : Integrable (fun ν : ℝ => HatK τ B Ψ χ (2 * Real.pi * ν)) :=
    integrable_Phi hτ hB0 hΨ hχ
  have hbridge : (fun t : ℝ => kap τ B Ψ χ t)
      = 𝓕 (fun ν : ℝ => HatK τ B Ψ χ (2 * Real.pi * ν)) :=
    kap_eq_fourier hτ hB0
  have hFint : Integrable (𝓕 (fun ν : ℝ => HatK τ B Ψ χ (2 * Real.pi * ν))) := by
    rw [← hbridge]
    exact kap_integrable hτ hB0 hε0 hK hD₁ hD₂ hΨ hΨ0 hΨ1 hΨ2 hχ hχ1 hχb hχd1 hχd2
  have hInv : 𝓕⁻ (𝓕 (fun ν : ℝ => HatK τ B Ψ χ (2 * Real.pi * ν)))
      = (fun ν : ℝ => HatK τ B Ψ χ (2 * Real.pi * ν)) :=
    Continuous.fourierInv_fourier_eq hΦcont hΦint hFint
  have hpt := congrFun hInv (μ / (2 * Real.pi))
  have hgoal : (∫ t : ℝ, kap τ B Ψ χ t
        * Complex.exp ((μ : ℂ) * Complex.I * (t : ℂ)))
      = 𝓕⁻ (𝓕 (fun ν : ℝ => HatK τ B Ψ χ (2 * Real.pi * ν))) (μ / (2 * Real.pi)) := by
    rw [Real.fourierInv_eq']
    simp only [Real.inner_apply]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    have hF : 𝓕 (fun ν : ℝ => HatK τ B Ψ χ (2 * Real.pi * ν)) v
        = kap τ B Ψ χ v :=
      (congrFun hbridge v).symm
    have h2 : 2 * Real.pi * (v * (μ / (2 * Real.pi))) = v * μ := by
      calc 2 * Real.pi * (v * (μ / (2 * Real.pi)))
          = v * (2 * Real.pi * (μ / (2 * Real.pi))) := by ring
        _ = v * μ := by rw [h2lam]
    have harg : ((((2 * Real.pi * (v * (μ / (2 * Real.pi)))) : ℝ)) : ℂ)
          * Complex.I = (μ : ℂ) * Complex.I * (v : ℂ) := by
      have h3 : ((((2 * Real.pi * (v * (μ / (2 * Real.pi)))) : ℝ)) : ℂ)
          = ((v * μ : ℝ) : ℂ) := by
        rw [h2]
      rw [h3]
      push_cast
      ring
    dsimp only
    rw [hF, harg, smul_eq_mul, mul_comm]
  have hΦw : (fun ν : ℝ => HatK τ B Ψ χ (2 * Real.pi * ν)) (μ / (2 * Real.pi))
      = Ψ μ := by
    show HatK τ B Ψ χ (2 * Real.pi * (μ / (2 * Real.pi))) = Ψ μ
    rw [h2lam]
    exact HatK_band hχ1 hμ
  calc (∫ t : ℝ, kap τ B Ψ χ t
        * Complex.exp ((μ : ℂ) * Complex.I * (t : ℂ)))
      = 𝓕⁻ (𝓕 (fun ν : ℝ => HatK τ B Ψ χ (2 * Real.pi * ν))) (μ / (2 * Real.pi)) :=
        hgoal
    _ = (fun ν : ℝ => HatK τ B Ψ χ (2 * Real.pi * ν)) (μ / (2 * Real.pi)) := hpt
    _ = Ψ μ := hΦw

end Realize
end RobustZ
