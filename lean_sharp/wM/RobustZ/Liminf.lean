import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# `liminf` versus eventual lower bounds

The mathematically intended statement is: if `c - δ ≤ a N / N` eventually for every `δ > 0`,
then `c ≤ liminf (a N / N)`.

**Warning.** With the exact signature requested — `{a : ℕ → ℝ} {c : ℝ}` and no boundedness
hypothesis — this is *false* in Lean/Mathlib. Reason: `Filter.liminf u f` is definitionally
`sSup {b | ∀ᶠ n in f, b ≤ u n}` (`Filter.liminf_eq`), and for `ℝ` `sSup` is junk (`= 0`) on
sets that are not bounded above (`Real.sSup_def`). For a sequence unbounded above the set of
eventual lower bounds is all of `ℝ`, hence `liminf = 0`. See `not_liminf_ge_of_eventually`
below for a fully formal counterexample (`a N = N * N`, `c = 1`), and
`liminf_ge_of_eventually_false` for the refutation of the general statement.

The provable statements need the set of eventual lower bounds to be bounded above, i.e.

* `BddAbove {b | ∀ᶠ N, b ≤ a N / N}`, or equivalently
* `Filter.IsCoboundedUnder (fun x1 x2 => x2 ≤ x1) atTop u` (the `autoParam` side condition of
  `Filter.le_liminf_of_le`), or
* `Filter.IsBoundedUnder (· ≤ ·) atTop u` (eventual boundedness above, which implies the
  previous one through `Filter.IsBoundedUnder.isCoboundedUnder_flip`).

All three variants are proved below, plus a hypothesis-free dichotomy
(`liminf_ge_or_tendsto_atTop`) that is still usable when boundedness above is unavailable.
-/

set_option autoImplicit false

open Filter

namespace RobustZ

/-! ### A fully formal counterexample -/

/-- `sSup` of an unbounded-above set of reals is the junk value `0`, so the `liminf` of an
unbounded-above sequence of naturals is `0` (rather than `+∞`). -/
theorem liminf_natCast_atTop : Filter.liminf (fun N : ℕ => (N : ℝ)) Filter.atTop = 0 := by
  rw [Filter.liminf_eq]
  have h : {a : ℝ | ∀ᶠ (N : ℕ) in Filter.atTop, a ≤ (N : ℝ)} = Set.univ := by
    ext b
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact Filter.eventually_atTop.2 ⟨⌈b⌉₊, fun n hn => Nat.ceil_le.1 hn⟩
  rw [h, Real.sSup_def]
  simp

/-- The hypothesis of the intended lemma is satisfied by `a N = N * N`, `c = 1`. -/
theorem counterexample_hyp :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ (N : ℕ) in Filter.atTop, (1 : ℝ) - δ ≤ ((N : ℝ) * (N : ℝ)) / (N : ℝ) := by
  intro δ _hδ
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  have hNne : N ≠ 0 := Nat.one_le_iff_ne_zero.1 hN
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hNne
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hdiv : ((N : ℝ) * (N : ℝ)) / (N : ℝ) = (N : ℝ) := by
    field_simp
  rw [hdiv]
  linarith

/-- …but the conclusion fails for it, since `liminf (fun N => N) atTop = 0` in `ℝ`. -/
theorem not_liminf_ge_of_eventually :
    ¬ ((1 : ℝ) ≤
      Filter.liminf (fun N : ℕ => ((N : ℝ) * (N : ℝ)) / (N : ℝ)) Filter.atTop) := by
  have hcongr : ∀ᶠ (N : ℕ) in Filter.atTop,
      ((N : ℝ) * (N : ℝ)) / (N : ℝ) = (N : ℝ) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    have hNne : N ≠ 0 := Nat.one_le_iff_ne_zero.1 hN
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hNne
    field_simp
  rw [Filter.liminf_congr hcongr, liminf_natCast_atTop]
  norm_num

/-- Hence the originally requested statement (no boundedness hypothesis) is refutable. -/
theorem liminf_ge_of_eventually_false :
    ¬ (∀ (a : ℕ → ℝ) (c : ℝ),
        (∀ δ : ℝ, 0 < δ → ∀ᶠ N in Filter.atTop, c - δ ≤ a N / N) →
        c ≤ Filter.liminf (fun N : ℕ => a N / N) Filter.atTop) :=
  fun H => not_liminf_ge_of_eventually (H (fun N => (N : ℝ) * (N : ℝ)) 1 counterexample_hyp)

/-! ### The provable versions -/

/-- **Key lemma.** If the set of eventual lower bounds is bounded above (so that the `sSup`
defining `liminf` is not junk), then eventual lower bounds `c - δ` for all `δ > 0` upgrade to
`c ≤ liminf`. -/
theorem liminf_ge_of_eventually_of_bddAbove {a : ℕ → ℝ} {c : ℝ}
    (hBdd : BddAbove {b : ℝ | ∀ᶠ N in Filter.atTop, b ≤ a N / N})
    (h : ∀ δ : ℝ, 0 < δ → ∀ᶠ N in Filter.atTop, c - δ ≤ a N / N) :
    c ≤ Filter.liminf (fun N : ℕ => a N / N) Filter.atTop := by
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  rw [Filter.liminf_eq]
  have hmem : c - δ ∈ {b : ℝ | ∀ᶠ N in Filter.atTop, b ≤ a N / N} := h δ hδ
  have := le_csSup hBdd hmem
  linarith

/-- **Corrected main lemma.** The requested statement plus eventual boundedness above of
`a N / N`. Intended use: `h` is the paper's `∀ δ > 0, T_min(N,φ)/N ≥ c - δ` eventually, and
`hbdd` an eventual upper bound for `T_min(N,φ)/N`. -/
theorem liminf_ge_of_eventually {a : ℕ → ℝ} {c : ℝ}
    (hbdd : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop fun N => a N / N)
    (h : ∀ δ : ℝ, 0 < δ → ∀ᶠ N in Filter.atTop, c - δ ≤ a N / N) :
    c ≤ Filter.liminf (fun N : ℕ => a N / N) Filter.atTop := by
  refine liminf_ge_of_eventually_of_bddAbove ?_ h
  obtain ⟨B, hB⟩ := hbdd
  refine ⟨B, fun b hb => ?_⟩
  simp only [Set.mem_ofPred_eq] at hb
  obtain ⟨N, hN₁, hN₂⟩ := (hb.and hB).exists
  exact hN₁.trans hN₂

/-- **Weakest-hypothesis form.** Only the `autoParam` side condition of
`Filter.le_liminf_of_le` is assumed: `Filter.IsCoboundedUnder (fun x1 x2 => x2 ≤ x1) atTop u`,
i.e. `BddAbove {b | ∀ᶠ N, b ≤ u N}`. (This is *not* provable for a sequence such as `N ↦ N`,
which is why the unconditional statement fails.) -/
theorem liminf_ge_of_eventually' {a : ℕ → ℝ} {c : ℝ}
    (hcob : Filter.IsCoboundedUnder (fun x1 x2 : ℝ => x2 ≤ x1) Filter.atTop
      fun N => a N / N)
    (h : ∀ δ : ℝ, 0 < δ → ∀ᶠ N in Filter.atTop, c - δ ≤ a N / N) :
    c ≤ Filter.liminf (fun N : ℕ => a N / N) Filter.atTop := by
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  have hle : c - δ ≤ Filter.liminf (fun N : ℕ => a N / N) Filter.atTop :=
    Filter.le_liminf_of_le hcob (h δ hδ)
  linarith

/-- **Hypothesis-free fallback (sharp dichotomy).** Either the desired `liminf` bound holds, or
`a N / N → +∞` (in which case `liminf` in `ℝ` is the junk value `0` and the statement is simply
false). No boundedness hypothesis is needed: the second alternative is exactly what can go wrong.

So a proof of `4 ≤ liminf (Tmin N φ / N)` must either supply
`Filter.IsBoundedUnder (· ≤ ·) atTop (fun N => Tmin N φ / N)` — e.g. from an explicit admissible
family with `cost θ ≤ M * N`, using `Tmin N φ = sInf (costs N φ) ≤ cost θ` — or rule out the
divergence alternative `∀ M, ∀ᶠ N, M ≤ Tmin N φ / N`. -/
theorem liminf_ge_or_tendsto_atTop {a : ℕ → ℝ} {c : ℝ}
    (h : ∀ δ : ℝ, 0 < δ → ∀ᶠ N in Filter.atTop, c - δ ≤ a N / N) :
    c ≤ Filter.liminf (fun N : ℕ => a N / N) Filter.atTop ∨
      ∀ M : ℝ, ∀ᶠ N in Filter.atTop, M ≤ a N / N := by
  by_cases hBdd : BddAbove {b : ℝ | ∀ᶠ N in Filter.atTop, b ≤ a N / N}
  · exact Or.inl (liminf_ge_of_eventually_of_bddAbove hBdd h)
  · refine Or.inr fun M => ?_
    obtain ⟨b, hb, hMb⟩ := not_bddAbove_iff.1 hBdd M
    simp only [Set.mem_ofPred_eq] at hb
    exact hb.mono fun N hN => hMb.le.trans hN

end RobustZ
