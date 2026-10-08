/-
Exact-criterion rung (document Theorem 5), coefficient `→ 4`:

  if   nrCcal_tight τ q · q² · nrE2star τ q  <  sin²(φ/4)   at a trial bandwidth
  `1 ≤ τ < q`, then `T > 2τ`,     q = 2N+2.

`nrCcal_tight` and `nrE2star` are the explicit closed-form quantities of the document (§VI).
Proof core: `RobustZ.new_rung_final_tight` — `lean_sharp/wC/RobustZ/RungTight.lean`;
the closed form below is `RobustZ.nr_closed_form` — `lean_sharp/wC/RobustZ/NewRung.lean`.
-/
import RobustZ.RungTight
import RobustZ.NewRung

noncomputable section

namespace RobustZ.MainIneq

/-- `nrCcal_tight τ q · q² · nrE2star τ q < sin²(φ/4)` ⟹ `T > 2τ`. -/
theorem exact_criterion {N : ℕ} {φ : ℝ} {L : ℕ} {α θ : Fin L → ℝ}
    (hN : 1 ≤ N) (hφ0 : 0 < φ) (hφπ : φ ≤ Real.pi) (hAdm : Admissible N φ L α θ)
    (τ : ℝ) (hτ1 : 1 ≤ τ) (hlt : τ < ((2 * N + 2 : ℕ) : ℝ))
    (hmain : nrCcal_tight τ (2 * N + 2) * (((2 * N + 2 : ℕ) : ℝ)) ^ 2
      * nrE2star τ (2 * N + 2) < Real.sin (φ / 4) ^ 2) :
    2 * τ < cost θ :=
  RobustZ.new_rung_final_tight hN hφ0 hφπ hAdm τ hτ1 hlt hmain

/-- `T ≥ 4(N+1)(1 - nrU q)` for `N ≥ 500 + ⌈exp((11 + |log s₀|)/1.2)⌉`, `q = 2N+2`,
`nrU q = 6 (log q / q)^{2/3}`, given truncation data `C` at the prescribed bandwidth. -/
theorem closed_form {N : ℕ} {φ : ℝ} {L : ℕ} {α θ : Fin L → ℝ} (C : nrCheb)
    (hφ0 : 0 < φ) (hφπ : φ ≤ Real.pi) (hAdm : Admissible N φ L α θ)
    (hqN : C.q = 2 * N + 2)
    (hCτ : C.τ = ((2 * N + 2 : ℕ) : ℝ) * (1 - nrU ((2 * N + 2 : ℕ) : ℝ)))
    (s0 : ℝ) (hs0 : 0 < s0) (hs0le : s0 ≤ Real.sin (φ / 4) ^ 2)
    (hN : 500 + ⌈Real.exp ((11 + |Real.log s0|) / 1.2)⌉₊ ≤ N) :
    4 * ((N : ℝ) + 1) * (1 - nrU ((2 * N + 2 : ℕ) : ℝ)) ≤ cost θ :=
  RobustZ.nr_closed_form C hφ0 hφπ hAdm hqN hCτ s0 hs0 hs0le hN

#print axioms exact_criterion
#print axioms closed_form

end RobustZ.MainIneq
