/-
The integers certified in Lean at `φ = π` by the exact criterion (paper Table II):

  T ≥ 2, 2, 4, 8, 10, 14, 16, 18, 22, 24, 28   for   N = 2, …, 12.

Proof core: `RobustZ.cert_N2`–`cert_N4` — `lean_sharp/wC/RobustZ/RungFinal.lean`;
`RobustZ.cert_N5_tight`–`cert_N12_tight` — `lean_sharp/wC/RobustZ/RungTight.lean`.
-/
import RobustZ.RungFinal
import RobustZ.RungTight

noncomputable section

namespace RobustZ.MainIneq

theorem cert_N2 {L : ℕ} {α θ : Fin L → ℝ} (hAdm : Admissible 2 Real.pi L α θ) : 2 ≤ cost θ :=
  RobustZ.cert_N2 hAdm

theorem cert_N3 {L : ℕ} {α θ : Fin L → ℝ} (hAdm : Admissible 3 Real.pi L α θ) : 2 ≤ cost θ :=
  RobustZ.cert_N3 hAdm

theorem cert_N4 {L : ℕ} {α θ : Fin L → ℝ} (hAdm : Admissible 4 Real.pi L α θ) : 4 ≤ cost θ :=
  RobustZ.cert_N4 hAdm

theorem cert_N5 {L : ℕ} {α θ : Fin L → ℝ} (hAdm : Admissible 5 Real.pi L α θ) : 8 ≤ cost θ :=
  RobustZ.cert_N5_tight hAdm

theorem cert_N6 {L : ℕ} {α θ : Fin L → ℝ} (hAdm : Admissible 6 Real.pi L α θ) : 10 ≤ cost θ :=
  RobustZ.cert_N6_tight hAdm

theorem cert_N7 {L : ℕ} {α θ : Fin L → ℝ} (hAdm : Admissible 7 Real.pi L α θ) : 14 ≤ cost θ :=
  RobustZ.cert_N7_tight hAdm

theorem cert_N8 {L : ℕ} {α θ : Fin L → ℝ} (hAdm : Admissible 8 Real.pi L α θ) : 16 ≤ cost θ :=
  RobustZ.cert_N8_tight hAdm

theorem cert_N9 {L : ℕ} {α θ : Fin L → ℝ} (hAdm : Admissible 9 Real.pi L α θ) : 18 ≤ cost θ :=
  RobustZ.cert_N9_tight hAdm

theorem cert_N10 {L : ℕ} {α θ : Fin L → ℝ} (hAdm : Admissible 10 Real.pi L α θ) : 22 ≤ cost θ :=
  RobustZ.cert_N10_tight hAdm

theorem cert_N11 {L : ℕ} {α θ : Fin L → ℝ} (hAdm : Admissible 11 Real.pi L α θ) : 24 ≤ cost θ :=
  RobustZ.cert_N11_tight hAdm

theorem cert_N12 {L : ℕ} {α θ : Fin L → ℝ} (hAdm : Admissible 12 Real.pi L α θ) : 28 ≤ cost θ :=
  RobustZ.cert_N12_tight hAdm

#print axioms cert_N2
#print axioms cert_N3
#print axioms cert_N4
#print axioms cert_N5
#print axioms cert_N6
#print axioms cert_N7
#print axioms cert_N8
#print axioms cert_N9
#print axioms cert_N10
#print axioms cert_N11
#print axioms cert_N12

end RobustZ.MainIneq
