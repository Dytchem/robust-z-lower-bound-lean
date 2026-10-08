/-
Elementary bound (paper Theorem 3), coefficient `4/e`:

  T ≥ 2 (2 q! sin²(φ/4))^{1/q},   q = 2N+2,   0 < φ ≤ π.

Proof core: `RobustZ.elementary_bound` — `lean_sharp/wC/RobustZ/ElementaryBound.lean`.
-/
import RobustZ.ElementaryBound

noncomputable section

namespace RobustZ.MainIneq

/-- `T ≥ 2 (2 q! sin²(φ/4))^{1/q}` for every order-`N` admissible sequence, `q = 2N+2`. -/
theorem elementary {L : ℕ} {α θ : Fin L → ℝ} {N : ℕ} {φ : ℝ}
    (hφ0 : 0 < φ) (hφπ : φ ≤ Real.pi) (hAdm : Admissible N φ L α θ) :
    2 * (2 * (Nat.factorial (2 * N + 2) : ℝ) * Real.sin (φ / 4) ^ 2)
      ^ (1 / ((2 * N + 2 : ℕ) : ℝ)) ≤ cost θ :=
  RobustZ.elementary_bound hφ0 hφπ hAdm

/-- `T ≥ 2 (q!)^{1/q}` at `φ = π`. -/
theorem elementary_pi {L : ℕ} {α θ : Fin L → ℝ} {N : ℕ}
    (hAdm : Admissible N Real.pi L α θ) :
    2 * (Nat.factorial (2 * N + 2) : ℝ) ^ (1 / ((2 * N + 2 : ℕ) : ℝ)) ≤ cost θ :=
  RobustZ.elementary_bound_pi hAdm

#print axioms elementary
#print axioms elementary_pi

end RobustZ.MainIneq
