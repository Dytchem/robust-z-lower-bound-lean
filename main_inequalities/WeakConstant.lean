/-
Weak-constant `8/e` variant (paper Remark 9), coefficient `8/e ≈ 2.943`:

  T ≥ 4 (q! sin⁴(φ/4) / (10⁸ q⁴))^{1/q},   q = 2N+2,   0 < φ ≤ π.

Proof core: `RobustZ.eight_over_e_bound` — `lean_sharp/wM/RobustZ/EightOverE.lean`.
-/
import RobustZ.EightOverE

noncomputable section

namespace RobustZ.MainIneq

/-- `T ≥ 4 (q! sin⁴(φ/4) / (10⁸ q⁴))^{1/q}` for every order-`N` admissible sequence. -/
theorem weak_constant {L : ℕ} {α θ : Fin L → ℝ} {N : ℕ} {φ : ℝ}
    (hφ0 : 0 < φ) (hφπ : φ ≤ Real.pi) (hAdm : Admissible N φ L α θ) :
    4 * ((Nat.factorial (2 * N + 2) : ℝ) * Real.sin (φ / 4) ^ 4
          / (10 ^ 8 * ((2 * N + 2 : ℕ) : ℝ) ^ 4))
        ^ (1 / ((2 * N + 2 : ℕ) : ℝ)) ≤ cost θ :=
  RobustZ.eight_over_e_bound hφ0 hφπ hAdm

#print axioms weak_constant

end RobustZ.MainIneq
