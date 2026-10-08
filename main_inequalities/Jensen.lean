/-
Jensen bound (document Theorem 4), coefficient `2π/e`:

  T ≥ (π q / e) sin^{2/q}(φ/4),   q = 2N+2,   0 < φ ≤ π.

Proof core: `RobustZ.jensen_rung_final`, which states the same bound as
`π q / (e (2/s)^{1/q})` with `s = 2 sin²(φ/4)` — `lean_sharp/wF/RobustZ/JensenBridge.lean`.
-/
import RobustZ.JensenBridge

noncomputable section

namespace RobustZ.MainIneq

/-- `T ≥ (π q / e) sin^{2/q}(φ/4)` for every order-`N` admissible sequence, `q = 2N+2`. -/
theorem jensen {L : ℕ} {α θ : Fin L → ℝ} {N : ℕ} {φ : ℝ}
    (hφ0 : 0 < φ) (hφπ : φ ≤ Real.pi) (hAdm : Admissible N φ L α θ) :
    Real.pi * ((2 * N + 2 : ℕ) : ℝ) / Real.exp 1
      * Real.sin (φ / 4) ^ (2 / ((2 * N + 2 : ℕ) : ℝ)) ≤ cost θ := by
  have hsin : 0 < Real.sin (φ / 4) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [hφπ, Real.pi_pos])
  have hcore := RobustZ.jensen_rung_final N hφ0 hφπ hAdm
  have hbase : (2 : ℝ) / (2 * Real.sin (φ / 4) ^ 2) = (Real.sin (φ / 4) ^ 2)⁻¹ := by
    field_simp
  have hpow : ((Real.sin (φ / 4) ^ 2)⁻¹) ^ (1 / ((2 * N + 2 : ℕ) : ℝ))
      = (Real.sin (φ / 4) ^ (2 / ((2 * N + 2 : ℕ) : ℝ)))⁻¹ := by
    rw [Real.inv_rpow (sq_nonneg _)]
    congr 1
    rw [← Real.rpow_natCast (Real.sin (φ / 4)) 2, ← Real.rpow_mul (le_of_lt hsin)]
    congr 1
    push_cast
    ring
  rw [hbase, hpow] at hcore
  have hEq : Real.pi * ((2 * N + 2 : ℕ) : ℝ) / Real.exp 1
        * Real.sin (φ / 4) ^ (2 / ((2 * N + 2 : ℕ) : ℝ))
      = Real.pi * ((2 * N + 2 : ℕ) : ℝ)
        / (Real.exp 1 * (Real.sin (φ / 4) ^ (2 / ((2 * N + 2 : ℕ) : ℝ)))⁻¹) := by
    field_simp
  rw [hEq]
  exact hcore

/-- `T ≥ π q / (e 2^{1/q})` at `φ = π`, i.e. `(π q / e) sin^{2/q}(π/4)`. -/
theorem jensen_pi {L : ℕ} {α θ : Fin L → ℝ} {N : ℕ}
    (hAdm : Admissible N Real.pi L α θ) :
    Real.pi * ((2 * N + 2 : ℕ) : ℝ)
      / (Real.exp 1 * (2 : ℝ) ^ ((1 : ℝ) / ((2 * N + 2 : ℕ) : ℝ))) ≤ cost θ :=
  RobustZ.jensen_rung_pi_final N hAdm

#print axioms jensen
#print axioms jensen_pi

end RobustZ.MainIneq
