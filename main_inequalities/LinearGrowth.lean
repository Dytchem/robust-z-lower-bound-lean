/-
Linear growth with coefficient `4` (paper Corollary 6):

  4 ≤ liminf_{N} T_min(N,φ) / N .

Proof core: `RobustZ.c_ge_four`, `RobustZ.c_ge_four_or_grows` — `lean_sharp/wC/RobustZ/Theorem.lean`.
-/
import RobustZ.Theorem

noncomputable section

namespace RobustZ.MainIneq

/-- `4 ≤ liminf T_min(N,φ)/N`, given that an admissible sequence exists at every order
and that `T_min(N,φ)/N` is eventually bounded above. -/
theorem linear_growth (φ : ℝ) (hφ0 : 0 < φ) (hφπ : φ ≤ Real.pi)
    (hne : ∀ N, (costs N φ).Nonempty)
    (hbdd : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop (fun N : ℕ => Tmin N φ / N)) :
    4 ≤ Filter.liminf (fun N : ℕ => Tmin N φ / N) Filter.atTop :=
  RobustZ.c_ge_four φ hφ0 hφπ hne hbdd

/-- The same without the boundedness hypothesis: either the bound holds, or
`T_min(N,φ)/N` diverges to `+∞`. -/
theorem linear_growth_or_grows (φ : ℝ) (hφ0 : 0 < φ) (hφπ : φ ≤ Real.pi)
    (hne : ∀ N, (costs N φ).Nonempty) :
    4 ≤ Filter.liminf (fun N : ℕ => Tmin N φ / N) Filter.atTop ∨
      ∀ M : ℝ, ∀ᶠ N in Filter.atTop, M ≤ Tmin N φ / N :=
  RobustZ.c_ge_four_or_grows φ hφ0 hφπ hne

#print axioms linear_growth
#print axioms linear_growth_or_grows

end RobustZ.MainIneq
