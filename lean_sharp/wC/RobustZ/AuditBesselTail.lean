import RobustZ.BesselTail

/-
Audit companion for `RobustZ.BesselTail` (`LEAN_READY.md` L1/L2):
re-emits `#print axioms` for every lemma/theorem of `BesselTail.lean`.
Expected: each depends only on `[propext, Classical.choice, Quot.sound]`
(no `sorry`/`admit`/`axiom` anywhere).
-/

#print axioms RobustZ.besselI0
#print axioms RobustZ.besselAlpha
#print axioms RobustZ.besselF
#print axioms RobustZ.majorB
#print axioms RobustZ.tailFactor
#print axioms RobustZ.cont_exp_cos
#print axioms RobustZ.integral_period_eq
#print axioms RobustZ.integral_sin_eq_cos
#print axioms RobustZ.integral_cos_double
#print axioms RobustZ.integral_sin_eq_I0
#print axioms RobustZ.one_sub_cos_ge
#print axioms RobustZ.besselI0_le
#print axioms RobustZ.sqrt_sq_sub_eq_mul_sinh
#print axioms RobustZ.fcoef_sharp
#print axioms RobustZ.bessel_L1
#print axioms RobustZ.majorB_eq
#print axioms RobustZ.sinh_add_eq
#print axioms RobustZ.cosh_add_eq
#print axioms RobustZ.sinh_le_mul_cosh
#print axioms RobustZ.cosh_sub_one_le_mul_sinh
#print axioms RobustZ.cosh_mul_sub_ge_sinh_sub
#print axioms RobustZ.besselF_gap
#print axioms RobustZ.majorB_geom
#print axioms RobustZ.tailFactor_le
#print axioms RobustZ.bessel_L2
