import AngularRetardedScattering

/-! Radiation zeros of the top daughter in the binomial polynomial
normalization. The quadratic uses retarded amplitudes, rather than local
particular fields. -/
namespace SchwarzschildMixtures.Strain

open Polynomial

noncomputable section

def angularResponse (E X O : ℂ) (even odd : ℂ[X]) : ℂ[X] :=
  C E * even^2 + C X * (even*odd) + C O * odd^2

/-- Convert the two closed retarded coefficients and the pure-odd integral
to the ordinary quadratic coefficients on the two incident parities. -/
theorem angular_retarded_response_coeff (n m : ℕ) (k q₁ q₂ q₃ : ℂ) (even odd : ℂ[X]) :
    let rho := alternativeRatio k n
    let d := (q₂-q₁)/(rho-1)
    let weights := angularSourceWeights n m k even odd
    weights.1*q₁+weights.2.1*q₂+weights.2.2*q₃ =
      (angularResponse (q₁-d+rho*q₃) (d-(1+rho)*q₃) q₃ even odd).coeff m := by
  dsimp only
  let rho := alternativeRatio k n
  let d := (q₂-q₁)/(rho-1)
  let delta := C ((rho-1)⁻¹)*even*(odd-even)
  change ((even^2).coeff m-delta.coeff m)*q₁+delta.coeff m*q₂+
      (angularObstruction rho even odd).coeff m*q₃ =
    (angularResponse (q₁-d+rho*q₃) (d-(1+rho)*q₃) q₃ even odd).coeff m
  have cross_term : C (q₂-q₁)*delta = C d*(even*(odd-even)) := by
    dsimp [delta,d]
    rw [div_eq_mul_inv, map_mul]
    ring
  have expansion : C q₁*even^2+C (q₂-q₁)*delta+C q₃*angularObstruction rho even odd =
      angularResponse (q₁-d+rho*q₃) (d-(1+rho)*q₃) q₃ even odd := by
    rw [cross_term]
    simp only [angularResponse, angularObstruction, map_add, map_sub, map_mul, map_one]
    ring
  calc
    _ = (C q₁*even^2+C (q₂-q₁)*delta+C q₃*angularObstruction rho even odd).coeff m := by
      simp only [coeff_add,coeff_C_mul]
      ring
    _ = _ := congrArg (fun p : ℂ[X] => p.coeff m) expansion

theorem angular_radiation_factor (E X O z₁ z₂ : ℂ) (even odd : ℂ[X])
    (hE : E = O*z₁*z₂) (hX : X = -O*(z₁+z₂)) :
    angularResponse E X O even odd = C O*(odd-C z₁*even)*(odd-C z₂*even) := by
  rw [hE,hX]
  simp only [angularResponse,map_add,map_mul,map_neg]
  ring

/-- Vanishing at every azimuthal daughter label selects a common ratio,
even when the incident profiles were initially independent. -/
theorem angular_radiation_zeros (E X O z₁ z₂ : ℂ) (even odd : ℂ[X])
    (hO : O ≠ 0) (hE : E = O*z₁*z₂) (hX : X = -O*(z₁+z₂)) :
    (∀ m : ℕ, (angularResponse E X O even odd).coeff m = 0) ↔
      odd = C z₁*even ∨ odd = C z₂*even := by
  have hCO : C O ≠ 0 := by simpa using hO
  have all_zero : (∀ m : ℕ, (angularResponse E X O even odd).coeff m = 0) ↔
      angularResponse E X O even odd = 0 := by
    constructor
    · intro h
      ext m
      simp [h m]
    · intro h m
      simp [h]
  rw [all_zero, angular_radiation_factor E X O z₁ z₂ even odd hE hX, mul_eq_zero, mul_eq_zero]
  simp [hCO, sub_eq_zero]

/-- Parity reverses only the mixed incident term in the other outgoing
spin component. If all three coefficients are nonzero, a nonzero incident
profile must radiate in at least one component of the top daughter. -/
theorem opposite_spin_no_joint_zero (E X O : ℂ) (even odd : ℂ[X])
    (hE : E ≠ 0) (hX : X ≠ 0) (hO : O ≠ 0)
    (minus : angularResponse E X O even odd = 0)
    (plus : angularResponse E (-X) O even odd = 0) : even = 0 ∧ odd = 0 := by
  have hCE : C E ≠ 0 := by simpa using hE
  have hCO : C O ≠ 0 := by simpa using hO
  have hCX : C (2*X) ≠ 0 := by simpa using mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) hX
  have cross : even*odd = 0 := by
    have difference : C (2*X)*(even*odd) = 0 := by
      calc
        _ = angularResponse E X O even odd-angularResponse E (-X) O even odd := by
          simp only [angularResponse,map_mul,map_neg]
          rw [show (2 : ℂ) = 1+1 by norm_num, map_add,map_one]
          ring
        _ = 0 := by rw [minus,plus,sub_zero]
    exact (mul_eq_zero.mp difference).resolve_left hCX
  rcases mul_eq_zero.mp cross with h | h
  · have power : odd^2 = 0 := (mul_eq_zero.mp (by simpa [angularResponse,h] using minus)).resolve_left hCO
    exact ⟨h, of_not_not (fun ne => pow_ne_zero 2 ne power)⟩
  · have power : even^2 = 0 := (mul_eq_zero.mp (by simpa [angularResponse,h] using minus)).resolve_left hCE
    exact ⟨of_not_not (fun ne => pow_ne_zero 2 ne power), h⟩

#print axioms angular_retarded_response_coeff
#print axioms angular_radiation_zeros
#print axioms opposite_spin_no_joint_zero

end
end SchwarzschildMixtures.Strain
