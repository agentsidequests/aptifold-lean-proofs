import MixedConservationCalculus
import MixedConservationCoefficients

/-! The projected axial conservation balance for a common
Regge–Wheeler parent. The parent itself need not be rational. -/
namespace SchwarzschildEinstein.PureOdd.Mixed

open SchwarzschildLaurent

noncomputable section

local notation "ℂᵣ" => RatFunc ℂ
local notation "R" => (RatFunc.X : ℂᵣ)
local notation "Cᵣ" => (RatFunc.C : ℂ →+* ℂᵣ)

variable {K : Type} [Field K] [CharZero K] [Algebra ℚ K]

omit [Algebra ℚ K] in
private theorem tensor_normalization (ell C : K) (he : ell ≠ 0) (hd : 2*ell-1 ≠ 0) :
    ((2*ell-1)*(2*ell+2)/2)*(2*C/(2*ell*(2*ell-1))) = ((ell+1)/ell)*C := by
  field_simp [he, hd]

/-- Conservation for the mixed daughter with time dependence exp(-2kt).
The vector and angular source coefficients have the normalization of
the full-angle mixed tensor. -/
theorem mixed_conservation_on_rw_parent (embed : ℂᵣ →+* K) (d : Derivation ℚ K K)
    (compatible : ∀ u, d (embed u) = embed (rationalDerivative u))
    (n : ℕ) (hn : 2 ≤ n) (k : ℂ) (ki : k.re = 0) (J : K)
    (wave : let r := embed R
            let w := embed (Cᵣ k)
            let ell := embed (Cᵣ (n:ℂ))
            lapse r*d (lapse r*d J) = (w^2+parentPotential r ell)*J) :
    let r := embed R
    let w := embed (Cᵣ k)
    let ell := embed (Cᵣ (n:ℂ))
    let f := lapse r
    let L := 2*ell
    let Z := r^2*(f*d J)
    let T := radialJet d (f*d (r*J)/2)
    let P := radialJet d (-(w*r)*J/(2*f))
    let E := scalarPolarReconstruction d r w ell (referenceEven r w ell J Z)
    let v := vectorValue r w ell T P E
    let sAng := axialAngularCoefficient r w ell T P E
    d (r*r*f*v.radius) + (2*w*r*r/f)*v.time = ((L-1)*(L+2)/2)*sAng := by
  let r := embed R
  let w := embed (Cᵣ k)
  let ell := embed (Cᵣ (n:ℂ))
  have hr : r ≠ 0 := (map_ne_zero embed).2 RatFunc.X_ne_zero
  have dr : d r = 1 := by simp only [r, compatible, rationalDerivative_radius, map_one]
  have hh : r-2 ≠ 0 := by
    have constant : rationalDerivative (2 : ℂᵣ) = 0 := by
      simpa only [map_ofNat] using rationalDerivative_constant (2 : ℂ)
    have nonzero : R-2 ≠ 0 := by
      intro h
      have hd := congrArg rationalDerivative h
      simp only [rationalDerivative_sub, rationalDerivative_radius, constant, sub_zero,
        rationalDerivative_zero, one_ne_zero] at hd
    simpa only [r, map_sub, map_ofNat] using (map_ne_zero embed).2 nonzero
  have cast_ell : ell = (n : K) := by simp only [ell, map_natCast]
  have he : ell ≠ 0 := by
    rw [cast_ell]
    exact Nat.cast_ne_zero.mpr (by omega)
  have hd : 2*ell-1 ≠ 0 := by
    rw [cast_ell]
    apply sub_ne_zero.mpr
    have h : 2*n ≠ 1 := by omega
    exact_mod_cast h
  have balance := conservation_rows_on_parent d r w ell J hr hh dr wave
  have zero := conservation_rows_zero embed (d : K → K) compatible n hn k ki
  change conservationRows (fun q => (q : K)) d r w ell = (0,0,0) at zero
  dsimp only at balance ⊢
  rw [zero] at balance
  simp only [quadraticValue, zero_mul, zero_add] at balance
  rw [axialAngularCoefficient, tensor_normalization _ _ he hd]
  exact sub_eq_zero.mp balance.symm

#print axioms mixed_conservation_on_rw_parent

end
end SchwarzschildEinstein.PureOdd.Mixed
