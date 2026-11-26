import QuadraticScatteringSource
import QuadraticConservationEvaluation
import MixedConservation

/-! Conservation of the three metric-derived bare scattering sectors
on a common Regge–Wheeler parent. -/
namespace SchwarzschildEinstein.PureOdd.Master

open SchwarzschildLaurent
noncomputable section
variable {K : Type} [Field K] [CharZero K] [Algebra ℚ K]

local notation "C" => (fun q : Rat => (q : K))
local notation "ℂᵣ" => RatFunc ℂ
local notation "R" => (RatFunc.X : ℂᵣ)
local notation "Cᵣ" => (RatFunc.C : ℂ →+* ℂᵣ)

/-- The time, radius, polar angular and axial angular conditions hold
for each bare quadratic sector of the reconstructed parent. -/
theorem quadratic_scattering_sectors_conserved (embed : ℂᵣ →+* K) (D : Derivation ℚ K K)
    (compatible : ∀ u, D (embed u) = embed (rationalDerivative u))
    (n : ℕ) (hn : 2 ≤ n) (k : ℂ) (ki : k.re = 0) (J : K)
    (hh : embed R-2 ≠ 0)
    (wave : let r := embed R
            let w := embed (Cᵣ k)
            let ell := embed (Cᵣ (n:ℂ))
            lapse r*D (lapse r*D J) = (w^2+parentPotential r ell)*J) :
    let r := embed R
    let w := embed (Cᵣ k)
    let ell := embed (Cᵣ (n:ℂ))
    ConservedMode D r (2*w) (2*ell) (evenScatteringSource D r w ell J) ∧
      ConservedMode D r (2*w) (2*ell) (mixedScatteringSource D r w ell J) ∧
      ConservedMode D r (2*w) (2*ell) (oddScatteringSource D r w ell J) := by
  let r := embed R
  let w := embed (Cᵣ k)
  let ell := embed (Cᵣ (n:ℂ))
  let Z := r^2*(lapse r*D J)
  have hr : r ≠ 0 := (map_ne_zero embed).2 RatFunc.X_ne_zero
  have dr : D r = 1 := by simpa only [r, rationalDerivative_radius, map_one] using compatible R
  obtain ⟨hj,hz,_,_⟩ := rw_parent_jet_rules D r w ell J hr hh dr wave
  have ez := polar_conservation_coefficients_zero embed D compatible n hn k ki true
  have oz := polar_conservation_coefficients_zero embed D compatible n hn k ki false
  have even := polar_zero_balances D r w ell J Z hj hz (evenParentSourceRows C D r w ell) ez
  have odd := polar_zero_balances D r w ell J Z hj hz (oddParentSourceRows C D r w ell) oz
  dsimp only at even odd ⊢
  have mixed := Mixed.mixed_conservation_on_rw_parent embed D compatible n hn k ki J wave
  refine ⟨⟨even.1, even.2.1, even.2.2, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨odd.1, odd.2.1, odd.2.2, ?_⟩⟩
  · simp [axialBalance, vectorDivergence, evenScatteringSource, evenParentSourceRows, mapModeSource, purePolarSource, quadraticValue]
  · simp [timeBalance, mixedScatteringSource, pureAxialSource]
  · simp [radiusBalance, mixedScatteringSource, pureAxialSource]
  · simp [polarBalance, vectorDivergence, mixedScatteringSource, pureAxialSource]
  · exact mixed_axial_balance D r w ell _ _ hr hh dr mixed
  · simp [axialBalance, vectorDivergence, oddScatteringSource, oddParentSourceRows, mapModeSource, purePolarSource, quadraticValue]

#print axioms quadratic_scattering_sectors_conserved

end
end SchwarzschildEinstein.PureOdd.Master
