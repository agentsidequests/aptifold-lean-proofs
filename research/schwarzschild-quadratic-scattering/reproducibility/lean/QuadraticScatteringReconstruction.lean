import QuadraticSourceConservation
import ParityReconstructionTheorem

/-! Apply the sourced Einstein converse with the actual bare quadratic
source and the manuscript's phase relating the two parent parities. -/
namespace SchwarzschildEinstein.PureOdd.Master

open SchwarzschildLaurent
noncomputable section
variable {K : Type} [Field K] [CharZero K] [Algebra ℚ K]

local notation "ℂᵣ" => RatFunc ℂ
local notation "R" => (RatFunc.X : ℂᵣ)
local notation "Cᵣ" => (RatFunc.C : ℂ →+* ℂᵣ)

private theorem combination_conserved (D : Derivation ℚ K K) (r w m a b : K)
    (E M O : ModeSource K) (da : D a = 0) (db : D b = 0)
    (ce : ConservedMode D r w m E) (cm : ConservedMode D r w m M)
    (co : ConservedMode D r w m O) :
    ConservedMode D r w m (quadraticModeCombination a b E M O) := by
  have dAA : D (a^2) = 0 := by simp [pow_two, D.leibniz, da]
  have dBB : D (b^2) = 0 := by simp [pow_two, D.leibniz, db]
  constructor
  · calc
      _ = a^2*timeBalance D r w m E+a*b*timeBalance D r w m M+b^2*timeBalance D r w m O := by
        simp only [timeBalance, quadraticModeCombination, map_add, D.leibniz, dAA, dBB, da, db,
          smul_eq_mul, mul_zero, zero_mul]
        ring
      _ = 0 := by simp [ce.time, cm.time, co.time]
  · calc
      _ = a^2*radiusBalance D r w m E+a*b*radiusBalance D r w m M+b^2*radiusBalance D r w m O := by
        simp only [radiusBalance, quadraticModeCombination, map_add, D.leibniz, dAA, dBB, da, db,
          smul_eq_mul, mul_zero, zero_mul, add_div]
        ring
      _ = 0 := by simp [ce.radius, cm.radius, co.radius]
  · calc
      _ = a^2*polarBalance D r w m E+a*b*polarBalance D r w m M+b^2*polarBalance D r w m O := by
        simp only [polarBalance, vectorDivergence, quadraticModeCombination, map_add, D.leibniz, dAA, dBB, da, db,
          smul_eq_mul, mul_zero, zero_mul, add_div]
        ring
      _ = 0 := by simp [ce.polar, cm.polar, co.polar]
  · calc
      _ = a^2*axialBalance D r w m E+a*b*axialBalance D r w m M+b^2*axialBalance D r w m O := by
        simp only [axialBalance, vectorDivergence, quadraticModeCombination, map_add, D.leibniz, dAA, dBB, da, db,
          smul_eq_mul, mul_zero, zero_mul]
        ring
      _ = 0 := by simp [ce.axial, cm.axial, co.axial]

/-- The raw source is conserved after weighting by constant parent
amplitudes, which need not be real. -/
theorem bare_scattering_source_conserved (embed : ℂᵣ →+* K) (D : Derivation ℚ K K)
    (compatible : ∀ u, D (embed u) = embed (rationalDerivative u))
    (n : ℕ) (hn : 2 ≤ n) (k : ℂ) (ki : k.re = 0) (J a beta : K)
    (da : D a = 0) (db : D beta = 0) (hh : embed R-2 ≠ 0)
    (wave : let r := embed R
            let w := embed (Cᵣ k)
            let ell := embed (Cᵣ (n:ℂ))
            lapse r*D (lapse r*D J) = (w^2+parentPotential r ell)*J) :
    let r := embed R
    let w := embed (Cᵣ k)
    let ell := embed (Cᵣ (n:ℂ))
    ConservedMode D r (2*w) (2*ell) (bareScatteringSource D r w ell J a beta) := by
  obtain ⟨ce,cm,co⟩ := quadratic_scattering_sectors_conserved embed D compatible n hn k ki J hh wave
  dsimp only [bareScatteringSource]
  exact combination_conserved _ _ _ _ _ _ _ _ _ da db ce cm co

/-- Conditional reconstruction for the bare Schwarzschild scattering
source. The reference odd parent has coefficient beta = -i b. Both
parity master fields must solve their own sourced equations. -/
theorem bare_scattering_einstein_reconstruction (embed : ℂᵣ →+* K) (D : Derivation ℚ K K)
    (compatible : ∀ u, D (embed u) = embed (rationalDerivative u))
    (n : ℕ) (hn : 2 ≤ n) (k : ℂ) (ki : k.re = 0) (a b : ℂ) (J c e o : K)
    (hh : embed R-2 ≠ 0) (hs : sineSquared c ≠ 0)
    (wave : let r := embed R
            let w := embed (Cᵣ k)
            let ell := embed (Cᵣ (n:ℂ))
            lapse r*D (lapse r*D J) = (w^2+parentPotential r ell)*J) :
    let r := embed R
    let w := embed (Cᵣ k)
    let ell := embed (Cᵣ (n:ℂ))
    let m := 2*ell
    let alpha := embed (Cᵣ a)
    let beta := embed (Cᵣ (-(Complex.I*b)))
    let s := bareScatteringSource D r w ell J alpha beta
    waveResidual D r (2*w) (SchwarzschildEinstein.zerilli r (modeLambda m)) e =
      evenMasterForcing D r m s.polar →
    waveResidual D r (2*w) (SchwarzschildEinstein.reggeWheeler r (modeLambda m)) o =
      oddMasterForcing D r (2*w) m s.axial →
    let p := reconstructPolar D r (2*w) m e s
    let u := reconstructAxial D r (2*w) m o s.axial
    linearChartEinstein r c (reconstructedChartMetric D (2*w) m c p u) =
      chartSourceTensor m c s ∧
      evenMasterField D r m p.rr p.sphere = e ∧ oddMasterField D r (2*w) m u.time u.radius = o := by
  dsimp only
  intro even odd
  let r := embed R
  let w := embed (Cᵣ k)
  let ell := embed (Cᵣ (n:ℂ))
  let m := 2*ell
  let alpha := embed (Cᵣ a)
  let beta := embed (Cᵣ (-(Complex.I*b)))
  have hr : r ≠ 0 := (map_ne_zero embed).2 RatFunc.X_ne_zero
  have dr : D r = 1 := by simpa only [r, rationalDerivative_radius, map_one] using compatible R
  have constant (z : ℂ) : D (embed (Cᵣ z)) = 0 := by
    rw [compatible, rationalDerivative_constant, _root_.map_zero]
  have d2w : D (2*w) = 0 := by simp [D.leibniz, derivative_two D, w, constant]
  have dm : D m = 0 := by simp [m, D.leibniz, derivative_two D, ell]
  have el : ell = (n : K) := by simp [ell]
  have lab : m = ((2*n : ℕ) : K) := by simp [m, el]
  have hm : m ≠ 0 := by rw [lab]; exact Nat.cast_ne_zero.mpr (by omega)
  have hl : m*(m+1) ≠ 0 := by
    refine mul_ne_zero hm (fun h => ?_)
    rw [lab] at h
    have h' : 2*n+1 = 0 := by exact_mod_cast h
    omega
  have hd : m-1 ≠ 0 := by
    apply sub_ne_zero.mpr
    rw [lab]
    exact_mod_cast (show 2*n ≠ 1 by omega)
  have hmu : (m-1)*(m+2) ≠ 0 := by
    refine mul_ne_zero hd (fun h => ?_)
    rw [lab] at h
    have h' : 2*n+2 = 0 := by exact_mod_cast h
    omega
  have lambda : modeLambda m ≠ 0 := div_ne_zero hmu (by norm_num)
  have dLambda : D (modeLambda m) = 0 := by
    simp [modeLambda, D.leibniz_div_const _ _ (derivative_two D), D.leibniz, dm, derivative_two D]
  have hp : modeLambda m*r+3 ≠ 0 := by
    intro hz
    have hdif := congrArg D hz
    simp only [_root_.map_zero, map_add, D.leibniz, smul_eq_mul, dLambda, dr, derivative_three D,
      mul_one, mul_zero, add_zero] at hdif
    exact lambda hdif
  have conserved := bare_scattering_source_conserved embed D compatible n hn k ki J alpha beta
    (constant a) (constant (-(Complex.I*b))) hh wave
  exact sourced_einstein_reconstruction D r (2*w) m c e o
    (bareScatteringSource D r w ell J alpha beta) hr hh hs hl hmu hp dr d2w dm conserved even odd

#print axioms bare_scattering_source_conserved
#print axioms bare_scattering_einstein_reconstruction

end
end SchwarzschildEinstein.PureOdd.Master
