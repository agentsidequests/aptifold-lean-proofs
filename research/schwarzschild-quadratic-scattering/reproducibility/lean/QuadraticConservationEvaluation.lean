import QuadraticConservationWitnesses
import EvenFormulaEvaluation
import VacuumRadialSoundness

/-! Interpret the two exact conservation programs in the radial field
used for the metric and the daughter reconstruction. -/
namespace SchwarzschildEinstein.PureOdd.Master

open Mixed SchwarzschildMixtures.ExactRational SchwarzschildMixtures.PureOddProgram
open SchwarzschildLaurent

noncomputable section
variable {K : Type} [DivisionRing K]
variable (d : K → K) (radius frequency angular : K)

local notation "F" => Formula.interpret d radius frequency angular
local notation "Q" => mapRow F
local notation "C" => (fun q : Rat => (q : K))
local notation "q" => Mixed.rationalConstant

private theorem map_polar_source (zero cross time : Quadratic Formula) (p : EvenSource (Quadratic Formula)) :
    mapModeSource Q (purePolarSource zero p cross time) =
      purePolarSource (Q zero) (mapSource Q p) (Q cross) (Q time) := rfl

private theorem eval_polar_extra (r k ell : Formula) (ts : List Polar.JetProduct) :
    Q (polarExtraRows q Formula.dr r k ell ts) =
      polarExtraRows C d (F r) (F k) (F ell) ts := by
  induction ts with
  | nil => simp [polarExtraRows, Polar.evaluateWith, mapRow, eval_rat]
  | cons t tail ih =>
    simp only [polarExtraRows, Polar.evaluateWith, List.foldr_cons] at ih ⊢
    simp only [eval_plus, eval_scale, Polar.eval_product, Polar.eval_jet, Mixed.eval_polar,
      Polar.eval_weight, eval_rat, Formula.interpret_div, Formula.interpret_sub, ih]

private theorem eval_even_source (r k ell : Formula) :
    mapModeSource Q (evenParentSourceRows q Formula.dr r k ell) =
      evenParentSourceRows C d (F r) (F k) (F ell) := by
  simp only [evenParentSourceRows, map_polar_source, Polar.eval_source, eval_polar_extra,
    eval_scale, eval_rat, Formula.interpret_neg,
    Formula.interpret_div, Formula.interpret_mul]
  simp only [mapRow, eval_rat]

private theorem eval_odd_extra (r k ell : Formula) (T P : RadialJet (Linear Formula)) :
    let cross := fun A B => oddParentCross q r k ell (q 1/r) (q 1/(r-q 2)) A B
    let time := fun A B => oddParentTimeVector q r k ell (q 1/r) (q 1/(r-q 2)) A B
    let cross' := fun A B => oddParentCross C (F r) (F k) (F ell) (1/F r) (1/(F r-2)) A B
    let time' := fun A B => oddParentTimeVector C (F r) (F k) (F ell) (1/F r) (1/(F r-2)) A B
    Q (rows cross T P) = rows cross' (mapJet (mapLinear F) T) (mapJet (mapLinear F) P) ∧
    Q (rows time T P) = rows time' (mapJet (mapLinear F) T) (mapJet (mapLinear F) P) := by
  dsimp only
  constructor <;> apply eval_rows d radius frequency angular <;> intro A B <;>
    simp only [oddParentCross, oddParentTimeVector, mapJet, Formula.interpret_add, Formula.interpret_neg,
      Formula.interpret_mul, Formula.interpret_div, Formula.interpret_sub, eval_rat, Rat.cast_one, Rat.cast_ofNat]

private theorem eval_odd_source (r k ell : Formula) :
    mapModeSource Q (oddParentSourceRows q Formula.dr r k ell) =
      oddParentSourceRows C d (F r) (F k) (F ell) := by
  obtain ⟨cross,time⟩ := eval_odd_extra d radius frequency angular r k ell
    (parentJet Formula.dr r k ell (timeAmplitude r)) (parentJet Formula.dr r k ell (radiusAmplitude r k))
  simp only [oddParentSourceRows, map_polar_source, eval_source_rows, cross, time,
    eval_parent_jet, eval_time_amplitude, eval_radius_amplitude, Rat.cast_one, Rat.cast_ofNat]
  simp only [mapRow, eval_rat]

private def mapBalances {A B : Type} (g : A → B) (v : A × A × A) : B × B × B :=
  (g v.1,g v.2.1,g v.2.2)

private theorem eval_balances (r k ell : Formula) (s : ModeSource (Quadratic Formula)) :
    mapBalances Q (polarConservationRows q Formula.dr r k ell s) =
      polarConservationRows C d (F r) (F k) (F ell) (mapModeSource Q s) := by
  simp only [mapBalances, polarConservationRows, mapModeSource, eval_plus, eval_scale,
    eval_quadratic_derivative, Formula.interpret_mul, Formula.interpret_add, Formula.interpret_sub,
    Formula.interpret_div, Formula.interpret_neg, eval_rat, lapse]
  eval_mixed_formula

end

section Physical

variable {K : Type} [Field K] [CharZero K]
local notation "C" => (fun q : Rat => (q : K))
local notation "ℂᵣ" => RatFunc ℂ
local notation "R" => (RatFunc.X : ℂᵣ)
local notation "Cᵣ" => (RatFunc.C : ℂ →+* ℂᵣ)

omit [CharZero K] in
private theorem evaluated_row_zero (embed : ℂᵣ →+* K) (d : K → K)
    (compatible : ∀ u, d (embed u) = embed (rationalDerivative u))
    (n : ℕ) (hn : 2 ≤ n) (k : ℂ) (ki : k.re = 0) (v : Quadratic Formula)
    (a : Vacuum.zeroCertificate v.1) (b : Vacuum.zeroCertificate v.2.1)
    (c : Vacuum.zeroCertificate v.2.2) :
    mapRow (Formula.interpret d (embed R) (embed (Cᵣ k)) (embed (Cᵣ (n:ℂ)))) v = (0,0,0) := by
  simp only [mapRow, Vacuum.interpreted_extension d embed compatible, Vacuum.formula_zero _ a n hn k ki,
    Vacuum.formula_zero _ b n hn k ki, Vacuum.formula_zero _ c n hn k ki, map_zero]

theorem polar_conservation_coefficients_zero (embed : ℂᵣ →+* K) (d : K → K)
    (compatible : ∀ u, d (embed u) = embed (rationalDerivative u))
    (n : ℕ) (hn : 2 ≤ n) (k : ℂ) (ki : k.re = 0) (even : Bool) :
    let r := embed R
    let w := embed (Cᵣ k)
    let ell := embed (Cᵣ (n:ℂ))
    let s := if even then evenParentSourceRows C d r w ell else oddParentSourceRows C d r w ell
    polarConservationRows C d r w ell s = ((0,0,0),(0,0,0),(0,0,0)) := by
  let r := embed R
  let w := embed (Cᵣ k)
  let ell := embed (Cᵣ (n:ℂ))
  let eval := Formula.interpret d r w ell
  have mapped : mapBalances (mapRow eval) (conservationProgram even) =
      polarConservationRows C d r w ell
        (if even then evenParentSourceRows C d r w ell else oddParentSourceRows C d r w ell) := by
    cases even <;>
      simp [conservationProgram, eval, eval_balances, eval_even_source, eval_odd_source, Formula.interpret]
  dsimp only
  rw [← mapped]
  let zero := evaluated_row_zero embed d compatible n hn k ki
  cases even
  · exact Prod.ext
      (zero _ zeroOddTimeSquare zeroOddTimeCross zeroOddTimeDerivativeSquare)
      (Prod.ext
        (zero _ zeroOddRadiusSquare zeroOddRadiusCross zeroOddRadiusDerivativeSquare)
        (zero _ zeroOddAngularSquare zeroOddAngularCross zeroOddAngularDerivativeSquare))
  · exact Prod.ext
      (zero _ zeroEvenTimeSquare zeroEvenTimeCross zeroEvenTimeDerivativeSquare)
      (Prod.ext
        (zero _ zeroEvenRadiusSquare zeroEvenRadiusCross zeroEvenRadiusDerivativeSquare)
        (zero _ zeroEvenAngularSquare zeroEvenAngularCross zeroEvenAngularDerivativeSquare))

end Physical

#print axioms polar_conservation_coefficients_zero

end SchwarzschildEinstein.PureOdd.Master
