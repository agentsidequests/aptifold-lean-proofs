import PureOddProgram
import Mathlib.Algebra.Field.Defs
import Mathlib.Data.Int.Cast.Basic

/-! Evaluate each stage of the symbolic calculation before composing
the stages. This keeps the proof from expanding the same radial
derivative and tensor coefficients at every use. -/
namespace SchwarzschildMixtures.ExactRational.Formula

variable {K : Type*} [DivisionRing K]
variable (d : K → K) (radius frequency angular : K)

def interpret : Formula → K
  | .integer z => z
  | .radius => radius
  | .frequency => frequency
  | .angular => angular
  | .add a b => interpret a + interpret b
  | .neg a => -interpret a
  | .mul a b => interpret a * interpret b
  | .div a b => interpret a / interpret b
  | .dr a => d (interpret a)

local notation "E" => (interpret d radius frequency angular)

theorem interpret_add (a b : Formula) : E (a+b) = E a+E b := rfl
theorem interpret_sub (a b : Formula) : E (a-b) = E a-E b := (sub_eq_add_neg _ _).symm
theorem interpret_neg (a : Formula) : E (-a) = -E a := rfl
theorem interpret_mul (a b : Formula) : E (a*b) = E a*E b := rfl
theorem interpret_div (a b : Formula) : E (a/b) = E a/E b := rfl
theorem interpret_dr (a : Formula) : E a.dr = d (E a) := rfl

theorem interpret_pow (a : Formula) (n : ℕ) : E (a^n) = (E a)^n := by
  change E (power a n) = _
  induction n with
  | zero => simp [power, interpret]
  | succ n ih =>
    cases n with
    | zero =>
      change E a = (E a)^1
      rw [pow_one]
    | succ n =>
      change E ((power a (n+1)).mul a) = (E a)^(n+1+1)
      simpa only [interpret, pow_succ] using congrArg (fun x => x*E a) ih

end SchwarzschildMixtures.ExactRational.Formula

namespace SchwarzschildMixtures.PureOddProgram

open SchwarzschildEinstein.PureOdd ExactRational

variable {K : Type*} [DivisionRing K]

def mapLinear (f : Formula → K) (p : Linear Formula) : Linear K :=
  (f p.1, f p.2)

def mapSource (f : Quadratic Formula → Quadratic K)
    (s : EvenSource (Quadratic Formula)) : EvenSource (Quadratic K) :=
  ⟨f s.tt, f s.rr, f s.radialVector, f s.sphereTrace, f s.traceFree⟩

variable (d : K → K) (radius frequency angular : K)

local notation "E" => (Formula.interpret d radius frequency angular)
local notation "L" => (mapLinear E)
local notation "Q" => (mapRow E)

macro "eval_formula" : tactic =>
  `(tactic|
    (simp only [Formula.interpret_add, Formula.interpret_sub, Formula.interpret_neg,
      Formula.interpret_mul, Formula.interpret_div, Formula.interpret_pow, Formula.interpret_dr]
     <;> simp only [SchwarzschildEinstein.PureOdd.instOfNat_pureOddFormulas, OfNat.ofNat,
       Formula.interpret, Int.cast_natCast]
     <;> rfl))

theorem eval_linear_derivative (r w e : Formula) (p : Linear Formula) :
    L (linearDerivative Formula.dr r w e p) = linearDerivative d (E r) (E w) (E e) (L p) := by
  rcases p with ⟨a,b⟩
  simp only [linearDerivative, mapLinear, jetU, jetV, jetW, parentPotential, lapse]
  eval_formula

theorem eval_quadratic_derivative (r w e : Formula) (p : Quadratic Formula) :
    Q (rowDerivative Formula.dr r w e p) = rowDerivative d (E r) (E w) (E e) (Q p) := by
  rcases p with ⟨a,b,c⟩
  simp only [rowDerivative, mapRow, jetU, jetV, jetW, parentPotential, lapse]
  eval_formula

theorem eval_parent_jet (r w e : Formula) (p : Linear Formula) :
    mapJet L (parentJet Formula.dr r w e p) = parentJet d (E r) (E w) (E e) (L p) := by
  simp only [parentJet, mapJet, eval_linear_derivative]

theorem eval_time_amplitude (r : Formula) :
    L (timeAmplitude r) = timeAmplitude (E r) := by
  simp only [timeAmplitude, mapLinear, lapse]
  eval_formula

theorem eval_radius_amplitude (r w : Formula) :
    L (radiusAmplitude r w) = radiusAmplitude (E r) (E w) := by
  simp only [radiusAmplitude, mapLinear, lapse]
  eval_formula

private theorem eval_tt (r w e : Formula) (T P : RadialJet Formula) :
    E (compactTT r w e T P) = compactTT (E r) (E w) (E e) (mapJet E T) (mapJet E P) := by
  simp only [compactTT, mapJet]
  eval_formula

private theorem eval_rr (r w e : Formula) (T P : RadialJet Formula) :
    E (compactRR r w e T P) = compactRR (E r) (E w) (E e) (mapJet E T) (mapJet E P) := by
  simp only [compactRR, mapJet]
  eval_formula

private theorem eval_radial_vector (r w e : Formula) (T P : RadialJet Formula) :
    E (compactRadialVector r w e T P) =
      compactRadialVector (E r) (E w) (E e) (mapJet E T) (mapJet E P) := by
  simp only [compactRadialVector, mapJet]
  eval_formula

private theorem eval_sphere_trace (r w e : Formula) (T P : RadialJet Formula) :
    E (compactSphereTrace r w e T P) =
      compactSphereTrace (E r) (E w) (E e) (mapJet E T) (mapJet E P) := by
  simp only [compactSphereTrace, mapJet]
  eval_formula

private theorem eval_trace_free (r w e : Formula) (T P : RadialJet Formula) :
    E (compactTraceFree r w e T P) =
      compactTraceFree (E r) (E w) (E e) (mapJet E T) (mapJet E P) := by
  simp only [compactTraceFree, mapJet]
  eval_formula

theorem eval_rows
    (f : RadialJet Formula → RadialJet Formula → Formula)
    (g : RadialJet K → RadialJet K → K)
    (h : ∀ T P, E (f T P) = g (mapJet E T) (mapJet E P))
    (T P : RadialJet (Linear Formula)) :
    Q (rows f T P) = rows g (mapJet L T) (mapJet L P) := by
  simp only [rows, mapRow, h, mapJet, mapLinear, Formula.interpret_add, Formula.interpret_sub]

theorem eval_source_rows (r w e : Formula) :
    mapSource Q (sourceRows Formula.dr r w e) = sourceRows d (E r) (E w) (E e) := by
  simp only [sourceRows, mapSource,
    eval_rows d radius frequency angular _ _ (eval_tt d radius frequency angular r w e),
    eval_rows d radius frequency angular _ _ (eval_rr d radius frequency angular r w e),
    eval_rows d radius frequency angular _ _ (eval_radial_vector d radius frequency angular r w e),
    eval_rows d radius frequency angular _ _ (eval_sphere_trace d radius frequency angular r w e),
    eval_rows d radius frequency angular _ _ (eval_trace_free d radius frequency angular r w e),
    eval_parent_jet, eval_time_amplitude, eval_radius_amplitude]

theorem eval_scale (a : Formula) (p : Quadratic Formula) :
    Q (scale a p) = scale (E a) (Q p) := by
  simp only [scale, mapRow, Formula.interpret_mul]

theorem eval_plus (p q : Quadratic Formula) :
    Q (plus p q) = plus (Q p) (Q q) := by
  simp only [plus, mapRow, Formula.interpret_add]

private theorem eval_minus (p q : Quadratic Formula) :
    Q (minus p q) = minus (Q p) (Q q) := by
  simp only [minus, mapRow, Formula.interpret_sub]

private theorem eval_even_master (r w e : Formula) (s : EvenSource (Quadratic Formula)) :
    Q (evenMaster Formula.dr r w e s) = evenMaster d (E r) (E w) (E e) (mapSource Q s) := by
  simp only [evenMaster, eval_scale, eval_plus, eval_quadratic_derivative, mapSource, lapse]
  eval_formula

theorem eval_projected_master (r w e : Formula) (s : EvenSource (Quadratic Formula)) :
    Q (projectedMaster Formula.dr r w e s) =
      projectedMaster d (E r) (E w) (E e) (mapSource Q s) := by
  simp only [projectedMaster, eval_scale, eval_minus, eval_quadratic_derivative,
    eval_even_master, lapse]
  eval_formula

theorem program_value : Q coefficients =
    bareForcing d radius frequency angular := by
  simp only [coefficients, bareForcing, eval_projected_master, eval_source_rows, Formula.interpret]

#print axioms program_value

end SchwarzschildMixtures.PureOddProgram
