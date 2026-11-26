import ExactRationalData
import MixturePolynomialCertificate
import RationalCalculus

/-! The certificates prove rational-function identities. The computation
used to propose a cancellation is outside this argument. -/
namespace SchwarzschildMixtures.ExactRational

open Polynomial SchwarzschildLaurent

noncomputable section

local notation "ℂᵣ" => RatFunc ℂ
local notation "ι" => (algebraMap ℂ[X] ℂᵣ)
local notation "Cᵣ" => (RatFunc.C : ℂ →+* ℂᵣ)
local notation "R" => (RatFunc.X : ℂᵣ)
local notation "δ" => rationalDerivative

def Formula.value (k ell : ℂ) : Formula → ℂᵣ
  | .integer z => z
  | .radius => R
  | .frequency => Cᵣ k
  | .angular => Cᵣ ell
  | .add a b => a.value k ell + b.value k ell
  | .neg a => -a.value k ell
  | .mul a b => a.value k ell * b.value k ell
  | .div a b => a.value k ell / b.value k ell
  | .dr a => δ (a.value k ell)

@[simp] theorem Formula.value_num (k ell : ℂ) (n : ℕ) :
    (n : Formula).value k ell = (n : ℂᵣ) := by
  change (↑(n : ℤ) : ℂᵣ) = (n : ℂᵣ)
  exact (Int.cast_natCast n : ((n : ℤ) : ℂᵣ) = (n : ℂᵣ))

@[simp] theorem Formula.value_add (k ell : ℂ) (a b : Formula) :
    (a+b).value k ell = a.value k ell+b.value k ell := rfl

@[simp] theorem Formula.value_sub (k ell : ℂ) (a b : Formula) :
    (a-b).value k ell = a.value k ell-b.value k ell := by
  exact (sub_eq_add_neg _ _).symm

@[simp] theorem Formula.value_mul (k ell : ℂ) (a b : Formula) :
    (a*b).value k ell = a.value k ell*b.value k ell := rfl

@[simp] theorem Formula.value_neg (k ell : ℂ) (a : Formula) :
    (-a).value k ell = -a.value k ell := rfl

@[simp] theorem Formula.value_div (k ell : ℂ) (a b : Formula) :
    (a/b).value k ell = a.value k ell/b.value k ell := rfl

@[simp] theorem Formula.value_dr (k ell : ℂ) (a : Formula) :
    a.dr.value k ell = δ (a.value k ell) := rfl

@[simp] theorem Formula.value_pow (k ell : ℂ) (a : Formula) (n : ℕ) :
    (a^n).value k ell = (a.value k ell)^n := by
  change (Formula.power a n).value k ell = _
  induction n with
  | zero => simp only [Formula.power, Formula.value, Int.cast_one, pow_zero]
  | succ n ih =>
    cases n with
    | zero =>
      change a.value k ell = (a.value k ell)^1
      rw [pow_one]
    | succ n =>
      change ((Formula.power a (n+1)).mul a).value k ell = (a.value k ell)^(n+1+1)
      simpa only [Formula.value, pow_succ] using congrArg (fun x => x*a.value k ell) ih

def Fraction.value (k ell : ℂ) (a : Fraction) : ℂᵣ :=
  ι (Expr.value k ell a.num) / ι (Expr.value k ell a.den)

def Fraction.nonzeroDen (k ell : ℂ) (a : Fraction) : Prop :=
  ι (Expr.value k ell a.den) ≠ 0

def factorValue (k ell : ℂ) (a : Factor) : ℂᵣ := ι (Expr.value k ell a.data)

def DivisorsNonzero (k ell : ℂ) : Prop :=
  ∀ a : Factor, a.valid = true → factorValue k ell a ≠ 0

theorem Cancellation.sound {raw out : Fraction} (h : Cancellation raw out) (k ell : ℂ)
    (defined : raw.nonzeroDen k ell) :
    out.value k ell = raw.value k ell ∧ out.nonzeroDen k ell := by
  have num := congrArg ι (Expr.value_eq_of_check _ _ h.numerator k ell)
  have den := congrArg ι (Expr.value_eq_of_check _ _ h.denominator k ell)
  simp only [Expr.value_mul, map_mul] at num den
  unfold Fraction.nonzeroDen at *
  rw [← den] at defined
  have nonzero := mul_ne_zero_iff.mp defined
  refine ⟨?_, nonzero.1⟩
  unfold Fraction.value
  rw [← num, ← den, mul_div_mul_right _ _ nonzero.2]

private theorem factor_product_nonzero (k ell : ℂ) (hz : DivisorsNonzero k ell)
    (factors : List Factor) (valid : factors.all Factor.valid = true) :
    ι (Expr.value k ell (factorProduct factors)) ≠ 0 := by
  induction factors with
  | nil => simp [factorProduct, Expr.value_constant]
  | cons a rest ih =>
    have hs : a.valid = true ∧ rest.all Factor.valid = true := by simpa using valid
    simpa only [factorProduct, factorValue, List.foldr_cons, Expr.value_mul, map_mul] using
      mul_ne_zero (hz a hs.1) (ih hs.2)

theorem Reduced.sound {e : Formula} {p : Fraction} (proof : Reduced e p)
    (k ell : ℂ) (hz : DivisorsNonzero k ell) :
    e.value k ell = p.value k ell ∧ p.nonzeroDen k ell := by
  induction proof with
  | integer z =>
    simp [Formula.value, Fraction.value, Fraction.polynomial, Fraction.nonzeroDen, Expr.value_constant]
  | radius =>
    simp [Formula.value, Fraction.value, Fraction.polynomial, Fraction.nonzeroDen, NumeratorData.x,
      Expr.value_single, Expr.value_constant, RatFunc.algebraMap_X]
  | frequency =>
    simp [Formula.value, Fraction.value, Fraction.polynomial, Fraction.nonzeroDen,
      Expr.value_constant, RatFunc.algebraMap_C]
  | angular =>
    simp [Formula.value, Fraction.value, Fraction.polynomial, Fraction.nonzeroDen,
      Expr.value_constant, RatFunc.algebraMap_C]
  | @add a b p q out ha hb hpa epa epb =>
    have d : (p.add q).nonzeroDen k ell := by
      simpa only [Fraction.add, Fraction.nonzeroDen, Expr.value_mul, map_mul] using
        mul_ne_zero epa.2 epb.2
    obtain ⟨v, nz⟩ := hpa.sound k ell d
    refine ⟨?_, nz⟩
    rw [Formula.value, epa.1, epb.1, v]
    simp only [Fraction.value, Fraction.add, Expr.value_add, Expr.value_mul, map_add, map_mul]
    rw [div_add_div _ _ epa.2 epb.2]
    ring
  | @neg a p ha ih =>
    constructor
    · simp only [Formula.value, ih.1, Fraction.value, Fraction.neg, Expr.value_neg, map_neg]
      ring
    · exact ih.2
  | @mul a b p q out ha hb hpa epa epb =>
    have d : (p.mul q).nonzeroDen k ell := by
      simpa only [Fraction.mul, Fraction.nonzeroDen, Expr.value_mul, map_mul] using
        mul_ne_zero epa.2 epb.2
    obtain ⟨v, nz⟩ := hpa.sound k ell d
    refine ⟨?_, nz⟩
    rw [Formula.value, epa.1, epb.1, v]
    simp only [Fraction.value, Fraction.mul, Expr.value_mul, map_mul, div_mul_div_comm]
  | @div a b p q out ha hb fs fv fcheck hpa epa epb =>
    have qn : ι (Expr.value k ell q.num) ≠ 0 := by
      rw [Expr.value_eq_of_check _ _ fcheck]
      exact factor_product_nonzero k ell hz fs fv
    have d : (p.div q).nonzeroDen k ell := by
      simpa only [Fraction.div, Fraction.nonzeroDen, Expr.value_mul, map_mul] using
        mul_ne_zero epa.2 qn
    obtain ⟨v, nz⟩ := hpa.sound k ell d
    refine ⟨?_, nz⟩
    rw [Formula.value, epa.1, epb.1, v]
    simp only [Fraction.value, Fraction.div, Expr.value_mul, map_mul]
    field_simp [epa.2, epb.2, qn]
  | @dr a p out ha hpa ih =>
    have d : p.dr.nonzeroDen k ell := by
      simpa only [Fraction.dr, Fraction.nonzeroDen, Expr.value_mul, map_mul] using
        mul_ne_zero ih.2 ih.2
    obtain ⟨v, nz⟩ := hpa.sound k ell d
    refine ⟨?_, nz⟩
    rw [Formula.value, ih.1, v]
    simp [Fraction.value, Fraction.dr, Expr.value_sub, rationalDerivative_div,
      rationalDerivative_algebraMap, pow_two]

#print axioms Reduced.sound

end
end SchwarzschildMixtures.ExactRational
