import OutgoingEndpointData
import AdmittedMixtureField
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-! Bind the endpoint certificates to the evaluated rational rows.
Each effective coefficient is a quotient of polynomials in \(1/r\)
whose denominator is nonzero at \(1/r=0\). -/
namespace SchwarzschildMixtures.OutgoingData

open Polynomial SchwarzschildLaurent

noncomputable section

local notation "ℂᵣ" => RatFunc ℂ
local notation "ι" => (algebraMap ℂ[X] ℂᵣ)

def scalarValue (k ell : ℂ) (p : Expr) : ℂ := (Expr.value k ell p).eval 0

@[simp] theorem scalar_add (k ell : ℂ) (p q : Expr) :
    scalarValue k ell (.add p q) = scalarValue k ell p + scalarValue k ell q := by
  simp [scalarValue]

@[simp] theorem scalar_sub (k ell : ℂ) (p q : Expr) :
    scalarValue k ell (.sub p q) = scalarValue k ell p - scalarValue k ell q := by
  simp [scalarValue, Expr.sub, sub_eq_add_neg]

@[simp] theorem scalar_neg (k ell : ℂ) (p : Expr) :
    scalarValue k ell (.neg p) = -scalarValue k ell p := by simp [scalarValue]

@[simp] theorem scalar_mul (k ell : ℂ) (p q : Expr) :
    scalarValue k ell (.mul p q) = scalarValue k ell p * scalarValue k ell q := by
  simp [scalarValue]

@[simp] theorem scalar_constant (k ell : ℂ) (n : ℤ) :
    scalarValue k ell (Expr.constant n) = (n : ℂ) := by
  simp [scalarValue, Expr.value_constant]

@[simp] theorem scalar_frequency (k ell : ℂ) : scalarValue k ell Expr.frequency = k := by
  simp [scalarValue]

@[simp] theorem scalar_angular (k ell : ℂ) : scalarValue k ell Expr.angular = ell := by
  simp [scalarValue]

theorem scalar_of_certificate (k ell : ℂ) {p q : Expr} (h : Expr.Check p q) :
    scalarValue k ell p = scalarValue k ell q :=
  congrArg (eval 0) (Expr.value_eq_of_check _ _ h k ell)

private theorem digit_values (k ell : ℂ) (r w size weight offset positive negative : Nat) :
    Poly.value k ell (CoefficientBand.digits r w weight size offset positive negative) =
      C ((Poly.value k ell (CoefficientBand.digits 0 w weight size offset positive negative)).eval 0)
        * X^r := by
  induction size generalizing offset positive negative with
  | zero => simp [CoefficientBand.digits, Poly.value]
  | succ j ih =>
    simp only [CoefficientBand.digits, Poly.value, Poly.termValue, ih, pow_zero, mul_one,
      eval_add, eval_C, map_add, add_mul]

private theorem band_value (k ell : ℂ) (b : CoefficientBand) :
    Poly.value k ell b.terms =
      C ((Poly.value k ell {b with radial := 0}.terms).eval 0) * X^b.radial := by
  exact digit_values k ell _ _ _ _ _ _ _

private theorem bands_degree (k ell : ℂ) (n : ℕ) (rows : List CoefficientBand)
    (h : ∀ x ∈ rows, x.radial ≤ n) :
    (Expr.value k ell (.bands rows)).natDegree ≤ n := by
  induction rows with
  | nil => simp [Expr.value, Poly.value]
  | cons b rows ih =>
    change (Poly.value k ell (b.terms ++ (rows.map CoefficientBand.terms).flatten)).natDegree ≤ n
    rw [Poly.value_append]
    apply (natDegree_add_le _ _).trans
    apply max_le
    · rw [band_value]
      exact (natDegree_C_mul_X_pow_le _ _).trans (h _ (by simp))
    · exact ih (fun x hx => h _ (by simp [hx]))

theorem degree_from_cap (k ell : ℂ) (n : ℕ) (p : Expr) (check : withinRadialCap n p = true) :
    (Expr.value k ell p).natDegree ≤ n := by
  cases p <;> simp only [withinRadialCap, Bool.false_eq_true] at check
  rename_i rows
  exact bands_degree k ell n rows (fun x hx => of_decide_eq_true (List.all_eq_true.mp check x hx))

private theorem band_coefficient (k ell : ℂ) (n : ℕ) (rows : List CoefficientBand) :
    (Expr.value k ell (.bands rows)).coeff n = scalarValue k ell (coefficientAt n (.bands rows)) := by
  induction rows with
  | nil => simp [Expr.value, scalarValue, coefficientAt, Poly.value]
  | cons b rows ih =>
    change
      (Poly.value k ell (b.terms ++ (rows.map CoefficientBand.terms).flatten)).coeff n =
        scalarValue k ell (coefficientAt n (.bands (b::rows)))
    rw [Poly.value_append, coeff_add, band_value k ell b]
    change
      (C ((Poly.value k ell {b with radial := 0}.terms).eval 0)*X^b.radial).coeff n +
        (Expr.value k ell (.bands rows)).coeff n =
      scalarValue k ell (coefficientAt n (.bands (b::rows)))
    rw [ih, coeff_C_mul_X_pow]
    by_cases e : b.radial = n
    · simp [e, coefficientAt, scalarValue, Expr.value, Poly.value_append]
    · simp [e, Ne.symm e, coefficientAt]

theorem coefficient_from_cap (k ell : ℂ) (n cap : ℕ) (p : Expr) (check : withinRadialCap cap p = true) :
    (Expr.value k ell p).coeff n = scalarValue k ell (coefficientAt n p) := by
  cases p <;> simp only [withinRadialCap, Bool.false_eq_true] at check
  exact band_coefficient k ell n _

def parentLead (ell : ℂ) : ℂ := (ell-1)*(ell+2)
def daughterLead (ell : ℂ) : ℂ := (2*ell-1)*(ell+1)

def reflectedDenominator (scalar ell t : ℂ) : ℂ :=
  scalar*(1-2*t)*(parentLead ell+6*t)^5*(daughterLead ell+3*t)

theorem reflected_denominator_evaluation (scalar ell r : ℂ) (hr : r ≠ 0) :
    reflectedDenominator scalar ell r⁻¹*r^18 = (fieldDenominator scalar ell).eval r := by
  simp [reflectedDenominator, fieldDenominator, shiftedRadius, parentPole, daughterPole,
    parentLead, daughterLead]
  field_simp [hr]

theorem reflected_denominator_nonzero (scalar : ℂ) (hs : scalar ≠ 0) (n : ℕ) (hn : 2 ≤ n) :
    reflectedDenominator scalar n 0 ≠ 0 := by
  have hn' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hp : parentLead (n : ℂ) ≠ 0 := by
    unfold parentLead
    exact mul_ne_zero (by exact_mod_cast (show (n : ℝ)-1 ≠ 0 by linarith))
      (by exact_mod_cast (show (n : ℝ)+2 ≠ 0 by linarith))
  have hd : daughterLead (n : ℂ) ≠ 0 := by
    unfold daughterLead
    exact mul_ne_zero (by exact_mod_cast (show 2*(n : ℝ)-1 ≠ 0 by linarith))
      (by exact_mod_cast (show (n : ℝ)+1 ≠ 0 by linarith))
  simp [reflectedDenominator,hs,hp,hd]

private theorem evaluated_fraction (p q : ℂ[X]) (r : ℂ) (hq : q.eval r ≠ 0) :
    RatFunc.eval (RingHom.id ℂ) r (ι p/ι q) = p.eval r/q.eval r := by
  have val := RadiusValue.fraction p q hq
  have denom := val.denom_ne_zero
  have can := RadiusValue.fraction (ι p/ι q).num (ι p/ι q).denom denom
  rw [RatFunc.num_div_denom] at can
  simpa only [RatFunc.eval, Polynomial.eval₂_id] using can.unique val

/-- The raw polynomial contributes with the extra \(r^d\) from its
number of \(Z\) factors. The reflected numerator has the same scale as
the reflected denominator. -/
theorem effective_coefficient (p : ℂ[X]) (n d : ℕ) (scale ell r : ℂ)
    (hd : n+d = 18) (hp : p.natDegree ≤ n) (hr : r ≠ 0)
    (hq : reflectedDenominator scale ell r⁻¹ ≠ 0) :
    RatFunc.eval (RingHom.id ℂ) r (ι p/ι (fieldDenominator scale ell))*r^d =
      (reflect n p).eval r⁻¹ / reflectedDenominator scale ell r⁻¹ := by
  let : Invertible r := invertibleOfNonzero hr
  have px : (reflect n p).eval r⁻¹*r^n = p.eval r := by
    simpa only [eval₂_id, invOf_eq_inv] using eval₂_reflect_mul_pow (RingHom.id ℂ) r n p hp
  have qx := reflected_denominator_evaluation scale ell r hr
  rw [evaluated_fraction _ _ _ (qx ▸ (mul_ne_zero hq (pow_ne_zero _ hr))), ← px, ← qx]
  rw [div_mul_eq_mul_div, mul_assoc, ← pow_add, hd, mul_div_mul_right _ _ (pow_ne_zero _ hr)]

#print axioms degree_from_cap
#print axioms coefficient_from_cap
#print axioms effective_coefficient

end
end SchwarzschildMixtures.OutgoingData
