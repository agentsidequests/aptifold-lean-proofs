import OutgoingEndpointPolynomials
import OutgoingEndpointCaseOne
import OutgoingEndpointCaseTwo
import AdmittedMixtures

/-! The endpoint coefficients of the two regularized fields, in the
reference-parent convention and before strain normalization. -/
namespace SchwarzschildMixtures.OutgoingData

open Polynomial SchwarzschildLaurent NumeratorData

noncomputable section

local notation "ℂᵣ" => RatFunc ℂ

def mixtureNumerators (second : Bool) : ExprRow :=
  if second then Case2.field else Case1.field

def mixtureMultiplier (second : Bool) : ℕ :=
  if second then Case2.multiplier else Case1.multiplier

def reciprocalNumerators (second : Bool) (k ell : ℂ) : Row ℂ[X] :=
  let p := rowValue k ell (mixtureNumerators second)
  (reflect 18 p.1, reflect 16 p.2.1, reflect 14 p.2.2)

def reciprocalScalar (second : Bool) (k ell : ℂ) : ℂ :=
  fieldScalar (mixtureMultiplier second) second k ell

def reciprocalCoefficients (second : Bool) (k ell t : ℂ) : Row ℂ :=
  let d := reflectedDenominator (reciprocalScalar second k ell) ell t
  mapRow (fun p : ℂ[X] => p.eval t/d) (reciprocalNumerators second k ell)

def effectiveFieldCoefficients (second : Bool) (k ell r : ℂ) : Row ℂ :=
  let p := admittedField second k ell
  let atRadius := RatFunc.eval (RingHom.id ℂ) r
  (atRadius p.1, atRadius p.2.1*r^2, atRadius p.2.2*r^4)

def signedWeight (p : Row ℂ) (rate : ℂ) : ℂ := p.1+rate*p.2.1+rate^2*p.2.2

def rationalAngularNumerator (ell : ℂ) : ℂ :=
  (20*ell^3+35*ell^2+ell-8)*ell^2*(ell-1)^2*(ell+1)*(ell+2)

def rationalAngularFactor (ell : ℂ) : ℂ := rationalAngularNumerator ell/(288*(2*ell-1))

def endpointOutgoing (second : Bool) (k ell : ℂ) : ℂ :=
  if second then
    rationalAngularFactor ell*k*(daughterGamma ell*k-gamma ell^2) /
      ((k+gamma ell)^2*(daughterGamma ell-gamma ell)^2)
  else 0

def endpointIncoming (second : Bool) (k ell : ℂ) : ℂ :=
  if second then
    -(rationalAngularFactor ell*daughterGamma ell*k*(gamma ell-k)^2 /
      ((daughterGamma ell-gamma ell)^2*(k+gamma ell)^2*(k-daughterGamma ell)))
  else -(rationalAngularFactor ell*k^2/((k+gamma ell)^2*(k-daughterGamma ell)))

private theorem caps (second : Bool) :
    withinRadialCap 18 (mixtureNumerators second).1 = true ∧
      withinRadialCap 16 (mixtureNumerators second).2.1 = true ∧
      withinRadialCap 14 (mixtureNumerators second).2.2 = true := by
  cases second
  · exact ⟨first_cap_a,first_cap_b,first_cap_c⟩
  · exact ⟨second_cap_a,second_cap_b,second_cap_c⟩

theorem reciprocal_at_zero_nonzero (second : Bool) (n : ℕ) (hn : 2 ≤ n)
    (k : ℂ) (hk : k ≠ 0) (ki : k.re = 0) :
    reflectedDenominator (reciprocalScalar second k n) n 0 ≠ 0 := by
  have pos : 0 < mixtureMultiplier second := by cases second <;> decide
  exact reflected_denominator_nonzero _ (fieldScalar_ne_zero _ n pos hn second k hk ki) n hn

theorem effective_row_equation (second : Bool) (k ell r : ℂ) (hr : r ≠ 0)
    (hq : reflectedDenominator (reciprocalScalar second k ell) ell r⁻¹ ≠ 0) :
    effectiveFieldCoefficients second k ell r = reciprocalCoefficients second k ell r⁻¹ := by
  obtain ⟨ha,hb,hc⟩ := caps second
  have field : admittedField second k ell =
      localField (mixtureNumerators second) (mixtureMultiplier second) second k ell := by
    cases second <;> rfl
  have A := effective_coefficient (Expr.value k ell (mixtureNumerators second).1) 18 0
    (reciprocalScalar second k ell) ell r rfl (degree_from_cap k ell 18 _ ha) hr hq
  have B := effective_coefficient (Expr.value k ell (mixtureNumerators second).2.1) 16 2
    (reciprocalScalar second k ell) ell r rfl (degree_from_cap k ell 16 _ hb) hr hq
  have C := effective_coefficient (Expr.value k ell (mixtureNumerators second).2.2) 14 4
    (reciprocalScalar second k ell) ell r rfl (degree_from_cap k ell 14 _ hc) hr hq
  unfold effectiveFieldCoefficients
  rw [field]
  refine Prod.ext ?_ (Prod.ext B C)
  simpa only [localField,fractionRow,rowValue,mapRow,reciprocalCoefficients,reciprocalNumerators,
    reciprocalScalar,pow_zero,mul_one] using A

private theorem reflected_coeff (k ell : ℂ) (d j : ℕ) (p : Expr) (hp : withinRadialCap d p = true)
    (hj : j ≤ d) :
    (reflect d (Expr.value k ell p)).coeff j = scalarValue k ell (coefficientAt (d-j) p) := by
  rw [coeff_reflect,revAt_le hj,coefficient_from_cap k ell (d-j) d p hp]

theorem mixed_reciprocal_divisible (second : Bool) (k ell : ℂ) :
    X^2 ∣ (reciprocalNumerators second k ell).1 - C (k^2)*(reciprocalNumerators second k ell).2.2 := by
  obtain ⟨ha,_,hc⟩ := caps second
  have lead : Expr.Check (mixedLead (mixtureNumerators second)) (c 0) := by
    cases second
    · exact first_mixed_lead
    · exact second_mixed_lead
  have next : Expr.Check (mixedNext (mixtureNumerators second)) (c 0) := by
    cases second
    · exact first_mixed_next
    · exact second_mixed_next
  rw [X_pow_dvd_iff]
  intro j hj
  have replace : j=0 ∨ j=1 := by omega
  change (reflect 18 (Expr.value k ell (mixtureNumerators second).1) -
    C (k^2)*reflect 14 (Expr.value k ell (mixtureNumerators second).2.2)).coeff j = 0
  rcases replace with rfl | rfl
  · rw [coeff_sub,coeff_C_mul,reflected_coeff _ _ 18 0 _ ha (by decide),
      reflected_coeff _ _ 14 0 _ hc (by decide)]
    simpa [mixedLead,topA,topC,w,c,pow_two] using scalar_of_certificate k ell lead
  · rw [coeff_sub,coeff_C_mul,reflected_coeff _ _ 18 1 _ ha (by decide),
      reflected_coeff _ _ 14 1 _ hc (by decide)]
    simpa [mixedNext,w,c,pow_two] using scalar_of_certificate k ell next

theorem mixed_endpoint_zero (second : Bool) (k ell : ℂ) :
    let p := reciprocalCoefficients second k ell 0
    p.1-k^2*p.2.2 = 0 := by
  obtain ⟨q,eq⟩ := mixed_reciprocal_divisible second k ell
  have e := congrArg (eval (0 : ℂ)) eq
  simp only [eval_sub,eval_mul,eval_C,eval_pow,eval_X,zero_pow (by decide : 2 ≠ 0),zero_mul] at e
  change (reciprocalNumerators second k ell).1.eval 0 /
      reflectedDenominator (reciprocalScalar second k ell) ell 0 -
    k^2*((reciprocalNumerators second k ell).2.2.eval 0 /
      reflectedDenominator (reciprocalScalar second k ell) ell 0) = 0
  rw [← mul_div_assoc, ← sub_div, e, zero_div]

private theorem signed_normalized (second : Bool) (k ell : ℂ) :
    let d := reflectedDenominator (reciprocalScalar second k ell) ell 0
    signedWeight (reciprocalCoefficients second k ell 0) k =
      scalarValue k ell (outgoingLead (mixtureNumerators second))/d ∧
    signedWeight (reciprocalCoefficients second k ell 0) (-k) =
      scalarValue k ell (incomingLead (mixtureNumerators second))/d := by
  obtain ⟨ha,hb,hc⟩ := caps second
  dsimp only [signedWeight,reciprocalCoefficients,reciprocalNumerators,mapRow,rowValue]
  simp only [← coeff_zero_eq_eval_zero,reflected_coeff k ell 18 0 _ ha (by decide),
    reflected_coeff k ell 16 0 _ hb (by decide),reflected_coeff k ell 14 0 _ hc (by decide)]
  constructor <;> simp [outgoingLead,incomingLead,topA,topB,topC,w,pow_two,div_eq_mul_inv] <;> ring

private theorem factor_num_value (k ell : ℂ) :
    scalarValue k ell factorNumerator = rationalAngularNumerator ell := by
  simp only [factorNumerator,parityPolynomial,square,c,l,rationalAngularNumerator,
    scalar_mul,scalar_add,scalar_sub,scalar_constant,scalar_angular,Int.cast_ofNat]
  ring

private theorem factor_den_value (k ell : ℂ) :
    scalarValue k ell factorDenominator = 288*(2*ell-1) := by
  simp [factorDenominator,c,u,l]

private theorem gamma_value (k ell : ℂ) : scalarValue k ell gammaTwelve = 12*gamma ell := by
  simp [gammaTwelve,gamma,c,l]
  ring

private theorem daughter_value (k ell : ℂ) : scalarValue k ell daughterSix = 6*daughterGamma ell := by
  simp [daughterSix,daughterGamma,gamma,c,u,l]
  ring

private theorem gap_value (k ell : ℂ) :
    scalarValue k ell gammaGapTwelve = 12*(daughterGamma ell-gamma ell) := by
  simp [gammaGapTwelve,c,gamma_value,daughter_value]
  ring

private theorem scalar_leading_denominator (m : ℕ) (second : Bool) (k ell : ℂ) :
    reflectedDenominator (fieldScalar m second k ell) ell 0 =
      scalarValue k ell (denominatorBase m second) *
        (12*(k+gamma ell))^2*(6*(k-daughterGamma ell)) := by
  have mix : scalarValue k ell (if second then square (Expr.sub (Expr.mul (c 7) l) (c 1)) else c 1) =
      (if second then (7*ell-1)^2 else 1) := by
    cases second <;> simp [square,c,l,pow_two]
  simp only [denominatorBase,scalar_mul]
  rw [mix]
  simp only [u,scalar_mul,scalar_add,scalar_sub,square,fifth,l,w,c,
    scalar_constant,scalar_angular,scalar_frequency,Int.cast_one,Int.cast_ofNat,Int.cast_natCast]
  simp only [reflectedDenominator,fieldScalar,sub_zero,mul_zero,add_zero,mul_one,
    parentLead,daughterLead,pow_succ,pow_zero,one_mul]
  ac_rfl

private theorem clear_second_out (L F base k g G : ℂ) (hL : L ≠ 0) (hplus : k+g ≠ 0)
    (hgap : G-g ≠ 0) :
    144*F*k*(24*(6*G)*k-(12*g)*(12*g))*base*(6*k-6*G) =
      L*(12*(G-g))^2*((F/L*k*(G*k-g^2)/((k+g)^2*(G-g)^2))*
        (base*(12*(k+g))^2*(6*(k-G)))) := by
  field_simp [hL,hplus,hgap] <;> ring

private theorem clear_second_in (L F base k g G : ℂ) (hL : L ≠ 0) (hplus : k+g ≠ 0)
    (hgap : G-g ≠ 0) (hminus : k-G ≠ 0) :
    -(144*F*(6*G)*k*((12*g-12*k)*(12*g-12*k))*base) =
      L*(12*(G-g))^2*((-(F/L*G*k*(g-k)^2/((G-g)^2*(k+g)^2*(k-G))))*
        (base*(12*(k+g))^2*(6*(k-G)))) := by
  field_simp [hL,hplus,hgap,hminus] <;> ring

/-- The signs and both reflection multipliers, specialized only after
the exact polynomial certificates are bound to the actual rows. -/
theorem signed_endpoint_coefficients (second : Bool) (n : ℕ) (hn : 2 ≤ n)
    (k : ℂ) (hk : k ≠ 0) (ki : k.re = 0) :
    let p := reciprocalCoefficients second k n 0
    signedWeight p k = endpointOutgoing second k n ∧ signedWeight p (-k) = endpointIncoming second k n := by
  have hn' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have ellFactor : 2*(n : ℂ)-1 ≠ 0 := by
    exact_mod_cast (show (2*(n : ℝ)-1) ≠ 0 by linarith)
  have factor : (288 : ℂ)*(2*(n : ℂ)-1) ≠ 0 := mul_ne_zero (by norm_num) ellFactor
  have plus := gamma_add_frequency n hn k ki
  have plus' : k+gamma (n : ℂ) ≠ 0 := by simpa [add_comm] using plus
  have minus := frequency_sub_daughter n hn k ki
  have gap : daughterGamma (n : ℂ)-gamma (n : ℂ) ≠ 0 := by
    intro eq
    have contradiction := (gap_positive n hn).ne'
    exact contradiction (by simp [eq])
  have normGap : (288 : ℂ)*(2*(n : ℂ)-1)*(12*(daughterGamma (n : ℂ)-gamma (n : ℂ)))^2 ≠ 0 :=
    mul_ne_zero factor (pow_ne_zero 2 (mul_ne_zero (by norm_num) gap))
  cases second
  · obtain ⟨out,inc⟩ := signed_normalized false k n
    simp only [endpointIncoming,endpointOutgoing,Bool.false_eq_true,if_false]
    rw [out,inc]
    have zero : scalarValue k n (outgoingLead (mixtureNumerators false)) = 0 := by
      simpa [mixtureNumerators,c] using scalar_of_certificate k n first_outgoing_lead
    refine ⟨by rw [zero,zero_div],?_⟩
    apply (div_eq_iff (reciprocal_at_zero_nonzero false n hn k hk ki)).2
    apply mul_left_cancel₀ factor
    have cert := scalar_of_certificate k n first_incoming_lead
    simp only [factorTimes,scalar_mul,factor_den_value,firstIncoming,scalar_neg,scalar_constant,c,
      factor_num_value,square,w,scalar_frequency,Int.cast_ofNat] at cert
    change _ * scalarValue k n (incomingLead Case1.field) = _
    rw [cert]
    unfold reciprocalScalar
    rw [scalar_leading_denominator]
    simp only [mixtureMultiplier,Bool.false_eq_true,if_false,rationalAngularFactor]
    field_simp [ellFactor,plus',minus] <;> ring
  · obtain ⟨out,inc⟩ := signed_normalized true k n
    simp only [endpointIncoming,endpointOutgoing]
    rw [out,inc]
    constructor <;> apply (div_eq_iff (reciprocal_at_zero_nonzero true n hn k hk ki)).2 <;>
      apply mul_left_cancel₀ normGap
    · have cert := scalar_of_certificate k n second_outgoing_lead
      simp only [factorGapTimes,scalar_mul,factor_den_value,gap_value,square,secondOutgoing,
        scalar_sub,scalar_constant,c,w,scalar_frequency,daughter_value,gamma_value,
        factor_num_value,Int.cast_ofNat] at cert
      change _ * scalarValue k n (outgoingLead Case2.field) = _
      rw [pow_two (12*(daughterGamma (n : ℂ)-gamma (n : ℂ))),cert]
      unfold reciprocalScalar
      rw [scalar_leading_denominator]
      simp only [mixtureMultiplier,rationalAngularFactor]
      rw [← pow_two (12*(daughterGamma (n : ℂ)-gamma (n : ℂ)))]
      exact clear_second_out _ _ _ _ _ _ factor plus' gap
    · have cert := scalar_of_certificate k n second_incoming_lead
      simp only [factorGapTimes,scalar_mul,factor_den_value,gap_value,square,secondIncoming,
        scalar_neg,scalar_sub,scalar_constant,c,w,scalar_frequency,daughter_value,gamma_value,
        factor_num_value,Int.cast_ofNat] at cert
      change _ * scalarValue k n (incomingLead Case2.field) = _
      rw [pow_two (12*(daughterGamma (n : ℂ)-gamma (n : ℂ))),cert]
      unfold reciprocalScalar
      rw [scalar_leading_denominator]
      simp only [mixtureMultiplier,rationalAngularFactor]
      rw [← pow_two (12*(daughterGamma (n : ℂ)-gamma (n : ℂ)))]
      exact clear_second_in _ _ _ _ _ _ factor plus' gap minus

#print axioms reciprocal_at_zero_nonzero
#print axioms effective_row_equation
#print axioms mixed_reciprocal_divisible
#print axioms mixed_endpoint_zero
#print axioms signed_endpoint_coefficients

end
end SchwarzschildMixtures.OutgoingData
