import ScatteringSoftNonzero

/-! Operations on the first two expansion coefficients at positive real
frequency, with the expansion variable k = i omega. -/
namespace SchwarzschildMixtures.Strain

open Filter Set
open scoped Topology

noncomputable section

def quadraticQuotient (f : ℝ → ℂ) (a b : ℂ) (w : ℝ) : ℂ :=
  (f w-a-b*frequencyParameter w)/(frequencyParameter w)^2

private theorem frequency_nonzero {w : ℝ} (h : 0 < w) : frequencyParameter w ≠ 0 :=
  mul_ne_zero (by exact_mod_cast h.ne') Complex.I_ne_zero

private theorem first_quotient_limit {f : ℝ → ℂ} {a b c : ℂ}
    (h : Tendsto (quadraticQuotient f a b) (𝓝[>] (0:ℝ)) (𝓝 c)) :
    Tendsto (fun w => (f w-a)/frequencyParameter w) (𝓝[>] (0:ℝ)) (𝓝 b) := by
  have t := (frequency_parameter_limit.mul h).add_const b
  simp only [zero_mul,zero_add] at t
  apply t.congr'
  filter_upwards [self_mem_nhdsWithin] with w hw
  unfold quadraticQuotient
  field_simp [frequency_nonzero (show 0 < w from hw)]
  ring

theorem value_limit_from_quadratic_quotient {f : ℝ → ℂ} {a b c : ℂ}
    (h : Tendsto (quadraticQuotient f a b) (𝓝[>] (0:ℝ)) (𝓝 c)) :
    Tendsto f (𝓝[>] (0:ℝ)) (𝓝 a) := by
  have t := (frequency_parameter_limit.mul (first_quotient_limit h)).add_const a
  simp only [zero_mul,zero_add] at t
  apply t.congr'
  filter_upwards [self_mem_nhdsWithin] with w hw
  rw [mul_div_cancel₀ _ (frequency_nonzero (show 0 < w from hw))]
  ring

theorem quadratic_quotient_product {f g : ℝ → ℂ} {a b c A B C : ℂ}
    (h : Tendsto (quadraticQuotient f a b) (𝓝[>] (0:ℝ)) (𝓝 c))
    (h' : Tendsto (quadraticQuotient g A B) (𝓝[>] (0:ℝ)) (𝓝 C)) :
    Tendsto (quadraticQuotient (fun w => f w*g w) (a*A) (b*A+a*B))
      (𝓝[>] (0:ℝ)) (𝓝 (c*A+b*B+a*C)) := by
  have t := ((h.mul (value_limit_from_quadratic_quotient h')).add
    ((first_quotient_limit h').const_mul b)).add (h'.const_mul a)
  apply t.congr'
  filter_upwards [self_mem_nhdsWithin] with w hw
  unfold quadraticQuotient
  dsimp only
  field_simp [frequency_nonzero (show 0 < w from hw)]
  ring

def evenEnvelopeWeight (g G : ℂ) (w : ℝ) : ℂ :=
  (frequencyParameter w-g^2/G)/(frequencyParameter w+g)^2

def oddEnvelopeWeight (G : ℂ) (w : ℝ) : ℂ :=
  1/(frequencyParameter w-G)

theorem even_envelope_weight_expansion (g G : ℂ) (g0 : g ≠ 0) (G0 : G ≠ 0) :
    Tendsto (quadraticQuotient (evenEnvelopeWeight g G) (-1/G) (1/g^2+2/(g*G)))
      (𝓝[>] (0:ℝ)) (𝓝 ((-2/g-3/G)/g^2)) := by
  let b := 1/g^2+2/(g*G)
  have numerator := (frequency_parameter_limit.const_mul (-b)).const_add (-2/g-3/G)
  have denom := (frequency_parameter_limit.add_const g).pow 2
  simp only [mul_zero,add_zero,zero_add] at numerator denom
  have t := numerator.div denom (pow_ne_zero _ g0)
  have good := (frequency_parameter_limit.add_const g).eventually
    (eventually_ne_nhds (show (0:ℂ)+g ≠ 0 by simpa only [zero_add] using g0))
  apply t.congr'
  filter_upwards [self_mem_nhdsWithin,good] with w hw plus
  have plus0 : frequencyParameter w+g ≠ 0 := plus
  unfold quadraticQuotient evenEnvelopeWeight
  simp only [Pi.div_apply,b]
  field_simp [g0,G0,frequency_nonzero (show 0 < w from hw),plus0]
  ring

theorem odd_envelope_weight_expansion (G : ℂ) (G0 : G ≠ 0) :
    Tendsto (quadraticQuotient (oddEnvelopeWeight G) (-1/G) (-1/G^2))
      (𝓝[>] (0:ℝ)) (𝓝 (-1/G^3)) := by
  have denom := (frequency_parameter_limit.sub_const G).const_mul (G^2)
  simp only [zero_sub] at denom
  have t := (tendsto_const_nhds (x := (1:ℂ))).div denom
    (mul_ne_zero (pow_ne_zero _ G0) (neg_ne_zero.mpr G0))
  have constant : (1:ℂ)/(G^2*(-G)) = -1/G^3 := by field_simp [G0]
  rw [constant] at t
  have good := (frequency_parameter_limit.sub_const G).eventually
    (eventually_ne_nhds (show (0:ℂ)-G ≠ 0 by rw [zero_sub]; exact neg_ne_zero.mpr G0))
  apply t.congr'
  filter_upwards [self_mem_nhdsWithin,good] with w hw minus
  have minus0 : frequencyParameter w-G ≠ 0 := minus
  unfold quadraticQuotient oddEnvelopeWeight
  simp only [Pi.div_apply]
  field_simp [G0,frequency_nonzero (show 0 < w from hw),minus0]
  ring

#print axioms value_limit_from_quadratic_quotient
#print axioms quadratic_quotient_product
#print axioms even_envelope_weight_expansion
#print axioms odd_envelope_weight_expansion

end
end SchwarzschildMixtures.Strain
