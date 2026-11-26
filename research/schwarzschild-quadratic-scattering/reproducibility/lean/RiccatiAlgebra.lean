import RationalRowOperator

/-! A quadratic relation for the logarithmic derivative gives a rational
solution or a rational mean and a nonsquare discriminant. -/
namespace SchwarzschildLaurent

noncomputable section

local notation "ℂᵣ" => RatFunc ℂ
local notation "R" => (RatFunc.X : ℂᵣ)
local notation "Cᵣ" => (RatFunc.C : ℂ →+* ℂᵣ)
local notation "δ" => rationalDerivative

def tortoiseDerivative (u : ℂᵣ) : ℂᵣ := radialFactor * δ u

local notation "D" => tortoiseDerivative

theorem tortoise_add (x y : ℂᵣ) : D (x+y) = D x + D y := by
  simp [tortoiseDerivative, rationalDerivative_add, mul_add]

theorem tortoise_sub (x y : ℂᵣ) : D (x-y) = D x - D y := by
  simp [tortoiseDerivative, rationalDerivative_sub, mul_sub]

theorem tortoise_mul (x y : ℂᵣ) : D (x*y) = D x*y + x*D y := by
  simp [tortoiseDerivative, rationalDerivative_mul]
  ring

theorem tortoise_sq (x : ℂᵣ) : D (x^2) = 2*x*D x := by
  rw [pow_two, tortoise_mul]
  ring

@[simp] theorem tortoise_const (c : ℂ) : D (Cᵣ c) = 0 := by simp [tortoiseDerivative]
@[simp] theorem tortoise_zero : D 0 = 0 := by simp [tortoiseDerivative]
@[simp] theorem tortoise_one : D 1 = 0 := by simp [tortoiseDerivative]

theorem tortoise_div_constant (x : ℂᵣ) (c : ℂ) : D (x/Cᵣ c) = D x/Cᵣ c := by
  rw [div_eq_mul_inv, ← map_inv₀, tortoise_mul, tortoise_const, mul_zero, add_zero, map_inv₀, ← div_eq_mul_inv]

theorem tortoise_half (x : ℂᵣ) : D (x/2) = D x/2 := by
  simpa only [map_ofNat] using tortoise_div_constant x 2

def parentTerm (h k : ℂ) : ℂᵣ := Cᵣ (k^2) + oddPotential h

def RationalRiccati (h k : ℂ) (u : ℂᵣ) : Prop := D u + u^2 = parentTerm h k

structure QuadraticRiccati (h k : ℂ) (a b : ℂᵣ) : Prop where
  mean : D a + a^2 + b = parentTerm h k
  discriminant : D b = -4*a*b
  nonsquare : ¬ ∃ v : ℂᵣ, b = v^2

/-- A differential field containing the radial rational functions. Its
differentiation extends the tortoise-coordinate derivative of the paper. -/
structure RadialDifferentialField (L : Type*) [Field L] where
  embed : ℂᵣ →+* L
  deriv : L →+ L
  product : ∀ x y, deriv (x*y) = deriv x*y + x*deriv y
  compatible : ∀ u, deriv (embed u) = embed (D u)

namespace RadialDifferentialField

variable {L : Type*} [Field L] (E : RadialDifferentialField L)

theorem quotient (u v : L) (hv : v ≠ 0) :
    E.deriv (u/v) = (E.deriv u*v-u*E.deriv v)/v^2 := by
  have h := E.product (u/v) v
  rw [div_mul_cancel₀ _ hv] at h
  apply (eq_div_iff (pow_ne_zero 2 hv)).mpr
  have h' := div_mul_cancel₀ u hv
  linear_combination -v*h - E.deriv v*h'

theorem square (u : L) : E.deriv (u^2) = 2*u*E.deriv u := by
  rw [pow_two, E.product]
  ring

theorem parent_log_derivative (h k : ℂ) (J : L) (hn : J ≠ 0)
    (he : E.deriv (E.deriv J) = E.embed (parentTerm h k)*J) :
    E.deriv (E.deriv J/J) + (E.deriv J/J)^2 = E.embed (parentTerm h k) := by
  rw [E.quotient _ _ hn, he]
  field_simp [hn]
  ring

private theorem affine_coefficient {u : L} (hu : ∀ t, E.embed t ≠ u)
    (a b : ℂᵣ) (eq : E.embed a*u + E.embed b = 0) : a = 0 ∧ b = 0 := by
  by_cases ha : a = 0
  · refine ⟨ha, E.embed.injective ?_⟩
    simpa [ha] using eq
  have hae : E.embed a ≠ 0 := (map_ne_zero E.embed).mpr ha
  exfalso
  apply hu (-b/a)
  rw [map_div₀, map_neg, div_eq_iff hae]
  linear_combination -eq

private theorem trace_equations {h k : ℂ} {u : L} {s p : ℂᵣ}
    (hu : ∀ t, E.embed t ≠ u) (eq : E.deriv u + u^2 = E.embed (parentTerm h k))
    (poly : u^2 = E.embed s*u-E.embed p) :
    D s = 2*parentTerm h k-s^2+2*p ∧ D p = s*(parentTerm h k-p) := by
  have d := congrArg E.deriv poly
  have du : E.deriv u = E.embed (parentTerm h k)-u^2 := eq_sub_of_add_eq eq
  change E.deriv (u^2) = E.deriv (E.embed s*u-E.embed p) at d
  rw [E.square, map_sub, E.product, E.compatible, E.compatible, du, poly] at d
  have aff : E.embed (2*parentTerm h k-s^2+2*p-D s)*u +
      E.embed (s*p-s*parentTerm h k + D p) = 0 := by
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
    linear_combination d + 2 * E.embed s * poly
  obtain ⟨a,b⟩ := E.affine_coefficient hu _ _ aff
  constructor
  · linear_combination -a
  · linear_combination b

private theorem quadratic_of_monic {h k : ℂ} {u : L} {s p : ℂᵣ}
    (hu : ∀ t, E.embed t ≠ u) (eq : E.deriv u + u^2 = E.embed (parentTerm h k))
    (poly : u^2 = E.embed s*u-E.embed p) :
    ∃ a b : ℂᵣ, QuadraticRiccati h k a b := by
  obtain ⟨hs,hp⟩ := E.trace_equations hu eq poly
  let a := s/2
  let b := a^2-p
  have twice : 2*a=s := by dsimp [a]; ring
  refine ⟨a,b,?_,?_,?_⟩
  · dsimp [a,b]
    rw [tortoise_half]
    linear_combination hs/2
  · change D (a^2-p) = -4*a*b
    rw [tortoise_sub,tortoise_sq]
    dsimp only [a,b]
    rw [tortoise_half]
    linear_combination (s/2)*hs-hp
  · rintro ⟨w,hw⟩
    have ht : 2*E.embed a=E.embed s := by simpa only [map_mul,map_ofNat] using congrArg E.embed twice
    have hb : E.embed b = E.embed a^2-E.embed p := by simp only [b,map_sub,map_pow]
    have hw' : E.embed b=(E.embed w)^2 := by simpa only [map_pow] using congrArg E.embed hw
    have sq : (u-E.embed a)^2 = (E.embed w)^2 := by
      linear_combination poly-ht*u-hb+hw'
    have factors : (u-E.embed a-E.embed w)*(u-E.embed a+E.embed w)=0 := by linear_combination sq
    rcases mul_eq_zero.mp factors with hp | hm
    · apply hu (a+w)
      rw [map_add]
      linear_combination -hp
    · apply hu (a-w)
      rw [map_sub]
      linear_combination -hm

/-- Every nontrivial relation of degree at most two yields one of the two
rational alternatives used in the independence proof. -/
theorem riccati_alternatives {h k : ℂ} {u : L} (eq : E.deriv u + u^2 = E.embed (parentTerm h k))
    (c b a : ℂᵣ) (nontrivial : (c,b,a) ≠ (0 : Row ℂᵣ))
    (relation : E.embed a*u^2+E.embed b*u+E.embed c = 0) :
    (∃ r, RationalRiccati h k r) ∨ (∃ v w, QuadraticRiccati h k v w) := by
  by_cases hr : ∃ t, E.embed t = u
  · obtain ⟨r,rfl⟩ := hr
    left
    refine ⟨r,E.embed.injective ?_⟩
    simpa only [RationalRiccati,map_add,map_pow,E.compatible] using eq
  have hu : ∀ r, E.embed r ≠ u := fun r er => hr ⟨r,er⟩
  right
  have ha : a ≠ 0 := by
    intro hz
    have affine : E.embed b*u+E.embed c=0 := by simpa [hz] using relation
    obtain ⟨hb,hc⟩ := E.affine_coefficient hu b c affine
    exact nontrivial (by simp [hz,hb,hc])
  have hae : E.embed a ≠ 0 := (map_ne_zero E.embed).mpr ha
  have poly : u^2 = E.embed (-b/a)*u - E.embed (c/a) := by
    simp only [map_div₀,map_neg]
    field_simp [hae]
    linear_combination relation
  exact E.quadratic_of_monic hu eq poly

end RadialDifferentialField

#print axioms RadialDifferentialField.parent_log_derivative
#print axioms RadialDifferentialField.riccati_alternatives

end

end SchwarzschildLaurent
