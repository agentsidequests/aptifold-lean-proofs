import RiccatiRational
import RiccatiSquare

/-! Independence and the row operator for a single fixed nonzero parent. -/
namespace SchwarzschildLaurent

noncomputable section

local notation "ℂᵣ" => RatFunc ℂ
local notation "R" => (RatFunc.X : ℂᵣ)
local notation "Cᵣ" => (RatFunc.C : ℂ →+* ℂᵣ)

namespace RadialDifferentialField

variable {L : Type*} [Field L] (E : RadialDifferentialField L)

def parentJet (J : L) : L := E.embed (R^2)*E.deriv J

def evaluateRow (J : L) (p : Row ℂᵣ) : L :=
  E.embed p.1 * J^2 + E.embed p.2.1 * J * E.parentJet J + E.embed p.2.2 * (E.parentJet J)^2

theorem evaluateRow_zero (J : L) : E.evaluateRow J 0 = 0 := by
  change E.embed 0 * J^2 + E.embed 0 * J * E.parentJet J + E.embed 0 * (E.parentJet J)^2 = 0
  simp

theorem evaluateRow_sub (J : L) (p q : Row ℂᵣ) :
    E.evaluateRow J (minus p q) = E.evaluateRow J p-E.evaluateRow J q := by
  simp only [evaluateRow,minus,map_sub]
  ring

theorem evaluateRow_scale (J : L) (a : ℂᵣ) (p : Row ℂᵣ) :
    E.evaluateRow J (scale a p) = E.embed a*E.evaluateRow J p := by
  simp only [evaluateRow,scale,map_mul]
  ring

/-- The three quadratic products of a fixed parent are independent over the
rational functions for physical angular labels and frequencies. -/
theorem fixed_parent_independence (n : ℕ) (hn : 2≤n) (k : ℂ) (hk : k≠0) (ki : k.re=0)
    (J : L) (hJ : J≠0)
    (parent : E.deriv (E.deriv J) = E.embed (parentTerm ((n:ℂ)*((n:ℂ)+1)) k)*J)
    (p : Row ℂᵣ) (relation : E.evaluateRow J p = 0) : p=0 := by
  let u := E.deriv J/J
  have riccati := E.parent_log_derivative ((n:ℂ)*((n:ℂ)+1)) k J hJ parent
  change E.deriv u+u^2=E.embed _ at riccati
  let a := p.2.2*R^4
  let b := p.2.1*R^2
  have poly : E.embed a*u^2+E.embed b*u+E.embed p.1=0 := by
    simp only [u,a,b,map_mul,map_pow]
    simp only [evaluateRow,parentJet,map_pow] at relation
    field_simp [hJ]
    linear_combination relation
  by_contra hp
  have nontrivial : (p.1,b,a) ≠ (0 : Row ℂᵣ) := by
    intro zero
    have e0 : p.1=0 := congrArg Prod.fst zero
    have e1 : p.2.1*R^2=0 := congrArg (fun v => v.2.1) zero
    have e2 : p.2.2*R^4=0 := congrArg (fun v => v.2.2) zero
    apply hp
    exact Prod.ext e0 (Prod.ext ((mul_eq_zero.mp e1).resolve_right (pow_ne_zero 2 RatFunc.X_ne_zero))
      ((mul_eq_zero.mp e2).resolve_right (pow_ne_zero 4 RatFunc.X_ne_zero)))
  rcases E.riccati_alternatives riccati p.1 b a nontrivial poly with rational | quadratic
  · exact rational_riccati_no_solution n hn k hk ki rational
  · exact quadratic_riccati_no_solution _ k hk ki quadratic

theorem evaluateRow_injective (n : ℕ) (hn : 2≤n) (k : ℂ) (hk : k≠0) (ki : k.re=0)
    (J : L) (hJ : J≠0)
    (parent : E.deriv (E.deriv J) = E.embed (parentTerm ((n:ℂ)*((n:ℂ)+1)) k)*J) :
    Function.Injective (E.evaluateRow J) := by
  intro p q eq
  have linear : E.evaluateRow J (minus p q) = 0 := by rw [E.evaluateRow_sub,eq,sub_self]
  have ident := E.fixed_parent_independence n hn k hk ki J hJ parent (minus p q) linear
  exact Prod.ext (sub_eq_zero.mp (congrArg Prod.fst ident))
    (Prod.ext (sub_eq_zero.mp (congrArg (fun v => v.2.1) ident))
      (sub_eq_zero.mp (congrArg (fun v => v.2.2) ident)))

private theorem deriv_of_parent (J : L) : E.deriv J = E.embed (1/R^2)*E.parentJet J := by
  have r : E.embed R≠0 := (map_ne_zero E.embed).mpr RatFunc.X_ne_zero
  simp only [parentJet,map_div₀,map_one,map_pow]
  field_simp [r]

private theorem deriv_parentJet (h k : ℂ) (J : L)
    (he : E.deriv (E.deriv J)=E.embed (parentTerm h k)*J) :
    E.deriv (E.parentJet J) = E.embed (R^2*parentTerm h k)*J
      + E.embed (2*radialFactor/R)*E.parentJet J := by
  have e : tortoiseDerivative (R^2) = (2*radialFactor/R)*R^2 := by
    rw [tortoiseDerivative,rationalDerivative_pow,rationalDerivative_radius]
    norm_num
    field_simp [RatFunc.X_ne_zero]
  conv_lhs => rw [parentJet,E.product,E.compatible,he,e]
  simp only [map_mul,parentJet]
  ring

theorem evaluateRow_step (h k : ℂ) (J : L)
    (he : E.deriv (E.deriv J)=E.embed (parentTerm h k)*J) (p : Row ℂᵣ) :
    E.deriv (E.evaluateRow J p) = E.evaluateRow J (rationalStep h k p) := by
  rw [rationalStep_physical]
  rcases p with ⟨p,q,s⟩
  have dj := E.deriv_of_parent J
  have dz := E.deriv_parentJet h k J he
  simp only [evaluateRow,map_add,E.product,E.square,E.compatible,
    dj,dz, plus, scale, jet, rationalRowDerivative,mapRow,
    tortoiseDerivative,parentTerm,map_mul,map_ofNat]
  ring

/-- Acting on the scalar value of a row gives the value of the rational
daughter operator on that row. -/
theorem evaluateRow_operator (h hD k : ℂ) (J : L)
    (he : E.deriv (E.deriv J)=E.embed (parentTerm h k)*J) (p : Row ℂᵣ) :
    E.deriv (E.deriv (E.evaluateRow J p)) -
      E.embed (Cᵣ (4*k^2)+oddPotential hD)*E.evaluateRow J p =
      E.evaluateRow J (rationalOperator h hD k p) := by
  rw [rationalOperator,E.evaluateRow_sub,E.evaluateRow_scale,
    E.evaluateRow_step h k J he,E.evaluateRow_step h k J he]

end RadialDifferentialField

#print axioms RadialDifferentialField.fixed_parent_independence
#print axioms RadialDifferentialField.evaluateRow_injective
#print axioms RadialDifferentialField.evaluateRow_operator

end

end SchwarzschildLaurent
