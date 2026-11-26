import OddSourceEndpointChecks
import MixturePolynomialCertificate
import Mathlib.Algebra.Polynomial.Div

/-! Interpret the checked endpoint data of the three source numerators. -/
namespace SchwarzschildMixtures

open Polynomial NumeratorData

noncomputable section

set_option maxRecDepth 12000

private theorem terms_have_radius (g : CoefficientBand) (t : Term) (member : t ∈ g.terms) :
    t.radial = g.radial := by
  have digits (r k weight count i p q : ℕ) :
      ∀ t ∈ CoefficientBand.digits r k weight count i p q, t.radial = r := by
    induction count generalizing i p q with
    | zero => simp [CoefficientBand.digits]
    | succ n ih =>
      intro item member
      simp only [CoefficientBand.digits, List.mem_cons] at member
      rcases member with rfl | tail
      · rfl
      · exact ih _ _ _ item tail
  exact digits _ _ _ _ _ _ _ t member

private theorem poly_degree_bound (k ell : ℂ) (p : Poly) (d : ℕ)
    (bound : ∀ t ∈ p, t.radial ≤ d) : (p.value k ell).natDegree ≤ d := by
  induction p with
  | nil => simp [Poly.value]
  | cons t p ih =>
    have head : (Poly.termValue k ell t).natDegree ≤ d := by
      unfold Poly.termValue
      exact (natDegree_C_mul_le _ _).trans
        ((natDegree_X_pow t.radial).le.trans (bound t List.mem_cons_self))
    exact (natDegree_add_le ..).trans (max_le head (ih fun u hu => bound u (List.mem_cons_of_mem _ hu)))

private theorem expression_degree_bound (k ell : ℂ) (p : Expr) (d : ℕ)
    (check : OddCase.radialLabelsAtMost p d = true) : (p.value k ell).natDegree ≤ d := by
  cases p <;> try contradiction
  case bands rows =>
    have bands : ∀ g ∈ rows, g.radial ≤ d := fun g hg =>
      of_decide_eq_true (List.all_eq_true.mp check g hg)
    unfold Expr.value
    apply poly_degree_bound
    intro t ht
    obtain ⟨block, member, inBlock⟩ := List.mem_flatten.mp ht
    obtain ⟨g,hg,rfl⟩ := List.mem_map.mp member
    rw [terms_have_radius g t inBlock]
    exact bands g hg

private theorem expression_horizon_zero (k ell : ℂ) (p : Expr)
    (check : Expr.Check (Expr.atHorizon p) (Expr.constant 0)) : (p.value k ell).eval 2 = 0 := by
  have eq := Expr.value_eq_of_check _ _ check k ell
  exact C_injective (by simpa only [Expr.value_atHorizon, Expr.value_constant, Int.cast_zero] using eq)

private theorem divide_horizon (p : ℂ[X]) (d : ℕ) (degree : p.natDegree ≤ d)
    (zero : p.eval 2 = 0) :
    ∃ q : ℂ[X], p = ((X : ℂ[X])-C 2)*q ∧ q.natDegree ≤ d-1 ∧ q.eval 2 = p.derivative.eval 2 := by
  obtain ⟨q,eq⟩ := (dvd_iff_isRoot.mpr zero : X-C (2:ℂ) ∣ p)
  change p = ((X : ℂ[X])-C 2)*q at eq
  refine ⟨q,eq,?_,?_⟩
  · by_cases hq : q = 0
    · simp [hq]
    have hs : ((X : ℂ[X])-C 2) ≠ 0 := X_sub_C_ne_zero 2
    have linear := natDegree_X_sub_C (2 : ℂ)
    rw [eq,natDegree_mul hs hq,linear] at degree
    omega
  · rw [eq,derivative_mul]
    simp


theorem odd_source_numerators_at_endpoints (k ell : ℂ) :
    ∃ a b c : ℂ[X],
      Expr.value k ell OddCase.sourceA = (X-C 2)*a ∧
      Expr.value k ell OddCase.sourceB = (X-C 2)*b ∧
      Expr.value k ell OddCase.sourceC = (X-C 2)*c ∧
      a.natDegree ≤ 23 ∧ b.natDegree ≤ 21 ∧ c.natDegree ≤ 19 ∧
      a.eval 2-4*k*b.eval 2+16*k^2*c.eval 2 = 0 := by
  obtain ⟨a,ea,da,ha⟩ := divide_horizon _ 24
    (expression_degree_bound k ell _ _ OddCase.sourceA_degree)
    (expression_horizon_zero k ell _ OddCase.sourceA_horizon)
  obtain ⟨b,eb,db,hb⟩ := divide_horizon _ 22
    (expression_degree_bound k ell _ _ OddCase.sourceB_degree)
    (expression_horizon_zero k ell _ OddCase.sourceB_horizon)
  obtain ⟨c,ec,dc,hc⟩ := divide_horizon _ 20
    (expression_degree_bound k ell _ _ OddCase.sourceC_degree)
    (expression_horizon_zero k ell _ OddCase.sourceC_horizon)
  refine ⟨a,b,c,ea,eb,ec,da,db,dc,?_⟩
  rw [ha,hb,hc]
  have eq := congrArg (Polynomial.eval (0 : ℂ))
    (Expr.value_eq_of_check _ _ OddCase.source_ingoing_slope_horizon k ell)
  simpa [horizonData,Expr.value_single,Expr.value_constant] using eq

#print axioms odd_source_numerators_at_endpoints

end
end SchwarzschildMixtures
