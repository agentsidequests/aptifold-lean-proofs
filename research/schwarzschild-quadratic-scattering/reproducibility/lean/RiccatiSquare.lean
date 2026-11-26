import RiccatiDiscriminant

/-! Equal numerator and denominator degrees and even nonzero-point orders
force the discriminant to be a square. -/
namespace SchwarzschildLaurent

open Polynomial

noncomputable section

local notation "ℂᵣ" => RatFunc ℂ
local notation "ι" => (algebraMap ℂ[X] ℂᵣ)
local notation "Cᵣ" => (RatFunc.C : ℂ →+* ℂᵣ)

private theorem polynomial_factors (p : ℂ[X]) (hp : p≠0) (s : Finset ℂ)
    (contains : p.roots.toFinset ⊆ s) :
    p = C p.leadingCoeff * ∏ a ∈ s, localCoordinate a ^ rootMultiplicity a p := by
  classical
  calc
    _ = C p.leadingCoeff * (p.roots.map (fun a => X-C a)).prod := (IsAlgClosed.splits p).eq_prod_roots
    _ = C p.leadingCoeff * ∏ a ∈ p.roots.toFinset, localCoordinate a ^ rootMultiplicity a p := by
      rw [Finset.prod_multiset_map_count]
      simp only [count_roots,localCoordinate]
    _ = _ := by
      congr 1
      apply Finset.prod_subset contains
      intro a _ notroot
      have h : ¬IsRoot p a := fun e => notroot (Multiset.mem_toFinset.mpr ((mem_roots hp).mpr e))
      rw [rootMultiplicity_eq_zero h,pow_zero]

private theorem degree_from_factors (p : ℂ[X]) (hp : p≠0) (s : Finset ℂ)
    (contains : p.roots.toFinset ⊆ s) :
    p.natDegree = ∑ a ∈ s, rootMultiplicity a p := by
  let f : ℂ → ℂ[X] := fun a => localCoordinate a ^ rootMultiplicity a p
  have nf (a : ℂ) : f a≠0 := pow_ne_zero _ (localCoordinate_ne_zero a)
  have d := congrArg natDegree (polynomial_factors p hp s contains)
  change p.natDegree = (C p.leadingCoeff * ∏ a∈s,f a).natDegree at d
  rw [natDegree_C_mul (leadingCoeff_ne_zero.mpr hp), natDegree_prod s f (fun a _ => nf a)] at d
  simpa only [f,natDegree_pow,localCoordinate,natDegree_X_sub_C,one_mul,mul_one] using d

private theorem rational_factors (b : ℂᵣ) (hb : b≠0) (s : Finset ℂ)
    (num : b.num.roots.toFinset ⊆ s) (denom : b.denom.roots.toFinset ⊆ s) :
    b=Cᵣ b.num.leadingCoeff * ∏ a∈s,(coordinate a)^(finiteOrder b a) := by
  have p := polynomial_factors b.num (RatFunc.num_ne_zero hb) s num
  have q := polynomial_factors b.denom b.denom_ne_zero s denom
  rw [b.monic_denom.leadingCoeff,C_1,one_mul] at q
  conv_lhs => rw [← RatFunc.num_div_denom b,p,q]
  simp only [map_mul,map_prod,map_pow,RatFunc.algebraMap_C,coordinate]
  rw [mul_div_assoc,← Finset.prod_div_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro a _
  exact (zpow_natCast_sub_natCast₀ (coordinate_ne_zero a)
    (rootMultiplicity a b.num) (rootMultiplicity a b.denom)).symm

private theorem half_exponents {b : ℂᵣ} {s : Finset ℂ} (zero : (0:ℂ)∈s)
    (total : ∑ x∈s,finiteOrder b x = 0)
    (off : ∀ x : ℂ, x≠0 → finiteOrder b x = 0 ∨ finiteOrder b x = -2) :
    ∀ x : ℂ, finiteOrder b x = finiteOrder b x / 2 + finiteOrder b x / 2 := by
  classical
  have nonzero (x : ℂ) (h : x≠0) : finiteOrder b x = finiteOrder b x/2+finiteOrder b x/2 := by
    rcases off x h with e | e <;> rw [e] <;> decide
  have rest : (∑ x ∈ s.erase 0, finiteOrder b x) =
      (∑ x ∈ s.erase 0, finiteOrder b x/2) + (∑ x ∈ s.erase 0, finiteOrder b x/2) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun x hm => nonzero x (Finset.mem_erase.mp hm).1)
  have hz := Finset.sum_erase_add s (fun x => finiteOrder b x) zero
  rw [total,rest] at hz
  intro x
  by_cases hx : x=0
  · subst x
    omega
  · exact nonzero x hx

/-- Parity of the finite divisor, including at the origin, follows from
the degree equality at infinity. -/
theorem discriminant_is_square {h k : ℂ} {a b : ℂᵣ}
    (q : QuadraticRiccati h k a b) (hk : k≠0) (ki : k.re=0) :
    ∃ w : ℂᵣ,b=w^2 := by
  classical
  let s := insert 0 (b.num.roots.toFinset ∪ b.denom.roots.toFinset)
  have pn : b.num.roots.toFinset ⊆ s := fun x hx => Finset.mem_insert_of_mem (Finset.mem_union_left _ hx)
  have dn : b.denom.roots.toFinset ⊆ s := fun x hx => Finset.mem_insert_of_mem (Finset.mem_union_right _ hx)
  have pd := degree_from_factors b.num (RatFunc.num_ne_zero q.nonzero) s pn
  have dd := degree_from_factors b.denom b.denom_ne_zero s dn
  have equal := discriminant_equal_degrees q hk
  have total : (∑ x∈s, finiteOrder b x) = 0 := by
    simp only [finiteOrder,Finset.sum_sub_distrib,← Nat.cast_sum,← pd,← dd,equal,sub_self]
  have off (x : ℂ) (hx : x≠0) : finiteOrder b x=0 ∨ finiteOrder b x = -2 := by
    by_cases h2 : x=2
    · subst x
      exact Or.inl (discriminant_horizon_order q hk ki)
    · exact discriminant_ordinary_order q hx h2
  have half := half_exponents (Finset.mem_insert_self (a := 0) _) total off
  obtain ⟨c,hc⟩ := IsAlgClosed.exists_pow_nat_eq b.num.leadingCoeff (by decide : 0 < (2:ℕ))
  refine ⟨Cᵣ c * ∏ x∈s,(coordinate x)^(finiteOrder b x/2),?_⟩
  conv_lhs => rw [rational_factors b q.nonzero s pn dn]
  rw [mul_pow, ← map_pow, hc, ← Finset.prod_pow]
  congr 1
  apply Finset.prod_congr rfl
  intro x _
  rw [pow_two,← zpow_add₀ (coordinate_ne_zero x),← half x]

theorem quadratic_riccati_no_solution (h k : ℂ) (hk : k≠0) (ki : k.re=0) :
    ¬ ∃ a b, QuadraticRiccati h k a b := by
  rintro ⟨a,b,q⟩
  exact q.nonsquare (discriminant_is_square q hk ki)

#print axioms discriminant_is_square
#print axioms quadratic_riccati_no_solution

end

end SchwarzschildLaurent
