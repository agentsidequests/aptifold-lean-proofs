import LaurentEmbedding
import MatrixCertificate

/-! Interpret the archived source coefficient table and check its radial orders. -/
namespace SchwarzschildLaurent

open Polynomial

noncomputable section

local notation "ℂᵣ" => RatFunc ℂ
local notation "ι" => (algebraMap ℂ[X] ℂᵣ)
local notation "R" => (RatFunc.X : ℂᵣ)
local notation "Cᵣ" => (RatFunc.C : ℂ →+* ℂᵣ)

def rowLabel (i : ℕ) : ℕ × ℤ := (SchwarzschildMatrix.rowLabels[i]?).getD (0, 0)

private theorem rowLabel_count : SchwarzschildMatrix.rowLabels.length = 41 := by decide +kernel

private theorem rowLabel_nodup : SchwarzschildMatrix.rowLabels.Nodup := by decide +kernel

theorem rowLabel_eq {i : ℕ} (hi : i < 41) : rowLabel i = SchwarzschildMatrix.rowLabels[i]'(by rw [rowLabel_count]; exact hi) := by
  have _ := rowLabel_count
  simp [rowLabel, List.getElem?_eq_getElem (by omega : i < SchwarzschildMatrix.rowLabels.length)]

private theorem rowLabel_injective {i j : ℕ} (hi : i < 41) (hj : j < 41)
    (h : rowLabel i = rowLabel j) : i = j := by
  exact rowLabel_nodup.getElem_inj_iff.mp ((rowLabel_eq hi).symm.trans (h.trans (rowLabel_eq hj)))

theorem rowLabel_component (i : ℕ) (hi : i < 41) : (rowLabel i).1 ≤ 2 := by
  have checked : SchwarzschildMatrix.rows.all (fun s => decide ((rowLabel s).1 ≤ 2)) = true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp checked i (by simpa [SchwarzschildMatrix.rows] using hi))

private theorem source_radial_bounds (i : ℕ) (hi : i < 41) :
    SchwarzschildMatrix.termsAt SchwarzschildMatrix.clearedSource i = [] ∨
      (-6 ≤ (rowLabel i).2 ∧ (rowLabel i).2 + 2*((rowLabel i).1 : ℤ) ≤ 3) := by
  have checked : SchwarzschildMatrix.rows.all (fun s => decide (SchwarzschildMatrix.termsAt SchwarzschildMatrix.clearedSource s = [] ∨
      (-6 ≤ (rowLabel s).2 ∧ (rowLabel s).2 + 2*((rowLabel s).1 : ℤ) ≤ 3))) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp checked i (by simpa [SchwarzschildMatrix.rows] using hi))

def archivedWeight (k ell : ℂ) (j i : ℕ) : ℂ :=
  if (rowLabel i).1 = j then SchwarzschildMatrix.sourceEntry k ell i else 0

def archivedComponent (k ell : ℂ) (j : ℕ) : LPoly :=
  ∑ i ∈ Finset.range 41, AddMonoidAlgebra.single (rowLabel i).2 (archivedWeight k ell j i)

def archivedLaurentSource (k ell : ℂ) : Row LPoly :=
  (archivedComponent k ell 0, archivedComponent k ell 1, archivedComponent k ell 2)

/-- The odd pole-subtracted source in the rescaled quadratic jet basis. -/
def archivedSource (k ell : ℂ) : Row ℂᵣ :=
  mapRow laurentToRat (archivedLaurentSource k ell)

private theorem archivedWeight_zero (k ell : ℂ) (j i : ℕ) (hz : SchwarzschildMatrix.termsAt SchwarzschildMatrix.clearedSource i = []) :
    archivedWeight k ell j i = 0 := by
  simp [archivedWeight, SchwarzschildMatrix.sourceEntry, SchwarzschildMatrix.clearedSourceEntry, SchwarzschildMatrix.total, hz]

theorem archivedComponent_coeff (k ell : ℂ) (i : ℕ) (hi : i < 41) :
    (archivedComponent k ell (rowLabel i).1).coeff (rowLabel i).2 = SchwarzschildMatrix.sourceEntry k ell i := by
  rw [archivedComponent, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single i]
  · simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same, archivedWeight, if_true]
  · intro s hs hne
    have hs' : s < 41 := Finset.mem_range.mp hs
    change (AddMonoidAlgebra.single (rowLabel s).2 (archivedWeight k ell (rowLabel i).1 s)).coeff (rowLabel i).2 = 0
    by_cases hcomponent : (rowLabel s).1 = (rowLabel i).1
    · have hradius : (rowLabel s).2 ≠ (rowLabel i).2 :=
        fun h => hne (rowLabel_injective hs' hi (Prod.ext hcomponent h))
      simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, if_neg hradius]
    · simp [archivedWeight, hcomponent]
  · simp [hi]

private def sourceNumerator (k ell : ℂ) (j : ℕ) : ℂ[X] :=
  ∑ i ∈ Finset.range 41, monomial ((rowLabel i).2+6).toNat (archivedWeight k ell j i)

private theorem archivedComponent_finite (k ell : ℂ) (j : ℕ) :
    laurentToRat (archivedComponent k ell j) = ι (sourceNumerator k ell j) / ι (X^6) := by
  simp only [archivedComponent, sourceNumerator, map_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  rcases source_radial_bounds i (Finset.mem_range.mp hi) with empty | bounds
  · simp [archivedWeight_zero k ell j i empty]
  · exact laurentToRat_monomial_fraction (rowLabel i).2 _ 6 (by omega)

private def infinityNumerator (k ell : ℂ) (j : ℕ) : ℂ[X] :=
  ∑ i ∈ Finset.range 41,
    monomial (3 - ((rowLabel i).2 + 2*(j:ℤ))).toNat (archivedWeight k ell j i)

private theorem archivedComponent_infinity (k ell : ℂ) (j : ℕ) :
    reciprocalHom (laurentToRat (archivedComponent k ell j) * R^(2*j)) =
      ι (infinityNumerator k ell j) / ι (X^3) := by
  simp only [archivedComponent, infinityNumerator, map_sum, Finset.sum_mul, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  rcases source_radial_bounds i (Finset.mem_range.mp hi) with empty | bounds
  · simp [archivedWeight_zero k ell j i empty]
  by_cases hj : (rowLabel i).1 = j
  · have hz : -((rowLabel i).2 + 2*(j:ℤ)) + ((3:ℕ):ℤ) = 3 - ((rowLabel i).2 + 2*(j:ℤ)) := by omega
    have term := laurentToRat_monomial_fraction (-((rowLabel i).2 + 2*(j:ℤ)))
      (archivedWeight k ell j i) 3 (by omega)
    rw [hz, laurentToRat_single] at term
    have mulPower : R^(rowLabel i).2 * R^(2*j) = R^((rowLabel i).2+2*(j:ℤ)) := by
      rw [← zpow_natCast R (2*j), ← zpow_add₀ RatFunc.X_ne_zero]
      congr 1
    rw [laurentToRat_single, mul_assoc, mulPower, map_mul, reciprocalHom_constant, reciprocal_radius_zpow]
    exact term
  · simp [archivedWeight, hj]

theorem archivedSource_orders (k ell : ℂ) : SourceOrders (archivedSource k ell) := by
  constructor
  · refine ⟨(sourceNumerator k ell 0, sourceNumerator k ell 1, sourceNumerator k ell 2), ?_⟩
    simp only [archivedSource, archivedLaurentSource, mapRow, fractionRow, archivedComponent_finite]
  · refine ⟨(infinityNumerator k ell 0, infinityNumerator k ell 1, infinityNumerator k ell 2), ?_⟩
    rw [reciprocalRow_eq_hom]
    apply Prod.ext
    · simpa only [Nat.mul_zero, pow_zero, mul_one, mapRow, unscaledRow, archivedSource,
        archivedLaurentSource, fractionRow] using archivedComponent_infinity k ell 0
    · exact Prod.ext (archivedComponent_infinity k ell 1) (archivedComponent_infinity k ell 2)

#print axioms archivedComponent_coeff
#print axioms archivedSource_orders

end

end SchwarzschildLaurent
