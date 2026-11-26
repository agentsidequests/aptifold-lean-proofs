/-! Scalar jets and their coordinate index, independent of the algebra
used to evaluate them. -/
namespace SchwarzschildEinstein

universe u

abbrev Axis := Fin 4

structure FirstJet (K : Type u) where
  value : K
  gradient : Axis → K

structure SecondJet (K : Type u) extends FirstJet K where
  second : Axis → Axis → K

abbrev FirstMetric (K : Type u) := Axis → Axis → FirstJet K
abbrev SecondMetric (K : Type u) := Axis → Axis → SecondJet K

end SchwarzschildEinstein
