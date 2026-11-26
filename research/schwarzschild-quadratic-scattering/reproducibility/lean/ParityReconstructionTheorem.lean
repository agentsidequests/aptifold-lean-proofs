import ParityReconstructionSufficiency
import ParityReconstructionGeometry

/-! The converse for the full tensor in the regular angular chart. -/
namespace SchwarzschildEinstein.PureOdd.Master

noncomputable section
variable {K : Type*} [Field K] [CharZero K] [Algebra ℚ K]
variable (D : Derivation ℚ K K)

def reconstructedChartMetric (w m c : K) (p : PolarAmplitudes K)
    (a : Mixed.AxialVector K) : SecondMetric K :=
  reggeWheelerChartMetric w m c (Mixed.radialJet D a.time) (Mixed.radialJet D a.radius)
    ⟨Mixed.radialJet D p.tt,Mixed.radialJet D p.tr,Mixed.radialJet D p.rr,Mixed.radialJet D p.sphere⟩

theorem sourced_einstein_reconstruction (r w m c e o : K) (s : ModeSource K)
    (hr : r ≠ 0) (hh : r-2 ≠ 0) (hs : sineSquared c ≠ 0)
    (hl : m*(m+1) ≠ 0) (hmu : (m-1)*(m+2) ≠ 0) (hp : modeLambda m*r+3 ≠ 0)
    (dr : D r = 1) (dw : D w = 0) (dm : D m = 0)
    (conservation : ConservedMode D r w m s)
    (even : waveResidual D r w (SchwarzschildEinstein.zerilli r (modeLambda m)) e =
      evenMasterForcing D r m s.polar)
    (odd : waveResidual D r w (SchwarzschildEinstein.reggeWheeler r (modeLambda m)) o =
      oddMasterForcing D r w m s.axial) :
    let p := reconstructPolar D r w m e s
    let a := reconstructAxial D r w m o s.axial
    linearChartEinstein r c (reconstructedChartMetric D w m c p a) = chartSourceTensor m c s ∧
      evenMasterField D r m p.rr p.sphere = e ∧ oddMasterField D r w m a.time a.radius = o := by
  let p := reconstructPolar D r w m e s
  let a := reconstructAxial D r w m o s.axial
  obtain ⟨mode,er,orr⟩ := sourced_mode_reconstruction D r w m e o s hr hh hl hmu hp dr dw dm conservation even odd
  refine ⟨?_,er,orr⟩
  have chart := full_angle_einstein_of_mode r w m c (Mixed.radialJet D a.time)
    (Mixed.radialJet D a.radius)
    ⟨Mixed.radialJet D p.tt,Mixed.radialJet D p.tr,Mixed.radialJet D p.rr,Mixed.radialJet D p.sphere⟩
    hr hh hs
  change linearChartEinstein r c (reconstructedChartMetric D w m c p a) =
    chartSourceTensor m c (radialModeEinstein D r w m p a) at chart
  rw [chart, mode]

#print axioms sourced_einstein_reconstruction

end
end SchwarzschildEinstein.PureOdd.Master
