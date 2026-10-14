import Submission.DifferentialGeometry.Geometry.Neck.VolumeComparison
import Submission.DifferentialGeometry.Geometry.Measure.RoundCylinderVolume
import Submission.DifferentialGeometry.Geometry.Measure.OpenSubtypeVolume

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Submission.Set _root_.Function _root_.TopologicalSpace _root_.Manifold _root_.Submission.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Geometry.Metric
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.ENNReal _root_.Topology _root_.Submission.DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry.Neck

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.E3 target :: scope.openDecls } }
private abbrev S2 := Metric.sphere (0 : E3) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.S2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.S2 target :: scope.openDecls } }
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.IC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.IC target :: scope.openDecls } }
private instance _root_.Submission.DifferentialGeometry.Geometry.Neck.instFactEqNatFinrankRealE3HAddOfNat : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.instFactEqNatFinrankRealE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.instFactEqNatFinrankRealE3HAddOfNat target :: scope.openDecls } }
private instance _root_.Submission.DifferentialGeometry.Geometry.Neck.instMeasurableSpaceSubtypeProdElemE3S2RealMemOpensBufferedCylinder {δ : ℝ} : MeasurableSpace (bufferedCylinder δ) := borel (bufferedCylinder δ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.instMeasurableSpaceSubtypeProdElemE3S2RealMemOpensBufferedCylinder
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.instMeasurableSpaceSubtypeProdElemE3S2RealMemOpensBufferedCylinder target :: scope.openDecls } }
private instance _root_.Submission.DifferentialGeometry.Geometry.Neck.instBorelSpaceSubtypeProdElemE3S2RealMemOpensBufferedCylinder {δ : ℝ} : BorelSpace (bufferedCylinder δ) := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.instBorelSpaceSubtypeProdElemE3S2RealMemOpensBufferedCylinder
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.instBorelSpaceSubtypeProdElemE3S2RealMemOpensBufferedCylinder target :: scope.openDecls } }
private instance _root_.Submission.DifferentialGeometry.Geometry.Neck.instSigmaCompactSpaceSubtypeProdElemE3S2RealMemOpensBufferedCylinder {δ : ℝ} : SigmaCompactSpace (bufferedCylinder δ) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen IC (bufferedCylinder δ).isOpen)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.instSigmaCompactSpaceSubtypeProdElemE3S2RealMemOpensBufferedCylinder
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.instSigmaCompactSpaceSubtypeProdElemE3S2RealMemOpensBufferedCylinder target :: scope.openDecls } }
private instance _root_.Submission.DifferentialGeometry.Geometry.Neck.instMeasurableSpaceProdElemE3S2Real : MeasurableSpace (S2 × ℝ) := borel (S2 × ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.instMeasurableSpaceProdElemE3S2Real
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.instMeasurableSpaceProdElemE3S2Real target :: scope.openDecls } }
private instance _root_.Submission.DifferentialGeometry.Geometry.Neck.instBorelSpaceProdElemE3S2Real : BorelSpace (S2 × ℝ) := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.instBorelSpaceProdElemE3S2Real
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.instBorelSpaceProdElemE3S2Real target :: scope.openDecls } }

private theorem referenceMetric_negative_closed_band_volume (δ : ℝ) :
    riemannianVolumeMeasure IC (bufferedCylinder δ) (referenceMetric δ)
      {q | q.val.2 ∈ _root_.Set.Icc (-δ⁻¹) (-1 : ℝ)} =
      ENNReal.ofReal (8 * Real.pi) * ENNReal.ofReal (δ⁻¹ - 1) := by
  have hS : MeasurableSet ((_root_.Set.univ : Set S2) ×ˢ _root_.Set.Icc (-δ⁻¹) (-1 : ℝ)) :=
    (isClosed_univ.prod isClosed_Icc).measurableSet
  have hfit : (_root_.Set.univ : Set S2) ×ˢ _root_.Set.Icc (-δ⁻¹) (-1 : ℝ) ⊆ bufferedCylinder δ := by
    intro q hq
    change -δ⁻¹ - 1 < q.2 ∧ q.2 < δ⁻¹ + 1
    constructor <;> linarith [hq.2.1, hq.2.2]
  have heq := DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_restrictOpen_preimage_of_subset
    (roundCylinderMetric (E := E3) (n := 2)) (bufferedCylinder δ) hS hfit
  have hset : (Subtype.val : bufferedCylinder δ → S2 × ℝ) ⁻¹'
      (_root_.Set.univ ×ˢ _root_.Set.Icc (-δ⁻¹) (-1 : ℝ)) = {q | q.val.2 ∈ _root_.Set.Icc (-δ⁻¹) (-1 : ℝ)} := by
    ext q
    simp only [_root_.Set.mem_preimage, _root_.Set.mem_prod, _root_.Set.mem_univ, true_and, _root_.Set.mem_ofPred_eq]
  rw [hset] at heq
  change riemannianVolumeMeasure IC (bufferedCylinder δ)
    ((roundCylinderMetric (E := E3) (n := 2)).restrictOpen (bufferedCylinder δ)) _ = _
  rw [heq, DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_roundCylinder_interval]
  congr 2
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.referenceMetric_negative_closed_band_volume
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.referenceMetric_negative_closed_band_volume target :: scope.openDecls } }

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M]
private local instance _root_.Submission.DifferentialGeometry.Geometry.Neck.instMeasurableSpace_differentialGeometry : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Geometry.Neck.instBorelSpace_differentialGeometry : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.instBorelSpace_differentialGeometry target :: scope.openDecls } }

namespace normalizedDatum

variable {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}

theorem negative_closed_band_volume_ge (d : normalizedDatum g x₀ δ k) (hδ : δ ≤ 1 / 4) :
    ENNReal.ofReal (2 * Real.pi / δ) * ENNReal.ofReal ((metricScalarAt g x₀) ^ (-3 / 2 : ℝ)) ≤
      riemannianVolumeMeasure I M g (d.map ''
        {q : bufferedCylinder δ | q.val.2 ∈ _root_.Set.Icc (-δ⁻¹) (-1 : ℝ)}) := by
  have hS : MeasurableSet {q : bufferedCylinder δ | q.val.2 ∈ _root_.Set.Icc (-δ⁻¹) (-1 : ℝ)} :=
    isClosed_Icc.measurableSet.preimage (continuous_snd.comp continuous_subtype_val).measurable
  have hcontrol : {q : bufferedCylinder δ | q.val.2 ∈ _root_.Set.Icc (-δ⁻¹) (-1 : ℝ)} ⊆
      controlledCylinder δ := by
    intro q hq
    exact ⟨hq.1, hq.2.trans (by linarith [inv_pos.mpr d.precision_pos])⟩
  have hv := d.volume_image_ge hS hcontrol
  have href := referenceMetric_negative_closed_band_volume δ
  change riemannianVolumeMeasure IC (bufferedCylinder δ)
    ((roundCylinderMetric (E := E3) (n := 2)).restrictOpen (bufferedCylinder δ)) _ = _ at href
  rw [href] at hv
  have hh : 1 / 2 ≤ (1 - δ) ^ (3 / 2 : ℝ) := by
    rw [Real.rpow_div_two_eq_sqrt 3 (by linarith : 0 ≤ 1 - δ)]
    norm_num only [Real.rpow_ofNat]
    have hs : (4 / 5 : ℝ) ≤ Real.sqrt (1 - δ) :=
      (Real.le_sqrt (by norm_num) (by linarith)).mpr (by nlinarith)
    calc
      (1 / 2 : ℝ) ≤ (4 / 5 : ℝ) ^ 3 := by norm_num
      _ ≤ Real.sqrt (1 - δ) ^ 3 := pow_le_pow_left₀ (by norm_num) hs 3
  have hi : 4 ≤ δ⁻¹ := by
    rw [inv_eq_one_div]
    exact (le_div_iff₀ d.precision_pos).mpr (by linarith)
  have hl : (1 / 2 : ℝ) * δ⁻¹ ≤ δ⁻¹ - 1 := by linarith
  have hreal : 2 * Real.pi / δ ≤ (1 - δ) ^ (3 / 2 : ℝ) *
      (8 * Real.pi) * (δ⁻¹ - 1) := by
    have hc := mul_le_mul hh hl (by positivity)
      (Real.rpow_nonneg (by linarith : 0 ≤ 1 - δ) _)
    have hm := mul_le_mul_of_nonneg_left hc (show 0 ≤ 8 * Real.pi by positivity)
    calc
      2 * Real.pi / δ = (8 * Real.pi) * ((1 / 2) * ((1 / 2) * δ⁻¹)) := by ring
      _ ≤ (8 * Real.pi) * ((1 - δ) ^ (3 / 2 : ℝ) * (δ⁻¹ - 1)) := hm
      _ = _ := by ring
  calc
    _ ≤ ENNReal.ofReal ((1 - δ) ^ (3 / 2 : ℝ) * (8 * Real.pi) * (δ⁻¹ - 1)) *
        ENNReal.ofReal ((metricScalarAt g x₀) ^ (-3 / 2 : ℝ)) :=
      mul_le_mul' (ENNReal.ofReal_le_ofReal hreal) le_rfl
    _ = _ := by
      rw [ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg (by linarith) _) (by positivity)),
        ENNReal.ofReal_mul (Real.rpow_nonneg (by linarith) _)]
      ac_rfl
    _ ≤ _ := hv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.negative_closed_band_volume_ge then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.negative_closed_band_volume_ge"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.negative_closed_band_volume_ge ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.negative_closed_band_volume_ge

end normalizedDatum
end DifferentialGeometry.Geometry.Neck
