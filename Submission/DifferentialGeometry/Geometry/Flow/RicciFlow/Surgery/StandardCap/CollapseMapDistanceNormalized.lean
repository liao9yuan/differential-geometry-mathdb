import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.CollapseMapDistance
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.QuotientCollapse

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.TopologicalSpace _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Geometry
open _root_.Submission.DifferentialGeometry.Geometry.Metric
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Topology _root_.Submission.DifferentialGeometry.Topology.Manifold
open _root_.Submission.DifferentialGeometry.Topology.Manifold.Attachment
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Topology.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.Geometry.Neck.normalizedDatum

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.normalizedDatum.E3 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.instFactEqNatFinrankRealE3HAddOfNat : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.instFactEqNatFinrankRealE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.normalizedDatum.instFactEqNatFinrankRealE3HAddOfNat target :: scope.openDecls } }
private local instance quotientChartedSpace {B : ℝ} {hB : 0 < B} :
    ChartedSpace E3 (InsertionQuotient hB) :=
  radialCapAttachmentChartedSpace transitionEnd_pos hB

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.quotientChartedSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.normalizedDatum.quotientChartedSpace target :: scope.openDecls } }
private local instance quotientIsManifold {B : ℝ} {hB : 0 < B} :
    IsManifold (𝓡 3) ∞ (InsertionQuotient hB) :=
  radialCapAttachment_isManifold transitionEnd_pos hB

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.quotientIsManifold
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.normalizedDatum.quotientIsManifold target :: scope.openDecls } }
private local instance quotientT2Space {B : ℝ} {hB : 0 < B} :
    T2Space (InsertionQuotient hB) := radialCapAttachment_t2Space transitionEnd_pos hB

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.quotientT2Space
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.normalizedDatum.quotientT2Space target :: scope.openDecls } }

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}

theorem controlledImage_controlledChart_symm_edist (d : normalizedDatum g x₀ δ k)
    (p q : d.controlledImage) :
    riemannianEDistOf d.controlledMetric (d.controlledChart.symm p) (d.controlledChart.symm q) =
      ENNReal.ofReal (Real.sqrt (metricScalarAt g x₀)) *
        riemannianEDistOf (g.restrictOpen d.controlledImage) p q := by
  rw [← edistOf_pullbackMetricCross d.controlledMetric d.controlledChart.symm p q,
    pullback_controlledMetric_controlledChart_symm,
    DifferentialGeometry.edistOf_scale (metricScalarAt g x₀) d.scalar_pos
      (g.restrictOpen d.controlledImage) p q]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledImage_controlledChart_symm_edist then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledImage_controlledChart_symm_edist"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledImage_controlledChart_symm_edist ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledImage_controlledChart_symm_edist

theorem positiveSideCollapseMap_riemannianEDistOf_le (d : normalizedDatum g x₀ δ k) {A : ℝ}
    (hA : 0 < A) (hAB : 2 * A < δ⁻¹) (p q : d.controlledImage) :
    riemannianEDistOf (d.positiveSideCollapseMetric hA hAB)
        (d.positiveSideCollapseMap hA hAB p) (d.positiveSideCollapseMap hA hAB q) ≤
      riemannianEDistOf (g.restrictOpen d.controlledImage) p q := by
  have hmodel :=
    DifferentialGeometry.PDE.RicciFlow.StandardCap.collapseMap_riemannianEDistOf_le_of_cylinder_lower
      hA hAB d.controlledMetric_cylinder_lower.1 d.controlledMetric
      d.controlledMetric_cylinder_lower.2 (d.controlledChart.symm p) (d.controlledChart.symm q)
  have hscale : ENNReal.ofReal (Real.sqrt (metricScalarAt g x₀)⁻¹) *
      ENNReal.ofReal (Real.sqrt (metricScalarAt g x₀)) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _),
      ← Real.sqrt_mul (inv_nonneg.mpr d.scalar_pos.le), inv_mul_cancel₀ d.scalar_pos.ne',
      Real.sqrt_one, ENNReal.ofReal_one]
  calc riemannianEDistOf (d.positiveSideCollapseMetric hA hAB)
        (d.positiveSideCollapseMap hA hAB p) (d.positiveSideCollapseMap hA hAB q)
      = ENNReal.ofReal (Real.sqrt (metricScalarAt g x₀)⁻¹) *
          riemannianEDistOf
            (insertedMetric hA hAB d.controlledMetric_cylinder_lower.1 d.controlledMetric)
            (collapseMap hA hAB (d.controlledChart.symm p))
            (collapseMap hA hAB (d.controlledChart.symm q)) := by
        rw [positiveSideCollapseMap, positiveSideCollapseMetric, Function.comp_apply]
        exact DifferentialGeometry.edistOf_scale (metricScalarAt g x₀)⁻¹
          (inv_pos.mpr d.scalar_pos)
          (insertedMetric hA hAB d.controlledMetric_cylinder_lower.1 d.controlledMetric)
          (collapseMap hA hAB (d.controlledChart.symm p))
          (collapseMap hA hAB (d.controlledChart.symm q))
    _ ≤ ENNReal.ofReal (Real.sqrt (metricScalarAt g x₀)⁻¹) *
          riemannianEDistOf d.controlledMetric
            (d.controlledChart.symm p) (d.controlledChart.symm q) :=
        mul_le_mul_right hmodel _
    _ = ENNReal.ofReal (Real.sqrt (metricScalarAt g x₀)⁻¹) *
          (ENNReal.ofReal (Real.sqrt (metricScalarAt g x₀)) *
            riemannianEDistOf (g.restrictOpen d.controlledImage) p q) := by
        rw [controlledImage_controlledChart_symm_edist]
    _ = riemannianEDistOf (g.restrictOpen d.controlledImage) p q := by
        rw [← mul_assoc, hscale, one_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideCollapseMap_riemannianEDistOf_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideCollapseMap_riemannianEDistOf_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideCollapseMap_riemannianEDistOf_le ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideCollapseMap_riemannianEDistOf_le

theorem positiveSideQuotientCollapseMap_riemannianEDistOf_le (d : normalizedDatum g x₀ δ k)
    {A : ℝ} (hA : 0 < A) (hAB : 2 * A < δ⁻¹) (p q : d.controlledImage) :
    letI := radialCapAttachmentChartedSpace transitionEnd_pos (inv_pos.mpr d.precision_pos)
    riemannianEDistOf (d.positiveSideInsertionMetric hA hAB)
        (d.positiveSideQuotientCollapseMap hA hAB p)
        (d.positiveSideQuotientCollapseMap hA hAB q) ≤
      riemannianEDistOf (g.restrictOpen d.controlledImage) p q := by
  rw [d.positiveSideQuotientCollapseMap_edist hA hAB p q]
  exact d.positiveSideCollapseMap_riemannianEDistOf_le hA hAB p q

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideQuotientCollapseMap_riemannianEDistOf_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideQuotientCollapseMap_riemannianEDistOf_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideQuotientCollapseMap_riemannianEDistOf_le ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideQuotientCollapseMap_riemannianEDistOf_le

end DifferentialGeometry.Geometry.Neck.normalizedDatum
