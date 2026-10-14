import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.RegularPoleRescalings
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.Measure

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Set _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Integral.Measure
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

private local instance endpointDensityComplete : CompleteSpace E :=
  FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.endpointDensityComplete
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.endpointDensityComplete target :: scope.openDecls } }
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.sigmaCompact PointedFlowData.t2
private local instance endpointDensityMeasurable : MeasurableSpace F.M := borel F.M

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.endpointDensityMeasurable
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.endpointDensityMeasurable target :: scope.openDecls } }
private local instance endpointDensityBorel : BorelSpace F.M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.endpointDensityBorel
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.endpointDensityBorel target :: scope.openDecls } }

theorem poleRescaledFlowSeq_redDensityMeasure_eq_endpoint_withDensity
    (hcar : D.carrier = _root_.Set.Iic 0) (hreg : D.regular = _root_.Set.Iio 0)
    (b : ℝ) (hbmem : b ∈ D.carrier) (tau : ℕ → ℝ) (q : ℕ → F.M)
    (hsigma : ∀ i, 0 < tau i + b) (i : ℕ) (p : F.M) (t : ℝ) :
    redDensityMeasure
      ((poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma).term i).S
      0 p (1 - t) =
      Measure.withDensity
        (riemannianVolumeMeasure (I := I) (M := F.M)
          (((poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma).term i).S.base.metric t))
        (fun y => ENNReal.ofReal (redDensity
          ((poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma).term i).S
          0 p y (1 - t))) := by
  have htime : (0 : ℝ) - (1 - t) = t - 1 := by ring
  unfold redDensityMeasure
  rw [poleEndpointRescaledFlowSeq_metric_eq_shift, htime]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.poleRescaledFlowSeq_redDensityMeasure_eq_endpoint_withDensity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.poleRescaledFlowSeq_redDensityMeasure_eq_endpoint_withDensity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.poleRescaledFlowSeq_redDensityMeasure_eq_endpoint_withDensity ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.poleRescaledFlowSeq_redDensityMeasure_eq_endpoint_withDensity

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
