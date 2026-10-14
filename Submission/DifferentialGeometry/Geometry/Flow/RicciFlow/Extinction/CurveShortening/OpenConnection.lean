import Submission.DifferentialGeometry.Geometry.Geodesic.Naturality.OpenSubtype
import Submission.DifferentialGeometry.Geometry.Connection.ParallelTransport.Derivative.CovariantDerivativeAlong

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.Filter _root_.TopologicalSpace
open scoped _root_.Manifold _root_.ContDiff _root_.Topology
open _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.AlongCurve
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem covDerivAlong_restrictOpen (g : SmoothRiemannianMetric I M) (U : _root_.TopologicalSpace.Opens M)
    (gamma : ℝ → U) (V : ∀ t, TangentSpace I (gamma t)) (t : ℝ)
    (hgamma : ContinuousAt gamma t) :
    letI : IsManifold I ∞ U := { U.instHasGroupoid (contDiffGroupoid ∞ I) with }
    (show TangentSpace I (gamma t : M) from covDerivAlong (g.restrictOpen U) gamma V t) =
      covDerivAlong g (fun s => (gamma s : M))
        (fun s => (show TangentSpace I (gamma s : M) from V s)) t := by
  let : IsManifold I ∞ U := { U.instHasGroupoid (contDiffGroupoid ∞ I) with }
  have hnear : ∀ᶠ s in 𝓝 t, (gamma s : M) ∈ (chartAt H (gamma t : M)).source :=
    ((continuous_subtype_val.continuousAt.comp hgamma).tendsto).eventually
      ((chartAt H (gamma t : M)).open_source.mem_nhds (mem_chart_source H (gamma t : M)))
  have hrep : chartRepAt gamma V t =ᶠ[𝓝 t]
      chartRepAt (fun s => (gamma s : M))
        (fun s => (show TangentSpace I (gamma s : M) from V s)) t := by
    filter_upwards [hnear] with s hs
    have hsU : gamma s ∈ (chartAt H (gamma t)).source := by
      rw [TopologicalSpace.Opens.chartAt_eq, OpenPartialHomeomorph.subtypeRestr_source]
      exact hs
    rw [chartRepAt_apply, chartRepAt_apply,
      TangentBundle.continuousLinearMapAt_trivializationAt_eq_core hsU,
      TangentBundle.continuousLinearMapAt_trivializationAt_eq_core hs,
      tangentCoordChange_opens (I := I) (gamma s) (gamma t) (gamma s)
        (mem_chart_source H (gamma s : M))]
    rfl
  have hsymm : (_root_.FiberBundle.trivializationAt E (TangentSpace I (M := U)) (gamma t)).symmL ℝ (gamma t) =
      (_root_.FiberBundle.trivializationAt E (TangentSpace I (M := M)) (gamma t : M)).symmL ℝ (gamma t : M) := by
    rw [TangentBundle.symmL_trivializationAt_eq_core (mem_chart_source H (gamma t)),
      TangentBundle.symmL_trivializationAt_eq_core (mem_chart_source H (gamma t : M)),
      tangentCoordChange_opens (I := I) (gamma t) (gamma t) (gamma t)
        (mem_chart_source H (gamma t : M))]
  have hcurve : chartCurve (I := I) (gamma t) gamma =
      chartCurve (I := I) (gamma t : M) (fun s => (gamma s : M)) := rfl
  unfold covDerivAlong
  rw [hsymm]
  unfold chartCovDerivAlong
  rw [hrep.deriv_eq, hrep.eq_of_nhds, hcurve]
  exact congrArg (fun z =>
    (_root_.FiberBundle.trivializationAt E (TangentSpace I (M := M)) (gamma t : M)).symmL ℝ (gamma t : M)
      (deriv (chartRepAt (I := I) (fun s => (gamma s : M))
        (fun s => (show TangentSpace I (gamma s : M) from V s)) t) t + z))
    (Geodesic.contr_open g U (gamma t) _ _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.covDerivAlong_restrictOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.covDerivAlong_restrictOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.covDerivAlong_restrictOpen ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.covDerivAlong_restrictOpen

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
