import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.ChartBilinear.H1Compl
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.ChartBilinear.Smooth
import Submission.DifferentialGeometry.Analysis.Elliptic.Operator.VariationalLaplacian
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.MeasureTheory _root_.Filter _root_.Topology _root_.Function
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.Matrix _root_.InnerProductSpace _root_.BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace ChartBilinearH1ComplFromDom

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartLocalLaplacian
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearSmooth
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean

private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1ComplFromDom.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1ComplFromDom.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1ComplFromDom.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1ComplFromDom.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1ComplFromDom.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1ComplFromDom.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1ComplFromDom.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1ComplFromDom.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1ComplFromDom.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1ComplFromDom.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1ComplFromDom.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1ComplFromDom.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [I.Boundaryless] [T2Space M] [CompactSpace M]

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_smooth_approx_seq
    (g : SmoothRiemannianMetric I M) (u_h : H1Compl g) :
    ∃ v : ℕ → SmoothScalar g,
      Tendsto (fun n => smoothToH1Compl (I := I) (M := M) g (v n)) _root_.Filter.atTop (𝓝 u_h) := by
  classical
  have h_dense :
      u_h ∈ closure (Set.range (smoothToH1Compl (I := I) (M := M) g)) := by
    rw [(denseRange_smoothToH1Compl (I := I) (M := M) g).closure_eq]
    exact Set.mem_univ _
  obtain ⟨s, hs_mem, hs_tendsto⟩ := mem_closure_iff_seq_limit.mp h_dense
  refine ⟨fun n => Classical.choose (hs_mem n), ?_⟩
  have h_eq : (fun n => smoothToH1Compl (I := I) (M := M) g
        (Classical.choose (hs_mem n))) = s := by
    funext n
    exact Classical.choose_spec (hs_mem n)
  rw [h_eq]
  exact hs_tendsto

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1ComplFromDom.exists_smooth_approx_seq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1ComplFromDom.exists_smooth_approx_seq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1ComplFromDom.exists_smooth_approx_seq ``Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1ComplFromDom.exists_smooth_approx_seq

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_smooth_approx_seq_lp
    (g : SmoothRiemannianMetric I M)
    (f_h : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    ∃ v : ℕ → SmoothScalar g,
      Tendsto (fun n => smoothToLp (I := I) (M := M) g (v n)) _root_.Filter.atTop (𝓝 f_h) := by
  classical
  have h_dense :
      f_h ∈ closure (Set.range (smoothToLp (I := I) (M := M) g)) := by
    rw [(denseRange_smoothToLp (I := I) (M := M) g).closure_eq]
    exact Set.mem_univ _
  obtain ⟨s, hs_mem, hs_tendsto⟩ := mem_closure_iff_seq_limit.mp h_dense
  refine ⟨fun n => Classical.choose (hs_mem n), ?_⟩
  have h_eq : (fun n => smoothToLp (I := I) (M := M) g
        (Classical.choose (hs_mem n))) = s := by
    funext n
    exact Classical.choose_spec (hs_mem n)
  rw [h_eq]
  exact hs_tendsto

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1ComplFromDom.exists_smooth_approx_seq_lp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1ComplFromDom.exists_smooth_approx_seq_lp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1ComplFromDom.exists_smooth_approx_seq_lp ``Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1ComplFromDom.exists_smooth_approx_seq_lp

end ChartBilinearH1ComplFromDom
end Laplacian
end Analysis
end DifferentialGeometry
