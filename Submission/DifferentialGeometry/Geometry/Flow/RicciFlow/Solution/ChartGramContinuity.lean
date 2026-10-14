import Submission.DifferentialGeometry.Geometry.Metric.Family.Basic
import Submission.DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set
open _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Tensor.Coordinates
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M]

private local instance _root_.Submission.DifferentialGeometry.Geometry.Curvature.instIsManifoldRealOfNatWithTopENat_differentialGeometry : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.instIsManifoldRealOfNatWithTopENat_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.instIsManifoldRealOfNatWithTopENat_differentialGeometry target :: scope.openDecls } }

theorem tensor0SFamilyContinuousOnSet.continuousOn_chartGram
    {g : ℝ → SmoothRiemannianMetric I M} {J : Set ℝ}
    (hg : tensor0SFamilyContinuousOnSet 2 J (fun t x => metricTensorField (g t) x))
    (α : M) (i j : Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (fun q : ℝ × M => chartGramMatrix (g q.1) α q.2 i j)
      (J ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet) := by
  let Q := ↥(J ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet)
  have hframe (l : Fin 2) : Continuous (fun q : Q =>
      TotalSpace.mk' E q.1.2
        (chartBasisVecFiber (I := I) α (![i, j] l) q.1.2)) :=
    (chartBasisVec_contMDiffOn (I := I) α (![i, j] l)).continuousOn.comp_continuous
      (continuous_snd.comp continuous_subtype_val) (fun q : Q => q.2.2)
  have heval := hg.eval_continuous (P := Q)
    (τ := fun q : Q => q.1.1) (b := fun q : Q => q.1.2)
    (v := fun l (q : Q) => chartBasisVecFiber (I := I) α (![i, j] l) q.1.2)
    (continuous_fst.comp continuous_subtype_val) (fun q : Q => q.2.1)
    (continuous_snd.comp continuous_subtype_val) hframe
  rw [continuousOn_iff_continuous_domRestrict]
  exact heval.congr (fun q => by
    simp only [metricTensorField_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      chartGramMatrix_apply]
    rfl)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.tensor0SFamilyContinuousOnSet.continuousOn_chartGram then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.tensor0SFamilyContinuousOnSet.continuousOn_chartGram"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.tensor0SFamilyContinuousOnSet.continuousOn_chartGram ``Submission.DifferentialGeometry.Geometry.Curvature.tensor0SFamilyContinuousOnSet.continuousOn_chartGram

end DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.SolutionOn

open _root_.Submission.DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] {D : RealTimeInterval}

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.SolutionOn.instIsManifoldRealOfNatWithTopENat : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.SolutionOn.instIsManifoldRealOfNatWithTopENat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.SolutionOn.instIsManifoldRealOfNatWithTopENat target :: scope.openDecls } }

omit [SigmaCompactSpace M] in
theorem continuousOn_chartGram (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) (α : M) (i j : Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (fun q : ℝ × M => chartGramMatrix (S.family.metric q.1) α q.2 i j)
      (D.carrier ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet) :=
  hS.smoothMetric.metricTensor_cont.continuousOn_chartGram α i j

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.SolutionOn.continuousOn_chartGram then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.SolutionOn.continuousOn_chartGram"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.SolutionOn.continuousOn_chartGram ``Submission.DifferentialGeometry.PDE.RicciFlow.SolutionOn.continuousOn_chartGram

end DifferentialGeometry.PDE.RicciFlow.SolutionOn
