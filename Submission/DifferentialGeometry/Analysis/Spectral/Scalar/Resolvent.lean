import Submission.DifferentialGeometry.Analysis.Elliptic.Operator.VariationalLaplacian
import Submission.DifferentialGeometry.Analysis.Sobolev.Manifold.Rellich.OnManifold
import Submission.DifferentialGeometry.Analysis.Sobolev.Intrinsic.Equivalence.NormEquivalence
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem

private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

variable [I.Boundaryless] [T2Space M] [CompactSpace M]

noncomputable def resolventL2 (g : SmoothRiemannianMetric I M) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) →L[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  (H1ComplToLp (I := I) (M := M) g).comp (resolvent (I := I) (M := M) g)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.resolventL2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.resolventL2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.resolventL2 ``Submission.DifferentialGeometry.Analysis.Laplacian.resolventL2

@[simp] lemma resolventL2_apply (g : SmoothRiemannianMetric I M)
    (f : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    resolventL2 (I := I) (M := M) g f =
      H1ComplToLp (I := I) (M := M) g (resolvent (I := I) (M := M) g f) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.resolventL2_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.resolventL2_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.resolventL2_apply ``Submission.DifferentialGeometry.Analysis.Laplacian.resolventL2_apply

private lemma inner_resolventL2_eq_inner_resolvent
    (g : SmoothRiemannianMetric I M)
    (f h : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    ⟪resolventL2 (I := I) (M := M) g f, h⟫_ℝ =
      ⟪resolvent (I := I) (M := M) g f,
        resolvent (I := I) (M := M) g h⟫_ℝ := by
  rw [resolventL2_apply]
  have hvar := resolvent_inner_eq_lpFunctional (I := I) (M := M) g h
    (resolvent (I := I) (M := M) g f)
  rw [← hvar]
  exact real_inner_comm _ _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.inner_resolventL2_eq_inner_resolvent
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.inner_resolventL2_eq_inner_resolvent target :: scope.openDecls } }

theorem resolventL2_symm
    (g : SmoothRiemannianMetric I M)
    (f h : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    ⟪resolventL2 (I := I) (M := M) g f, h⟫_ℝ =
      ⟪f, resolventL2 (I := I) (M := M) g h⟫_ℝ := by
  rw [inner_resolventL2_eq_inner_resolvent (I := I) (M := M) g f h]
  rw [show ⟪f, resolventL2 (I := I) (M := M) g h⟫_ℝ =
      ⟪resolventL2 (I := I) (M := M) g h, f⟫_ℝ from real_inner_comm _ _]
  rw [inner_resolventL2_eq_inner_resolvent (I := I) (M := M) g h f]
  exact real_inner_comm _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.resolventL2_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.resolventL2_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.resolventL2_symm ``Submission.DifferentialGeometry.Analysis.Laplacian.resolventL2_symm

theorem resolventL2_isSelfAdjoint (g : SmoothRiemannianMetric I M) :
    IsSelfAdjoint (resolventL2 (I := I) (M := M) g) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro f h
  exact resolventL2_symm (I := I) (M := M) g f h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.resolventL2_isSelfAdjoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.resolventL2_isSelfAdjoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.resolventL2_isSelfAdjoint ``Submission.DifferentialGeometry.Analysis.Laplacian.resolventL2_isSelfAdjoint

end Laplacian
end Analysis
end DifferentialGeometry

end
