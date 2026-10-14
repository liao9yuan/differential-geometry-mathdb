import Submission.DifferentialGeometry.Geometry.Connection.Laplacian.ConnectionLaplacian
import Submission.DifferentialGeometry.Geometry.Connection.Laplacian.TensorConnLaplacian
import Submission.DifferentialGeometry.Analysis.Integration.L2.SmoothSections.Defs
import Submission.DifferentialGeometry.Tensor.RSTensor.Defs

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Connection


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators _root_.Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Elliptic
namespace ConnectionLaplacian

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }


def connLaplacianMixed (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
      (fun x : M => TensorRSSpace r s I x)⟯)
    (x : M) : TensorRSSpace r s I x :=
  rawTensorConnLap (I := I) g r s (fun b : M => T b) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.connLaplacianMixed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.connLaplacianMixed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.connLaplacianMixed ``Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.connLaplacianMixed


omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
@[simp] lemma connLaplacianMixed_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
      (fun x : M => TensorRSSpace r s I x)⟯) (x : M) :
    connLaplacianMixed (I := I) g r s T x =
      rawTensorConnLap (I := I) g r s (fun b : M => T b) x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.connLaplacianMixed_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.connLaplacianMixed_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.connLaplacianMixed_def ``Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.connLaplacianMixed_def


def connLaplacianMixedSection (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
      (fun x : M => TensorRSSpace r s I x)⟯) :
    Π x : M, TensorRSSpace r s I x :=
  fun x => connLaplacianMixed (I := I) g r s T x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.connLaplacianMixedSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.connLaplacianMixedSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.connLaplacianMixedSection ``Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.connLaplacianMixedSection


omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem connLaplacianMixed_scalar_eq_function
    (g : SmoothRiemannianMetric I M)
    (T : Cₛ^∞⟮I; TensorRSModel 0 0 ℝ E,
      (fun x : M => TensorRSSpace 0 0 I x)⟯)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    ∃ c : ℝ,
      connLaplacianFunction (I := I) g hf x = c ∧
      connLaplacianMixed (I := I) g 0 0 T x =
        rawTensorConnLap (I := I) g 0 0 (fun b : M => T b) x := by
  refine ⟨connLaplacianFunction (I := I) g hf x, rfl, ?_⟩
  exact connLaplacianMixed_def (I := I) g 0 0 T x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.connLaplacianMixed_scalar_eq_function then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.connLaplacianMixed_scalar_eq_function"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.connLaplacianMixed_scalar_eq_function ``Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.connLaplacianMixed_scalar_eq_function

end ConnectionLaplacian
end Elliptic
end Analysis
end DifferentialGeometry

end
