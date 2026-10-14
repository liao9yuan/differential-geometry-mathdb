import Submission.DifferentialGeometry.Analysis.Spectral.Scalar.EigenBasis

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
namespace Spectral

open _root_.Submission.DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.Spectral.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.Spectral.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.Spectral.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.Spectral.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.Spectral.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.Spectral.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.Spectral.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.Spectral.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.Spectral.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.Spectral.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.Spectral.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.Spectral.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

abbrev EigenIdx (g : SmoothRiemannianMetric I M) : Type _ :=
  Σ μ : NonzeroResolventEigenvalue (I := I) (M := M) g,
    Fin (Module.finrank ℝ (resolventEigenspace (I := I) (M := M) g μ.val))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.Spectral.EigenIdx then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.Spectral.EigenIdx"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.Spectral.EigenIdx ``Submission.DifferentialGeometry.Analysis.Laplacian.Spectral.EigenIdx

noncomputable abbrev EigenIdx.lambda
    {g : SmoothRiemannianMetric I M}
    (i : EigenIdx (I := I) (M := M) g) : ℝ :=
  laplacianEigenvalueOf i.fst.val

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Analysis.Laplacian.Spectral.EigenIdx
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.Spectral.EigenIdx.lambda then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.Spectral.EigenIdx.lambda"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.Spectral.EigenIdx.lambda ``Submission.DifferentialGeometry.Analysis.Laplacian.Spectral.EigenIdx.lambda

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem EigenIdx.lambda_nonneg
    {g : SmoothRiemannianMetric I M}
    (i : EigenIdx (I := I) (M := M) g) :
    0 ≤ EigenIdx.lambda (I := I) (M := M) i :=
  laplacianEigenvalueOf_nonneg (I := I) (M := M) i.fst

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.Spectral.EigenIdx.lambda_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.Spectral.EigenIdx.lambda_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.Spectral.EigenIdx.lambda_nonneg ``Submission.DifferentialGeometry.Analysis.Laplacian.Spectral.EigenIdx.lambda_nonneg

end Spectral
end Laplacian
end Analysis
end DifferentialGeometry

end
