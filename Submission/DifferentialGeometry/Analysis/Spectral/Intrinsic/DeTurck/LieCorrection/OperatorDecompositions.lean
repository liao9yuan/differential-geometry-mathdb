import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.LieCorrection.TameBounds
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.LieCorrection.Zero.Splitting

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

noncomputable section
set_option backward.isDefEq.respectTransparency false

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff

namespace DifferentialGeometry.Analysis.Spectral

open _root_.Submission.DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators
open _root_.Submission.DifferentialGeometry.Integral.L2

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem lieCorrectionZeroInsertion_eq_lieCorrectionZeroInsertionField
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    lieCorrectionZeroInsertion (I := I) (M := M) g₀ g₁ g_bg =
      lieCorrectionZeroInsertionField (I := I) (M := M) g₀ g₁ g_bg := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  exact (lieCorrectionZero_insert_fiber (I := I) (M := M) g₀ g₁ g_bg x D m).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.lieCorrectionZeroInsertion_eq_lieCorrectionZeroInsertionField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.lieCorrectionZeroInsertion_eq_lieCorrectionZeroInsertionField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.lieCorrectionZeroInsertion_eq_lieCorrectionZeroInsertionField ``Submission.DifferentialGeometry.Analysis.Spectral.lieCorrectionZeroInsertion_eq_lieCorrectionZeroInsertionField

omit [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem lieCorrectionZeroVectorBundle_eq_field (g₀ g₁ : SmoothRiemannianMetric I M) :
    lieCorrectionZeroVectorBundle (I := I) (M := M) g₀ g₁ =
      lieCorrectionZeroVectorBundleField (I := I) (M := M) g₀ g₁ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  change lieCorrectionZeroVBFib (I := I) g₀ g₁ x D = _
  exact (lieCorrectionZero_vb_fiber (I := I) (M := M) g₀ g₁ x D).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.lieCorrectionZeroVectorBundle_eq_field then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.lieCorrectionZeroVectorBundle_eq_field"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.lieCorrectionZeroVectorBundle_eq_field ``Submission.DifferentialGeometry.Analysis.Spectral.lieCorrectionZeroVectorBundle_eq_field

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem lieCorrectionZeroMixedConnection_eq_lieCorrectionZeroMixedConnectionField (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    lieCorrectionZeroMixedConnection (I := I) (M := M) g₀ g₁ g_bg =
      lieCorrectionZeroMixedConnectionField (I := I) (M := M) g₀ g₁ g_bg := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  change lieCorrectionZeroMixedConnectionFib (I := I) g₀ g₁ g_bg x D = _
  exact (lieCorrectionZero_amix_fiber (I := I) (M := M) g₀ g₁ g_bg x D).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.lieCorrectionZeroMixedConnection_eq_lieCorrectionZeroMixedConnectionField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.lieCorrectionZeroMixedConnection_eq_lieCorrectionZeroMixedConnectionField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.lieCorrectionZeroMixedConnection_eq_lieCorrectionZeroMixedConnectionField ``Submission.DifferentialGeometry.Analysis.Spectral.lieCorrectionZeroMixedConnection_eq_lieCorrectionZeroMixedConnectionField

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem lieCorrectionZeroRiemann_eq_field (g₀ g₁ : SmoothRiemannianMetric I M) :
    lieCorrectionZeroRiemann (I := I) (M := M) g₀ g₁ =
      lieCorrectionZeroRiemannField (I := I) (M := M) g₀ g₁ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  change TensorRSSpace.ofCLM (lieCorrectionZeroRiemFib (I := I) g₀ g₁ x) D = _
  exact (lieCorrectionZero_riem_fiber (I := I) (M := M) g₀ g₁ x D).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.lieCorrectionZeroRiemann_eq_field then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.lieCorrectionZeroRiemann_eq_field"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.lieCorrectionZeroRiemann_eq_field ``Submission.DifferentialGeometry.Analysis.Spectral.lieCorrectionZeroRiemann_eq_field

end DifferentialGeometry.Analysis.Spectral

end
