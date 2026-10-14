import Submission.DifferentialGeometry.Analysis.Parabolic.RicciLinearization.CovariantJetDecomposition.CoefficientFields
import Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricPerturbation.CovariantOrderCoefficient.ReindexingNorm

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Geometry.Curvature


noncomputable section

open _root_.MeasureTheory _root_.Set _root_.Filter _root_.Topology _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.DifferentialGeometry.Tensor0SBundle
    ContinuousLinearMap
open scoped _root_.ENNReal _root_.NNReal _root_.BigOperators _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Analysis.Sobolev

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (linearizedRicciOrderZeroBaseCoeff linearizedRicciFirstOrderBaseCoeff ricciDeTurckPrincipalCoefficient
    traceHessianCoeff)
open _root_.Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization (metricPerturbationPath)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

noncomputable def coeffPerOrderJetBound (R δ₀ : ℝ) (curvWeight : ℕ) (i : ℕ) : ℝ :=
  (Module.finrank ℝ E : ℝ) ^ (curvWeight + 2) * (1 + R) ^ (2 * i + 6) *
    (1 / (1 - δ₀)) ^ (4 * i + 12)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.coeffPerOrderJetBound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.coeffPerOrderJetBound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.coeffPerOrderJetBound ``Submission.DifferentialGeometry.Analysis.Sobolev.coeffPerOrderJetBound

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem coeffPerOrderJetBound_nonneg (R δ₀ : ℝ) (hR : 0 ≤ R) (hδ₀ : δ₀ < 1)
    (curvWeight i : ℕ) : 0 ≤ coeffPerOrderJetBound (E := E) R δ₀ curvWeight i := by
  have hpos : 0 < 1 - δ₀ := by linarith
  have hinv_nn : 0 ≤ 1 / (1 - δ₀) := by positivity
  simp only [coeffPerOrderJetBound]
  refine mul_nonneg (mul_nonneg ?_ ?_) ?_
  · exact pow_nonneg (Nat.cast_nonneg _) _
  · exact pow_nonneg (by linarith) _
  · exact pow_nonneg hinv_nn _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.coeffPerOrderJetBound_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.coeffPerOrderJetBound_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.coeffPerOrderJetBound_nonneg ``Submission.DifferentialGeometry.Analysis.Sobolev.coeffPerOrderJetBound_nonneg

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem l2_of_pointwise_riemannianFiberNormSq_iteratedCovGrad_perOrder
    (g₀ : SmoothRiemannianMetric I M) (r i : ℕ)
    (C : SmoothCcTensor g₀ r 2) (Ki : ℝ)
    (hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ r (2 + i) x
          ((iteratedCovGrad (I := I) g₀ r 2 i C).toSection x) ≤ Ki) :
    ‖iteratedCovGrad (I := I) g₀ r 2 i C‖ ^ 2 ≤
      Ki * (riemannianVolumeMeasure (I := I) (M := M) g₀ Set.univ).toReal :=
  norm_le_of_pointwise_fiberNormSq_bound_rs (I := I) (M := M) g₀ r (2 + i)
    (iteratedCovGrad (I := I) g₀ r 2 i C) Ki hpt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.l2_of_pointwise_riemannianFiberNormSq_iteratedCovGrad_perOrder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.l2_of_pointwise_riemannianFiberNormSq_iteratedCovGrad_perOrder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.l2_of_pointwise_riemannianFiberNormSq_iteratedCovGrad_perOrder ``Submission.DifferentialGeometry.Analysis.Sobolev.l2_of_pointwise_riemannianFiberNormSq_iteratedCovGrad_perOrder

end DifferentialGeometry.Analysis.Sobolev

end
