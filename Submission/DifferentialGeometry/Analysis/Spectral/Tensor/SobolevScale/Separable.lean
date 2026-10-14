import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Defs
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.CompactResolvent

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

instance instSeparableSpace (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : ℝ) :
    TopologicalSpace.SeparableSpace (TensorHs g r s σ) := by
  let : Countable (TensorSpectral.TensorNonzeroResolventEigenvalue g r s) :=
    TensorSpectral.TensorNonzeroResolventEigenvalue.countable_ofCompact g r s
      (DifferentialGeometry.Analysis.Spectral.tensorResolventL2_isCompactOperator g r s)
  let : Countable (TensorEigenIdx g r s) := inferInstance
  let b : HilbertBasis (TensorEigenIdx g r s) ℝ (TensorHs g r s σ) :=
    HilbertBasis.ofRepr (rescaleEquivL2 (g := g) (r := r) (s := s) (σ := σ))
  have hd : Dense (Submodule.span ℝ (Set.range b) : Set (TensorHs g r s σ)) := by
    rw [dense_iff_closure_eq, ← Submodule.topologicalClosure_coe, b.dense_span]
    rfl
  exact hd.isSeparable_iff.mp (Set.countable_range b).isSeparable.span

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.instSeparableSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.instSeparableSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.instSeparableSpace ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.instSeparableSpace

end DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs
