import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.UniformChartBounds.FiberNorm.UniformBound
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Iterated.Linear

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Analysis.Spectral

open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem exists_riemannianFiberNormSq_iteratedCovGrad_bound
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (F : SmoothCcTensor g r s) :
    ∃ c : ℕ → ℝ, (∀ i, 0 ≤ c i) ∧ ∀ (i : ℕ) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g r (s + i) x
        ((iteratedCovGrad (I := I) g r s i F).toSection x) ≤ c i := by
  refine ⟨fun i => (exists_bound_riemannianFiberNormSq_smoothCcTensor
      (I := I) (M := M) g r (s + i)
      (iteratedCovGrad (I := I) g r s i F)).choose,
    fun i => (exists_bound_riemannianFiberNormSq_smoothCcTensor
      (I := I) (M := M) g r (s + i)
      (iteratedCovGrad (I := I) g r s i F)).choose_spec.1,
    fun i x => (exists_bound_riemannianFiberNormSq_smoothCcTensor
      (I := I) (M := M) g r (s + i)
      (iteratedCovGrad (I := I) g r s i F)).choose_spec.2 x⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.exists_riemannianFiberNormSq_iteratedCovGrad_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.exists_riemannianFiberNormSq_iteratedCovGrad_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.exists_riemannianFiberNormSq_iteratedCovGrad_bound ``Submission.DifferentialGeometry.Analysis.Spectral.exists_riemannianFiberNormSq_iteratedCovGrad_bound

end DifferentialGeometry.Analysis.Spectral

end
