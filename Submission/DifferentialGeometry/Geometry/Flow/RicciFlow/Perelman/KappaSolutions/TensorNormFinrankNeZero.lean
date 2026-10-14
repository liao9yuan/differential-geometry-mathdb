import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetric
import Submission.DifferentialGeometry.Tensor.RSTensor.Defs

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.Tensor0SBundle

open scoped _root_.Manifold _root_.ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem finrank_ne_zero_of_normSq0S_ne_zero
    (g : SmoothRiemannianMetric I M) (x : M) {s : ℕ} (hs : 0 < s)
    (A : Tensor0SSpace s I x) (hA : normSq0S (I := I) g x s A ≠ 0) :
    Module.finrank ℝ E ≠ 0 := by
  intro h0
  refine hA ?_
  rw [normSq0S_eq_zero_iff]
  let : Subsingleton E := Module.finrank_zero_iff.mp h0
  apply Tensor0SSpace.toModel_injective
  change Tensor0SSpace.toModel A = Tensor0SSpace.toModel (0 : Tensor0SSpace s I x)
  rw [Tensor0SSpace.toModel_zero]
  ext v
  exact (Tensor0SSpace.toModel A).map_coord_zero ⟨0, hs⟩ (Subsingleton.elim _ _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.finrank_ne_zero_of_normSq0S_ne_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.finrank_ne_zero_of_normSq0S_ne_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.finrank_ne_zero_of_normSq0S_ne_zero ``Submission.DifferentialGeometry.Tensor0SBundle.finrank_ne_zero_of_normSq0S_ne_zero

end DifferentialGeometry.Tensor0SBundle
