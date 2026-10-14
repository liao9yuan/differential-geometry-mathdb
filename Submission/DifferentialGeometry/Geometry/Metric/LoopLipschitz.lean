import Submission.DifferentialGeometry.Geometry.Metric.CompactSourceDerivative
import Submission.DifferentialGeometry.Geometry.Metric.ConvexSourceLipschitz
import Submission.DifferentialGeometry.Topology.LoopSpace.Lipschitz

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

noncomputable section

open _root_.Set _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.Topology _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

theorem exists_riemannian_lipschitz_freeLoop_of_contMDiff
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : loopCircle → M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 (fun t : ℝ => γ (t : loopCircle))) :
    ∃ C : ℝ≥0, ∀ θ η, riemannianEDistOf g (γ θ) (γ η) ≤ (C : ℝ≥0∞) * _root_.EDist.edist θ η := by
  obtain ⟨C, hC⟩ := exists_compact_source_mfderiv_bound g isOpen_univ hγ.contMDiffOn
    (_root_.CompactIccSpace.isCompact_Icc : IsCompact (_root_.Set.Icc (-1 : ℝ) 2)) (_root_.Set.subset_univ _)
  refine ⟨C, ?_⟩
  intro θ η
  obtain ⟨a, d, ha0, ha1, hd0, hd1, haη, hadθ, hdist⟩ := exists_short_circle_lifts θ η
  have ha : a ∈ _root_.Set.Icc (-1 : ℝ) 2 := ⟨by linarith, by linarith⟩
  have had : a + d ∈ _root_.Set.Icc (-1 : ℝ) 2 := ⟨by linarith, by linarith⟩
  have h := riemannian_edist_le_on_convex_source g isOpen_univ hγ.contMDiffOn
    (_root_.Set.subset_univ _) (convex_Icc (-1 : ℝ) 2) hC had ha
  have hdist' : _root_.EDist.edist (a + d) a = _root_.EDist.edist θ η := by
    rw [edist_dist, edist_dist, hdist, Real.dist_eq, add_sub_cancel_left]
  simpa only [haη, hadθ, hdist'] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_riemannian_lipschitz_freeLoop_of_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_riemannian_lipschitz_freeLoop_of_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_riemannian_lipschitz_freeLoop_of_contMDiff ``Submission.DifferentialGeometry.Geometry.exists_riemannian_lipschitz_freeLoop_of_contMDiff

end DifferentialGeometry.Geometry

end

end
