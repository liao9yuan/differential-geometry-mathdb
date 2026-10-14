import Submission.DifferentialGeometry.Geometry.Metric.NeighborhoodRetraction
import Submission.DifferentialGeometry.Analysis.Calculus.Compactness.Lipschitz
import Submission.DifferentialGeometry.Topology.Manifold.AddCircle.Circle
import Submission.DifferentialGeometry.Topology.LoopSpace.CircleMetric
import Mathlib.Topology.MetricSpace.Antilipschitz

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Manifold _root_.Set
open scoped _root_.Manifold _root_.ContDiff _root_.NNReal _root_.ENNReal

namespace DifferentialGeometry.Topology

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_antilipschitzWith_of_smooth_loop_embedding [FiniteDimensional ℝ F]
    {Γ : loopCircle → F} (hΓ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, F) ∞ Γ)
    (hemb : _root_.Topology.IsEmbedding Γ)
    (himm : ∀ θ, Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) Γ θ)) :
    ∃ L : ℝ≥0, AntilipschitzWith L Γ := by
  obtain ⟨r, U, hU, hΓU, hr, hleft⟩ :=
    DifferentialGeometry.Geometry.exists_smooth_neighborhood_retraction hΓ hemb himm
  let e : loopCircle → ℂ := fun θ => (AddCircle.diffeomorphCircle θ : ℂ)
  have he : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ e := by
    let : Fact (Module.finrank ℝ ℂ = 1 + 1) := ⟨by simp⟩
    exact (contMDiff_coe_sphere (E := ℂ) (n := 1)).comp
      AddCircle.diffeomorphCircle.contMDiff
  have hc : ContDiffOn ℝ 1 (e ∘ r) U :=
    (he.comp_contMDiffOn hr).contDiffOn.of_le (by simp)
  obtain ⟨L, hL⟩ := hc.exists_lipschitzOnWith_of_isCompact hU
    (isCompact_range hΓ.continuous) hΓU
  have hparam (x y : loopCircle) : _root_.Dist.dist x y ≤ _root_.Dist.dist (e x) (e y) := by
    have h := circle_parameter_lipschitz.dist_le_mul
      (AddCircle.diffeomorphCircle x) (AddCircle.diffeomorphCircle y)
    have hi (θ : loopCircle) :
        (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm
          (AddCircle.diffeomorphCircle θ) = θ :=
      (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm_apply_apply θ
    have hd : _root_.Dist.dist (AddCircle.diffeomorphCircle x) (AddCircle.diffeomorphCircle y) =
        dist (e x) (e y) := rfl
    simpa only [hi, NNReal.coe_one, one_mul, hd] using h
  refine ⟨L, AntilipschitzWith.of_le_mul_dist fun x y => ?_⟩
  apply (hparam x y).trans
  have h := hL.dist_le_mul (Γ x) (_root_.Set.mem_range_self x) (Γ y) (_root_.Set.mem_range_self y)
  simpa only [Function.comp_apply, hleft] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_antilipschitzWith_of_smooth_loop_embedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_antilipschitzWith_of_smooth_loop_embedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_antilipschitzWith_of_smooth_loop_embedding ``Submission.DifferentialGeometry.Topology.exists_antilipschitzWith_of_smooth_loop_embedding

end DifferentialGeometry.Topology

end
