import Submission.DifferentialGeometry.Topology.LoopSpace.Regular
import Submission.DifferentialGeometry.Geometry.Metric.NeighborhoodRetraction
import Submission.DifferentialGeometry.Analysis.Calculus.IteratedDerivative.Families

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission









noncomputable section

open _root_.Set _root_.Function _root_.ContinuousMap _root_.Manifold
open scoped _root_.Topology _root_.ContDiff _root_.Manifold

namespace DifferentialGeometry.Topology

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [Nonempty M]



theorem continuous_regularLoopTopology_change (e : M → F)
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ e) (hemb : _root_.Topology.IsEmbedding e)
    (hi : ∀ p, _root_.Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) e p))
    (a : M → G) (ha : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, G) 1 a) :
    Continuous[regularLoopTopology e (he.of_le (by exact_mod_cast le_top)),
      regularLoopTopology a ha] id := by
  let he₁ := he.of_le (show (1 : ℕ∞ω) ≤ ∞ by exact_mod_cast le_top)
  let : TopologicalSpace (regularLoop E M) := regularLoopTopology e he₁
  obtain ⟨r, U, hU, heU, hr, hleft⟩ :=
    DifferentialGeometry.Geometry.exists_smooth_neighborhood_retraction he hemb hi
  obtain ⟨hv, hd⟩ := (continuous_regularLoop_iff e he₁ id).mp continuous_id
  have hreal : Continuous (fun p : regularLoop E M × ℝ => e (p.1.val (p.2 : loopCircle))) :=
    hv.comp (continuous_fst.prodMk ((AddCircle.continuous_mk' (1 : ℝ)).comp continuous_snd))
  have har : ContDiffOn ℝ 1 (a ∘ r) U :=
    (ha.comp_contMDiffOn (hr.of_le (by exact_mod_cast le_top))).contDiffOn
  have heq (γ : regularLoop E M) (θ : loopCircle) :
      a (γ.val θ) = (a ∘ r) (e (γ.val θ)) := by rw [_root_.Function.comp_apply, hleft]
  apply (continuous_regularLoop_iff a ha id).mpr
  constructor
  · simp only [id_eq]
    simp_rw [heq]
    exact har.continuousOn.comp_continuous hv (fun p => heU (_root_.Set.mem_range_self _))
  · simp only [id_eq]
    simp_rw [heq]
    exact DifferentialGeometry.Analysis.continuous_deriv_family_comp hU har
      (fun γ => (regularLoop_embedded_contDiff e he₁ γ).differentiable one_ne_zero)
      hreal hd (fun p => heU (_root_.Set.mem_range_self _))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.continuous_regularLoopTopology_change then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.continuous_regularLoopTopology_change"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.continuous_regularLoopTopology_change ``Submission.DifferentialGeometry.Topology.continuous_regularLoopTopology_change



theorem regularLoopTopology_eq [FiniteDimensional ℝ G]
    (e : M → F) (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ e)
    (hemb : _root_.Topology.IsEmbedding e)
    (hi : ∀ p, _root_.Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) e p))
    (a : M → G) (ha : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, G) ∞ a)
    (hamb : _root_.Topology.IsEmbedding a)
    (hai : ∀ p, _root_.Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, G) a p)) :
    regularLoopTopology e (he.of_le (by exact_mod_cast le_top)) =
      regularLoopTopology a (ha.of_le (by exact_mod_cast le_top)) := by
  apply le_antisymm
  · exact continuous_id_iff_le.mp
      (continuous_regularLoopTopology_change e he hemb hi a (ha.of_le (by exact_mod_cast le_top)))
  · exact continuous_id_iff_le.mp
      (continuous_regularLoopTopology_change a ha hamb hai e (he.of_le (by exact_mod_cast le_top)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.regularLoopTopology_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.regularLoopTopology_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.regularLoopTopology_eq ``Submission.DifferentialGeometry.Topology.regularLoopTopology_eq

end DifferentialGeometry.Topology
