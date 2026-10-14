import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.SmoothExtension
import Submission.DifferentialGeometry.Topology.Manifold.OpenTarget

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission








noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry _root_.Set _root_.Filter _root_.ContinuousMap
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]




theorem SmoothDiskExtension.exists_open_corestriction
    (N : TopologicalSpace.Opens M) {u : C(closedDisk, N)} {U : ℂ → M}
    (h : SmoothDiskExtension (E := E)
      ((⟨Subtype.val, continuous_subtype_val⟩ : C(N, M)).comp u) U) :
    ∃ V : ℂ → N, SmoothDiskExtension (E := E) u V ∧
      ∀ z ∈ Metric.closedBall (0 : ℂ) 1, (Subtype.val ∘ V) =ᶠ[𝓝 z] U := by
  classical
  obtain ⟨hval, S, hS, hDS, hU⟩ := h
  let V : ℂ → N := fun z => if hz : U z ∈ N then ⟨U z, hz⟩ else u (diskBoundary 0)
  let T := S ∩ U ⁻¹' (N : Set M)
  have hT : IsOpen T := hU.continuousOn.isOpen_inter_preimage hS N.isOpen
  have hDT : Metric.closedBall (0 : ℂ) 1 ⊆ T := by
    intro z hz
    refine ⟨hDS hz, ?_⟩
    change U z ∈ N
    rw [hval ⟨z, hz⟩]
    exact (u ⟨z, hz⟩).property
  have heq : _root_.Set.EqOn (Subtype.val ∘ V) U T := by
    intro z hz
    dsimp only [Function.comp_apply, V]
    rw [dif_pos (show U z ∈ N from hz.2)]
  refine ⟨V, ⟨?_, T, hT, hDT, ?_⟩, ?_⟩
  · intro z
    apply Subtype.ext
    exact (heq (hDT z.property)).trans (hval z)
  · intro z hz
    apply (contMDiffWithinAt_subtypeVal_comp_iff N V T z).mp
    exact ((hU.mono _root_.Set.inter_subset_left) z hz).congr heq (heq hz)
  · intro z hz
    exact Filter.eventuallyEq_of_mem (hT.mem_nhds (hDT hz)) heq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.SmoothDiskExtension.exists_open_corestriction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.SmoothDiskExtension.exists_open_corestriction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.SmoothDiskExtension.exists_open_corestriction ``Submission.DifferentialGeometry.Geometry.SmoothDiskExtension.exists_open_corestriction

end DifferentialGeometry.Geometry
