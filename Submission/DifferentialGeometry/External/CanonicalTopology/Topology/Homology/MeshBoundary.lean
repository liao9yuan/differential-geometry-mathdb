import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.AffineMesh

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-! # The original boundary preserves actual affine mesh -/

noncomputable section

open _root_.CategoryTheory _root_.Set _root_.Module

universe u

namespace DifferentialGeometry.Topology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Deleting original vertices cannot enlarge the actual diameter, so the
same original singular boundary preserves the specified affine mesh. -/
theorem affineSingularMesh_boundary (n : ℕ) (A : Set E) (δ : ℝ)
    {c : (integralSingularChains E).X (n + 1)} (hc : c ∈ affineSingularMesh (n + 1) A δ) :
    (integralSingularChains E).d (n + 1) n c ∈ affineSingularMesh n A δ := by
  have h : affineSingularMesh (n + 1) A δ ≤
      Submodule.comap ((integralSingularChains E).d (n + 1) n).hom (affineSingularMesh n A δ) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨v, hv, hd, rfl⟩
    change (integralSingularChains E).d (n + 1) n (affineSingularChain (n + 1) v) ∈
      affineSingularMesh n A δ
    rw [affineSingularChain_boundary]
    apply Submodule.sum_mem
    intro i _
    apply (affineSingularMesh n A δ).toAddSubgroup.zsmul_mem
    apply affineSingularMesh_generator n A δ (v ∘ i.succAbove) (fun j => hv _)
    apply le_trans _ hd
    apply Metric.diam_mono _ (_root_.Set.finite_range v).isBounded
    rintro _ ⟨j, rfl⟩
    exact ⟨i.succAbove j, rfl⟩
  exact h hc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.affineSingularMesh_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.affineSingularMesh_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.affineSingularMesh_boundary ``Submission.DifferentialGeometry.Topology.affineSingularMesh_boundary

end DifferentialGeometry.Topology
