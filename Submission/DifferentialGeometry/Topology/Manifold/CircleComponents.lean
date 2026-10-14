import Submission.DifferentialGeometry.Topology.Flow.Circle
import Submission.DifferentialGeometry.Topology.VectorField.OpenRestriction
import Submission.DifferentialGeometry.Topology.Manifold.LocalDiffeomorphImmersion
import Submission.DifferentialGeometry.Topology.Manifold.SmoothEmbeddingComposition
import Mathlib.Topology.Connected.LocallyConnected

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Manifold _root_.Submission.Manifold
open scoped _root_.ContDiff

namespace DifferentialGeometry.Topology.Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless] [IsManifold I ∞ M]
  [T2Space M] [CompactSpace M]

theorem exists_circle_embedding_connectedComponent
    (hdim : Module.finrank ℝ E = 1)
    (V : (x : M) → TangentSpace I x)
    (hV : ContMDiff I I.tangent ∞ (fun x => (⟨x, V x⟩ : TangentBundle I M)))
    (hne : ∀ x, V x ≠ 0) (x : M) :
    ∃ γ : AddCircle (1 : ℝ) → M,
      IsSmoothEmbedding 𝓘(ℝ, ℝ) I ∞ γ ∧ _root_.Set.range γ = connectedComponent x := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let : LocallyConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyConnectedSpace
  let : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace H M
  let U : TopologicalSpace.Opens M := ⟨connectedComponent x, isOpen_connectedComponent⟩
  let : CompactSpace U := isCompact_iff_compactSpace.mp isClosed_connectedComponent.isCompact
  let : ConnectedSpace U := isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  have hW := DifferentialGeometry.VectorField.contMDiff_tangentSection_restrict_opens
    U hV.contMDiffOn
  obtain ⟨D⟩ := DifferentialGeometry.Topology.Flow.exists_addCircle_diffeomorph_of_nonvanishing_vectorField
    hdim (fun y : U => V y.val) hW (fun y => hne y.val)
  have hD := isSmoothEmbedding_of_isLocalDiffeomorph_of_injective
    D.isLocalDiffeomorph D.injective
  refine ⟨Subtype.val ∘ D, (IsSmoothEmbedding.of_opens U).comp hD (by simp), ?_⟩
  have hsurj : _root_.Set.range (D : AddCircle (1 : ℝ) → U) = univ := D.surjective.range_eq
  rw [_root_.Set.range_comp, hsurj, _root_.Set.image_univ, Subtype.range_coe_subtype]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.exists_circle_embedding_connectedComponent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.exists_circle_embedding_connectedComponent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.exists_circle_embedding_connectedComponent ``Submission.DifferentialGeometry.Topology.Manifold.exists_circle_embedding_connectedComponent

theorem exists_circle_embeddings_components
    (hdim : Module.finrank ℝ E = 1)
    (V : (x : M) → TangentSpace I x)
    (hV : ContMDiff I I.tangent ∞ (fun x => (⟨x, V x⟩ : TangentBundle I M)))
    (hne : ∀ x, V x ≠ 0) :
    Finite (ConnectedComponents M) ∧
      ∃ γ : ConnectedComponents M → AddCircle (1 : ℝ) → M,
        (∀ C, _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) I ∞ (γ C)) ∧
        ∀ C, _root_.Set.range (γ C) = {x | ConnectedComponents.mk x = C} := by
  let : LocallyConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyConnectedSpace
  let : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace H M
  refine ⟨inferInstance, ?_⟩
  have h (C : ConnectedComponents M) : ∃ γ : AddCircle (1 : ℝ) → M,
      IsSmoothEmbedding 𝓘(ℝ, ℝ) I ∞ γ ∧ _root_.Set.range γ = {x | ConnectedComponents.mk x = C} := by
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe C
    obtain ⟨γ, hγ, hrange⟩ := exists_circle_embedding_connectedComponent hdim V hV hne x
    refine ⟨γ, hγ, hrange.trans ?_⟩
    ext y
    exact ConnectedComponents.coe_eq_coe'.symm
  choose γ hγ hrange using h
  exact ⟨γ, hγ, hrange⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.exists_circle_embeddings_components then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.exists_circle_embeddings_components"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.exists_circle_embeddings_components ``Submission.DifferentialGeometry.Topology.Manifold.exists_circle_embeddings_components

end DifferentialGeometry.Topology.Manifold
