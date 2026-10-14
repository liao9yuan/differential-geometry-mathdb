import Submission.DifferentialGeometry.Topology.Embedding.Stereographic
import Submission.DifferentialGeometry.Topology.Embedding.FiniteDimension
import Submission.DifferentialGeometry.Topology.Attachment.Basic
import Submission.DifferentialGeometry.Topology.PlanarJordan.SmoothSchoenflies
import Submission.DifferentialGeometry.Topology.Handle.SphereComplement

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Submission.Set _root_.Metric _root_.Submission.Metric _root_.Manifold _root_.Submission.Manifold
open scoped _root_.ContDiff _root_.Submission.ContDiff _root_.Manifold _root_.Submission.Manifold
namespace DifferentialGeometry.Topology.Handle

attribute [local instance] closedCellChartedSpaceSucc closedCellIsManifold

theorem exists_isSmoothEmbedding_closedCell_sphere_of_circle
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fact (Module.finrank ℝ E = 2 + 1)]
    {f : AddCircle (1 : ℝ) → Metric.sphere (0 : E) 1}
    (hf : _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) (𝓡 2) ∞ f) :
    ∃ b : ClosedCell 2 → Metric.sphere (0 : E) 1,
      _root_.Manifold.IsSmoothEmbedding (𝓡∂ 2) (𝓡 2) ∞ b ∧
      range (b ∘ cellBoundaryInclusion 2) = _root_.Set.range f := by
  obtain ⟨p, hp⟩ := not_forall.mp (hf.not_surjective_of_finrank_ne (by simp)
    (by simp : Module.finrank ℝ ℝ ≠ Module.finrank ℝ (EuclideanSpace ℝ (Fin 2))))
  have hpf : p ∉ _root_.Set.range f := hp
  let c := stereographic' 2 p
  have hfc := hf.stereographic_comp p hpf
  obtain ⟨Φ, hΦ, _, _⟩ := PlanarJordan.smooth_schoenflies hfc
  let b : ClosedCell 2 → Metric.sphere (0 : E) 1 := fun x => c.symm (Φ x.val)
  have hb : _root_.Manifold.IsSmoothEmbedding (𝓡∂ 2) (𝓡 2) ∞ b := by
    have hi := (closedCellInclusion_isSmoothEmbedding 1).diffeomorph_comp Φ
    exact ⟨hi.isImmersion.isLocalDiffeomorphOn_comp
      (fun x => DifferentialGeometry.Topology.Manifold.stereographicInverse_isLocalDiffeomorph p x.val),
      (c.symm.isOpenEmbedding (by simp [c])).isEmbedding.comp hi.isEmbedding⟩
  refine ⟨b, hb, ?_⟩
  have hboundary : _root_.Set.range ((Subtype.val : ClosedCell 2 → EuclideanSpace ℝ (Fin 2)) ∘
      cellBoundaryInclusion 2) = _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := range_cellBoundary 2
  have hleft : ∀ x, c.symm (c (f x)) = f x := by
    intro x
    apply c.left_inv
    simp only [c, stereographic'_source, _root_.Set.mem_compl_iff, _root_.Set.mem_singleton_iff]
    exact fun h => hp ⟨x, h⟩
  change _root_.Set.range ((c.symm ∘ Φ) ∘ ((Subtype.val : ClosedCell 2 → EuclideanSpace ℝ (Fin 2)) ∘
    cellBoundaryInclusion 2)) = _root_.Set.range f
  rw [_root_.Set.range_comp, hboundary, _root_.Set.image_comp, hΦ, ← _root_.Set.range_comp]
  congr 1
  exact funext hleft

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.exists_isSmoothEmbedding_closedCell_sphere_of_circle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.exists_isSmoothEmbedding_closedCell_sphere_of_circle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.exists_isSmoothEmbedding_closedCell_sphere_of_circle ``Submission.DifferentialGeometry.Topology.Handle.exists_isSmoothEmbedding_closedCell_sphere_of_circle

private local instance _root_.Submission.DifferentialGeometry.Topology.Handle.instFactEqNatFinrankRealEuclideanSpaceFinOfNatHAdd_differentialGeometry : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Handle.instFactEqNatFinrankRealEuclideanSpaceFinOfNatHAdd_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Handle.instFactEqNatFinrankRealEuclideanSpaceFinOfNatHAdd_differentialGeometry target :: scope.openDecls } }

theorem exists_two_smooth_disks_sphere_of_circle
    {f : AddCircle (1 : ℝ) → Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1}
    (hf : _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) (𝓡 2) ∞ f) :
    ∃ b₀ b₁ : ClosedCell 2 → Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
      _root_.Manifold.IsSmoothEmbedding (𝓡∂ 2) (𝓡 2) ∞ b₀ ∧ _root_.Manifold.IsSmoothEmbedding (𝓡∂ 2) (𝓡 2) ∞ b₁ ∧
      _root_.Set.range (b₀ ∘ cellBoundaryInclusion 2) = _root_.Set.range f ∧
      _root_.Set.range (b₁ ∘ cellBoundaryInclusion 2) = _root_.Set.range f ∧
      range b₀ ∪ _root_.Set.range b₁ = _root_.Set.univ ∧ _root_.Set.range b₀ ∩ _root_.Set.range b₁ = _root_.Set.range f := by
  obtain ⟨b₀, hb₀, hf₀⟩ := exists_isSmoothEmbedding_closedCell_sphere_of_circle hf
  obtain ⟨b₁, hb₁, himage⟩ := exists_isSmoothEmbedding_closedCell_complement_sphere 1 hb₀
  have hclosed : IsClosed (_root_.Set.range b₀) := (isCompact_range hb₀.isEmbedding.continuous).isClosed
  have hfrontier : frontier (_root_.Set.range b₀) = _root_.Set.range f :=
    (frontier_range_closedCell_sphere 1 hb₀).trans hf₀
  have hfrontier₁ : frontier (_root_.Set.range b₁) = frontier (_root_.Set.range b₀) := by
    rw [himage, closure_compl, frontier_compl]
    simp only [frontier, closure_interior_range_closedCell_sphere 1 hb₀,
      interior_interior, hclosed.closure_eq]
  refine ⟨b₀, b₁, hb₀, hb₁, hf₀,
    (frontier_range_closedCell_sphere 1 hb₁).symm.trans (hfrontier₁.trans hfrontier), ?_, ?_⟩
  · rw [himage]
    apply _root_.Set.eq_univ_of_forall
    intro x
    by_cases hx : x ∈ _root_.Set.range b₀
    · exact Or.inl hx
    · exact Or.inr (subset_closure hx)
  · rw [himage, closure_compl, ← hfrontier, frontier, hclosed.closure_eq]
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.exists_two_smooth_disks_sphere_of_circle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.exists_two_smooth_disks_sphere_of_circle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.exists_two_smooth_disks_sphere_of_circle ``Submission.DifferentialGeometry.Topology.Handle.exists_two_smooth_disks_sphere_of_circle


end DifferentialGeometry.Topology.Handle
