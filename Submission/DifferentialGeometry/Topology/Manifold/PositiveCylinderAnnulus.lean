import Submission.DifferentialGeometry.Topology.Manifold.CylinderAnnulus
import Submission.DifferentialGeometry.Topology.SphereSeparation.PositiveProductFrontier
import Submission.DifferentialGeometry.Topology.Embedding.Factor
import Submission.DifferentialGeometry.Topology.Manifold.SmoothEmbeddingFromOpen

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.Submission.Function _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.Topology.Manifold

private abbrev S2 := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.S2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.S2 target :: scope.openDecls } }
private abbrev Pos : TopologicalSpace.Opens SphereCylinder :=
  ⟨univ ×ˢ _root_.Set.Ioi (0 : ℝ),isOpen_univ.prod isOpen_Ioi⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Pos
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Pos target :: scope.openDecls } }

theorem exists_smooth_positive_cylinder_lower_annulus
    (σ : S2 → Pos) (hσ : _root_.Manifold.IsSmoothEmbedding (𝓡 2) SphereCylinderModel ∞ σ)
    (p : SphereSeparation.ComplementPair (_root_.Set.range σ))
    (hleft : _root_.Set.range σ ⊆ closure p.left) (hright : _root_.Set.range σ ⊆ closure p.right)
    (hK : IsCompact (closure ((Subtype.val : Pos → SphereCylinder) '' p.left)))
    (a : ℝ) (ha : 0 < a) (hlow : ∀ q : Pos, q.val.2 < a → q ∈ p.left) :
    ∃ (e : PartialEquiv (S2 × unitInterval) SphereCylinder)
      (η : Diffeomorph (𝓡 2) (𝓡 2) S2 S2 ∞),
      e.source = _root_.Set.univ ∧ e.target = closure ((Subtype.val : Pos → SphereCylinder) '' p.left) ∧
      ContMDiff ((𝓡 2).prod (𝓡∂ 1)) SphereCylinderModel ∞ e ∧
      ContMDiffOn SphereCylinderModel ((𝓡 2).prod (𝓡∂ 1)) ∞ e.symm e.target ∧
      (∀ q : S2, e (q,0) = (q,0)) ∧ ∀ q : S2, e (η q,1) = (σ q).val := by
  let B := (Subtype.val : Pos → SphereCylinder) '' p.left
  have hi : interior (closure B) = B :=
    SphereSeparation.interior_closure_image_subtype_val_positive_product
      (p.interior_closure_left_eq hleft hright)
  have hBo : IsOpen B := Pos.isOpen.isOpenEmbedding_subtypeVal.isOpenMap _ p.isOpen_left
  have hreg : closure (interior (closure B)) = closure B := by rw [hi]
  have hconn : IsPreconnected (interior (closure B)) := by
    rw [hi]
    exact p.isConnected_left.isPreconnected.image Subtype.val continuous_subtype_val.continuousOn
  have hf : frontier (closure B) = _root_.Set.range (fun q : S2 => (σ q).val) ∪
      range (fun q : S2 => (q,(0 : ℝ))) := by
    rw [frontier,closure_closure,hi,← hBo.frontier_eq]
    change frontier ((Subtype.val : Pos → SphereCylinder) '' p.left) = _
    have h := SphereSeparation.frontier_image_subtype_val_positive_product p
      (p.frontier_left_eq hleft) a ha hlow
    rw [← _root_.Set.range_comp] at h
    convert h using 1 <;> rfl
  have hs : _root_.Manifold.IsSmoothEmbedding (𝓡 2) SphereCylinderModel ∞ (fun q : S2 => (σ q).val) :=
    isSmoothEmbedding_fromOpen (𝓡 2) SphereCylinderModel Pos σ hσ
  have hz : _root_.Manifold.IsSmoothEmbedding (𝓡 2) SphereCylinderModel ∞ (fun q : S2 => (q,(0 : ℝ))) := by
    have hid : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 2) ∞
        (Prod.fst ∘ fun q : S2 => (q,(0 : ℝ))) := IsSmoothEmbedding.id
    exact hid.of_comp (J := SphereCylinderModel) (by simp)
      (contMDiff_id.prodMk contMDiff_const) contMDiff_fst
  have hd : Disjoint (_root_.Set.range (fun q : S2 => (σ q).val))
      (_root_.Set.range (fun q : S2 => (q,(0 : ℝ)))) := by
    rw [_root_.Set.disjoint_left]
    rintro q ⟨x,hx⟩ ⟨y,hy⟩
    have h := congrArg Prod.snd (hx.trans hy.symm)
    exact (ne_of_gt (σ x).property.2) h
  obtain ⟨e,η,hes,het,he,hei,h₀,h₁⟩ := exists_smooth_cylinder_annulus_parametrization
    hK hreg hconn _ _ hz hs (hf.trans (_root_.Set.union_comm _ _)) hd.symm
  exact ⟨e,η,hes,het,he,het.symm ▸ hei,h₀,h₁⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.exists_smooth_positive_cylinder_lower_annulus then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.exists_smooth_positive_cylinder_lower_annulus"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.exists_smooth_positive_cylinder_lower_annulus ``Submission.DifferentialGeometry.Topology.Manifold.exists_smooth_positive_cylinder_lower_annulus

end DifferentialGeometry.Topology.Manifold
