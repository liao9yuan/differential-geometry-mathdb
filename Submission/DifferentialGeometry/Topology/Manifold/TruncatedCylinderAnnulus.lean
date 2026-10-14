import Submission.DifferentialGeometry.Topology.Manifold.PositiveCylinderAnnulus
import Submission.DifferentialGeometry.Topology.SphereSeparation.PositiveProductTruncation

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

theorem exists_smooth_truncated_positive_cylinder_lower_annulus
    (σ : S2 → Pos) (hσ : _root_.Manifold.IsSmoothEmbedding (𝓡 2) SphereCylinderModel ∞ σ)
    (p : SphereSeparation.ComplementPair (_root_.Set.range σ))
    (hleft : _root_.Set.range σ ⊆ closure p.left) (hright : _root_.Set.range σ ⊆ closure p.right)
    (hK : IsCompact (closure ((Subtype.val : Pos → SphereCylinder) '' p.left)))
    {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hlow : ∀ q : Pos, q.val.2 < b → q ∈ p.left)
    (hdepth : ∀ q : S2, b < (σ q).val.2) :
    ∃ (e : PartialEquiv (S2 × unitInterval) SphereCylinder)
      (η : Diffeomorph (𝓡 2) (𝓡 2) S2 S2 ∞),
      e.source = _root_.Set.univ ∧
      e.target = closure ((Subtype.val : Pos → SphereCylinder) '' p.left) ∩ (_root_.Set.univ ×ˢ _root_.Set.Ici a) ∧
      ContMDiff ((𝓡 2).prod (𝓡∂ 1)) SphereCylinderModel ∞ e ∧
      ContMDiffOn SphereCylinderModel ((𝓡 2).prod (𝓡∂ 1)) ∞ e.symm e.target ∧
      (∀ q : S2, e (q,0) = (q,a)) ∧ ∀ q : S2, e (η q,1) = (σ q).val := by
  let : ConnectedSpace S2 := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num)
      (0 : EuclideanSpace ℝ (Fin 3)) (by norm_num : (0 : ℝ) ≤ 1))
  let B := (Subtype.val : Pos → SphereCylinder) '' p.left
  let K := closure B ∩ (_root_.Set.univ ×ˢ _root_.Set.Ici a)
  have hBo : IsOpen B := Pos.isOpen.isOpenEmbedding_subtypeVal.isOpenMap _ p.isOpen_left
  have hiB : interior (closure B) = B :=
    SphereSeparation.interior_closure_image_subtype_val_positive_product
      (p.interior_closure_left_eq hleft hright)
  have hband : _root_.Set.univ ×ˢ _root_.Set.Ioo (0 : ℝ) b ⊆ B := by
    intro q hq
    exact ⟨⟨q,_root_.Set.mem_univ _,hq.2.1⟩,hlow _ hq.2.2,rfl⟩
  have hKi : interior K = B ∩ (_root_.Set.univ ×ˢ _root_.Set.Ioi a) := by
    rw [show K = closure B ∩ (_root_.Set.univ ×ˢ _root_.Set.Ici a) from rfl,interior_inter,hiB,
      interior_prod_eq,interior_univ,interior_Ici]
  have hKr : closure (interior K) = K := by
    rw [hKi]
    exact SphereSeparation.closure_inter_positive_product_tail ha hab hband
  have hKconn : IsPreconnected (interior K) := by
    rw [hKi]
    exact SphereSeparation.isPreconnected_inter_positive_product_tail
      (p.isConnected_left.isPreconnected.image Subtype.val continuous_subtype_val.continuousOn) ha hab hband
  have hKc : IsCompact K := hK.inter_right (isClosed_univ.prod isClosed_Ici)
  have hfB : frontier B = _root_.Set.range (fun q : S2 => (σ q).val) ∪
      range (fun q : S2 => (q,(0 : ℝ))) := by
    have h := SphereSeparation.frontier_image_subtype_val_positive_product p
      (p.frontier_left_eq hleft) b (ha.trans hab) hlow
    rw [← _root_.Set.range_comp] at h
    convert h using 1 <;> rfl
  have hfK : frontier K = _root_.Set.range (fun q : S2 => (σ q).val) ∪
      range (fun q : S2 => (q,a)) := by
    rw [frontier,hKc.isClosed.closure_eq,hKi]
    ext q
    constructor
    · rintro ⟨⟨hqB,hqa⟩,hqn⟩
      rcases (show a ≤ q.2 from hqa.2).eq_or_lt with hqa | hqa
      · exact Or.inr ⟨q.1,Prod.ext rfl hqa⟩
      · have hqnot : q ∉ B := fun hq => hqn ⟨hq,_root_.Set.mem_univ _,hqa⟩
        have hfq : q ∈ frontier B := by rw [hBo.frontier_eq]; exact ⟨hqB,hqnot⟩
        rw [hfB] at hfq
        rcases hfq with hS | ⟨x,hx⟩
        · exact Or.inl hS
        · have h := congrArg Prod.snd hx
          exfalso
          change 0 = q.2 at h
          linarith
    · rintro (⟨x,rfl⟩ | ⟨x,rfl⟩)
      · have hσcl : (σ x).val ∈ closure B :=
          image_closure_subset_closure_image continuous_subtype_val ⟨σ x,hleft (_root_.Set.mem_range_self x),rfl⟩
        refine ⟨⟨hσcl,_root_.Set.mem_univ _,(hab.trans (hdepth x)).le⟩,?_⟩
        rintro ⟨⟨z,hz,hzx⟩,_⟩
        exact p.left_disjoint_sphere.le_bot ⟨(Subtype.val_injective hzx) ▸ hz,_root_.Set.mem_range_self x⟩
      · refine ⟨⟨subset_closure (hband ⟨mem_univ _,ha,hab⟩),_root_.Set.mem_univ _,show a ≤ a from le_rfl⟩,?_⟩
        exact fun h => (lt_irrefl a) h.2.2
  have hs : _root_.Manifold.IsSmoothEmbedding (𝓡 2) SphereCylinderModel ∞ (fun q : S2 => (σ q).val) :=
    isSmoothEmbedding_fromOpen (𝓡 2) SphereCylinderModel Pos σ hσ
  have hz : _root_.Manifold.IsSmoothEmbedding (𝓡 2) SphereCylinderModel ∞ (fun q : S2 => (q,a)) := by
    have hid : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 2) ∞
        (Prod.fst ∘ fun q : S2 => (q,a)) := IsSmoothEmbedding.id
    exact hid.of_comp (J := SphereCylinderModel) (by simp)
      (contMDiff_id.prodMk contMDiff_const) contMDiff_fst
  have hd : Disjoint (_root_.Set.range (fun q : S2 => (σ q).val)) (_root_.Set.range (fun q : S2 => (q,a))) := by
    rw [_root_.Set.disjoint_left]
    rintro q ⟨x,hx⟩ ⟨y,hy⟩
    have h := congrArg Prod.snd (hx.trans hy.symm)
    change (σ x).val.2 = a at h
    linarith [hdepth x]
  obtain ⟨e,η,hes,het,he,hei,h₀,h₁⟩ := exists_smooth_cylinder_annulus_parametrization
    hKc hKr hKconn _ _ hz hs (hfK.trans (_root_.Set.union_comm _ _)) hd.symm
  exact ⟨e,η,hes,het,he,het.symm ▸ hei,h₀,h₁⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.exists_smooth_truncated_positive_cylinder_lower_annulus then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.exists_smooth_truncated_positive_cylinder_lower_annulus"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.exists_smooth_truncated_positive_cylinder_lower_annulus ``Submission.DifferentialGeometry.Topology.Manifold.exists_smooth_truncated_positive_cylinder_lower_annulus

end DifferentialGeometry.Topology.Manifold
