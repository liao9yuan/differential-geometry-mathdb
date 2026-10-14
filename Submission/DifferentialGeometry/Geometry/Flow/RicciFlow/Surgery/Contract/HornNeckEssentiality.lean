import Submission.DifferentialGeometry.Topology.SphereSeparation.ProductEnds
import Submission.DifferentialGeometry.Topology.SphereSeparation.Transport
import Submission.DifferentialGeometry.Topology.Covering.CylindricalModel
import Submission.DifferentialGeometry.Topology.SphereSeparation.BicollarComponents
import Submission.DifferentialGeometry.Topology.SphereSeparation.BicollarLineReparametrization
import Submission.DifferentialGeometry.Geometry.Neck.OpenImageCompactSide
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.HornNeckCoordinates
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NeckSpatialBridge
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.HornComponents

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open _root_.Submission.DifferentialGeometry.Topology.SphereSeparation

universe u

private theorem positiveHornMap_range
    {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ)
    (c : ConnectedComponents D.slab.terminalRegularOpen) (e : P.hornIndex c) :
    range (P.positiveHornMap c e) = P.horn c e '' (_root_.Set.univ ×ˢ _root_.Set.Ioi (0:ℝ)) := by
  ext x
  constructor
  · rintro ⟨q,rfl⟩
    exact ⟨q.val,q.property,rfl⟩
  · rintro ⟨q,hq,rfl⟩
    exact ⟨⟨q,hq⟩,rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.positiveHornMap_range
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.positiveHornMap_range target :: scope.openDecls } }

theorem exists_horn_normalized_neck_compact_side_exclusion_tolerance :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ),
        ε ≤ eta → ∀ (c : ConnectedComponents D.slab.terminalRegularOpen) (e : P.hornIndex c)
          {δ : ℝ} {k : ℕ} (N : NormalizedNeck D.terminal.metric δ k),
          δ ≤ ε → ⌈ε⁻¹⌉₊ ≤ k →
          ∀ S : Set positiveHornDomain,
            P.positiveHornMap c e '' S = _root_.Set.range (fun q : Sphere 2 => N.chart ⟨(q,0),by
              have hp := inv_pos.mpr N.delta_pos
              constructor <;> linarith⟩) →
            ¬ Nonempty (SphereSides S) := by
  obtain ⟨eta,heta,hexclude⟩ := exists_spatial_neck_open_image_side_exclusion_tolerance
  refine ⟨min eta (1/12),lt_min heta (by norm_num),?_⟩
  intro D ε Λ P hε c e δ k N hδ hk S hS
  have hsmall : ε < 1/11 := lt_of_le_of_lt (hε.trans (min_le_right _ _)) (by norm_num)
  obtain ⟨nk,_,hmap⟩ := N.exists_spatialNeck hδ hsmall hk
  have hzero (q : Sphere 2) : (q,(0:ℝ)) ∈ neckBuffer δ := by
    have hp := inv_pos.mpr N.delta_pos
    constructor <;> linarith
  have hcenters : _root_.Set.range (fun q : Sphere 2 => nk.map (q,0)) =
      range (fun q : Sphere 2 => N.chart ⟨(q,0),hzero q⟩) := by
    congr 1
    funext q
    exact hmap ⟨(q,0),hzero q⟩
  let : ConnectedSpace (Sphere 2) := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp [ThreeSpace]))
      (0 : ThreeSpace) (by norm_num : (0 : ℝ) ≤ 1))
  let : ConnectedSpace positiveHornDomain :=
    Subtype.connectedSpace (isConnected_univ.prod isConnected_Ioi)
  have hf : _root_.Topology.IsOpenEmbedding (P.positiveHornMap c e) :=
    .of_continuous_injective_isOpenMap (P.horn_interior_embedding c e).contMDiff.continuous
      (P.horn_interior_embedding c e).isEmbedding.injective (P.positiveHornMap_local c e).isOpenMap
  have hall : ∀ x ∈ _root_.Set.range (P.positiveHornMap c e), Nonempty (SpatialNeck D.terminal.metric ε x) := by
    intro x hx
    have hxpos : x ∈ P.horn c e '' (_root_.Set.univ ×ˢ _root_.Set.Ioi (0:ℝ)) := positiveHornMap_range P c e ▸ hx
    have hin : x ∈ interior (_root_.Set.range (fun q : HalfNeckCylinder => P.horn c e q.val)) := by
      apply (P.isOpen_positive_horn c e).subset_interior_iff.mpr ?_ hxpos
      rintro y ⟨q,hq,rfl⟩
      exact ⟨⟨q,hq.2.le⟩,rfl⟩
    obtain ⟨δ',k',N',hc,hδ',hk'⟩ := P.horn_spatial_neck c e x hin
    obtain ⟨nx,_,_⟩ := N'.exists_spatialNeck hδ' hsmall
      ((Nat.ceil_le_floor_add_one ε⁻¹).trans hk')
    exact hc ▸ ⟨nx⟩
  have hpc : N.center ∈ _root_.Set.range (P.positiveHornMap c e) := by
    apply _root_.Set.image_subset_range (P.positiveHornMap c e) S
    rw [hS,← hcenters]
    exact ⟨nk.center,nk.center_eq⟩
  have hrange := (isConnected_range hf.continuous).isPreconnected.subset_connectedComponent hpc
  have hnc : ¬ IsCompact (connectedComponent N.center) := by
    intro hc
    apply P.not_isCompact_closure_positive_horn c e
    rw [← positiveHornMap_range P c e]
    exact hc.of_isClosed_subset isClosed_closure (closure_minimal hrange isClosed_connectedComponent)
  exact hexclude ε (hε.trans (min_le_left _ _)) positiveHornDomain D.slab.terminalRegularOpen
    D.terminal.metric N.center nk (P.positiveHornMap c e) hf hall hnc S (hS.trans hcenters.symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_horn_normalized_neck_compact_side_exclusion_tolerance then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_horn_normalized_neck_compact_side_exclusion_tolerance"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_horn_normalized_neck_compact_side_exclusion_tolerance ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_horn_normalized_neck_compact_side_exclusion_tolerance

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open _root_.Submission.DifferentialGeometry.Topology.SphereSeparation
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

private def hornLineHomeomorph : NeckCylinder ≃ₜ positiveHornDomain where
  toFun q := ⟨(q.1,Real.exp q.2),_root_.Set.mem_univ _,Real.exp_pos _⟩
  invFun q := (q.val.1,Real.log q.val.2)
  left_inv q := by simp only [Real.log_exp]
  right_inv q := by apply Subtype.ext; simp only [Real.exp_log q.property.2]
  continuous_toFun := (continuous_fst.prodMk (Real.continuous_exp.comp continuous_snd)).subtype_mk _
  continuous_invFun := (continuous_fst.comp continuous_subtype_val).prodMk
    ((continuous_snd.comp continuous_subtype_val).log (fun q => ne_of_gt q.property.2))

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hornLineHomeomorph
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hornLineHomeomorph target :: scope.openDecls } }

private def neckLineHomeomorph (δ : ℝ) (hδ : 0 < δ) : NeckCylinder ≃ₜ neckCentralOpen δ :=
  (bicollarLineHomeomorph δ⁻¹ (inv_pos.mpr hδ)).trans
    (Homeomorph.setCongr (by ext q; simp only [neckCentralOpen,
      TopologicalSpace.Opens.coe_mk, _root_.Set.mem_prod, _root_.Set.mem_univ, true_and, _root_.Set.mem_Ioo]; rfl))

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.neckLineHomeomorph
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.neckLineHomeomorph target :: scope.openDecls } }

private theorem neckLineHomeomorph_center (δ : ℝ) (hδ : 0 < δ) (q : Sphere 2) :
    (neckLineHomeomorph δ hδ (q,0)).val = (q,0) :=
  bicollarLineHomeomorph_center δ⁻¹ (inv_pos.mpr hδ) q

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.neckLineHomeomorph_center
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.neckLineHomeomorph_center target :: scope.openDecls } }

universe u

theorem exists_horn_neck_end_separation_tolerance :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ),
        ε ≤ eta → ∀ (c : ConnectedComponents D.slab.terminalRegularOpen) (e : P.hornIndex c)
          {δ : ℝ} {k : ℕ} (N : NormalizedNeck D.terminal.metric δ k),
          δ ≤ ε → ⌈ε⁻¹⌉₊ ≤ k →
          ∀ Θ : neckCentralOpen δ → positiveHornDomain,
            _root_.Manifold.IsSmoothEmbedding NeckCylinderModel NeckCylinderModel ∞ Θ →
            (∀ z, P.horn c e (Θ z).val =
              N.chart (TopologicalSpace.Opens.inclusion (neckCentralOpen_le_buffer δ) z)) →
            ∃ (p : ComplementPair (_root_.Set.range (fun q : Sphere 2 => Θ ⟨(q,0),_root_.Set.mem_univ _,
                neg_lt_zero.mpr (inv_pos.mpr N.delta_pos),inv_pos.mpr N.delta_pos⟩)))
              (R : ℝ), 0 < R ∧
              (frontier p.left = _root_.Set.range (fun q : Sphere 2 => Θ ⟨(q,0),_root_.Set.mem_univ _,
                neg_lt_zero.mpr (inv_pos.mpr N.delta_pos),inv_pos.mpr N.delta_pos⟩)) ∧
              (frontier p.right = _root_.Set.range (fun q : Sphere 2 => Θ ⟨(q,0),_root_.Set.mem_univ _,
                neg_lt_zero.mpr (inv_pos.mpr N.delta_pos),inv_pos.mpr N.delta_pos⟩)) ∧
              (closure p.left = p.left ∪ _root_.Set.range (fun q : Sphere 2 => Θ ⟨(q,0),_root_.Set.mem_univ _,
                neg_lt_zero.mpr (inv_pos.mpr N.delta_pos),inv_pos.mpr N.delta_pos⟩)) ∧
              (closure p.right = p.right ∪ _root_.Set.range (fun q : Sphere 2 => Θ ⟨(q,0),_root_.Set.mem_univ _,
                neg_lt_zero.mpr (inv_pos.mpr N.delta_pos),inv_pos.mpr N.delta_pos⟩)) ∧
              IsCompact (closure ((Subtype.val : positiveHornDomain → NeckCylinder) '' p.left)) ∧
              (∀ a : ℝ, 0 < a → IsCompact
                (closure p.left ∩ {q : positiveHornDomain | a ≤ q.val.2})) ∧
              (∀ q : positiveHornDomain, q.val.2 < Real.exp (-R) → q ∈ p.left) ∧
              (∀ q : positiveHornDomain, Real.exp R < q.val.2 → q ∈ p.right) ∧
              (∀ q : Sphere 2, Real.exp (-R) <
                (Θ ⟨(q,0),_root_.Set.mem_univ _,neg_lt_zero.mpr (inv_pos.mpr N.delta_pos),
                  inv_pos.mpr N.delta_pos⟩).val.2 ∧
                (Θ ⟨(q,0),_root_.Set.mem_univ _,neg_lt_zero.mpr (inv_pos.mpr N.delta_pos),
                  inv_pos.mpr N.delta_pos⟩).val.2 < Real.exp R) := by
  obtain ⟨eta,heta,hexclude⟩ := exists_horn_normalized_neck_compact_side_exclusion_tolerance
  refine ⟨eta,heta,?_⟩
  intro D ε Λ P hε c e δ k N hδ hk Θ hΘ hmap
  let H := hornLineHomeomorph
  let B := neckLineHomeomorph δ N.delta_pos
  let φ : NeckCylinder → NeckCylinder := H.symm ∘ Θ ∘ B
  have hΘopen : _root_.Topology.IsOpenEmbedding Θ :=
    ⟨hΘ.isEmbedding, Manifold.isOpen_range_of_isSmoothEmbedding (by rfl) hΘ⟩
  have hφ : _root_.Topology.IsOpenEmbedding φ :=
    H.symm.isOpenEmbedding.comp (hΘopen.comp B.isOpenEmbedding)
  let : SimplyConnectedSpace NeckCylinder := DifferentialGeometry.Topology.simplyConnectedSpace_sphereTwo_prod_real
  let : LocallyPathConnectedSpace (Sphere 2) := ChartedSpace.locallyPathConnectedSpace
    (EuclideanSpace ℝ (Fin 2)) (Sphere 2)
  let : ConnectedSpace (Sphere 2) := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp [ThreeSpace]))
      (0 : ThreeSpace) (by norm_num : (0 : ℝ) ≤ 1))
  obtain ⟨L,U,hL,hU,hLop,hUop,hLU,hcover,_,_,hLcl,hUcl,_,_,_⟩ :=
    bicollar_complement_components φ hφ
  let T := _root_.Set.range (fun q : Sphere 2 => φ (q,0))
  let p : ComplementPair T := ⟨L,U,hLop,hUop,hL,hU,hLU,hcover⟩
  have hTc : IsCompact T := isCompact_range (hφ.continuous.comp (continuous_id.prodMk continuous_const))
  have hTL : T ⊆ closure p.left := by rw [show p.left = L from rfl,hLcl]; exact _root_.Set.subset_union_right
  have hTU : T ⊆ closure p.right := by rw [show p.right = U from rfl,hUcl]; exact _root_.Set.subset_union_right
  let S := _root_.Set.range (fun q : Sphere 2 => Θ ⟨(q,0),_root_.Set.mem_univ _,
    neg_lt_zero.mpr (inv_pos.mpr N.delta_pos),inv_pos.mpr N.delta_pos⟩)
  have hHT : H '' T = S := by
    rw [← _root_.Set.range_comp]
    congr 1
    funext q
    change H (H.symm (Θ (B (q,0)))) = _
    rw [H.apply_symm_apply]
    congr 1
    apply Subtype.ext
    exact neckLineHomeomorph_center δ N.delta_pos q
  have hS : P.positiveHornMap c e '' S = _root_.Set.range (fun q : Sphere 2 => N.chart ⟨(q,0),by
      have hp := inv_pos.mpr N.delta_pos
      constructor <;> linarith⟩) := by
    rw [← _root_.Set.range_comp]
    congr 1
    funext q
    exact hmap ⟨(q,0),_root_.Set.mem_univ _,neg_lt_zero.mpr (inv_pos.mpr N.delta_pos),inv_pos.mpr N.delta_pos⟩
  have hnot : ¬ Nonempty (SphereSides T) := by
    rintro ⟨d⟩
    exact hexclude P hε c e N hδ hk S hS ⟨hHT ▸ d.image H⟩
  obtain ⟨R,hR,hband,htails⟩ := (p.compact_side_or_separates_product_ends hTc hTL hTU).resolve_left hnot
  have orient : ∃ p' : ComplementPair T,
      (_root_.Set.univ ×ˢ _root_.Set.Iio (-R) ⊆ p'.left ∧ _root_.Set.univ ×ˢ _root_.Set.Ioi R ⊆ p'.right) ∧
        T ⊆ closure p'.left ∧ T ⊆ closure p'.right := by
    rcases htails with h | h
    · exact ⟨p,h,hTL,hTU⟩
    · exact ⟨p.swap,h,hTU,hTL⟩
  obtain ⟨p',⟨hlo,hhi⟩,hTleft,hTright⟩ := orient
  let d : ComplementPair S := {
    left := H '' p'.left
    right := H '' p'.right
    isOpen_left := H.isOpenMap _ p'.isOpen_left
    isOpen_right := H.isOpenMap _ p'.isOpen_right
    isConnected_left := H.isConnected_image.mpr p'.isConnected_left
    isConnected_right := H.isConnected_image.mpr p'.isConnected_right
    disjoint := Set.disjoint_image_of_injective H.injective p'.disjoint
    union_eq_compl := by rw [← _root_.Set.image_union,p'.union_eq_compl,H.image_compl,hHT] }
  have hSl : S ⊆ closure d.left := by
    change S ⊆ closure (H '' p'.left)
    rw [← hHT,← H.image_closure]
    exact _root_.Set.image_mono hTleft
  have hSr : S ⊆ closure d.right := by
    change S ⊆ closure (H '' p'.right)
    rw [← hHT,← H.image_closure]
    exact _root_.Set.image_mono hTright
  have hlo' : ∀ q : positiveHornDomain, q.val.2 < Real.exp (-R) → q ∈ d.left := by
    intro q hq
    refine ⟨H.symm q,hlo ⟨mem_univ _,?_⟩,H.apply_symm_apply q⟩
    change Real.log q.val.2 < -R
    rw [← Real.exp_lt_exp,Real.exp_log q.property.2]
    exact hq
  have hhi' : ∀ q : positiveHornDomain, Real.exp R < q.val.2 → q ∈ d.right := by
    intro q hq
    refine ⟨H.symm q,hhi ⟨mem_univ _,?_⟩,H.apply_symm_apply q⟩
    change R < Real.log q.val.2
    rw [← Real.exp_lt_exp,Real.exp_log q.property.2]
    exact hq
  have hfullcompact : IsCompact (closure ((Subtype.val : positiveHornDomain → NeckCylinder) '' d.left)) := by
    have hbound : (Subtype.val : positiveHornDomain → NeckCylinder) '' d.left ⊆
        univ ×ˢ _root_.Set.Icc (0:ℝ) (Real.exp R) := by
      rintro q ⟨z,hz,rfl⟩
      refine ⟨mem_univ _,z.property.2.le,?_⟩
      by_contra hn
      exact d.disjoint.le_bot ⟨hz,hhi' z (lt_of_not_ge hn)⟩
    exact (isCompact_univ.prod _root_.CompactIccSpace.isCompact_Icc).of_isClosed_subset isClosed_closure
      (closure_minimal hbound (isClosed_univ.prod isClosed_Icc))
  have hcompact : ∀ a : ℝ, 0 < a → IsCompact
      (closure d.left ∩ {q : positiveHornDomain | a ≤ q.val.2}) := by
    intro a ha
    have hbound : closure d.left ∩ {q : positiveHornDomain | a ≤ q.val.2} ⊆
        H '' (_root_.Set.univ ×ˢ _root_.Set.Icc (Real.log a) R) := by
      intro q hq
      refine ⟨H.symm q,⟨mem_univ _,?_,?_⟩,H.apply_symm_apply q⟩
      · change Real.log a ≤ Real.log q.val.2
        exact Real.log_le_log ha hq.2
      · change Real.log q.val.2 ≤ R
        by_contra hn
        have hqr : Real.exp R < q.val.2 := by
          simpa only [Real.exp_log q.property.2] using Real.exp_lt_exp.mpr (lt_of_not_ge hn)
        exact (d.disjoint.closure_left d.isOpen_right).le_bot ⟨hq.1,hhi' q hqr⟩
    exact ((isCompact_univ.prod _root_.CompactIccSpace.isCompact_Icc).image H.continuous).of_isClosed_subset
      (isClosed_closure.inter (isClosed_le continuous_const continuous_subtype_val.snd)) hbound
  refine ⟨d,R,hR,d.frontier_left_eq hSl,d.frontier_right_eq hSr,
    d.closure_left_eq hSl,d.closure_right_eq hSr,hfullcompact,hcompact,hlo',hhi',?_⟩
  · intro q
    have h := (hband ⟨q,rfl⟩).2
    have heq : φ (q,0) = H.symm (Θ ⟨(q,0),_root_.Set.mem_univ _,
        neg_lt_zero.mpr (inv_pos.mpr N.delta_pos),inv_pos.mpr N.delta_pos⟩) := by
      change H.symm (Θ (B (q,0))) = _
      congr 2
      apply Subtype.ext
      exact neckLineHomeomorph_center δ N.delta_pos q
    change -R < (φ (q,0)).2 ∧ (φ (q,0)).2 < R at h
    rw [heq] at h
    change -R < Real.log _ ∧ Real.log _ < R at h
    constructor
    · simpa only [Real.exp_log (Θ _).property.2] using Real.exp_lt_exp.mpr h.1
    · simpa only [Real.exp_log (Θ _).property.2] using Real.exp_lt_exp.mpr h.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_horn_neck_end_separation_tolerance then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_horn_neck_end_separation_tolerance"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_horn_neck_end_separation_tolerance ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_horn_neck_end_separation_tolerance


theorem exists_deep_horn_neck_end_separation_tolerance :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ),
        ε ≤ eta → ∀ (c : ConnectedComponents D.slab.terminalRegularOpen) (_ : c ∈ P.component)
          (e : P.hornIndex c) (r : ℝ),
          ∃ Q : ℝ, 0 < Q ∧ ∀ {δ : ℝ} {k : ℕ} (N : NormalizedNeck D.terminal.metric δ k),
            δ ≤ ε → ⌊ε⁻¹⌋₊ + 1 ≤ k → N.center ∈ TerminalCorePresentation.hornHalfRange P c e → Q < N.scale →
            ∃ Θ : neckCentralOpen δ → positiveHornDomain,
              _root_.Manifold.IsSmoothEmbedding NeckCylinderModel NeckCylinderModel ∞ Θ ∧
              (∀ z, P.horn c e (Θ z).val =
                N.chart (TopologicalSpace.Opens.inclusion (neckCentralOpen_le_buffer δ) z)) ∧
              (∀ z, r < (Θ z).val.2) ∧
              ∃ (p : ComplementPair (_root_.Set.range (fun q : Sphere 2 => Θ ⟨(q,0),_root_.Set.mem_univ _,
                  neg_lt_zero.mpr (inv_pos.mpr N.delta_pos),inv_pos.mpr N.delta_pos⟩)))
                (R : ℝ), 0 < R ∧
              (frontier p.left = _root_.Set.range (fun q : Sphere 2 => Θ ⟨(q,0),_root_.Set.mem_univ _,
                neg_lt_zero.mpr (inv_pos.mpr N.delta_pos),inv_pos.mpr N.delta_pos⟩)) ∧
              (frontier p.right = _root_.Set.range (fun q : Sphere 2 => Θ ⟨(q,0),_root_.Set.mem_univ _,
                neg_lt_zero.mpr (inv_pos.mpr N.delta_pos),inv_pos.mpr N.delta_pos⟩)) ∧
              (closure p.left = p.left ∪ _root_.Set.range (fun q : Sphere 2 => Θ ⟨(q,0),_root_.Set.mem_univ _,
                neg_lt_zero.mpr (inv_pos.mpr N.delta_pos),inv_pos.mpr N.delta_pos⟩)) ∧
              (closure p.right = p.right ∪ _root_.Set.range (fun q : Sphere 2 => Θ ⟨(q,0),_root_.Set.mem_univ _,
                neg_lt_zero.mpr (inv_pos.mpr N.delta_pos),inv_pos.mpr N.delta_pos⟩)) ∧
              IsCompact (closure ((Subtype.val : positiveHornDomain → NeckCylinder) '' p.left)) ∧
              (∀ a : ℝ, 0 < a → IsCompact
                (closure p.left ∩ {q : positiveHornDomain | a ≤ q.val.2})) ∧
                (∀ q : positiveHornDomain, q.val.2 < Real.exp (-R) → q ∈ p.left) ∧
                (∀ q : positiveHornDomain, Real.exp R < q.val.2 → q ∈ p.right) ∧
                (∀ q : Sphere 2, Real.exp (-R) <
                  (Θ ⟨(q,0),_root_.Set.mem_univ _,neg_lt_zero.mpr (inv_pos.mpr N.delta_pos),
                    inv_pos.mpr N.delta_pos⟩).val.2 ∧
                  (Θ ⟨(q,0),_root_.Set.mem_univ _,neg_lt_zero.mpr (inv_pos.mpr N.delta_pos),
                    inv_pos.mpr N.delta_pos⟩).val.2 < Real.exp R) := by
  obtain ⟨eta,heta,hseparate⟩ := exists_horn_neck_end_separation_tolerance
  refine ⟨min eta (1/8646),lt_min heta (by norm_num),?_⟩
  intro D ε Λ P hε c hc e r
  obtain ⟨Q,hQ,hcoords⟩ := P.exists_scale_threshold_neck_coordinates_beyond_depth c hc e r
  refine ⟨Q,hQ,?_⟩
  intro δ k N hδ hk hcenter hscale
  have hεsmall : ε ≤ 1/8646 := hε.trans (min_le_right _ _)
  have hεpos : 0 < ε := N.delta_pos.trans_le hδ
  have hlarge : (1:ℝ) ≤ ε⁻¹ := (le_inv_comm₀ (by norm_num) hεpos).mpr (by linarith)
  have hfloor : 1 ≤ ⌊ε⁻¹⌋₊ := (Nat.le_floor_iff (by positivity)).mpr (by exact_mod_cast hlarge)
  have hk2 : 2 ≤ k := by omega
  obtain ⟨Θ,hΘ,hmap,hdepth⟩ := hcoords N hk2 (hδ.trans hεsmall) hcenter hscale
  obtain ⟨p,R,hR,hfrontl,hfrontr,hcll,hclr,hfullcompact,hcompact,hlo,hhi,hband⟩ := hseparate P (hε.trans (min_le_left _ _)) c e N hδ
    ((Nat.ceil_le_floor_add_one ε⁻¹).trans hk) Θ hΘ hmap
  exact ⟨Θ,hΘ,hmap,hdepth,p,R,hR,hfrontl,hfrontr,hcll,hclr,hfullcompact,hcompact,hlo,hhi,hband⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_deep_horn_neck_end_separation_tolerance then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_deep_horn_neck_end_separation_tolerance"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_deep_horn_neck_end_separation_tolerance ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_deep_horn_neck_end_separation_tolerance

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
