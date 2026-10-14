import Submission.DifferentialGeometry.Geometry.Neck.Spatial
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ComparisonComposition
import Submission.DifferentialGeometry.Topology.Manifold.OpenSubtypeDiffeomorph
import Submission.DifferentialGeometry.Geometry.Curvature.RicciRestriction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Submission.Set _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

theorem SpatialNeck.exists_restrict_target
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    [T2Space M] {g : SmoothRiemannianMetric I3 M} {p : M} {eps : ℝ}
    (nk : SpatialNeck g eps p) (U : TopologicalSpace.Opens M)
    (hcapture : nk.map '' (_root_.Set.univ ×ˢ _root_.Set.Ioo (-eps⁻¹) eps⁻¹) ⊆ U) :
    ∃ (hp : p ∈ U) (out : SpatialNeck (g.restrictOpen U) eps ⟨p, hp⟩),
      out.center = nk.center ∧
      (∀ z ∈ _root_.Set.univ ×ˢ _root_.Set.Ioo (-eps⁻¹) eps⁻¹, (out.map z : M) = nk.map z) ∧
      (∀ x : U, out.map.symm x = nk.map.symm (x : M)) ∧
      out.map.target = {x : U | (x : M) ∈ nk.map.target} ∧
      ∀ x : U, metricScalarAt (g.restrictOpen U) x = metricScalarAt g (x : M) := by
  have hcenter : (nk.center, (0 : ℝ)) ∈ _root_.Set.univ ×ˢ _root_.Set.Ioo (-eps⁻¹) eps⁻¹ :=
    ⟨mem_univ _, neg_lt_zero.mpr (inv_pos.mpr nk.eps_pos), inv_pos.mpr nk.eps_pos⟩
  have hp : p ∈ U := nk.center_eq ▸ hcapture (_root_.Set.mem_image_of_mem nk.map hcenter)
  have hne : Nonempty U := ⟨⟨p, hp⟩⟩
  let iU := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph I3 U hne
  let F := partialDiffeomorphTransMixed nk.map iU.symm
  have hsource : _root_.Set.univ ×ˢ _root_.Set.Ioo (-eps⁻¹) eps⁻¹ ⊆ F.source := by
    intro z hz
    refine ⟨nk.domain hz, ?_⟩
    change nk.map z ∈ iU.target
    rw [DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_target]
    exact hcapture (_root_.Set.mem_image_of_mem nk.map hz)
  have hmap (z : Cylinder) (hz : z ∈ _root_.Set.univ ×ˢ _root_.Set.Ioo (-eps⁻¹) eps⁻¹) :
      (F z : M) = nk.map z := by
    change (iU.symm (nk.map z) : M) = nk.map z
    rw [DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_symm_apply I3 U hne
      (hcapture (_root_.Set.mem_image_of_mem nk.map hz))]
  have hder (z : Cylinder) (hz : z ∈ _root_.Set.univ ×ˢ _root_.Set.Ioo (-eps⁻¹) eps⁻¹) :
      mfderiv IC I3 F z = mfderiv IC I3 nk.map z := by
    have heq : (fun y => (F y : M)) =ᶠ[𝓝 z] (nk.map : Cylinder → M) :=
      Filter.eventuallyEq_of_mem ((isOpen_univ.prod isOpen_Ioo).mem_nhds hz) hmap
    exact (mfderiv_subtypeVal_comp F z).symm.trans heq.mfderiv_eq
  have hscalar : ∀ x : U, metricScalarAt (g.restrictOpen U) x = metricScalarAt g (x : M) := by
    intro x
    exact metricScalarAt_restrictOpen g U x
  have hQ : 0 < metricScalarAt (g.restrictOpen U) ⟨p, hp⟩ := by rw [hscalar]; exact nk.Q_pos
  let cmp : MetricComparisonOn (fun _ => nk.cylinder.metric 0)
      (fun _ => DifferentialGeometry.scaleMetric (metricScalarAt (g.restrictOpen U) ⟨p, hp⟩) hQ (g.restrictOpen U))
      F (_root_.Set.univ ×ˢ _root_.Set.Ioo (-eps⁻¹) eps⁻¹) {0} ⌈eps⁻¹⌉₊ eps := {
    pullback := nk.comparison.pullback
    pullback_eq := by
      intro s z hz v
      rw [nk.comparison.pullback_eq s z hz v]
      simp only [scaleMetric_inner, SmoothRiemannianMetric.restrictOpen_inner, hscalar, hder z hz]
      rw [hmap z hz]
      rfl
    jet := nk.comparison.jet
    jet_zero := nk.comparison.jet_zero
    jet_succ := nk.comparison.jet_succ
    equivalence := nk.comparison.equivalence
    close := nk.comparison.close }
  refine ⟨hp, {
    eps_pos := nk.eps_pos
    eps_small := nk.eps_small
    Q_pos := hQ
    cylinder := nk.cylinder
    map := F
    center := nk.center
    center_eq := ?_
    domain := hsource
    comparison := cmp }, rfl, hmap, fun _ => rfl, ?_, hscalar⟩
  · apply Subtype.ext
    exact (hmap _ hcenter).trans nk.center_eq
  · ext x
    change (x ∈ (_root_.Set.univ : Set U) ∧ (x : M) ∈ nk.map.target) ↔ (x : M) ∈ nk.map.target
    simp only [_root_.Set.mem_univ, true_and]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.exists_restrict_target then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.exists_restrict_target"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.exists_restrict_target ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.exists_restrict_target

theorem SpatialNeck.controlled_range_subset_connectedComponent
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    {g : SmoothRiemannianMetric I3 M} {p : M} {eps : ℝ} (nk : SpatialNeck g eps p) :
    nk.map '' (_root_.Set.univ ×ˢ _root_.Set.Ioo (-eps⁻¹) eps⁻¹) ⊆ connectedComponent p := by
  let : ConnectedSpace (Sphere 2) := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp [ThreeSpace]))
      (0 : ThreeSpace) (by norm_num : (0 : ℝ) ≤ 1))
  have hpre : IsPreconnected (nk.map '' (_root_.Set.univ ×ˢ _root_.Set.Ioo (-eps⁻¹) eps⁻¹)) :=
    (isPreconnected_univ.prod isPreconnected_Ioo).image nk.map
      (nk.map.contMDiffOn_toFun.continuousOn.mono nk.domain)
  apply hpre.subset_connectedComponent
  exact ⟨(nk.center,0), ⟨mem_univ _, neg_lt_zero.mpr (inv_pos.mpr nk.eps_pos),
    inv_pos.mpr nk.eps_pos⟩, nk.center_eq⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.controlled_range_subset_connectedComponent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.controlled_range_subset_connectedComponent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.controlled_range_subset_connectedComponent ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.controlled_range_subset_connectedComponent

theorem SpatialNeck.exists_of_restrictOpen
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    [T2Space M] {g : SmoothRiemannianMetric I3 M} {U : TopologicalSpace.Opens M}
    {p : U} {eps : ℝ} (nk : SpatialNeck (g.restrictOpen U) eps p) :
    ∃ out : SpatialNeck g eps (p : M),
      out.center = nk.center ∧
      (∀ z, out.map z = (nk.map z : M)) ∧
      (∀ x : U, out.map.symm (x : M) = nk.map.symm x) ∧
      out.map.source = nk.map.source ∧
      out.map.target = Subtype.val '' nk.map.target := by
  let iU := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph I3 U ⟨p⟩
  let F := partialDiffeomorphTransMixed nk.map iU
  have hmap (z : Cylinder) : F z = (nk.map z : M) := rfl
  have hsource : F.source = nk.map.source := by
    ext z
    change (z ∈ nk.map.source ∧ nk.map z ∈ (_root_.Set.univ : Set U)) ↔ z ∈ nk.map.source
    simp only [_root_.Set.mem_univ, and_true]
  have hder (z : Cylinder) : mfderiv IC I3 F z = mfderiv IC I3 nk.map z :=
    mfderiv_subtypeVal_comp nk.map z
  have hscalar : metricScalarAt (g.restrictOpen U) p = metricScalarAt g (p : M) :=
    metricScalarAt_restrictOpen g U p
  have hQ : 0 < metricScalarAt g (p : M) := hscalar ▸ nk.Q_pos
  let cmp : MetricComparisonOn (fun _ => nk.cylinder.metric 0)
      (fun _ => DifferentialGeometry.scaleMetric (metricScalarAt g (p : M)) hQ g)
      F (_root_.Set.univ ×ˢ _root_.Set.Ioo (-eps⁻¹) eps⁻¹) {0} ⌈eps⁻¹⌉₊ eps := {
    pullback := nk.comparison.pullback
    pullback_eq := by
      intro s z hz v
      rw [nk.comparison.pullback_eq s z hz v]
      simp only [scaleMetric_inner, SmoothRiemannianMetric.restrictOpen_inner,
        hscalar, hder]
      rfl
    jet := nk.comparison.jet
    jet_zero := nk.comparison.jet_zero
    jet_succ := nk.comparison.jet_succ
    equivalence := nk.comparison.equivalence
    close := nk.comparison.close }
  refine ⟨{
    eps_pos := nk.eps_pos
    eps_small := nk.eps_small
    Q_pos := hQ
    cylinder := nk.cylinder
    map := F
    center := nk.center
    center_eq := congrArg Subtype.val nk.center_eq
    domain := hsource ▸ nk.domain
    comparison := cmp }, rfl, hmap, ?_, hsource, ?_⟩
  · intro x
    change nk.map.symm (iU.symm (x : M)) = nk.map.symm x
    rw [DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_symm_apply I3 U ⟨p⟩ x.property]
  · ext x
    change (x ∈ iU.target ∧ iU.symm x ∈ nk.map.target) ↔
      x ∈ Subtype.val '' nk.map.target
    constructor
    · rintro ⟨hxU, hx⟩
      exact ⟨iU.symm x, hx, iU.right_inv hxU⟩
    · rintro ⟨y, hy, rfl⟩
      refine ⟨?_, ?_⟩
      · exact iU.map_source (_root_.Set.mem_univ y)
      rw [DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_symm_apply I3 U ⟨p⟩ y.property]
      exact hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.exists_of_restrictOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.exists_of_restrictOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.exists_of_restrictOpen ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.exists_of_restrictOpen


theorem exists_spatial_neck_frontier_on_connectedComponent
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    [T2Space M] {g : SmoothRiemannianMetric I3 M} {eps : ℝ}
    {ι : Type*} (b : Finset ι) (point : ι → M)
    (neck : ∀ i, SpatialNeck g eps (point i)) (level : ι → ℝ)
    (hlevel : ∀ i ∈ b, |level i| < eps⁻¹)
    (c : M) {W : Set M} (hW : IsCompact W)
    (hregular : closure (interior W) = W) (hcomponent : W ⊆ connectedComponent c)
    (hfront : frontier W = ⋃ i ∈ b, _root_.Set.range (fun q => (neck i).map (q, level i)))
    (hdisjoint : (b : Set ι).Pairwise (fun i j =>
      Disjoint (_root_.Set.range (fun q => (neck i).map (q, level i)))
        (_root_.Set.range (fun q => (neck j).map (q, level j))))) :
    let U := connectedComponentOpen (I := I3) c
    let W' := (Subtype.val : U → M) ⁻¹' W
    ∃ (point' : {i // i ∈ b} → U)
      (neck' : ∀ i, SpatialNeck (g.restrictOpen U) eps (point' i)),
      (∀ i, (point' i : M) = point i.val) ∧
      (∀ i, (neck' i).center = (neck i.val).center) ∧
      (∀ i z, z ∈ _root_.Set.univ ×ˢ _root_.Set.Ioo (-eps⁻¹) eps⁻¹ →
        ((neck' i).map z : M) = (neck i.val).map z) ∧
      IsCompact W' ∧ closure (interior W') = W' ∧
      interior W' = (Subtype.val : U → M) ⁻¹' interior W ∧
      frontier W' = ⋃ i, _root_.Set.range (fun q => (neck' i).map (q, level i.val)) ∧
      Pairwise (fun i j => Disjoint
        (_root_.Set.range (fun q => (neck' i).map (q, level i.val)))
        (_root_.Set.range (fun q => (neck' j).map (q, level j.val)))) := by
  classical
  intro U W'
  have hcontrolled (i : {i // i ∈ b}) (q : Sphere 2) :
      (q, level i.val) ∈ _root_.Set.univ ×ˢ _root_.Set.Ioo (-eps⁻¹) eps⁻¹ := by
    exact ⟨mem_univ _, abs_lt.mp (hlevel i.val i.property)⟩
  have hcapture (i : {i // i ∈ b}) :
      (neck i.val).map '' (_root_.Set.univ ×ˢ _root_.Set.Ioo (-eps⁻¹) eps⁻¹) ⊆ U := by
    let x := (neck i.val).map ((neck i.val).center, level i.val)
    have hxfront : x ∈ frontier W := by
      rw [hfront]
      exact mem_iUnion₂.mpr ⟨i.val, i.property, ⟨(neck i.val).center, rfl⟩⟩
    have hxc : x ∈ connectedComponent c := hcomponent (hW.isClosed.frontier_subset hxfront)
    have hxp : x ∈ connectedComponent (point i.val) :=
      (neck i.val).controlled_range_subset_connectedComponent
        ⟨((neck i.val).center, level i.val), hcontrolled i _, rfl⟩
    have heq : connectedComponent (point i.val) = connectedComponent c :=
      (connectedComponent_eq hxp).trans (connectedComponent_eq hxc).symm
    change _ ⊆ connectedComponent c
    rw [← heq]
    exact (neck i.val).controlled_range_subset_connectedComponent
  choose hp nk hcenter hmap hinv htarget hscalar using
    fun i : {i // i ∈ b} => (neck i.val).exists_restrict_target U (hcapture i)
  let point' (i : {i // i ∈ b}) : U := ⟨point i.val, hp i⟩
  have hinterior : interior W' = (Subtype.val : U → M) ⁻¹' interior W :=
    (U.isOpenEmbedding'.isOpenMap.preimage_interior_eq_interior_preimage
      continuous_subtype_val W).symm
  have hrange (i : {i // i ∈ b}) :
      _root_.Set.range (fun q => (nk i).map (q, level i.val)) =
        (Subtype.val : U → M) ⁻¹' _root_.Set.range (fun q => (neck i.val).map (q, level i.val)) := by
    ext x
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨q, (hmap i _ (hcontrolled i q)).symm⟩
    · rintro ⟨q, hq⟩
      exact ⟨q, Subtype.ext ((hmap i _ (hcontrolled i q)).trans hq)⟩
  refine ⟨point', nk, fun _ => rfl, hcenter, hmap, ?_, ?_, hinterior, ?_, ?_⟩
  · exact _root_.Topology.IsInducing.subtypeVal.isCompact_preimage' hW
      (fun x hx => ⟨⟨x, hcomponent hx⟩, rfl⟩)
  · rw [hinterior, ← U.isOpenEmbedding'.isOpenMap.preimage_closure_eq_closure_preimage
      continuous_subtype_val, hregular]
  · rw [← U.isOpenEmbedding'.isOpenMap.preimage_frontier_eq_frontier_preimage
      continuous_subtype_val, hfront]
    ext x
    simp only [_root_.Set.mem_preimage, _root_.Set.mem_iUnion]
    constructor
    · rintro ⟨i, hi, hxi⟩
      exact ⟨⟨i, hi⟩, (hrange ⟨i, hi⟩).superset hxi⟩
    · rintro ⟨i, hxi⟩
      exact ⟨i.val, i.property, (hrange i).subset hxi⟩
  · intro i j hij
    rw [hrange, hrange]
    exact (hdisjoint i.property j.property (fun h => hij (Subtype.ext h))).preimage _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_spatial_neck_frontier_on_connectedComponent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_spatial_neck_frontier_on_connectedComponent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_spatial_neck_frontier_on_connectedComponent ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_spatial_neck_frontier_on_connectedComponent

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
