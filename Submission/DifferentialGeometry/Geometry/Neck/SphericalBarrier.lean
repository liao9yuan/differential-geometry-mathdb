import Submission.DifferentialGeometry.Geometry.Neck.SpatialChart
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckCapCompactDomains
import Submission.DifferentialGeometry.Topology.Manifold.ProductChartCollar
import Submission.DifferentialGeometry.Topology.Embedding.Factor
import Submission.DifferentialGeometry.Topology.Manifold.ImmersionCriterion
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NeckSpatialBridge
import Batteries.Tactic.OpenPrivate

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open private exists_compactDomain_of_cylinder_slab from Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckCapCompactDomains

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open _root_.Submission.DifferentialGeometry.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric I3 M} {eps : ℝ} {p : M}

private theorem SpatialNeck.slice_isSmoothEmbedding (nk : SpatialNeck g eps p)
    {t : ℝ} (ht : t ∈ _root_.Set.Ioo (-eps⁻¹) eps⁻¹) :
    IsSmoothEmbedding I2 I3 ∞ (fun y : Sphere 2 => nk.map (y,t)) := by
  let f : Sphere 2 → Cylinder := fun y => (y,t)
  have hf : _root_.Manifold.IsSmoothEmbedding I2 IC ∞ f :=
    (IsSmoothEmbedding.id : _root_.Manifold.IsSmoothEmbedding I2 I2 ∞ (Prod.fst ∘ f)).of_comp
      (J := IC) (by simp) (contMDiff_id.prodMk contMDiff_const) contMDiff_fst
  have hs (y : Sphere 2) : f y ∈ nk.map.source := nk.domain ⟨mem_univ _,ht⟩
  have hc : ContMDiff I2 I3 ∞ (nk.map ∘ f) := contMDiffOn_univ.mp
    (nk.map.contMDiffOn_toFun.comp hf.contMDiff.contMDiffOn (fun y _ => hs y))
  refine ⟨DifferentialGeometry.Topology.Manifold.isImmersion_of_injective_mfderiv (by simp) hc ?_,
    (hc.continuous.isClosedEmbedding (fun a b h => congrArg Prod.fst (nk.map.injOn (hs a) (hs b) h))).isEmbedding⟩
  intro y
  have hl := nk.map.isLocalDiffeomorphAt IC I3 ∞ (hs y)
  change Function.Injective (mfderiv I2 I3 (nk.map ∘ f) y)
  rw [mfderiv_comp y (hl.contMDiffAt.mdifferentiableAt (by simp)) (hf.contMDiff.mdifferentiableAt (by simp))]
  exact (hl.mfderivToContinuousLinearEquiv (by simp)).injective.comp
    ((hf.isImmersion.isImmersionAt y).injective_mfderiv (by simp))

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.slice_isSmoothEmbedding
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.slice_isSmoothEmbedding target :: scope.openDecls } }

omit [T2Space M] in
private theorem SpatialNeck.exists_slice_collar (nk : SpatialNeck g eps p)
    {t : ℝ} (ht : t ∈ _root_.Set.Ioo (-eps⁻¹) eps⁻¹) :
    ∃ c : SmoothTwoSidedCollar I2 I3 (fun y : Sphere 2 => nk.map (y,t)),
      c.radius < 1 ∧ ∀ q : Sphere 2 × symmetricOpenInterval c.radius,
        c.toFun q = nk.map (q.1,t+(q.2 : ℝ)) := by
  have hm : ∀ y : Sphere 2, (y,t) ∈ nk.cylindricalChart.domain := fun y => ⟨mem_univ _,ht⟩
  obtain ⟨c,hc,_,hcoord⟩ := exists_smoothTwoSidedCollar_of_product_chart_graph
    nk.cylindricalChart.domain nk.cylindricalChart.target nk.cylindricalChart.chart
    (fun _ => t) contMDiff_const hm (by norm_num : (0 : ℝ)<1)
  exact ⟨c,hc,fun q => (hcoord q).choose_spec⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.exists_slice_collar
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.exists_slice_collar target :: scope.openDecls } }

theorem SpatialNeck.exists_short_spherical_barrier
    (nk : SpatialNeck g eps p) (heps : eps < 1 / 8646)
    (A C2 : ℝ) (hA : 0 < A) (hC2 : 1 ≤ C2) (hscale : metricScalarAt g p = 4 * C2 * A) :
    ∃ K : CompactDomain M,
      K.carrier = nk.map '' (_root_.Set.univ ×ˢ _root_.Set.Icc (-3 : ℝ) 3) ∧ p ∈ interior K.carrier ∧
      frontier K.carrier = _root_.Set.range (fun y : Sphere 2 => nk.map (y,-3)) ∪
        _root_.Set.range (fun y : Sphere 2 => nk.map (y,3)) ∧
      Disjoint (_root_.Set.range (fun y : Sphere 2 => nk.map (y,-3)))
        (_root_.Set.range (fun y : Sphere 2 => nk.map (y,3))) ∧
      (∀ t ∈ ({-3,3} : Set ℝ), _root_.Manifold.IsSmoothEmbedding I2 I3 ∞ (fun y : Sphere 2 => nk.map (y,t))) ∧
      (∀ y ∈ K.carrier, 2*A < metricScalarAt g y ∧ metricScalarAt g y ≤ 8*C2^2*A) ∧
      (∀ z ∈ (_root_.Set.univ ×ˢ _root_.Set.Icc (-101 : ℝ) 101 : Set Cylinder),
        2*A < metricScalarAt g (nk.map z) ∧ metricScalarAt g (nk.map z) ≤ 8*C2^2*A) ∧
      nk.cylindricalChart.metricCloseOn g eps
        {z : nk.cylindricalChart.domain | z.val.2 ∈ _root_.Set.Icc (-101 : ℝ) 101} ∧
      (∀ y t, t ∈ _root_.Set.Icc (-101 : ℝ) 101 → (y,t) ∈ nk.cylindricalChart.domain) ∧
      ∃ (cneg : SmoothTwoSidedCollar I2 I3 (fun y : Sphere 2 => nk.map (y,-3)))
        (cpos : SmoothTwoSidedCollar I2 I3 (fun y : Sphere 2 => nk.map (y,3))),
        cneg.radius < 1 ∧ cpos.radius < 1 ∧
        (∀ q : Sphere 2 × symmetricOpenInterval cneg.radius,
          cneg.toFun q = nk.map (q.1,-3-(q.2 : ℝ)) ∧ (cneg.toFun q ∈ K.carrier ↔ (q.2 : ℝ) ≤ 0)) ∧
        (∀ q : Sphere 2 × symmetricOpenInterval cpos.radius,
          cpos.toFun q = nk.map (q.1,3+(q.2 : ℝ)) ∧ (cpos.toFun q ∈ K.carrier ↔ (q.2 : ℝ) ≤ 0)) := by
  have hlen : (101 : ℝ) < eps⁻¹ := (lt_inv_comm₀ (by norm_num) nk.eps_pos).mpr (by linarith)
  have h3 : (3 : ℝ) < eps⁻¹ := by linarith
  have hsrc : (_root_.Set.univ ×ˢ _root_.Set.Icc (-3 : ℝ) 3 : Set Cylinder) ⊆ nk.map.source := by
    intro z hz
    exact nk.domain ⟨hz.1,by linarith [hz.2.1],by linarith [hz.2.2]⟩
  obtain ⟨K,hK⟩ := exists_compactDomain_of_cylinder_slab nk.map (by norm_num : (-3 : ℝ)<3) hsrc
  have hband : ∀ z ∈ (_root_.Set.univ ×ˢ _root_.Set.Icc (-101 : ℝ) 101 : Set Cylinder),
      2*A < metricScalarAt g (nk.map z) ∧ metricScalarAt g (nk.map z) ≤ 8*C2^2*A := by
    intro z hz
    have hs := nk.scalar_bounds_on_image_window ⟨z,⟨hz.1,by linarith [hz.2.1],by linarith [hz.2.2]⟩,rfl⟩
    rw [hscale] at hs
    have hp : 0 < 4*C2*A := by positivity
    have hl : 2*C2*A < (1-4323*eps)*(4*C2*A) := by nlinarith
    have h2A : 2*A ≤ 2*C2*A := by nlinarith
    have hu : (1+4323*eps)*(4*C2*A) ≤ 8*C2^2*A := by
      have h1 : 1+4323*eps ≤ 2*C2 := by linarith
      have hh := mul_le_mul_of_nonneg_right h1 hp.le
      nlinarith
    exact ⟨h2A.trans_lt (hl.trans_le hs.1),hs.2.trans hu⟩
  have hminus : (-3 : ℝ) ∈ _root_.Set.Ioo (-eps⁻¹) eps⁻¹ := by constructor <;> linarith
  have hplus : (3 : ℝ) ∈ _root_.Set.Ioo (-eps⁻¹) eps⁻¹ := by constructor <;> linarith
  obtain ⟨cm,hcm,hcmmap⟩ := nk.exists_slice_collar hminus
  obtain ⟨cp,hcp,hcpmap⟩ := nk.exists_slice_collar hplus
  refine ⟨K,hK,?_,?_,?_,?_,?_,hband,?_,?_,cm.reverse,cp,hcm,hcp,?_,?_⟩
  · rw [hK]
    have hopen := nk.isOpen_image_openSlab hminus.1.le hplus.2.le
    apply hopen.subset_interior_iff.mpr (_root_.Set.image_mono (_root_.Set.prod_mono subset_rfl _root_.Set.Ioo_subset_Icc_self))
    exact ⟨(nk.center,0),⟨mem_univ _,by norm_num⟩,nk.center_eq⟩
  · rw [hK,nk.frontier_image_slab hminus.1 hplus.2 (by norm_num)]
    ext y
    constructor
    · rintro ⟨⟨z,t⟩,⟨_,ht⟩,rfl⟩
      rcases ht with rfl | rfl
      · exact Or.inl ⟨z,rfl⟩
      · exact Or.inr ⟨z,rfl⟩
    · rintro (⟨z,rfl⟩ | ⟨z,rfl⟩)
      · exact ⟨(z,-3),⟨mem_univ _,Or.inl rfl⟩,rfl⟩
      · exact ⟨(z,3),⟨mem_univ _,Or.inr rfl⟩,rfl⟩
  · rw [_root_.Set.disjoint_left]
    rintro y ⟨z,rfl⟩ ⟨w,hw⟩
    have hh := congrArg Prod.snd (nk.map.injOn (nk.domain ⟨mem_univ _,hplus⟩) (nk.domain ⟨mem_univ _,hminus⟩) hw)
    norm_num at hh
  · intro t ht
    rcases ht with rfl | rfl
    · exact nk.slice_isSmoothEmbedding hminus
    · exact nk.slice_isSmoothEmbedding hplus
  · rw [hK]
    rintro y ⟨z,hz,rfl⟩
    exact hband z ⟨hz.1,by constructor <;> linarith [hz.2.1,hz.2.2]⟩
  · intro z _ j hj
    exact nk.cylindricalChart_metricCloseOn z (_root_.Set.mem_univ _) j hj
  · intro y t ht
    exact ⟨mem_univ _,by linarith [ht.1],by linarith [ht.2]⟩
  · intro q
    have hqrange : -cm.radius < (q.2 : ℝ) ∧ (q.2 : ℝ) < cm.radius := q.2.property
    have hm := hcmmap (q.1,⟨-(q.2 : ℝ),by constructor <;> linarith [hqrange.1,hqrange.2]⟩)
    change cm.toFun (q.1,⟨-(q.2 : ℝ),_⟩) = _ ∧ _
    constructor
    · simpa only [sub_eq_add_neg] using hm
    · change cm.toFun (q.1,⟨-(q.2 : ℝ),_⟩) ∈ K.carrier ↔ (q.2 : ℝ) ≤ 0
      rw [hm,hK]
      constructor
      · rintro ⟨z,hz,hzq⟩
        have hqsrc : (q.1,-3+ -(q.2 : ℝ)) ∈ nk.map.source := nk.domain
          ⟨mem_univ _,by linarith [hqrange.1,hqrange.2],by linarith [hqrange.1,hqrange.2]⟩
        have hh := congrArg Prod.snd (nk.map.injOn (hsrc hz) hqsrc hzq)
        linarith [hz.2.1]
      · intro hq
        exact ⟨(q.1,-3+ -(q.2 : ℝ)),⟨mem_univ _,by constructor <;> linarith [hqrange.1,hqrange.2]⟩,rfl⟩
  · intro q
    refine ⟨hcpmap q,?_⟩
    rw [hcpmap q,hK]
    constructor
    · rintro ⟨z,hz,hzq⟩
      have hqsrc : (q.1,3+(q.2 : ℝ)) ∈ nk.map.source := nk.domain
        ⟨mem_univ _,by linarith [q.2.property.1,q.2.property.2],by linarith [q.2.property.1,q.2.property.2]⟩
      have hh := congrArg Prod.snd (nk.map.injOn (hsrc hz) hqsrc hzq)
      linarith [hz.2.2]
    · intro hq
      exact ⟨(q.1,3+(q.2 : ℝ)),⟨mem_univ _,by constructor <;> linarith [q.2.property.1,q.2.property.2]⟩,rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.exists_short_spherical_barrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.exists_short_spherical_barrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.exists_short_spherical_barrier ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.exists_short_spherical_barrier

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
