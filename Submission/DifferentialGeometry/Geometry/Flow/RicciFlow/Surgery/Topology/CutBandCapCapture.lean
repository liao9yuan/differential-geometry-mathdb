import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckRegionBall
import Submission.DifferentialGeometry.Geometry.Metric.Distance.Boundary
import Submission.DifferentialGeometry.Topology.Connected.CoverBySides
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutCap
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CapRegionStructure
import Mathlib.Topology.Order.ProjIcc

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Metric _root_.Submission.Metric _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Topology
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Topology.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M] (T : TubeSystem M)

omit [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] [T2Space M] in
theorem isPreconnected_closedBand (a : T.Index) :
    IsPreconnected (T.tube a '' {q : TubeDomain | q.2.val ∈ _root_.Set.Icc (-1 : ℝ) 1}) := by
  let : PreconnectedSpace (Sphere 2) := isPreconnected_iff_preconnectedSpace.mp
    (isPreconnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp [ThreeSpace]))
      (0 : ThreeSpace) 1)
  let : PreconnectedSpace (_root_.Set.Icc (-1 : ℝ) 1) := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  let j : Sphere 2 × _root_.Set.Icc (-1 : ℝ) 1 → TubeDomain :=
    fun q => (q.1,⟨q.2.val,by constructor <;> linarith [q.2.property.1,q.2.property.2]⟩)
  have hj : Continuous j := continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).subtype_mk _)
  have hr : _root_.Set.range (T.tube a ∘ j) = T.tube a '' {q : TubeDomain | q.2.val ∈ _root_.Set.Icc (-1 : ℝ) 1} := by
    ext x
    constructor
    · rintro ⟨q,rfl⟩
      exact ⟨j q,q.2.property,rfl⟩
    · rintro ⟨q,hq,rfl⟩
      exact ⟨(q.1,⟨q.2.val,hq⟩),rfl⟩
  exact hr ▸ isPreconnected_range ((T.tube a).continuous.comp hj)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.isPreconnected_closedBand then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.isPreconnected_closedBand"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.isPreconnected_closedBand ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.isPreconnected_closedBand

omit [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] [T2Space M] in
theorem central_and_boundary_spheres_subset_of_closedBand_subset
    (a : T.Index) {K : Set M}
    (h : T.tube a '' {q : TubeDomain | q.2.val ∈ _root_.Set.Icc (-1 : ℝ) 1} ⊆ K) :
    _root_.Set.range (fun z : Sphere 2 => T.tube a (z,⟨0,by norm_num⟩)) ⊆ K ∧
      ∀ side : Bool, _root_.Set.range (T.boundarySphere (a,side)) ⊆ K := by
  constructor
  · rintro _ ⟨z,rfl⟩
    exact h (_root_.Set.mem_image_of_mem (T.tube a) (by norm_num))
  · intro side
    rintro _ ⟨z,rfl⟩
    apply h
    refine ⟨(z,boundaryLevel side),?_,rfl⟩
    cases side <;> norm_num [boundaryLevel]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.central_and_boundary_spheres_subset_of_closedBand_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.central_and_boundary_spheres_subset_of_closedBand_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.central_and_boundary_spheres_subset_of_closedBand_subset ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.central_and_boundary_spheres_subset_of_closedBand_subset

omit [T2Space M] in
theorem closedBand_subset_cap_core_interior_or_meets_inner_boundary
    {J : RealTimeInterval} {S : SolutionOn (I := ThreeModel) (M := M) J}
    {eps t : ℝ} {x : M} {U : Set M} (cap : LocalCap S eps x t U)
    (a : T.Index) (q : TubeDomain) (hq : q.2.val ∈ _root_.Set.Icc (-1 : ℝ) 1)
    (hcontact : T.tube a q ∈ cap.core.carrier) :
    (T.tube a '' {q : TubeDomain | q.2.val ∈ _root_.Set.Icc (-1 : ℝ) 1} ⊆ interior cap.core.carrier) ∨
      ∃ (r : TubeDomain) (z : Sphere 2), r.2.val ∈ _root_.Set.Icc (-1 : ℝ) 1 ∧
        T.tube a r = cap.tube_map (z,0) := by
  rcases Set.disjoint_or_nonempty_inter
      (T.tube a '' {q : TubeDomain | q.2.val ∈ _root_.Set.Icc (-1 : ℝ) 1}) (frontier cap.core.carrier) with hd | h
  · exact Or.inl (DifferentialGeometry.Topology.isPreconnected_subset_interior_of_meets_of_disjoint_frontier
      (T.isPreconnected_closedBand a) ⟨T.tube a q,_root_.Set.mem_image_of_mem (T.tube a) hq,hcontact⟩ hd)
  · obtain ⟨w,⟨r,hr,hrw⟩,hw⟩ := h
    obtain ⟨⟨z,s⟩,hs,heq⟩ := cap.inner_boundary.symm ▸ hw
    obtain rfl : s = 0 := hs.2
    exact Or.inr ⟨r,z,hr,hrw.trans heq.symm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.closedBand_subset_cap_core_interior_or_meets_inner_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.closedBand_subset_cap_core_interior_or_meets_inner_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.closedBand_subset_cap_core_interior_or_meets_inner_boundary ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.closedBand_subset_cap_core_interior_or_meets_inner_boundary

omit [T2Space M] in
theorem closedBand_subset_cap_core_interior_or_far_inner_boundary
    {J : RealTimeInterval} {S : SolutionOn (I := ThreeModel) (M := M) J}
    {eps t : ℝ} {x : M} {U : Set M} (cap : LocalCap S eps x t U)
    (hdepth : ∀ y ∈ cap.tube,
      10000 / Real.sqrt (S.scalar t x) ≤ metricDistance (S.base.metric t) x y)
    (a : T.Index) (q : TubeDomain) (hq : q.2.val ∈ _root_.Set.Icc (-1 : ℝ) 1)
    (hcontact : T.tube a q ∈ cap.core.carrier) :
    (T.tube a '' {q : TubeDomain | q.2.val ∈ _root_.Set.Icc (-1 : ℝ) 1} ⊆ interior cap.core.carrier) ∨
      ∃ (r : TubeDomain) (z : Sphere 2), r.2.val ∈ _root_.Set.Icc (-1 : ℝ) 1 ∧
        T.tube a r = cap.tube_map (z,0) ∧
        10000 / Real.sqrt (S.scalar t x) ≤ metricDistance (S.base.metric t) x (T.tube a r) := by
  obtain h | ⟨r,z,hr,he⟩ := T.closedBand_subset_cap_core_interior_or_meets_inner_boundary cap a q hq hcontact
  · exact Or.inl h
  · refine Or.inr ⟨r,z,hr,he,?_⟩
    apply hdepth
    rw [he,← cap.tube_eq]
    exact _root_.Set.mem_image_of_mem cap.tube_map ⟨mem_univ _,le_rfl,zero_le_one⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.closedBand_subset_cap_core_interior_or_far_inner_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.closedBand_subset_cap_core_interior_or_far_inner_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.closedBand_subset_cap_core_interior_or_far_inner_boundary ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.closedBand_subset_cap_core_interior_or_far_inner_boundary

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] (T : TubeSystem M)

theorem closedBand_subset_closedBall_of_spatialNeck
    {g : SmoothRiemannianMetric ThreeModel M} {eps : ℝ} {p : M}
    (nk : SpatialNeck g eps p) (a : T.Index)
    (hmap : ∀ q : TubeDomain, q.2.val ∈ _root_.Set.Icc (-1 : ℝ) 1 → T.tube a q = nk.map (q.1,q.2.val)) :
    T.tube a '' {q : TubeDomain | q.2.val ∈ _root_.Set.Icc (-1 : ℝ) 1} ⊆ riemannianClosedBallOf g p
      (7 * Real.sqrt (1+eps) / Real.sqrt (metricScalarAt g p)) := by
  have hsmall : (1 : ℝ) < eps⁻¹ :=
    (one_lt_inv₀ nk.eps_pos).mpr (nk.eps_small.trans (by norm_num))
  rintro _ ⟨q,hq,rfl⟩
  rw [hmap q hq]
  have h := nk.image_slab_subset_closedBall zero_le_one hsmall
    (show nk.map (q.1,q.2.val) ∈ nk.map '' (_root_.Set.univ ×ˢ _root_.Set.Icc (-(1 : ℝ)) 1) from
      ⟨(q.1,q.2.val),⟨mem_univ _,hq⟩,rfl⟩)
  simpa only [show (1 : ℝ)+6=7 by norm_num] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.closedBand_subset_closedBall_of_spatialNeck then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.closedBand_subset_closedBall_of_spatialNeck"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.closedBand_subset_closedBall_of_spatialNeck ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.closedBand_subset_closedBall_of_spatialNeck

theorem closedBand_subset_cap_core_interior_or_center_far_of_spatialNeck
    {J : RealTimeInterval} {S : SolutionOn (I := ThreeModel) (M := M) J}
    {eps epsc t : ℝ} {x p : M} {U : Set M} (cap : LocalCap S epsc x t U)
    (hdepth : ∀ y ∈ cap.tube,
      10000 / Real.sqrt (S.scalar t x) ≤ metricDistance (S.base.metric t) x y)
    (nk : SpatialNeck (S.base.metric t) eps p)
    (a : T.Index)
    (hmap : ∀ q : TubeDomain, q.2.val ∈ _root_.Set.Icc (-1 : ℝ) 1 → T.tube a q = nk.map (q.1,q.2.val))
    (q : TubeDomain) (hq : q.2.val ∈ _root_.Set.Icc (-1 : ℝ) 1)
    (hcontact : T.tube a q ∈ cap.core.carrier) :
    (T.tube a '' {q : TubeDomain | q.2.val ∈ _root_.Set.Icc (-1 : ℝ) 1} ⊆ interior cap.core.carrier) ∨
      ∃ (r : TubeDomain) (z : Sphere 2), r.2.val ∈ _root_.Set.Icc (-1 : ℝ) 1 ∧
        T.tube a r = cap.tube_map (z,0) ∧
        ENNReal.ofReal (10000 / Real.sqrt (S.scalar t x)) ≤
          riemannianEDistOf (S.base.metric t) x p +
            ENNReal.ofReal (7 * Real.sqrt (1+eps) / Real.sqrt (metricScalarAt (S.base.metric t) p)) := by
  obtain h | ⟨r,z,hr,he,hfar⟩ := T.closedBand_subset_cap_core_interior_or_far_inner_boundary
    cap hdepth a q hq hcontact
  · exact Or.inl h
  · refine Or.inr ⟨r,z,hr,he,?_⟩
    have hbound := T.closedBand_subset_closedBall_of_spatialNeck nk a hmap
      (_root_.Set.mem_image_of_mem (T.tube a) hr)
    have hdist : ENNReal.ofReal (10000 / Real.sqrt (S.scalar t x)) ≤
        riemannianEDistOf (S.base.metric t) x (T.tube a r) :=
      (ENNReal.ofReal_le_ofReal hfar).trans ENNReal.ofReal_toReal_le
    exact hdist.trans ((riemannianEDistOf_triangle (S.base.metric t) x p (T.tube a r)).trans
      (add_le_add_right hbound _))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.closedBand_subset_cap_core_interior_or_center_far_of_spatialNeck then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.closedBand_subset_cap_core_interior_or_center_far_of_spatialNeck"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.closedBand_subset_cap_core_interior_or_center_far_of_spatialNeck ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.closedBand_subset_cap_core_interior_or_center_far_of_spatialNeck

theorem closedBand_subset_cap_core_interior_of_spatialNeck_center_close
    {J : RealTimeInterval} {S : SolutionOn (I := ThreeModel) (M := M) J}
    {eps epsc t : ℝ} {x p : M} {U : Set M} (cap : LocalCap S epsc x t U)
    (hdepth : ∀ y ∈ cap.tube,
      10000 / Real.sqrt (S.scalar t x) ≤ metricDistance (S.base.metric t) x y)
    (nk : SpatialNeck (S.base.metric t) eps p)
    (a : T.Index)
    (hmap : ∀ q : TubeDomain, q.2.val ∈ _root_.Set.Icc (-1 : ℝ) 1 → T.tube a q = nk.map (q.1,q.2.val))
    (hclose : riemannianEDistOf (S.base.metric t) x p +
      ENNReal.ofReal (7 * Real.sqrt (1+eps) / Real.sqrt (metricScalarAt (S.base.metric t) p)) <
        ENNReal.ofReal (10000 / Real.sqrt (S.scalar t x))) :
    T.tube a '' {q : TubeDomain | q.2.val ∈ _root_.Set.Icc (-1 : ℝ) 1} ⊆ interior cap.core.carrier := by
  have hcapture := DifferentialGeometry.Geometry.Metric.riemannianEDistOf_ball_subset_of_le_frontier_distance
    (S.base.metric t) cap.center_inside (r := ENNReal.ofReal (10000 / Real.sqrt (S.scalar t x)))
    (fun y hy => (ENNReal.ofReal_le_ofReal (hdepth y ((cap.overlap_eq.symm ▸ hy).2))).trans
      ENNReal.ofReal_toReal_le)
  intro y hy
  apply hcapture
  exact ((riemannianEDistOf_triangle (S.base.metric t) x p y).trans
    (add_le_add_right (T.closedBand_subset_closedBall_of_spatialNeck nk a hmap hy) _)).trans_lt hclose

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.closedBand_subset_cap_core_interior_of_spatialNeck_center_close then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.closedBand_subset_cap_core_interior_of_spatialNeck_center_close"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.closedBand_subset_cap_core_interior_of_spatialNeck_center_close ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.closedBand_subset_cap_core_interior_of_spatialNeck_center_close

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem

section

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem

variable {M : Type*} [TopologicalSpace M] (T : TubeSystem M)

theorem boundarySphere_mem_closure_removedBand (b : T.Boundary) (q : Sphere 2) :
    T.boundarySphere b q ∈ closure (T.removedBand b.1) := by
  let f : ℝ → M := fun t => T.tube b.1 (q, Set.projIcc (-2 : ℝ) 2 (by norm_num) t)
  have hf : Continuous f := (T.tube b.1).continuous.comp
    (continuous_const.prodMk continuous_projIcc)
  have hlevel : (boundaryLevel b.2).val ∈ closure (_root_.Set.Ioo (-1 : ℝ) 1) := by
    rw [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)]
    cases b with
    | mk a side => cases side <;> norm_num [boundaryLevel]
  have himage : f '' _root_.Set.Ioo (-1 : ℝ) 1 ⊆ T.removedBand b.1 := by
    rintro y ⟨t, ht, rfl⟩
    have ht2 : t ∈ _root_.Set.Icc (-2 : ℝ) 2 := by constructor <;> linarith [ht.1, ht.2]
    refine ⟨(q, Set.projIcc (-2 : ℝ) 2 (by norm_num) t), ?_, rfl⟩
    change -1 < (Set.projIcc (-2 : ℝ) 2 (by norm_num) t).val ∧
      (Set.projIcc (-2 : ℝ) 2 (by norm_num) t).val < 1
    rw [Set.projIcc_of_mem (by norm_num : (-2 : ℝ) ≤ 2) ht2]
    exact ht
  have hh := closure_mono himage (mem_closure_image hf.continuousAt hlevel)
  have heq : f (boundaryLevel b.2).val = T.boundarySphere b q := by
    dsimp [f]
    rw [Set.projIcc_of_mem (by norm_num : (-2 : ℝ) ≤ 2) (boundaryLevel b.2).property]
    rfl
  exact heq ▸ hh

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.boundarySphere_mem_closure_removedBand then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.boundarySphere_mem_closure_removedBand"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.boundarySphere_mem_closure_removedBand ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.boundarySphere_mem_closure_removedBand

theorem eq_of_boundarySphere_mem_of_frontier_eq
    {K : Set M} (hcore : K ⊆ T.core) (b : T.Boundary)
    (hfront : frontier K = _root_.Set.range (T.boundarySphere b))
    {b' : T.Boundary} {q : Sphere 2} (hq : T.boundarySphere b' q ∈ K) : b' = b := by
  have hnot : T.boundarySphere b' q ∉ interior K := by
    intro hint
    have hh := T.boundarySphere_mem_closure_removedBand b' q
    have hn := (mem_closure_iff_nhds.mp hh) (interior K)
      (isOpen_interior.mem_nhds hint)
    obtain ⟨y, hyint, hyband⟩ := hn
    exact hcore (interior_subset hyint) (mem_iUnion.mpr ⟨b'.1, hyband⟩)
  have hf : T.boundarySphere b' q ∈ frontier K := (mem_frontier_iff_notMem_interior hq).mpr hnot
  obtain ⟨z, hz⟩ := hfront ▸ hf
  have hidx : b'.1 = b.1 := by
    by_contra hne
    exact (disjoint_left.mp (T.disjoint hne))
      (_root_.Set.mem_range_self (q, boundaryLevel b'.2)) ⟨(z, boundaryLevel b.2), hz⟩
  apply Prod.ext hidx
  have he : T.tube b.1 (q, boundaryLevel b'.2) = T.tube b.1 (z, boundaryLevel b.2) := by
    have hh : T.tube b.1 (z, boundaryLevel b.2) = T.tube b'.1 (q, boundaryLevel b'.2) := hz
    rw [hidx] at hh
    exact hh.symm
  have hcoord := congrArg (fun p : TubeDomain => p.2.val) ((T.embedding b.1).injective he)
  revert hcoord
  cases hb' : b'.2 <;> cases hb : b.2
  · intro _; rfl
  · norm_num [boundaryLevel]
  · norm_num [boundaryLevel]
  · intro _; rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.eq_of_boundarySphere_mem_of_frontier_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.eq_of_boundarySphere_mem_of_frontier_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.eq_of_boundarySphere_mem_of_frontier_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.eq_of_boundarySphere_mem_of_frontier_eq

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem

end

section

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem

variable {M : Type*} [TopologicalSpace M] (T : TubeSystem M)

theorem closedBand_subset_connectedComponent_of_cylinder
    (b : T.Boundary) (R : Sphere 2 × ℝ → M)
    (hR : ContinuousOn R (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1))
    (hRzero : ∀ q : Sphere 2, R (q,0) = T.boundarySphere b q)
    (q : Sphere 2) :
    T.tube b.1 '' {p : TubeDomain | p.2.val ∈ _root_.Set.Icc (-1 : ℝ) 1} ⊆
      connectedComponent (R (q,1)) := by
  let _ : PreconnectedSpace (Sphere 2) := isPreconnected_iff_preconnectedSpace.mp
    (isPreconnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp [ThreeSpace]))
      (0 : ThreeSpace) 1)
  have hconn : IsPreconnected (R '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1)) :=
    (isPreconnected_univ.prod isPreconnected_Icc).image R hR
  have hR0 : R (q,0) ∈ R '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) :=
    ⟨(q,0),⟨mem_univ _,by norm_num⟩,rfl⟩
  have hR1 : R (q,1) ∈ R '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) :=
    ⟨(q,1),⟨mem_univ _,by norm_num⟩,rfl⟩
  have h01 : T.boundarySphere b q ∈ connectedComponent (R (q,1)) :=
    hRzero q ▸ hconn.subset_connectedComponent hR1 hR0
  have hqband : T.boundarySphere b q ∈
      T.tube b.1 '' {p : TubeDomain | p.2.val ∈ _root_.Set.Icc (-1 : ℝ) 1} := by
    refine ⟨(q,boundaryLevel b.2),?_,rfl⟩
    cases b.2 <;> norm_num [boundaryLevel]
  intro y hy
  have hy0 := (T.isPreconnected_closedBand b.1).subset_connectedComponent hqband hy
  rwa [← connectedComponent_eq h01] at hy0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.closedBand_subset_connectedComponent_of_cylinder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.closedBand_subset_connectedComponent_of_cylinder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.closedBand_subset_connectedComponent_of_cylinder ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.closedBand_subset_connectedComponent_of_cylinder

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem

end
