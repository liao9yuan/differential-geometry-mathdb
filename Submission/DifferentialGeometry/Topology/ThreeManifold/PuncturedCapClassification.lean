import Submission.DifferentialGeometry.Topology.ThreeManifold.PuncturedCapCover
import Submission.DifferentialGeometry.Topology.ThreeManifold.SphericalBoundaryBallHoles
import Submission.DifferentialGeometry.Topology.ThreeManifold.SphericalBoundaryProjectiveHoles
import Submission.DifferentialGeometry.Topology.ThreeManifold.NestedBallRecapping
import Submission.DifferentialGeometry.Topology.ThreeManifold.CapCoreBallReplacement
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ProjectivePresentation
import Submission.DifferentialGeometry.Topology.ThreeManifold.CoreComponentGeometry
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutCapCoreComponent
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapCoreCapping

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Submission.Set _root_.Metric _root_.Submission.Metric _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff

namespace DifferentialGeometry.Topology.SphericalCapping

universe u

variable {M N : ClosedOrientedManifold.{u} 3} {T : SphericalTubeSystem M}
  (C : SphericalCapping M N T)
  {Ω : Set M.Carrier} (cap : CapCore Ω) (outer : T.Boundary)
  (hfront : frontier Ω = range (T.boundarySphere outer))
  (s : Finset T.Boundary)
  (B : T.Boundary → PartialDiffeomorph I3 I3 ThreeSpace M.Carrier ∞)
  (hB : ∀ b ∈ s, closedBall (0 : ThreeSpace) 1 ⊆ (B b).source)
  (hinside : ∀ b ∈ s, B b '' closedBall (0 : ThreeSpace) 1 ⊆ interior Ω)
  (hdis : (s : Set T.Boundary).Pairwise (fun b c =>
    Disjoint (B b '' closedBall (0 : ThreeSpace) 1) (B c '' closedBall (0 : ThreeSpace) 1)))
  (hsphere : ∀ b ∈ s, B b '' sphere (0 : ThreeSpace) 1 = range (T.boundarySphere b))
  (x : T.core)
  (hcomponent : Ω \ ⋃ b ∈ s, B b '' ball (0 : ThreeSpace) 1 =
    (Subtype.val : T.core → M.Carrier) '' connectedComponent x)

include hfront hinside hsphere in
private theorem outer_not_mem : outer ∉ s := by
  intro hout
  let q : Sphere 2 := ⟨EuclideanSpace.single 0 1, by simp⟩
  have hq : T.boundarySphere outer q ∈ frontier Ω := hfront.symm ▸ _root_.Set.mem_range_self q
  have hbq : T.boundarySphere outer q ∈ B outer '' _root_.Metric.sphere (0 : ThreeSpace) 1 :=
    (hsphere outer hout).symm ▸ _root_.Set.mem_range_self q
  exact hq.2 (hinside outer hout (_root_.Set.image_mono _root_.Metric.sphere_subset_closedBall hbq))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphericalCapping.outer_not_mem
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphericalCapping.outer_not_mem target :: scope.openDecls } }

include cap hfront hB hinside hdis hsphere hcomponent

theorem frontier_coreComponent_union_caps_of_finite_ball_complement :
    frontier (C.coreInclusion '' connectedComponent x ∪ ⋃ b ∈ s, _root_.Set.range (C.cap b)) =
      range (C.coreInclusion.comp (T.coreBoundarySphere outer)) := by
  obtain ⟨_,J,hJ,hJimage,hcoreEq,_,_⟩ :=
    C.nonempty_capCore_union_caps_of_finite_ball_complement cap s B hB hinside hdis hsphere x hcomponent
  have hinc := (T.toTopological.boundary_incidence_of_finite_ball_complement_component
    cap.isCompact_carrier.isClosed outer hfront s B hB hinside hdis hsphere x hcomponent).1
  rw [← hJimage, ← J.image_frontier_of_isCompact cap.isCompact_carrier hJ, hfront]
  ext y
  constructor
  · rintro ⟨_,⟨q,rfl⟩,rfl⟩
    exact ⟨q,(hcoreEq (T.coreBoundarySphere outer q) (hinc outer (Or.inl rfl) q)).symm⟩
  · rintro ⟨q,rfl⟩
    exact ⟨T.boundarySphere outer q,_root_.Set.mem_range_self q,
      hcoreEq (T.coreBoundarySphere outer q) (hinc outer (Or.inl rfl) q)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping.frontier_coreComponent_union_caps_of_finite_ball_complement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping.frontier_coreComponent_union_caps_of_finite_ball_complement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping.frontier_coreComponent_union_caps_of_finite_ball_complement ``Submission.DifferentialGeometry.Topology.SphericalCapping.frontier_coreComponent_union_caps_of_finite_ball_complement

theorem coreComponent_union_caps_inter_cap_of_finite_ball_complement :
    (C.coreInclusion '' connectedComponent x ∪ ⋃ b ∈ s, _root_.Set.range (C.cap b)) ∩
        range (C.cap outer) = _root_.Set.range (C.coreInclusion.comp (T.coreBoundarySphere outer)) := by
  have hnot : outer ∉ s := outer_not_mem outer hfront s B hinside hsphere
  have hinc := (T.toTopological.boundary_incidence_of_finite_ball_complement_component
    cap.isCompact_carrier.isClosed outer hfront s B hB hinside hdis hsphere x hcomponent).1
  apply Subset.antisymm
  · rintro y ⟨hy,hycap⟩
    rcases hy with hycore | hy
    · exact (C.core_cap_intersection outer).subset
        ⟨image_subset_range _ _ hycore,hycap⟩
    · obtain ⟨b,hb,hyb⟩ := mem_iUnion₂.mp hy
      exact False.elim (disjoint_left.mp (C.cap_disjoint (i := b) (j := outer) (fun he => hnot (he ▸ hb))) hyb hycap)
  · rintro y ⟨q,rfl⟩
    refine ⟨Or.inl ⟨T.coreBoundarySphere outer q,hinc outer (Or.inl rfl) q,rfl⟩,?_⟩
    refine ⟨sphereToClosedCell ((C.attaching outer).symm q),?_⟩
    exact (C.boundary_eq outer _).trans (congrArg C.coreInclusion
      (congrArg (T.coreBoundarySphere outer) ((C.attaching outer).apply_symm_apply q)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping.coreComponent_union_caps_inter_cap_of_finite_ball_complement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping.coreComponent_union_caps_inter_cap_of_finite_ball_complement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping.coreComponent_union_caps_inter_cap_of_finite_ball_complement ``Submission.DifferentialGeometry.Topology.SphericalCapping.coreComponent_union_caps_inter_cap_of_finite_ball_complement

theorem isPoincareStandard_component_of_finite_ball_complement :
    isPoincareStandard (N.component (ConnectedComponents.mk (C.coreInclusion x))).Carrier := by
  obtain ⟨hcap,_⟩ :=
    C.nonempty_capCore_union_caps_of_finite_ball_complement cap s B hB hinside hdis hsphere x hcomponent
  exact C.isPoincareStandard_component_of_capCore_union_cap hcap.some outer _
    (C.image_coreComponent_union_caps_eq_componentSet_of_finite_ball_complement
      cap.isCompact_carrier.isClosed outer hfront s B hB hinside hdis hsphere x hcomponent)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping.isPoincareStandard_component_of_finite_ball_complement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping.isPoincareStandard_component_of_finite_ball_complement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping.isPoincareStandard_component_of_finite_ball_complement ``Submission.DifferentialGeometry.Topology.SphericalCapping.isPoincareStandard_component_of_finite_ball_complement

end DifferentialGeometry.Topology.SphericalCapping

namespace DifferentialGeometry.Topology.SphericalCutCapTransition

universe u

variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)

theorem isPoincareStandard_discardedComponent_of_finite_ball_complement
    {Ω : Set M.Carrier} (cap : CapCore Ω) (outer : E.tubes.Boundary)
    (hfront : frontier Ω = _root_.Set.range (E.tubes.boundarySphere outer))
    (s : Finset E.tubes.Boundary)
    (B : E.tubes.Boundary → PartialDiffeomorph I3 I3 ThreeSpace M.Carrier ∞)
    (hB : ∀ b ∈ s, _root_.Metric.closedBall (0 : ThreeSpace) 1 ⊆ (B b).source)
    (hinside : ∀ b ∈ s, B b '' _root_.Metric.closedBall (0 : ThreeSpace) 1 ⊆ interior Ω)
    (hdis : (s : Set E.tubes.Boundary).Pairwise (fun b c =>
      Disjoint (B b '' _root_.Metric.closedBall (0 : ThreeSpace) 1) (B c '' _root_.Metric.closedBall (0 : ThreeSpace) 1)))
    (hsphere : ∀ b ∈ s, B b '' _root_.Metric.sphere (0 : ThreeSpace) 1 = _root_.Set.range (E.tubes.boundarySphere b))
    (x : E.tubes.core)
    (hcomponent : Ω \ ⋃ b ∈ s, B b '' _root_.Metric.ball (0 : ThreeSpace) 1 =
      (Subtype.val : E.tubes.core → M.Carrier) '' connectedComponent x)
    (d : E.discarded.Carrier) (hd : E.presentation (E.capping.coreInclusion x) = Sum.inr d) :
    isPoincareStandard (E.discarded.component (ConnectedComponents.mk d)).Carrier := by
  have hstd := E.capping.isPoincareStandard_component_of_finite_ball_complement
    cap outer hfront s B hB hinside hdis hsphere x hcomponent
  obtain ⟨e⟩ := E.cappedDiscardedPresentationRealization x d hd
  exact isPoincareStandard_of_diffeomorph e.val.symm hstd

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.isPoincareStandard_discardedComponent_of_finite_ball_complement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.isPoincareStandard_discardedComponent_of_finite_ball_complement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.isPoincareStandard_discardedComponent_of_finite_ball_complement ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.isPoincareStandard_discardedComponent_of_finite_ball_complement

end DifferentialGeometry.Topology.SphericalCutCapTransition

section

namespace DifferentialGeometry.Topology.SphericalCapping

universe u
variable {M N : ClosedOrientedManifold.{u} 3} {T : SphericalTubeSystem M}
  (C : SphericalCapping M N T)

theorem isPoincareStandard_component_of_ball_spherical_frontier
    (x : T.core) (A : PartialDiffeomorph I3 I3 ThreeSpace M.Carrier ∞)
    (hA : _root_.Metric.closedBall (0 : ThreeSpace) 1 ⊆ A.source)
    (outer : T.Boundary) (houter : A '' _root_.Metric.sphere (0 : ThreeSpace) 1 = _root_.Set.range (T.boundarySphere outer))
    (s : Finset T.Boundary)
    (hregular : closure (interior ((Subtype.val : T.core → M.Carrier) '' connectedComponent x)) =
      (Subtype.val : T.core → M.Carrier) '' connectedComponent x)
    (hconnected : IsPreconnected (interior ((Subtype.val : T.core → M.Carrier) '' connectedComponent x)))
    (hcontained : (Subtype.val : T.core → M.Carrier) '' connectedComponent x ⊆
      A '' _root_.Metric.closedBall (0 : ThreeSpace) 1)
    (hinside : ∀ b ∈ s, _root_.Set.range (T.boundarySphere b) ⊆ A '' _root_.Metric.ball (0 : ThreeSpace) 1)
    (hfront : frontier ((Subtype.val : T.core → M.Carrier) '' connectedComponent x) =
      _root_.Set.range (T.boundarySphere outer) ∪ ⋃ b ∈ s, _root_.Set.range (T.boundarySphere b)) :
    isPoincareStandard (N.component (ConnectedComponents.mk (C.coreInclusion x))).Carrier := by
  classical
  let I := {b : T.Boundary // b ∈ s}
  have hsmooth (b : I) : _root_.Manifold.IsSmoothEmbedding I2 I3 ∞ (T.boundarySphere b.val) :=
    T.toTopological.isSmoothEmbedding_boundarySphere b.val (T.smooth b.val.1)
  have hfr : frontier ((Subtype.val : T.core → M.Carrier) '' connectedComponent x) =
      A '' _root_.Metric.sphere (0 : ThreeSpace) 1 ∪ ⋃ b : I, _root_.Set.range (T.boundarySphere b.val) := by
    rw [houter,_root_.Set.iUnion_subtype]
    exact hfront
  have hpair : Pairwise (fun b c : I => Disjoint (_root_.Set.range (T.boundarySphere b.val))
      (_root_.Set.range (T.boundarySphere c.val))) := by
    intro b c hbc
    exact T.toTopological.pairwise_disjoint_range_boundarySphere (fun he => hbc (Subtype.ext he))
  obtain ⟨B,hB,hBs,hBA,hdis,hW⟩ :=
    DifferentialGeometry.Topology.ThreeManifold.exists_finite_disjoint_ball_holes_of_spherical_frontier
      A hA hregular hconnected hcontained (fun b : I => T.boundarySphere b.val)
      hsmooth (fun b => hinside b.val b.property) hfr hpair
  let B' : T.Boundary → PartialDiffeomorph I3 I3 ThreeSpace M.Carrier ∞ :=
    fun b => if hb : b ∈ s then B ⟨b,hb⟩ else A
  have hB'eq (b : T.Boundary) (hb : b ∈ s) : B' b = B ⟨b,hb⟩ := dif_pos hb
  have hAint : interior (A '' _root_.Metric.closedBall (0 : ThreeSpace) 1) = A '' _root_.Metric.ball (0 : ThreeSpace) 1 := by
    have hh := A.toOpenPartialHomeomorph.image_interior_of_subset_source hA
    change A '' interior (_root_.Metric.closedBall (0 : ThreeSpace) 1) = interior (A '' _root_.Metric.closedBall 0 1) at hh
    rw [interior_closedBall _ one_ne_zero] at hh
    exact hh.symm
  have hAf : frontier (A '' _root_.Metric.closedBall (0 : ThreeSpace) 1) = _root_.Set.range (T.boundarySphere outer) := by
    rw [← A.image_frontier_of_isCompact (_root_.ProperSpace.isCompact_closedBall _ _) hA,frontier_closedBall _ one_ne_zero,houter]
  have hholes : (⋃ b ∈ s, B' b '' _root_.Metric.ball (0 : ThreeSpace) 1) =
      ⋃ b : I, B b '' _root_.Metric.ball (0 : ThreeSpace) 1 := by
    ext y
    constructor
    · intro hy
      obtain ⟨b,hb,hy⟩ := mem_iUnion₂.mp hy
      exact mem_iUnion.mpr ⟨⟨b,hb⟩,hB'eq b hb ▸ hy⟩
    · intro hy
      obtain ⟨b,hb⟩ := mem_iUnion.mp hy
      exact mem_iUnion₂.mpr ⟨b.val,b.property,(hB'eq b.val b.property).symm ▸ hb⟩
  apply C.isPoincareStandard_component_of_finite_ball_complement
    (CapCore.ball A hA rfl) outer hAf s B'
    (fun b hb => hB'eq b hb ▸ hB ⟨b,hb⟩)
  · intro b hb
    rw [hB'eq b hb,hAint]
    exact hBA ⟨b,hb⟩
  · intro b hb c hc hbc
    rw [hB'eq b hb,hB'eq c hc]
    exact hdis (fun he => hbc (congrArg Subtype.val he))
  · intro b hb
    rw [hB'eq b hb]
    exact hBs ⟨b,hb⟩
  · rw [hholes]
    exact hW.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping.isPoincareStandard_component_of_ball_spherical_frontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping.isPoincareStandard_component_of_ball_spherical_frontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping.isPoincareStandard_component_of_ball_spherical_frontier ``Submission.DifferentialGeometry.Topology.SphericalCapping.isPoincareStandard_component_of_ball_spherical_frontier

end DifferentialGeometry.Topology.SphericalCapping

end

section

namespace DifferentialGeometry.Topology.SphericalCapping

universe u
variable {M N : ClosedOrientedManifold.{u} 3} {T : SphericalTubeSystem M}
  (C : SphericalCapping M N T)

theorem isPoincareStandard_component_of_ball_containing_coreComponent
    (x : T.core) (A : PartialDiffeomorph (𝓡 3) (𝓡 3) ThreeSpace M.Carrier ∞)
    (hA : _root_.Metric.closedBall (0 : ThreeSpace) 1 ⊆ A.source)
    (outer : T.Boundary)
    (houter : A '' _root_.Metric.sphere (0 : ThreeSpace) 1 = _root_.Set.range (T.boundarySphere outer))
    (houter_mem : ∃ q : Sphere 2, T.coreBoundarySphere outer q ∈ connectedComponent x)
    (hcontained : (Subtype.val : T.core → M.Carrier) '' connectedComponent x ⊆
      A '' _root_.Metric.closedBall (0 : ThreeSpace) 1) :
    isPoincareStandard (N.component (ConnectedComponents.mk (C.coreInclusion x))).Carrier := by
  classical
  let _ : ConnectedSpace (Sphere 2) := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp [ThreeSpace]))
      (0 : ThreeSpace) zero_le_one)
  have hAint : interior (A '' _root_.Metric.closedBall (0 : ThreeSpace) 1) = A '' _root_.Metric.ball (0 : ThreeSpace) 1 := by
    have hh := A.toOpenPartialHomeomorph.image_interior_of_subset_source hA
    change A '' interior (_root_.Metric.closedBall (0 : ThreeSpace) 1) = interior (A '' _root_.Metric.closedBall 0 1) at hh
    rw [interior_closedBall _ one_ne_zero] at hh
    exact hh.symm
  have hAfr : frontier (A '' _root_.Metric.closedBall (0 : ThreeSpace) 1) = _root_.Set.range (T.boundarySphere outer) := by
    rw [← A.image_frontier_of_isCompact (_root_.ProperSpace.isCompact_closedBall _ _) hA,
      frontier_closedBall _ one_ne_zero,houter]
  have hinside (b : T.Boundary) (hb : b ≠ outer)
      (hbmem : ∃ q : Sphere 2, T.coreBoundarySphere b q ∈ connectedComponent x) :
      range (T.boundarySphere b) ⊆ A '' _root_.Metric.ball (0 : ThreeSpace) 1 := by
    obtain ⟨q₀,hq₀⟩ := hbmem
    rintro y ⟨q,rfl⟩
    have hpre := isPreconnected_range (T.coreBoundarySphere b).continuous
    have hq : T.coreBoundarySphere b q ∈ connectedComponent x := by
      have hh := hpre.subset_connectedComponent (_root_.Set.mem_range_self q₀) (_root_.Set.mem_range_self q)
      rwa [← connectedComponent_eq hq₀] at hh
    have hclosed : T.boundarySphere b q ∈ A '' _root_.Metric.closedBall (0 : ThreeSpace) 1 :=
      hcontained (_root_.Set.mem_image_of_mem Subtype.val hq)
    rw [← hAint]
    apply (mem_interior_iff_notMem_frontier hclosed).mpr
    intro hyfront
    obtain ⟨r,hr⟩ := hAfr ▸ hyfront
    exact hb ((T.toTopological.boundarySphere_eq_iff b outer q r).mp hr.symm).1
  let s : Finset T.Boundary := Finset.univ.filter (fun b => b ≠ outer ∧
    ∃ q : Sphere 2, T.coreBoundarySphere b q ∈ connectedComponent x)
  obtain ⟨_,_,hregular,hconnected,hfront⟩ := C.coreComponent_geometry x
  have hinside' : ∀ b ∈ s, _root_.Set.range (T.boundarySphere b) ⊆ A '' _root_.Metric.ball (0 : ThreeSpace) 1 := by
    intro b hb
    obtain ⟨hne,hbcomp⟩ := (Finset.mem_filter.mp hb).2
    exact hinside b hne hbcomp
  have hfront' : frontier ((Subtype.val : T.core → M.Carrier) '' connectedComponent x) =
      range (T.boundarySphere outer) ∪ ⋃ b ∈ s, _root_.Set.range (T.boundarySphere b) := by
    rw [hfront]
    ext y
    constructor
    · intro hy
      obtain ⟨b,hb⟩ := mem_iUnion.mp hy
      by_cases he : b.val = outer
      · exact Or.inl (he ▸ hb)
      · exact Or.inr (mem_iUnion₂.mpr ⟨b.val,Finset.mem_filter.mpr
          ⟨Finset.mem_univ _,he,b.property⟩,hb⟩)
    · rintro (hy | hy)
      · exact mem_iUnion.mpr ⟨⟨outer,houter_mem⟩,hy⟩
      · obtain ⟨b,hb,hy⟩ := mem_iUnion₂.mp hy
        exact mem_iUnion.mpr ⟨⟨b,(Finset.mem_filter.mp hb).2.2⟩,hy⟩
  exact C.isPoincareStandard_component_of_ball_spherical_frontier x A hA outer houter s
    hregular hconnected hcontained hinside' hfront'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping.isPoincareStandard_component_of_ball_containing_coreComponent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping.isPoincareStandard_component_of_ball_containing_coreComponent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping.isPoincareStandard_component_of_ball_containing_coreComponent ``Submission.DifferentialGeometry.Topology.SphericalCapping.isPoincareStandard_component_of_ball_containing_coreComponent

end DifferentialGeometry.Topology.SphericalCapping

end

section

namespace DifferentialGeometry.Topology.SphericalCapping

universe u
variable {M N : ClosedOrientedManifold.{u} 3} {T : SphericalTubeSystem M}
  (C : SphericalCapping M N T)

theorem isPoincareStandard_component_of_ball_cutting_side
    (A : PartialDiffeomorph (𝓡 3) (𝓡 3) ThreeSpace M.Carrier ∞)
    (hA : _root_.Metric.closedBall (0 : ThreeSpace) 1 ⊆ A.source)
    (b : T.Boundary) (hfront : A '' _root_.Metric.sphere (0 : ThreeSpace) 1 = _root_.Set.range (T.boundarySphere b))
    (hdis : Disjoint (A '' _root_.Metric.closedBall (0 : ThreeSpace) 1) (T.removedBand b.1))
    (q : Sphere 2) :
    isPoincareStandard
      (N.component (ConnectedComponents.mk (C.coreInclusion (T.coreBoundarySphere b q)))).Carrier := by
  have hAf : frontier (A '' _root_.Metric.closedBall (0 : ThreeSpace) 1) = _root_.Set.range (T.boundarySphere b) := by
    rw [← A.image_frontier_of_isCompact (_root_.ProperSpace.isCompact_closedBall _ _) hA,
      frontier_closedBall _ one_ne_zero,hfront]
  have hq : T.boundarySphere b q ∈ A '' _root_.Metric.closedBall (0 : ThreeSpace) 1 :=
    _root_.Set.image_mono _root_.Metric.sphere_subset_closedBall (hfront.symm ▸ _root_.Set.mem_range_self q)
  apply C.isPoincareStandard_component_of_ball_containing_coreComponent
    (T.coreBoundarySphere b q) A hA b hfront ⟨q,mem_connectedComponent⟩
  rintro y ⟨z,hz,rfl⟩
  exact T.toTopological.connectedComponent_subset_preimage_of_capCore_of_boundarySphere
    (CapCore.ball A hA rfl) b hdis hAf (T.smooth b.1) (T.coreBoundarySphere b q) hq hz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping.isPoincareStandard_component_of_ball_cutting_side then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping.isPoincareStandard_component_of_ball_cutting_side"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping.isPoincareStandard_component_of_ball_cutting_side ``Submission.DifferentialGeometry.Topology.SphericalCapping.isPoincareStandard_component_of_ball_cutting_side

end DifferentialGeometry.Topology.SphericalCapping

namespace DifferentialGeometry.Topology.SphericalCutCapTransition

universe u
variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)

theorem isPoincareStandard_discardedComponent_of_ball_cutting_side
    (A : PartialDiffeomorph (𝓡 3) (𝓡 3) ThreeSpace M.Carrier ∞)
    (hA : _root_.Metric.closedBall (0 : ThreeSpace) 1 ⊆ A.source)
    (b : E.tubes.Boundary)
    (hfront : A '' _root_.Metric.sphere (0 : ThreeSpace) 1 = _root_.Set.range (E.tubes.boundarySphere b))
    (hdis : Disjoint (A '' _root_.Metric.closedBall (0 : ThreeSpace) 1) (E.tubes.removedBand b.1))
    (q : Sphere 2) (d : E.discarded.Carrier)
    (hd : E.presentation (E.capping.coreInclusion (E.tubes.coreBoundarySphere b q)) = Sum.inr d) :
    isPoincareStandard (E.discarded.component (ConnectedComponents.mk d)).Carrier := by
  have hstd := E.capping.isPoincareStandard_component_of_ball_cutting_side A hA b hfront hdis q
  obtain ⟨e⟩ := E.cappedDiscardedPresentationRealization (E.tubes.coreBoundarySphere b q) d hd
  exact isPoincareStandard_of_diffeomorph e.val.symm hstd

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.isPoincareStandard_discardedComponent_of_ball_cutting_side then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.isPoincareStandard_discardedComponent_of_ball_cutting_side"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.isPoincareStandard_discardedComponent_of_ball_cutting_side ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.isPoincareStandard_discardedComponent_of_ball_cutting_side

end DifferentialGeometry.Topology.SphericalCutCapTransition

end

section

namespace DifferentialGeometry.Topology.SphericalCapping

universe u
variable {M N : ClosedOrientedManifold.{u} 3} {T : SphericalTubeSystem M}
  (C : SphericalCapping M N T)

private theorem image_coreComponent_union_caps_eq_componentSet_of_frontier
    (x : T.core) (outer : T.Boundary) (s : Finset T.Boundary)
    (hfront : frontier ((Subtype.val : T.core → M.Carrier) '' connectedComponent x) =
      _root_.Set.range (T.boundarySphere outer) ∪ ⋃ b ∈ s, _root_.Set.range (T.boundarySphere b)) :
    (C.coreInclusion '' connectedComponent x ∪ ⋃ b ∈ s, _root_.Set.range (C.cap b)) ∪
      range (C.cap outer) = N.componentSet (ConnectedComponents.mk (C.coreInclusion x)) := by
  classical
  let W := (Subtype.val : T.core → M.Carrier) '' connectedComponent x
  obtain ⟨hWc,_,_,_,_⟩ := C.coreComponent_geometry x
  have hWcore : W ⊆ T.core := by
    rintro y ⟨z,_,rfl⟩
    exact z.property
  have hmem {y : T.core} (hy : y.val ∈ W) : y ∈ connectedComponent x := by
    obtain ⟨z,hz,hzy⟩ := hy
    exact (Subtype.ext hzy : z=y) ▸ hz
  have hbmem (b : T.Boundary) (hb : b=outer ∨ b∈s) (q : Sphere 2) :
      T.coreBoundarySphere b q ∈ connectedComponent x := by
    apply hmem
    apply hWc.isClosed.frontier_subset
    change T.boundarySphere b q ∈ frontier W
    rw [hfront]
    rcases hb with rfl | hb
    · exact Or.inl (_root_.Set.mem_range_self q)
    · exact Or.inr (mem_iUnion₂.mpr ⟨b,hb,_root_.Set.mem_range_self q⟩)
  have hexact (b : T.Boundary)
      (hb : ∃ q : Sphere 2, T.coreBoundarySphere b q ∈ connectedComponent x) : b=outer ∨ b∈s := by
    obtain ⟨q,hq⟩ := hb
    have hqW : T.boundarySphere b q ∈ W := _root_.Set.mem_image_of_mem Subtype.val hq
    have hqnot : T.boundarySphere b q ∉ interior W := by
      intro hin
      have hh := T.toTopological.boundarySphere_mem_closure_removedBand b q
      obtain ⟨y,hyint,hyband⟩ := (mem_closure_iff_nhds.mp hh) (interior W) (isOpen_interior.mem_nhds hin)
      exact hWcore (interior_subset hyint) (mem_iUnion.mpr ⟨b.1,hyband⟩)
    have hqf : T.boundarySphere b q ∈ frontier W := (mem_frontier_iff_notMem_interior hqW).mpr hqnot
    rw [hfront] at hqf
    rcases hqf with ⟨z,hz⟩ | hh
    · exact Or.inl ((T.toTopological.boundarySphere_eq_iff b outer q z).mp hz.symm).1
    · obtain ⟨b',hb',z,hz⟩ := mem_iUnion₂.mp hh
      have heq := ((T.toTopological.boundarySphere_eq_iff b b' q z).mp hz.symm).1
      exact Or.inr (heq.symm ▸ hb')
  have hc := C.image_coreComponent_union_caps_eq_connectedComponent x
    (_root_.Insert.insert outer (s : Set T.Boundary))
    (fun b hb q => hbmem b (by simpa only [_root_.Set.mem_insert_iff,Finset.mem_coe] using hb) q)
    (fun b hb => by simpa only [_root_.Set.mem_insert_iff,Finset.mem_coe] using hexact b hb)
  rw [ClosedOrientedManifold.componentSet_mk,← hc]
  ext y
  constructor
  · rintro ((hy | hy) | hy)
    · exact Or.inl hy
    · obtain ⟨b,hb,hyb⟩ := mem_iUnion₂.mp hy
      exact Or.inr (mem_iUnion₂.mpr ⟨b,Or.inr hb,hyb⟩)
    · exact Or.inr (mem_iUnion₂.mpr ⟨outer,Or.inl rfl,hy⟩)
  · rintro (hy | hy)
    · exact Or.inl (Or.inl hy)
    · obtain ⟨b,hb,hyb⟩ := mem_iUnion₂.mp hy
      rcases hb with rfl | hb
      · exact Or.inr hyb
      · exact Or.inl (Or.inr (mem_iUnion₂.mpr ⟨b,hb,hyb⟩))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphericalCapping.image_coreComponent_union_caps_eq_componentSet_of_frontier
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphericalCapping.image_coreComponent_union_caps_eq_componentSet_of_frontier target :: scope.openDecls } }

end DifferentialGeometry.Topology.SphericalCapping

end

section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

universe u
variable {Z M N : Type u} {ι : Type*} [Finite ι]
  [TopologicalSpace Z] [ChartedSpace ThreeSpace Z] [IsManifold I3 ∞ Z] [T2Space Z] [CompactSpace Z]
  [TopologicalSpace M] [ChartedSpace ThreeSpace M] [T3Space M]
  [TopologicalSpace N] [ChartedSpace ThreeSpace N] [T2Space N]

private theorem nonempty_capCore_of_recapped_projective_holes
    (pr : ProjectivePresentation Z)
    (C : PartialDiffeomorph I3 I3 ThreeSpace Z ∞)
    (F : PartialDiffeomorph I3 I3 Z M ∞)
    (hC : _root_.Metric.closedBall (0 : ThreeSpace) 2 ⊆ C.source)
    (hF : (C '' _root_.Metric.ball (0 : ThreeSpace) 1)ᶜ ⊆ F.source)
    (K : ι → Set M) (B : ι → PartialDiffeomorph I3 I3 ThreeSpace Z ∞)
    (hB : ∀ i, _root_.Metric.closedBall (0 : ThreeSpace) 1 ⊆ (B i).source)
    (hmodel : ∀ i, (B i '' _root_.Metric.closedBall (0 : ThreeSpace) 1 ⊆ (C '' _root_.Metric.closedBall (0 : ThreeSpace) 1)ᶜ ∧
      F '' (B i '' _root_.Metric.closedBall (0 : ThreeSpace) 1) = K i ∧ F '' (B i '' _root_.Metric.ball (0 : ThreeSpace) 1) = interior (K i)) ∨
      ((B i '' _root_.Metric.ball (0 : ThreeSpace) 1)ᶜ ⊆ (C '' _root_.Metric.closedBall (0 : ThreeSpace) 1)ᶜ ∧
      F '' (B i '' _root_.Metric.ball (0 : ThreeSpace) 1)ᶜ = K i ∧ F '' (B i '' _root_.Metric.closedBall (0 : ThreeSpace) 1)ᶜ = interior (K i)))
    (hKc : ∀ i, IsClosed (K i))
    (hKf : ∀ i, F '' (B i '' _root_.Metric.sphere (0 : ThreeSpace) 1) = frontier (K i))
    (hKin : ∀ i, K i ⊆ interior (F '' (C '' _root_.Metric.ball (0 : ThreeSpace) 1)ᶜ))
    (hpair : Pairwise (fun i j => Disjoint (K i) (K j)))
    (hunique : ∀ i j, F '' (B i '' _root_.Metric.ball (0 : ThreeSpace) 1)ᶜ = K i →
      F '' (B j '' _root_.Metric.ball (0 : ThreeSpace) 1)ᶜ = K j → i = j)
    {W : Set M} (hW : W = F '' (C '' _root_.Metric.ball (0 : ThreeSpace) 1)ᶜ \ ⋃ i, interior (K i))
    (P : PartialDiffeomorph I3 I3 M N ∞) (hP : W ⊆ P.source)
    (G : ι → PartialDiffeomorph I3 I3 ThreeSpace N ∞)
    (hG : ∀ i, _root_.Metric.closedBall (0 : ThreeSpace) 1 ⊆ (G i).source)
    (hGpair : Pairwise (fun i j => Disjoint (G i '' _root_.Metric.closedBall (0 : ThreeSpace) 1) (G j '' _root_.Metric.closedBall (0 : ThreeSpace) 1)))
    (hboundary : ∀ i, P '' frontier (K i) = G i '' _root_.Metric.sphere (0 : ThreeSpace) 1)
    (hinter : ∀ i, P '' W ∩ G i '' _root_.Metric.closedBall (0 : ThreeSpace) 1 ⊆ G i '' _root_.Metric.sphere (0 : ThreeSpace) 1) :
    Nonempty (CapCore (P '' W ∪ ⋃ i, G i '' _root_.Metric.closedBall (0 : ThreeSpace) 1)) := by
  classical
  let _ := Fintype.ofFinite ι
  let Ω := F '' (C '' _root_.Metric.ball (0 : ThreeSpace) 1)ᶜ
  let b : ι → PartialDiffeomorph I3 I3 ThreeSpace M ∞ := fun i => (B i).trans F
  have houter : CapCore Ω := CapCore.projective Z pr C hC F hF rfl
  have hcomp (i : ι) (s : Set ThreeSpace) : b i '' s = F '' (B i '' s) := by
    rw [_root_.Set.image_image]
    rfl
  have hball (i : ι)
      (hi : B i '' _root_.Metric.closedBall (0 : ThreeSpace) 1 ⊆ (C '' _root_.Metric.closedBall (0 : ThreeSpace) 1)ᶜ ∧
        F '' (B i '' _root_.Metric.closedBall (0 : ThreeSpace) 1) = K i ∧ F '' (B i '' _root_.Metric.ball (0 : ThreeSpace) 1) = interior (K i)) :
      _root_.Metric.closedBall (0 : ThreeSpace) 1 ⊆ (b i).source ∧
      b i '' _root_.Metric.closedBall (0 : ThreeSpace) 1 = K i ∧
      b i '' _root_.Metric.ball (0 : ThreeSpace) 1 = interior (K i) := by
    refine ⟨?_,(hcomp i _).trans hi.2.1,(hcomp i _).trans hi.2.2⟩
    intro z hz
    exact ⟨hB i hz,hF (fun hx => hi.1 (_root_.Set.mem_image_of_mem (B i) hz) (_root_.Set.image_mono _root_.Metric.ball_subset_closedBall hx))⟩
  have hbfr (i : ι) : P '' (b i '' _root_.Metric.sphere (0 : ThreeSpace) 1) = G i '' _root_.Metric.sphere (0 : ThreeSpace) 1 := by
    rw [hcomp,hKf,hboundary]
  by_cases he : ∃ j, (B j '' _root_.Metric.ball (0 : ThreeSpace) 1)ᶜ ⊆ (C '' _root_.Metric.closedBall (0 : ThreeSpace) 1)ᶜ ∧
      F '' (B j '' _root_.Metric.ball (0 : ThreeSpace) 1)ᶜ = K j ∧
      F '' (B j '' _root_.Metric.closedBall (0 : ThreeSpace) 1)ᶜ = interior (K j)
  · obtain ⟨j,hjside,hj,hji⟩ := he
    have hbdata (i : ι) (hi : i ∈ (Finset.univ.erase j : Finset ι)) :
        _root_.Metric.closedBall (0 : ThreeSpace) 1 ⊆ (b i).source ∧ b i '' _root_.Metric.closedBall (0 : ThreeSpace) 1 = K i ∧
          b i '' _root_.Metric.ball (0 : ThreeSpace) 1 = interior (K i) := by
      rcases hmodel i with h | h
      · exact hball i h
      · exact ((Finset.mem_erase.mp hi).1 (hunique i j h.2.1 hj)).elim
    have hWi : W = Ω \ (interior (K j) ∪ ⋃ i ∈ Finset.univ.erase j, b i '' _root_.Metric.ball (0 : ThreeSpace) 1) := by
      rw [hW]
      congr 1
      ext x
      constructor
      · intro hx
        obtain ⟨i,hi⟩ := mem_iUnion.mp hx
        by_cases hij : i=j
        · exact Or.inl (hij ▸ hi)
        · exact Or.inr (mem_iUnion₂.mpr ⟨i,Finset.mem_erase.mpr ⟨hij,Finset.mem_univ _⟩,
            (hbdata i (Finset.mem_erase.mpr ⟨hij,Finset.mem_univ _⟩)).2.2.symm ▸ hi⟩)
      · rintro (hx | hx)
        · exact mem_iUnion.mpr ⟨j,hx⟩
        · obtain ⟨i,hi,hx⟩ := mem_iUnion₂.mp hx
          exact mem_iUnion.mpr ⟨i,(hbdata i hi).2.2 ▸ hx⟩
    obtain ⟨A,_,_,hA,_,_,hAi,_,_,_,_,_,_,_,_,_⟩ :=
      DifferentialGeometry.Topology.ThreeManifold.exists_ball_chart_of_finitely_recapped_nested_ball_complements
        C (B j) F P (G j) (Finset.univ.erase j) b G
        ((_root_.Metric.closedBall_subset_closedBall (by norm_num)).trans hC) (hB j) (hG j)
        (fun i hi => (hbdata i hi).1) (fun i _ => hG i) hF hjside (hKc j) hji (hKf j)
        (hKin j) (fun i hi => (hbdata i hi).2.1.symm ▸ hKin i)
        (fun i hi => (hbdata i hi).2.1.symm ▸ hpair (Finset.mem_erase.mp hi).1)
        (fun i hi k hk hik => by
          change Disjoint (b i '' _root_.Metric.closedBall (0 : ThreeSpace) 1) (b k '' _root_.Metric.closedBall (0 : ThreeSpace) 1)
          rw [(hbdata i hi).2.1,(hbdata k hk).2.1]
          exact hpair hik)
        (fun i _ k _ hik => hGpair hik) (fun i hi => hGpair (Finset.mem_erase.mp hi).1)
        hWi hP (fun i _ => hbfr i) (hboundary j) (fun i _ => hinter i) (hinter j)
    have htarget : (P '' W ∪ ⋃ i ∈ Finset.univ.erase j, G i '' _root_.Metric.closedBall (0 : ThreeSpace) 1) ∪
        G j '' _root_.Metric.closedBall (0 : ThreeSpace) 1 = P '' W ∪ ⋃ i, G i '' _root_.Metric.closedBall (0 : ThreeSpace) 1 := by
      ext x
      constructor
      · rintro ((hx | hx) | hx)
        · exact Or.inl hx
        · obtain ⟨i,_,hxi⟩ := mem_iUnion₂.mp hx
          exact Or.inr (mem_iUnion.mpr ⟨i,hxi⟩)
        · exact Or.inr (mem_iUnion.mpr ⟨j,hx⟩)
      · rintro (hx | hx)
        · exact Or.inl (Or.inl hx)
        · obtain ⟨i,hxi⟩ := mem_iUnion.mp hx
          by_cases hij : i=j
          · exact Or.inr (hij ▸ hxi)
          · exact Or.inl (Or.inr (mem_iUnion₂.mpr ⟨i,Finset.mem_erase.mpr ⟨hij,Finset.mem_univ _⟩,hxi⟩))
    exact ⟨CapCore.ball A hA (hAi.trans htarget)⟩
  · have hbdata (i : ι) : _root_.Metric.closedBall (0 : ThreeSpace) 1 ⊆ (b i).source ∧
        b i '' _root_.Metric.closedBall (0 : ThreeSpace) 1 = K i ∧ b i '' _root_.Metric.ball (0 : ThreeSpace) 1 = interior (K i) := by
      rcases hmodel i with h | h
      · exact hball i h
      · exact (he ⟨i,h⟩).elim
    have hres : Ω \ ⋃ i ∈ (Finset.univ : Finset ι), b i '' _root_.Metric.ball (0 : ThreeSpace) 1 = W := by
      rw [hW]
      congr 1
      simp only [Finset.mem_univ,_root_.Set.iUnion_true]
      apply _root_.Set.iUnion_congr
      intro i
      exact (hbdata i).2.2
    have hc := houter.nonempty_finite_ball_replacement Finset.univ b G
      (fun i _ => (hbdata i).1) (fun i _ => hG i)
      (fun i _ => (hbdata i).2.1.symm ▸ hKin i)
      (fun i _ j _ hij => by
        change Disjoint (b i '' _root_.Metric.closedBall (0 : ThreeSpace) 1) (b j '' _root_.Metric.closedBall (0 : ThreeSpace) 1)
        rw [(hbdata i).2.1,(hbdata j).2.1]
        exact hpair hij)
      (fun i _ j _ hij => hGpair hij) P (hres.symm ▸ hP) (fun i _ => hbfr i)
      (fun i _ => hres.symm ▸ hinter i)
    have hi : P '' (Ω \ ⋃ i ∈ (Finset.univ : Finset ι), b i '' _root_.Metric.ball (0 : ThreeSpace) 1) ∪
        (⋃ i ∈ (Finset.univ : Finset ι), G i '' _root_.Metric.closedBall (0 : ThreeSpace) 1) =
        P '' W ∪ ⋃ i, G i '' _root_.Metric.closedBall (0 : ThreeSpace) 1 := by
      rw [hres]
      simp only [Finset.mem_univ,_root_.Set.iUnion_true]
    exact hi ▸ hc.1

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.nonempty_capCore_of_recapped_projective_holes
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.nonempty_capCore_of_recapped_projective_holes target :: scope.openDecls } }

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

section

namespace DifferentialGeometry.Topology.SphericalCapping

universe u
variable {M N : ClosedOrientedManifold.{u} 3} {T : SphericalTubeSystem M}
  (C : SphericalCapping M N T)

theorem isPoincareStandard_component_of_projective_spherical_frontier
    {Z : Type u} [TopologicalSpace Z] [ChartedSpace ThreeSpace Z]
    [IsManifold I3 ∞ Z] [T2Space Z] [CompactSpace Z]
    (pr : ProjectivePresentation Z)
    (A : PartialDiffeomorph I3 I3 ThreeSpace Z ∞)
    (F : PartialDiffeomorph I3 I3 Z M.Carrier ∞)
    (hA : _root_.Metric.closedBall (0 : ThreeSpace) 2 ⊆ A.source)
    (hF : (A '' _root_.Metric.ball (0 : ThreeSpace) 1)ᶜ ⊆ F.source)
    (x : T.core) (outer : T.Boundary)
    (houter : F '' (A '' _root_.Metric.sphere (0 : ThreeSpace) 1) = _root_.Set.range (T.boundarySphere outer))
    (s : Finset T.Boundary)
    (hregular : closure (interior ((Subtype.val : T.core → M.Carrier) '' connectedComponent x)) =
      (Subtype.val : T.core → M.Carrier) '' connectedComponent x)
    (hconnected : IsPreconnected (interior ((Subtype.val : T.core → M.Carrier) '' connectedComponent x)))
    (hcontained : (Subtype.val : T.core → M.Carrier) '' connectedComponent x ⊆ F '' (A '' _root_.Metric.ball (0 : ThreeSpace) 1)ᶜ)
    (hinside : ∀ b ∈ s, _root_.Set.range (T.boundarySphere b) ⊆ interior (F '' (A '' _root_.Metric.ball (0 : ThreeSpace) 1)ᶜ))
    (hfront : frontier ((Subtype.val : T.core → M.Carrier) '' connectedComponent x) =
      _root_.Set.range (T.boundarySphere outer) ∪ ⋃ b ∈ s, _root_.Set.range (T.boundarySphere b)) :
    isPoincareStandard (N.component (ConnectedComponents.mk (C.coreInclusion x))).Carrier := by
  classical
  let I := {b : T.Boundary // b ∈ s}
  let W := (Subtype.val : T.core → M.Carrier) '' connectedComponent x
  have hsmooth (b : I) : _root_.Manifold.IsSmoothEmbedding I2 I3 ∞ (T.boundarySphere b.val) :=
    T.toTopological.isSmoothEmbedding_boundarySphere b.val (T.smooth b.val.1)
  have hfr : frontier W = F '' (A '' _root_.Metric.sphere (0 : ThreeSpace) 1) ∪ ⋃ b : I, _root_.Set.range (T.boundarySphere b.val) := by
    rw [houter,_root_.Set.iUnion_subtype]
    exact hfront
  have hpair : Pairwise (fun b c : I => Disjoint (_root_.Set.range (T.boundarySphere b.val)) (_root_.Set.range (T.boundarySphere c.val))) := by
    intro b c hbc
    exact T.toTopological.pairwise_disjoint_range_boundarySphere (fun he => hbc (Subtype.ext he))
  obtain ⟨K,B,hB,hBs,hmodel,hKc,_,hKf,hKin,_,_,hdis,hunique,_,hW⟩ :=
    ThreeManifold.exists_finite_disjoint_projective_cap_holes_of_spherical_frontier
      pr.quotient pr.isLocalDiffeomorph pr.onto pr.fibers A F
      ((_root_.Metric.closedBall_subset_closedBall (by norm_num)).trans hA) hF
      hregular hconnected hcontained (fun b : I => T.boundarySphere b.val) hsmooth
      (fun b => hinside b.val b.property) hfr hpair
  obtain ⟨P,hPsource,_,hPeq,_⟩ := C.exists_core_neighborhood_partialDiffeomorph x
  have hP : W ⊆ P.source := by
    rintro y ⟨z,_,rfl⟩
    exact hPsource z.property
  have hPW : P '' W = C.coreInclusion '' connectedComponent x := by
    rw [_root_.Set.image_image]
    apply _root_.Set.image_congr
    intro z _
    exact hPeq z
  choose G hG _ hGc hGs using C.exists_cap_partialDiffeomorph
  have hGb : Pairwise (fun i j : I => Disjoint (G i.val '' _root_.Metric.closedBall (0 : ThreeSpace) 1)
      (G j.val '' _root_.Metric.closedBall (0 : ThreeSpace) 1)) := by
    intro i j hij
    rw [hGc,hGc]
    exact C.cap_disjoint (fun h => hij (Subtype.ext h))
  have hbound (i : I) : P '' frontier (K i) = G i.val '' _root_.Metric.sphere (0 : ThreeSpace) 1 := by
    rw [hKf,hGs]
    ext y
    constructor
    · rintro ⟨_,⟨q,rfl⟩,rfl⟩
      exact ⟨q,(hPeq (T.coreBoundarySphere i.val q)).symm⟩
    · rintro ⟨q,rfl⟩
      exact ⟨T.boundarySphere i.val q,_root_.Set.mem_range_self q,hPeq (T.coreBoundarySphere i.val q)⟩
  have hint (i : I) : P '' W ∩ G i.val '' _root_.Metric.closedBall (0 : ThreeSpace) 1 ⊆ G i.val '' _root_.Metric.sphere (0 : ThreeSpace) 1 := by
    rw [hPW,hGc,hGs]
    exact (_root_.Set.inter_subset_inter_left _ (_root_.Set.image_subset_range _ _)).trans (C.core_cap_intersection i.val).subset
  obtain ⟨hcap⟩ := nonempty_capCore_of_recapped_projective_holes pr A F hA hF
    K B hB hmodel (fun i => (hKc i).isClosed) (fun i => (hBs i).trans (hKf i).symm)
    hKin hdis hunique hW P hP (fun i : I => G i.val) (fun i => hG i.val) hGb hbound hint
  have heq : P '' W ∪ (⋃ i : I, G i.val '' _root_.Metric.closedBall (0 : ThreeSpace) 1) =
      C.coreInclusion '' connectedComponent x ∪ ⋃ b ∈ s, _root_.Set.range (C.cap b) := by
    rw [hPW]
    congr 1
    change (⋃ i : {b : T.Boundary // b ∈ s}, G i.val '' _root_.Metric.closedBall (0 : ThreeSpace) 1) = _
    rw [_root_.Set.iUnion_subtype]
    simp only [hGc]
  apply C.isPoincareStandard_component_of_capCore_union_cap (heq ▸ hcap) outer _
  exact image_coreComponent_union_caps_eq_componentSet_of_frontier C x outer s hfront

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping.isPoincareStandard_component_of_projective_spherical_frontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping.isPoincareStandard_component_of_projective_spherical_frontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping.isPoincareStandard_component_of_projective_spherical_frontier ``Submission.DifferentialGeometry.Topology.SphericalCapping.isPoincareStandard_component_of_projective_spherical_frontier

end DifferentialGeometry.Topology.SphericalCapping

end

section

namespace DifferentialGeometry.Topology.SphericalCapping

universe u
variable {M N : ClosedOrientedManifold.{u} 3} {T : SphericalTubeSystem M}
  (C : SphericalCapping M N T)

theorem isPoincareStandard_component_of_projective_containing_coreComponent
    {Z : Type u} [TopologicalSpace Z] [ChartedSpace ThreeSpace Z]
    [IsManifold I3 ∞ Z] [T2Space Z] [CompactSpace Z]
    (pr : ProjectivePresentation Z)
    (A : PartialDiffeomorph I3 I3 ThreeSpace Z ∞)
    (F : PartialDiffeomorph I3 I3 Z M.Carrier ∞)
    (hA : _root_.Metric.closedBall (0 : ThreeSpace) 2 ⊆ A.source)
    (hF : (A '' _root_.Metric.ball (0 : ThreeSpace) 1)ᶜ ⊆ F.source)
    (x : T.core)
    (outer : T.Boundary)
    (houter : F '' (A '' _root_.Metric.sphere (0 : ThreeSpace) 1) = _root_.Set.range (T.boundarySphere outer))
    (houter_mem : ∃ q : Sphere 2, T.coreBoundarySphere outer q ∈ connectedComponent x)
    (hcontained : (Subtype.val : T.core → M.Carrier) '' connectedComponent x ⊆
      F '' (A '' _root_.Metric.ball (0 : ThreeSpace) 1)ᶜ) :
    isPoincareStandard (N.component (ConnectedComponents.mk (C.coreInclusion x))).Carrier := by
  classical
  let _ : ConnectedSpace (Sphere 2) := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp [ThreeSpace]))
      (0 : ThreeSpace) zero_le_one)
  have hA1 : _root_.Metric.closedBall (0 : ThreeSpace) 1 ⊆ A.source :=
    (_root_.Metric.closedBall_subset_closedBall (by norm_num)).trans hA
  have hΩc : IsCompact (A '' _root_.Metric.ball (0 : ThreeSpace) 1)ᶜ :=
    (A.toOpenPartialHomeomorph.isOpen_image_of_subset_source _root_.Metric.isOpen_ball
      (ball_subset_closedBall.trans hA1)).isClosed_compl.isCompact
  have hAfr : frontier (F '' (A '' _root_.Metric.ball (0 : ThreeSpace) 1)ᶜ) = _root_.Set.range (T.boundarySphere outer) :=
    (DifferentialGeometry.Topology.Manifold.image_sphere_eq_frontier_of_ball_complement A F hA1 hΩc hF).symm.trans houter
  have hinside (b : T.Boundary) (hb : b ≠ outer)
      (hbmem : ∃ q : Sphere 2, T.coreBoundarySphere b q ∈ connectedComponent x) :
      range (T.boundarySphere b) ⊆ interior (F '' (A '' _root_.Metric.ball (0 : ThreeSpace) 1)ᶜ) := by
    obtain ⟨q₀,hq₀⟩ := hbmem
    rintro y ⟨q,rfl⟩
    have hpre := isPreconnected_range (T.coreBoundarySphere b).continuous
    have hq : T.coreBoundarySphere b q ∈ connectedComponent x := by
      have hh := hpre.subset_connectedComponent (_root_.Set.mem_range_self q₀) (_root_.Set.mem_range_self q)
      rwa [← connectedComponent_eq hq₀] at hh
    have hclosed : T.boundarySphere b q ∈ F '' (A '' _root_.Metric.ball (0 : ThreeSpace) 1)ᶜ :=
      hcontained (_root_.Set.mem_image_of_mem Subtype.val hq)
    apply (mem_interior_iff_notMem_frontier hclosed).mpr
    intro hyfront
    obtain ⟨r,hr⟩ := hAfr ▸ hyfront
    exact hb ((T.toTopological.boundarySphere_eq_iff b outer q r).mp hr.symm).1
  let s : Finset T.Boundary := Finset.univ.filter (fun b => b ≠ outer ∧
    ∃ q : Sphere 2, T.coreBoundarySphere b q ∈ connectedComponent x)
  obtain ⟨_,_,hregular,hconnected,hfront⟩ := C.coreComponent_geometry x
  have hinside' : ∀ b ∈ s, _root_.Set.range (T.boundarySphere b) ⊆ interior (F '' (A '' _root_.Metric.ball (0 : ThreeSpace) 1)ᶜ) := by
    intro b hb
    obtain ⟨hne,hbcomp⟩ := (Finset.mem_filter.mp hb).2
    exact hinside b hne hbcomp
  have hfront' : frontier ((Subtype.val : T.core → M.Carrier) '' connectedComponent x) =
      range (T.boundarySphere outer) ∪ ⋃ b ∈ s, _root_.Set.range (T.boundarySphere b) := by
    rw [hfront]
    ext y
    constructor
    · intro hy
      obtain ⟨b,hb⟩ := mem_iUnion.mp hy
      by_cases he : b.val = outer
      · exact Or.inl (he ▸ hb)
      · exact Or.inr (mem_iUnion₂.mpr ⟨b.val,Finset.mem_filter.mpr
          ⟨Finset.mem_univ _,he,b.property⟩,hb⟩)
    · rintro (hy | hy)
      · exact mem_iUnion.mpr ⟨⟨outer,houter_mem⟩,hy⟩
      · obtain ⟨b,hb,hy⟩ := mem_iUnion₂.mp hy
        exact mem_iUnion.mpr ⟨⟨b,(Finset.mem_filter.mp hb).2.2⟩,hy⟩
  exact C.isPoincareStandard_component_of_projective_spherical_frontier pr A F hA hF x outer houter s
    hregular hconnected hcontained hinside' hfront'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping.isPoincareStandard_component_of_projective_containing_coreComponent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping.isPoincareStandard_component_of_projective_containing_coreComponent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping.isPoincareStandard_component_of_projective_containing_coreComponent ``Submission.DifferentialGeometry.Topology.SphericalCapping.isPoincareStandard_component_of_projective_containing_coreComponent


end DifferentialGeometry.Topology.SphericalCapping

end

section

namespace DifferentialGeometry.Topology.SphericalCapping

universe u
variable {M N : ClosedOrientedManifold.{u} 3} {T : SphericalTubeSystem M}
  (C : SphericalCapping M N T)

theorem isPoincareStandard_component_of_projective_cutting_side
    {Z : Type u} [TopologicalSpace Z] [ChartedSpace ThreeSpace Z]
    [IsManifold I3 ∞ Z] [T2Space Z] [CompactSpace Z]
    (pr : ProjectivePresentation Z)
    (A : PartialDiffeomorph I3 I3 ThreeSpace Z ∞)
    (F : PartialDiffeomorph I3 I3 Z M.Carrier ∞)
    (hA : _root_.Metric.closedBall (0 : ThreeSpace) 2 ⊆ A.source)
    (hF : (A '' _root_.Metric.ball (0 : ThreeSpace) 1)ᶜ ⊆ F.source)
    (b : T.Boundary)
    (hfront : F '' (A '' _root_.Metric.sphere (0 : ThreeSpace) 1) = _root_.Set.range (T.boundarySphere b))
    (hdis : Disjoint (F '' (A '' _root_.Metric.ball (0 : ThreeSpace) 1)ᶜ) (T.removedBand b.1))
    (q : Sphere 2) :
    isPoincareStandard
      (N.component (ConnectedComponents.mk (C.coreInclusion (T.coreBoundarySphere b q)))).Carrier := by
  let cap : CapCore (F '' (A '' _root_.Metric.ball (0 : ThreeSpace) 1)ᶜ) :=
    CapCore.projective Z pr A hA F hF rfl
  have hA1 : _root_.Metric.closedBall (0 : ThreeSpace) 1 ⊆ A.source :=
    (_root_.Metric.closedBall_subset_closedBall (by norm_num)).trans hA
  have hΩc : IsCompact (A '' _root_.Metric.ball (0 : ThreeSpace) 1)ᶜ :=
    (A.toOpenPartialHomeomorph.isOpen_image_of_subset_source _root_.Metric.isOpen_ball
      (ball_subset_closedBall.trans hA1)).isClosed_compl.isCompact
  have hAf : frontier (F '' (A '' _root_.Metric.ball (0 : ThreeSpace) 1)ᶜ) = _root_.Set.range (T.boundarySphere b) :=
    (DifferentialGeometry.Topology.Manifold.image_sphere_eq_frontier_of_ball_complement A F hA1 hΩc hF).symm.trans hfront
  have hq : T.boundarySphere b q ∈ F '' (A '' _root_.Metric.ball (0 : ThreeSpace) 1)ᶜ :=
    cap.isCompact_carrier.isClosed.frontier_subset (hAf.symm ▸ _root_.Set.mem_range_self q)
  apply C.isPoincareStandard_component_of_projective_containing_coreComponent
    pr A F hA hF (T.coreBoundarySphere b q) b hfront ⟨q,mem_connectedComponent⟩
  rintro y ⟨z,hz,rfl⟩
  exact T.toTopological.connectedComponent_subset_preimage_of_capCore_of_boundarySphere
    cap b hdis hAf (T.smooth b.1) (T.coreBoundarySphere b q) hq hz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping.isPoincareStandard_component_of_projective_cutting_side then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping.isPoincareStandard_component_of_projective_cutting_side"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping.isPoincareStandard_component_of_projective_cutting_side ``Submission.DifferentialGeometry.Topology.SphericalCapping.isPoincareStandard_component_of_projective_cutting_side

end DifferentialGeometry.Topology.SphericalCapping

namespace DifferentialGeometry.Topology.SphericalCutCapTransition

universe u
variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)

theorem isPoincareStandard_discardedComponent_of_projective_cutting_side
    {Z : Type u} [TopologicalSpace Z] [ChartedSpace ThreeSpace Z]
    [IsManifold I3 ∞ Z] [T2Space Z] [CompactSpace Z]
    (pr : ProjectivePresentation Z)
    (A : PartialDiffeomorph I3 I3 ThreeSpace Z ∞)
    (F : PartialDiffeomorph I3 I3 Z M.Carrier ∞)
    (hA : _root_.Metric.closedBall (0 : ThreeSpace) 2 ⊆ A.source)
    (hF : (A '' _root_.Metric.ball (0 : ThreeSpace) 1)ᶜ ⊆ F.source)
    (b : E.tubes.Boundary)
    (hfront : F '' (A '' _root_.Metric.sphere (0 : ThreeSpace) 1) = _root_.Set.range (E.tubes.boundarySphere b))
    (hdis : Disjoint (F '' (A '' _root_.Metric.ball (0 : ThreeSpace) 1)ᶜ) (E.tubes.removedBand b.1))
    (q : Sphere 2) (d : E.discarded.Carrier)
    (hd : E.presentation (E.capping.coreInclusion (E.tubes.coreBoundarySphere b q)) = Sum.inr d) :
    isPoincareStandard (E.discarded.component (ConnectedComponents.mk d)).Carrier := by
  have hstd := E.capping.isPoincareStandard_component_of_projective_cutting_side pr A F hA hF b hfront hdis q
  obtain ⟨e⟩ := E.cappedDiscardedPresentationRealization (E.tubes.coreBoundarySphere b q) d hd
  exact isPoincareStandard_of_diffeomorph e.val.symm hstd

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.isPoincareStandard_discardedComponent_of_projective_cutting_side then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.isPoincareStandard_discardedComponent_of_projective_cutting_side"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.isPoincareStandard_discardedComponent_of_projective_cutting_side ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.isPoincareStandard_discardedComponent_of_projective_cutting_side

end DifferentialGeometry.Topology.SphericalCutCapTransition

end

section

namespace DifferentialGeometry.Topology.SphericalCapping

universe u
variable {M N : ClosedOrientedManifold.{u} 3} {T : SphericalTubeSystem M}
  (C : SphericalCapping M N T)

theorem isPoincareStandard_component_of_capCore_cutting_side
    {K : Set M.Carrier} (cap : CapCore K) (b : T.Boundary)
    (hfront : frontier K = _root_.Set.range (T.boundarySphere b))
    (hdis : Disjoint K (T.removedBand b.1)) (q : Sphere 2) :
    isPoincareStandard
      (N.component (ConnectedComponents.mk (C.coreInclusion (T.coreBoundarySphere b q)))).Carrier := by
  cases cap with
  | ball A hA hK =>
    have hAf : A '' _root_.Metric.sphere (0 : ThreeSpace) 1 = _root_.Set.range (T.boundarySphere b) := by
      have h := A.image_frontier_of_isCompact (_root_.ProperSpace.isCompact_closedBall (0 : ThreeSpace) 1) hA
      rw [frontier_closedBall _ one_ne_zero,hK,hfront] at h
      exact h
    exact C.isPoincareStandard_component_of_ball_cutting_side A hA b hAf (hK.symm ▸ hdis) q
  | projective Z pr A hA F hF hK =>
    have hA1 : _root_.Metric.closedBall (0 : ThreeSpace) 1 ⊆ A.source :=
      (_root_.Metric.closedBall_subset_closedBall (by norm_num)).trans hA
    have hΩ : IsCompact (A '' _root_.Metric.ball (0 : ThreeSpace) 1)ᶜ :=
      (A.toOpenPartialHomeomorph.isOpen_image_of_subset_source _root_.Metric.isOpen_ball
        (ball_subset_closedBall.trans hA1)).isClosed_compl.isCompact
    have hAf : F '' (A '' _root_.Metric.sphere (0 : ThreeSpace) 1) = _root_.Set.range (T.boundarySphere b) :=
      (DifferentialGeometry.Topology.Manifold.image_sphere_eq_frontier_of_ball_complement
        A F hA1 hΩ hF).trans ((congrArg frontier hK).trans hfront)
    exact C.isPoincareStandard_component_of_projective_cutting_side pr A F hA hF b hAf
      (hK.symm ▸ hdis) q

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping.isPoincareStandard_component_of_capCore_cutting_side then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping.isPoincareStandard_component_of_capCore_cutting_side"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping.isPoincareStandard_component_of_capCore_cutting_side ``Submission.DifferentialGeometry.Topology.SphericalCapping.isPoincareStandard_component_of_capCore_cutting_side

end DifferentialGeometry.Topology.SphericalCapping

namespace DifferentialGeometry.Topology.SphericalCutCapTransition

universe u
variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)

theorem isPoincareStandard_discardedComponent_of_capCore_cutting_side
    {K : Set M.Carrier} (cap : CapCore K) (b : E.tubes.Boundary)
    (hfront : frontier K = _root_.Set.range (E.tubes.boundarySphere b))
    (hdis : Disjoint K (E.tubes.removedBand b.1))
    (q : Sphere 2) (d : E.discarded.Carrier)
    (hd : E.presentation (E.capping.coreInclusion (E.tubes.coreBoundarySphere b q)) = Sum.inr d) :
    isPoincareStandard (E.discarded.component (ConnectedComponents.mk d)).Carrier := by
  have hstd := E.capping.isPoincareStandard_component_of_capCore_cutting_side cap b hfront hdis q
  obtain ⟨e⟩ := E.cappedDiscardedPresentationRealization (E.tubes.coreBoundarySphere b q) d hd
  exact isPoincareStandard_of_diffeomorph e.val.symm hstd

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.isPoincareStandard_discardedComponent_of_capCore_cutting_side then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.isPoincareStandard_discardedComponent_of_capCore_cutting_side"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.isPoincareStandard_discardedComponent_of_capCore_cutting_side ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.isPoincareStandard_discardedComponent_of_capCore_cutting_side

end DifferentialGeometry.Topology.SphericalCutCapTransition

end
