import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ProjectivePresentation
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CapRegionStructure
import Submission.DifferentialGeometry.Topology.ThreeManifold.TwoBallCover
import Submission.DifferentialGeometry.Topology.ThreeManifold.ProjectiveCapGluing
import Submission.DifferentialGeometry.Topology.ThreeManifold.ProjectiveCapCylinder
import Submission.DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Globalization

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M]

theorem nonempty_positiveComponent_of_ball_cap_cover
    {K : Set M} (B : PartialDiffeomorph I3 I3 ThreeSpace M ∞)
    (hB : Metric.closedBall (0 : ThreeSpace) 1 ⊆ B.source)
    (cap : CapCore K)
    (hcover : B '' Metric.closedBall (0 : ThreeSpace) 1 ∪ K = _root_.Set.univ) :
    Nonempty (PositiveComponent (_root_.Set.univ : Set M)) := by
  have hBK : IsConnected (B '' Metric.closedBall (0 : ThreeSpace) 1) :=
    capCore_isConnected_image_closedBall B hB
  have hK := cap.isConnected_carrier
  have hclosedK : IsClosed K := cap.isCompact_carrier.isClosed
  have hmeet : (B '' Metric.closedBall (0 : ThreeSpace) 1 ∩ K).Nonempty := by
    by_contra hn
    have hdisj : Disjoint (B '' Metric.closedBall (0 : ThreeSpace) 1) K :=
      Set.disjoint_iff_inter_eq_empty.mpr (Set.not_nonempty_iff_eq_empty.mp hn)
    have heq : (B '' Metric.closedBall (0 : ThreeSpace) 1)ᶜ = K := by
      ext x
      constructor
      · intro hx
        have hh : x ∈ B '' Metric.closedBall (0 : ThreeSpace) 1 ∪ K := hcover.symm ▸ Set.mem_univ x
        exact hh.resolve_left hx
      · intro hx hxb
        exact Set.disjoint_left.mp hdisj hxb hx
    have hopen : IsOpen (B '' Metric.closedBall (0 : ThreeSpace) 1) := by
      rw [← isClosed_compl_iff, heq]
      exact hclosedK
    have hclosed : IsClosed (B '' Metric.closedBall (0 : ThreeSpace) 1) :=
      ((_root_.ProperSpace.isCompact_closedBall (0 : ThreeSpace) 1).image_of_continuousOn
        (B.contMDiffOn_toFun.continuousOn.mono hB)).isClosed
    have hfront : frontier (B '' Metric.closedBall (0 : ThreeSpace) 1) = ∅ :=
      IsClopen.frontier_eq ⟨hclosed, hopen⟩
    have he := B.image_frontier_of_isCompact (_root_.ProperSpace.isCompact_closedBall (0 : ThreeSpace) 1) hB
    rw [frontier_closedBall _ one_ne_zero, hfront] at he
    have hz : (EuclideanSpace.single 0 1 : ThreeSpace) ∈ Metric.sphere 0 1 := by simp
    have hmem := Set.mem_image_of_mem B hz
    rw [he] at hmem
    exact hmem
  let _ : PreconnectedSpace M := ⟨hcover ▸ (hBK.union hmeet hK).isPreconnected⟩
  cases cap with
  | ball A hA hK =>
    obtain ⟨e, _⟩ :=
      DifferentialGeometry.Topology.Manifold.exists_sphere_diffeomorph_of_ball_chart_cover
        A B hA hB (hK.symm ▸ hcover)
    exact ⟨positiveComponentOfDiffeomorphSphereThree e.symm⟩
  | projective Z pr b hb F hF hK =>
    have hb1 : Metric.closedBall (0 : ThreeSpace) 1 ⊆ b.source :=
      (Metric.closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2)).trans hb
    rcases DifferentialGeometry.Topology.ThreeManifold.exists_sphere_or_projective_diffeomorph_of_cap_cover
      pr.quotient pr.isLocalDiffeomorph pr.onto pr.fibers b F B hb1 hF hB
      (hK.symm ▸ hcover) with ⟨e, _⟩ | ⟨e, _⟩
    · exact ⟨positiveComponentOfDiffeomorphSphereThree e.symm⟩
    · exact ⟨positiveComponentOfDiffeomorphProjective Z pr e.symm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.nonempty_positiveComponent_of_ball_cap_cover then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.nonempty_positiveComponent_of_ball_cap_cover"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.nonempty_positiveComponent_of_ball_cap_cover ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.nonempty_positiveComponent_of_ball_cap_cover

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Topology
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]

theorem isPoincareStandard_of_positiveComponent
    (W : PositiveComponent (_root_.Set.univ : Set M)) : isPoincareStandard M := by
  cases W with
  | sphere F hs ht =>
    let e := Perelman.KappaSolutions.globalDiffeomorphOfUniv F hs ht
    exact isPoincareStandard_of_diffeomorph
      (e.symm.trans standardThreeSphereLiftDiffeomorph) isPoincareStandard_sphere
  | projective Z pr F hs ht =>
    let e := Perelman.KappaSolutions.globalDiffeomorphOfUniv F hs ht
    exact isPoincareStandard_of_diffeomorph e.symm
      (isPoincareStandard_of_antipodal_presentation
        pr.quotient pr.isLocalDiffeomorph pr.onto pr.fibers)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isPoincareStandard_of_positiveComponent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isPoincareStandard_of_positiveComponent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isPoincareStandard_of_positiveComponent ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isPoincareStandard_of_positiveComponent

variable [IsManifold I3 ∞ M] [T2Space M]

private theorem isPoincareStandard_of_ball_cap_cover_generic
    {K : Set M} (B : PartialDiffeomorph I3 I3 ThreeSpace M ∞)
    (hB : Metric.closedBall (0 : ThreeSpace) 1 ⊆ B.source)
    (cap : CapCore K)
    (hcover : B '' Metric.closedBall (0 : ThreeSpace) 1 ∪ K = _root_.Set.univ) :
    isPoincareStandard M := by
  obtain ⟨W⟩ := nonempty_positiveComponent_of_ball_cap_cover B hB cap hcover
  exact isPoincareStandard_of_positiveComponent W

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isPoincareStandard_of_ball_cap_cover_generic
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isPoincareStandard_of_ball_cap_cover_generic target :: scope.openDecls } }

theorem isPoincareStandard_of_capCore_cover
    {K L : Set M} (capK : CapCore K) (capL : CapCore L)
    (hinter : L ∩ K = frontier K)
    (hcover : K ∪ L = _root_.Set.univ) : isPoincareStandard M := by
  have hfrontier : frontier L = frontier K := by
    have hL : L = (interior K)ᶜ := by
      ext x
      constructor
      · intro hx hxint
        have hxf : x ∈ frontier K := hinter ▸ ⟨hx, interior_subset hxint⟩
        exact (mem_interior_iff_notMem_frontier (interior_subset hxint)).mp hxint hxf
      · intro hx
        have hxu : x ∈ K ∪ L := hcover.symm ▸ _root_.Set.mem_univ x
        rcases hxu with hxK | hxL
        · have hxf : x ∈ frontier K := (mem_frontier_iff_notMem_interior hxK).mpr hx
          exact ((hinter.symm ▸ hxf : x ∈ L ∩ K)).1
        · exact hxL
    rw [hL, frontier_compl, frontier, capK.closure_interior_carrier, interior_interior,
      capK.isCompact_carrier.isClosed.frontier_eq]
  cases capK with
  | ball B hB hK =>
    exact isPoincareStandard_of_ball_cap_cover_generic B hB capL (hK.symm ▸ hcover)
  | projective Z₀ pr₀ b₀ hb₀ F₀ hF₀ hK =>
    cases capL with
    | ball B hB hL =>
      have cap : CapCore K := CapCore.projective Z₀ pr₀ b₀ hb₀ F₀ hF₀ hK
      apply isPoincareStandard_of_ball_cap_cover_generic B hB cap
      rw [hL, _root_.Set.union_comm]
      exact hcover
    | projective Z₁ pr₁ b₁ hb₁ F₁ hF₁ hL =>
      apply isPoincareStandard_of_projective_ball_complement_cover
        pr₀.quotient pr₁.quotient pr₀.isLocalDiffeomorph pr₁.isLocalDiffeomorph
        pr₀.onto pr₁.onto pr₀.fibers pr₁.fibers b₀ b₁ hb₀ hb₁ F₀ F₁ hF₀ hF₁
      · rwa [hK, hL]
      · rwa [hK, hL]
      · rwa [hK, hL]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isPoincareStandard_of_capCore_cover then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isPoincareStandard_of_capCore_cover"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isPoincareStandard_of_capCore_cover ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isPoincareStandard_of_capCore_cover

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
