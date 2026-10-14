import Submission.DifferentialGeometry.Topology.ThreeManifold.SmoothSchoenflies
import Submission.DifferentialGeometry.Topology.SphereSeparation.SmoothSchoenfliesBallFilling
import Submission.DifferentialGeometry.Topology.SphereSeparation.ReconstructionRegions
import Submission.DifferentialGeometry.Topology.Manifold.PartialChartEmbedding
import Submission.DifferentialGeometry.Topology.OpenPartialHomeomorph.Images

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Submission.Set _root_.Metric _root_.Submission.Metric _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.Topology.ThreeManifold

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.E3 target :: scope.openDecls } }
private abbrev S2 := Metric.sphere (0 : E3) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.S2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.S2 target :: scope.openDecls } }

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M]

theorem exists_ball_chart_of_compact_closure_sphere_frontier
    (A : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 M ∞)
    {C : Set M} (hC : IsOpen C) (hne : C.Nonempty) (hcompact : IsCompact (closure C))
    (hsource : closure C ⊆ A.target)
    (e : S2 → M) (he : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    (hfront : frontier C = _root_.Set.range e) :
    ∃ G : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 M ∞,
      _root_.Metric.closedBall (0 : E3) 1 ⊆ G.source ∧ G '' _root_.Metric.ball (0 : E3) 1 = C ∧
      G '' _root_.Metric.closedBall (0 : E3) 1 = closure C ∧
      G '' _root_.Metric.sphere (0 : E3) 1 = _root_.Set.range e := by
  let V := A.symm '' C
  have hCsource : C ⊆ A.target := subset_closure.trans hsource
  have hVopen : IsOpen V :=
    A.symm.toOpenPartialHomeomorph.isOpen_image_of_subset_source hC hCsource
  have hVne : V.Nonempty := hne.image A.symm
  have hK : IsCompact (A.symm '' closure C) :=
    hcompact.image_of_continuousOn (A.contMDiffOn_invFun.continuousOn.mono hsource)
  have hcl : closure V = A.symm '' closure C := by
    apply Subset.antisymm (closure_minimal (_root_.Set.image_mono subset_closure) hK.isClosed)
    exact (A.contMDiffOn_invFun.continuousOn.mono hsource).image_closure
  have hVs : closure V ⊆ A.source := by
    rw [hcl]
    rintro x ⟨y, hy, rfl⟩
    exact A.map_target (hsource hy)
  have hfrontV : frontier V = A.symm '' frontier C := by
    have hh :=
      (A.symm.toOpenPartialHomeomorph.isImage_image_of_subset_source hCsource).frontier.image_eq
    have h1 : frontier C ⊆ A.target := frontier_subset_closure.trans hsource
    have h2 : frontier V ⊆ A.source := frontier_subset_closure.trans hVs
    change A.symm '' (A.target ∩ frontier C) = A.source ∩ frontier V at hh
    rw [inter_eq_right.mpr h1, inter_eq_right.mpr h2] at hh
    exact hh.symm
  let f : S2 → E3 := A.symm ∘ e
  have hesource : _root_.Set.range e ⊆ A.target := hfront ▸ frontier_subset_closure.trans hsource
  have hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f :=
    DifferentialGeometry.Topology.isSmoothEmbedding_comp_partialDiffeomorph A.symm he hesource
  have hfrange : frontier V = _root_.Set.range f := by rw [hfrontV, hfront, ← _root_.Set.range_comp]
  let sides := SphereSeparation.jordanBrouwer_openThreeSpace f hf
    (Diffeomorph.refl (𝓡 3) E3 ∞)
  have hside : V = sides.compactSide :=
    sides.toSphereSides.eq_compactSide_of_frontier_subset hVopen hVne (hcl ▸ hK)
      (by
        rw [← hfrange]
        apply disjoint_left.mpr
        intro x hx hfrontier
        exact hfrontier.2 (hVopen.interior_eq.symm ▸ hx)) hfrange.subset
  have hSch : SphereSeparation.smoothSchoenfliesThree :=
    SphereSeparation.smoothSchoenfliesThree_iff_exists_ambient_diffeomorph.mpr
      smooth_schoenflies_three
  obtain ⟨F, hF⟩ :=
    SphereSeparation.smoothSchoenfliesThree_iff_smoothSchoenfliesBallFilling.mp hSch f hf
  have hFball : F '' _root_.Metric.ball (0 : E3) 1 = V := hF.trans hside.symm
  have hFclosed : F '' _root_.Metric.closedBall (0 : E3) 1 = closure V := by
    calc
      F '' _root_.Metric.closedBall (0 : E3) 1 = F '' closure (_root_.Metric.ball (0 : E3) 1) := by
        rw [closure_ball _ one_ne_zero]
      _ = closure (F '' _root_.Metric.ball (0 : E3) 1) := F.toHomeomorph.image_closure _
      _ = closure V := by rw [hFball]
  let G := F.toPartialDiffeomorph.trans A
  have hGs : _root_.Metric.closedBall (0 : E3) 1 ⊆ G.source := by
    intro x hx
    exact ⟨mem_univ _, hVs (hFclosed ▸ _root_.Set.mem_image_of_mem F hx)⟩
  have hCV : A '' V = C := by
    ext x
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      exact (A.right_inv (hCsource hz)).symm ▸ hz
    · intro hx
      exact ⟨A.symm x, _root_.Set.mem_image_of_mem _ hx, A.right_inv (hCsource hx)⟩
  have hGC : G '' _root_.Metric.ball (0 : E3) 1 = C := by
    change (A ∘ F) '' _root_.Metric.ball (0 : E3) 1 = C
    rw [_root_.Set.image_comp, hFball, hCV]
  have hGclosed : G '' _root_.Metric.closedBall (0 : E3) 1 = closure C := by
    change (A ∘ F) '' _root_.Metric.closedBall (0 : E3) 1 = closure C
    rw [_root_.Set.image_comp, hFclosed, hcl]
    ext x
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      exact (A.right_inv (hsource hz)).symm ▸ hz
    · intro hx
      exact ⟨A.symm x, _root_.Set.mem_image_of_mem _ hx, A.right_inv (hsource hx)⟩
  refine ⟨G, hGs, hGC, hGclosed, ?_⟩
  have hFsphere : F '' _root_.Metric.sphere (0 : E3) 1 = frontier V := by
    calc
      F '' _root_.Metric.sphere (0 : E3) 1 = F '' frontier (_root_.Metric.ball (0 : E3) 1) := by
        rw [frontier_ball _ one_ne_zero]
      _ = frontier (F '' _root_.Metric.ball (0 : E3) 1) := F.toHomeomorph.image_frontier _
      _ = frontier V := by rw [hFball]
  change (A ∘ F) '' _root_.Metric.sphere (0 : E3) 1 = _root_.Set.range e
  rw [_root_.Set.image_comp, hFsphere, hfrontV, hfront]
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact (A.right_inv (hesource hz)).symm ▸ hz
  · intro hx
    exact ⟨A.symm x, _root_.Set.mem_image_of_mem _ hx, A.right_inv (hesource hx)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.exists_ball_chart_of_compact_closure_sphere_frontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.exists_ball_chart_of_compact_closure_sphere_frontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.exists_ball_chart_of_compact_closure_sphere_frontier ``Submission.DifferentialGeometry.Topology.ThreeManifold.exists_ball_chart_of_compact_closure_sphere_frontier

end DifferentialGeometry.Topology.ThreeManifold
