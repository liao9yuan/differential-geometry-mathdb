import Submission.DifferentialGeometry.Topology.ThreeManifold.SphereInsideProjectiveCap
import Submission.DifferentialGeometry.Topology.ThreeManifold.BallSphereSides
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
private abbrev E4 := EuclideanSpace ℝ (Fin 4)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.E4
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.E4 target :: scope.openDecls } }
private abbrev S2 := Metric.sphere (0 : E3) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.S2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.S2 target :: scope.openDecls } }
private abbrev S3 := Metric.sphere (0 : E4) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.S3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.S3 target :: scope.openDecls } }

variable {M Z : Type*} [TopologicalSpace M] [ChartedSpace E3 M]
  [T2Space M]
  [TopologicalSpace Z] [ChartedSpace E3 Z] [IsManifold (𝓡 3) ∞ Z] [T2Space Z] [CompactSpace Z]

theorem exists_compact_side_inside_projective_cap_of_sphere_embedding
    (p : S3 → Z) (hp : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ p)
    (honto : Function.Surjective p)
    (hfib : ∀ x y : S3, p x = p y ↔ x = y ∨ (x : E4) = -(y : E4))
    (C : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 Z ∞)
    (F : PartialDiffeomorph (𝓡 3) (𝓡 3) Z M ∞)
    (hC : _root_.Metric.closedBall (0 : E3) 1 ⊆ C.source)
    (hF : (C '' _root_.Metric.ball (0 : E3) 1)ᶜ ⊆ F.source)
    (e : S2 → M) (he : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    (hinside : _root_.Set.range e ⊆ interior (F '' (C '' _root_.Metric.ball (0 : E3) 1)ᶜ)) :
    ∃ (K : Set M) (B : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 Z ∞),
      _root_.Metric.closedBall (0 : E3) 1 ⊆ B.source ∧
      F '' (B '' _root_.Metric.sphere (0 : E3) 1) = _root_.Set.range e ∧
      ((K = F '' (B '' _root_.Metric.closedBall (0 : E3) 1) ∧
        B '' _root_.Metric.closedBall (0 : E3) 1 ⊆ (C '' _root_.Metric.closedBall (0 : E3) 1)ᶜ) ∨
       (K = F '' (B '' _root_.Metric.ball (0 : E3) 1)ᶜ ∧
        (B '' _root_.Metric.ball (0 : E3) 1)ᶜ ⊆ (C '' _root_.Metric.closedBall (0 : E3) 1)ᶜ)) ∧
      IsCompact K ∧ closure (interior K) = K ∧ frontier K = _root_.Set.range e ∧
      K ⊆ interior (F '' (C '' _root_.Metric.ball (0 : E3) 1)ᶜ) := by
  let K0 := (C '' _root_.Metric.ball (0 : E3) 1)ᶜ
  have hK0int : interior K0 = (C '' _root_.Metric.closedBall (0 : E3) 1)ᶜ := by
    rw [interior_compl, DifferentialGeometry.Topology.Manifold.closure_image_ball_of_partialDiffeomorph C hC]
  have hFint : F '' (C '' _root_.Metric.closedBall (0 : E3) 1)ᶜ = interior (F '' K0) := by
    have h := F.toOpenPartialHomeomorph.image_interior_of_subset_source hF
    change F '' interior K0 = interior (F '' K0) at h
    rwa [hK0int] at h
  have hes : _root_.Set.range e ⊆ F.target := by
    rintro x hx
    obtain ⟨z, hz, rfl⟩ := interior_subset (hinside hx)
    exact F.map_source (hF hz)
  let eZ : S2 → Z := F.symm ∘ e
  have heZ : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ eZ :=
    DifferentialGeometry.Topology.isSmoothEmbedding_comp_partialDiffeomorph F.symm he hes
  have heZsub : _root_.Set.range eZ ⊆ (C '' _root_.Metric.closedBall (0 : E3) 1)ᶜ := by
    rintro x ⟨q, rfl⟩
    obtain ⟨z, hz, heq⟩ := hFint.symm ▸ hinside (_root_.Set.mem_range_self q)
    have hz0 : z ∈ K0 := fun hzball => hz (_root_.Set.image_mono _root_.Metric.ball_subset_closedBall hzball)
    change F.toPartialEquiv.symm (e q) ∈ _
    rw [← heq, F.toPartialEquiv.left_inv (hF hz0)]
    exact hz
  obtain ⟨B, hB, hBs, havoid⟩ :=
    exists_ball_or_complement_avoiding_closed_ball_of_projective_sphere_embedding
      p hp honto hfib C hC eZ heZ
      (disjoint_left.mpr (fun x hx he => heZsub he hx))
  have hFsphere : F '' (B '' _root_.Metric.sphere (0 : E3) 1) = _root_.Set.range e := by
    rw [hBs, ← _root_.Set.range_comp]
    apply congrArg _root_.Set.range
    funext q
    exact F.right_inv (hes (_root_.Set.mem_range_self q))
  have hBcompact : IsCompact (B '' _root_.Metric.closedBall (0 : E3) 1) :=
    (_root_.ProperSpace.isCompact_closedBall _ _).image_of_continuousOn (B.contMDiffOn_toFun.continuousOn.mono hB)
  have hBint : interior (B '' _root_.Metric.closedBall (0 : E3) 1) = B '' _root_.Metric.ball (0 : E3) 1 := by
    have h := B.toOpenPartialHomeomorph.image_interior_of_subset_source hB
    change B '' interior (_root_.Metric.closedBall (0 : E3) 1) = interior (B '' _root_.Metric.closedBall (0 : E3) 1) at h
    rw [interior_closedBall _ one_ne_zero] at h
    exact h.symm
  have hBfront : frontier (B '' _root_.Metric.closedBall (0 : E3) 1) = B '' _root_.Metric.sphere (0 : E3) 1 := by
    rw [← B.image_frontier_of_isCompact (_root_.ProperSpace.isCompact_closedBall _ _) hB,
      frontier_closedBall _ one_ne_zero]
  have hBreg : closure (interior (B '' _root_.Metric.closedBall (0 : E3) 1)) =
      B '' _root_.Metric.closedBall (0 : E3) 1 := by
    rw [hBint, DifferentialGeometry.Topology.Manifold.closure_image_ball_of_partialDiffeomorph B hB]
  have hBoreg : closure (interior (B '' _root_.Metric.ball (0 : E3) 1)ᶜ) =
      (B '' _root_.Metric.ball (0 : E3) 1)ᶜ := by
    rw [interior_compl, DifferentialGeometry.Topology.Manifold.closure_image_ball_of_partialDiffeomorph B hB,
      closure_compl, hBint]
  have hBofront : frontier (B '' _root_.Metric.ball (0 : E3) 1)ᶜ = B '' _root_.Metric.sphere (0 : E3) 1 := by
    rw [frontier_compl, DifferentialGeometry.Topology.Manifold.frontier_image_ball_of_partialDiffeomorph B hB]
  have finish (A : Set Z) (hA : IsCompact A) (hAr : closure (interior A) = A)
      (hAf : frontier A = B '' _root_.Metric.sphere (0 : E3) 1)
      (hAin : A ⊆ (C '' _root_.Metric.closedBall (0 : E3) 1)ᶜ) :
      IsCompact (F '' A) ∧ closure (interior (F '' A)) = F '' A ∧
        frontier (F '' A) = _root_.Set.range e ∧ F '' A ⊆ interior (F '' K0) := by
    have hAs : A ⊆ F.source := fun x hx => hF (fun h => hAin hx (_root_.Set.image_mono _root_.Metric.ball_subset_closedBall h))
    have hK : IsCompact (F '' A) := hA.image_of_continuousOn (F.contMDiffOn_toFun.continuousOn.mono hAs)
    refine ⟨hK, ?_, ?_, ?_⟩
    · exact F.toOpenPartialHomeomorph.closure_interior_image_of_subset_source hAs hAr hK.isClosed
    · rw [← F.image_frontier_of_isCompact hA hAs, hAf, hFsphere]
    · rw [← hFint]
      exact _root_.Set.image_mono hAin
  rcases havoid with havoid | havoid
  · exact ⟨F '' (B '' _root_.Metric.closedBall (0 : E3) 1), B, hB, hFsphere, Or.inl ⟨rfl, havoid⟩,
      finish _ hBcompact hBreg hBfront havoid⟩
  · have hcompact : IsCompact (B '' _root_.Metric.ball (0 : E3) 1)ᶜ :=
      (B.toOpenPartialHomeomorph.isOpen_image_of_subset_source _root_.Metric.isOpen_ball
        (ball_subset_closedBall.trans hB)).isClosed_compl.isCompact
    exact ⟨F '' (B '' _root_.Metric.ball (0 : E3) 1)ᶜ, B, hB, hFsphere, Or.inr ⟨rfl, havoid⟩,
      finish _ hcompact hBoreg hBofront havoid⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.exists_compact_side_inside_projective_cap_of_sphere_embedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.exists_compact_side_inside_projective_cap_of_sphere_embedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.exists_compact_side_inside_projective_cap_of_sphere_embedding ``Submission.DifferentialGeometry.Topology.ThreeManifold.exists_compact_side_inside_projective_cap_of_sphere_embedding

omit [CompactSpace Z] in
theorem exists_ball_or_complement_of_projective_sphere_frontier
    (p : S3 → Z) (hp : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ p)
    (honto : Function.Surjective p)
    (hfib : ∀ x y : S3, p x = p y ↔ x = y ∨ (x : E4) = -(y : E4))
    (F : PartialDiffeomorph (𝓡 3) (𝓡 3) Z M ∞)
    {K : Set M} (hK : IsCompact K) (hregular : closure (interior K) = K)
    (hconnected : IsConnected (interior K)) (hsource : K ⊆ F.target)
    (e : S2 → M) (he : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    (hfront : frontier K = _root_.Set.range e) :
    ∃ B : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 Z ∞,
      _root_.Metric.closedBall (0 : E3) 1 ⊆ B.source ∧ F '' (B '' _root_.Metric.sphere (0 : E3) 1) = _root_.Set.range e ∧
      ((B '' _root_.Metric.closedBall (0 : E3) 1 ⊆ F.source ∧
        F '' (B '' _root_.Metric.closedBall (0 : E3) 1) = K ∧ F '' (B '' _root_.Metric.ball (0 : E3) 1) = interior K) ∨
       ((B '' _root_.Metric.ball (0 : E3) 1)ᶜ ⊆ F.source ∧
        F '' (B '' _root_.Metric.ball (0 : E3) 1)ᶜ = K ∧
          F '' (B '' _root_.Metric.closedBall (0 : E3) 1)ᶜ = interior K)) := by
  let _ : ConnectedSpace S3 := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp [E4])) 0 zero_le_one)
  let _ : ConnectedSpace Z := honto.connectedSpace hp.contMDiff.continuous
  let V := F.symm '' interior K
  have hKs : interior K ⊆ F.target := interior_subset.trans hsource
  have hVopen : IsOpen V :=
    F.symm.toOpenPartialHomeomorph.isOpen_image_of_subset_source isOpen_interior hKs
  have hVconnected : IsConnected V := hconnected.image F.symm
    (F.contMDiffOn_invFun.continuousOn.mono hKs)
  have hVcompact : IsCompact (F.symm '' K) := hK.image_of_continuousOn
    (F.contMDiffOn_invFun.continuousOn.mono hsource)
  have hclosure : closure V = F.symm '' K := by
    apply Subset.antisymm (closure_minimal (_root_.Set.image_mono interior_subset) hVcompact.isClosed)
    have hcont : ContinuousOn F.symm (closure (interior K)) := by
      rw [hregular]
      exact F.contMDiffOn_invFun.continuousOn.mono hsource
    simpa only [hregular] using hcont.image_closure
  have hVs : closure V ⊆ F.source := by
    rw [hclosure]
    rintro z ⟨x,hx,rfl⟩
    exact F.map_target (hsource hx)
  have hfrontint : frontier (interior K) = frontier K := by
    rw [frontier, hregular, interior_interior, hK.isClosed.frontier_eq]
  have hVfront : frontier V = F.symm '' _root_.Set.range e := by
    have hh := (F.symm.toOpenPartialHomeomorph.isImage_image_of_subset_source hKs).frontier.image_eq
    change F.symm '' (F.target ∩ frontier (interior K)) = F.source ∩ frontier V at hh
    have hfrontsource : frontier (interior K) ⊆ F.target := by
      rw [hfrontint]
      exact hK.isClosed.frontier_subset.trans hsource
    rw [inter_eq_right.mpr hfrontsource,
      inter_eq_right.mpr (frontier_subset_closure.trans hVs)] at hh
    rw [← hh, hfrontint, hfront]
  have hes : _root_.Set.range e ⊆ F.target := hfront ▸ hK.isClosed.frontier_subset.trans hsource
  let eZ := F.symm ∘ e
  have heZ : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ eZ :=
    DifferentialGeometry.Topology.isSmoothEmbedding_comp_partialDiffeomorph F.symm he hes
  obtain ⟨B,hB,hBs⟩ := exists_ball_chart_of_antipodal_quotient_sphere_embedding
    p hp honto hfib eZ heZ
  have hBfront : frontier V = B '' _root_.Metric.sphere (0 : E3) 1 := by
    rw [hVfront, ← _root_.Set.range_comp]
    exact hBs.symm
  have hFi : F '' V = interior K := F.toPartialEquiv.image_symm_image_of_subset_target hKs
  have hFc : F '' closure V = K := by
    rw [hclosure]
    exact F.toPartialEquiv.image_symm_image_of_subset_target hsource
  have hFsphere : F '' (B '' _root_.Metric.sphere (0 : E3) 1) = _root_.Set.range e := by
    rw [hBs, _root_.Set.range_comp]
    exact F.toPartialEquiv.image_symm_image_of_subset_target hes
  refine ⟨B,hB,hFsphere,?_⟩
  rcases eq_ball_or_complement_of_connected_sphere_frontier B hB hVopen hVconnected hBfront with hb | hc
  · left
    have hcl : B '' _root_.Metric.closedBall (0 : E3) 1 = closure V := by
      rw [← DifferentialGeometry.Topology.Manifold.closure_image_ball_of_partialDiffeomorph B hB, ← hb]
    exact ⟨hcl ▸ hVs, hcl ▸ hFc, hb ▸ hFi⟩
  · right
    have hcl : (B '' _root_.Metric.ball (0 : E3) 1)ᶜ = closure V := by
      rw [hc, closure_compl]
      have hh := B.toOpenPartialHomeomorph.image_interior_of_subset_source hB
      rw [interior_closedBall _ one_ne_zero] at hh
      exact congrArg (fun A : Set Z => Aᶜ) hh
    exact ⟨hcl ▸ hVs, hcl ▸ hFc, hc ▸ hFi⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.exists_ball_or_complement_of_projective_sphere_frontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.exists_ball_or_complement_of_projective_sphere_frontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.exists_ball_or_complement_of_projective_sphere_frontier ``Submission.DifferentialGeometry.Topology.ThreeManifold.exists_ball_or_complement_of_projective_sphere_frontier


omit [CompactSpace Z] in
theorem exists_ball_or_complement_of_projective_cap_sphere_frontier
    (p : S3 → Z) (hp : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ p)
    (honto : Function.Surjective p)
    (hfib : ∀ x y : S3, p x = p y ↔ x = y ∨ (x : E4) = -(y : E4))
    (C : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 Z ∞)
    (F : PartialDiffeomorph (𝓡 3) (𝓡 3) Z M ∞)
    (hC : _root_.Metric.closedBall (0 : E3) 1 ⊆ C.source)
    (hF : (C '' _root_.Metric.ball (0 : E3) 1)ᶜ ⊆ F.source)
    {K : Set M} (hK : IsCompact K) (hregular : closure (interior K) = K)
    (hconnected : IsConnected (interior K))
    (hinside : K ⊆ interior (F '' (C '' _root_.Metric.ball (0 : E3) 1)ᶜ))
    (e : S2 → M) (he : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    (hfront : frontier K = _root_.Set.range e) :
    ∃ B : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 Z ∞,
      _root_.Metric.closedBall (0 : E3) 1 ⊆ B.source ∧ F '' (B '' _root_.Metric.sphere (0 : E3) 1) = _root_.Set.range e ∧
      ((B '' _root_.Metric.closedBall (0 : E3) 1 ⊆ (C '' _root_.Metric.closedBall (0 : E3) 1)ᶜ ∧
        F '' (B '' _root_.Metric.closedBall (0 : E3) 1) = K ∧ F '' (B '' _root_.Metric.ball (0 : E3) 1) = interior K) ∨
       ((B '' _root_.Metric.ball (0 : E3) 1)ᶜ ⊆ (C '' _root_.Metric.closedBall (0 : E3) 1)ᶜ ∧
        F '' (B '' _root_.Metric.ball (0 : E3) 1)ᶜ = K ∧
          F '' (B '' _root_.Metric.closedBall (0 : E3) 1)ᶜ = interior K)) := by
  have hinterior : interior (F '' (C '' _root_.Metric.ball (0 : E3) 1)ᶜ) =
      F '' (C '' _root_.Metric.closedBall (0 : E3) 1)ᶜ := by
    have h := F.toOpenPartialHomeomorph.image_interior_of_subset_source hF
    rw [interior_compl,
      DifferentialGeometry.Topology.Manifold.closure_image_ball_of_partialDiffeomorph C hC] at h
    exact h.symm
  have hsource : K ⊆ F.target := by
    intro x hx
    obtain ⟨z,hz,rfl⟩ := interior_subset (hinside hx)
    exact F.map_source (hF hz)
  have hside (S : Set Z) (hS : S ⊆ F.source) (himage : F '' S = K) :
      S ⊆ (C '' _root_.Metric.closedBall (0 : E3) 1)ᶜ := by
    intro x hx
    have hFx : F x ∈ interior (F '' (C '' _root_.Metric.ball (0 : E3) 1)ᶜ) :=
      hinside (himage ▸ _root_.Set.mem_image_of_mem F hx)
    obtain ⟨z,hz,hzx⟩ := hinterior ▸ hFx
    have hzsource : z ∈ F.source := hF (fun h => hz (_root_.Set.image_mono _root_.Metric.ball_subset_closedBall h))
    exact F.injOn hzsource (hS hx) hzx ▸ hz
  obtain ⟨B,hB,hBs,hball | hcompl⟩ :=
    exists_ball_or_complement_of_projective_sphere_frontier p hp honto hfib F
      hK hregular hconnected hsource e he hfront
  · exact ⟨B,hB,hBs,Or.inl ⟨hside _ hball.1 hball.2.1,hball.2⟩⟩
  · exact ⟨B,hB,hBs,Or.inr ⟨hside _ hcompl.1 hcompl.2.1,hcompl.2⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.exists_ball_or_complement_of_projective_cap_sphere_frontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.exists_ball_or_complement_of_projective_cap_sphere_frontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.exists_ball_or_complement_of_projective_cap_sphere_frontier ``Submission.DifferentialGeometry.Topology.ThreeManifold.exists_ball_or_complement_of_projective_cap_sphere_frontier

end DifferentialGeometry.Topology.ThreeManifold
