import Submission.DifferentialGeometry.Topology.ThreeManifold.ChartSphereBall
import Submission.DifferentialGeometry.Topology.Manifold.StereographicChart

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Submission.Set _root_.Metric _root_.Submission.Metric _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff

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

theorem exists_ball_chart_of_sphere_embedding_avoiding_point
    (e : S2 → S3) (he : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    (p : S3) (hp : p ∉ _root_.Set.range e) :
    ∃ B : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 S3 ∞,
      _root_.Metric.closedBall (0 : E3) 1 ⊆ B.source ∧
      B '' _root_.Metric.sphere (0 : E3) 1 = _root_.Set.range e ∧ p ∉ B '' _root_.Metric.closedBall (0 : E3) 1 := by
  let A : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 S3 ∞ :=
    { toPartialEquiv := (stereographic' 3 p).symm.toPartialEquiv
      open_source := (stereographic' 3 p).symm.open_source
      open_target := (stereographic' 3 p).symm.open_target
      contMDiffOn_toFun :=
        (DifferentialGeometry.Topology.Manifold.stereographicInverse_isLocalDiffeomorph p)
          |>.contMDiff.contMDiffOn
      contMDiffOn_invFun :=
        (DifferentialGeometry.Topology.Manifold.stereographic_isLocalDiffeomorphOn p).contMDiffOn }
  have hAs : A.source = univ := by change (stereographic' 3 p).target = _root_.Set.univ; simp
  have hAt : A.target = {p}ᶜ := by change (stereographic' 3 p).source = {p}ᶜ; simp
  have hes : _root_.Set.range e ⊆ A.target := by
    rw [hAt]
    intro x hx hxp
    exact hp (mem_singleton_iff.mp hxp ▸ hx)
  let f : S2 → E3 := A.symm ∘ e
  have hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f :=
    DifferentialGeometry.Topology.isSmoothEmbedding_comp_partialDiffeomorph A.symm he hes
  obtain ⟨F, hF⟩ := smooth_schoenflies_three f hf
  let B := F.toPartialDiffeomorph.trans A
  have hB : _root_.Metric.closedBall (0 : E3) 1 ⊆ B.source := by
    intro x _
    exact ⟨mem_univ _, hAs ▸ _root_.Set.mem_univ _⟩
  have hBsphere : B '' _root_.Metric.sphere (0 : E3) 1 = _root_.Set.range e := by
    change (A ∘ F) '' _root_.Metric.sphere (0 : E3) 1 = _root_.Set.range e
    rw [_root_.Set.image_comp, hF, _root_.Set.range_comp]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨z, hz, hzy⟩ := hy
      rw [← hzy]
      exact (A.right_inv (hes hz)).symm ▸ hz
    · rintro ⟨z, rfl⟩
      refine ⟨A.symm (e z), _root_.Set.mem_image_of_mem _ (_root_.Set.mem_range_self z), ?_⟩
      exact A.right_inv (hes (_root_.Set.mem_range_self z))
  refine ⟨B, hB, hBsphere, ?_⟩
  rintro ⟨x, hx, hxp⟩
  have hmem := A.map_source (hAs ▸ _root_.Set.mem_univ (F x))
  change B x ∈ A.target at hmem
  rw [hxp, hAt] at hmem
  exact hmem (_root_.Set.mem_singleton p)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.exists_ball_chart_of_sphere_embedding_avoiding_point then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.exists_ball_chart_of_sphere_embedding_avoiding_point"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.exists_ball_chart_of_sphere_embedding_avoiding_point ``Submission.DifferentialGeometry.Topology.ThreeManifold.exists_ball_chart_of_sphere_embedding_avoiding_point

end DifferentialGeometry.Topology.ThreeManifold
