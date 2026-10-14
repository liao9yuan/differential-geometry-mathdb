import Submission.DifferentialGeometry.Topology.ThreeManifold.AntipodalSphereBall
import Submission.DifferentialGeometry.Topology.Covering.AntipodalSphereLift
import Submission.DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.PartialDiffeomorph

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

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [T2Space M]

theorem exists_ball_chart_of_antipodal_quotient_sphere_embedding
    (p : S3 → M) (hp : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ p)
    (honto : Function.Surjective p)
    (hfib : ∀ x y : S3, p x = p y ↔ x = y ∨ (x : E4) = -(y : E4))
    (e : S2 → M) (he : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e) :
    ∃ G : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 M ∞,
      closedBall (0 : E3) 1 ⊆ G.source ∧ G '' _root_.Metric.sphere (0 : E3) 1 = _root_.Set.range e := by
  obtain ⟨f, hf, hpf, _, hdisj, _⟩ :=
    DifferentialGeometry.Topology.exists_smooth_sphere_lift_disjoint_antipodal
      p hp honto hfib e he
  obtain ⟨B, hB, hBs, hBB⟩ := exists_ball_chart_disjoint_antipodal_of_sphere_embedding f hf hdisj
  let K := B '' _root_.Metric.closedBall (0 : E3) 1
  have hK : IsCompact K := (_root_.ProperSpace.isCompact_closedBall _ _).image_of_continuousOn
    (B.contMDiffOn_toFun.continuousOn.mono hB)
  have hne : K.Nonempty := (nonempty_closedBall.mpr zero_le_one).image B
  have hinj : _root_.Set.InjOn p K := by
    intro x hx y hy hxy
    rcases (hfib x y).mp hxy with h | h
    · exact h
    · have heq : x = -y := Subtype.ext h
      exact False.elim (hBB.le_bot ⟨hx, y, hy, heq.symm⟩)
  obtain ⟨P, hP, hPeq⟩ :=
    DifferentialGeometry.IsLocalDiffeomorphOn.exists_partialDiffeomorph_of_isCompact
      (show IsLocalDiffeomorphOn (𝓡 3) (𝓡 3) ∞ p K from fun x => hp x.val)
      hK hne hinj
  let G := B.trans P
  have hGs : _root_.Metric.closedBall (0 : E3) 1 ⊆ G.source := by
    intro x hx
    exact ⟨hB hx, hP (_root_.Set.mem_image_of_mem B hx)⟩
  refine ⟨G, hGs, ?_⟩
  change (P ∘ B) '' _root_.Metric.sphere (0 : E3) 1 = _root_.Set.range e
  rw [_root_.Set.image_comp, hBs]
  change P.toFun '' _root_.Set.range f = _root_.Set.range e
  rw [hPeq, ← _root_.Set.range_comp]
  exact congrArg _root_.Set.range (funext hpf)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.exists_ball_chart_of_antipodal_quotient_sphere_embedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.exists_ball_chart_of_antipodal_quotient_sphere_embedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.exists_ball_chart_of_antipodal_quotient_sphere_embedding ``Submission.DifferentialGeometry.Topology.ThreeManifold.exists_ball_chart_of_antipodal_quotient_sphere_embedding

end DifferentialGeometry.Topology.ThreeManifold
