import Submission.DifferentialGeometry.Topology.ThreeManifold.ProjectiveCapTrim
import Submission.DifferentialGeometry.Topology.ThreeManifold.TwoBallCharts

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
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
private abbrev S3 := _root_.Metric.sphere (0 : E4) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.S3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.S3 target :: scope.openDecls } }

variable {M Z : Type*} [TopologicalSpace M] [ChartedSpace E3 M]
  [IsManifold (𝓡 3) ∞ M] [T2Space M] [PreconnectedSpace M]
  [TopologicalSpace Z] [ChartedSpace E3 Z] [IsManifold (𝓡 3) ∞ Z] [T2Space Z] [CompactSpace Z]

theorem exists_sphere_or_projective_diffeomorph_of_cap_cover
    (p : S3 → Z) (hp : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ p)
    (honto : Function.Surjective p)
    (hfib : ∀ x y : S3, p x = p y ↔ x = y ∨ (x : E4) = -(y : E4))
    (b : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 Z ∞)
    (F : PartialDiffeomorph (𝓡 3) (𝓡 3) Z M ∞)
    (B : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 M ∞)
    (hb : _root_.Metric.closedBall (0 : E3) 1 ⊆ b.source)
    (hF : (b '' _root_.Metric.ball (0 : E3) 1)ᶜ ⊆ F.source)
    (hB : _root_.Metric.closedBall (0 : E3) 1 ⊆ B.source)
    (hcover : B '' _root_.Metric.closedBall (0 : E3) 1 ∪ F '' (b '' _root_.Metric.ball (0 : E3) 1)ᶜ = _root_.Set.univ) :
    (∃ (e : M ≃ₘ⟮𝓡 3,𝓡 3⟯ S3)
      (a : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 S3 ∞),
      a.source = _root_.Set.univ ∧
      (∀ z ∈ _root_.Metric.closedBall (0 : E3) 1, e (B z) = a z) ∧
      ∃ U : Set M, IsOpen U ∧ B '' _root_.Metric.closedBall (0 : E3) 1 ⊆ U ∧
        U ⊆ (B.symm.trans a).source ∧ _root_.Set.EqOn e (B.symm.trans a) U) ∨
    ∃ (e : M ≃ₘ⟮𝓡 3,𝓡 3⟯ Z)
      (G : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 Z ∞)
      (D : E3 ≃ₘ[ℝ] E3),
      _root_.Metric.closedBall (0 : E3) 1 ⊆ G.source ∧
      (G '' _root_.Metric.ball (0 : E3) 1)ᶜ ⊆ F.source ∧
      D '' _root_.Metric.closedBall (0 : E3) 1 = _root_.Metric.closedBall (0 : E3) 1 ∧
      (∀ z ∈ _root_.Metric.closedBall (0 : E3) 1, e (B (D z)) = G z) ∧
      _root_.Set.EqOn e.symm F (G '' _root_.Metric.ball (0 : E3) 1)ᶜ ∧
      e '' (B '' _root_.Metric.ball (0 : E3) 1) = G '' _root_.Metric.ball (0 : E3) 1 ∧
      F '' (G '' _root_.Metric.ball (0 : E3) 1)ᶜ = (B '' _root_.Metric.ball (0 : E3) 1)ᶜ ∧
      F '' (G '' _root_.Metric.sphere (0 : E3) 1) = B '' _root_.Metric.sphere (0 : E3) 1 ∧
      ∃ U : Set Z, IsOpen U ∧ (G '' _root_.Metric.ball (0 : E3) 1)ᶜ ⊆ U ∧
        U ⊆ F.source ∧ _root_.Set.EqOn e.symm F U := by
  obtain h | h := exists_ball_or_projective_complement_of_cap_cover p hp honto hfib b F B hb hF hB hcover
  · obtain ⟨G,hG,hGo,_,_⟩ := h
    obtain ⟨e,a,c,ha,_,_,heB,D,hD,heG,U,hU,hBU,hUs,hEq⟩ :=
      DifferentialGeometry.Topology.Manifold.exists_sphere_diffeomorph_of_complementary_ball_charts_eqOn_neighborhood
        B G hB hG hGo
    refine Or.inl ⟨e.symm,a,ha,?_,U,hU,hBU,hUs,hEq⟩
    intro z hz
    exact (congrArg e.symm (heB z hz)).symm.trans (e.symm_apply_apply _)
  · obtain ⟨G,hG,hGF,hFo,hFc,hFs⟩ := h
    have hBo : B '' _root_.Metric.ball (0 : E3) 1 = ((B '' _root_.Metric.ball (0 : E3) 1)ᶜ)ᶜ := (compl_compl _).symm
    obtain ⟨e,heF,heBall,D,hD,heB,U,hU,hGU,hUF,hEq⟩ :=
      DifferentialGeometry.Topology.Manifold.exists_diffeomorph_of_ball_complement_and_ball G F B
        hG hGF hB hFc hBo
    refine Or.inr ⟨e.symm,G,D,hG,hGF,hD,?_,heF,?_,hFc,hFs,U,hU,hGU,hUF,hEq⟩
    · intro z hz
      exact (congrArg e.symm (heB z hz)).symm.trans (e.symm_apply_apply _)
    · rw [← compl_compl (B '' _root_.Metric.ball (0 : E3) 1),← heBall,_root_.Set.image_image]
      simp only [e.symm_apply_apply,_root_.Set.image_id']

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.exists_sphere_or_projective_diffeomorph_of_cap_cover then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.exists_sphere_or_projective_diffeomorph_of_cap_cover"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.exists_sphere_or_projective_diffeomorph_of_cap_cover ``Submission.DifferentialGeometry.Topology.ThreeManifold.exists_sphere_or_projective_diffeomorph_of_cap_cover

end DifferentialGeometry.Topology.ThreeManifold
