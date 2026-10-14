import Submission.DifferentialGeometry.Geometry.Boundary.ParametrizationInterior
import Submission.DifferentialGeometry.Geometry.Boundary.ProductHalfSpace
import Submission.DifferentialGeometry.Topology.Manifold.NestedBallShell

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Metric _root_.Topology _root_.Manifold
open scoped _root_.ContDiff

namespace DifferentialGeometry.Geometry.Boundary

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

private theorem positive_dimension (v : _root_.Metric.sphere (0 : E) 1) : 0 < Module.finrank ℝ E := by
  have hv : (v : E) ≠ 0 := by
    intro h
    have := v.property
    simp [h] at this
  have : Nontrivial E := ⟨⟨v, 0, hv⟩⟩
  exact Module.finrank_pos

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Boundary.positive_dimension
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Boundary.positive_dimension target :: scope.openDecls } }

theorem isPreconnected_interior_nestedBallShell [PreconnectedSpace (_root_.Metric.sphere (0 : E) 1)]
    (outer inner : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞)
    {r R : ℝ} (hr : 0 < r)
    (houter : _root_.Metric.closedBall (0 : E) R ⊆ outer.source)
    (hinner : _root_.Metric.closedBall (0 : E) r ⊆ inner.source)
    (hnested : inner '' _root_.Metric.closedBall 0 r ⊆ outer '' _root_.Metric.ball 0 R)
    (v : _root_.Metric.sphere (0 : E) 1) :
    IsPreconnected (interior (outer '' _root_.Metric.closedBall 0 R \ inner '' _root_.Metric.ball 0 r)) := by
  let n := Module.finrank ℝ E - 1
  have : Fact (Module.finrank ℝ E = n + 1) :=
    ⟨(Nat.sub_add_cancel (positive_dimension v)).symm⟩
  obtain ⟨e, hes, het, he, hei⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_smooth_nestedBallShell_parametrization (n := n)
      outer inner hr houter hinner hnested v
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 1)) =
      Module.finrank ℝ E := by
    simpa only [Module.finrank_prod, finrank_euclideanSpace_fin] using
      (Fact.out : Module.finrank ℝ E = n + 1).symm
  have h := isPreconnected_interior_target_of_smooth_parametrization e hes he hei hdim
  rwa [het] at h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Boundary.isPreconnected_interior_nestedBallShell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Boundary.isPreconnected_interior_nestedBallShell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Boundary.isPreconnected_interior_nestedBallShell ``Submission.DifferentialGeometry.Geometry.Boundary.isPreconnected_interior_nestedBallShell

theorem closure_interior_nestedBallShell
    (outer inner : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞)
    {r R : ℝ} (hr : 0 < r)
    (houter : _root_.Metric.closedBall (0 : E) R ⊆ outer.source)
    (hinner : _root_.Metric.closedBall (0 : E) r ⊆ inner.source)
    (hnested : inner '' _root_.Metric.closedBall 0 r ⊆ outer '' _root_.Metric.ball 0 R)
    (v : _root_.Metric.sphere (0 : E) 1) :
    closure (interior (outer '' _root_.Metric.closedBall 0 R \ inner '' _root_.Metric.ball 0 r)) =
      outer '' _root_.Metric.closedBall 0 R \ inner '' _root_.Metric.ball 0 r := by
  let n := Module.finrank ℝ E - 1
  have : Fact (Module.finrank ℝ E = n + 1) :=
    ⟨(Nat.sub_add_cancel (positive_dimension v)).symm⟩
  obtain ⟨e, hes, het, he, hei⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_smooth_nestedBallShell_parametrization (n := n)
      outer inner hr houter hinner hnested v
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 1)) =
      Module.finrank ℝ E := by
    simpa only [Module.finrank_prod, finrank_euclideanSpace_fin] using
      (Fact.out : Module.finrank ℝ E = n + 1).symm
  have h := closure_interior_target_of_smooth_parametrization e hes he hei hdim
  rwa [het] at h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Boundary.closure_interior_nestedBallShell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Boundary.closure_interior_nestedBallShell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Boundary.closure_interior_nestedBallShell ``Submission.DifferentialGeometry.Geometry.Boundary.closure_interior_nestedBallShell

end DifferentialGeometry.Geometry.Boundary
