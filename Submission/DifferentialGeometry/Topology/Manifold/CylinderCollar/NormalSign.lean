import Submission.DifferentialGeometry.Topology.Manifold.CylinderCollar.NormalCoorientation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

open _root_.Set _root_.Function _root_.Manifold _root_.Submission.Manifold _root_.Metric
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology.Manifold

private abbrev S2 := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.S2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.S2 target :: scope.openDecls } }

open private cylinderAxialDerivative_continuousOn from Submission.DifferentialGeometry.Topology.Manifold.CylinderCollar.NormalDerivative

theorem exists_constant_axial_sign
    (A : PartialDiffeomorph SphereCylinderModel SphereCylinderModel SphereCylinder SphereCylinder ∞)
    (hsource : ∀ p : S2, (p, 0) ∈ A.source)
    (hzero : ∀ p : S2, (A (p, 0)).2 = 0) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      ∀ p : S2, σ * deriv (fun t => (A (p, t)).2) 0 > 0 := by
  classical
  let : ConnectedSpace S2 := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num)
      (0 : EuclideanSpace ℝ (Fin 3)) (by norm_num : (0 : ℝ) ≤ 1))
  let d : S2 → ℝ := fun p => deriv (fun t => (A (p, t)).2) 0
  have hd : Continuous d := by
    let f : SphereCylinder → ℝ := fun q => deriv (fun t => (A (q.1, t)).2) q.2
    let j : S2 → SphereCylinder := fun p => (p, 0)
    have hj : Continuous j := continuous_id.prodMk continuous_const
    have hF : ContinuousOn f A.source := cylinderAxialDerivative_continuousOn A
    exact continuousOn_univ.mp (hF.comp hj.continuousOn (fun p _ => hsource p))
  have hne : ∀ p, d p ≠ 0 := fun p => axial_derivative_ne_zero_of_zero_section A hsource hzero p
  by_cases hp : ∀ p : S2, 0 < d p
  · exact ⟨1, Or.inl rfl, fun p => by simpa [d] using hp p⟩
  · push Not at hp
    obtain ⟨q, hq⟩ := hp
    have hqneg : d q < 0 := lt_of_le_of_ne hq (hne q)
    have hn : ∀ p : S2, d p < 0 := by
      intro p
      by_contra hp
      have hp0 : 0 ≤ d p := le_of_not_gt hp
      obtain ⟨z, hz⟩ := intermediate_value_univ q p hd ⟨hqneg.le, hp0⟩
      exact hne z hz
    exact ⟨-1, Or.inr rfl, fun p => by change 0 < -1 * d p; nlinarith [hn p]⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.exists_constant_axial_sign then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.exists_constant_axial_sign"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.exists_constant_axial_sign ``Submission.DifferentialGeometry.Topology.Manifold.exists_constant_axial_sign

end DifferentialGeometry.Topology.Manifold
