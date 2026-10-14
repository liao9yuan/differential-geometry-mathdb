import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.ConnectingCylinderRealization
import Submission.DifferentialGeometry.Topology.ThreeManifold.PoincareStandardSumClosure

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Function
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology.ConnectedSumQuotient

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ConnectedSumQuotient.E3 target :: scope.openDecls } }
private abbrev S2 := Metric.sphere (0 : E3) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.S2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ConnectedSumQuotient.S2 target :: scope.openDecls } }
private abbrev CI := (𝓡 2).prod 𝓘(ℝ, ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.CI
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ConnectedSumQuotient.CI target :: scope.openDecls } }

universe u
variable {M N : ConnectedClosedOrientedManifold.{u} 3}
  (c : OrientedBallChart M.toClosedOrientedManifold)
  (d : OrientedBallChart N.toClosedOrientedManifold)
  {P : Type u} [TopologicalSpace P] [ChartedSpace E3 P]

theorem isPoincareStandard_of_outer_caps_cylinder_cover
    [T2Space P]
    (F₀ : PartialDiffeomorph (𝓡 3) (𝓡 3) M.Carrier P ∞)
    (F₁ : PartialDiffeomorph (𝓡 3) (𝓡 3) N.Carrier P ∞)
    (T : PartialDiffeomorph CI (𝓡 3) (S2 × ℝ) P ∞)
    (hF₀ : ∀ x : outerPunctured c, x.val.val ∈ F₀.source)
    (hF₁ : ∀ x : outerPunctured d, x.val.val ∈ F₁.source)
    (hTs : _root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1 ⊆ T.source)
    (hdisj : Disjoint (_root_.Set.range (fun x : outerPunctured c => F₀ x.val.val))
      (_root_.Set.range (fun x : outerPunctured d => F₁ x.val.val)))
    (hcross₀ : ∀ (q : S2 × unitInterval) (x : outerPunctured c),
      T (q.1,q.2.val) = F₀ x.val.val → q.2 = 0 ∧ outerLeftBoundary c q.1 = x)
    (hcross₁ : ∀ (q : S2 × unitInterval) (x : outerPunctured d),
      T (q.1,q.2.val) = F₁ x.val.val → q.2 = 1 ∧ outerRightBoundary d boundaryAttachment q.1 = x)
    (hcover : _root_.Set.range (fun q : S2 × unitInterval => T (q.1,q.2.val)) ∪
      (_root_.Set.range (fun x : outerPunctured c => F₀ x.val.val) ∪
        _root_.Set.range (fun x : outerPunctured d => F₁ x.val.val)) = _root_.Set.univ)
    (hzero : ∀ z : S2, T (z,0) = F₀ (outerLeftBoundary c z).val.val)
    (hone : ∀ z : S2, T (z,1) = F₁ (outerRightBoundary d boundaryAttachment z).val.val)
    (hM : isPoincareStandard M.Carrier) (hN : isPoincareStandard N.Carrier) :
    isPoincareStandard P := by
  obtain ⟨_, _, _, _, D, _, _, _, _, _, _⟩ :=
    exists_diffeomorph_of_outer_caps_cylinder_cover c d boundaryAttachment F₀ F₁ T
      hF₀ hF₁ hTs hdisj hcross₀ hcross₁ hcover hzero hone
  exact isPoincareStandard_of_diffeomorph D.symm
    (isPoincareStandard_smoothConnectedSum M N c d hM hN)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.isPoincareStandard_of_outer_caps_cylinder_cover then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.isPoincareStandard_of_outer_caps_cylinder_cover"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.isPoincareStandard_of_outer_caps_cylinder_cover ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.isPoincareStandard_of_outer_caps_cylinder_cover

end DifferentialGeometry.Topology.ConnectedSumQuotient
