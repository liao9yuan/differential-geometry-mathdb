import Submission.DifferentialGeometry.Topology.Manifold.OpenSphereCylinder
import Submission.DifferentialGeometry.Topology.Manifold.OpenSubtypeDiffeomorph
import Submission.DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Composition

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

open _root_.Set _root_.Function _root_.Manifold _root_.Metric
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology.Manifold

abbrev SphereCylinder := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.SphereCylinder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.SphereCylinder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.SphereCylinder ``Submission.DifferentialGeometry.Topology.Manifold.SphereCylinder
abbrev SphereCylinderModel := (𝓡 2).prod 𝓘(ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.SphereCylinderModel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.SphereCylinderModel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.SphereCylinderModel ``Submission.DifferentialGeometry.Topology.Manifold.SphereCylinderModel

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.E3 target :: scope.openDecls } }
private abbrev S2 := Metric.sphere (0 : E3) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.S2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.S2 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Topology.Manifold.instFactEqNatFinrankRealE3HAddOfNat : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.instFactEqNatFinrankRealE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.instFactEqNatFinrankRealE3HAddOfNat target :: scope.openDecls } }

def cylinderExponentialChart (v : S2) : PartialDiffeomorph SphereCylinderModel (𝓡 3) SphereCylinder E3 ∞ :=
  (sphereProdRealDiffeomorphPunctured (n := 2) v).toPartialDiffeomorph.trans
    (DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph (𝓡 3) (puncturedSpace E3)
      ⟨⟨v.val, ne_zero_of_mem_unit_sphere v⟩⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.cylinderExponentialChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.cylinderExponentialChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.cylinderExponentialChart ``Submission.DifferentialGeometry.Topology.Manifold.cylinderExponentialChart

@[simp] theorem cylinderExponentialChart_apply (v : S2) (q : SphereCylinder) :
    cylinderExponentialChart v q = Real.exp q.2 • (q.1 : E3) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.cylinderExponentialChart_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.cylinderExponentialChart_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.cylinderExponentialChart_apply ``Submission.DifferentialGeometry.Topology.Manifold.cylinderExponentialChart_apply

@[simp] theorem cylinderExponentialChart_source (v : S2) :
    (cylinderExponentialChart v).source = univ := by
  ext q
  change (q ∈ _root_.Set.univ ∧ _ ∈ _root_.Set.univ) ↔ q ∈ _root_.Set.univ
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.cylinderExponentialChart_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.cylinderExponentialChart_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.cylinderExponentialChart_source ``Submission.DifferentialGeometry.Topology.Manifold.cylinderExponentialChart_source

@[simp] theorem cylinderExponentialChart_target (v : S2) :
    (cylinderExponentialChart v).target = {0}ᶜ := by
  ext x
  change (x ∈ (DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph (𝓡 3) (puncturedSpace E3)
      ⟨⟨v.val, ne_zero_of_mem_unit_sphere v⟩⟩).target ∧ _ ∈ _root_.Set.univ) ↔ x ∈ ({0}ᶜ : Set E3)
  rw [DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_target]
  simp [puncturedSpace]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.cylinderExponentialChart_target then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.cylinderExponentialChart_target"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.cylinderExponentialChart_target ``Submission.DifferentialGeometry.Topology.Manifold.cylinderExponentialChart_target

theorem cylinderExponentialChart_symm_apply (v : S2) (x : E3) (hx : x ≠ 0) :
    (cylinderExponentialChart v).symm x = (sphereDirection v x, Real.log ‖x‖) := by
  change (sphereProdRealDiffeomorphPunctured (n := 2) v).symm
    ((DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph (𝓡 3) (puncturedSpace E3)
      ⟨⟨v.val, ne_zero_of_mem_unit_sphere v⟩⟩).symm x) = _
  rw [DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_symm_apply _ _ _ hx]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.cylinderExponentialChart_symm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.cylinderExponentialChart_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.cylinderExponentialChart_symm_apply ``Submission.DifferentialGeometry.Topology.Manifold.cylinderExponentialChart_symm_apply

theorem norm_cylinderExponentialChart (v : S2) (q : SphereCylinder) :
    ‖cylinderExponentialChart v q‖ = Real.exp q.2 := by
  rw [cylinderExponentialChart_apply, norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), norm_eq_of_mem_sphere, mul_one]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.norm_cylinderExponentialChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.norm_cylinderExponentialChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.norm_cylinderExponentialChart ``Submission.DifferentialGeometry.Topology.Manifold.norm_cylinderExponentialChart

theorem cylinderExponentialChart_zero (v p : S2) :
    cylinderExponentialChart v (p, 0) = p.val := by
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.cylinderExponentialChart_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.cylinderExponentialChart_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.cylinderExponentialChart_zero ``Submission.DifferentialGeometry.Topology.Manifold.cylinderExponentialChart_zero

theorem cylinderExponentialChart_symm_sphere (v p : S2) :
    (cylinderExponentialChart v).symm p.val = (p, 0) := by
  rw [← cylinderExponentialChart_zero v p]
  exact (cylinderExponentialChart v).left_inv (by rw [cylinderExponentialChart_source]; trivial)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.cylinderExponentialChart_symm_sphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.cylinderExponentialChart_symm_sphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.cylinderExponentialChart_symm_sphere ``Submission.DifferentialGeometry.Topology.Manifold.cylinderExponentialChart_symm_sphere

end DifferentialGeometry.Topology.Manifold
