import Submission.DifferentialGeometry.Geometry.Metric.PolarCoordinates

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Function _root_.TopologicalSpace _root_.Manifold
open scoped _root_.Manifold _root_.ContDiff _root_.Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev PositiveE3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.PositiveE3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.PositiveE3 target :: scope.openDecls } }
private abbrev PositiveS2 := Metric.sphere (0 : PositiveE3) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.PositiveS2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.PositiveS2 target :: scope.openDecls } }
private abbrev PositiveIC := (𝓡 2).prod 𝓘(ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.PositiveIC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.PositiveIC target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.instFactEqNatFinrankRealPositiveE3HAddOfNat : Fact (Module.finrank ℝ PositiveE3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.instFactEqNatFinrankRealPositiveE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.instFactEqNatFinrankRealPositiveE3HAddOfNat target :: scope.openDecls } }

def positiveCuttingCylinder (r : ℝ) : _root_.TopologicalSpace.Opens (PositiveS2 × ℝ) :=
  ⟨{q | 0 < q.2 ∧ q.2 < r}, isOpen_Ioo.preimage continuous_snd⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.positiveCuttingCylinder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.positiveCuttingCylinder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.positiveCuttingCylinder ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.positiveCuttingCylinder

def positiveCuttingAnnulus (L r : ℝ) : _root_.TopologicalSpace.Opens PositiveE3 :=
  ⟨{x | L < ‖x‖ ∧ ‖x‖ < L + r},
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.positiveCuttingAnnulus then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.positiveCuttingAnnulus"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.positiveCuttingAnnulus ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.positiveCuttingAnnulus

private theorem radial_norm {L r : ℝ} (hL : 0 < L) (q : positiveCuttingCylinder r) :
    ‖(L + q.val.2) • q.val.1.val‖ = L + q.val.2 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (add_pos hL q.property.1),
    mem_sphere_zero_iff_norm.mp q.val.1.property, mul_one]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.radial_norm
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.radial_norm target :: scope.openDecls } }
private def positiveRadial {L : ℝ} (hL : 0 < L) (r : ℝ) :
    positiveCuttingCylinder r → positiveCuttingAnnulus L r :=
  fun q => ⟨(L + q.val.2) • q.val.1.val, by
    change L < ‖(L + q.val.2) • q.val.1.val‖ ∧ ‖(L + q.val.2) • q.val.1.val‖ < L + r
    rw [radial_norm hL]
    exact ⟨lt_add_of_pos_right L q.property.1, (add_lt_add_iff_left L).mpr q.property.2⟩⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.positiveRadial
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.positiveRadial target :: scope.openDecls } }
private theorem point_ne_zero {L r : ℝ} (hL : 0 < L) (x : positiveCuttingAnnulus L r) : x.val ≠ 0 :=
  norm_pos_iff.mp (hL.trans x.property.1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.point_ne_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.point_ne_zero target :: scope.openDecls } }
private def positiveRadialBack {L : ℝ} (hL : 0 < L) (r : ℝ) :
    positiveCuttingAnnulus L r → positiveCuttingCylinder r :=
  fun x => ⟨((homeomorphUnitSphereProd PositiveE3 ⟨x.val, point_ne_zero hL x⟩).1, ‖x.val‖ - L),
    by change 0 < ‖x.val‖ - L ∧ ‖x.val‖ - L < r; constructor <;> linarith [x.property.1, x.property.2]⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.positiveRadialBack
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.positiveRadialBack target :: scope.openDecls } }
private theorem back_direction {L : ℝ} (hL : 0 < L) (r : ℝ) (x : positiveCuttingAnnulus L r) :
    (positiveRadialBack hL r x).val.1.val = ‖x.val‖⁻¹ • x.val :=
  homeomorphUnitSphereProd_apply_fst_coe PositiveE3 _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.back_direction
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.back_direction target :: scope.openDecls } }
private theorem positiveRadial_left {L : ℝ} (hL : 0 < L) (r : ℝ) (q : positiveCuttingCylinder r) :
    positiveRadialBack hL r (positiveRadial hL r q) = q := by
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    rw [back_direction]
    change ‖(L + q.val.2) • q.val.1.val‖⁻¹ • ((L + q.val.2) • q.val.1.val) = q.val.1.val
    rw [radial_norm hL, smul_smul, inv_mul_cancel₀ (add_pos hL q.property.1).ne', one_smul]
  · change ‖(L + q.val.2) • q.val.1.val‖ - L = q.val.2
    rw [radial_norm hL]
    ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.positiveRadial_left
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.positiveRadial_left target :: scope.openDecls } }
private theorem positiveRadial_right {L : ℝ} (hL : 0 < L) (r : ℝ) (x : positiveCuttingAnnulus L r) :
    positiveRadial hL r (positiveRadialBack hL r x) = x := by
  apply Subtype.ext
  change (L + (‖x.val‖ - L)) • (positiveRadialBack hL r x).val.1.val = x.val
  rw [back_direction, show L + (‖x.val‖ - L) = ‖x.val‖ by ring,
    smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr (point_ne_zero hL x)), one_smul]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.positiveRadial_right
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.positiveRadial_right target :: scope.openDecls } }
private theorem positiveRadial_smooth {L : ℝ} (hL : 0 < L) (r : ℝ) :
    ContMDiff PositiveIC (𝓡 3) ∞ (positiveRadial hL r) := by
  apply (ContMDiff.subtypeVal_comp_iff (positiveCuttingAnnulus L r) (positiveRadial hL r)).mp
  have hv := contMDiff_subtype_val (I := PositiveIC) (n := ∞) (U := positiveCuttingCylinder r)
  exact (contMDiff_const.add (contMDiff_snd.comp hv)).smul
    ((contMDiff_coe_sphere (n := 2)).comp (contMDiff_fst.comp hv))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.positiveRadial_smooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.positiveRadial_smooth target :: scope.openDecls } }
private theorem positiveRadialBack_smooth {L : ℝ} (hL : 0 < L) (r : ℝ) :
    ContMDiff (𝓡 3) PositiveIC ∞ (positiveRadialBack hL r) := by
  have hn : ContMDiff (𝓡 3) 𝓘(ℝ) ∞ (fun x : positiveCuttingAnnulus L r => ‖x.val‖) := by
    intro x
    apply (contMDiffAt_subtype_iff (U := positiveCuttingAnnulus L r)).mpr
    exact (contDiffAt_norm ℝ (point_ne_zero hL x)).contMDiffAt
  have hv : ContMDiff (𝓡 3) (𝓡 3) ∞ (fun x : positiveCuttingAnnulus L r => (positiveRadialBack hL r x).val.1.val) := by
    simp_rw [back_direction]
    exact (hn.inv₀ (fun x => norm_ne_zero_iff.mpr (point_ne_zero hL x))).smul
      (contMDiff_subtype_val (U := positiveCuttingAnnulus L r))
  have hy : ContMDiff (𝓡 3) (𝓡 2) ∞ (fun x : positiveCuttingAnnulus L r => (positiveRadialBack hL r x).val.1) :=
    ContMDiff.codRestrict_sphere hv (fun x => (positiveRadialBack hL r x).val.1.property)
  apply (ContMDiff.subtypeVal_comp_iff (positiveCuttingCylinder r) (positiveRadialBack hL r)).mp
  exact hy.prodMk (hn.sub contMDiff_const)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.positiveRadialBack_smooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.positiveRadialBack_smooth target :: scope.openDecls } }

def positiveCuttingDiffeomorph {L : ℝ} (hL : 0 < L) (r : ℝ) :
    positiveCuttingCylinder r ≃ₘ⟮PositiveIC, 𝓡 3⟯ positiveCuttingAnnulus L r where
  toEquiv :=
    { toFun := positiveRadial hL r
      invFun := positiveRadialBack hL r
      left_inv := positiveRadial_left hL r
      right_inv := positiveRadial_right hL r }
  contMDiff_toFun := positiveRadial_smooth hL r
  contMDiff_invFun := positiveRadialBack_smooth hL r

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.positiveCuttingDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.positiveCuttingDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.positiveCuttingDiffeomorph ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.positiveCuttingDiffeomorph

theorem positiveCuttingDiffeomorph_apply {L : ℝ} (hL : 0 < L) (r : ℝ) (q : positiveCuttingCylinder r) :
    (positiveCuttingDiffeomorph hL r q).val = (L + q.val.2) • q.val.1.val := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.positiveCuttingDiffeomorph_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.positiveCuttingDiffeomorph_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.positiveCuttingDiffeomorph_apply ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.positiveCuttingDiffeomorph_apply

theorem positiveCuttingDiffeomorph_symm_direction {L : ℝ} (hL : 0 < L) (r : ℝ) (x : positiveCuttingAnnulus L r) :
    ((positiveCuttingDiffeomorph hL r).symm x).val.1.val = ‖x.val‖⁻¹ • x.val := back_direction hL r x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.positiveCuttingDiffeomorph_symm_direction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.positiveCuttingDiffeomorph_symm_direction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.positiveCuttingDiffeomorph_symm_direction ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.positiveCuttingDiffeomorph_symm_direction

theorem positiveCuttingDiffeomorph_symm_height {L : ℝ} (hL : 0 < L) (r : ℝ) (x : positiveCuttingAnnulus L r) :
    ((positiveCuttingDiffeomorph hL r).symm x).val.2 = ‖x.val‖ - L := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.positiveCuttingDiffeomorph_symm_height then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.positiveCuttingDiffeomorph_symm_height"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.positiveCuttingDiffeomorph_symm_height ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.positiveCuttingDiffeomorph_symm_height
end DifferentialGeometry.Topology.ThreeManifold.Surgery
