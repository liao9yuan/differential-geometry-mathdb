import Submission.DifferentialGeometry.Topology.Manifold.SmoothTwoSidedCollarRestriction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Topology.SmoothTwoSidedCollar

private def rescaleInterval (r lambda : ℝ) (hlambda : 0 < lambda) :
    Diffeomorph 𝓘(ℝ) 𝓘(ℝ) (symmetricOpenInterval (lambda * r)) (symmetricOpenInterval r) ∞ where
  toFun t := ⟨t.val / lambda, by
    constructor
    · apply (lt_div_iff₀ hlambda).mpr
      nlinarith [t.property.1]
    · apply (div_lt_iff₀ hlambda).mpr
      nlinarith [t.property.2]⟩
  invFun t := ⟨lambda * t.val, by constructor <;> nlinarith [t.property.1, t.property.2]⟩
  left_inv t := Subtype.ext (by field_simp)
  right_inv t := Subtype.ext (by simp [hlambda.ne'])
  contMDiff_toFun := (ContMDiff.subtypeVal_comp_iff (symmetricOpenInterval r) _).mp
    (contMDiff_subtype_val.div_const lambda)
  contMDiff_invFun := (ContMDiff.subtypeVal_comp_iff (symmetricOpenInterval (lambda * r)) _).mp
    (contMDiff_const.mul contMDiff_subtype_val)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SmoothTwoSidedCollar.rescaleInterval
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SmoothTwoSidedCollar.rescaleInterval target :: scope.openDecls } }

variable {E H F G S M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  [TopologicalSpace S] [ChartedSpace H S]
  [TopologicalSpace M] [ChartedSpace G M]
  {e : S → M} (c : SmoothTwoSidedCollar I J e)

def rescaleParameter (lambda : ℝ) (hlambda : 0 < lambda) : SmoothTwoSidedCollar I J e where
  radius := lambda * c.radius
  radius_pos := mul_pos hlambda c.radius_pos
  neighborhood := c.neighborhood
  toDiffeomorph := ((Diffeomorph.refl I S ∞).prodCongr
    (rescaleInterval c.radius lambda hlambda)).trans c.toDiffeomorph
  zero_eq s := by
    change c.toFun (s, ⟨(0 : ℝ) / lambda, _⟩) = e s
    exact (congrArg (fun t : symmetricOpenInterval c.radius => c.toFun (s, t))
      (Subtype.ext (zero_div lambda))).trans (c.toFun_zero s)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SmoothTwoSidedCollar.rescaleParameter then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SmoothTwoSidedCollar.rescaleParameter"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SmoothTwoSidedCollar.rescaleParameter ``Submission.DifferentialGeometry.Topology.SmoothTwoSidedCollar.rescaleParameter

@[simp] theorem rescaleParameter_radius (lambda : ℝ) (hlambda : 0 < lambda) :
    (c.rescaleParameter lambda hlambda).radius = lambda * c.radius := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SmoothTwoSidedCollar.rescaleParameter_radius then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SmoothTwoSidedCollar.rescaleParameter_radius"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SmoothTwoSidedCollar.rescaleParameter_radius ``Submission.DifferentialGeometry.Topology.SmoothTwoSidedCollar.rescaleParameter_radius

@[simp] theorem rescaleParameter_neighborhood (lambda : ℝ) (hlambda : 0 < lambda) :
    (c.rescaleParameter lambda hlambda).neighborhood = c.neighborhood := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SmoothTwoSidedCollar.rescaleParameter_neighborhood then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SmoothTwoSidedCollar.rescaleParameter_neighborhood"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SmoothTwoSidedCollar.rescaleParameter_neighborhood ``Submission.DifferentialGeometry.Topology.SmoothTwoSidedCollar.rescaleParameter_neighborhood

@[simp] theorem rescaleParameter_toFun (lambda : ℝ) (hlambda : 0 < lambda)
    (p : S × symmetricOpenInterval (lambda * c.radius)) :
    (c.rescaleParameter lambda hlambda).toFun p = c.toFun (p.1, ⟨p.2.val / lambda, by
      constructor
      · apply (lt_div_iff₀ hlambda).mpr
        nlinarith [p.2.property.1]
      · apply (div_lt_iff₀ hlambda).mpr
        nlinarith [p.2.property.2]⟩) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SmoothTwoSidedCollar.rescaleParameter_toFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SmoothTwoSidedCollar.rescaleParameter_toFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SmoothTwoSidedCollar.rescaleParameter_toFun ``Submission.DifferentialGeometry.Topology.SmoothTwoSidedCollar.rescaleParameter_toFun

theorem rescaleParameter_symm_toDiffeomorph (lambda : ℝ) (hlambda : 0 < lambda)
    (p : c.neighborhood) :
    (c.rescaleParameter lambda hlambda).toDiffeomorph.symm p =
      ((c.toDiffeomorph.symm p).1, ⟨lambda * (c.toDiffeomorph.symm p).2.val, by
        change -(lambda * c.radius) < lambda * (c.toDiffeomorph.symm p).2.val ∧
          lambda * (c.toDiffeomorph.symm p).2.val < lambda * c.radius
        constructor <;> nlinarith [(c.toDiffeomorph.symm p).2.property.1,
          (c.toDiffeomorph.symm p).2.property.2]⟩) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SmoothTwoSidedCollar.rescaleParameter_symm_toDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SmoothTwoSidedCollar.rescaleParameter_symm_toDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SmoothTwoSidedCollar.rescaleParameter_symm_toDiffeomorph ``Submission.DifferentialGeometry.Topology.SmoothTwoSidedCollar.rescaleParameter_symm_toDiffeomorph

theorem rescaleParameter_radius_add_le (hc : c.radius ≤ 1 / 2)
    (R : ℝ) (hR : 0 < R) :
    (c.rescaleParameter (2 * R) (mul_pos (by norm_num) hR)).radius + R ≤ 2 * R := by
  rw [rescaleParameter_radius]
  nlinarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SmoothTwoSidedCollar.rescaleParameter_radius_add_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SmoothTwoSidedCollar.rescaleParameter_radius_add_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SmoothTwoSidedCollar.rescaleParameter_radius_add_le ``Submission.DifferentialGeometry.Topology.SmoothTwoSidedCollar.rescaleParameter_radius_add_le

theorem restrictRadius_rescaleParameter_radius_add_lt (R : ℝ) (hR : 0 < R) :
    ((c.restrictRadius (_root_.Min.min c.radius (1 / 4))
      (lt_min c.radius_pos (by norm_num)) (min_le_left _ _)).rescaleParameter
      (2 * R) (mul_pos (by norm_num) hR)).radius + R < 2 * R := by
  rw [rescaleParameter_radius, restrictRadius_radius]
  have hr : _root_.Min.min c.radius (1 / 4) ≤ (1 / 4 : ℝ) := min_le_right _ _
  nlinarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SmoothTwoSidedCollar.restrictRadius_rescaleParameter_radius_add_lt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SmoothTwoSidedCollar.restrictRadius_rescaleParameter_radius_add_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SmoothTwoSidedCollar.restrictRadius_rescaleParameter_radius_add_lt ``Submission.DifferentialGeometry.Topology.SmoothTwoSidedCollar.restrictRadius_rescaleParameter_radius_add_lt

end DifferentialGeometry.Topology.SmoothTwoSidedCollar
