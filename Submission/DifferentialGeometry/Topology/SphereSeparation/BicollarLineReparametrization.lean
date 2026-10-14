import Mathlib.Analysis.Normed.Module.Ball.Homeomorph

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Metric _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions


def bicollarLineHomeomorph {A : Type*} [TopologicalSpace A] (a : ℝ) (ha : 0 < a) :
    A × ℝ ≃ₜ {p : A × ℝ // -a < p.2 ∧ p.2 < a} where
  toFun p := ⟨(p.1, OpenPartialHomeomorph.univBall (0 : ℝ) a p.2), by
    have hp := (OpenPartialHomeomorph.univBall (0 : ℝ) a).map_source
      (by simp : p.2 ∈ (OpenPartialHomeomorph.univBall (0 : ℝ) a).source)
    rw [OpenPartialHomeomorph.univBall_target _ ha, Real.ball_eq_Ioo] at hp
    simpa using hp⟩
  invFun p := (p.1.1, (OpenPartialHomeomorph.univBall (0 : ℝ) a).symm p.1.2)
  left_inv p := Prod.ext rfl ((OpenPartialHomeomorph.univBall (0 : ℝ) a).left_inv (by simp))
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    apply (OpenPartialHomeomorph.univBall (0 : ℝ) a).right_inv
    rw [OpenPartialHomeomorph.univBall_target _ ha, Real.ball_eq_Ioo]
    simpa using p.property
  continuous_toFun := (continuous_fst.prodMk
    ((OpenPartialHomeomorph.continuous_univBall (0 : ℝ) a).comp continuous_snd)).subtype_mk _
  continuous_invFun := (continuous_fst.comp continuous_subtype_val).prodMk
    ((OpenPartialHomeomorph.continuousOn_univBall_symm (0 : ℝ) a).comp_continuous
      (continuous_snd.comp continuous_subtype_val) (by
        intro p
        simpa [Real.ball_eq_Ioo] using p.property))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.bicollarLineHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.bicollarLineHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.bicollarLineHomeomorph ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.bicollarLineHomeomorph


theorem bicollarLineHomeomorph_center {A : Type*} [TopologicalSpace A]
    (a : ℝ) (ha : 0 < a) (y : A) :
    (bicollarLineHomeomorph a ha (y, 0)).val = (y, 0) := by
  change (y, OpenPartialHomeomorph.univBall (0 : ℝ) a 0) = (y, 0)
  rw [OpenPartialHomeomorph.univBall_apply_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.bicollarLineHomeomorph_center then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.bicollarLineHomeomorph_center"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.bicollarLineHomeomorph_center ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.bicollarLineHomeomorph_center

private theorem bicollar_line_formula (a : ℝ) (ha : 0 < a) (z : ℝ) :
    OpenPartialHomeomorph.univBall (0 : ℝ) a z =
      (a * (Real.sqrt (1 + ‖z‖ ^ 2))⁻¹) * z := by
  rw [OpenPartialHomeomorph.univBall, dif_pos ha]
  change a * ((Real.sqrt (1 + ‖z‖ ^ 2))⁻¹ * z) + 0 = _
  simp only [add_zero, mul_assoc]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.bicollar_line_formula
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.bicollar_line_formula target :: scope.openDecls } }


theorem bicollarLineHomeomorph_negative_iff {A : Type*} [TopologicalSpace A]
    (a : ℝ) (ha : 0 < a) (y : A) (z : ℝ) :
    (bicollarLineHomeomorph a ha (y, z)).val.2 < 0 ↔ z < 0 := by
  change OpenPartialHomeomorph.univBall (0 : ℝ) a z < 0 ↔ z < 0
  rw [bicollar_line_formula a ha z]
  have hpos : 0 < a * (Real.sqrt (1 + ‖z‖ ^ 2))⁻¹ :=
    mul_pos ha (inv_pos.mpr (Real.sqrt_pos.mpr (by positivity)))
  rw [mul_neg_iff]
  simp only [hpos, hpos.not_gt, true_and, false_and, or_false]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.bicollarLineHomeomorph_negative_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.bicollarLineHomeomorph_negative_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.bicollarLineHomeomorph_negative_iff ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.bicollarLineHomeomorph_negative_iff


theorem bicollarLineHomeomorph_positive_iff {A : Type*} [TopologicalSpace A]
    (a : ℝ) (ha : 0 < a) (y : A) (z : ℝ) :
    0 < (bicollarLineHomeomorph a ha (y, z)).val.2 ↔ 0 < z := by
  change 0 < OpenPartialHomeomorph.univBall (0 : ℝ) a z ↔ 0 < z
  rw [bicollar_line_formula a ha z]
  exact mul_pos_iff_of_pos_left (mul_pos ha (inv_pos.mpr (Real.sqrt_pos.mpr (by positivity))))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.bicollarLineHomeomorph_positive_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.bicollarLineHomeomorph_positive_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.bicollarLineHomeomorph_positive_iff ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.bicollarLineHomeomorph_positive_iff

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
