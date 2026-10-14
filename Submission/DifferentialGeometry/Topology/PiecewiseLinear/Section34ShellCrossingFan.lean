import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorphOpen
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

noncomputable def section34ShellCrossingFan : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) where
  toFun p := (p.1 - p.2 / 2, p.2 + 2 * _root_.Max.max (p.1 - p.2 / 2) 0)
  invFun p := (p.1 + (p.2 - 2 * _root_.Max.max p.1 0) / 2, p.2 - 2 * _root_.Max.max p.1 0)
  left_inv p := by ext <;> dsimp <;> ring
  right_inv p := by
    dsimp
    rw [show p.1 + (p.2 - 2 * _root_.Max.max p.1 0) / 2 - (p.2 - 2 * _root_.Max.max p.1 0) / 2 = p.1 by ring]
    ext <;> dsimp; ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34ShellCrossingFan then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34ShellCrossingFan"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34ShellCrossingFan ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34ShellCrossingFan

theorem isPLHomeomorphOn_section34ShellCrossingFan :
    IsPLHomeomorphOn section34ShellCrossingFan _root_.Set.univ univ := by
  let T : (ℝ × ℝ) →ₗ[ℝ] ℝ := LinearMap.fst ℝ ℝ ℝ - (1 / 2 : ℝ) • LinearMap.snd ℝ ℝ ℝ
  have hT : IsPiecewiseAffineOn (fun p : ℝ × ℝ => p.1 - p.2 / 2) univ := by
    convert isPiecewiseAffineOn_of_affine T.toAffineMap isOpen_univ using 1
    ext p
    simp [T, div_eq_mul_inv, mul_comm]
  have hzero : IsPiecewiseAffineOn (fun _ : ℝ × ℝ => (0 : ℝ)) univ :=
    isPiecewiseAffineOn_of_affine (AffineMap.const ℝ _ 0) isOpen_univ
  have hR := isPiecewiseAffineOn_of_affine (LinearMap.snd ℝ ℝ ℝ).toAffineMap isOpen_univ
  have hpl : IsPiecewiseAffineOn section34ShellCrossingFan univ := by
    convert hT.prod_mk (hR.add ((hT.max hzero).add (hT.max hzero))) using 1
    ext p <;> dsimp [section34ShellCrossingFan]; ring
  have hbij : _root_.Set.BijOn section34ShellCrossingFan _root_.Set.univ univ :=
    ⟨mapsTo_univ _ _, section34ShellCrossingFan.injective.injOn, fun y _ =>
      ⟨section34ShellCrossingFan.symm y, _root_.Set.mem_univ _,
        section34ShellCrossingFan.apply_symm_apply y⟩⟩
  have hinv := IsPiecewiseAffineOn.symm
    (e := section34ShellCrossingFan.toOpenPartialHomeomorph) hpl
  refine ⟨hbij, hpl, hinv.congr fun y hy => ?_⟩
  apply section34ShellCrossingFan.injective
  exact (hbij.invOn_invFunOn.2 hy).trans (section34ShellCrossingFan.apply_symm_apply y).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_section34ShellCrossingFan then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_section34ShellCrossingFan"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_section34ShellCrossingFan ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_section34ShellCrossingFan

theorem section34ShellCrossingFan_horizontal_iff (p : ℝ × ℝ) :
    (section34ShellCrossingFan p).2 = 2 * _root_.Max.max (section34ShellCrossingFan p).1 0 ↔
      p.2 = 0 := by
  change p.2 + 2 * _root_.Max.max (p.1 - p.2 / 2) 0 = 2 * _root_.Max.max (p.1 - p.2 / 2) 0 ↔ p.2 = 0
  exact add_eq_right

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34ShellCrossingFan_horizontal_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34ShellCrossingFan_horizontal_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34ShellCrossingFan_horizontal_iff ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34ShellCrossingFan_horizontal_iff

theorem section34ShellCrossingFan_vertical_iff (p : ℝ × ℝ) :
    (section34ShellCrossingFan p).2 = -2 * _root_.Min.min (section34ShellCrossingFan p).1 0 ↔
      p.1 = 0 := by
  change p.2 + 2 * _root_.Max.max (p.1 - p.2 / 2) 0 = -2 * _root_.Min.min (p.1 - p.2 / 2) 0 ↔ p.1 = 0
  have h := max_add_min (p.1 - p.2 / 2) 0
  constructor <;> intro hp <;> linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34ShellCrossingFan_vertical_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34ShellCrossingFan_vertical_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34ShellCrossingFan_vertical_iff ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34ShellCrossingFan_vertical_iff

end DifferentialGeometry.Topology.PiecewiseLinear
