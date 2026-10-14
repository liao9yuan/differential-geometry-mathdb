import Submission.DifferentialGeometry.Analysis.Complex.BoundaryLens.Geometry
import Submission.DifferentialGeometry.Analysis.Integration.PlaneRotation
import Submission.DifferentialGeometry.Topology.LoopSpace.WeaklyMonotone
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.LoopSpace.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.MeasureTheory
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.NNReal

namespace CircleDeg1Lift
open _root_.CircleDeg1Lift

open _root_.CircleDeg1Lift in
theorem continuous_mul_translate (ψ : CircleDeg1Lift) (hψ : Continuous ψ) (d : ℝ) :
    Continuous (ψ * (CircleDeg1Lift.translate (Multiplicative.ofAdd d) : CircleDeg1Lift)) := by
  change Continuous (fun t : ℝ => ψ (d + t))
  exact hψ.comp (continuous_const.add continuous_id)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `CircleDeg1Lift.continuous_mul_translate then
    throwError "Refusing to shadow existing declaration CircleDeg1Lift.continuous_mul_translate"
  Lean.modifyEnv fun env => Lean.addAlias env `CircleDeg1Lift.continuous_mul_translate ``Submission.CircleDeg1Lift.continuous_mul_translate

open _root_.CircleDeg1Lift in
theorem sub_le_two_thirds_mul_translate (ψ : CircleDeg1Lift)
    (h₁ : ψ (1 / 3 : ℝ) = ψ 0 + 1 / 3)
    (h₂ : ψ (2 / 3 : ℝ) = ψ 0 + 2 / 3) (d : ℝ)
    {a b : ℝ} (hab : b - a ≤ 1 / 3) :
    (ψ * (CircleDeg1Lift.translate (Multiplicative.ofAdd d) : CircleDeg1Lift)) b -
      (ψ * (CircleDeg1Lift.translate (Multiplicative.ofAdd d) : CircleDeg1Lift)) a ≤ 2 / 3 := by
  change ψ (d + b) - ψ (d + a) ≤ 2 / 3
  exact ψ.sub_le_two_thirds_of_map_thirds h₁ h₂ (by linarith)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `CircleDeg1Lift.sub_le_two_thirds_mul_translate then
    throwError "Refusing to shadow existing declaration CircleDeg1Lift.sub_le_two_thirds_mul_translate"
  Lean.modifyEnv fun env => Lean.addAlias env `CircleDeg1Lift.sub_le_two_thirds_mul_translate ``Submission.CircleDeg1Lift.sub_le_two_thirds_mul_translate

end CircleDeg1Lift

namespace DifferentialGeometry.Analysis

theorem preimage_rotated_boundaryLens (ζ : Circle) (r : ℝ) :
    rotation ζ ⁻¹' (Metric.closedBall (rotation ζ (-1)) r ∩ Metric.closedBall (0 : ℂ) 1) =
      boundaryLens r := by
  ext z
  simp only [boundaryLens, _root_.Set.mem_preimage, _root_.Set.mem_inter_iff, Metric.mem_closedBall,
    dist_zero_right, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.dist_map]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.preimage_rotated_boundaryLens then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.preimage_rotated_boundaryLens"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.preimage_rotated_boundaryLens ``Submission.DifferentialGeometry.Analysis.preimage_rotated_boundaryLens

theorem preimage_rotated_annular_cap (ζ : Circle) (r R : ℝ) :
    rotation ζ ⁻¹' ({z : ℂ | _root_.Dist.dist z (rotation ζ (-1)) ∈ _root_.Set.Icc r R} ∩
      Metric.closedBall (0 : ℂ) 1) =
      {z : ℂ | _root_.Dist.dist z (-1) ∈ _root_.Set.Icc r R} ∩ Metric.closedBall (0 : ℂ) 1 := by
  ext z
  simp only [_root_.Set.mem_preimage, _root_.Set.mem_inter_iff, _root_.Set.mem_ofPred_eq, Metric.mem_closedBall,
    dist_zero_right, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.dist_map]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.preimage_rotated_annular_cap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.preimage_rotated_annular_cap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.preimage_rotated_annular_cap ``Submission.DifferentialGeometry.Analysis.preimage_rotated_annular_cap

theorem lipschitzWith_comp_rotation {M : Type*} [PseudoEMetricSpace M]
    {f : ℂ → M} {K : ℝ≥0} (hf : LipschitzWith K f) (ζ : Circle) :
    LipschitzWith K (f ∘ rotation ζ) := by
  simpa only [mul_one] using hf.comp (rotation ζ).isometry.lipschitz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.lipschitzWith_comp_rotation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.lipschitzWith_comp_rotation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.lipschitzWith_comp_rotation ``Submission.DifferentialGeometry.Analysis.lipschitzWith_comp_rotation

theorem mapsTo_comp_rotation_closedDisk {M : Type*} {f : ℂ → M} {S : Set M}
    (hf : _root_.Set.MapsTo f (Metric.closedBall (0 : ℂ) 1) S) (ζ : Circle) :
    MapsTo (f ∘ rotation ζ) (Metric.closedBall (0 : ℂ) 1) S := by
  intro z hz
  apply hf
  simpa only [Metric.mem_closedBall, dist_zero_right, LinearIsometryEquiv.norm_map] using hz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.mapsTo_comp_rotation_closedDisk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.mapsTo_comp_rotation_closedDisk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.mapsTo_comp_rotation_closedDisk ``Submission.DifferentialGeometry.Analysis.mapsTo_comp_rotation_closedDisk

theorem circle_trace_comp_rotation {M : Type*} (f : ℂ → M) (Γ : loopCircle → M)
    (ψ : ℝ → ℝ)
    (htrace : ∀ t : ℝ, f (circleMap 0 1 (2 * Real.pi * t)) = Γ (ψ t : loopCircle))
    (d t : ℝ) :
    (f ∘ rotation (Circle.exp (2 * Real.pi * d))) (circleMap 0 1 (2 * Real.pi * t)) =
      Γ (ψ (d + t) : loopCircle) := by
  rw [Function.comp_apply, rotation_exp_circleMap,
    show 2 * Real.pi * d + 2 * Real.pi * t = 2 * Real.pi * (d + t) by ring, htrace]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.circle_trace_comp_rotation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.circle_trace_comp_rotation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.circle_trace_comp_rotation ``Submission.DifferentialGeometry.Analysis.circle_trace_comp_rotation

theorem circle_lift_trace_comp_rotation {M : Type*} (f : ℂ → M) (Γ : loopCircle → M)
    (ψ : CircleDeg1Lift)
    (htrace : ∀ t : ℝ, f (circleMap 0 1 (2 * Real.pi * t)) = Γ (ψ t : loopCircle))
    (d t : ℝ) :
    (f ∘ rotation (Circle.exp (2 * Real.pi * d))) (circleMap 0 1 (2 * Real.pi * t)) =
      Γ ((ψ * (CircleDeg1Lift.translate (Multiplicative.ofAdd d) :
        CircleDeg1Lift)) t : loopCircle) :=
  circle_trace_comp_rotation f Γ ψ htrace d t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.circle_lift_trace_comp_rotation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.circle_lift_trace_comp_rotation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.circle_lift_trace_comp_rotation ``Submission.DifferentialGeometry.Analysis.circle_lift_trace_comp_rotation

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem integral_quadratic_fderiv_comp_rotation_boundaryLens
    (A : F → F →L[ℝ] F →L[ℝ] ℝ) (f : ℂ → F) (ζ : Circle) (r : ℝ) :
    (∫ z in boundaryLens r,
      (A (f (rotation ζ z)) (fderiv ℝ (f ∘ rotation ζ) z 1)
          (fderiv ℝ (f ∘ rotation ζ) z 1) +
        A (f (rotation ζ z)) (fderiv ℝ (f ∘ rotation ζ) z Complex.I)
          (fderiv ℝ (f ∘ rotation ζ) z Complex.I)) / 2) =
      ∫ z in Metric.closedBall (rotation ζ (-1)) r ∩ Metric.closedBall (0 : ℂ) 1,
        (A (f z) (fderiv ℝ f z 1) (fderiv ℝ f z 1) +
          A (f z) (fderiv ℝ f z Complex.I) (fderiv ℝ f z Complex.I)) / 2 := by
  simpa only [preimage_rotated_boundaryLens] using
    integral_quadratic_fderiv_comp_rotation_preimage A f ζ
      (Metric.closedBall (rotation ζ (-1)) r ∩ Metric.closedBall (0 : ℂ) 1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.integral_quadratic_fderiv_comp_rotation_boundaryLens then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.integral_quadratic_fderiv_comp_rotation_boundaryLens"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.integral_quadratic_fderiv_comp_rotation_boundaryLens ``Submission.DifferentialGeometry.Analysis.integral_quadratic_fderiv_comp_rotation_boundaryLens

theorem integral_quadratic_fderiv_comp_rotation_annular_cap
    (A : F → F →L[ℝ] F →L[ℝ] ℝ) (f : ℂ → F) (ζ : Circle) (r R : ℝ) :
    (∫ z in {z : ℂ | _root_.Dist.dist z (-1) ∈ _root_.Set.Icc r R} ∩ Metric.closedBall (0 : ℂ) 1,
      (A (f (rotation ζ z)) (fderiv ℝ (f ∘ rotation ζ) z 1)
          (fderiv ℝ (f ∘ rotation ζ) z 1) +
        A (f (rotation ζ z)) (fderiv ℝ (f ∘ rotation ζ) z Complex.I)
          (fderiv ℝ (f ∘ rotation ζ) z Complex.I)) / 2) =
      ∫ z in {z : ℂ | _root_.Dist.dist z (rotation ζ (-1)) ∈ _root_.Set.Icc r R} ∩ Metric.closedBall (0 : ℂ) 1,
        (A (f z) (fderiv ℝ f z 1) (fderiv ℝ f z 1) +
          A (f z) (fderiv ℝ f z Complex.I) (fderiv ℝ f z Complex.I)) / 2 := by
  simpa only [preimage_rotated_annular_cap] using
    integral_quadratic_fderiv_comp_rotation_preimage A f ζ
      ({z : ℂ | _root_.Dist.dist z (rotation ζ (-1)) ∈ _root_.Set.Icc r R} ∩ Metric.closedBall (0 : ℂ) 1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.integral_quadratic_fderiv_comp_rotation_annular_cap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.integral_quadratic_fderiv_comp_rotation_annular_cap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.integral_quadratic_fderiv_comp_rotation_annular_cap ``Submission.DifferentialGeometry.Analysis.integral_quadratic_fderiv_comp_rotation_annular_cap

end DifferentialGeometry.Analysis

end
