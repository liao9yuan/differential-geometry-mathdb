import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.ConformalDisk
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.Function _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ContDiff _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold

namespace DifferentialGeometry.Geometry



theorem diskBoundary_angle (θ : ℝ) :
    (diskBoundary ((θ / (2 * Real.pi) : ℝ) : loopCircle) : ℂ) = circleMap 0 1 θ := by
  rw [diskBoundary_coe]
  have hθ : 2 * Real.pi * (θ / (2 * Real.pi)) = θ := by
    field_simp
  simp [hθ, circleMap]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.diskBoundary_angle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.diskBoundary_angle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.diskBoundary_angle ``Submission.DifferentialGeometry.Geometry.diskBoundary_angle




theorem IsSmoothPositiveCircleMap.exists_angle_parameter {σ : C(loopCircle, loopCircle)}
    (hσ : IsSmoothPositiveCircleMap σ) :
    ∃ φ : ℝ → ℝ, ContDiff ℝ ∞ φ ∧ Monotone φ ∧
      (∀ θ, φ (θ + 2 * Real.pi) = φ θ + 1) ∧
      (∀ θ, (φ θ : loopCircle) = σ ((θ / (2 * Real.pi) : ℝ) : loopCircle)) := by
  obtain ⟨ψ, hψ, hm, hp, hl⟩ := hσ
  refine ⟨fun θ => ψ (θ / (2 * Real.pi)), hψ.comp (contDiff_id.div_const _),
    fun a b hab => hm (div_le_div_of_nonneg_right hab (by positivity)), ?_, fun θ => hl _⟩
  intro θ
  have hθ : (θ + 2 * Real.pi) / (2 * Real.pi) = θ / (2 * Real.pi) + 1 := by
    field_simp
  dsimp only
  rw [hθ, hp]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.IsSmoothPositiveCircleMap.exists_angle_parameter then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.IsSmoothPositiveCircleMap.exists_angle_parameter"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.IsSmoothPositiveCircleMap.exists_angle_parameter ``Submission.DifferentialGeometry.Geometry.IsSmoothPositiveCircleMap.exists_angle_parameter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]



theorem SmoothDiskExtension.angle_trace {u : C(closedDisk, M)} {U : ℂ → M}
    (hu : SmoothDiskExtension (E := E) u U) {γ : freeLoop M}
    {σ : C(loopCircle, loopCircle)} (htrace : diskTrace u = γ.comp σ)
    {φ : ℝ → ℝ}
    (hl : ∀ θ, (φ θ : loopCircle) = σ ((θ / (2 * Real.pi) : ℝ) : loopCircle)) :
    U ∘ circleMap 0 1 = (fun t : ℝ => γ (t : loopCircle)) ∘ φ := by
  funext θ
  change U (circleMap 0 1 θ) = γ (φ θ : loopCircle)
  rw [← diskBoundary_angle θ, hu.1 _]
  have ht := congrArg (fun η : freeLoop M => η ((θ / (2 * Real.pi) : ℝ) : loopCircle)) htrace
  exact ht.trans (congrArg γ (hl θ).symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.SmoothDiskExtension.angle_trace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.SmoothDiskExtension.angle_trace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.SmoothDiskExtension.angle_trace ``Submission.DifferentialGeometry.Geometry.SmoothDiskExtension.angle_trace

end DifferentialGeometry.Geometry
