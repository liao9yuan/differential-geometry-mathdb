import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.ImmersionTraceLift
import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.SmoothDiskTrace

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.Function _root_.Manifold _root_.Submission.Manifold _root_.ContinuousMap
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.Topology _root_.ContDiff _root_.Manifold _root_.Submission.Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

omit [FiniteDimensional ℝ E] in
theorem realContinuousLinearMap_injective_of_one_ne_zero (L : ℝ →L[ℝ] E)
    (h : L 1 ≠ 0) : _root_.Function.Injective L := by
  intro a b hab
  have hz : (a - b) • L 1 = 0 := by
    rw [← map_smul, smul_eq_mul, mul_one, map_sub, hab, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.realContinuousLinearMap_injective_of_one_ne_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.realContinuousLinearMap_injective_of_one_ne_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.realContinuousLinearMap_injective_of_one_ne_zero ``Submission.DifferentialGeometry.Geometry.realContinuousLinearMap_injective_of_one_ne_zero




theorem IsSmoothEmbeddedLoop.contDiff_parameterLift {γ : freeLoop M}
    (hγ : IsSmoothEmbeddedLoop (E := E) γ) {ψ : ℝ → ℝ} (hψ : Continuous ψ)
    (hc : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun t => γ (ψ t : loopCircle))) :
    ContDiff ℝ ∞ ψ := by
  rw [contDiff_iff_contDiffAt]
  intro t
  exact contDiffAt_parameterLift_of_manifoldImmersion hγ.smooth
    (realContinuousLinearMap_injective_of_one_ne_zero _ (hγ.immersed (ψ t)))
    hψ.continuousAt (hc.contMDiffAt)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.IsSmoothEmbeddedLoop.contDiff_parameterLift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.IsSmoothEmbeddedLoop.contDiff_parameterLift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.IsSmoothEmbeddedLoop.contDiff_parameterLift ``Submission.DifferentialGeometry.Geometry.IsSmoothEmbeddedLoop.contDiff_parameterLift



theorem IsSmoothEmbeddedLoop.contDiff_weakTraceLift {γ : freeLoop M}
    (hγ : IsSmoothEmbeddedLoop (E := E) γ) {u : C(closedDisk, M)}
    (hu : DiskSmoothUpToBoundary (E := E) u) {σ : C(loopCircle, loopCircle)}
    (htrace : diskTrace u = γ.comp σ) {ψ : ℝ → ℝ} (hψ : Continuous ψ)
    (hlift : ∀ t : ℝ, (ψ t : loopCircle) = σ (t : loopCircle)) : ContDiff ℝ ∞ ψ := by
  apply hγ.contDiff_parameterLift hψ
  apply hu.trace.congr
  intro t
  exact (congrArg γ (hlift t)).trans
    (congrArg (fun f : freeLoop M => f (t : loopCircle)) htrace).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.IsSmoothEmbeddedLoop.contDiff_weakTraceLift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.IsSmoothEmbeddedLoop.contDiff_weakTraceLift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.IsSmoothEmbeddedLoop.contDiff_weakTraceLift ``Submission.DifferentialGeometry.Geometry.IsSmoothEmbeddedLoop.contDiff_weakTraceLift




theorem DiskWeakJordanTrace.exists_smooth_signed_lift {γ : freeLoop M}
    {u : C(closedDisk, M)} (h : DiskWeakJordanTrace γ u)
    (hγ : IsSmoothEmbeddedLoop (E := E) γ) (hu : DiskSmoothUpToBoundary (E := E) u) :
    ∃ (σ : C(loopCircle, loopCircle)) (ψ : ℝ → ℝ), ContDiff ℝ ∞ ψ ∧
      (∀ t : ℝ, (ψ t : loopCircle) = σ (t : loopCircle)) ∧ diskTrace u = γ.comp σ ∧
      ((Monotone ψ ∧ ∀ t, ψ (t + 1) = ψ t + 1) ∨
        (Antitone ψ ∧ ∀ t, ψ (t + 1) = ψ t - 1)) := by
  obtain ⟨σ, ⟨ψ, hc, hlift, hsign⟩, htrace⟩ := h
  exact ⟨σ, ψ, hγ.contDiff_weakTraceLift hu htrace hc hlift, hlift, htrace, hsign⟩

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Geometry.DiskWeakJordanTrace
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.DiskWeakJordanTrace.exists_smooth_signed_lift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.DiskWeakJordanTrace.exists_smooth_signed_lift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.DiskWeakJordanTrace.exists_smooth_signed_lift ``Submission.DifferentialGeometry.Geometry.DiskWeakJordanTrace.exists_smooth_signed_lift

end DifferentialGeometry.Geometry
