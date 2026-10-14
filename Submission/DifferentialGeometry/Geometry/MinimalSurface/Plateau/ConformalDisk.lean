import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.MorreyDisk
import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.SmoothExtension

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission








noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry _root_.Set _root_.ContinuousMap
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry



def IsSmoothPositiveCircleMap (σ : C(loopCircle, loopCircle)) : Prop :=
  ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ Monotone ψ ∧
    (∀ t, ψ (t + 1) = ψ t + 1) ∧ (∀ t : ℝ, (ψ t : loopCircle) = σ (t : loopCircle))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.IsSmoothPositiveCircleMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.IsSmoothPositiveCircleMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.IsSmoothPositiveCircleMap ``Submission.DifferentialGeometry.Geometry.IsSmoothPositiveCircleMap



theorem IsSmoothPositiveCircleMap.weaklyMonotoneOnce {σ : C(loopCircle, loopCircle)}
    (h : IsSmoothPositiveCircleMap σ) : IsWeaklyMonotoneOnce σ := by
  obtain ⟨ψ, hψ, hm, hp, hl⟩ := h
  exact ⟨ψ, hψ.continuous, hl, Or.inl ⟨hm, hp⟩⟩

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Geometry.IsSmoothPositiveCircleMap
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.IsSmoothPositiveCircleMap.weaklyMonotoneOnce then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.IsSmoothPositiveCircleMap.weaklyMonotoneOnce"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.IsSmoothPositiveCircleMap.weaklyMonotoneOnce ``Submission.DifferentialGeometry.Geometry.IsSmoothPositiveCircleMap.weaklyMonotoneOnce

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]




structure IsConformalMinimizingDisk (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ : freeLoop M) (u : C(closedDisk, M)) (σ : C(loopCircle, loopCircle))
    (U : ℂ → M) : Prop where
  extension : SmoothDiskExtension (E := E) u U
  positiveTrace : IsSmoothPositiveCircleMap σ
  trace : diskTrace u = γ.comp σ
  conformal : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, DiskMapConformalAt g U z
  harmonic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, diskMapTension g U z = 0
  minimizesSmooth : ∀ v : C(closedDisk, M), DiskSmoothUpToBoundary (E := E) v →
    diskTrace v = γ → riemannianDiskArea g u ≤ riemannianDiskArea g v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.IsConformalMinimizingDisk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.IsConformalMinimizingDisk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.IsConformalMinimizingDisk ``Submission.DifferentialGeometry.Geometry.IsConformalMinimizingDisk



theorem IsConformalMinimizingDisk.weakJordanTrace
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M}
    {u : C(closedDisk, M)} {σ : C(loopCircle, loopCircle)} {U : ℂ → M}
    (h : IsConformalMinimizingDisk g γ u σ U) : DiskWeakJordanTrace γ u :=
  ⟨σ, h.positiveTrace.weaklyMonotoneOnce, h.trace⟩

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Geometry.IsConformalMinimizingDisk
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.IsConformalMinimizingDisk.weakJordanTrace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.IsConformalMinimizingDisk.weakJordanTrace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.IsConformalMinimizingDisk.weakJordanTrace ``Submission.DifferentialGeometry.Geometry.IsConformalMinimizingDisk.weakJordanTrace

end DifferentialGeometry.Geometry
