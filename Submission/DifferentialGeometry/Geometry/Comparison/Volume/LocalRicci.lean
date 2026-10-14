import Submission.DifferentialGeometry.Geometry.Comparison.BonnetMyers.RicciBound

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set
open scoped _root_.ContDiff _root_.Manifold

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

def ricciBoundedBelowOn (g : SmoothRiemannianMetric I M) (s : Set M) (κ : ℝ) : Prop :=
  ∀ x ∈ s, ∀ v : TangentSpace I x,
    κ * (g.inner x v v : ℝ) ≤ ricciTensor (I := I) g x v v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.ricciBoundedBelowOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.VolumeComparison.ricciBoundedBelowOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.ricciBoundedBelowOn ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.ricciBoundedBelowOn

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem ricciBoundedBelowOn_mono {g : SmoothRiemannianMetric I M}
    {s t : Set M} {κ : ℝ} (hst : s ⊆ t) (h : ricciBoundedBelowOn g t κ) :
    ricciBoundedBelowOn g s κ := by
  intro x hx v
  exact h x (hst hx) v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.ricciBoundedBelowOn_mono then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.VolumeComparison.ricciBoundedBelowOn_mono"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.ricciBoundedBelowOn_mono ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.ricciBoundedBelowOn_mono

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem ricciBoundedBelowOn_of_global {g : SmoothRiemannianMetric I M}
    {s : Set M} {κ : ℝ}
    (h : BonnetMyers.RicciBoundedBelow (I := I) g κ) :
    ricciBoundedBelowOn g s κ := by
  intro x _ v
  exact h x v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.ricciBoundedBelowOn_of_global then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.VolumeComparison.ricciBoundedBelowOn_of_global"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.ricciBoundedBelowOn_of_global ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.ricciBoundedBelowOn_of_global

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem ricciBoundedBelowOn_univ_iff {g : SmoothRiemannianMetric I M} {κ : ℝ} :
    ricciBoundedBelowOn g Set.univ κ ↔
      BonnetMyers.RicciBoundedBelow (I := I) g κ := by
  constructor
  · intro h x v
    exact h x (Set.mem_univ x) v
  · exact ricciBoundedBelowOn_of_global

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.ricciBoundedBelowOn_univ_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.VolumeComparison.ricciBoundedBelowOn_univ_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.ricciBoundedBelowOn_univ_iff ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.ricciBoundedBelowOn_univ_iff

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem ricciBoundedBelowOn_apply {g : SmoothRiemannianMetric I M}
    {s : Set M} {κ : ℝ} (h : ricciBoundedBelowOn g s κ)
    {x : M} (hx : x ∈ s) (v : TangentSpace I x) :
    κ * (g.inner x v v : ℝ) ≤ ricciTensor (I := I) g x v v :=
  h x hx v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.ricciBoundedBelowOn_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.VolumeComparison.ricciBoundedBelowOn_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.ricciBoundedBelowOn_apply ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.ricciBoundedBelowOn_apply

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
