import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Topology.VectorBundle.Riemannian

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Bundle
open scoped _root_.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] {n : ℕ∞ω}

open _root_.IsContMDiffRiemannianBundle in
theorem IsContMDiffRiemannianBundle.isContinuousRiemannianBundle
    [h : IsContMDiffRiemannianBundle I n F V] : IsContinuousRiemannianBundle F V := by
  obtain ⟨g, hg, hinner⟩ := h.exists_contMDiff
  exact ⟨g, hg.continuous, hinner⟩

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.IsContMDiffRiemannianBundle
  let env ← Lean.getEnv
  if env.contains `IsContMDiffRiemannianBundle.isContinuousRiemannianBundle then
    throwError "Refusing to shadow existing declaration IsContMDiffRiemannianBundle.isContinuousRiemannianBundle"
  Lean.modifyEnv fun env => Lean.addAlias env `IsContMDiffRiemannianBundle.isContinuousRiemannianBundle ``Submission.IsContMDiffRiemannianBundle.isContinuousRiemannianBundle
