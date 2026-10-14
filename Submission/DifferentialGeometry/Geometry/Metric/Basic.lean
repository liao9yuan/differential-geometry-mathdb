import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry

open _root_.Bundle
open scoped _root_.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H]

abbrev SmoothRiemannianMetric
    (I : ModelWithCorners Real E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] : Type _ :=
  Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M -> Type _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SmoothRiemannianMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SmoothRiemannianMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SmoothRiemannianMetric ``Submission.DifferentialGeometry.SmoothRiemannianMetric

@[ext]
theorem SmoothRiemannianMetric.ext_inner
    {I : ModelWithCorners Real E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {g h : SmoothRiemannianMetric I M}
    (hinner : ∀ (x : M) (v w : TangentSpace I x),
      g.inner x v w = h.inner x v w) :
    g = h := by
  obtain ⟨gi, gs, gp, gb, gc⟩ := g
  obtain ⟨hi, hs, hp, hb, hc⟩ := h
  have hfield : gi = hi :=
    funext fun x =>
      ContinuousLinearMap.ext fun v =>
        ContinuousLinearMap.ext fun w => hinner x v w
  subst hfield
  rfl

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.SmoothRiemannianMetric
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SmoothRiemannianMetric.ext_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SmoothRiemannianMetric.ext_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SmoothRiemannianMetric.ext_inner ``Submission.DifferentialGeometry.SmoothRiemannianMetric.ext_inner

theorem metric_inner_self_nonneg
    {I : ModelWithCorners Real E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (g : SmoothRiemannianMetric I M) (x : M) (v : TangentSpace I x) :
    0 ≤ g.inner x v v := by
  by_cases hv : v = 0
  · simp [hv]
  · exact (g.pos x v hv).le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.metric_inner_self_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.metric_inner_self_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.metric_inner_self_nonneg ``Submission.DifferentialGeometry.metric_inner_self_nonneg

end DifferentialGeometry
