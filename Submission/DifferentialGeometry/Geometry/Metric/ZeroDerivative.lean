import Submission.DifferentialGeometry.Geometry.Metric.ConvexSourceLipschitz

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry
open scoped _root_.Topology _root_.ContDiff _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.Geometry

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T3Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
set_option backward.isDefEq.respectTransparency false in
theorem eq_of_mfderiv_eq_zero_on_convex
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {f : V → M} {U S : Set V}
    (hU : IsOpen U) (hf : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) 1 f U)
    (hSU : S ⊆ U) (hS : Convex ℝ S)
    (hd : ∀ p ∈ S, mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) f p = 0)
    {x y : V} (hx : x ∈ S) (hy : y ∈ S) : f x = f y := by
  have hdist := riemannian_edist_le_on_convex_source g hU hf hSU hS (C := 0)
    (fun p hp v => by simp [hd p hp]) hx hy
  have hzero : riemannianEDistOf g (f x) (f y) = 0 := by
    simpa only [ENNReal.coe_zero, _root_.MulZeroClass.zero_mul, nonpos_iff_eq_zero] using hdist
  let : _root_.Bundle.RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric 𝓘(ℝ, E) M
  exact edist_eq_zero.mp hzero

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.eq_of_mfderiv_eq_zero_on_convex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.eq_of_mfderiv_eq_zero_on_convex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.eq_of_mfderiv_eq_zero_on_convex ``Submission.DifferentialGeometry.Geometry.eq_of_mfderiv_eq_zero_on_convex

end DifferentialGeometry.Geometry
