import Submission.DifferentialGeometry.Geometry.Metric.UniformFiberInjectivity
import Submission.DifferentialGeometry.Geometry.Exponential.DiagonalExponential.LocalInverse

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Exponential
open scoped _root_.Topology _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M] [T2Space (TangentBundle I M)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (TangentSpace I : M → Type _)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (TangentSpace I : M → Type _)]



theorem exists_uniform_diagExp_injective (g : SmoothRiemannianMetric I M)
    (hg : IsMetricNorm (I := I) (M := M) g) :
    ∃ ε : ℝ, 0 < ε ∧ _root_.Set.InjOn (diagExp (I := I) g hg)
      {u : TangentBundle I M | Real.sqrt (g.inner u.proj u.2 u.2) ≤ ε} := by
  apply exists_uniform_fiber_injectivity g (diagExp (I := I) g hg)
  · intro u v huv
    exact congrArg Prod.fst huv
  · intro x
    let B := standardDiagonalInverseBranch (I := I) g hg x
    refine ⟨B.hom.source, B.hom.open_source, B.zero_mem, ?_⟩
    intro u hu v hv huv
    apply B.hom.injOn hu hv
    exact (B.hom_eq hu).trans (huv.trans (B.hom_eq hv).symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_uniform_diagExp_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_uniform_diagExp_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_uniform_diagExp_injective ``Submission.DifferentialGeometry.Geometry.exists_uniform_diagExp_injective

end DifferentialGeometry.Geometry
