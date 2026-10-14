import Submission.DifferentialGeometry.Geometry.Curvature.Algebraic.Tensor
import Submission.DifferentialGeometry.Geometry.Curvature.Metric.Defs
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetric

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature

open _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open scoped _root_.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M]

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
    [SigmaCompactSpace M] [T2Space M] in
noncomputable def algebraicCurvatureTensorProjection
    (g : SmoothRiemannianMetric I M) (x : M) :
    Tensor04At (I := I) (M := M) x →ₗ[Real]
      algebraicCurvatureTensorSubmodule (I := I) (M := M) x :=
  MetricFiberData.submoduleProjection
    (tensor0SMetricData (I := I) g x 4)
    (algebraicCurvatureTensorSubmodule (I := I) (M := M) x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.algebraicCurvatureTensorProjection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.algebraicCurvatureTensorProjection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.algebraicCurvatureTensorProjection ``Submission.DifferentialGeometry.Geometry.Curvature.algebraicCurvatureTensorProjection

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
    [SigmaCompactSpace M] [T2Space M] in
theorem algebraicCurvatureTensorProjection_inner
    (g : SmoothRiemannianMetric I M) (x : M)
    (A : Tensor04At (I := I) (M := M) x)
    (B : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    inner0S (I := I) g x 4
        (algebraicCurvatureTensorProjection (I := I) g x A :
          Tensor04At (I := I) (M := M) x) B =
      inner0S (I := I) g x 4 A B :=
  MetricFiberData.submoduleProjection_inner
    (tensor0SMetricData (I := I) g x 4)
    (algebraicCurvatureTensorSubmodule (I := I) (M := M) x) A B

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.algebraicCurvatureTensorProjection_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.algebraicCurvatureTensorProjection_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.algebraicCurvatureTensorProjection_inner ``Submission.DifferentialGeometry.Geometry.Curvature.algebraicCurvatureTensorProjection_inner

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
    [SigmaCompactSpace M] [T2Space M] in
@[simp]
theorem algebraicCurvatureTensorProjection_coe
    (g : SmoothRiemannianMetric I M) (x : M)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    algebraicCurvatureTensorProjection (I := I) g x
        (A : Tensor04At (I := I) (M := M) x) = A :=
  MetricFiberData.submoduleProjection_eq_self
    (tensor0SMetricData (I := I) g x 4)
    (algebraicCurvatureTensorSubmodule (I := I) (M := M) x) A A.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.algebraicCurvatureTensorProjection_coe then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.algebraicCurvatureTensorProjection_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.algebraicCurvatureTensorProjection_coe ``Submission.DifferentialGeometry.Geometry.Curvature.algebraicCurvatureTensorProjection_coe

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
    [SigmaCompactSpace M] [T2Space M] in
theorem algebraicCurvatureTensorProjection_eq_self
    (g : SmoothRiemannianMetric I M) (x : M)
    {A : Tensor04At (I := I) (M := M) x}
    (hA : A ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    (algebraicCurvatureTensorProjection (I := I) g x A :
      Tensor04At (I := I) (M := M) x) = A :=
  congrArg Subtype.val
    (MetricFiberData.submoduleProjection_eq_self
      (tensor0SMetricData (I := I) g x 4)
      (algebraicCurvatureTensorSubmodule (I := I) (M := M) x) A hA)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.algebraicCurvatureTensorProjection_eq_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.algebraicCurvatureTensorProjection_eq_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.algebraicCurvatureTensorProjection_eq_self ``Submission.DifferentialGeometry.Geometry.Curvature.algebraicCurvatureTensorProjection_eq_self

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
    [SigmaCompactSpace M] [T2Space M] in
theorem algebraicCurvatureTensorProjection_norm_le
    (g : SmoothRiemannianMetric I M) (x : M)
    (A : Tensor04At (I := I) (M := M) x) :
    tensor04FiberNorm (I := I) g x
        (algebraicCurvatureTensorProjection (I := I) g x A :
          Tensor04At (I := I) (M := M) x) ≤
      tensor04FiberNorm (I := I) g x A := by
  unfold tensor04FiberNorm tensor0SFiberNorm normSq0S
  exact Real.sqrt_le_sqrt
    (MetricFiberData.submoduleProjection_inner_self_le
      (tensor0SMetricData (I := I) g x 4)
      (algebraicCurvatureTensorSubmodule (I := I) (M := M) x) A)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.algebraicCurvatureTensorProjection_norm_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.algebraicCurvatureTensorProjection_norm_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.algebraicCurvatureTensorProjection_norm_le ``Submission.DifferentialGeometry.Geometry.Curvature.algebraicCurvatureTensorProjection_norm_le

omit [SigmaCompactSpace M] in
theorem metricRm04At_mem_algebraicCurvatureTensorSubmodule
    (g : SmoothRiemannianMetric I M) (x : M) :
    metricRm04At (I := I) (M := M) g x ∈
      algebraicCurvatureTensorSubmodule (I := I) (M := M) x := by
  let K := metricCurvatureSections (I := I) (M := M) g
  apply mem_algebraicCurvatureTensorSubmodule_iff_symmetries.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro X Y Z W
    simpa [metricRm04StandardAt_apply, metricRm04_apply] using
      (rm04InputSkewAt_of_leviCivita_realizes
        (I := I) g (metricRm04 (I := I) (M := M) g) K.rm04Realizes Y X Z W)
  · intro X Y Z W
    simpa [metricRm04StandardAt_apply, metricRm04_apply] using
      (rm04OutputSkewAt_of_leviCivita_realizes
        (I := I) g (metricRm04 (I := I) (M := M) g) K.rm04Realizes X Y Z W)
  · intro X Y Z W
    simpa [metricRm04StandardAt_apply, metricRm04_apply] using
      (firstBianchiAt_of_leviCivita_realizes
        (I := I) g (metricRm04 (I := I) (M := M) g) K.rm04Realizes X Y Z W)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.metricRm04At_mem_algebraicCurvatureTensorSubmodule then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.metricRm04At_mem_algebraicCurvatureTensorSubmodule"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.metricRm04At_mem_algebraicCurvatureTensorSubmodule ``Submission.DifferentialGeometry.Geometry.Curvature.metricRm04At_mem_algebraicCurvatureTensorSubmodule

omit [SigmaCompactSpace M] in
noncomputable def metricAlgebraicCurvatureTensorAt
    (g : SmoothRiemannianMetric I M) (x : M) :
    algebraicCurvatureTensorSubmodule (I := I) (M := M) x :=
  ⟨metricRm04At (I := I) (M := M) g x,
    metricRm04At_mem_algebraicCurvatureTensorSubmodule
      (I := I) (M := M) g x⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.metricAlgebraicCurvatureTensorAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.metricAlgebraicCurvatureTensorAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.metricAlgebraicCurvatureTensorAt ``Submission.DifferentialGeometry.Geometry.Curvature.metricAlgebraicCurvatureTensorAt

omit [SigmaCompactSpace M] in
@[simp]
theorem metricAlgebraicCurvatureTensorAt_coe
    (g : SmoothRiemannianMetric I M) (x : M) :
    (metricAlgebraicCurvatureTensorAt (I := I) (M := M) g x :
      Tensor04At (I := I) (M := M) x) =
        metricRm04At (I := I) (M := M) g x :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.metricAlgebraicCurvatureTensorAt_coe then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.metricAlgebraicCurvatureTensorAt_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.metricAlgebraicCurvatureTensorAt_coe ``Submission.DifferentialGeometry.Geometry.Curvature.metricAlgebraicCurvatureTensorAt_coe

end DifferentialGeometry.Geometry.Curvature
