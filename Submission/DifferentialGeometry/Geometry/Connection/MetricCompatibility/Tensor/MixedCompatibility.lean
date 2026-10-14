import Submission.DifferentialGeometry.Geometry.Connection.MetricCompatibility.Tensor.CovariantCompatibility
import Submission.DifferentialGeometry.Geometry.Metric.PointwiseInner.MetricLowering

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators _root_.Matrix


namespace DifferentialGeometry
namespace Geometry
namespace Connection

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.TensorMetricLowering
open _root_.Submission.DifferentialGeometry.Tensor0SNabla

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [BoundarylessManifold I M]

def liftedTensorSection
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯) :
    Π y : M, Tensor0SSpace (r + s) I y :=
  fun y => Tensor0SSpace.ofModel
    (lowerAllUpperIndices (I := I) (M := M) g r s y (TensorRSSpace.toModel (S y)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.liftedTensorSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.liftedTensorSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.liftedTensorSection ``Submission.DifferentialGeometry.Geometry.Connection.liftedTensorSection

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [T2Space M]
    [BoundarylessManifold I M] in
@[simp]
lemma liftedTensorSection_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (y : M) :
    liftedTensorSection (I := I) (M := M) g r s S y =
      Tensor0SSpace.ofModel
        (lowerAllUpperIndices (I := I) (M := M) g r s y
          (TensorRSSpace.toModel (S y))) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.liftedTensorSection_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.liftedTensorSection_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.liftedTensorSection_apply ``Submission.DifferentialGeometry.Geometry.Connection.liftedTensorSection_apply

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [T2Space M]
    [BoundarylessManifold I M] in
lemma toModel_liftedTensorSection
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (y : M) :
    Tensor0SSpace.toModel (liftedTensorSection (I := I) (M := M) g r s S y) =
      lowerAllUpperIndices (I := I) (M := M) g r s y
        (TensorRSSpace.toModel (S y)) := by
  rw [liftedTensorSection_apply, Tensor0SSpace.toModel_ofModel]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.toModel_liftedTensorSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.toModel_liftedTensorSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.toModel_liftedTensorSection ``Submission.DifferentialGeometry.Geometry.Connection.toModel_liftedTensorSection

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [T2Space M]
    [BoundarylessManifold I M] in
lemma liftedTensorSection_contMDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (r + s) ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel (r + s) ℝ E)
        (E := fun z : M => Tensor0SSpace (r + s) I z) y
        (liftedTensorSection (I := I) (M := M) g r s S y)) :=
  contMDiff_lifted_section (I := I) (M := M) g r s S

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.liftedTensorSection_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.liftedTensorSection_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.liftedTensorSection_contMDiff ``Submission.DifferentialGeometry.Geometry.Connection.liftedTensorSection_contMDiff

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [T2Space M]
    [BoundarylessManifold I M] in
lemma liftedTensorSection_mdiffAt
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (x : M) :
    TensorSectionMDiffAt (I := I) (r + s)
      (liftedTensorSection (I := I) (M := M) g r s S) x :=
  ((liftedTensorSection_contMDiff (I := I) (M := M) g r s S) x).mdifferentiableAt
    (by simp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.liftedTensorSection_mdiffAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.liftedTensorSection_mdiffAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.liftedTensorSection_mdiffAt ``Submission.DifferentialGeometry.Geometry.Connection.liftedTensorSection_mdiffAt

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [T2Space M]
    [BoundarylessManifold I M] in
lemma tensorInnerPointwise_eq_liftedTensorSection_inner
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (W S : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (y : M) :
    tensorInnerPointwise (I := I) (M := M) g r s y
        (TensorRSSpace.toModel (W y)) (TensorRSSpace.toModel (S y)) =
      covariantTensorInnerPointwise (I := I) (M := M) (r + s) g y
        (Tensor0SSpace.toModel (liftedTensorSection (I := I) (M := M) g r s W y))
        (Tensor0SSpace.toModel
          (liftedTensorSection (I := I) (M := M) g r s S y)) := by
  rw [toModel_liftedTensorSection, toModel_liftedTensorSection]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensorInnerPointwise_eq_liftedTensorSection_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensorInnerPointwise_eq_liftedTensorSection_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensorInnerPointwise_eq_liftedTensorSection_inner ``Submission.DifferentialGeometry.Geometry.Connection.tensorInnerPointwise_eq_liftedTensorSection_inner

def loweredCovDerivAt
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (x : M) (v : TangentSpace I x) :
    Tensor0SSpace (r + s) I x :=
  tensor0SCovariantDerivative I M (r + s) (LeviCivita (I := I) g)
    (liftedTensorSection (I := I) (M := M) g r s S) x v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.loweredCovDerivAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.loweredCovDerivAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.loweredCovDerivAt ``Submission.DifferentialGeometry.Geometry.Connection.loweredCovDerivAt

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp]
lemma loweredCovDerivAt_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (x : M) (v : TangentSpace I x) :
    loweredCovDerivAt (I := I) (M := M) g r s S x v =
      tensor0SCovariantDerivative I M (r + s) (LeviCivita (I := I) g)
        (liftedTensorSection (I := I) (M := M) g r s S) x v := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.loweredCovDerivAt_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.loweredCovDerivAt_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.loweredCovDerivAt_def ``Submission.DifferentialGeometry.Geometry.Connection.loweredCovDerivAt_def

open _root_.Submission.DifferentialGeometry.Tensor0SNabla in
omit [CompleteSpace E] in
theorem tensorInnerPointwise_hasMFDerivAt_metricCompatible
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (W S : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (x : M) (v : TangentSpace I x) :
    mfderiv I 𝓘(ℝ, ℝ)
        (fun y : M => tensorInnerPointwise (I := I) (M := M) g r s y
          (TensorRSSpace.toModel (W y)) (TensorRSSpace.toModel (S y))) x v =
      covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
          (Tensor0SSpace.toModel
            (loweredCovDerivAt (I := I) (M := M) g r s W x v))
          (Tensor0SSpace.toModel
            (liftedTensorSection (I := I) (M := M) g r s S x))
        + covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
          (Tensor0SSpace.toModel
            (liftedTensorSection (I := I) (M := M) g r s W x))
          (Tensor0SSpace.toModel
            (loweredCovDerivAt (I := I) (M := M) g r s S x v)) := by
  have hfun : (fun y : M => tensorInnerPointwise (I := I) (M := M) g r s y
        (TensorRSSpace.toModel (W y)) (TensorRSSpace.toModel (S y))) =
      fun y : M => covariantTensorInnerPointwise (I := I) (M := M) (r + s) g y
        (Tensor0SSpace.toModel (liftedTensorSection (I := I) (M := M) g r s W y))
        (Tensor0SSpace.toModel
          (liftedTensorSection (I := I) (M := M) g r s S y)) := by
    funext y
    exact tensorInnerPointwise_eq_liftedTensorSection_inner
      (I := I) (M := M) g r s W S y
  rw [hfun]
  exact tensorInnerPointwise_0s_mfderiv_metricCompatible
    (I := I) (M := M) g (r + s)
    (liftedTensorSection (I := I) (M := M) g r s W)
    (liftedTensorSection (I := I) (M := M) g r s S)
    (liftedTensorSection_mdiffAt (I := I) (M := M) g r s W x)
    (liftedTensorSection_mdiffAt (I := I) (M := M) g r s S x) v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensorInnerPointwise_hasMFDerivAt_metricCompatible then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensorInnerPointwise_hasMFDerivAt_metricCompatible"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensorInnerPointwise_hasMFDerivAt_metricCompatible ``Submission.DifferentialGeometry.Geometry.Connection.tensorInnerPointwise_hasMFDerivAt_metricCompatible

open _root_.Submission.DifferentialGeometry.Tensor0SNabla in
omit [CompleteSpace E] in
theorem hasMFDerivAt_tensorInnerPointwise_metricCompatible
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (W S : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (x : M) :
    HasMFDerivAt I 𝓘(ℝ, ℝ)
      (fun y : M => tensorInnerPointwise (I := I) (M := M) g r s y
        (TensorRSSpace.toModel (W y)) (TensorRSSpace.toModel (S y))) x
      (tensorMetricCompatDiff (I := I) (M := M) g (r + s)
        (liftedTensorSection (I := I) (M := M) g r s W)
        (liftedTensorSection (I := I) (M := M) g r s S) x) := by
  have hfun : (fun y : M => tensorInnerPointwise (I := I) (M := M) g r s y
        (TensorRSSpace.toModel (W y)) (TensorRSSpace.toModel (S y))) =
      fun y : M => covariantTensorInnerPointwise (I := I) (M := M) (r + s) g y
        (Tensor0SSpace.toModel (liftedTensorSection (I := I) (M := M) g r s W y))
        (Tensor0SSpace.toModel
          (liftedTensorSection (I := I) (M := M) g r s S y)) := by
    funext y
    exact tensorInnerPointwise_eq_liftedTensorSection_inner
      (I := I) (M := M) g r s W S y
  rw [hfun]
  exact tensorInnerPointwise_0s_hasMFDerivAt_metricCompatible
    (I := I) (M := M) g (r + s)
    (liftedTensorSection (I := I) (M := M) g r s W)
    (liftedTensorSection (I := I) (M := M) g r s S)
    (liftedTensorSection_mdiffAt (I := I) (M := M) g r s W x)
    (liftedTensorSection_mdiffAt (I := I) (M := M) g r s S x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.hasMFDerivAt_tensorInnerPointwise_metricCompatible then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.hasMFDerivAt_tensorInnerPointwise_metricCompatible"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.hasMFDerivAt_tensorInnerPointwise_metricCompatible ``Submission.DifferentialGeometry.Geometry.Connection.hasMFDerivAt_tensorInnerPointwise_metricCompatible

end Connection
end Geometry
end DifferentialGeometry

end
