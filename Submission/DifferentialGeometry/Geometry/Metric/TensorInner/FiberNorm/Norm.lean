import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.FiberNorm.Defs
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.FiberNorm.NormBridge
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.FiberNorm.Inner
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.TensorRS.RiemannianBundle

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Elliptic

open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Tensor.TensorRSRiemannianBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

@[implicit_reducible]
noncomputable def riemannianFiberNormedAddCommGroup
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M) :
    NormedAddCommGroup (TensorRSSpace r s I b) := by
  letI : Bundle.RiemannianBundle (fun x : M => TensorRSSpace r s I x) :=
    tensorRSRiemannianBundle (I := I) (M := M) g r s
  let h : Bundle.RiemannianBundle (fun x : M => TensorRSSpace r s I x) := inferInstance
  exact (h.g.toCore b).toNormedAddCommGroupOfTopology
    (h.g.continuousAt b) (h.g.isVonNBounded b)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.riemannianFiberNormedAddCommGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.riemannianFiberNormedAddCommGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.riemannianFiberNormedAddCommGroup ``Submission.DifferentialGeometry.Analysis.Elliptic.riemannianFiberNormedAddCommGroup

noncomputable def riemannianFiberNorm
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M)
    (T : TensorRSSpace r s I b) : ℝ :=
  letI : NormedAddCommGroup (TensorRSSpace r s I b) :=
    riemannianFiberNormedAddCommGroup g r s b
  ‖T‖

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.riemannianFiberNorm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.riemannianFiberNorm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.riemannianFiberNorm ``Submission.DifferentialGeometry.Analysis.Elliptic.riemannianFiberNorm

theorem riemannianFiberNorm_nonneg (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M)
    (T : TensorRSSpace r s I b) :
    0 ≤ riemannianFiberNorm g r s b T := by
  let : NormedAddCommGroup (TensorRSSpace r s I b) :=
    riemannianFiberNormedAddCommGroup g r s b
  exact norm_nonneg T

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.riemannianFiberNorm_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.riemannianFiberNorm_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.riemannianFiberNorm_nonneg ``Submission.DifferentialGeometry.Analysis.Elliptic.riemannianFiberNorm_nonneg

theorem riemannianFiberNorm_eq_sqrt (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M)
    (T : TensorRSSpace r s I b) :
    riemannianFiberNorm g r s b T =
      Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g r s b T) := by
  let : Bundle.RiemannianBundle (fun x : M => TensorRSSpace r s I x) :=
    tensorRSRiemannianBundle (I := I) (M := M) g r s
  let : NormedAddCommGroup (TensorRSSpace r s I b) :=
    riemannianFiberNormedAddCommGroup g r s b
  rw [riemannianFiberNorm, norm_eq_sqrt_tensorInnerPointwise]
  rw [← riemannianFiberNormSq_eq_tensorInnerPointwise]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.riemannianFiberNorm_eq_sqrt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.riemannianFiberNorm_eq_sqrt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.riemannianFiberNorm_eq_sqrt ``Submission.DifferentialGeometry.Analysis.Elliptic.riemannianFiberNorm_eq_sqrt

theorem riemannianFiberNorm_sq (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M)
    (T : TensorRSSpace r s I b) :
    riemannianFiberNorm g r s b T ^ 2 = riemannianFiberNormSq (I := I) (M := M) g r s b T := by
  rw [riemannianFiberNorm_eq_sqrt]
  exact Real.sq_sqrt (riemannianFiberNormSq_nonneg (I := I) (M := M) g r s b T)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.riemannianFiberNorm_sq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.riemannianFiberNorm_sq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.riemannianFiberNorm_sq ``Submission.DifferentialGeometry.Analysis.Elliptic.riemannianFiberNorm_sq

theorem riemannianFiberNorm_eq_zero (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M)
    (T : TensorRSSpace r s I b) :
    riemannianFiberNorm g r s b T = 0 ↔ T = 0 := by
  let : NormedAddCommGroup (TensorRSSpace r s I b) :=
    riemannianFiberNormedAddCommGroup g r s b
  exact norm_eq_zero

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.riemannianFiberNorm_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.riemannianFiberNorm_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.riemannianFiberNorm_eq_zero ``Submission.DifferentialGeometry.Analysis.Elliptic.riemannianFiberNorm_eq_zero

theorem riemannianFiberNorm_add_le (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M)
    (S T : TensorRSSpace r s I b) :
    riemannianFiberNorm g r s b (S + T) ≤
      riemannianFiberNorm g r s b S + riemannianFiberNorm g r s b T := by
  let : NormedAddCommGroup (TensorRSSpace r s I b) :=
    riemannianFiberNormedAddCommGroup g r s b
  exact norm_add_le S T

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.riemannianFiberNorm_add_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.riemannianFiberNorm_add_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.riemannianFiberNorm_add_le ``Submission.DifferentialGeometry.Analysis.Elliptic.riemannianFiberNorm_add_le

theorem riemannianFiberNorm_smul (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M)
    (c : ℝ) (T : TensorRSSpace r s I b) :
    riemannianFiberNorm g r s b (c • T) = |c| * riemannianFiberNorm g r s b T := by
  let : Bundle.RiemannianBundle (fun x : M => TensorRSSpace r s I x) :=
    tensorRSRiemannianBundle (I := I) (M := M) g r s
  let h : Bundle.RiemannianBundle (fun x : M => TensorRSSpace r s I x) := inferInstance
  let : NormedAddCommGroup (TensorRSSpace r s I b) :=
    (h.g.toCore b).toNormedAddCommGroupOfTopology
      (h.g.continuousAt b) (h.g.isVonNBounded b)
  let : NormedSpace ℝ (TensorRSSpace r s I b) :=
    (h.g.toCore b).toNormedSpaceOfTopology
      (h.g.continuousAt b) (h.g.isVonNBounded b)
  exact norm_smul c T

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.riemannianFiberNorm_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.riemannianFiberNorm_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.riemannianFiberNorm_smul ``Submission.DifferentialGeometry.Analysis.Elliptic.riemannianFiberNorm_smul

theorem riemannianFiberNormSq_smul (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M)
    (c : ℝ) (T : TensorRSSpace r s I b) :
    riemannianFiberNormSq (I := I) (M := M) g r s b (c • T) =
      c ^ 2 * riemannianFiberNormSq (I := I) (M := M) g r s b T := by
  rw [← riemannianFiberNorm_sq, ← riemannianFiberNorm_sq, riemannianFiberNorm_smul,
    mul_pow, sq_abs]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.riemannianFiberNormSq_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.riemannianFiberNormSq_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.riemannianFiberNormSq_smul ``Submission.DifferentialGeometry.Analysis.Elliptic.riemannianFiberNormSq_smul

end Elliptic
end Analysis
end DifferentialGeometry
