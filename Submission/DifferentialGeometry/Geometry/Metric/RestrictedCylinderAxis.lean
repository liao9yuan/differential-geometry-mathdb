import Submission.DifferentialGeometry.Geometry.Metric.Cylinder
import Submission.DifferentialGeometry.Geometry.Curvature.Naturality.OpenSubtype

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff
open _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.Geometry.Metric

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def restrictedCylinderAxis (U : TopologicalSpace.Opens (M × ℝ)) (x : U) :
    TangentSpace (I.prod 𝓘(ℝ)) x := cylinderAxis (I := I) (x : M × ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.restrictedCylinderAxis then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.restrictedCylinderAxis"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.restrictedCylinderAxis ``Submission.DifferentialGeometry.Geometry.Metric.restrictedCylinderAxis

theorem contMDiff_restrictedCylinderAxis
    [FiniteDimensional ℝ E] (U : TopologicalSpace.Opens (M × ℝ)) :
    ContMDiff (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ)).tangent ∞
      (fun x : U ↦ (⟨x, restrictedCylinderAxis U x⟩ : TangentBundle (I.prod 𝓘(ℝ)) U)) := by
  let : CompleteSpace (E × ℝ) := FiniteDimensional.complete ℝ (E × ℝ)
  let Y : ContMDiffSection (I.prod 𝓘(ℝ)) (E × ℝ) ∞ (TangentSpace (I.prod 𝓘(ℝ)) : M × ℝ → Type _) :=
    ⟨cylinderAxis, contMDiff_cylinderAxis⟩
  have h := contMDiff_restrictOpen_section (I := I.prod 𝓘(ℝ)) U Y
  convert h using 1
  first
    | rfl
    | (funext x; rw [restrictOpenTangentField_apply]; rfl)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.contMDiff_restrictedCylinderAxis then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.contMDiff_restrictedCylinderAxis"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.contMDiff_restrictedCylinderAxis ``Submission.DifferentialGeometry.Geometry.Metric.contMDiff_restrictedCylinderAxis

theorem restrictedCylinderAxis_unit
    [FiniteDimensional ℝ E] [T2Space M]
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens (M × ℝ)) (x : U) :
    ((cylinderMetric g).restrictOpen U).inner x
      (restrictedCylinderAxis U x) (restrictedCylinderAxis U x) = 1 :=
  cylinderMetric_axis_unit g (x : M × ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.restrictedCylinderAxis_unit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.restrictedCylinderAxis_unit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.restrictedCylinderAxis_unit ``Submission.DifferentialGeometry.Geometry.Metric.restrictedCylinderAxis_unit

theorem restrictedCylinderAxis_inner
    [FiniteDimensional ℝ E] [T2Space M]
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens (M × ℝ))
    (x : U) (v : TangentSpace (I.prod 𝓘(ℝ)) x) :
    ((cylinderMetric g).restrictOpen U).inner x (restrictedCylinderAxis U x) v =
      mvfderiv (I.prod 𝓘(ℝ)) (fun y : U ↦ (y : M × ℝ).2) x v := by
  have h := mvfderiv_restrictOpen (I := I.prod 𝓘(ℝ)) U Prod.snd x v
    (contMDiff_snd.mdifferentiable (by decide : (∞ : WithTop ℕ∞) ≠ 0) (x : M × ℝ))
  exact (cylinderMetric_axis_inner g (x : M × ℝ) v).trans h.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.restrictedCylinderAxis_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.restrictedCylinderAxis_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.restrictedCylinderAxis_inner ``Submission.DifferentialGeometry.Geometry.Metric.restrictedCylinderAxis_inner

theorem gradFun_restricted_height_eq_restrictedCylinderAxis
    [FiniteDimensional ℝ E] [T2Space M]
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens (M × ℝ)) (x : U) :
    DifferentialGeometry.Geometry.Operator.gradFun ((cylinderMetric g).restrictOpen U)
      (fun y : U ↦ (y : M × ℝ).2) x = restrictedCylinderAxis U x := by
  apply DifferentialGeometry.Geometry.Operator.metricFlatLinear_injective
    ((cylinderMetric g).restrictOpen U) x
  ext v
  rw [DifferentialGeometry.Geometry.Operator.metricFlatLinear_apply,
    DifferentialGeometry.Geometry.Operator.metricFlatLinear_apply,
    DifferentialGeometry.Geometry.Operator.inner_gradFun,
    restrictedCylinderAxis_inner]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.gradFun_restricted_height_eq_restrictedCylinderAxis then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.gradFun_restricted_height_eq_restrictedCylinderAxis"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.gradFun_restricted_height_eq_restrictedCylinderAxis ``Submission.DifferentialGeometry.Geometry.Metric.gradFun_restricted_height_eq_restrictedCylinderAxis

end DifferentialGeometry.Geometry.Metric
