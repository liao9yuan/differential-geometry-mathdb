import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Defs

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open _root_.Bundle
open scoped _root_.Manifold _root_.ContDiff _root_.Bundle

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]

@[reducible] def PointedRiemannianManifold.emetricSpace
    {I : ModelWithCorners Real E H}
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) : EMetricSpace Y.M := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : IsManifold I 1 Y.M :=
    IsManifold.of_le (I := I) (M := Y.M) (n := ∞)
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  letI : SigmaCompactSpace Y.M := Y.sigmaCompact
  letI : T2Space Y.M := Y.t2
  letI : TopologicalSpace.MetrizableSpace Y.M := Manifold.metrizableSpace I Y.M
  letI : T3Space Y.M := inferInstance
  letI : _root_.Bundle.RiemannianBundle (fun x : Y.M => TangentSpace I x) :=
    ⟨Y.metric.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : Y.M => TangentSpace I x) :=
    ⟨⟨Y.metric.inner, Y.metric.contMDiff.continuous, by intro x v w; rfl⟩⟩
  exact EMetricSpace.ofRiemannianMetric I Y.M

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.emetricSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.emetricSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.emetricSpace ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.emetricSpace

@[reducible] def PointedRiemannianManifold.riemBundle
    {I : ModelWithCorners Real E H}
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    Bundle.RiemannianBundle (fun x : Y.M => TangentSpace I x) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  exact ⟨Y.metric.toRiemannianMetric⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.riemBundle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.riemBundle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.riemBundle ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.riemBundle

@[reducible] def PointedRiemannianManifold.riemInner
    {I : ModelWithCorners Real E H}
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : Bundle.RiemannianBundle (fun x : Y.M => TangentSpace I x) :=
      Y.riemBundle (I := I)
    (x : Y.M) → InnerProductSpace Real (TangentSpace I x) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : Bundle.RiemannianBundle (fun x : Y.M => TangentSpace I x) :=
    Y.riemBundle (I := I)
  exact fun _ => inferInstance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.riemInner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.riemInner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.riemInner ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.riemInner

omit [FiniteDimensional Real E] [CompleteSpace E] in
theorem PointedRiemannianManifold.riemBundle_cont
    {I : ModelWithCorners Real E H}
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : Bundle.RiemannianBundle (fun x : Y.M => TangentSpace I x) :=
      Y.riemBundle (I := I)
    IsContinuousRiemannianBundle E (fun x : Y.M => TangentSpace I x) := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : Bundle.RiemannianBundle (fun x : Y.M => TangentSpace I x) :=
    Y.riemBundle (I := I)
  exact ⟨⟨Y.metric.inner, Y.metric.contMDiff.continuous, by intro x v w; rfl⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.riemBundle_cont then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.riemBundle_cont"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.riemBundle_cont ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.riemBundle_cont

end CheegerGromovCompactness
end DifferentialGeometry
