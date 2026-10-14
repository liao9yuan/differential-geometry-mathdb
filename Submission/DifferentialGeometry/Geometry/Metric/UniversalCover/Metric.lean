import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Chart.Density
import Submission.DifferentialGeometry.Topology.Covering.Smooth.Manifold
import Submission.DifferentialGeometry.Geometry.Metric.UniversalCover.Smoothness
import Mathlib.Topology.VectorBundle.Riemannian

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Function _root_.Filter _root_.Bundle
open scoped _root_.Topology _root_.ContDiff
open _root_.Submission.DifferentialGeometry (SmoothRiemannianMetric)

noncomputable section

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Topology
namespace UniversalCover

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [LocallyPathConnectedSpace M]
  [DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace M]
  [Inhabited M]

noncomputable def liftedMetric (g : SmoothRiemannianMetric I M) :
    SmoothRiemannianMetric I
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) where
  inner x' := g.inner (proj x')
  symm x' v w := g.symm (proj x') v w
  pos x' v hv := g.pos (proj x') v hv
  isVonNBounded x' := g.isVonNBounded (proj x')
  contMDiff := uc_liftedMetric_contMDiff (I := I) (M := M) g

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.liftedMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.liftedMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.liftedMetric ``Submission.DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.liftedMetric

@[reducible] noncomputable def ucPseudoEMetricSpace
    (g : SmoothRiemannianMetric I
        (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M))
    [RegularSpace
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)] :
    PseudoEMetricSpace
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :=
  letI : _root_.Bundle.RiemannianBundle
      (fun (x : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) ↦
        TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E
      (fun (x : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) ↦
        TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩
  PseudoEMetricSpace.ofRiemannianMetric I _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.ucPseudoEMetricSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.ucPseudoEMetricSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.ucPseudoEMetricSpace ``Submission.DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.ucPseudoEMetricSpace

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
omit [ConnectedSpace M] in
theorem isRiemannianManifold
    (g : SmoothRiemannianMetric I
        (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M))
    [RegularSpace
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)] :
    letI : _root_.Bundle.RiemannianBundle
        (fun (x : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) ↦
          TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : PseudoEMetricSpace
        (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :=
      ucPseudoEMetricSpace (I := I) (M := M) g
    IsRiemannianManifold I
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) := by
  let : _root_.Bundle.RiemannianBundle
      (fun (x : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) ↦
        TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  let : PseudoEMetricSpace
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :=
    ucPseudoEMetricSpace (I := I) (M := M) g
  exact ⟨fun _ _ => rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.isRiemannianManifold then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.isRiemannianManifold"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.isRiemannianManifold ``Submission.DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.isRiemannianManifold

omit [SigmaCompactSpace M] [ConnectedSpace M] in
omit [I.Boundaryless] in
theorem uc_regularSpace (I : ModelWithCorners ℝ E H) :
    RegularSpace
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) := by
  have : LocallyCompactSpace M :=
    Manifold.locallyCompact_of_finiteDimensional (M := M) I
  infer_instance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.uc_regularSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.uc_regularSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.uc_regularSpace ``Submission.DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.uc_regularSpace

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
omit [ConnectedSpace M] in
theorem liftedMetric_inner_eq (g : SmoothRiemannianMetric I M)
    (x' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :
    ∀ (v w : E),
      g.inner (proj x') v w =
        (liftedMetric (I := I) g).inner x' v w :=
  fun _ _ => rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.liftedMetric_inner_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.liftedMetric_inner_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.liftedMetric_inner_eq ``Submission.DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.liftedMetric_inner_eq

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem liftedMetric_injective :
    Function.Injective (liftedMetric (I := I) (M := M)) := by
  let _ : PathConnectedSpace M := PathConnectedSpace.of_locallyPathConnectedSpace
  intro g h heq
  apply DifferentialGeometry.SmoothRiemannianMetric.ext_inner
  intro x v w
  let x' : UniversalCover M := ⟨x, ⟦PathConnectedSpace.somePath _root_.Inhabited.default x⟧⟩
  exact congrArg (fun k : DifferentialGeometry.SmoothRiemannianMetric I (UniversalCover M) =>
    k.inner x' v w) heq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.liftedMetric_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.liftedMetric_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.liftedMetric_injective ``Submission.DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.liftedMetric_injective

end UniversalCover
end Topology
end Riemannian
end Geometry
end DifferentialGeometry

end
