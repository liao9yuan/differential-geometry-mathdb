import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.ChartFamily
import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.CenterOfMass.NormalCoordinates.Hessian

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

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.TopologicalSpace
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.NNReal _root_.Topology

open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Exponential

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

def HasChartCenterOfMassSolution
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) Y)
    (hconn : letI : TopologicalSpace Y.M := Y.topology; ConnectedSpace Y.M)
    (p : Y.M) (c : NormalChartAt (I := I) Y p)
    {q : NNReal} {delta : Real}
    {ι : Type} [Fintype ι]
    (mu : ι → Real) (points : ι → Y.M)
    (join : Y.M → Y.M → Real → Y.M) (x : Y.M) (rad : Real)
    (hcm :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : IsManifold I 1 Y.M := IsManifold.of_le
        (I := I) (M := Y.M) (n := ∞) (by decide)
      letI : SigmaCompactSpace Y.M := Y.sigmaCompact
      letI : T2Space Y.M := Y.t2
      letI : ConnectedSpace Y.M := hconn
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      letI : TopologicalSpace.MetrizableSpace Y.M :=
        Manifold.metrizableSpace I Y.M
      letI : T3Space Y.M := inferInstance
      letI : _root_.Bundle.RiemannianBundle
          (fun y : Y.M ↦ TangentSpace I y) := Y.riemBundle (I := I)
      letI : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
        Y.riemInner (I := I)
      letI : IsContinuousRiemannianBundle E
          (fun y : Y.M ↦ TangentSpace I y) := Y.riemBundle_cont (I := I)
      letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
      letI : CompleteSpace Y.M :=
        MetricComplete.complete (I := I) Y hcomplete
      letI : MetricSpace Y.M :=
        HopfRinow.riemMetricSpace (I := I) (M := Y.M)
      CenterOfMassConditions (I := I) Y.metric mu points join x rad) : Prop :=
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : IsManifold I 1 Y.M := IsManifold.of_le
    (I := I) (M := Y.M) (n := ∞) (by decide)
  letI : SigmaCompactSpace Y.M := Y.sigmaCompact
  letI : T2Space Y.M := Y.t2
  letI : ConnectedSpace Y.M := hconn
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  letI : TopologicalSpace.MetrizableSpace Y.M :=
    Manifold.metrizableSpace I Y.M
  letI : T3Space Y.M := inferInstance
  letI : _root_.Bundle.RiemannianBundle
      (fun y : Y.M ↦ TangentSpace I y) := Y.riemBundle (I := I)
  letI : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
    Y.riemInner (I := I)
  letI : IsContinuousRiemannianBundle E
      (fun y : Y.M ↦ TangentSpace I y) := Y.riemBundle_cont (I := I)
  letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
  letI : CompleteSpace Y.M :=
    MetricComplete.complete (I := I) Y hcomplete
  letI : MetricSpace Y.M :=
    HopfRinow.riemMetricSpace (I := I) (M := Y.M)
  ∃ (hq : 0 < q)
      (e : OpenPartialHomeomorph (E × E) (E × E))
      (he : IsNormalDiag (I := I) Y hcomplete hconn p q delta e (c := c)),
    NormalDiagFence (I := I) Y p q e (c := c) ∧
      let B := IsNormalDiag.toBranch (I := I) Y hcomplete hconn p hq he
      let y := centerOfMass (I := I) Y.metric mu points join x rad hcm
      let z := c.inv y
      let xi : ι → E := fun i ↦ c.inv (points i)
      y ∈ c.restrictBall.target ∧
        HasCenterOfMassChartSolution (I := I) Y.metric (normal_enorm (I := I) Y)
          p c B z (mu, xi)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HasChartCenterOfMassSolution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HasChartCenterOfMassSolution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HasChartCenterOfMassSolution ``Submission.DifferentialGeometry.CheegerGromovCompactness.HasChartCenterOfMassSolution

end CheegerGromovCompactness
end DifferentialGeometry
