import Submission.DifferentialGeometry.Geometry.Metric.Sphere.Isometry.KillingHopf
import Submission.DifferentialGeometry.Geometry.Metric.Sphere.Round.BasisPoints
import Submission.DifferentialGeometry.Bundle.FiberBundleHausdorff
import Submission.DifferentialGeometry.Topology.Covering.SemilocallySimplyConnected
import Submission.DifferentialGeometry.Geometry.Metric.UniversalCover.Completeness
import Submission.DifferentialGeometry.Geometry.Metric.UniversalCover.Curvature

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Metric
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold

namespace DifferentialGeometry
namespace Geometry

variable {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [FiniteDimensional ℝ A]
variable {n : ℕ} [Fact (Module.finrank ℝ A = n + 1)] [NeZero n]

universe u

variable {Q : Type u} [TopologicalSpace Q]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) Q]
  [IsManifold (𝓡 n) ∞ Q]
  [T2Space Q] [SigmaCompactSpace Q]
  [CompactSpace Q] [ConnectedSpace Q] [Inhabited Q]
  [LocallyPathConnectedSpace Q]
  [DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace Q]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem sphereCover_one
    (hn : 1 < n)
    (g : SmoothRiemannianMetric (𝓡 n) Q)
    (c : ℝ) (hc : 0 < c)
    (hsec : ∀ x : Q, ∀ X Y : TangentSpace (𝓡 n) x,
      DifferentialGeometry.Geometry.Curvature.metricRm04StandardAt
          (I := 𝓡 n) (M := Q) g x X Y Y X =
        c * (g.inner x X X * g.inner x Y Y -
          g.inner x X Y * g.inner x X Y))
    (p q : _root_.Metric.sphere (0 : A) 1) (hpq : p ≠ q) (hqneg : q ≠ -p) :
    ∃ d : Diffeomorph (𝓡 n) (𝓡 n) (_root_.Metric.sphere (0 : A) 1)
        (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover Q) ∞,
      ∀ (x : _root_.Metric.sphere (0 : A) 1)
        (Y Z : TangentSpace (𝓡 n) x),
        (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.liftedMetric
            (I := 𝓡 n)
            (DifferentialGeometry.scaleMetric
              (I := 𝓡 n) c hc g)).inner (d x)
            (mfderiv (𝓡 n) (𝓡 n)
              (d : _root_.Metric.sphere (0 : A) 1 →
                DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover Q)
              x Y)
            (mfderiv (𝓡 n) (𝓡 n)
              (d : _root_.Metric.sphere (0 : A) 1 →
                DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover Q)
              x Z) =
          (roundMetric (E := A) (n := n)).inner x Y Z := by
  classical
  let g₁ : SmoothRiemannianMetric (𝓡 n) Q :=
    DifferentialGeometry.scaleMetric
      (I := 𝓡 n) c hc g
  have : LocallyCompactSpace Q :=
    Manifold.locallyCompact_of_finiteDimensional (M := Q) (𝓡 n)
  let : _root_.Bundle.RiemannianBundle
      (fun x : Q => TangentSpace (𝓡 n) x) :=
    ⟨g₁.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (fun x : Q => TangentSpace (𝓡 n) x) :=
    ⟨g₁.inner, g₁.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : PseudoEMetricSpace Q :=
    PseudoEMetricSpace.ofRiemannianMetric (𝓡 n) Q
  let : IsRiemannianManifold (𝓡 n) Q :=
    ⟨fun _ _ => rfl⟩
  let : CompleteSpace Q := inferInstance
  let gUC :
      SmoothRiemannianMetric (𝓡 n)
        (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover Q) :=
    DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.liftedMetric
      (I := 𝓡 n) g₁
  have :
      RegularSpace
        (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover Q) :=
    DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.uc_regularSpace
      (𝓡 n)
  let : _root_.Bundle.RiemannianBundle
      (fun x :
          DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover Q =>
        TangentSpace (𝓡 n) x) :=
    ⟨gUC.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (fun x :
          DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover Q =>
        TangentSpace (𝓡 n) x) :=
    ⟨gUC.inner, gUC.contMDiff.continuous, fun _ _ _ => rfl⟩
  let :
      PseudoEMetricSpace
        (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover Q) :=
    DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.ucPseudoEMetricSpace
      (I := 𝓡 n) (M := Q) gUC
  let :
      IsRiemannianManifold (𝓡 n)
        (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover Q) :=
    DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.isRiemannianManifold
      (I := 𝓡 n) (M := Q) gUC
  have hEnormBase :
      ∀ (x : Q) (v : TangentSpace (𝓡 n) x),
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g₁.inner x v v)) := by
    intro x v
    rw [← ofReal_norm, norm_eq_sqrt_real_inner]
    rfl
  have hEnormCover :
      ∀ (x :
          DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover Q)
        (v : TangentSpace (𝓡 n) x),
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (gUC.inner x v v)) := by
    intro x v
    rw [← ofReal_norm, norm_eq_sqrt_real_inner]
    rfl
  let :
      CompleteSpace
        (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover Q) :=
    DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.completeSpace_of_complete
      (I := 𝓡 n) (M := Q) g₁ hEnormBase hEnormCover
  let :
      LocallyPathConnectedSpace
        (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover Q) :=
    ChartedSpace.locallyPathConnectedSpace
      (EuclideanSpace ℝ (Fin n))
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover Q)
  let : _root_.Bundle.RiemannianBundle
      (fun x : _root_.Metric.sphere (0 : A) 1 => TangentSpace (𝓡 n) x) :=
    roundBundle (A := A) (n := n)
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (fun x : _root_.Metric.sphere (0 : A) 1 => TangentSpace (𝓡 n) x) :=
    ⟨(roundMetric (E := A) (n := n)).inner,
      (roundMetric (E := A) (n := n)).contMDiff.continuous,
      fun _ _ _ => rfl⟩
  let spherePseudo : PseudoEMetricSpace (_root_.Metric.sphere (0 : A) 1) :=
    PseudoEMetricSpace.ofRiemannianMetric (𝓡 n) (_root_.Metric.sphere (0 : A) 1)
  let : IsRiemannianManifold (𝓡 n) (_root_.Metric.sphere (0 : A) 1) :=
    ⟨fun _ _ => rfl⟩
  let : @CompleteSpace (_root_.Metric.sphere (0 : A) 1)
      (@PseudoEMetricSpace.toUniformSpace _ spherePseudo) :=
    @complete_of_compact (_root_.Metric.sphere (0 : A) 1)
      (@PseudoEMetricSpace.toUniformSpace _ spherePseudo) (by
        infer_instance)
  have hRound :
      ∀ (x : _root_.Metric.sphere (0 : A) 1) (w : TangentSpace (𝓡 n) x),
        ‖w‖ₑ = ENNReal.ofReal
          (Real.sqrt ((roundMetric (E := A) (n := n)).inner x w w)) := by
    simpa only using (round_enorm (A := A) (n := n))
  refine sphere_diffeo_one
    (A := A) (n := n) (J := 𝓡 n)
    (N := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover Q)
    hn hRound gUC hEnormCover ?_ p q hpq hqneg
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.basePoint
      (X := Q))
  change ∀ (x' :
      DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover Q)
      (X Y Z : EuclideanSpace ℝ (Fin n)), _
  intro x' X Y Z
  exact
    DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.riemannOp_lift_one
      (I := 𝓡 n) (M := Q) g c hc hsec x' X Y Z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.sphereCover_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.sphereCover_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.sphereCover_one ``Submission.DifferentialGeometry.Geometry.sphereCover_one

end Geometry
end DifferentialGeometry
