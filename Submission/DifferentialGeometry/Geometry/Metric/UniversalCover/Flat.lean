import Submission.DifferentialGeometry.Geometry.Exponential.RadialFlat
import Submission.DifferentialGeometry.Geometry.Metric.UniversalCover.Completeness
import Submission.DifferentialGeometry.Geometry.Metric.UniversalCover.Curvature

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  [ConnectedSpace M] [Nonempty M]

def HasEuclideanUniversalCover
    (g : SmoothRiemannianMetric I M) : Prop :=
  let _ : LocallyPathConnectedSpace H :=
    I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  let _ : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
  let _ : SemilocallySimplyConnectedSpace M :=
    manifold_semilocallySimplyConnectedSpace (I := I)
  let _ : Inhabited M := ⟨Classical.choice (inferInstance : Nonempty M)⟩
  let gtilde := liftedMetric (I := I) g
  ∃ (p : UniversalCover M)
      (F : Diffeomorph (modelWithCornersSelf Real E) I E (UniversalCover M) ∞),
    ∀ (z : E) (a b : TangentSpace (modelWithCornersSelf Real E) z),
      gtilde.inner (F z)
          (mfderiv (modelWithCornersSelf Real E) I F z a)
          (mfderiv (modelWithCornersSelf Real E) I F z b) =
        gtilde.inner p
          (show TangentSpace I p from (show E from a))
          (show TangentSpace I p from (show E from b))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.HasEuclideanUniversalCover then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.HasEuclideanUniversalCover"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.HasEuclideanUniversalCover ``Submission.DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.HasEuclideanUniversalCover

theorem hasEuclideanUniversalCover_of_riemannOp_eq_zero
    (g : SmoothRiemannianMetric I M)
    (hg : DifferentialGeometry.RiemannianMetricComplete (I := I) g)
    (hR : ∀ x (X Y Z : TangentSpace I x),
      riemannOp (LeviCivita (I := I) g) x X Y Z = 0) :
    HasEuclideanUniversalCover (I := I) (M := M) g := by
  let : LocallyPathConnectedSpace H :=
    I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  let : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
  let : SemilocallySimplyConnectedSpace M :=
    manifold_semilocallySimplyConnectedSpace (I := I)
  let : Inhabited M := ⟨Classical.choice (inferInstance : Nonempty M)⟩
  let : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
  let : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  let : RegularSpace (UniversalCover M) := uc_regularSpace (M := M) I
  let : LocallyPathConnectedSpace (UniversalCover M) :=
    ChartedSpace.locallyPathConnectedSpace H (UniversalCover M)
  let gtilde := liftedMetric (I := I) g
  let : PseudoEMetricSpace (UniversalCover M) :=
    ucPseudoEMetricSpace (I := I) (M := M) gtilde
  let (x : UniversalCover M) : NormedAddCommGroup (TangentSpace I x) :=
    (gtilde.toRiemannianMetric.toCore x).toNormedAddCommGroupOfTopology
      (gtilde.toRiemannianMetric.continuousAt x)
      (gtilde.toRiemannianMetric.isVonNBounded x)
  let (x : UniversalCover M) : InnerProductSpace Real (TangentSpace I x) :=
    .ofCoreOfTopology (gtilde.toRiemannianMetric.toCore x)
      (gtilde.toRiemannianMetric.continuousAt x)
      (gtilde.toRiemannianMetric.isVonNBounded x)
  let : _root_.Bundle.RiemannianBundle (fun x : UniversalCover M => TangentSpace I x) :=
    ⟨gtilde.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E
      (fun x : UniversalCover M => TangentSpace I x) :=
    ⟨gtilde.inner, gtilde.contMDiff.continuous, by intro x v w; rfl⟩
  let : IsRiemannianManifold I (UniversalCover M) :=
    isRiemannianManifold (I := I) (M := M) gtilde
  have hgtilde : DifferentialGeometry.RiemannianMetricComplete (I := I) gtilde :=
    liftedMetric_complete (I := I) (M := M) g hg
  let : CompleteSpace (UniversalCover M) := hgtilde.complete
  have hEnorm : IsMetricNorm (I := I) (M := UniversalCover M) gtilde := by
    intro x v
    exact tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) gtilde x v
  have hRtilde : ∀ x (X Y Z : TangentSpace I x),
      riemannOp (LeviCivita (I := I) gtilde) x X Y Z = 0 := by
    intro x X Y Z
    rw [riemannOp_lifted_natural (I := I) (M := M) g x X Y Z
      (chartRiemannBasisIdentity_holds (I := I) gtilde x)
      (chartRiemannBasisIdentity_holds (I := I) g (proj x))]
    exact hR (proj x) X Y Z
  let p : UniversalCover M :=
    Classical.choice (inferInstance : Nonempty (UniversalCover M))
  let F := Exponential.expMapIntrinsicDiffeomorphOfRiemannOpEqZero
    (I := I) gtilde hEnorm hRtilde p
  refine ⟨p, F, ?_⟩
  intro z a b
  have hF := Exponential.expMapIntrinsic_diffeomorph_isometry_of_riemannOp_eq_zero
    (I := I) gtilde hEnorm hRtilde p z a b
  change gtilde.inner (F z)
      (mfderiv (modelWithCornersSelf Real E) I F z a)
      (mfderiv (modelWithCornersSelf Real E) I F z b) = _
  rw [show gtilde.inner p
      (show TangentSpace I p from (show E from a))
      (show TangentSpace I p from (show E from b)) =
      _root_.Inner.inner Real
        (show TangentSpace I p from (show E from a))
        (show TangentSpace I p from (show E from b)) from rfl]
  simpa [F] using hF

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.hasEuclideanUniversalCover_of_riemannOp_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.hasEuclideanUniversalCover_of_riemannOp_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.hasEuclideanUniversalCover_of_riemannOp_eq_zero ``Submission.DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.hasEuclideanUniversalCover_of_riemannOp_eq_zero

end DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover
