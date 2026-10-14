import Submission.DifferentialGeometry.Geometry.Metric.UniversalCover.Metric
import Submission.DifferentialGeometry.Geometry.Metric.UniversalCover.Coordinates
import Submission.DifferentialGeometry.Geometry.Comparison.BonnetMyers.RicciBound
import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Ricci.Basic
import Submission.DifferentialGeometry.Geometry.Connection.LeviCivita.Defs
import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Sections
import Submission.DifferentialGeometry.Geometry.Curvature.Algebraic.CurvatureOperatorConeMetric
import Submission.DifferentialGeometry.Geometry.Connection.ChartBridge.Curvature.Ricci
import Submission.DifferentialGeometry.Geometry.Curvature.Coordinates.RiemannTensorBridge
import Submission.DifferentialGeometry.Geometry.Curvature.Metric.Sectional
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.LinearAlgebra.Trace
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Finite.Defs

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Tensor0SBundle

open _root_.Set _root_.Function _root_.Filter _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Topology _root_.ContDiff
open _root_.Submission.DifferentialGeometry (SmoothRiemannianMetric)

open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.BonnetMyers

noncomputable section

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Topology
namespace UniversalCover

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [LocallyPathConnectedSpace M]
  [DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace M]
  [Inhabited M] [PseudoEMetricSpace M] [SecondCountableTopology M]

omit [PseudoEMetricSpace M] in
omit [NeZero (Module.finrank ℝ E)]
  [SigmaCompactSpace M]
  [ConnectedSpace M]
  [SecondCountableTopology M] in
theorem metricRm_lifted
    (g : SmoothRiemannianMetric I M)
    (x' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
    (X Y Z W : E) :
    metricRm04StandardAt
        (I := I)
        (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
        (liftedMetric (I := I) g) x' X Y Z W =
      metricRm04StandardAt (I := I) (M := M) g (proj (X := M) x') X Y Z W := by
  classical
  have hRModel :
      DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv (I := I) x'
        (chartRiemannCLM
          (I := I)
          (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
          (liftedMetric (I := I) g) x'
          ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
            (I := I) x').symm X)
          ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
            (I := I) x').symm Y)
          ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
            (I := I) x').symm Z)) =
        DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
          (I := I) (proj (X := M) x')
          (chartRiemannCLM (I := I) (M := M) g (proj (X := M) x')
            ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
              (I := I) (proj (X := M) x')).symm X)
            ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
              (I := I) (proj (X := M) x')).symm Y)
            ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
              (I := I) (proj (X := M) x')).symm Z)) := by
    rw [chart_riemann_clm_model_apply, chart_riemann_clm_model_apply]
    refine Finset.sum_congr rfl ?_
    intro i _
    refine Finset.sum_congr rfl ?_
    intro j _
    refine Finset.sum_congr rfl ?_
    intro k _
    refine Finset.sum_congr rfl ?_
    intro l _
    rw [chartRiemannTensor_lifted (I := I) (M := M) g x' x'
      (mem_chart_source H x') i j k l]
  have hR :
      chartRiemannCLM
          (I := I)
          (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
          (liftedMetric (I := I) g) x'
          ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
            (I := I) x').symm X)
          ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
            (I := I) x').symm Y)
          ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
            (I := I) x').symm Z) =
        chartRiemannCLM (I := I) (M := M) g (proj (X := M) x')
          ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
            (I := I) (proj (X := M) x')).symm X)
          ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
            (I := I) (proj (X := M) x')).symm Y)
          ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
            (I := I) (proj (X := M) x')).symm Z) := by
    apply (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
      (I := I) x').injective
    rw [hRModel]
    simp only [DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv_apply,
      tangentSpaceModelContinuousLinearEquiv_apply]
    let R : TangentSpace I x' :=
      chartRiemannCLM (I := I) (M := M) g (proj (X := M) x')
        ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
          (I := I) (proj (X := M) x')).symm X)
        ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
          (I := I) (proj (X := M) x')).symm Y)
        ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
          (I := I) (proj (X := M) x')).symm Z)
    change R = DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
      (I := I) x' R
    rw [DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv_apply,
      tangentSpaceModelContinuousLinearEquiv_apply]
  have hMetric :
      metricRm04StandardAt
          (I := I)
          (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
          (liftedMetric (I := I) g) x'
          ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
            (I := I) x').symm X)
          ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
            (I := I) x').symm Y)
          ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
            (I := I) x').symm Z)
          ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
            (I := I) x').symm W) =
        metricRm04StandardAt (I := I) (M := M) g (proj (X := M) x')
          ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
            (I := I) (proj (X := M) x')).symm X)
          ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
            (I := I) (proj (X := M) x')).symm Y)
          ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
            (I := I) (proj (X := M) x')).symm Z)
          ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
            (I := I) (proj (X := M) x')).symm W) := by
    rw [metricRm04StandardAt_eq_chartRiemannCLM,
      metricRm04StandardAt_eq_chartRiemannCLM, hR]
    simp only [DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv_symm_apply]
    let R : TangentSpace I (proj (X := M) x') :=
      chartRiemannCLM (I := I) (M := M) g (proj (X := M) x') X Y Z
    change (g.inner (proj (X := M) x')) W R =
      (g.inner (proj (X := M) x')) W R
    rfl
  simpa only [DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv_symm_apply]
    using hMetric

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.metricRm_lifted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.metricRm_lifted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.metricRm_lifted ``Submission.DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.metricRm_lifted

omit [PseudoEMetricSpace M] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M]
    [ConnectedSpace M] [SecondCountableTopology M] in
theorem metricRm04At_liftedMetric_apply
    (g : SmoothRiemannianMetric I M)
    (x' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
    (v : Fin 4 → E) :
    metricRm04At (I := I) (liftedMetric (I := I) g) x' v =
      metricRm04At (I := I) g (proj x') v := by
  have hvUp : vec4 (I := I) (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
      (x := x') (v 0) (v 1) (v 2) (v 3) = v := by
    funext i
    fin_cases i <;> rfl
  have hvBase : vec4 (I := I) (M := M) (x := proj x')
      (v 0) (v 1) (v 2) (v 3) = v := by
    funext i
    fin_cases i <;> rfl
  calc
    _ = metricRm04StandardAt (I := I) (liftedMetric (I := I) g) x'
        (v 0) (v 1) (v 2) (v 3) :=
      (congrArg (fun w : Fin 4 → TangentSpace I x' =>
        metricRm04At (I := I) (liftedMetric (I := I) g) x' w) hvUp).symm
    _ = metricRm04StandardAt (I := I) g (proj x')
        (v 0) (v 1) (v 2) (v 3) := metricRm_lifted g x' (v 0) (v 1) (v 2) (v 3)
    _ = _ := congrArg (fun w : Fin 4 → TangentSpace I (proj x') =>
      metricRm04At (I := I) g (proj x') w) hvBase

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.metricRm04At_liftedMetric_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.metricRm04At_liftedMetric_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.metricRm04At_liftedMetric_apply ``Submission.DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.metricRm04At_liftedMetric_apply

omit [PseudoEMetricSpace M] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [ConnectedSpace M]
    [SecondCountableTopology M] in
theorem normSq0S_metricRm04At_liftedMetric
    (g : SmoothRiemannianMetric I M)
    (x' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :
    normSq0S (I := I) (liftedMetric (I := I) g) x' 4
        (metricRm04At (I := I) (liftedMetric (I := I) g) x') =
      normSq0S (I := I) g (proj x') 4
        (metricRm04At (I := I) g (proj x')) := by
  classical
  obtain ⟨b, hb⟩ := exists_orthonormal_basis (I := I) g (proj x')
  let b' : Module.Basis (Fin (Module.finrank ℝ (TangentSpace I (proj x')))) ℝ
      (TangentSpace I x') := by
    with_unfolding_all exact b
  have hb' : ∀ i j, (liftedMetric (I := I) g).inner x' (b' i) (b' j) =
      if i = j then (1 : ℝ) else 0 := by
    intro i j
    change g.inner (proj x') (b i) (b j) = _
    exact hb i j
  have hinv := metricInverseInBasis_identity_of_orthonormal (I := I) g b hb
  have hinv' := metricInverseInBasis_identity_of_orthonormal (I := I)
    (liftedMetric (I := I) g) b' hb'
  rw [normSq0S_identity_eq_sum_sq (I := I) (liftedMetric (I := I) g) x' 4 b' hinv',
    normSq0S_identity_eq_sum_sq (I := I) g (proj x') 4 b hinv]
  refine Finset.sum_congr rfl fun slots _ => ?_
  rw [component0S_apply, component0S_apply]
  change (metricRm04At (I := I) (liftedMetric (I := I) g) x'
      (fun a : Fin 4 => b (slots a))) ^ 2 =
    (metricRm04At (I := I) g (proj x') (fun a : Fin 4 => b (slots a))) ^ 2
  exact congrArg (fun a : ℝ => a ^ 2)
    (metricRm04At_liftedMetric_apply g x' (fun a => b (slots a)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.normSq0S_metricRm04At_liftedMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.normSq0S_metricRm04At_liftedMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.normSq0S_metricRm04At_liftedMetric ``Submission.DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.normSq0S_metricRm04At_liftedMetric

omit [PseudoEMetricSpace M] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M]
    [ConnectedSpace M] [SecondCountableTopology M] in
theorem metricAlgebraicCurvatureTensorAt_lifted_mem_curvatureOperatorNonnegativeCone_iff
    (g : SmoothRiemannianMetric I M)
    (x' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :
    metricAlgebraicCurvatureTensorAt (I := I) (liftedMetric (I := I) g) x' ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) ↔
      metricAlgebraicCurvatureTensorAt (I := I) g (proj x') ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) := by
  have heval (n : ℕ) (c : Fin n → ℝ) (v w : Fin n → E) :
      (∑ i, ∑ j, c i * c j * metricRm04StandardAt (I := I)
        (liftedMetric (I := I) g) x' (v i) (w i) (w j) (v j)) =
      ∑ i, ∑ j, c i * c j * metricRm04StandardAt (I := I)
        g (proj x') (v i) (w i) (w j) (v j) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact congrArg (fun a : ℝ => c i * c j * a)
      (metricRm_lifted (I := I) g x' (v i) (w i) (w j) (v j))
  rw [metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff,
    metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff]
  constructor
  · intro h n c v w
    exact (h n c v w).trans_eq (heval n c v w)
  · intro h n c v w
    exact (h n c v w).trans_eq (heval n c v w).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.metricAlgebraicCurvatureTensorAt_lifted_mem_curvatureOperatorNonnegativeCone_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.metricAlgebraicCurvatureTensorAt_lifted_mem_curvatureOperatorNonnegativeCone_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.metricAlgebraicCurvatureTensorAt_lifted_mem_curvatureOperatorNonnegativeCone_iff ``Submission.DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.metricAlgebraicCurvatureTensorAt_lifted_mem_curvatureOperatorNonnegativeCone_iff

omit [PseudoEMetricSpace M]
  [NeZero (Module.finrank ℝ E)]
  [ConnectedSpace M]
  [SecondCountableTopology M]
  [SigmaCompactSpace M] in
theorem metricRm_lift_one
    (g : SmoothRiemannianMetric I M) (c : Real) (hc : 0 < c)
    (hsec : ∀ x : M, ∀ X Y : TangentSpace I x,
      metricRm04StandardAt (I := I) (M := M) g x X Y Y X =
        c * (g.inner x X X * g.inner x Y Y -
          g.inner x X Y * g.inner x X Y)) :
    ∀ (x' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
        (X Y Z W : E),
      metricRm04StandardAt
          (I := I)
          (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
          (liftedMetric (I := I) (scaleMetric (I := I) c hc g))
          x' X Y Z W =
        (liftedMetric (I := I) (scaleMetric (I := I) c hc g)).inner x' Y Z *
            (liftedMetric (I := I) (scaleMetric (I := I) c hc g)).inner x' X W -
          (liftedMetric (I := I) (scaleMetric (I := I) c hc g)).inner x' X Z *
            (liftedMetric (I := I) (scaleMetric (I := I) c hc g)).inner x' Y W := by
  intro x' X Y Z W
  rw [metricRm_lifted]
  exact metricRm_scale_one (I := I) (M := M) g (proj (X := M) x') c hc
    (hsec (proj (X := M) x')) X Y Z W

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.metricRm_lift_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.metricRm_lift_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.metricRm_lift_one ``Submission.DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.metricRm_lift_one

omit [PseudoEMetricSpace M]
  [ConnectedSpace M]
  [SecondCountableTopology M]
  [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem riemannOp_lift_one
    (g : SmoothRiemannianMetric I M) (c : Real) (hc : 0 < c)
    (hsec : ∀ x : M, ∀ X Y : TangentSpace I x,
      metricRm04StandardAt (I := I) (M := M) g x X Y Y X =
        c * (g.inner x X X * g.inner x Y Y -
          g.inner x X Y * g.inner x X Y)) :
    ∀ (x' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
        (X Y Z : E),
      riemannOp
          (LeviCivita (I := I)
            (liftedMetric (I := I) (scaleMetric (I := I) c hc g)))
          x' X Y Z =
        (liftedMetric (I := I) (scaleMetric (I := I) c hc g)).inner x' Y Z • X -
          (liftedMetric (I := I) (scaleMetric (I := I) c hc g)).inner x' X Z • Y := by
  intro x' X Y Z
  have hRm : ∀ A B C D : E,
      metricRm04StandardAt
          (I := I)
          (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
          (liftedMetric (I := I) (scaleMetric (I := I) c hc g))
          x' A B C D =
        1 * ((liftedMetric (I := I) (scaleMetric (I := I) c hc g)).inner x' B C *
            (liftedMetric (I := I) (scaleMetric (I := I) c hc g)).inner x' A D -
          (liftedMetric (I := I) (scaleMetric (I := I) c hc g)).inner x' A C *
            (liftedMetric (I := I) (scaleMetric (I := I) c hc g)).inner x' B D) := by
    intro A B C D
    simpa only [one_mul] using
      metricRm_lift_one (I := I) (M := M) g c hc hsec x' A B C D
  let XT : TangentSpace I x' := X
  let YT : TangentSpace I x' := Y
  let ZT : TangentSpace I x' := Z
  change riemannOp
      (LeviCivita (I := I)
        (liftedMetric (I := I) (scaleMetric (I := I) c hc g)))
      x' XT YT ZT =
    (liftedMetric (I := I) (scaleMetric (I := I) c hc g)).inner x' YT ZT • XT -
      (liftedMetric (I := I) (scaleMetric (I := I) c hc g)).inner x' XT ZT • YT
  simpa only [one_smul] using
    riemannOp_of_rm
      (I := I)
      (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
      (liftedMetric (I := I) (scaleMetric (I := I) c hc g)) x' 1 hRm X Y Z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.riemannOp_lift_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.riemannOp_lift_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.riemannOp_lift_one ``Submission.DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.riemannOp_lift_one

omit [PseudoEMetricSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] [ConnectedSpace M] [SecondCountableTopology M] in
theorem riemannOp_lifted_natural (g : SmoothRiemannianMetric I M)
    (x' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
    (v' w' u' : E)
    (h_lifted : chartRiemannBasisIdentity
        (I := I)
        (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
        (liftedMetric (I := I) g) x')
    (h_base : chartRiemannBasisIdentity (I := I) (M := M) g (proj (X := M) x')) :
    riemannOp (LeviCivita (I := I) (liftedMetric (I := I) g)) x' v' w' u' =
      riemannOp (LeviCivita (I := I) g) (proj x') v' w' u' := by
  classical
  have hRModel :
      DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv (I := I) x'
        (chartRiemannCLM
          (I := I)
          (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
          (liftedMetric (I := I) g) x'
          ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
            (I := I) x').symm v')
          ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
            (I := I) x').symm w')
          ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
            (I := I) x').symm u')) =
        DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
          (I := I) (proj (X := M) x')
          (chartRiemannCLM (I := I) (M := M) g (proj (X := M) x')
            ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
              (I := I) (proj (X := M) x')).symm v')
            ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
              (I := I) (proj (X := M) x')).symm w')
            ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
              (I := I) (proj (X := M) x')).symm u')) := by
    rw [chart_riemann_clm_model_apply, chart_riemann_clm_model_apply]
    refine Finset.sum_congr rfl ?_
    intro i _
    refine Finset.sum_congr rfl ?_
    intro j _
    refine Finset.sum_congr rfl ?_
    intro k _
    refine Finset.sum_congr rfl ?_
    intro l _
    rw [chartRiemannTensor_lifted (I := I) (M := M) g x' x'
      (mem_chart_source H x') i j k l]
  have hModel :
      DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv (I := I) x'
        (riemannOp (LeviCivita (I := I) (liftedMetric (I := I) g)) x'
          ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
            (I := I) x').symm v')
          ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
            (I := I) x').symm w')
          ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
            (I := I) x').symm u')) =
        DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
          (I := I) (proj (X := M) x')
          (riemannOp (LeviCivita (I := I) g) (proj (X := M) x')
            ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
              (I := I) (proj (X := M) x')).symm v')
            ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
              (I := I) (proj (X := M) x')).symm w')
            ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
              (I := I) (proj (X := M) x')).symm u')) := by
    rw [riemannOp_eq_chartRiemannCLM_apply_of_basis_identity
          (I := I)
          (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
          (liftedMetric (I := I) g) x' h_lifted,
        riemannOp_eq_chartRiemannCLM_apply_of_basis_identity
          (I := I) (M := M) g (proj (X := M) x') h_base]
    exact hRModel
  have hR :
      riemannOp (LeviCivita (I := I) (liftedMetric (I := I) g)) x'
          ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
            (I := I) x').symm v')
          ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
            (I := I) x').symm w')
          ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
            (I := I) x').symm u') =
        riemannOp (LeviCivita (I := I) g) (proj (X := M) x')
          ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
            (I := I) (proj (X := M) x')).symm v')
          ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
            (I := I) (proj (X := M) x')).symm w')
          ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
            (I := I) (proj (X := M) x')).symm u') := by
    apply (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
      (I := I) x').injective
    rw [hModel]
    simp only [DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv_apply,
      tangentSpaceModelContinuousLinearEquiv_apply]
    let R : TangentSpace I x' :=
      riemannOp (LeviCivita (I := I) g) (proj (X := M) x')
        ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
          (I := I) (proj (X := M) x')).symm v')
        ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
          (I := I) (proj (X := M) x')).symm w')
        ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
          (I := I) (proj (X := M) x')).symm u')
    change R = DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv
      (I := I) x' R
    rw [DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv_apply,
      tangentSpaceModelContinuousLinearEquiv_apply]
  simpa only [DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv_symm_apply]
    using hR

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.riemannOp_lifted_natural then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.riemannOp_lifted_natural"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.riemannOp_lifted_natural ``Submission.DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.riemannOp_lifted_natural

omit [PseudoEMetricSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] [ConnectedSpace M] [SecondCountableTopology M] in
theorem ricciTensor_lifted_natural (g : SmoothRiemannianMetric I M)
    (x' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
    (v' w' : E)
    (h_lifted : chartRiemannBasisIdentity
        (I := I)
        (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
        (liftedMetric (I := I) g) x')
    (h_base : chartRiemannBasisIdentity (I := I) (M := M) g (proj (X := M) x')) :
    ricciTensor (I := I) (liftedMetric (I := I) g) x' v' w' =
      ricciTensor (I := I) g (proj x') v' w' := by
  classical
  rw [ricciTensor_apply_basisSum
        (I := I)
        (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
        (liftedMetric (I := I) g) x' v' w',
      ricciTensor_apply_basisSum (I := I) (M := M) g (proj (X := M) x') v' w']
  refine Finset.sum_congr rfl ?_
  intro i _
  have hRiem :
      riemannOp (cov := LeviCivita (I := I) (liftedMetric (I := I) g)) x'
          (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i) v' w' =
        riemannOp (cov := LeviCivita (I := I) g) (proj (X := M) x')
          (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i) v' w' :=
    riemannOp_lifted_natural (I := I) (M := M) g x'
      (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i) v' w' h_lifted h_base
  simp only [DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis_repr,
    DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis_apply,
    DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv_apply,
    DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv_symm_apply,
    tangentSpaceModelContinuousLinearEquiv_apply]
  rw [hRiem]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.ricciTensor_lifted_natural then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.ricciTensor_lifted_natural"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.ricciTensor_lifted_natural ``Submission.DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.ricciTensor_lifted_natural

omit [PseudoEMetricSpace M]
  [NeZero (Module.finrank ℝ E)]
  [ConnectedSpace M]
  [SecondCountableTopology M]
  [SigmaCompactSpace M] in
theorem metricScalarAt_lifted (g : SmoothRiemannianMetric I M)
    (x' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :
    metricScalarAt (I := I)
        (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
        (liftedMetric (I := I) g) x' =
      metricScalarAt (I := I) g (proj x') := by
  classical
  obtain ⟨bb, hbb⟩ :=
    DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (I := I) g (proj x')
  let eb : TangentSpace I (proj x') ≃L[ℝ] E :=
    tangentSpaceModelContinuousLinearEquiv (I := I) (proj x')
  let ex : TangentSpace I x' ≃L[ℝ] E :=
    tangentSpaceModelContinuousLinearEquiv (I := I) x'
  let e : TangentSpace I (proj x') ≃ₗ[ℝ] TangentSpace I x' :=
    eb.toLinearEquiv.trans ex.symm.toLinearEquiv
  let b1 : Module.Basis (Fin (Module.finrank ℝ (TangentSpace I (proj x')))) ℝ
      (TangentSpace I x') := bb.map e
  have hb0 : ∀ i j, g.inner (proj x') (bb i) (bb j) =
      if i = j then (1 : ℝ) else 0 := by
    intro i j
    exact hbb i j
  have hb1 : ∀ i j, (liftedMetric (I := I) g).inner x' (b1 i) (b1 j) =
      if i = j then (1 : ℝ) else 0 := by
    intro i j
    have h := liftedMetric_inner_eq (I := I) g x' (b1 i) (b1 j)
    rw [← h]
    change g.inner (proj x') (bb i) (bb j) = _
    exact hb0 i j
  have hi0 : MetricInverseInBasis (I := I) g (proj x') bb
      (identityInvMetric (Idx := Fin (Module.finrank ℝ (TangentSpace I (proj x'))))) :=
    metricInverseInBasis_of_orthonormal (I := I) g bb hb0
  have hi1 : MetricInverseInBasis (I := I)
      (liftedMetric (I := I) g) x' b1
      (identityInvMetric (Idx := Fin (Module.finrank ℝ (TangentSpace I (proj x'))))) :=
    metricInverseInBasis_of_orthonormal (I := I) (liftedMetric (I := I) g) b1 hb1
  rw [metricScalarAt_def, metricScalarAt_def,
    DifferentialGeometry.Geometry.Operator.metricTracePair0SAt_eq_sum_basis
      (I := I) (liftedMetric (I := I) g) b1
      (identityInvMetric (Idx := Fin (Module.finrank ℝ (TangentSpace I (proj x'))))) hi1
      (metricRicciAt (I := I)
        (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
        (liftedMetric (I := I) g) x'),
    DifferentialGeometry.Geometry.Operator.metricTracePair0SAt_eq_sum_basis
      (I := I) g bb
        (identityInvMetric (Idx := Fin (Module.finrank ℝ (TangentSpace I (proj x'))))) hi0
      (metricRicciAt (I := I) g (proj x'))]
  apply Finset.sum_congr rfl
  intro i hi
  have hric : metricRicciAt (I := I)
        (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
        (liftedMetric (I := I) g) x' (vec2 (b1 i) (b1 i)) =
      metricRicciAt (I := I) g (proj x') (vec2 (bb i) (bb i)) := by
    rw [metricRicciAt_apply_eq_ricciTensor, metricRicciAt_apply_eq_ricciTensor]
    change ricciTensor (I := I)
      (liftedMetric (I := I) g) x' (bb i) (bb i) =
      ricciTensor (I := I) g (proj x') (bb i) (bb i)
    simpa [b1, e, ex, eb, tangentSpaceModelContinuousLinearEquiv_apply] using
      ricciTensor_lifted_natural (I := I) (M := M) g x'
        (bb i) (bb i)
        (chartRiemannBasisIdentity_holds (I := I)
          (liftedMetric (I := I) g) x')
        (chartRiemannBasisIdentity_holds (I := I) g (proj x'))
  simp only [identityInvMetric, diagonalInvMetric]
  rw [Finset.sum_eq_single i]
  · simp [hric]
  · intro j _ hji
    simp [Ne.symm hji]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.metricScalarAt_lifted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.metricScalarAt_lifted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.metricScalarAt_lifted ``Submission.DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.metricScalarAt_lifted

omit [PseudoEMetricSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] [ConnectedSpace M] [SecondCountableTopology M] in
theorem ricciBoundedBelow_liftedMetric_of_base
    {g : SmoothRiemannianMetric I M} {κ : ℝ}
    (hRic : RicciBoundedBelow (I := I) g κ)
    (h_lifted_all : ∀ x' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M,
        chartRiemannBasisIdentity
          (I := I)
          (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
          (liftedMetric (I := I) g) x')
    (h_base_all : ∀ x : M, chartRiemannBasisIdentity (I := I) (M := M) g x) :
    RicciBoundedBelow (I := I) (liftedMetric (I := I) g) κ := by
  intro x' v'
  set x : M := proj x' with hx_def
  have h_inner :
      (liftedMetric (I := I) g).inner x' v' v' = g.inner x v' v' := by
    exact (liftedMetric_inner_eq (I := I) g x' v' v').symm
  have h_ric :
      ricciTensor (I := I) (liftedMetric (I := I) g) x' v' v' =
        ricciTensor (I := I) g x v' v' :=
    ricciTensor_lifted_natural (I := I) g x' v' v'
      (h_lifted_all x') (h_base_all (proj (X := M) x'))
  rw [h_inner, h_ric]
  exact hRic x v'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.ricciBoundedBelow_liftedMetric_of_base then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.ricciBoundedBelow_liftedMetric_of_base"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.ricciBoundedBelow_liftedMetric_of_base ``Submission.DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.ricciBoundedBelow_liftedMetric_of_base

end UniversalCover
end Topology
end Riemannian
end Geometry
end DifferentialGeometry

end
