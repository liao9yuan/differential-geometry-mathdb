import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.RicciNorm
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Scalar.Basic
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Scalar.TraceAlgebra
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Scalar.RmTrace
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Scalar.EvolutionEquation
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.Equation.Norm
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Preservation.Pinching.TraceFreeRicci.Norm
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Regularity
import Submission.DifferentialGeometry.Geometry.Curvature.Bochner.Tensor.Basic
import Submission.DifferentialGeometry.Geometry.Curvature.DimensionThree.Reconstruction.RicciControlsRiemann
import Submission.DifferentialGeometry.Geometry.Curvature.DimensionThree.Algebra.Pinching
import Submission.DifferentialGeometry.Geometry.Metric.RiemannianMetricTensor
import Submission.DifferentialGeometry.Geometry.Connection.MetricCompatibility.Tensor.Metric

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

attribute [local instance] Fintype.ofFinite Classical.propDecidable

open scoped _root_.Manifold _root_.ContDiff _root_.BigOperators
open _root_.Submission.DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M]

abbrev Tensor02Fam : Type _ :=
  Real -> (x : M) ->
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.PDE.RicciFlow.Tensor02Fam with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Tensor02Fam"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Tensor02Fam ``Submission.DifferentialGeometry.PDE.RicciFlow.Tensor02Fam

def metric02
    (G : Real -> SmoothRiemannianMetric I M) :
    Tensor02Fam (E := E) (H := H) (I := I) (M := M) :=
  fun t x => Tensor0SBundle.metricTensorField (I := I) (G t) x

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.PDE.RicciFlow.metric02 with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.metric02"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.metric02 ``Submission.DifferentialGeometry.PDE.RicciFlow.metric02

@[simp]
theorem metric02_apply
    (G : Real -> SmoothRiemannianMetric I M)
    (t : Real) (x : M) (v : Fin 2 -> TangentSpace I x) :
    metric02 (I := I) G t x v = (G t).inner x (v 0) (v 1) := by
  simp [metric02]

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.PDE.RicciFlow.metric02_apply with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.metric02_apply"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.metric02_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.metric02_apply

def traceFreeRicciTensor
    (G : Real -> SmoothRiemannianMetric I M)
    (Ric : Tensor02Fam (E := E) (H := H) (I := I) (M := M))
    (scalar : Real -> M -> Real) :
    Tensor02Fam (E := E) (H := H) (I := I) (M := M) :=
  fun t x =>
    Ric t x -
      (((1 : Real) / 3) * scalar t x) •
        metric02 (I := I) G t x

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.PDE.RicciFlow.traceFreeRicciTensor with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.traceFreeRicciTensor"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.traceFreeRicciTensor ``Submission.DifferentialGeometry.PDE.RicciFlow.traceFreeRicciTensor

@[simp]
theorem trace_free_ricci_apply
    (G : Real -> SmoothRiemannianMetric I M)
    (Ric : Tensor02Fam (E := E) (H := H) (I := I) (M := M))
    (scalar : Real -> M -> Real)
    (t : Real) (x : M) (v : Fin 2 -> TangentSpace I x) :
    traceFreeRicciTensor (I := I) G Ric scalar t x v =
      Ric t x v - (((1 : Real) / 3) * scalar t x) *
        (G t).inner x (v 0) (v 1) := by
  unfold traceFreeRicciTensor
  calc
    (Ric t x - (((1 : Real) / 3) * scalar t x) • metric02 (I := I) G t x) v =
        Ric t x v -
          ((((1 : Real) / 3) * scalar t x) • metric02 (I := I) G t x) v :=
      Tensor0SSpace.sub_apply 2 x _ _ v
    _ = _ := by
      rw [Tensor0SSpace.smul_apply, metric02_apply]
      simp only [smul_eq_mul]

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.PDE.RicciFlow.trace_free_ricci_apply with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.trace_free_ricci_apply"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.trace_free_ricci_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.trace_free_ricci_apply

abbrev traceFreeRicciNormSqAt (scalar ricciNormSq : Real) : Real :=
  traceFreeRicciNormSqAtOf scalar ricciNormSq

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.PDE.RicciFlow.traceFreeRicciNormSqAt with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.traceFreeRicciNormSqAt"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.traceFreeRicciNormSqAt ``Submission.DifferentialGeometry.PDE.RicciFlow.traceFreeRicciNormSqAt

abbrev traceFreeRicciNormSq
    (scalar ricciNormSq : Real -> M -> Real) : Real -> M -> Real :=
  traceFreeRicciNormSqOf scalar ricciNormSq

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.PDE.RicciFlow.traceFreeRicciNormSq with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.traceFreeRicciNormSq"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.traceFreeRicciNormSq ``Submission.DifferentialGeometry.PDE.RicciFlow.traceFreeRicciNormSq

omit [TopologicalSpace M] in
theorem trace_free_ricci_norm_sq_compat
    (scalar ricciNormSq : Real -> M -> Real) (t : Real) (x : M) :
    traceFreeRicciNormSq scalar ricciNormSq t x =
      traceFreeRicciNormSqOf scalar ricciNormSq t x := rfl

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.PDE.RicciFlow.trace_free_ricci_norm_sq_compat with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.trace_free_ricci_norm_sq_compat"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.trace_free_ricci_norm_sq_compat ``Submission.DifferentialGeometry.PDE.RicciFlow.trace_free_ricci_norm_sq_compat

def pinchP
    (scalar ricciNormSq : Real -> M -> Real) (epsilon : Real)
    (t : Real) (x : M) : Real :=
  traceFreeRicciNormSq scalar ricciNormSq t x / Real.rpow (scalar t x) (2 - epsilon)

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.PDE.RicciFlow.pinchP with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.pinchP"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.pinchP ``Submission.DifferentialGeometry.PDE.RicciFlow.pinchP

def cubicQAt (scalar ricciNormSq ricciTraceCube : Real) : Real :=
  2 * ricciNormSq ^ 2 + scalar ^ 4 -
    5 * scalar ^ 2 * ricciNormSq + 4 * scalar * ricciTraceCube

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.PDE.RicciFlow.cubicQAt with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.cubicQAt"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.cubicQAt ``Submission.DifferentialGeometry.PDE.RicciFlow.cubicQAt

def cubicQ
    (scalar ricciNormSq ricciTraceCube : Real -> M -> Real)
    (t : Real) (x : M) : Real :=
  cubicQAt (scalar t x) (ricciNormSq t x) (ricciTraceCube t x)

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.PDE.RicciFlow.cubicQ with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.cubicQ"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.cubicQ ``Submission.DifferentialGeometry.PDE.RicciFlow.cubicQ

theorem cubicQ_eigen (l1 l2 l3 : Real) :
    cubicQAt
        (DifferentialGeometry.Geometry.Curvature.ricciEigenScalar3 l1 l2 l3)
        (DifferentialGeometry.Geometry.Curvature.ricciEigenNormSq3 l1 l2 l3)
        (DifferentialGeometry.Geometry.Curvature.ricciEigenTraceCube3 l1 l2 l3) =
      DifferentialGeometry.Geometry.Curvature.hamiltonCubicQ3 l1 l2 l3 := by
  unfold cubicQAt DifferentialGeometry.Geometry.Curvature.hamiltonCubicQ3
  ring

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.PDE.RicciFlow.cubicQ_eigen with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.cubicQ_eigen"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.cubicQ_eigen ``Submission.DifferentialGeometry.PDE.RicciFlow.cubicQ_eigen

theorem trace_free_ricci_norm_sq_eigenvalues (l1 l2 l3 : Real) :
    traceFreeRicciNormSqAt
        (DifferentialGeometry.Geometry.Curvature.ricciEigenScalar3 l1 l2 l3)
        (DifferentialGeometry.Geometry.Curvature.ricciEigenNormSq3 l1 l2 l3) =
      DifferentialGeometry.Geometry.Curvature.tracefreeRicciEigenNormSq3 l1 l2 l3 := by
  unfold traceFreeRicciNormSqAt traceFreeRicciNormSqAtOf
    DifferentialGeometry.Geometry.Curvature.tracefreeRicciEigenNormSq3
    DifferentialGeometry.Geometry.Curvature.ricciEigenPairwiseGapSq3
    DifferentialGeometry.Geometry.Curvature.ricciEigenScalar3
    DifferentialGeometry.Geometry.Curvature.ricciEigenNormSq3
  ring

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.PDE.RicciFlow.trace_free_ricci_norm_sq_eigenvalues with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.trace_free_ricci_norm_sq_eigenvalues"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.trace_free_ricci_norm_sq_eigenvalues ``Submission.DifferentialGeometry.PDE.RicciFlow.trace_free_ricci_norm_sq_eigenvalues

def EigenPinchCtxOn
    (l1 l2 l3 : Real -> M -> Real) (delta : Real) : Prop :=
  forall t x, DifferentialGeometry.Geometry.Curvature.PinchEigen3 (l1 t x) (l2 t x) (l3 t x) delta

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.PDE.RicciFlow.EigenPinchCtxOn with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.EigenPinchCtxOn"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.EigenPinchCtxOn ``Submission.DifferentialGeometry.PDE.RicciFlow.EigenPinchCtxOn

theorem cubicQ_pinch
    {l1 l2 l3 delta epsilon : Real}
    (hctx : DifferentialGeometry.Geometry.Curvature.PinchEigen3 l1 l2 l3 delta)
    (hepsilon : epsilon <= 2 * delta ^ 2) :
    0 <=
      cubicQAt
          (DifferentialGeometry.Geometry.Curvature.ricciEigenScalar3 l1 l2 l3)
          (DifferentialGeometry.Geometry.Curvature.ricciEigenNormSq3 l1 l2 l3)
          (DifferentialGeometry.Geometry.Curvature.ricciEigenTraceCube3 l1 l2 l3) -
        epsilon * DifferentialGeometry.Geometry.Curvature.ricciEigenNormSq3 l1 l2 l3 *
          traceFreeRicciNormSqAt
            (DifferentialGeometry.Geometry.Curvature.ricciEigenScalar3 l1 l2 l3)
            (DifferentialGeometry.Geometry.Curvature.ricciEigenNormSq3 l1 l2 l3) := by
  simpa [cubicQ_eigen, trace_free_ricci_norm_sq_eigenvalues] using
    DifferentialGeometry.Geometry.Curvature.PinchEigen3.q_sub_nonneg hctx hepsilon

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.PDE.RicciFlow.cubicQ_pinch with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.cubicQ_pinch"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.cubicQ_pinch ``Submission.DifferentialGeometry.PDE.RicciFlow.cubicQ_pinch

omit [TopologicalSpace M] in
theorem cubicQ_pinchOn
    (l1 l2 l3 : Real -> M -> Real) {delta epsilon : Real}
    (hctx : EigenPinchCtxOn (M := M) l1 l2 l3 delta)
    (hepsilon : epsilon <= 2 * delta ^ 2) :
    forall t x,
      0 <=
        cubicQAt
            (DifferentialGeometry.Geometry.Curvature.ricciEigenScalar3 (l1 t x) (l2 t x) (l3 t x))
            (DifferentialGeometry.Geometry.Curvature.ricciEigenNormSq3 (l1 t x) (l2 t x) (l3 t x))
            (DifferentialGeometry.Geometry.Curvature.ricciEigenTraceCube3 (l1 t x) (l2 t x)
              (l3 t x)) -
          epsilon * DifferentialGeometry.Geometry.Curvature.ricciEigenNormSq3 (l1 t x) (l2 t x)
            (l3 t x) *
            traceFreeRicciNormSqAt
              (DifferentialGeometry.Geometry.Curvature.ricciEigenScalar3 (l1 t x) (l2 t x)
                (l3 t x))
              (DifferentialGeometry.Geometry.Curvature.ricciEigenNormSq3 (l1 t x) (l2 t x)
                (l3 t x)) := by
  intro t x
  exact cubicQ_pinch (hctx t x) hepsilon

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.PDE.RicciFlow.cubicQ_pinchOn with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.cubicQ_pinchOn"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.cubicQ_pinchOn ``Submission.DifferentialGeometry.PDE.RicciFlow.cubicQ_pinchOn

def ricciReact3 (l1 l2 l3 : Real) : Real :=
  l1 * l2 * (l1 + l2 - l3) +
    l1 * l3 * (l1 + l3 - l2) +
      l2 * l3 * (l2 + l3 - l1)

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.PDE.RicciFlow.ricciReact3 with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ricciReact3"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ricciReact3 ``Submission.DifferentialGeometry.PDE.RicciFlow.ricciReact3

theorem react3_diag (l1 l2 l3 : Real) :
    (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
      DifferentialGeometry.Geometry.Curvature.standardRmDiag3 l1 l2 l3 i k j l *
        DifferentialGeometry.Geometry.Curvature.ricciDiag3 l1 l2 l3 i j *
          DifferentialGeometry.Geometry.Curvature.ricciDiag3 l1 l2 l3 k l) =
      ricciReact3 l1 l2 l3 := by
  unfold ricciReact3 DifferentialGeometry.Geometry.Curvature.standardRmDiag3
    DifferentialGeometry.Geometry.Curvature.ricciDiag3
    DifferentialGeometry.Geometry.Curvature.ricciEigenScalar3
      DifferentialGeometry.Geometry.Curvature.delta3
  simp [Fin.sum_univ_three]
  ring

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.PDE.RicciFlow.react3_diag with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.react3_diag"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.react3_diag ``Submission.DifferentialGeometry.PDE.RicciFlow.react3_diag

theorem curv3_diag_eq (l1 l2 l3 : Real) :
    (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
      DifferentialGeometry.Geometry.Curvature.standardRmDiag3 l1 l2 l3 i k j l *
        DifferentialGeometry.Geometry.Curvature.ricciDiag3 l1 l2 l3 i j *
          DifferentialGeometry.Geometry.Curvature.ricciDiag3 l1 l2 l3 k l) =
      ricciReact3 l1 l2 l3 := by
  unfold ricciReact3 DifferentialGeometry.Geometry.Curvature.standardRmDiag3
    DifferentialGeometry.Geometry.Curvature.ricciDiag3
    DifferentialGeometry.Geometry.Curvature.ricciEigenScalar3
      DifferentialGeometry.Geometry.Curvature.delta3
  simp [Fin.sum_univ_three]
  ring

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.PDE.RicciFlow.curv3_diag_eq with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.curv3_diag_eq"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.curv3_diag_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.curv3_diag_eq

theorem curv3_neg_eq (l1 l2 l3 : Real) :
    (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
      DifferentialGeometry.Geometry.Curvature.standardRmDiag3 (-l1) (-l2) (-l3) i k j l *
        DifferentialGeometry.Geometry.Curvature.ricciDiag3 l1 l2 l3 i j *
          DifferentialGeometry.Geometry.Curvature.ricciDiag3 l1 l2 l3 k l) =
      -ricciReact3 l1 l2 l3 := by
  unfold ricciReact3 DifferentialGeometry.Geometry.Curvature.standardRmDiag3
    DifferentialGeometry.Geometry.Curvature.ricciDiag3
    DifferentialGeometry.Geometry.Curvature.ricciEigenScalar3
      DifferentialGeometry.Geometry.Curvature.delta3
  simp [Fin.sum_univ_three]
  ring

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.PDE.RicciFlow.curv3_neg_eq with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.curv3_neg_eq"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.curv3_neg_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.curv3_neg_eq

def diagReact3
    (l1 l2 l3 : Real -> M -> Real) : Real -> M -> Real :=
  fun t x =>
    ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
      DifferentialGeometry.Geometry.Curvature.standardRmDiag3 (l1 t x) (l2 t x) (l3 t x) i k j l *
        DifferentialGeometry.Geometry.Curvature.ricciDiag3 (l1 t x) (l2 t x) (l3 t x) i j *
          DifferentialGeometry.Geometry.Curvature.ricciDiag3 (l1 t x) (l2 t x) (l3 t x) k l

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.PDE.RicciFlow.diagReact3 with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.diagReact3"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.diagReact3 ``Submission.DifferentialGeometry.PDE.RicciFlow.diagReact3

omit [TopologicalSpace M] in
@[simp]
theorem diagReact3_apply
    (l1 l2 l3 : Real -> M -> Real) (t : Real) (x : M) :
    diagReact3 (M := M) l1 l2 l3 t x =
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
        DifferentialGeometry.Geometry.Curvature.standardRmDiag3 (l1 t x) (l2 t x) (l3 t x) i k j l *
          DifferentialGeometry.Geometry.Curvature.ricciDiag3 (l1 t x) (l2 t x) (l3 t x) i j *
            DifferentialGeometry.Geometry.Curvature.ricciDiag3 (l1 t x) (l2 t x) (l3 t x) k l := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.PDE.RicciFlow.diagReact3_apply with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.diagReact3_apply"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.diagReact3_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.diagReact3_apply

omit [TopologicalSpace M] in
theorem diagReact3_eq
    (l1 l2 l3 : Real -> M -> Real) (t : Real) (x : M) :
    diagReact3 (M := M) l1 l2 l3 t x =
      ricciReact3 (l1 t x) (l2 t x) (l3 t x) := by
  exact react3_diag (l1 t x) (l2 t x) (l3 t x)

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.PDE.RicciFlow.diagReact3_eq with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.diagReact3_eq"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.diagReact3_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.diagReact3_eq

theorem trace_free_ricci_reaction_relation_eigenvalues (l1 l2 l3 : Real)
    (hR : DifferentialGeometry.Geometry.Curvature.ricciEigenScalar3 l1 l2 l3 ≠ 0) :
    4 * ricciReact3 l1 l2 l3 -
        ((4 : Real) / 3) *
          DifferentialGeometry.Geometry.Curvature.ricciEigenScalar3 l1 l2 l3 *
            DifferentialGeometry.Geometry.Curvature.ricciEigenNormSq3 l1 l2 l3 =
      (4 * DifferentialGeometry.Geometry.Curvature.ricciEigenNormSq3 l1 l2 l3 *
          traceFreeRicciNormSqAt
            (DifferentialGeometry.Geometry.Curvature.ricciEigenScalar3 l1 l2 l3)
            (DifferentialGeometry.Geometry.Curvature.ricciEigenNormSq3 l1 l2 l3) -
        2 * cubicQAt
          (DifferentialGeometry.Geometry.Curvature.ricciEigenScalar3 l1 l2 l3)
          (DifferentialGeometry.Geometry.Curvature.ricciEigenNormSq3 l1 l2 l3)
          (DifferentialGeometry.Geometry.Curvature.ricciEigenTraceCube3 l1 l2 l3)) /
        DifferentialGeometry.Geometry.Curvature.ricciEigenScalar3 l1 l2 l3 := by
  unfold ricciReact3 traceFreeRicciNormSqAt traceFreeRicciNormSqAtOf cubicQAt
    DifferentialGeometry.Geometry.Curvature.ricciEigenScalar3
      DifferentialGeometry.Geometry.Curvature.ricciEigenNormSq3
    DifferentialGeometry.Geometry.Curvature.ricciEigenTraceCube3
  have hR' : l1 + l2 + l3 ≠ 0 := by
    simpa [DifferentialGeometry.Geometry.Curvature.ricciEigenScalar3] using hR
  field_simp [hR']
  ring_nf

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.PDE.RicciFlow.trace_free_ricci_reaction_relation_eigenvalues with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.trace_free_ricci_reaction_relation_eigenvalues"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.trace_free_ricci_reaction_relation_eigenvalues ``Submission.DifferentialGeometry.PDE.RicciFlow.trace_free_ricci_reaction_relation_eigenvalues

def TraceFreeRicciReactionRelation
    (scalar ricciNormSq tfNormSq Q reaction : Real -> M -> Real) : Prop :=
  ∀ t x, scalar t x ≠ 0 ->
    4 * reaction t x - ((4 : Real) / 3) * scalar t x * ricciNormSq t x =
      (4 * ricciNormSq t x * tfNormSq t x - 2 * Q t x) / scalar t x

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.PDE.RicciFlow.TraceFreeRicciReactionRelation with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.TraceFreeRicciReactionRelation"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.TraceFreeRicciReactionRelation ``Submission.DifferentialGeometry.PDE.RicciFlow.TraceFreeRicciReactionRelation

omit [TopologicalSpace M] in
theorem trace_free_ricci_reaction_relation_of_eigenvalues
    (scalar ricciNormSq ricciTraceCube reaction : Real -> M -> Real)
    (l1 l2 l3 : Real -> M -> Real)
    (hscalar : ∀ t x,
      scalar t x =
        DifferentialGeometry.Geometry.Curvature.ricciEigenScalar3 (l1 t x) (l2 t x) (l3 t x))
    (hnorm : ∀ t x,
      ricciNormSq t x =
        DifferentialGeometry.Geometry.Curvature.ricciEigenNormSq3 (l1 t x) (l2 t x) (l3 t x))
    (hcube : ∀ t x,
      ricciTraceCube t x =
        DifferentialGeometry.Geometry.Curvature.ricciEigenTraceCube3 (l1 t x) (l2 t x) (l3 t x))
    (hreaction : ∀ t x,
      reaction t x = ricciReact3 (l1 t x) (l2 t x) (l3 t x)) :
    TraceFreeRicciReactionRelation
      scalar ricciNormSq (traceFreeRicciNormSq scalar ricciNormSq)
      (cubicQ scalar ricciNormSq ricciTraceCube) reaction := by
  intro t x hR
  have hR' :
      DifferentialGeometry.Geometry.Curvature.ricciEigenScalar3 (l1 t x) (l2 t x) (l3 t x) ≠
        0 := by
    simpa [hscalar t x] using hR
  rw [hreaction t x, hscalar t x, hnorm t x]
  rw [traceFreeRicciNormSq, traceFreeRicciNormSqOf, cubicQ, hscalar t x, hnorm t x,
    hcube t x]
  exact trace_free_ricci_reaction_relation_eigenvalues (l1 t x) (l2 t x) (l3 t x) hR'

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.PDE.RicciFlow.trace_free_ricci_reaction_relation_of_eigenvalues with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.trace_free_ricci_reaction_relation_of_eigenvalues"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.trace_free_ricci_reaction_relation_of_eigenvalues ``Submission.DifferentialGeometry.PDE.RicciFlow.trace_free_ricci_reaction_relation_of_eigenvalues

omit [TopologicalSpace M] in
theorem trace_free_ricci_reaction_relation_of_diagonal_components
    (scalar ricciNormSq ricciTraceCube : Real -> M -> Real)
    (l1 l2 l3 : Real -> M -> Real)
    (hscalar : ∀ t x,
      scalar t x =
        DifferentialGeometry.Geometry.Curvature.ricciEigenScalar3 (l1 t x) (l2 t x) (l3 t x))
    (hnorm : ∀ t x,
      ricciNormSq t x =
        DifferentialGeometry.Geometry.Curvature.ricciEigenNormSq3 (l1 t x) (l2 t x) (l3 t x))
    (hcube : ∀ t x,
      ricciTraceCube t x =
        DifferentialGeometry.Geometry.Curvature.ricciEigenTraceCube3 (l1 t x) (l2 t x) (l3 t x)) :
    TraceFreeRicciReactionRelation
      scalar ricciNormSq (traceFreeRicciNormSq scalar ricciNormSq)
      (cubicQ scalar ricciNormSq ricciTraceCube) (diagReact3 l1 l2 l3) := by
  exact trace_free_ricci_reaction_relation_of_eigenvalues
    (M := M)
    scalar ricciNormSq ricciTraceCube (diagReact3 l1 l2 l3)
    l1 l2 l3 hscalar hnorm hcube
    (by intro t x; exact diagReact3_eq (M := M) l1 l2 l3 t x)

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.PDE.RicciFlow.trace_free_ricci_reaction_relation_of_diagonal_components with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.trace_free_ricci_reaction_relation_of_diagonal_components"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.trace_free_ricci_reaction_relation_of_diagonal_components ``Submission.DifferentialGeometry.PDE.RicciFlow.trace_free_ricci_reaction_relation_of_diagonal_components

theorem curvReact3_frame
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Geometry.Curvature.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Geometry.Curvature.InverseMetricComponents M (Fin 3))
    (frame : Fin 3 -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (l1 l2 l3 : Real)
    (hInv : ∀ i j : Fin 3,
      gInv t x i j = DifferentialGeometry.Geometry.Curvature.delta3 i j)
    (hRic : ∀ i j : Fin 3,
      ricciCompInFrame (I := I) S frame t x i j =
        DifferentialGeometry.Geometry.Curvature.ricciDiag3 l1 l2 l3 i j)
    (hRm : ∀ i j k l : Fin 3,
      DifferentialGeometry.Geometry.Curvature.rm04Comp (I := I) (Rm04 t) frame x i k j l =
        DifferentialGeometry.Geometry.Curvature.standardRmDiag3 l1 l2 l3 i k j l) :
    curvRicciRicciInFrame (I := I) S Rm04 gInv frame t x =
      ricciReact3 l1 l2 l3 := by
  classical
  have hRicEval : ∀ i j : Fin 3,
      S.base.ricciAt t x (DifferentialGeometry.Geometry.Curvature.vec2 (frame i x) (frame j x)) =
        DifferentialGeometry.Geometry.Curvature.ricciDiag3 l1 l2 l3 i j := by
    intro i j
    simpa [ricciCompInFrame] using hRic i j
  have hraised : ∀ i j : Fin 3,
      raisedRicciCompInFrame (I := I) S gInv frame t x i j =
        DifferentialGeometry.Geometry.Curvature.ricciDiag3 l1 l2 l3 i j := by
    intro i j
    unfold raisedRicciCompInFrame
    fin_cases i <;> fin_cases j <;>
      simp [Fin.sum_univ_three, hInv, hRicEval, DifferentialGeometry.Geometry.Curvature.delta3,
        DifferentialGeometry.Geometry.Curvature.ricciDiag3]
  unfold curvRicciRicciInFrame
  simp_rw [hraised]
  simp_rw [hRm]
  exact curv3_diag_eq l1 l2 l3

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.PDE.RicciFlow.curvReact3_frame with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.curvReact3_frame"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.curvReact3_frame ``Submission.DifferentialGeometry.PDE.RicciFlow.curvReact3_frame

theorem canonReact3_frame
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Geometry.Curvature.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Geometry.Curvature.InverseMetricComponents M (Fin 3))
    (frame : Fin 3 -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (l1 l2 l3 : Real)
    (hInv : ∀ i j : Fin 3,
      gInv t x i j = DifferentialGeometry.Geometry.Curvature.delta3 i j)
    (hRic : ∀ i j : Fin 3,
      ricciCompInFrame (I := I) S frame t x i j =
        DifferentialGeometry.Geometry.Curvature.ricciDiag3 l1 l2 l3 i j)
    (hRm : ∀ i j k l : Fin 3,
      DifferentialGeometry.Geometry.Curvature.rm04Comp (I := I) (Rm04 t) frame x i k j l =
        DifferentialGeometry.Geometry.Curvature.standardRmDiag3 l1 l2 l3 i k j l) :
    ricciNormCurvatureReactionInFrame (I := I) S Rm04 gInv frame t x =
      -ricciReact3 l1 l2 l3 := by
  rw [ricciNormCurvatureReactionInFrame_apply,
    curvReact3_frame (I := I) S Rm04 gInv frame t x l1 l2 l3 hInv hRic hRm]

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.PDE.RicciFlow.canonReact3_frame with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.canonReact3_frame"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.canonReact3_frame ``Submission.DifferentialGeometry.PDE.RicciFlow.canonReact3_frame

theorem curv3_frame_neg
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Geometry.Curvature.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Geometry.Curvature.InverseMetricComponents M (Fin 3))
    (frame : Fin 3 -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (l1 l2 l3 : Real)
    (hInv : ∀ i j : Fin 3,
      gInv t x i j = DifferentialGeometry.Geometry.Curvature.delta3 i j)
    (hRic : ∀ i j : Fin 3,
      ricciCompInFrame (I := I) S frame t x i j =
        DifferentialGeometry.Geometry.Curvature.ricciDiag3 l1 l2 l3 i j)
    (hRm : ∀ i j k l : Fin 3,
      DifferentialGeometry.Geometry.Curvature.rm04Comp (I := I) (Rm04 t) frame x i k j l =
        DifferentialGeometry.Geometry.Curvature.standardRmDiag3 (-l1) (-l2) (-l3) i k j l) :
    curvRicciRicciInFrame (I := I) S Rm04 gInv frame t x =
      -ricciReact3 l1 l2 l3 := by
  classical
  have hRicEval : ∀ i j : Fin 3,
      S.base.ricciAt t x (DifferentialGeometry.Geometry.Curvature.vec2 (frame i x) (frame j x)) =
        DifferentialGeometry.Geometry.Curvature.ricciDiag3 l1 l2 l3 i j := by
    intro i j
    simpa [ricciCompInFrame] using hRic i j
  have hraised : ∀ i j : Fin 3,
      raisedRicciCompInFrame (I := I) S gInv frame t x i j =
        DifferentialGeometry.Geometry.Curvature.ricciDiag3 l1 l2 l3 i j := by
    intro i j
    unfold raisedRicciCompInFrame
    fin_cases i <;> fin_cases j <;>
      simp [Fin.sum_univ_three, hInv, hRicEval, DifferentialGeometry.Geometry.Curvature.delta3,
        DifferentialGeometry.Geometry.Curvature.ricciDiag3]
  unfold curvRicciRicciInFrame
  simp_rw [hraised]
  simp_rw [hRm]
  exact curv3_neg_eq l1 l2 l3

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.PDE.RicciFlow.curv3_frame_neg with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.curv3_frame_neg"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.curv3_frame_neg ``Submission.DifferentialGeometry.PDE.RicciFlow.curv3_frame_neg

theorem canon3_frame_neg
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Geometry.Curvature.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Geometry.Curvature.InverseMetricComponents M (Fin 3))
    (frame : Fin 3 -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (l1 l2 l3 : Real)
    (hInv : ∀ i j : Fin 3,
      gInv t x i j = DifferentialGeometry.Geometry.Curvature.delta3 i j)
    (hRic : ∀ i j : Fin 3,
      ricciCompInFrame (I := I) S frame t x i j =
        DifferentialGeometry.Geometry.Curvature.ricciDiag3 l1 l2 l3 i j)
    (hRm : ∀ i j k l : Fin 3,
      DifferentialGeometry.Geometry.Curvature.rm04Comp (I := I) (Rm04 t) frame x i k j l =
        DifferentialGeometry.Geometry.Curvature.standardRmDiag3 (-l1) (-l2) (-l3) i k j l) :
    ricciNormCurvatureReactionInFrame (I := I) S Rm04 gInv frame t x =
      ricciReact3 l1 l2 l3 := by
  rw [ricciNormCurvatureReactionInFrame_apply,
    curv3_frame_neg (I := I) S Rm04 gInv frame t x l1 l2 l3 hInv hRic hRm]
  ring

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.PDE.RicciFlow.canon3_frame_neg with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.canon3_frame_neg"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.canon3_frame_neg ``Submission.DifferentialGeometry.PDE.RicciFlow.canon3_frame_neg

def ricciNormAt {x : M}
    (Ric : DifferentialGeometry.Geometry.Curvature.Tensor02At (I := I) (M := M) x)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x)) : Real :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    DifferentialGeometry.Geometry.Curvature.ricciCompAt (I := I) basis Ric i j *
      DifferentialGeometry.Geometry.Curvature.ricciCompAt (I := I) basis Ric i j

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.PDE.RicciFlow.ricciNormAt with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ricciNormAt"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ricciNormAt ``Submission.DifferentialGeometry.PDE.RicciFlow.ricciNormAt

def curvRicAt {x : M}
    (Ric : DifferentialGeometry.Geometry.Curvature.Tensor02At (I := I) (M := M) x)
    (Rm04 : DifferentialGeometry.Geometry.Curvature.Tensor04At (I := I) (M := M) x)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x)) : Real :=
  ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
    DifferentialGeometry.Geometry.Curvature.rm04CompAt (I := I) basis Rm04 i k j l *
      DifferentialGeometry.Geometry.Curvature.ricciCompAt (I := I) basis Ric i j *
        DifferentialGeometry.Geometry.Curvature.ricciCompAt (I := I) basis Ric k l

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.PDE.RicciFlow.curvRicAt with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.curvRicAt"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.curvRicAt ``Submission.DifferentialGeometry.PDE.RicciFlow.curvRicAt

def reactAt {x : M}
    (Ric : DifferentialGeometry.Geometry.Curvature.Tensor02At (I := I) (M := M) x)
    (Rm04 : DifferentialGeometry.Geometry.Curvature.Tensor04At (I := I) (M := M) x)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x)) : Real :=
  -curvRicAt (I := I) Ric Rm04 basis

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.PDE.RicciFlow.reactAt with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.reactAt"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.reactAt ``Submission.DifferentialGeometry.PDE.RicciFlow.reactAt

def ricciCubeAt {x : M}
    (Ric : DifferentialGeometry.Geometry.Curvature.Tensor02At (I := I) (M := M) x)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x)) : Real :=
  ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
    DifferentialGeometry.Geometry.Curvature.ricciCompAt (I := I) basis Ric i j *
      DifferentialGeometry.Geometry.Curvature.ricciCompAt (I := I) basis Ric j k *
      DifferentialGeometry.Geometry.Curvature.ricciCompAt (I := I) basis Ric k i

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.PDE.RicciFlow.ricciCubeAt with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ricciCubeAt"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ricciCubeAt ``Submission.DifferentialGeometry.PDE.RicciFlow.ricciCubeAt

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] in
theorem ricciCubeAt_diag {x : M}
    {Ric : DifferentialGeometry.Geometry.Curvature.Tensor02At (I := I) (M := M) x}
    {scalar l1 l2 l3 : Real}
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    (hdiag : DifferentialGeometry.Geometry.Curvature.RicciDiagAt
      (I := I) Ric scalar l1 l2 l3 basis) :
    ricciCubeAt (I := I) Ric basis =
      DifferentialGeometry.Geometry.Curvature.ricciEigenTraceCube3 l1 l2 l3 := by
  classical
  unfold ricciCubeAt DifferentialGeometry.Geometry.Curvature.ricciEigenTraceCube3
  simp_rw [hdiag.2]
  unfold DifferentialGeometry.Geometry.Curvature.ricciDiag3
  simp [Fin.sum_univ_three]
  ring

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.PDE.RicciFlow.ricciCubeAt_diag with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ricciCubeAt_diag"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ricciCubeAt_diag ``Submission.DifferentialGeometry.PDE.RicciFlow.ricciCubeAt_diag

omit [IsManifold I 1 M] in
theorem ricciEnd_diagVec {x : M}
    (g : SmoothRiemannianMetric I M)
    {Ric : DifferentialGeometry.Geometry.Curvature.Tensor02At (I := I) (M := M) x}
    {scalar l1 l2 l3 : Real}
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    (horth : DifferentialGeometry.Geometry.Curvature.OrthonormalBasisAt (I := I) g x basis)
    (hdiag : DifferentialGeometry.Geometry.Curvature.RicciDiagAt
      (I := I) Ric scalar l1 l2 l3 basis) :
    DifferentialGeometry.Geometry.Curvature.ricciEndAt (I := I) g Ric (basis 0) = l1 • basis 0 /\
      DifferentialGeometry.Geometry.Curvature.ricciEndAt (I := I) g Ric (basis 1) = l2 • basis 1 /\
      DifferentialGeometry.Geometry.Curvature.ricciEndAt (I := I) g Ric (basis 2) = l3 • basis
        2 := by
  classical
  let T := DifferentialGeometry.Geometry.Curvature.ricciEndAt (I := I) g Ric
  have hdiagComp := hdiag.2
  have h0 : T (basis 0) = l1 • basis 0 := by
    apply eq_of_inner_basis_eq (I := I) g x basis
    intro j
    calc
      g.inner x (T (basis 0)) (basis j) =
          Ric (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) (basis 0) (basis j)) := by
            exact DifferentialGeometry.Geometry.Curvature.ricciEnd_inner (I := I) g Ric (basis 0)
              (basis j)
      _ = DifferentialGeometry.Geometry.Curvature.ricciDiag3 l1 l2 l3 0 j := by
            simpa [DifferentialGeometry.Geometry.Curvature.ricciCompAt_apply] using hdiagComp 0 j
      _ = g.inner x (l1 • basis 0) (basis j) := by
            fin_cases j <;> simp [DifferentialGeometry.Geometry.Curvature.ricciDiag3,
              DifferentialGeometry.Geometry.Curvature.delta3, horth 0 0, horth 0 1, horth 0 2]
  have h1 : T (basis 1) = l2 • basis 1 := by
    apply eq_of_inner_basis_eq (I := I) g x basis
    intro j
    calc
      g.inner x (T (basis 1)) (basis j) =
          Ric (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) (basis 1) (basis j)) := by
            exact DifferentialGeometry.Geometry.Curvature.ricciEnd_inner (I := I) g Ric (basis 1)
              (basis j)
      _ = DifferentialGeometry.Geometry.Curvature.ricciDiag3 l1 l2 l3 1 j := by
            simpa [DifferentialGeometry.Geometry.Curvature.ricciCompAt_apply] using hdiagComp 1 j
      _ = g.inner x (l2 • basis 1) (basis j) := by
            fin_cases j <;> simp [DifferentialGeometry.Geometry.Curvature.ricciDiag3,
              DifferentialGeometry.Geometry.Curvature.delta3, horth 1 0, horth 1 1, horth 1 2]
  have h2 : T (basis 2) = l3 • basis 2 := by
    apply eq_of_inner_basis_eq (I := I) g x basis
    intro j
    calc
      g.inner x (T (basis 2)) (basis j) =
          Ric (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) (basis 2) (basis j)) := by
            exact DifferentialGeometry.Geometry.Curvature.ricciEnd_inner (I := I) g Ric (basis 2)
              (basis j)
      _ = DifferentialGeometry.Geometry.Curvature.ricciDiag3 l1 l2 l3 2 j := by
            simpa [DifferentialGeometry.Geometry.Curvature.ricciCompAt_apply] using hdiagComp 2 j
      _ = g.inner x (l3 • basis 2) (basis j) := by
            fin_cases j <;> simp [DifferentialGeometry.Geometry.Curvature.ricciDiag3,
              DifferentialGeometry.Geometry.Curvature.delta3, horth 2 0, horth 2 1, horth 2 2]
  exact ⟨h0, h1, h2⟩

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.PDE.RicciFlow.ricciEnd_diagVec with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ricciEnd_diagVec"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ricciEnd_diagVec ``Submission.DifferentialGeometry.PDE.RicciFlow.ricciEnd_diagVec

def ricciCubeInvAt {x : M}
    (g : SmoothRiemannianMetric I M)
    (Ric : DifferentialGeometry.Geometry.Curvature.Tensor02At (I := I) (M := M) x) : Real :=
  let T := DifferentialGeometry.Geometry.Curvature.ricciEndAt (I := I) g Ric
  LinearMap.trace Real (TangentSpace I x) (T.comp (T.comp T))

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.PDE.RicciFlow.ricciCubeInvAt with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ricciCubeInvAt"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ricciCubeInvAt ``Submission.DifferentialGeometry.PDE.RicciFlow.ricciCubeInvAt

omit [IsManifold I 1 M] in
theorem ricciCubeInv_diag {x : M}
    (g : SmoothRiemannianMetric I M)
    {Ric : DifferentialGeometry.Geometry.Curvature.Tensor02At (I := I) (M := M) x}
    {scalar l1 l2 l3 : Real}
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    (horth : DifferentialGeometry.Geometry.Curvature.OrthonormalBasisAt (I := I) g x basis)
    (hdiag : DifferentialGeometry.Geometry.Curvature.RicciDiagAt
      (I := I) Ric scalar l1 l2 l3 basis) :
    ricciCubeInvAt (I := I) g Ric =
      DifferentialGeometry.Geometry.Curvature.ricciEigenTraceCube3 l1 l2 l3 := by
  classical
  let T := DifferentialGeometry.Geometry.Curvature.ricciEndAt (I := I) g Ric
  rcases ricciEnd_diagVec (I := I) g horth hdiag with ⟨hT0, hT1, hT2⟩
  have hT0c : (T.comp (T.comp T)) (basis 0) = (l1 ^ 3) • basis 0 := by
    simp [T, LinearMap.comp_apply, hT0, map_smul, pow_three, smul_smul,
      mul_assoc]
  have hT1c : (T.comp (T.comp T)) (basis 1) = (l2 ^ 3) • basis 1 := by
    simp [T, LinearMap.comp_apply, hT1, map_smul, pow_three, smul_smul,
      mul_assoc]
  have hT2c : (T.comp (T.comp T)) (basis 2) = (l3 ^ 3) • basis 2 := by
    simp [T, LinearMap.comp_apply, hT2, map_smul, pow_three, smul_smul,
      mul_assoc]
  have hinv :
      MetricInverseInBasis (I := I) g x basis DifferentialGeometry.Geometry.Curvature.delta3 :=
    DifferentialGeometry.Geometry.Curvature.orthonormal_invBasis3 (I := I) g basis horth
  unfold ricciCubeInvAt
  change LinearMap.trace Real (TangentSpace I x) (T.comp (T.comp T)) =
    DifferentialGeometry.Geometry.Curvature.ricciEigenTraceCube3 l1 l2 l3
  rw [linearMap_trace_eq_sum_inv_inner_apply (I := I) g x basis
    DifferentialGeometry.Geometry.Curvature.delta3 hinv]
  unfold DifferentialGeometry.Geometry.Curvature.ricciEigenTraceCube3
  simp only [Fin.sum_univ_three, DifferentialGeometry.Geometry.Curvature.delta3,
    LinearMap.coe_comp,
    Function.comp_apply]
  rw [show T (T (T (basis 0))) = (l1 ^ 3) • basis 0 by
        simpa [LinearMap.comp_apply] using hT0c,
      show T (T (T (basis 1))) = (l2 ^ 3) • basis 1 by
        simpa [LinearMap.comp_apply] using hT1c,
      show T (T (T (basis 2))) = (l3 ^ 3) • basis 2 by
        simpa [LinearMap.comp_apply] using hT2c]
  simp [DifferentialGeometry.Geometry.Curvature.delta3, horth 0 0, horth 1 1, horth 2 2]

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.PDE.RicciFlow.ricciCubeInv_diag with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ricciCubeInv_diag"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ricciCubeInv_diag ``Submission.DifferentialGeometry.PDE.RicciFlow.ricciCubeInv_diag

def ricciCube
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) : Real -> M -> Real :=
  fun t x => ricciCubeInvAt (I := I) (S.base.metric t) (S.ricciAt t x)

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.PDE.RicciFlow.ricciCube with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ricciCube"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ricciCube ``Submission.DifferentialGeometry.PDE.RicciFlow.ricciCube

private theorem prod_delta4
    (I0 J0 : Fin 4 -> Fin 3) :
    (∏ a : Fin 4, DifferentialGeometry.Geometry.Curvature.delta3 (I0 a) (J0 a)) =
      if I0 = J0 then 1 else 0 := by
  classical
  rw [Fin.prod_univ_four]
  by_cases h : I0 = J0
  · subst J0
    simp [DifferentialGeometry.Geometry.Curvature.delta3]
  · have hne :
        I0 0 ≠ J0 0 ∨ I0 1 ≠ J0 1 ∨ I0 2 ≠ J0 2 ∨ I0 3 ≠ J0 3 := by
      by_contra hslots
      push Not at hslots
      apply h
      funext a
      fin_cases a <;> simp [hslots]
    rcases hne with h0 | h1 | h2 | h3
    · simp [DifferentialGeometry.Geometry.Curvature.delta3, h, h0]
    · simp [DifferentialGeometry.Geometry.Curvature.delta3, h, h1]
    · simp [DifferentialGeometry.Geometry.Curvature.delta3, h, h2]
    · simp [DifferentialGeometry.Geometry.Curvature.delta3, h, h3]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.prod_delta4
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.prod_delta4 target :: scope.openDecls } }

private theorem sum_delta4
    (F G : (Fin 4 -> Fin 3) -> Real) :
    (∑ I0 : Fin 4 -> Fin 3, ∑ J0 : Fin 4 -> Fin 3,
        (∏ a : Fin 4, DifferentialGeometry.Geometry.Curvature.delta3 (I0 a) (J0 a)) * F I0 * G J0)
          =
      ∑ I0 : Fin 4 -> Fin 3, F I0 * G I0 := by
  classical
  apply Finset.sum_congr rfl
  intro I0 _
  simp [prod_delta4]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.sum_delta4
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.sum_delta4 target :: scope.openDecls } }

private def fin4ikjl :
    (Fin 4 -> Fin 3) ≃ (((Fin 3 × Fin 3) × Fin 3) × Fin 3) where
  toFun f := (((f 0, f 2), f 1), f 3)
  invFun p := DifferentialGeometry.Geometry.Curvature.slots4 p.1.1.1 p.1.2 p.1.1.2 p.2
  left_inv f := by
    funext a
    fin_cases a <;> simp [DifferentialGeometry.Geometry.Curvature.slots4]
  right_inv p := by
    rcases p with ⟨⟨⟨i, j⟩, k⟩, l⟩
    simp [DifferentialGeometry.Geometry.Curvature.slots4]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.fin4ikjl
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.fin4ikjl target :: scope.openDecls } }

private theorem sum4ikjl {α : Type*} [AddCommMonoid α]
    (F : (Fin 4 -> Fin 3) -> α) :
    (∑ I0 : Fin 4 -> Fin 3, F I0) =
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
        F (DifferentialGeometry.Geometry.Curvature.slots4 i k j l) := by
  classical
  rw [Fintype.sum_equiv fin4ikjl F
    (fun p : (((Fin 3 × Fin 3) × Fin 3) × Fin 3) =>
      F (DifferentialGeometry.Geometry.Curvature.slots4 p.1.1.1 p.1.2 p.1.1.2 p.2))]
  · repeat rw [Fintype.sum_prod_type]
  · intro I0
    have hslot :
        DifferentialGeometry.Geometry.Curvature.slots4 (fin4ikjl I0).1.1.1 (fin4ikjl I0).1.2
            (fin4ikjl I0).1.1.2 (fin4ikjl I0).2 = I0 := by
      change fin4ikjl.symm (fin4ikjl I0) = I0
      exact fin4ikjl.left_inv I0
    rw [hslot]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.sum4ikjl
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.sum4ikjl target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] in
private theorem coordPair04 {x : M}
    (Ric : DifferentialGeometry.Geometry.Curvature.Tensor02At (I := I) (M := M) x)
    (Rm04 : DifferentialGeometry.Geometry.Curvature.Tensor04At (I := I) (M := M) x)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x)) :
    coordInner0S (I := I) (x := x) 4 DifferentialGeometry.Geometry.Curvature.delta3
        Rm04 (ricciPair04 (I := I) Ric) basis =
      curvRicAt (I := I) Ric Rm04 basis := by
  classical
  unfold coordInner0S curvRicAt
  rw [sum_delta4]
  rw [sum4ikjl]
  have hpair : ∀ (v : Fin 4 → TangentSpace I x),
      ricciPair04 (I := I) Ric v =
        Ric (fun q : Fin 2 => if q = 0 then v 0 else v 2) *
          Ric (fun q : Fin 2 => if q = 0 then v 1 else v 3) := by
    intro v
    rw [ricciPair04_apply]
    congr 2
  have hslots2 (i j : Fin 3) :
      (fun q : Fin 2 => if q = 0 then basis i else basis j) =
        fun q : Fin 2 => basis (if q = 0 then i else j) := by
    funext q
    fin_cases q <;> rfl
  simp [tensor0SComponent, DifferentialGeometry.Geometry.Curvature.rm04CompAt,
    DifferentialGeometry.Geometry.Curvature.ricciCompAt,
    DifferentialGeometry.Geometry.Curvature.slots4,
    DifferentialGeometry.Geometry.Curvature.slots2,
    hpair, hslots2, mul_assoc]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.coordPair04
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.coordPair04 target :: scope.openDecls } }

theorem curvRic_inner {x : M}
    (g : SmoothRiemannianMetric I M)
    (Ric : DifferentialGeometry.Geometry.Curvature.Tensor02At (I := I) (M := M) x)
    (Rm04 : DifferentialGeometry.Geometry.Curvature.Tensor04At (I := I) (M := M) x)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (hinv : MetricInverseInBasis (I := I) g x basis
      DifferentialGeometry.Geometry.Curvature.delta3) :
    curvRicAt (I := I) Ric Rm04 basis =
      inner0S (I := I) g x 4 Rm04 (ricciPair04 (I := I) Ric) := by
  rw [inner0S_eq_coord (I := I) g x 4 basis DifferentialGeometry.Geometry.Curvature.delta3 hinv]
  exact (coordPair04 (I := I) Ric Rm04 basis).symm

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.PDE.RicciFlow.curvRic_inner with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.curvRic_inner"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.curvRic_inner ``Submission.DifferentialGeometry.PDE.RicciFlow.curvRic_inner

theorem reactAt_eq_react
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    {t : Real} {x : M}
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    (horth : DifferentialGeometry.Geometry.Curvature.OrthonormalBasisAt
      (I := I) (S.base.metric t) x basis) :
    reactAt (I := I) (S.ricciAt t x) (S.base.rm04 t x) basis =
      ricciReact (I := I) S t x := by
  have hinv :
      MetricInverseInBasis (I := I) (S.base.metric t) x basis
        DifferentialGeometry.Geometry.Curvature.delta3 :=
    DifferentialGeometry.Geometry.Curvature.orthonormal_invBasis3 (I := I) (S.base.metric t) basis
      horth
  unfold reactAt ricciReact
  rw [curvRic_inner (I := I) (S.base.metric t) (S.ricciAt t x)
    (S.base.rm04 t x) basis hinv]

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.PDE.RicciFlow.reactAt_eq_react with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.reactAt_eq_react"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.reactAt_eq_react ``Submission.DifferentialGeometry.PDE.RicciFlow.reactAt_eq_react

theorem react_frame {x : M}
    (g : SmoothRiemannianMetric I M)
    (Ric : DifferentialGeometry.Geometry.Curvature.Tensor02At (I := I) (M := M) x)
    (Rm04 : DifferentialGeometry.Geometry.Curvature.Tensor04At (I := I) (M := M) x)
    (basis₁ basis₂ : Module.Basis (Fin 3) Real (TangentSpace I x))
    (h₁ : DifferentialGeometry.Geometry.Curvature.OrthonormalBasisAt (I := I) g x basis₁)
    (h₂ : DifferentialGeometry.Geometry.Curvature.OrthonormalBasisAt (I := I) g x basis₂) :
    reactAt (I := I) Ric Rm04 basis₁ =
      reactAt (I := I) Ric Rm04 basis₂ := by
  have hinv₁ : MetricInverseInBasis (I := I) g x basis₁
    DifferentialGeometry.Geometry.Curvature.delta3 :=
    DifferentialGeometry.Geometry.Curvature.orthonormal_invBasis3 (I := I) g basis₁ h₁
  have hinv₂ : MetricInverseInBasis (I := I) g x basis₂
    DifferentialGeometry.Geometry.Curvature.delta3 :=
    DifferentialGeometry.Geometry.Curvature.orthonormal_invBasis3 (I := I) g basis₂ h₂
  unfold reactAt
  rw [curvRic_inner (I := I) g Ric Rm04 basis₁ hinv₁,
    curvRic_inner (I := I) g Ric Rm04 basis₂ hinv₂]

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.PDE.RicciFlow.react_frame with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.react_frame"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.react_frame ``Submission.DifferentialGeometry.PDE.RicciFlow.react_frame

private theorem prod_delta2
    (I0 J0 : Fin 2 -> Fin 3) :
    (∏ a : Fin 2, DifferentialGeometry.Geometry.Curvature.delta3 (I0 a) (J0 a)) =
      if I0 = J0 then 1 else 0 := by
  classical
  rw [Fin.prod_univ_two]
  by_cases h : I0 = J0
  · subst J0
    simp [DifferentialGeometry.Geometry.Curvature.delta3]
  · have hne : I0 0 ≠ J0 0 ∨ I0 1 ≠ J0 1 := by
      by_contra hslots
      push Not at hslots
      apply h
      funext a
      fin_cases a <;> simp [hslots]
    rcases hne with h0 | h1
    · simp [DifferentialGeometry.Geometry.Curvature.delta3, h, h0]
    · simp [DifferentialGeometry.Geometry.Curvature.delta3, h, h1]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.prod_delta2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.prod_delta2 target :: scope.openDecls } }

private theorem sum_delta2
    (F G : (Fin 2 -> Fin 3) -> Real) :
    (∑ I0 : Fin 2 -> Fin 3, ∑ J0 : Fin 2 -> Fin 3,
        (∏ a : Fin 2, DifferentialGeometry.Geometry.Curvature.delta3 (I0 a) (J0 a)) * F I0 * G J0)
          =
      ∑ I0 : Fin 2 -> Fin 3, F I0 * G I0 := by
  classical
  apply Finset.sum_congr rfl
  intro I0 _
  calc
    (∑ J0 : Fin 2 -> Fin 3,
        (∏ a : Fin 2, DifferentialGeometry.Geometry.Curvature.delta3 (I0 a) (J0 a)) * F I0 * G J0)
          =
        ∑ J0 : Fin 2 -> Fin 3, (if I0 = J0 then 1 else 0) * F I0 * G J0 := by
          apply Finset.sum_congr rfl
          intro J0 _
          rw [prod_delta2]
    _ = F I0 * G I0 := by
          simp

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.sum_delta2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.sum_delta2 target :: scope.openDecls } }

private def fin2ij :
    (Fin 2 -> Fin 3) ≃ (Fin 3 × Fin 3) where
  toFun f := (f 0, f 1)
  invFun p := DifferentialGeometry.Geometry.Curvature.slots2 p.1 p.2
  left_inv f := by
    funext a
    fin_cases a <;> simp [DifferentialGeometry.Geometry.Curvature.slots2]
  right_inv p := by
    rcases p with ⟨i, j⟩
    simp [DifferentialGeometry.Geometry.Curvature.slots2]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.fin2ij
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.fin2ij target :: scope.openDecls } }

private theorem sum2ij {α : Type*} [AddCommMonoid α]
    (F : (Fin 2 -> Fin 3) -> α) :
    (∑ I0 : Fin 2 -> Fin 3, F I0) =
      ∑ i : Fin 3, ∑ j : Fin 3, F (DifferentialGeometry.Geometry.Curvature.slots2 i j) := by
  classical
  rw [Fintype.sum_equiv fin2ij F
    (fun p : Fin 3 × Fin 3 => F (DifferentialGeometry.Geometry.Curvature.slots2 p.1 p.2))]
  · rw [Fintype.sum_prod_type]
  · intro I0
    have hslot :
        DifferentialGeometry.Geometry.Curvature.slots2 (fin2ij I0).1 (fin2ij I0).2 = I0 := by
      change fin2ij.symm (fin2ij I0) = I0
      exact fin2ij.left_inv I0
    rw [hslot]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.sum2ij
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.sum2ij target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] in
private theorem coordRic02 {x : M}
    (Ric : DifferentialGeometry.Geometry.Curvature.Tensor02At (I := I) (M := M) x)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x)) :
    coordInner0S (I := I) (x := x) 2 DifferentialGeometry.Geometry.Curvature.delta3 Ric Ric basis =
      ricciNormAt (I := I) Ric basis := by
  classical
  unfold coordInner0S ricciNormAt
  rw [sum_delta2]
  rw [sum2ij]
  simp [tensor0SComponent, DifferentialGeometry.Geometry.Curvature.ricciCompAt,
    DifferentialGeometry.Geometry.Curvature.slots2]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.coordRic02
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.coordRic02 target :: scope.openDecls } }

omit [IsManifold I 1 M] in
theorem ricciNorm_inner {x : M}
    (g : SmoothRiemannianMetric I M)
    (Ric : DifferentialGeometry.Geometry.Curvature.Tensor02At (I := I) (M := M) x)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (hinv : MetricInverseInBasis (I := I) g x basis
      DifferentialGeometry.Geometry.Curvature.delta3) :
    ricciNormAt (I := I) Ric basis =
      normSq0S (I := I) g x 2 Ric := by
  rw [normSq0S_eq_coord (I := I) g x 2 basis DifferentialGeometry.Geometry.Curvature.delta3 hinv
    Ric]
  exact (coordRic02 (I := I) Ric basis).symm

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.PDE.RicciFlow.ricciNorm_inner with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ricciNorm_inner"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ricciNorm_inner ``Submission.DifferentialGeometry.PDE.RicciFlow.ricciNorm_inner

omit [IsManifold I 1 M] in
theorem ricciNorm_frame {x : M}
    (g : SmoothRiemannianMetric I M)
    (Ric : DifferentialGeometry.Geometry.Curvature.Tensor02At (I := I) (M := M) x)
    (basis₁ basis₂ : Module.Basis (Fin 3) Real (TangentSpace I x))
    (h₁ : DifferentialGeometry.Geometry.Curvature.OrthonormalBasisAt (I := I) g x basis₁)
    (h₂ : DifferentialGeometry.Geometry.Curvature.OrthonormalBasisAt (I := I) g x basis₂) :
    ricciNormAt (I := I) Ric basis₁ =
      ricciNormAt (I := I) Ric basis₂ := by
  have hinv₁ : MetricInverseInBasis (I := I) g x basis₁
    DifferentialGeometry.Geometry.Curvature.delta3 :=
    DifferentialGeometry.Geometry.Curvature.orthonormal_invBasis3 (I := I) g basis₁ h₁
  have hinv₂ : MetricInverseInBasis (I := I) g x basis₂
    DifferentialGeometry.Geometry.Curvature.delta3 :=
    DifferentialGeometry.Geometry.Curvature.orthonormal_invBasis3 (I := I) g basis₂ h₂
  rw [ricciNorm_inner (I := I) g Ric basis₁ hinv₁,
    ricciNorm_inner (I := I) g Ric basis₂ hinv₂]

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.PDE.RicciFlow.ricciNorm_frame with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ricciNorm_frame"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ricciNorm_frame ``Submission.DifferentialGeometry.PDE.RicciFlow.ricciNorm_frame

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] in
theorem ricciNormAt_diag {x : M}
    {Ric : DifferentialGeometry.Geometry.Curvature.Tensor02At (I := I) (M := M) x}
    {scalar l1 l2 l3 : Real}
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    (hdiag : DifferentialGeometry.Geometry.Curvature.RicciDiagAt (I := I) Ric scalar l1 l2 l3
      basis) :
    ricciNormAt (I := I) Ric basis =
      DifferentialGeometry.Geometry.Curvature.ricciEigenNormSq3 l1 l2 l3 := by
  classical
  rcases hdiag with ⟨_, hric⟩
  unfold ricciNormAt DifferentialGeometry.Geometry.Curvature.ricciEigenNormSq3
  simp_rw [hric]
  unfold DifferentialGeometry.Geometry.Curvature.ricciDiag3
  simp [Fin.sum_univ_three]
  ring

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.PDE.RicciFlow.ricciNormAt_diag with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ricciNormAt_diag"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ricciNormAt_diag ``Submission.DifferentialGeometry.PDE.RicciFlow.ricciNormAt_diag

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] in
theorem reactAt_diag {x : M}
    {Ric : DifferentialGeometry.Geometry.Curvature.Tensor02At (I := I) (M := M) x}
    {Rm04 : DifferentialGeometry.Geometry.Curvature.Tensor04At (I := I) (M := M) x}
    {scalar l1 l2 l3 : Real}
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    (hdiag : DifferentialGeometry.Geometry.Curvature.RicciDiagAt (I := I) Ric scalar l1 l2 l3
      basis)
    (hRm : ∀ i j k l : Fin 3,
      DifferentialGeometry.Geometry.Curvature.rm04CompAt (I := I) basis Rm04 i k j l =
        DifferentialGeometry.Geometry.Curvature.standardRmDiag3 (-l1) (-l2) (-l3) i k j l) :
    reactAt (I := I) Ric Rm04 basis = ricciReact3 l1 l2 l3 := by
  classical
  rcases hdiag with ⟨_, hric⟩
  unfold reactAt curvRicAt
  simp_rw [hRm]
  simp_rw [hric]
  rw [curv3_neg_eq]
  ring

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.PDE.RicciFlow.reactAt_diag with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.reactAt_diag"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.reactAt_diag ``Submission.DifferentialGeometry.PDE.RicciFlow.reactAt_diag

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] in
theorem trace_free_ricci_reaction_relation_in_basis {x : M}
    {Ric : DifferentialGeometry.Geometry.Curvature.Tensor02At (I := I) (M := M) x}
    {Rm04 : DifferentialGeometry.Geometry.Curvature.Tensor04At (I := I) (M := M) x}
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    {scalar l1 l2 l3 ricciTraceCube : Real}
    (hdiag : DifferentialGeometry.Geometry.Curvature.RicciDiagAt (I := I) Ric scalar l1 l2 l3
      basis)
    (hcube :
      ricciTraceCube = DifferentialGeometry.Geometry.Curvature.ricciEigenTraceCube3 l1 l2 l3)
    (hRm : ∀ i j k l : Fin 3,
      DifferentialGeometry.Geometry.Curvature.rm04CompAt (I := I) basis Rm04 i k j l =
        DifferentialGeometry.Geometry.Curvature.standardRmDiag3 (-l1) (-l2) (-l3) i k j l)
    (hR : scalar ≠ 0) :
    4 * reactAt (I := I) Ric Rm04 basis -
        ((4 : Real) / 3) * scalar * ricciNormAt (I := I) Ric basis =
      (4 * ricciNormAt (I := I) Ric basis *
          traceFreeRicciNormSqAt scalar (ricciNormAt (I := I) Ric basis) -
        2 * cubicQAt scalar (ricciNormAt (I := I) Ric basis)
          ricciTraceCube) / scalar := by
  have hscalar :
      scalar = DifferentialGeometry.Geometry.Curvature.ricciEigenScalar3 l1 l2 l3 := hdiag.1
  have hR' :
      DifferentialGeometry.Geometry.Curvature.ricciEigenScalar3 l1 l2 l3 ≠ 0 := by
    simpa [hscalar] using hR
  rw [reactAt_diag (I := I) hdiag hRm, ricciNormAt_diag (I := I) hdiag,
    hscalar, hcube]
  exact trace_free_ricci_reaction_relation_eigenvalues l1 l2 l3 hR'

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.PDE.RicciFlow.trace_free_ricci_reaction_relation_in_basis with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.trace_free_ricci_reaction_relation_in_basis"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.trace_free_ricci_reaction_relation_in_basis ``Submission.DifferentialGeometry.PDE.RicciFlow.trace_free_ricci_reaction_relation_in_basis

omit [IsManifold I 1 M] in
omit [FiniteDimensional ℝ E] in
theorem diag_neg {x : M}
    {Ric : DifferentialGeometry.Geometry.Curvature.Tensor02At (I := I) (M := M) x}
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    {scalar l1 l2 l3 : Real}
    (hdiag : DifferentialGeometry.Geometry.Curvature.RicciDiagAt (I := I) Ric scalar l1 l2 l3
      basis) :
    DifferentialGeometry.Geometry.Curvature.RicciDiagAt (I := I) (-Ric) (-scalar)
      (-l1) (-l2) (-l3) basis := by
  rcases hdiag with ⟨hscalar, hric⟩
  constructor
  · unfold DifferentialGeometry.Geometry.Curvature.ricciEigenScalar3 at hscalar ⊢
    linarith
  · intro i j
    have hij := hric i j
    fin_cases i <;> fin_cases j <;>
      simpa [DifferentialGeometry.Geometry.Curvature.ricciCompAt_apply,
        DifferentialGeometry.Geometry.Curvature.ricciDiag3] using
        congrArg Neg.neg hij

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.PDE.RicciFlow.diag_neg with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.diag_neg"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.diag_neg ``Submission.DifferentialGeometry.PDE.RicciFlow.diag_neg

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] in
theorem trace_free_ricci_reaction_relation_of_trace_data {x : M}
    {g : SmoothRiemannianMetric I M}
    {Ric : DifferentialGeometry.Geometry.Curvature.Tensor02At (I := I) (M := M) x}
    {Rm04 : DifferentialGeometry.Geometry.Curvature.Tensor04At (I := I) (M := M) x}
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    {scalar l1 l2 l3 ricciTraceCube : Real}
    (htrace :
      DifferentialGeometry.Geometry.Curvature.RiemannFromRicci3DTraceDataAt
        (I := I) g (-Ric) (-scalar) Rm04 basis)
    (hdiag : DifferentialGeometry.Geometry.Curvature.RicciDiagAt (I := I) Ric scalar l1 l2 l3
      basis)
    (hcube :
      ricciTraceCube = DifferentialGeometry.Geometry.Curvature.ricciEigenTraceCube3 l1 l2 l3)
    (hR : scalar ≠ 0) :
    4 * reactAt (I := I) Ric Rm04 basis -
        ((4 : Real) / 3) * scalar * ricciNormAt (I := I) Ric basis =
      (4 * ricciNormAt (I := I) Ric basis *
          traceFreeRicciNormSqAt scalar (ricciNormAt (I := I) Ric basis) -
        2 * cubicQAt scalar (ricciNormAt (I := I) Ric basis)
          ricciTraceCube) / scalar := by
  have hneg := diag_neg (I := I) hdiag
  have hcomp :=
    DifferentialGeometry.Geometry.Curvature.standardRmComp_eq_diag (I := I) htrace hneg
  have hRm : ∀ i j k l : Fin 3,
      DifferentialGeometry.Geometry.Curvature.rm04CompAt (I := I) basis Rm04 i k j l =
        DifferentialGeometry.Geometry.Curvature.standardRmDiag3 (-l1) (-l2) (-l3) i k j l := by
    intro i j k l
    have h := hcomp i k j l
    simpa [DifferentialGeometry.Geometry.Curvature.standardRmCompAt_apply] using h
  exact trace_free_ricci_reaction_relation_in_basis (I := I) (Ric := Ric) (Rm04 := Rm04)
    (basis := basis) hdiag hcube hRm hR

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.PDE.RicciFlow.trace_free_ricci_reaction_relation_of_trace_data with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.trace_free_ricci_reaction_relation_of_trace_data"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.trace_free_ricci_reaction_relation_of_trace_data ``Submission.DifferentialGeometry.PDE.RicciFlow.trace_free_ricci_reaction_relation_of_trace_data

theorem trace_free_ricci_reaction_relation_at_point {x : M}
    {g : SmoothRiemannianMetric I M}
    {Ric : DifferentialGeometry.Geometry.Curvature.Tensor02At (I := I) (M := M) x}
    {Rm04 : DifferentialGeometry.Geometry.Curvature.Tensor04At (I := I) (M := M) x}
    {heatBasis eigBasis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    {scalar l1 l2 l3 ricciTraceCube : Real}
    (hheat : DifferentialGeometry.Geometry.Curvature.OrthonormalBasisAt (I := I) g x heatBasis)
    (heig : DifferentialGeometry.Geometry.Curvature.OrthonormalBasisAt (I := I) g x eigBasis)
    (htrace :
      DifferentialGeometry.Geometry.Curvature.RiemannFromRicci3DTraceDataAt
        (I := I) g (-Ric) (-scalar) Rm04 eigBasis)
    (hdiag : DifferentialGeometry.Geometry.Curvature.RicciDiagAt (I := I) Ric scalar l1 l2 l3
      eigBasis)
    (hcube :
      ricciTraceCube = DifferentialGeometry.Geometry.Curvature.ricciEigenTraceCube3 l1 l2 l3)
    (hR : scalar ≠ 0) :
    4 * reactAt (I := I) Ric Rm04 heatBasis -
        ((4 : Real) / 3) * scalar * ricciNormAt (I := I) Ric heatBasis =
      (4 * ricciNormAt (I := I) Ric heatBasis *
          traceFreeRicciNormSqAt scalar (ricciNormAt (I := I) Ric heatBasis) -
        2 * cubicQAt scalar (ricciNormAt (I := I) Ric heatBasis)
          ricciTraceCube) / scalar := by
  have hrel :=
    trace_free_ricci_reaction_relation_of_trace_data (I := I) (g := g) (Ric := Ric) (Rm04 := Rm04)
      (basis := eigBasis) htrace hdiag hcube hR
  have hreact :
      reactAt (I := I) Ric Rm04 heatBasis =
        reactAt (I := I) Ric Rm04 eigBasis :=
    react_frame (I := I) g Ric Rm04 heatBasis eigBasis hheat heig
  have hnorm :
      ricciNormAt (I := I) Ric heatBasis =
        ricciNormAt (I := I) Ric eigBasis :=
    ricciNorm_frame (I := I) g Ric heatBasis eigBasis hheat heig
  simpa [hreact, hnorm] using hrel

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.PDE.RicciFlow.trace_free_ricci_reaction_relation_at_point with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.trace_free_ricci_reaction_relation_at_point"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.trace_free_ricci_reaction_relation_at_point ``Submission.DifferentialGeometry.PDE.RicciFlow.trace_free_ricci_reaction_relation_at_point

private theorem raiseRicci_delta
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Geometry.Curvature.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M)
    (hInv : ∀ i j : Idx, gInv t x i j = if i = j then 1 else 0)
    (i j : Idx) :
    raisedRicciCompInFrame (I := I) S gInv frame t x i j =
      ricciCompInFrame (I := I) S frame t x i j := by
  classical
  unfold raisedRicciCompInFrame
  simp [hInv]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.raiseRicci_delta
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.raiseRicci_delta target :: scope.openDecls } }

theorem ricci_norm_sq_in_frame_eq_basis
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Geometry.Curvature.InverseMetricComponents M (Fin 3))
    (frame : Fin 3 -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (hbasis : ∀ i : Fin 3, basis i = frame i x)
    (hInv : ∀ i j : Fin 3, gInv t x i j = DifferentialGeometry.Geometry.Curvature.delta3 i j) :
    ricciNormSqInFrame (I := I) S gInv frame t x =
      ricciNormAt (I := I) (S.ricciAt t x) basis := by
  classical
  have hRicAt : ∀ i j : Fin 3,
      ricciCompInFrame (I := I) S frame t x i j =
        DifferentialGeometry.Geometry.Curvature.ricciCompAt (I := I) basis (S.ricciAt t x) i
          j := by
    intro i j
    simp [ricciCompInFrame, DifferentialGeometry.Geometry.Curvature.ricciCompAt_apply, hbasis i,
      hbasis j]
  have hraisedFrame : ∀ i j : Fin 3,
      raisedRicciCompInFrame (I := I) S gInv frame t x i j =
        ricciCompInFrame (I := I) S frame t x i j := by
    intro i j
    apply raiseRicci_delta (I := I) S gInv frame t x
    intro a b
    simpa [DifferentialGeometry.Geometry.Curvature.delta3] using hInv a b
  have hraised : ∀ i j : Fin 3,
      raisedRicciCompInFrame (I := I) S gInv frame t x i j =
        DifferentialGeometry.Geometry.Curvature.ricciCompAt (I := I) basis (S.ricciAt t x) i
          j := by
    intro i j
    rw [hraisedFrame i j, hRicAt i j]
  rw [ricciNormSqInFrame_apply]
  unfold ricciNormAt
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hRicAt i j, hraised i j]

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.PDE.RicciFlow.ricci_norm_sq_in_frame_eq_basis with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ricci_norm_sq_in_frame_eq_basis"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ricci_norm_sq_in_frame_eq_basis ``Submission.DifferentialGeometry.PDE.RicciFlow.ricci_norm_sq_in_frame_eq_basis

theorem ricci_norm_curvature_reaction_in_frame_eq_basis
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Geometry.Curvature.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Geometry.Curvature.InverseMetricComponents M (Fin 3))
    (frame : Fin 3 -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (hbasis : ∀ i : Fin 3, basis i = frame i x)
    (hInv : ∀ i j : Fin 3, gInv t x i j = DifferentialGeometry.Geometry.Curvature.delta3 i j) :
    ricciNormCurvatureReactionInFrame (I := I) S Rm04 gInv frame t x =
      reactAt (I := I) (S.ricciAt t x) (Rm04 t x) basis := by
  classical
  have hRicAt : ∀ i j : Fin 3,
      ricciCompInFrame (I := I) S frame t x i j =
        DifferentialGeometry.Geometry.Curvature.ricciCompAt (I := I) basis (S.ricciAt t x) i
          j := by
    intro i j
    simp [ricciCompInFrame, DifferentialGeometry.Geometry.Curvature.ricciCompAt_apply, hbasis i,
      hbasis j]
  have hraisedFrame : ∀ i j : Fin 3,
      raisedRicciCompInFrame (I := I) S gInv frame t x i j =
        ricciCompInFrame (I := I) S frame t x i j := by
    intro i j
    apply raiseRicci_delta (I := I) S gInv frame t x
    intro a b
    simpa [DifferentialGeometry.Geometry.Curvature.delta3] using hInv a b
  have hraised : ∀ i j : Fin 3,
      raisedRicciCompInFrame (I := I) S gInv frame t x i j =
        DifferentialGeometry.Geometry.Curvature.ricciCompAt (I := I) basis (S.ricciAt t x) i
          j := by
    intro i j
    rw [hraisedFrame i j, hRicAt i j]
  have hRmAt : ∀ i j k l : Fin 3,
      DifferentialGeometry.Geometry.Curvature.rm04Comp (I := I) (Rm04 t) frame x i k j l =
        DifferentialGeometry.Geometry.Curvature.rm04CompAt (I := I) basis (Rm04 t x) i k j l := by
    intro i j k l
    simp [DifferentialGeometry.Geometry.Curvature.rm04Comp,
      DifferentialGeometry.Geometry.Curvature.rm04Comp,
      DifferentialGeometry.Geometry.Curvature.rm04CompAt_apply,
      hbasis i, hbasis k, hbasis j, hbasis l]
  unfold ricciNormCurvatureReactionInFrame reactAt
  congr 1
  unfold curvRicciRicciInFrame curvRicAt
  simp_rw [hraised, hRmAt]

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.PDE.RicciFlow.ricci_norm_curvature_reaction_in_frame_eq_basis with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ricci_norm_curvature_reaction_in_frame_eq_basis"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ricci_norm_curvature_reaction_in_frame_eq_basis ``Submission.DifferentialGeometry.PDE.RicciFlow.ricci_norm_curvature_reaction_in_frame_eq_basis

theorem trace_free_ricci_reaction_relation_of_frame_basis
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Geometry.Curvature.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Geometry.Curvature.InverseMetricComponents M (Fin 3))
    (frame : Fin 3 -> (x : M) -> TangentSpace I x)
    (heatBasis eigBasis : (t : Real) -> (x : M) ->
      Module.Basis (Fin 3) Real (TangentSpace I x))
    (scalar ricciTraceCube : Real -> M -> Real)
    (l1 l2 l3 : Real -> M -> Real)
    (hheatBasis : ∀ (t : Real) (x : M) (i : Fin 3),
      heatBasis t x i = frame i x)
    (hheat : ∀ (t : Real) (x : M),
      DifferentialGeometry.Geometry.Curvature.OrthonormalBasisAt
        (I := I) (S.base.metric t) x (heatBasis t x))
    (heig : ∀ (t : Real) (x : M),
      DifferentialGeometry.Geometry.Curvature.OrthonormalBasisAt
        (I := I) (S.base.metric t) x (eigBasis t x))
    (htrace : ∀ (t : Real) (x : M),
      DifferentialGeometry.Geometry.Curvature.RiemannFromRicci3DTraceDataAt
        (I := I) (S.base.metric t) (-(S.ricciAt t x))
        (-(scalar t x)) (Rm04 t x) (eigBasis t x))
    (hdiag : ∀ (t : Real) (x : M),
      DifferentialGeometry.Geometry.Curvature.RicciDiagAt (I := I) (S.ricciAt t x)
        (scalar t x) (l1 t x) (l2 t x) (l3 t x) (eigBasis t x))
    (hcube : ∀ t x,
      ricciTraceCube t x =
        DifferentialGeometry.Geometry.Curvature.ricciEigenTraceCube3 (l1 t x) (l2 t x) (l3 t x))
    (hInv : ∀ (t : Real) (x : M) (i j : Fin 3),
      gInv t x i j = DifferentialGeometry.Geometry.Curvature.delta3 i j) :
    TraceFreeRicciReactionRelation
      scalar
      (ricciNormSqInFrame (I := I) S gInv frame)
      (traceFreeRicciNormSq scalar (ricciNormSqInFrame (I := I) S gInv frame))
      (cubicQ scalar (ricciNormSqInFrame (I := I) S gInv frame)
        ricciTraceCube)
      (ricciNormCurvatureReactionInFrame (I := I) S Rm04 gInv frame) := by
  intro t x hR
  have hnorm := ricci_norm_sq_in_frame_eq_basis (I := I) S gInv frame t x (heatBasis t x)
    (hheatBasis t x) (hInv t x)
  have hreact := ricci_norm_curvature_reaction_in_frame_eq_basis (I := I) S Rm04 gInv frame t x (heatBasis t x)
    (hheatBasis t x) (hInv t x)
  have hpoint := trace_free_ricci_reaction_relation_at_point (I := I) (g := S.base.metric t)
    (Ric := S.ricciAt t x) (Rm04 := Rm04 t x)
    (heatBasis := heatBasis t x) (eigBasis := eigBasis t x)
    (scalar := scalar t x) (l1 := l1 t x) (l2 := l2 t x) (l3 := l3 t x)
    (ricciTraceCube := ricciTraceCube t x)
    (hheat t x) (heig t x) (htrace t x) (hdiag t x) (hcube t x) hR
  rw [hreact, hnorm]
  unfold traceFreeRicciNormSq traceFreeRicciNormSqOf cubicQ
  rw [hnorm]
  exact hpoint

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.PDE.RicciFlow.trace_free_ricci_reaction_relation_of_frame_basis with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.trace_free_ricci_reaction_relation_of_frame_basis"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.trace_free_ricci_reaction_relation_of_frame_basis ``Submission.DifferentialGeometry.PDE.RicciFlow.trace_free_ricci_reaction_relation_of_frame_basis

theorem trace_free_ricci_reaction_relation_of_first_trace
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Geometry.Curvature.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Geometry.Curvature.InverseMetricComponents M (Fin 3))
    (frame : Fin 3 -> (x : M) -> TangentSpace I x)
    (heatBasis eigBasis : (t : Real) -> (x : M) ->
      Module.Basis (Fin 3) Real (TangentSpace I x))
    (scalar ricciTraceCube : Real -> M -> Real)
    (l1 l2 l3 : Real -> M -> Real)
    (hheatBasis : ∀ (t : Real) (x : M) (i : Fin 3),
      heatBasis t x i = frame i x)
    (hheat : ∀ (t : Real) (x : M),
      DifferentialGeometry.Geometry.Curvature.OrthonormalBasisAt
        (I := I) (S.base.metric t) x (heatBasis t x))
    (heig : ∀ (t : Real) (x : M),
      DifferentialGeometry.Geometry.Curvature.OrthonormalBasisAt
        (I := I) (S.base.metric t) x (eigBasis t x))
    (hcurv : ∀ (t : Real) (x : M),
      DifferentialGeometry.Geometry.Curvature.AlgebraicCurvatureSymmetries3
        (DifferentialGeometry.Geometry.Curvature.standardRmCompAt (I := I) (eigBasis t x)
          (Rm04 t x)))
    (hRicFirst : ∀ (t : Real) (x : M),
      DifferentialGeometry.Geometry.Curvature.RicciRealizesRm04FirstTraceAt (I := I)
        (S.ricciAt t x)
        (Rm04 t x) DifferentialGeometry.Geometry.Curvature.delta3 (eigBasis t x))
    (hScalarTrace : ∀ (t : Real) (x : M),
      DifferentialGeometry.Geometry.Curvature.ScalarRealizesRicciTraceAt (I := I) (scalar t x)
        (S.ricciAt t x) DifferentialGeometry.Geometry.Curvature.delta3 (eigBasis t x))
    (hdiag : ∀ (t : Real) (x : M),
      DifferentialGeometry.Geometry.Curvature.RicciDiagAt (I := I) (S.ricciAt t x)
        (scalar t x) (l1 t x) (l2 t x) (l3 t x) (eigBasis t x))
    (hcube : ∀ t x,
      ricciTraceCube t x =
        DifferentialGeometry.Geometry.Curvature.ricciEigenTraceCube3 (l1 t x) (l2 t x) (l3 t x))
    (hInv : ∀ (t : Real) (x : M) (i j : Fin 3),
      gInv t x i j = DifferentialGeometry.Geometry.Curvature.delta3 i j) :
    TraceFreeRicciReactionRelation
      scalar
      (ricciNormSqInFrame (I := I) S gInv frame)
      (traceFreeRicciNormSq scalar (ricciNormSqInFrame (I := I) S gInv frame))
      (cubicQ scalar (ricciNormSqInFrame (I := I) S gInv frame)
        ricciTraceCube)
      (ricciNormCurvatureReactionInFrame (I := I) S Rm04 gInv frame) := by
  refine trace_free_ricci_reaction_relation_of_frame_basis (I := I) S Rm04 gInv frame heatBasis eigBasis
    scalar ricciTraceCube l1 l2 l3 hheatBasis hheat heig ?_ hdiag hcube hInv
  intro t x
  exact DifferentialGeometry.Geometry.Curvature.traceDataOfFirst (I := I) (M := M) (heig t x)
    (hcurv t x) (hRicFirst t x) (hScalarTrace t x)

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.PDE.RicciFlow.trace_free_ricci_reaction_relation_of_first_trace with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.trace_free_ricci_reaction_relation_of_first_trace"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.trace_free_ricci_reaction_relation_of_first_trace ``Submission.DifferentialGeometry.PDE.RicciFlow.trace_free_ricci_reaction_relation_of_first_trace

omit [IsManifold I 1 M] in
omit [FiniteDimensional ℝ E] in
theorem scalar_eq_diag {x : M}
    {Ric : DifferentialGeometry.Geometry.Curvature.Tensor02At (I := I) (M := M) x}
    {scalar scalar0 l1 l2 l3 : Real}
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    (hScalar : DifferentialGeometry.Geometry.Curvature.ScalarRealizesRicciTraceAt
      (I := I) scalar Ric DifferentialGeometry.Geometry.Curvature.delta3 basis)
    (hdiag : DifferentialGeometry.Geometry.Curvature.RicciDiagAt
      (I := I) Ric scalar0 l1 l2 l3 basis) :
    scalar = scalar0 := by
  classical
  rcases hdiag with ⟨hscalar0, hric⟩
  have h00 :
      Ric (DifferentialGeometry.Geometry.Curvature.vec2 (basis 0) (basis 0)) = l1 := by
    simpa [DifferentialGeometry.Geometry.Curvature.ricciCompAt_apply,
      DifferentialGeometry.Geometry.Curvature.ricciDiag3] using hric 0 0
  have h11 :
      Ric (DifferentialGeometry.Geometry.Curvature.vec2 (basis 1) (basis 1)) = l2 := by
    simpa [DifferentialGeometry.Geometry.Curvature.ricciCompAt_apply,
      DifferentialGeometry.Geometry.Curvature.ricciDiag3] using hric 1 1
  have h22 :
      Ric (DifferentialGeometry.Geometry.Curvature.vec2 (basis 2) (basis 2)) = l3 := by
    simpa [DifferentialGeometry.Geometry.Curvature.ricciCompAt_apply,
      DifferentialGeometry.Geometry.Curvature.ricciDiag3] using hric 2 2
  rw [hScalar, hscalar0]
  rw [Fin.sum_univ_three]
  simp [DifferentialGeometry.Geometry.Curvature.delta3, h00, h11, h22,
    DifferentialGeometry.Geometry.Curvature.ricciEigenScalar3]

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.PDE.RicciFlow.scalar_eq_diag with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.scalar_eq_diag"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.scalar_eq_diag ``Submission.DifferentialGeometry.PDE.RicciFlow.scalar_eq_diag

omit [IsManifold I 1 M] in
theorem scalarTrace_delta {x : M}
    (g : SmoothRiemannianMetric I M)
    (Ric : DifferentialGeometry.Geometry.Curvature.Tensor02At (I := I) (M := M) x)
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    (horth : DifferentialGeometry.Geometry.Curvature.OrthonormalBasisAt (I := I) g x basis) :
    DifferentialGeometry.Geometry.Curvature.ScalarRealizesRicciTraceAt (I := I)
      (DifferentialGeometry.Geometry.Operator.metricTracePair0SAt (I := I) g Ric)
      Ric DifferentialGeometry.Geometry.Curvature.delta3 basis := by
  classical
  have hinv :
      Tensor0SBundle.MetricInverseInBasis (I := I) g x basis
        DifferentialGeometry.Geometry.Curvature.delta3 :=
    DifferentialGeometry.Geometry.Curvature.orthonormal_invBasis3 (I := I) g basis horth
  unfold DifferentialGeometry.Geometry.Curvature.ScalarRealizesRicciTraceAt
  rw [DifferentialGeometry.Geometry.Operator.metricTracePair0SAt_eq_sum_basis
    (I := I) g basis DifferentialGeometry.Geometry.Curvature.delta3 hinv Ric]

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.PDE.RicciFlow.scalarTrace_delta with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.scalarTrace_delta"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.scalarTrace_delta ``Submission.DifferentialGeometry.PDE.RicciFlow.scalarTrace_delta

omit [IsManifold I 1 M] in
theorem firstTrace_delta
    {x : M} (g : SmoothRiemannianMetric I M)
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    (horth : DifferentialGeometry.Geometry.Curvature.OrthonormalBasisAt (I := I) g x basis)
    (Ric : DifferentialGeometry.Geometry.Curvature.Tensor02At (I := I) (M := M) x)
    (Rm13 : DifferentialGeometry.Geometry.Curvature.Tensor13At (I := I) (M := M) x)
    (Rm04 : DifferentialGeometry.Geometry.Curvature.Tensor04At (I := I) (M := M) x)
    (hRic : Ric = DifferentialGeometry.Geometry.Curvature.ricciFromRm13At (I := I) (M := M) Rm13)
    (hLower : DifferentialGeometry.Geometry.Curvature.Rm04LowersRm13At (I := I) g x Rm13 Rm04) :
    DifferentialGeometry.Geometry.Curvature.RicciRealizesRm04FirstTraceAt (I := I) Ric Rm04
      DifferentialGeometry.Geometry.Curvature.delta3 basis := by
  classical
  have hinv :
      Tensor0SBundle.MetricInverseInBasis (I := I) g x basis
        DifferentialGeometry.Geometry.Curvature.delta3 :=
    DifferentialGeometry.Geometry.Curvature.orthonormal_invBasis3 (I := I) g basis horth
  exact DifferentialGeometry.Geometry.Curvature.ricciFirstTraceAt_of_rm13 (I := I) g basis
    DifferentialGeometry.Geometry.Curvature.delta3 hinv Ric Rm13 Rm04 hRic hLower

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.PDE.RicciFlow.firstTrace_delta with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.firstTrace_delta"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.firstTrace_delta ``Submission.DifferentialGeometry.PDE.RicciFlow.firstTrace_delta

theorem delta3_symm (i j : Fin 3) :
    DifferentialGeometry.Geometry.Curvature.delta3 i j =
      DifferentialGeometry.Geometry.Curvature.delta3 j i := by
  unfold DifferentialGeometry.Geometry.Curvature.delta3
  by_cases hij : i = j
  · subst j
    simp
  · have hji : j ≠ i := fun h => hij h.symm
    simp [hij, hji]

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.PDE.RicciFlow.delta3_symm with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.delta3_symm"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.delta3_symm ``Submission.DifferentialGeometry.PDE.RicciFlow.delta3_symm

private theorem sum_fin_two_fun_local {Idx : Type*} [Fintype Idx]
    {α : Type*} [AddCommMonoid α]
    (F : (Fin 2 -> Idx) -> α) :
    (∑ I0 : Fin 2 -> Idx, F I0) =
      ∑ i : Idx, ∑ j : Idx, F (fun a : Fin 2 => if a = 0 then i else j) := by
  classical
  rw [Fintype.sum_equiv (finTwoArrowEquiv Idx) F
    (fun p : Idx × Idx => F (fun a : Fin 2 => if a = 0 then p.1 else p.2))]
  · rw [Fintype.sum_prod_type]
  · intro I0
    congr
    funext a
    fin_cases a <;> simp [finTwoArrowEquiv]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.sum_fin_two_fun_local
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.sum_fin_two_fun_local target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [IsManifold I 1 M] in
private theorem vec2_update_zero {x : M}
    (X Y X' : TangentSpace I x) :
    Function.update (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) X Y)
        (0 : Fin 2) X' =
      DifferentialGeometry.Geometry.Curvature.vec2 (I := I) X' Y := by
  funext a
  fin_cases a <;> simp [DifferentialGeometry.Geometry.Curvature.vec2, Function.update]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.vec2_update_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.vec2_update_zero target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [IsManifold I 1 M] in
private theorem vec2_update_one {x : M}
    (X Y Y' : TangentSpace I x) :
    Function.update (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) X Y)
        (1 : Fin 2) Y' =
      DifferentialGeometry.Geometry.Curvature.vec2 (I := I) X Y' := by
  funext a
  fin_cases a <;> simp [DifferentialGeometry.Geometry.Curvature.vec2, Function.update]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.vec2_update_one
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.vec2_update_one target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] in
theorem ricciSym_of_basis
    {Idx : Type*} [Finite Idx]
    {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (A : DifferentialGeometry.Geometry.Curvature.Tensor02At (I := I) (M := M) x)
    (hsym : ∀ i j : Idx,
      A (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) (basis i) (basis j)) =
        A (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) (basis j) (basis i))) :
    DifferentialGeometry.Geometry.Curvature.RicciSymAt (I := I) A := by
  classical
  intro X Y
  let cx : Idx -> Real := fun i => basis.repr X i
  let cy : Idx -> Real := fun i => basis.repr Y i
  have hX : X = ∑ i : Idx, cx i • basis i := by
    simp [cx]
  have hY : Y = ∑ i : Idx, cy i • basis i := by
    simp [cy]
  have hXY :
      A (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) X Y) =
        ∑ r : Fin 2 -> Idx,
          A (fun a : Fin 2 =>
            (if a = 0 then cx (r a) else cy (r a)) • basis (r a)) := by
    rw [hX, hY]
    have hsum :
        A (fun a : Fin 2 =>
            ∑ j : Idx,
              (if a = 0 then cx j else cy j) • basis j) =
          ∑ r : Fin 2 -> Idx,
            A (fun a : Fin 2 =>
              (if a = 0 then cx (r a) else cy (r a)) • basis (r a)) := by
      exact
        (ContinuousMultilinearMap.map_sum
          (f := A)
          (g := fun a j =>
            (if a = 0 then cx j else cy j) • basis j))
    have hfun : DifferentialGeometry.Geometry.Curvature.vec2 (I := I)
        (∑ i : Idx, cx i • basis i) (∑ i : Idx, cy i • basis i) =
        fun a : Fin 2 => ∑ j : Idx,
          (if a = 0 then cx j else cy j) • basis j := by
      funext a
      fin_cases a <;> simp [DifferentialGeometry.Geometry.Curvature.vec2]
    rw [hfun]
    exact hsum
  have hYX :
      A (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) Y X) =
        ∑ r : Fin 2 -> Idx,
          A (fun a : Fin 2 =>
            (if a = 0 then cy (r a) else cx (r a)) • basis (r a)) := by
    rw [hX, hY]
    have hsum :
        A (fun a : Fin 2 =>
            ∑ j : Idx,
              (if a = 0 then cy j else cx j) • basis j) =
          ∑ r : Fin 2 -> Idx,
            A (fun a : Fin 2 =>
              (if a = 0 then cy (r a) else cx (r a)) • basis (r a)) := by
      exact
        (ContinuousMultilinearMap.map_sum
          (f := A)
          (g := fun a j =>
            (if a = 0 then cy j else cx j) • basis j))
    have hfun : DifferentialGeometry.Geometry.Curvature.vec2 (I := I)
        (∑ i : Idx, cy i • basis i) (∑ i : Idx, cx i • basis i) =
        fun a : Fin 2 => ∑ j : Idx,
          (if a = 0 then cy j else cx j) • basis j := by
      funext a
      fin_cases a <;> simp [DifferentialGeometry.Geometry.Curvature.vec2]
    rw [hfun]
    exact hsum
  rw [hXY, hYX]
  rw [sum_fin_two_fun_local, sum_fin_two_fun_local]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  have hleft :
      (fun a : Fin 2 =>
        (if a = 0
          then cx ((fun a : Fin 2 => if a = 0 then j else i) a)
          else cy ((fun a : Fin 2 => if a = 0 then j else i) a)) •
            basis ((fun a : Fin 2 => if a = 0 then j else i) a)) =
        DifferentialGeometry.Geometry.Curvature.vec2 (I := I) (cx j • basis j)
          (cy i • basis i) := by
    funext a
    fin_cases a <;> simp [DifferentialGeometry.Geometry.Curvature.vec2,
      DifferentialGeometry.Geometry.Curvature.vec2]
  have hright :
      (fun a : Fin 2 =>
        (if a = 0
          then cy ((fun a : Fin 2 => if a = 0 then i else j) a)
          else cx ((fun a : Fin 2 => if a = 0 then i else j) a)) •
            basis ((fun a : Fin 2 => if a = 0 then i else j) a)) =
        DifferentialGeometry.Geometry.Curvature.vec2 (I := I) (cy i • basis i)
          (cx j • basis j) := by
    funext a
    fin_cases a <;> simp [DifferentialGeometry.Geometry.Curvature.vec2,
      DifferentialGeometry.Geometry.Curvature.vec2]
  rw [hleft, hright]
  have hL :
      A (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) (cx j • basis j) (cy i • basis i)) =
        (cx j) * (cy i) *
          A (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) (basis j) (basis i)) := by
    have h0 := A.map_update_smul
      (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) (basis j) (cy i • basis i))
      (0 : Fin 2) (cx j) (basis j)
    have h1 := A.map_update_smul
      (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) (basis j) (basis i))
      (1 : Fin 2) (cy i) (basis i)
    calc
      A (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) (cx j • basis j) (cy i • basis i))
          = (cx j) *
              A (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) (basis j)
                (cy i • basis i)) := by
              simpa only [DifferentialGeometry.Geometry.Curvature.vec2,
                DifferentialGeometry.Geometry.Curvature.vec2,
                vec2_update_zero,
                smul_eq_mul] using h0
      _ = (cx j) * ((cy i) *
              A (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) (basis j) (basis i))) := by
              congr 1
              simpa only [DifferentialGeometry.Geometry.Curvature.vec2,
                DifferentialGeometry.Geometry.Curvature.vec2,
                vec2_update_one,
                smul_eq_mul] using h1
      _ = (cx j) * (cy i) *
              A (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) (basis j) (basis i)) :=
                by ring
  have hR :
      A (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) (cy i • basis i) (cx j • basis j)) =
        (cy i) * (cx j) *
          A (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) (basis i) (basis j)) := by
    have h0 := A.map_update_smul
      (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) (basis i) (cx j • basis j))
      (0 : Fin 2) (cy i) (basis i)
    have h1 := A.map_update_smul
      (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) (basis i) (basis j))
      (1 : Fin 2) (cx j) (basis j)
    calc
      A (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) (cy i • basis i) (cx j • basis j))
          = (cy i) *
              A (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) (basis i)
                (cx j • basis j)) := by
              simpa only [DifferentialGeometry.Geometry.Curvature.vec2,
                DifferentialGeometry.Geometry.Curvature.vec2,
                vec2_update_zero,
                smul_eq_mul] using h0
      _ = (cy i) * ((cx j) *
              A (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) (basis i) (basis j))) := by
              congr 1
              simpa only [DifferentialGeometry.Geometry.Curvature.vec2,
                DifferentialGeometry.Geometry.Curvature.vec2,
                vec2_update_one,
                smul_eq_mul] using h1
      _ = (cy i) * (cx j) *
              A (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) (basis i) (basis j)) :=
                by ring
  rw [hL, hR, hsym j i]
  ring

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.PDE.RicciFlow.ricciSym_of_basis with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ricciSym_of_basis"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ricciSym_of_basis ``Submission.DifferentialGeometry.PDE.RicciFlow.ricciSym_of_basis

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] in
theorem ricciSym_rm04
    {Idx : Type*} [Fintype Idx]
    {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (Ric : DifferentialGeometry.Geometry.Curvature.Tensor02At (I := I) (M := M) x)
    (Rm04 : DifferentialGeometry.Geometry.Curvature.Tensor04At (I := I) (M := M) x)
    (hTrace : DifferentialGeometry.Geometry.Curvature.RicciRealizesRm04FirstTraceAt (I := I) Ric
      Rm04
      gInv basis)
    (hPair : ∀ W X Y Z : TangentSpace I x,
      Rm04 (DifferentialGeometry.Geometry.Curvature.vec4 (I := I) W X Y Z) =
        Rm04 (DifferentialGeometry.Geometry.Curvature.vec4 (I := I) Y Z W X))
    (hOutput : DifferentialGeometry.Geometry.Curvature.Rm04OutputSkewAt (I := I) Rm04)
    (hInput : ∀ X Y Z W : TangentSpace I x,
      Rm04 (DifferentialGeometry.Geometry.Curvature.vec4 (I := I) Y X Z W) =
        -Rm04 (DifferentialGeometry.Geometry.Curvature.vec4 (I := I) X Y Z W))
    (hInv : ∀ i j : Idx, gInv i j = gInv j i) :
    DifferentialGeometry.Geometry.Curvature.RicciSymAt (I := I) Ric := by
  exact ricciSym_of_basis (I := I) basis Ric
    (fun i j =>
      DifferentialGeometry.Geometry.Curvature.ricciSymm_of_rm04 (I := I) basis gInv Ric Rm04 hTrace
        hPair hOutput hInput hInv i j)

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.PDE.RicciFlow.ricciSym_rm04 with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ricciSym_rm04"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ricciSym_rm04 ``Submission.DifferentialGeometry.PDE.RicciFlow.ricciSym_rm04

theorem trace_free_ricci_reaction_relation_of_diagonal_frame_components
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Geometry.Curvature.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Geometry.Curvature.InverseMetricComponents M (Fin 3))
    (frame : Fin 3 -> (x : M) -> TangentSpace I x)
    (scalar ricciTraceCube : Real -> M -> Real)
    (l1 l2 l3 : Real -> M -> Real)
    (hscalar : ∀ t x,
      scalar t x =
        DifferentialGeometry.Geometry.Curvature.ricciEigenScalar3 (l1 t x) (l2 t x) (l3 t x))
    (hcube : ∀ t x,
      ricciTraceCube t x =
        DifferentialGeometry.Geometry.Curvature.ricciEigenTraceCube3 (l1 t x) (l2 t x) (l3 t x))
    (hInv : ∀ (t : Real) (x : M) (i j : Fin 3),
      gInv t x i j = DifferentialGeometry.Geometry.Curvature.delta3 i j)
    (hRic : ∀ (t : Real) (x : M) (i j : Fin 3),
      ricciCompInFrame (I := I) S frame t x i j =
        DifferentialGeometry.Geometry.Curvature.ricciDiag3 (l1 t x) (l2 t x) (l3 t x) i j)
    (hRm : ∀ (t : Real) (x : M) (i j k l : Fin 3),
      DifferentialGeometry.Geometry.Curvature.rm04Comp (I := I) (Rm04 t) frame x i k j l =
        DifferentialGeometry.Geometry.Curvature.standardRmDiag3 (-(l1 t x)) (-(l2 t x)) (-(l3 t x))
          i k j l) :
    TraceFreeRicciReactionRelation
      scalar
      (ricciNormSqInFrame (I := I) S gInv frame)
      (traceFreeRicciNormSq scalar (ricciNormSqInFrame (I := I) S gInv frame))
      (cubicQ scalar (ricciNormSqInFrame (I := I) S gInv frame)
        ricciTraceCube)
      (ricciNormCurvatureReactionInFrame (I := I) S Rm04 gInv frame) := by
  classical
  refine trace_free_ricci_reaction_relation_of_eigenvalues
    (M := M)
    scalar (ricciNormSqInFrame (I := I) S gInv frame) ricciTraceCube
    (ricciNormCurvatureReactionInFrame (I := I) S Rm04 gInv frame)
    l1 l2 l3 hscalar ?_ hcube ?_
  · intro t x
    have hRicAt : ∀ i j : Fin 3,
        S.base.ricciAt t x (DifferentialGeometry.Geometry.Curvature.vec2 (frame i x) (frame j x)) =
          DifferentialGeometry.Geometry.Curvature.ricciDiag3 (l1 t x) (l2 t x) (l3 t x) i j := by
      intro i j
      simpa [ricciCompInFrame] using hRic t x i j
    have hraised : ∀ i j : Fin 3,
        raisedRicciCompInFrame (I := I) S gInv frame t x i j =
          DifferentialGeometry.Geometry.Curvature.ricciDiag3 (l1 t x) (l2 t x) (l3 t x) i j := by
      intro i j
      unfold raisedRicciCompInFrame
      fin_cases i <;> fin_cases j <;>
        simp [Fin.sum_univ_three, hInv t x, hRicAt, DifferentialGeometry.Geometry.Curvature.delta3,
          DifferentialGeometry.Geometry.Curvature.ricciDiag3]
    rw [ricciNormSqInFrame_apply]
    simp only [hraised]
    unfold DifferentialGeometry.Geometry.Curvature.ricciEigenNormSq3
      DifferentialGeometry.Geometry.Curvature.ricciDiag3
    simp only [Fin.sum_univ_three]
    rw [hRic t x 0 0, hRic t x 1 1, hRic t x 2 2]
    simp [DifferentialGeometry.Geometry.Curvature.ricciDiag3]
    ring
  · intro t x
    exact canon3_frame_neg (I := I) S Rm04 gInv frame t x
      (l1 t x) (l2 t x) (l3 t x)
      (hInv t x) (hRic t x) (hRm t x)

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.PDE.RicciFlow.trace_free_ricci_reaction_relation_of_diagonal_frame_components with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.trace_free_ricci_reaction_relation_of_diagonal_frame_components"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.trace_free_ricci_reaction_relation_of_diagonal_frame_components ``Submission.DifferentialGeometry.PDE.RicciFlow.trace_free_ricci_reaction_relation_of_diagonal_frame_components

theorem trace_free_ricci_reaction_relation_of_curvature_trace
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Geometry.Curvature.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Geometry.Curvature.InverseMetricComponents M (Fin 3))
    (frame : Fin 3 -> (x : M) -> TangentSpace I x)
    (basis : (t : Real) -> (x : M) ->
      Module.Basis (Fin 3) Real (TangentSpace I x))
    (scalar ricciTraceCube : Real -> M -> Real)
    (l1 l2 l3 : Real -> M -> Real)
    (hbasis : ∀ (t : Real) (x : M) (i : Fin 3),
      basis t x i = frame i x)
    (htrace : ∀ (t : Real) (x : M),
      DifferentialGeometry.Geometry.Curvature.RiemannFromRicci3DTraceDataAt
        (I := I) (S.base.metric t) (-(S.ricciAt t x))
        (-(scalar t x)) (Rm04 t x) (basis t x))
    (hscalar : ∀ t x,
      scalar t x =
        DifferentialGeometry.Geometry.Curvature.ricciEigenScalar3 (l1 t x) (l2 t x) (l3 t x))
    (hcube : ∀ t x,
      ricciTraceCube t x =
        DifferentialGeometry.Geometry.Curvature.ricciEigenTraceCube3 (l1 t x) (l2 t x) (l3 t x))
    (hInv : ∀ (t : Real) (x : M) (i j : Fin 3),
      gInv t x i j = DifferentialGeometry.Geometry.Curvature.delta3 i j)
    (hRic : ∀ (t : Real) (x : M) (i j : Fin 3),
      ricciCompInFrame (I := I) S frame t x i j =
        DifferentialGeometry.Geometry.Curvature.ricciDiag3 (l1 t x) (l2 t x) (l3 t x) i j) :
    TraceFreeRicciReactionRelation
      scalar
      (ricciNormSqInFrame (I := I) S gInv frame)
      (traceFreeRicciNormSq scalar (ricciNormSqInFrame (I := I) S gInv frame))
      (cubicQ scalar (ricciNormSqInFrame (I := I) S gInv frame)
        ricciTraceCube)
      (ricciNormCurvatureReactionInFrame (I := I) S Rm04 gInv frame) := by
  classical
  have hRm : ∀ (t : Real) (x : M) (i j k l : Fin 3),
      DifferentialGeometry.Geometry.Curvature.rm04Comp (I := I) (Rm04 t) frame x i k j l =
        DifferentialGeometry.Geometry.Curvature.standardRmDiag3 (-(l1 t x)) (-(l2 t x)) (-(l3 t x))
          i k j l := by
    intro t x i j k l
    have hdiag : DifferentialGeometry.Geometry.Curvature.RicciDiagAt (I := I)
        (S.ricciAt t x) (scalar t x)
        (l1 t x) (l2 t x) (l3 t x) (basis t x) := by
      constructor
      · exact hscalar t x
      · intro a b
        have h := hRic t x a b
        simpa [ricciCompInFrame, DifferentialGeometry.Geometry.Curvature.ricciCompAt_apply,
          hbasis t x a, hbasis t x b] using h
    have hneg := diag_neg (I := I) hdiag
    have hcomp :=
      DifferentialGeometry.Geometry.Curvature.standardRmComp_eq_diag (I := I) (htrace t x) hneg
    have h := hcomp i k j l
    simpa [DifferentialGeometry.Geometry.Curvature.standardRmCompAt_apply,
      DifferentialGeometry.Geometry.Curvature.rm04Comp,
      DifferentialGeometry.Geometry.Curvature.rm04Comp,
        DifferentialGeometry.Geometry.Curvature.rm04CompAt_apply,
      hbasis t x i, hbasis t x k, hbasis t x j, hbasis t x l] using h
  exact trace_free_ricci_reaction_relation_of_diagonal_frame_components (I := I) S Rm04 gInv frame scalar ricciTraceCube
    l1 l2 l3 hscalar hcube hInv hRic hRm

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.PDE.RicciFlow.trace_free_ricci_reaction_relation_of_curvature_trace with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.trace_free_ricci_reaction_relation_of_curvature_trace"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.trace_free_ricci_reaction_relation_of_curvature_trace ``Submission.DifferentialGeometry.PDE.RicciFlow.trace_free_ricci_reaction_relation_of_curvature_trace

theorem trace_free_ricci_reaction_relation_of_first_trace_frame
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Geometry.Curvature.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Geometry.Curvature.InverseMetricComponents M (Fin 3))
    (frame : Fin 3 -> (x : M) -> TangentSpace I x)
    (basis : (t : Real) -> (x : M) ->
      Module.Basis (Fin 3) Real (TangentSpace I x))
    (scalar ricciTraceCube : Real -> M -> Real)
    (l1 l2 l3 : Real -> M -> Real)
    (hbasis : ∀ (t : Real) (x : M) (i : Fin 3),
      basis t x i = frame i x)
    (horth : ∀ (t : Real) (x : M),
      DifferentialGeometry.Geometry.Curvature.OrthonormalBasisAt
        (I := I) (S.base.metric t) x (basis t x))
    (hcurv : ∀ (t : Real) (x : M),
      DifferentialGeometry.Geometry.Curvature.AlgebraicCurvatureSymmetries3
        (DifferentialGeometry.Geometry.Curvature.standardRmCompAt (I := I) (basis t x) (Rm04 t x)))
    (hRicTrace : ∀ (t : Real) (x : M),
      DifferentialGeometry.Geometry.Curvature.RicciRealizesRm04FirstTraceAt
        (I := I) (S.ricciAt t x) (Rm04 t x) DifferentialGeometry.Geometry.Curvature.delta3
        (basis t x))
    (hScalarTrace : ∀ (t : Real) (x : M),
      DifferentialGeometry.Geometry.Curvature.ScalarRealizesRicciTraceAt
        (I := I) (scalar t x) (S.ricciAt t x) DifferentialGeometry.Geometry.Curvature.delta3
        (basis t x))
    (hscalar : ∀ t x,
      scalar t x =
        DifferentialGeometry.Geometry.Curvature.ricciEigenScalar3 (l1 t x) (l2 t x) (l3 t x))
    (hcube : ∀ t x,
      ricciTraceCube t x =
        DifferentialGeometry.Geometry.Curvature.ricciEigenTraceCube3 (l1 t x) (l2 t x) (l3 t x))
    (hInv : ∀ (t : Real) (x : M) (i j : Fin 3),
      gInv t x i j = DifferentialGeometry.Geometry.Curvature.delta3 i j)
    (hRic : ∀ (t : Real) (x : M) (i j : Fin 3),
      ricciCompInFrame (I := I) S frame t x i j =
        DifferentialGeometry.Geometry.Curvature.ricciDiag3 (l1 t x) (l2 t x) (l3 t x) i j) :
    TraceFreeRicciReactionRelation
      scalar
      (ricciNormSqInFrame (I := I) S gInv frame)
      (traceFreeRicciNormSq scalar (ricciNormSqInFrame (I := I) S gInv frame))
      (cubicQ scalar (ricciNormSqInFrame (I := I) S gInv frame)
        ricciTraceCube)
      (ricciNormCurvatureReactionInFrame (I := I) S Rm04 gInv frame) := by
  refine trace_free_ricci_reaction_relation_of_curvature_trace (I := I) S Rm04 gInv frame basis scalar
    ricciTraceCube l1 l2 l3 hbasis ?_ hscalar hcube hInv hRic
  intro t x
  exact DifferentialGeometry.Geometry.Curvature.traceDataOfFirst
    (I := I) (horth t x) (hcurv t x) (hRicTrace t x) (hScalarTrace t x)

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.PDE.RicciFlow.trace_free_ricci_reaction_relation_of_first_trace_frame with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.trace_free_ricci_reaction_relation_of_first_trace_frame"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.trace_free_ricci_reaction_relation_of_first_trace_frame ``Submission.DifferentialGeometry.PDE.RicciFlow.trace_free_ricci_reaction_relation_of_first_trace_frame

end DifferentialGeometry.PDE.RicciFlow
