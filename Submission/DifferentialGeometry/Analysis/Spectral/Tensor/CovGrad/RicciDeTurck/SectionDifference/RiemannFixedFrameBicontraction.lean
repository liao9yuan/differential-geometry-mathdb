import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifference.KoszulCovariantDerivative
import Submission.DifferentialGeometry.Geometry.Curvature.RoughLaplacian.ConnectionDifference.CovariantDerivative
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Cotangent.InverseMetricField
import Submission.DifferentialGeometry.Geometry.Connection.MetricCompatibility.Tensor.InverseMetric
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Metric.CometricDoubleTrace
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Permutation.Naturality
import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ConnectionDifference.RicciPalatini
import Submission.DifferentialGeometry.Geometry.Curvature.RoughLaplacian.RicciTrace.Basic
import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.TensorAction.Field
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurck.SectionDifference.KoszulSecondCovariantDerivative
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurck.SectionDifference.PrincipalEndomorphismTrace
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurck.SectionDifference.SymmetrizedReindexedCoefficient
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurck.SectionDifference.ReindexingTermDecomposition

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Connection.Realization _root_.Submission.DifferentialGeometry.Tensor.Multilinear
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Operator


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators _root_.Matrix _root_.Submission.Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2

open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow _root_.Submission.DifferentialGeometry.Analysis.Parabolic
    DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.DeTurck

section NormedRiemannCoefficients

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

def riemannKernelBilin (g₁ : SmoothRiemannianMetric I M) (x : M) (p q : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun v0 => (g₁.inner x (riemannOp (LeviCivita (I := I) g₁) x v0 p q))
      map_add' := fun v0 v0' => by
        rw [(riemannOp (LeviCivita (I := I) g₁) x).map_add v0 v0',
          add_apply, add_apply, map_add]
      map_smul' := fun c v0 => by
        rw [(riemannOp (LeviCivita (I := I) g₁) x).map_smul c v0,
          smul_apply, smul_apply, map_smul,
          RingHom.id_apply] }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannKernelBilin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannKernelBilin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannKernelBilin ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannKernelBilin

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
@[simp] theorem riemannKernelBilin_apply (g₁ : SmoothRiemannianMetric I M) (x : M)
    (p q v0 v1 : TangentSpace I x) :
    riemannKernelBilin (I := I) g₁ x p q v0 v1 =
      g₁.inner x (riemannOp (LeviCivita (I := I) g₁) x v0 p q) v1 := by
  rw [riemannKernelBilin, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannKernelBilin_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannKernelBilin_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannKernelBilin_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannKernelBilin_apply

def riemannSummandFib (g₁ : SmoothRiemannianMetric I M) (x : M) (p q : TangentSpace I x) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  haveI : FiniteDimensional ℝ (Tensor0SSpace 2 I x) := inferInstance
  LinearMap.toContinuousLinearMap
    { toFun := fun D =>
        (Tensor0SSpace.toModel D
          ![tangentSpaceModelContinuousLinearEquiv (I := I) x p,
            tangentSpaceModelContinuousLinearEquiv (I := I) x q]) •
          Tensor0SSpace.ofModel (I := I) (x := x)
            (DifferentialGeometry.Tensor.Multilinear.biForm₂ToModel E
              (tangentBilinearFormToModel (I := I) x
                (riemannKernelBilin (I := I) g₁ x p q)))
      map_add' := fun D D' => by
        rw [Tensor0SSpace.toModel_add, add_apply, add_smul]
      map_smul' := fun c D => by
        rw [Tensor0SSpace.toModel_smul, smul_apply, smul_eq_mul,
          RingHom.id_apply, _root_.SemigroupAction.mul_smul] }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannSummandFib then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannSummandFib"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannSummandFib ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannSummandFib

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
@[simp] theorem riemannSummandFib_toModel (g₁ : SmoothRiemannianMetric I M) (x : M)
    (p q : TangentSpace I x) (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel (riemannSummandFib (I := I) g₁ x p q D) v =
      (Tensor0SSpace.toModel D
        ![tangentSpaceModelContinuousLinearEquiv (I := I) x p,
          tangentSpaceModelContinuousLinearEquiv (I := I) x q]) *
        g₁.inner x (riemannOp (LeviCivita (I := I) g₁) x
          ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 0)) p q)
          ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 1)) := by
  rw [riemannSummandFib, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
    Tensor0SSpace.toModel_smul, smul_apply, Tensor0SSpace.toModel_ofModel,
    DifferentialGeometry.Tensor.Multilinear.biForm₂ToModel_apply, tangentBilinearFormToModel_apply, smul_eq_mul,
    riemannKernelBilin_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannSummandFib_toModel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannSummandFib_toModel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannSummandFib_toModel ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannSummandFib_toModel

def riemannBiContrFibFixedFrame (g₁ : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  (2 : ℝ) • ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
    riemannSummandFib (I := I) g₁ x (B a x) (B b x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannBiContrFibFixedFrame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannBiContrFibFixedFrame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannBiContrFibFixedFrame ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannBiContrFibFixedFrame

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem riemannBiContrFibFixedFrame_toModel (g₁ : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M)
    (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel (riemannBiContrFibFixedFrame (I := I) g₁ B x D) v =
      2 * ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        g₁.inner x (riemannOp (LeviCivita (I := I) g₁) x
          ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 0))
          (B a x) (B b x))
          ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 1)) *
          Tensor0SSpace.toModel D
            ![tangentSpaceModelContinuousLinearEquiv (I := I) x (B a x),
              tangentSpaceModelContinuousLinearEquiv (I := I) x (B b x)] := by
  classical
  rw [riemannBiContrFibFixedFrame, smul_apply, Tensor0SSpace.toModel_smul,
    smul_apply, smul_eq_mul]
  apply congrArg (fun z : ℝ => 2 * z)
  rw [sum_apply, ← Tensor0SSpace.toModelL_apply, map_sum, sum_apply]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [sum_apply, Tensor0SSpace.toModelL_apply, ← Tensor0SSpace.toModelL_apply,
    map_sum, sum_apply]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Tensor0SSpace.toModelL_apply, riemannSummandFib_toModel]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannBiContrFibFixedFrame_toModel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannBiContrFibFixedFrame_toModel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannBiContrFibFixedFrame_toModel ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannBiContrFibFixedFrame_toModel

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem riemannBiContrFibFixedFrame_eval (g₁ : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M)
    (D : Tensor0SSpace 2 I x) (v : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.eval (riemannBiContrFibFixedFrame (I := I) g₁ B x D) v =
      2 * ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        g₁.inner x (riemannOp (LeviCivita (I := I) g₁) x (v 0) (B a x) (B b x)) (v 1) *
          Tensor0SSpace.eval D ![B a x, B b x] := by
  let vE : Fin 2 → E :=
    fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x (v i)
  have h := riemannBiContrFibFixedFrame_toModel (I := I) g₁ B x D vE
  rw [show vE = (fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x (v i)) from rfl,
    Tensor0SSpace.toModel_apply_tangent] at h
  simp only [Tensor0SSpace.toModel_apply_model_vector,
    tangentSpaceModelContinuousLinearEquiv_apply,
    tangentSpaceModelContinuousLinearEquiv_symm_apply,
    Tensor0SSpace.eval_eq] at h
  have hv (a b : Fin (Module.finrank ℝ E)) :
      (fun i => ![B a x, B b x] i) = ![B a x, B b x] := by
    funext i
    rfl
  convert h using 1
  · rw [Tensor0SSpace.eval_eq]
  · simp only [Tensor0SSpace.eval_eq]
    apply congrArg (fun z : ℝ => 2 * z)
    refine Finset.sum_congr rfl (fun a _ => ?_)
    refine Finset.sum_congr rfl (fun b _ => ?_)
    apply congrArg (fun z : ℝ =>
      g₁.inner x (riemannOp (LeviCivita (I := I) g₁) x (v 0) (B a x) (B b x)) (v 1) * z)
    exact congrArg D (hv a b).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannBiContrFibFixedFrame_eval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannBiContrFibFixedFrame_eval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannBiContrFibFixedFrame_eval ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannBiContrFibFixedFrame_eval

def innerPairBilin (x : M) (K Dd : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (X : TangentSpace I x) : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun Y => (K X Y) • (Dd X)
      map_add' := fun Y Y' => by rw [map_add, add_smul]
      map_smul' := fun c Y => by rw [map_smul, smul_eq_mul, RingHom.id_apply, _root_.SemigroupAction.mul_smul] }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.innerPairBilin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.innerPairBilin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.innerPairBilin ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.innerPairBilin

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem innerPairBilin_apply (x : M) (K Dd : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (X Y Y' : TangentSpace I x) :
    innerPairBilin (I := I) x K Dd X Y Y' = K X Y * Dd X Y' := by
  rw [innerPairBilin, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
    smul_apply, smul_eq_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.innerPairBilin_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.innerPairBilin_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.innerPairBilin_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.innerPairBilin_apply

def outerPairBilin (g : SmoothRiemannianMetric I M) (x : M)
    (K Dd : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun X => ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        (chartInvGramMatrix (I := I) g x x k l *
            K X (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x k)) •
          (ContinuousLinearMap.flip Dd (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x l))
      map_add' := fun X X' => by
        ext Y'
        simp only [add_apply, FunLike.coe_sum,
          FunLike.coe_smul, Finset.sum_apply, Pi.smul_apply, map_add, smul_eq_mul]
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        change chartInvGramMatrix (I := I) g x x k l *
            (K X (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x k) +
              K X' (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x k)) *
              Dd Y' (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x l) = _
        have hflip :
            (ContinuousLinearMap.flip Dd (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x l)) Y' =
              Dd Y' (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x l) := rfl
        rw [hflip]
        ring
      map_smul' := fun c X => by
        ext Y'
        simp only [smul_apply, FunLike.coe_sum,
          FunLike.coe_smul, Finset.sum_apply, Pi.smul_apply,
          map_smul, smul_eq_mul, RingHom.id_apply]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        change chartInvGramMatrix (I := I) g x x k l *
            (c * K X (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x k)) *
              Dd Y' (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x l) = _
        have hflip :
            (ContinuousLinearMap.flip Dd (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x l)) Y' =
              Dd Y' (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x l) := rfl
        rw [hflip]
        ring }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.outerPairBilin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.outerPairBilin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.outerPairBilin ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.outerPairBilin

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
theorem outerPairBilin_apply (g : SmoothRiemannianMetric I M) (x : M)
    (K Dd : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) (X X' : TangentSpace I x) :
    outerPairBilin (I := I) g x K Dd X X' =
      ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g x x k l *
          (K X (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x k) *
            Dd X' (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x l)) := by
  rw [outerPairBilin, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]
  simp only [sum_apply, smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine Finset.sum_congr rfl (fun l _ => ?_)
  change chartInvGramMatrix (I := I) g x x k l *
      K X (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x k) *
        Dd X' (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x l) = _
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.outerPairBilin_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.outerPairBilin_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.outerPairBilin_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.outerPairBilin_apply

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
theorem double_frame_bilin_trace_eq_fixed
    (g : SmoothRiemannianMetric I M) (x : M)
    (K Dd : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (B : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hB : ∀ i j, g.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0) :
    ∑ a, ∑ b, K (B a) (B b) * Dd (B a) (B b) =
      ∑ m, ∑ n, chartInvGramMatrix (I := I) g x x m n *
        (∑ k, ∑ l, chartInvGramMatrix (I := I) g x x k l *
          (K (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x m)
              (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x k) *
            Dd (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x n)
              (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x l))) := by
  classical
  have hinner : ∀ a, ∑ b, K (B a) (B b) * Dd (B a) (B b) =
      outerPairBilin (I := I) g x K Dd (B a) (B a) := by
    intro a
    rw [outerPairBilin_apply]
    have h := orthonormal_basis_bilin_trace (I := I) (M := M) g (x := x)
      (innerPairBilin (I := I) x K Dd (B a)) B hB
    simp only [innerPairBilin_apply] at h
    rw [h]
  rw [Finset.sum_congr rfl (fun a _ => hinner a)]
  have hout := orthonormal_basis_bilin_trace (I := I) (M := M) g (x := x)
    (outerPairBilin (I := I) g x K Dd) B hB
  rw [hout]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [outerPairBilin_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.double_frame_bilin_trace_eq_fixed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.double_frame_bilin_trace_eq_fixed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.double_frame_bilin_trace_eq_fixed ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.double_frame_bilin_trace_eq_fixed

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
theorem double_frame_bilin_trace_indep
    (g : SmoothRiemannianMetric I M) (x : M)
    (K Dd : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (B C : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hB : ∀ i j, g.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0)
    (hC : ∀ i j, g.inner x (C i) (C j) = if i = j then (1 : ℝ) else 0) :
    ∑ a, ∑ b, K (B a) (B b) * Dd (B a) (B b) =
      ∑ a, ∑ b, K (C a) (C b) * Dd (C a) (C b) := by
  rw [double_frame_bilin_trace_eq_fixed (I := I) g x K Dd B hB,
    double_frame_bilin_trace_eq_fixed (I := I) g x K Dd C hC]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.double_frame_bilin_trace_indep then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.double_frame_bilin_trace_indep"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.double_frame_bilin_trace_indep ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.double_frame_bilin_trace_indep

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
theorem contMDiff_bilinSection_of_chartScalar
    (Hb : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (hscalar : ∀ (x₀ : M) (σ : Fin 2 → Fin (Module.finrank ℝ E)),
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞
        (fun x : M => Hb x (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ (σ 0) x) (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ (σ 1) x))
        (chartAt H x₀).source) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x
        (Tensor0SSpace.ofModel (I := I) (x := x)
          (DifferentialGeometry.Tensor.Multilinear.biForm₂ToModel (TangentSpace I x) (Hb x)))) := by
  classical
  let d := Module.finrank ℝ E
  let b : Module.Basis (Fin d) ℝ E := DifferentialGeometry.Tensor.Coordinates.chartModelBasis E
  refine (contMDiff_multilinearSection_iff_coord (TangentSpace I) ∞ b
    (fun x => Tensor0SSpace.ofModel (I := I) (x := x)
      (DifferentialGeometry.Tensor.Multilinear.biForm₂ToModel (TangentSpace I x) (Hb x)))).mpr fun σ x₀ => ?_
  have hcomp : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun x : M => Hb x (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ (σ 0) x) (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ (σ 1) x))
      (chartAt H x₀).source := hscalar x₀ σ
  have hx₀_source : x₀ ∈ (chartAt H x₀).source := mem_chart_source H x₀
  have hx₀_base : x₀ ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet :=
    _root_.FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) x₀
  have h_source_nhd : (chartAt H x₀).source ∈ 𝓝 x₀ :=
    (chartAt H x₀).open_source.mem_nhds hx₀_source
  refine ((hcomp x₀ hx₀_source).contMDiffAt h_source_nhd).congr_of_eventuallyEq ?_
  have h_base_nhd : (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet ∈ 𝓝 x₀ :=
    (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds hx₀_base
  filter_upwards [h_base_nhd] with x hx
  rw [continuousMultilinearMap_basis_repr]
  change Tensor0SSpace.eval
      ((tensor0SSpaceFiberContinuousLinearEquiv (I := I) 2 x).symm
        (DifferentialGeometry.Tensor.Multilinear.biForm₂ToModel (TangentSpace I x) (Hb x)))
      (fun j => (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).symmL ℝ x (b (σ j))) = _
  rw [Tensor0SSpace.eval_fiber_equiv_symm, DifferentialGeometry.Tensor.Multilinear.biForm₂ToModel_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.contMDiff_bilinSection_of_chartScalar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.contMDiff_bilinSection_of_chartScalar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.contMDiff_bilinSection_of_chartScalar ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.contMDiff_bilinSection_of_chartScalar

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem kernelScalar_global (g₁ : SmoothRiemannianMetric I M)
    {Y W p q : Π b : M, TangentSpace I b}
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W))
    (hp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% p))
    (hq : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% q)) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => g₁.inner x
        (riemannOp (LeviCivita (I := I) g₁) x (Y x) (p x) (q x)) (W x)) := by
  classical
  have hRsec : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => riemannSec (LeviCivita (I := I) g₁) Y p q b)) :=
    riemannSec_contMDiff (cov := LeviCivita (I := I) g₁) hY hp hq
  have hcongr : (fun x : M => g₁.inner x
        (riemannOp (LeviCivita (I := I) g₁) x (Y x) (p x) (q x)) (W x)) =
      (fun x : M => g₁.inner x (riemannSec (LeviCivita (I := I) g₁) Y p q x) (W x)) := by
    funext x
    rw [riemannOp_apply_smooth (cov := LeviCivita (I := I) g₁) hY hp hq]
  rw [hcongr]
  exact contMDiff_g_inner_of_smooth_sections (I := I) g₁
    ⟨fun b => riemannSec (LeviCivita (I := I) g₁) Y p q b, hRsec⟩ ⟨fun b => W b, hW⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.kernelScalar_global then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.kernelScalar_global"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.kernelScalar_global ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.kernelScalar_global

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem riemannKernelBilin_homSection_contMDiff (g₁ : SmoothRiemannianMetric I M)
    {p q : Π b : M, TangentSpace I b}
    (hp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% p))
    (hq : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% q)) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun b : M => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ)
        x (riemannKernelBilin (I := I) g₁ x (p x) (q x))) := by
  classical
  apply contMDiff_continuousLinearMap_section_of_apply
    (V₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
    (φ := fun x : M => riemannKernelBilin (I := I) g₁ x (p x) (q x))
  intro Y
  apply contMDiff_continuousLinearMap_section_of_apply
    (V₂ := fun _ : M => ℝ)
    (φ := fun x : M => riemannKernelBilin (I := I) g₁ x (p x) (q x) (Y x))
  intro W
  have h_scalar := kernelScalar_global (I := I) g₁ Y.contMDiff W.contMDiff hp hq
  intro x
  rw [_root_.Bundle.contMDiffAt_section]
  refine (h_scalar.contMDiffAt).congr_of_eventuallyEq ?_
  filter_upwards with y
  change riemannKernelBilin (I := I) g₁ y (p y) (q y) (Y y) (W y) =
    (_root_.FiberBundle.trivializationAt ℝ (Bundle.Trivial M ℝ) x ⟨y, _⟩).2
  rw [riemannKernelBilin_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannKernelBilin_homSection_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannKernelBilin_homSection_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannKernelBilin_homSection_contMDiff ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannKernelBilin_homSection_contMDiff

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
theorem contMDiff_bilinSection_of_homSection
    (Hb : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (hHb : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun b : M => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ) x (Hb x))) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x
        (Tensor0SSpace.ofModel (I := I) (x := x)
          (DifferentialGeometry.Tensor.Multilinear.biForm₂ToModel (TangentSpace I x) (Hb x)))) := by
  classical
  refine contMDiff_bilinSection_of_chartScalar (I := I) Hb (fun x₀ σ => ?_)
  have hcf_0 : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b => DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ (σ 0) b))
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet := fun x hx =>
    DifferentialGeometry.Tensor.Coordinates.chartBasisVec_contMDiffOn (I := I) x₀ (σ 0) x hx
  have hcf_1 : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b => DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ (σ 1) b))
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet := fun x hx =>
    DifferentialGeometry.Tensor.Coordinates.chartBasisVec_contMDiffOn (I := I) x₀ (σ 1) x hx
  have happ1 := ContMDiffOn.clm_bundle_apply (F₁ := E) (F₂ := E →L[ℝ] ℝ)
    (E₁ := fun z : M => TangentSpace I z) (E₂ := fun z : M => TangentSpace I z →L[ℝ] ℝ)
    (b := id) hHb.contMDiffOn hcf_0
  have happ := ContMDiffOn.clm_bundle_apply (F₁ := E) (F₂ := ℝ)
    (E₁ := fun z : M => TangentSpace I z) (E₂ := fun _ : M => ℝ)
    (b := id) happ1 hcf_1
  intro x hx
  have hpx := happ x hx
  rw [Bundle.contMDiffWithinAt_totalSpace] at hpx
  exact hpx.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.contMDiff_bilinSection_of_homSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.contMDiff_bilinSection_of_homSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.contMDiff_bilinSection_of_homSection ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.contMDiff_bilinSection_of_homSection

omit [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem riemannBiContrFibFixedFrame_apply_section_contMDiff (g₁ : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (Y : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun x : M => Tensor0SSpace 2 I x⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x
        (riemannBiContrFibFixedFrame (I := I) g₁ B x (Y x))) := by
  classical
  have hsummand : ∀ a b : Fin (Module.finrank ℝ E),
      ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
          (E := fun z : M => Tensor0SSpace 2 I z) x
          (riemannSummandFib (I := I) g₁ x (B a x) (B b x) (Y x))) := by
    intro a b
    have hscalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
        (fun x : M => Tensor0SSpace.toModel (Y x) ![(B a x : E), (B b x : E)]) := by
      have h := TensorMultilinear.contMDiff_section_apply (n := 2)
        (fun b => Y b) Y.contMDiff
        (![fun z => B a z, fun z => B b z])
        (by
          intro i
          fin_cases i
          · exact hB a
          · exact hB b)
      refine h.congr ?_
      intro x
      congr 1
      funext i
      fin_cases i <;> rfl
    have hbilin := contMDiff_bilinSection_of_homSection (I := I)
      (fun x => riemannKernelBilin (I := I) g₁ x (B a x) (B b x))
      (riemannKernelBilin_homSection_contMDiff (I := I) g₁ (hB a) (hB b))
    have hsmul := ContMDiff.smul_section (f := fun x => Tensor0SSpace.toModel (Y x)
        ![(B a x : E), (B b x : E)])
      (s := fun x => Tensor0SSpace.ofModel (I := I) (x := x)
        (DifferentialGeometry.Tensor.Multilinear.biForm₂ToModel (TangentSpace I x) (riemannKernelBilin (I := I) g₁ x (B a x) (B b x))))
      hscalar hbilin
    refine hsmul.congr ?_
    intro x
    rfl
  set S : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯ :=
    fun a b =>
      { toFun := fun x : M => riemannSummandFib (I := I) g₁ x (B a x) (B b x) (Y x)
        contMDiff_toFun := hsummand a b } with hS_def
  set Stot : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯ :=
    (2 : ℝ) • ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), S a b with hStot_def
  have hStot := Stot.contMDiff
  refine hStot.congr ?_
  intro x
  refine congrArg (TotalSpace.mk' (Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SSpace 2 I z) x) ?_
  rw [riemannBiContrFibFixedFrame, hStot_def, ContMDiffSection.coe_smul, Pi.smul_apply]
  have hcoeOuter : ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), S a b :
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
        Π z : M, Tensor0SSpace 2 I z) =
      ∑ a : Fin (Module.finrank ℝ E),
        ((∑ b : Fin (Module.finrank ℝ E), S a b :
          Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
          Π z : M, Tensor0SSpace 2 I z) :=
    map_sum (ContMDiffSection.coeAddHom I (Tensor0SModel 2 ℝ E) ∞
      (fun z : M => Tensor0SSpace 2 I z))
      (fun a => ∑ b : Fin (Module.finrank ℝ E), S a b) Finset.univ
  have hcoeInner : ∀ a : Fin (Module.finrank ℝ E),
      ((∑ b : Fin (Module.finrank ℝ E), S a b :
        Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
        Π z : M, Tensor0SSpace 2 I z) =
      ∑ b : Fin (Module.finrank ℝ E), ((S a b : Π z : M, Tensor0SSpace 2 I z)) := fun a =>
    map_sum (ContMDiffSection.coeAddHom I (Tensor0SModel 2 ℝ E) ∞
      (fun z : M => Tensor0SSpace 2 I z)) (fun b => S a b) Finset.univ
  have hsum : ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), S a b :
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
        Π z : M, Tensor0SSpace 2 I z) x =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (S a b : Π z : M, Tensor0SSpace 2 I z) x := by
    rw [hcoeOuter, Finset.sum_apply]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [hcoeInner a, Finset.sum_apply]
  rw [hsum, smul_apply, sum_apply]
  congr 1
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [sum_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannBiContrFibFixedFrame_apply_section_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannBiContrFibFixedFrame_apply_section_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannBiContrFibFixedFrame_apply_section_contMDiff ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannBiContrFibFixedFrame_apply_section_contMDiff

omit [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem riemannBiContrFibFixedFrame_contMDiff (g₁ : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (riemannBiContrFibFixedFrame (I := I) g₁ B x))) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I)
    (F₁ := Tensor0SModel 2 ℝ E) (V₁ := fun z : M => Tensor0SSpace 2 I z)
    (F₂ := Tensor0SModel 2 ℝ E) (V₂ := fun z : M => Tensor0SSpace 2 I z)
    (φ := fun x : M => riemannBiContrFibFixedFrame (I := I) g₁ B x)
  intro Y
  exact riemannBiContrFibFixedFrame_apply_section_contMDiff (I := I) g₁ B hB Y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannBiContrFibFixedFrame_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannBiContrFibFixedFrame_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannBiContrFibFixedFrame_contMDiff ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannBiContrFibFixedFrame_contMDiff

def frameRiemannKernel (g₁ : SmoothRiemannianMetric I M) (x : M) (v0 v1 : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun p => (g₁.inner x).flip v1 |>.comp
        ((riemannOp (LeviCivita (I := I) g₁) x v0 p))
      map_add' := fun p p' => by
        ext q
        simp only [ContinuousLinearMap.comp_apply, add_apply,
          (riemannOp (LeviCivita (I := I) g₁) x v0).map_add p p', map_add]
      map_smul' := fun c p => by
        ext q
        simp only [ContinuousLinearMap.comp_apply, smul_apply,
          RingHom.id_apply, (riemannOp (LeviCivita (I := I) g₁) x v0).map_smul c p, map_smul] }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.frameRiemannKernel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.frameRiemannKernel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.frameRiemannKernel ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.frameRiemannKernel

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem frameRiemannKernel_apply (g₁ : SmoothRiemannianMetric I M) (x : M)
    (v0 v1 p q : TangentSpace I x) :
    frameRiemannKernel (I := I) g₁ x v0 v1 p q =
      g₁.inner x (riemannOp (LeviCivita (I := I) g₁) x v0 p q) v1 := by
  rw [frameRiemannKernel, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.frameRiemannKernel_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.frameRiemannKernel_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.frameRiemannKernel_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.frameRiemannKernel_apply

def riemannBiContrFib (g₁ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  riemannBiContrFibFixedFrame (I := I) g₁ (smoothOrthoFrame (I := I) g₁ x) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannBiContrFib then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannBiContrFib"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannBiContrFib ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannBiContrFib

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private theorem riemannBiContrFibFixedFrame_eq_of_orthonormal
    (g₁ : SmoothRiemannianMetric I M) (y : M)
    (B C : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i j, g₁.inner y (B i y) (B j y) = if i = j then (1 : ℝ) else 0)
    (hC : ∀ i j, g₁.inner y (C i y) (C j y) = if i = j then (1 : ℝ) else 0) :
    riemannBiContrFibFixedFrame (I := I) g₁ B y =
      riemannBiContrFibFixedFrame (I := I) g₁ C y := by
  classical
  apply ContinuousLinearMap.ext
  intro D
  apply (tensor0SSpaceFiberContinuousLinearEquiv (I := I) 2 y).injective
  apply ContinuousMultilinearMap.ext
  intro v
  change Tensor0SSpace.eval (riemannBiContrFibFixedFrame (I := I) g₁ B y D) v =
    Tensor0SSpace.eval (riemannBiContrFibFixedFrame (I := I) g₁ C y D) v
  rw [riemannBiContrFibFixedFrame_eval, riemannBiContrFibFixedFrame_eval]
  apply congrArg (fun z : ℝ => 2 * z)
  let Dd : TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ :=
    (DifferentialGeometry.Tensor.Multilinear.biForm₂ToModel (TangentSpace I y)).symm
      (tensor0SSpaceFiberContinuousLinearEquiv (I := I) 2 y D)
  have hrewrite : ∀ (Bf : Fin (Module.finrank ℝ E) → TangentSpace I y),
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        g₁.inner y (riemannOp (LeviCivita (I := I) g₁) y (v 0) (Bf a) (Bf b)) (v 1) *
          Tensor0SSpace.eval D ![Bf a, Bf b] =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        frameRiemannKernel (I := I) g₁ y (v 0) (v 1) (Bf a) (Bf b) *
          Dd (Bf a) (Bf b) := by
    intro Bf
    refine Finset.sum_congr rfl (fun a _ => ?_)
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [frameRiemannKernel_apply (I := I) g₁ y (v 0) (v 1) (Bf a) (Bf b)]
    dsimp only [Dd]
    rw [DifferentialGeometry.Tensor.Multilinear.biForm₂ToModel_symm_apply]
    rfl
  rw [hrewrite (fun a => B a y), hrewrite (fun a => C a y)]
  exact double_frame_bilin_trace_indep (I := I) g₁ y
    (frameRiemannKernel (I := I) g₁ y (v 0) (v 1))
    Dd
    (fun a => B a y) (fun a => C a y) hB hC

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannBiContrFibFixedFrame_eq_of_orthonormal
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannBiContrFibFixedFrame_eq_of_orthonormal target :: scope.openDecls } }

omit [CompactSpace M] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem riemannBiContrFib_eq_fixedFrame_on_neighborhood (g₁ : SmoothRiemannianMetric I M) (x₀ : M)
    {y : M} (hy : y ∈ smoothOrthoFrameNeighborhood (I := I) (M := M) x₀) :
    riemannBiContrFib (I := I) g₁ y =
      riemannBiContrFibFixedFrame (I := I) g₁ (smoothOrthoFrame (I := I) g₁ x₀) y := by
  rw [riemannBiContrFib]
  exact riemannBiContrFibFixedFrame_eq_of_orthonormal (I := I) g₁ y
    (smoothOrthoFrame (I := I) g₁ y) (smoothOrthoFrame (I := I) g₁ x₀)
    (fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g₁ y i j)
    (fun i j => smoothOrthoFrame_orthonormal (I := I) g₁ x₀ hy i j)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannBiContrFib_eq_fixedFrame_on_neighborhood then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannBiContrFib_eq_fixedFrame_on_neighborhood"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannBiContrFib_eq_fixedFrame_on_neighborhood ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannBiContrFib_eq_fixedFrame_on_neighborhood

omit [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
theorem riemannBiContrFib_contMDiff (g₁ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (riemannBiContrFib (I := I) g₁ x))) := by
  classical
  intro x₀
  have h_fixed : ContMDiffAt I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (riemannBiContrFibFixedFrame (I := I) g₁
          (smoothOrthoFrame (I := I) g₁ x₀) x))) x₀ :=
    riemannBiContrFibFixedFrame_contMDiff (I := I) g₁ (smoothOrthoFrame (I := I) g₁ x₀)
      (fun i => smoothOrthoFrame_smooth (I := I) g₁ x₀ i) x₀
  refine h_fixed.congr_of_eventuallyEq ?_
  filter_upwards [smoothOrthoFrameNeighborhood_mem_nhds (I := I) (M := M) x₀] with y hy
  exact congrArg (TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
    (E := fun z : M => TensorRSSpace 2 2 I z) y)
    (congrArg TensorRSSpace.ofCLM
      (riemannBiContrFib_eq_fixedFrame_on_neighborhood (I := I) g₁ x₀ hy))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannBiContrFib_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannBiContrFib_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannBiContrFib_contMDiff ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannBiContrFib_contMDiff

def ricciOrderZeroRiemannCoeffField (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace 2 2 I x from TensorRSSpace.ofCLM (riemannBiContrFib (I := I) g₁ x))
      contMDiff_toFun := riemannBiContrFib_contMDiff (I := I) g₁ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciOrderZeroRiemannCoeffField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciOrderZeroRiemannCoeffField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciOrderZeroRiemannCoeffField ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciOrderZeroRiemannCoeffField

omit [I.Boundaryless] [SigmaCompactSpace M] in
@[simp] theorem ricciOrderZeroRiemannCoeffField_toSection (g₀ g₁ : SmoothRiemannianMetric I M)
    (x : M) :
    (ricciOrderZeroRiemannCoeffField (I := I) (M := M) g₀ g₁).toSection x =
      (show TensorRSSpace 2 2 I x from TensorRSSpace.ofCLM (riemannBiContrFib (I := I) g₁ x)) :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciOrderZeroRiemannCoeffField_toSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciOrderZeroRiemannCoeffField_toSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciOrderZeroRiemannCoeffField_toSection ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciOrderZeroRiemannCoeffField_toSection

omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem exists_ricciOrderZeroRiemannCoeff (g₀ g₁ : SmoothRiemannianMetric I M) :
    ∃ R_Rm : SmoothCcTensor g₀ 2 2,
      ∀ (W : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x),
        unitModel (I := I) (M := M) g₀ 2
            (operatorFieldApply (I := I) (M := M) g₀ 2 2 R_Rm W) x v =
          2 * ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            g₁.inner x
                (riemannOp (LeviCivita (I := I) g₁) x (v 0)
                  (smoothOrthoFrame (I := I) g₁ x a x)
                  (smoothOrthoFrame (I := I) g₁ x b x)) (v 1) *
              unitModel (I := I) (M := M) g₀ 2 W x
                (fun j => if j = 0 then smoothOrthoFrame (I := I) g₁ x a x
                  else smoothOrthoFrame (I := I) g₁ x b x) :=
  by
  classical
  refine ⟨ricciOrderZeroRiemannCoeffField (I := I) (M := M) g₀ g₁, fun W x v => ?_⟩
  rw [unitModel, operatorFieldApplication_toSection]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (ricciOrderZeroRiemannCoeffField (I := I) (M := M) g₀ g₁).toSection x).comp
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x))
        (unitTensor (I := I) (M := M) x) =
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (ricciOrderZeroRiemannCoeffField (I := I) (M := M) g₀ g₁).toSection x)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x)) from rfl]
  rw [ricciOrderZeroRiemannCoeffField_toSection]
  rw [show (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (show TensorRSSpace 2 2 I x from TensorRSSpace.ofCLM (riemannBiContrFib (I := I) g₁ x)))
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x)) =
      riemannBiContrFib (I := I) g₁ x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x)) from rfl]
  rw [riemannBiContrFib]
  change Tensor0SSpace.eval
      (riemannBiContrFibFixedFrame (I := I) g₁
        (smoothOrthoFrame (I := I) g₁ x) x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x))) v = _
  rw [riemannBiContrFibFixedFrame_eval]
  refine congrArg (fun t => (2 : ℝ) * t) ?_
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine Finset.sum_congr rfl (fun b _ => ?_)
  congr 1
  rw [unitModel]
  congr 1
  funext j
  fin_cases j <;> simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_ricciOrderZeroRiemannCoeff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_ricciOrderZeroRiemannCoeff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_ricciOrderZeroRiemannCoeff ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_ricciOrderZeroRiemannCoeff

noncomputable def ricciOrderZeroRiemannCoeff (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 :=
  ricciOrderZeroRiemannCoeffField (I := I) (M := M) g₀ g₁

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciOrderZeroRiemannCoeff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciOrderZeroRiemannCoeff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciOrderZeroRiemannCoeff ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciOrderZeroRiemannCoeff

omit [I.Boundaryless] [SigmaCompactSpace M] in
@[simp] theorem ricciOrderZeroRiemannCoeff_toSection (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₁).toSection x =
      (show TensorRSSpace 2 2 I x from TensorRSSpace.ofCLM (riemannBiContrFib (I := I) g₁ x)) :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciOrderZeroRiemannCoeff_toSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciOrderZeroRiemannCoeff_toSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciOrderZeroRiemannCoeff_toSection ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciOrderZeroRiemannCoeff_toSection


omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem ricciOrderZeroRiemannCoeff_operatorFieldApplication_eq (g₀ g₁ : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 2 2
          (ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₁) W) x v =
      2 * ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        g₁.inner x
            (riemannOp (LeviCivita (I := I) g₁) x (v 0)
              (smoothOrthoFrame (I := I) g₁ x a x)
              (smoothOrthoFrame (I := I) g₁ x b x)) (v 1) *
          unitModel (I := I) (M := M) g₀ 2 W x
            (fun j => if j = 0 then smoothOrthoFrame (I := I) g₁ x a x
              else smoothOrthoFrame (I := I) g₁ x b x) := by
  rw [unitModel, operatorFieldApplication_toSection]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₁).toSection x).comp
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x))
        (unitTensor (I := I) (M := M) x) =
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₁).toSection x)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x)) from rfl]
  rw [ricciOrderZeroRiemannCoeff_toSection]
  rw [show (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (show TensorRSSpace 2 2 I x from TensorRSSpace.ofCLM (riemannBiContrFib (I := I) g₁ x)))
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x)) =
      riemannBiContrFib (I := I) g₁ x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x)) from rfl]
  rw [riemannBiContrFib]
  change Tensor0SSpace.eval
      (riemannBiContrFibFixedFrame (I := I) g₁
        (smoothOrthoFrame (I := I) g₁ x) x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x))) v = _
  rw [riemannBiContrFibFixedFrame_eval]
  refine congrArg (fun t => (2 : ℝ) * t) ?_
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine Finset.sum_congr rfl (fun b _ => ?_)
  congr 1
  rw [unitModel]
  congr 1
  funext j
  fin_cases j <;> simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciOrderZeroRiemannCoeff_operatorFieldApplication_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciOrderZeroRiemannCoeff_operatorFieldApplication_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciOrderZeroRiemannCoeff_operatorFieldApplication_eq ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciOrderZeroRiemannCoeff_operatorFieldApplication_eq

end NormedRiemannCoefficients

section InnerProductSpaceSymmetrization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instCompleteSpace_differentialGeometry_1 : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instCompleteSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instCompleteSpace_differentialGeometry_1 target :: scope.openDecls } }

noncomputable def symmAbsorbedPrincipalCoeffPure (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) : SmoothCcTensor g₀ 4 2 :=
  symmAbsorbedCoeff (I := I) (M := M) g₀ 2
    (cometricDoubleTraceCoefficient (I := I) (M := M) g₀ g₁)
    (Classical.choose (exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) S 2))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.symmAbsorbedPrincipalCoeffPure then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.symmAbsorbedPrincipalCoeffPure"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.symmAbsorbedPrincipalCoeffPure ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.symmAbsorbedPrincipalCoeffPure


omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem symmAbsorbedPrincipalCoeffPure_operatorFieldApplication_eq (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 4 2
          (symmAbsorbedPrincipalCoeffPure (I := I) (M := M) g₀ g₁ S)
          (iteratedCovGrad (I := I) g₀ 0 2 2 S)) x v =
      unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 4 2
          (cometricDoubleTraceCoefficient (I := I) (M := M) g₀ g₁)
          (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ S))) x v := by
  exact symmAbsorbedCoeff_operatorFieldApplication_eq (I := I) (M := M) g₀ 2 S
    (cometricDoubleTraceCoefficient (I := I) (M := M) g₀ g₁)
    (Classical.choose (exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) S 2))
    (Classical.choose_spec (exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) S 2)) x v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.symmAbsorbedPrincipalCoeffPure_operatorFieldApplication_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.symmAbsorbedPrincipalCoeffPure_operatorFieldApplication_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.symmAbsorbedPrincipalCoeffPure_operatorFieldApplication_eq ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.symmAbsorbedPrincipalCoeffPure_operatorFieldApplication_eq

noncomputable def symmAbsorbedOrder0CurvCoeff (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) : SmoothCcTensor g₀ 2 2 :=
  symmAbsorbedCoeff (I := I) (M := M) g₀ 0
    (ricciOrderZeroCurvCoeff (I := I) (M := M) g₀ g₁)
    (Classical.choose (exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) S 0))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.symmAbsorbedOrder0CurvCoeff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.symmAbsorbedOrder0CurvCoeff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.symmAbsorbedOrder0CurvCoeff ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.symmAbsorbedOrder0CurvCoeff


omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem symmAbsorbedOrder0CurvCoeff_operatorFieldApplication_eq (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 2 2
          (symmAbsorbedOrder0CurvCoeff (I := I) (M := M) g₀ g₁ S)
          (iteratedCovGrad (I := I) g₀ 0 2 0 S)) x v =
      unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 2 2
          (ricciOrderZeroCurvCoeff (I := I) (M := M) g₀ g₁)
          (iteratedCovGrad (I := I) g₀ 0 2 0 (ccTensor02Symm (I := I) (M := M) g₀ S))) x v := by
  exact symmAbsorbedCoeff_operatorFieldApplication_eq (I := I) (M := M) g₀ 0 S
    (ricciOrderZeroCurvCoeff (I := I) (M := M) g₀ g₁)
    (Classical.choose (exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) S 0))
    (Classical.choose_spec (exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) S 0)) x v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.symmAbsorbedOrder0CurvCoeff_operatorFieldApplication_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.symmAbsorbedOrder0CurvCoeff_operatorFieldApplication_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.symmAbsorbedOrder0CurvCoeff_operatorFieldApplication_eq ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.symmAbsorbedOrder0CurvCoeff_operatorFieldApplication_eq

noncomputable def symmAbsorbedOrder0RiemannCoeff (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) : SmoothCcTensor g₀ 2 2 :=
  symmAbsorbedCoeff (I := I) (M := M) g₀ 0
    (ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₁)
    (Classical.choose (exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) S 0))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.symmAbsorbedOrder0RiemannCoeff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.symmAbsorbedOrder0RiemannCoeff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.symmAbsorbedOrder0RiemannCoeff ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.symmAbsorbedOrder0RiemannCoeff


omit [SigmaCompactSpace M] in
theorem symmAbsorbedOrder0RiemannCoeff_operatorFieldApplication_eq (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 2 2
          (symmAbsorbedOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ S)
          (iteratedCovGrad (I := I) g₀ 0 2 0 S)) x v =
      unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 2 2
          (ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₁)
          (iteratedCovGrad (I := I) g₀ 0 2 0 (ccTensor02Symm (I := I) (M := M) g₀ S))) x v := by
  exact symmAbsorbedCoeff_operatorFieldApplication_eq (I := I) (M := M) g₀ 0 S
    (ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₁)
    (Classical.choose (exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) S 0))
    (Classical.choose_spec (exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) S 0)) x v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.symmAbsorbedOrder0RiemannCoeff_operatorFieldApplication_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.symmAbsorbedOrder0RiemannCoeff_operatorFieldApplication_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.symmAbsorbedOrder0RiemannCoeff_operatorFieldApplication_eq ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.symmAbsorbedOrder0RiemannCoeff_operatorFieldApplication_eq

end InnerProductSpaceSymmetrization

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
