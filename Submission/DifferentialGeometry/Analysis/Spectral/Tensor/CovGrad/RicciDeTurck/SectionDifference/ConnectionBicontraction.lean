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
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurck.SectionDifference.RiemannFixedFrameBicontraction
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurck.SectionDifference.DeTurckLieBicontraction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Connection.Realization
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
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.DeTurck

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


omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem connectionDifferenceQuad_telescope (g₀ g₁ g₁' : SmoothRiemannianMetric I M) (x : M)
    (p q r : TangentSpace I x) :
    PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x
        (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x p q) r
      - PDE.DeTurck.connectionDifference (I := I) g₁' g₀ x
        (PDE.DeTurck.connectionDifference (I := I) g₁' g₀ x p q) r =
      PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x
          (PDE.DeTurck.connectionDifference (I := I) g₁ g₁' x p q) r
        + PDE.DeTurck.connectionDifference (I := I) g₁ g₁' x
            (PDE.DeTurck.connectionDifference (I := I) g₁' g₀ x p q) r := by
  rw [connectionDifference_bilinear_diff_split (I := I) g₀ g₁ g₁' x
        (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x p q)
        (PDE.DeTurck.connectionDifference (I := I) g₁' g₀ x p q) r]
  rw [connectionDifference_endpoint_cocycle (I := I) g₀ g₁ g₁' x p q]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceQuad_telescope then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceQuad_telescope"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceQuad_telescope ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceQuad_telescope


omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem block3LegSummand_telescope (g₀ g₁ g₁' : SmoothRiemannianMetric I M) (x : M)
    (Xv0 Xv1 Xei : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x
          (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁) Xv0 Xv1 x) (Xei x)
        - PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x
          (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁) Xei Xv1 x) (Xv0 x))
      - (PDE.DeTurck.connectionDifference (I := I) g₁' g₀ x
          (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁') Xv0 Xv1 x) (Xei x)
        - PDE.DeTurck.connectionDifference (I := I) g₁' g₀ x
          (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁') Xei Xv1 x) (Xv0 x)) =
      (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x
            (PDE.DeTurck.connectionDifference (I := I) g₁ g₁' x (Xv1 x) (Xv0 x)) (Xei x)
          + PDE.DeTurck.connectionDifference (I := I) g₁ g₁' x
              (PDE.DeTurck.connectionDifference (I := I) g₁' g₀ x (Xv1 x) (Xv0 x)) (Xei x))
        - (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x
              (PDE.DeTurck.connectionDifference (I := I) g₁ g₁' x (Xv1 x) (Xei x)) (Xv0 x)
            + PDE.DeTurck.connectionDifference (I := I) g₁ g₁' x
                (PDE.DeTurck.connectionDifference (I := I) g₁' g₀ x (Xv1 x) (Xei x)) (Xv0 x)) := by
  have h1 := connectionDifferenceQuad_telescope (I := I) g₀ g₁ g₁' x (Xv1 x) (Xv0 x) (Xei x)
  have h2 := connectionDifferenceQuad_telescope (I := I) g₀ g₁ g₁' x (Xv1 x) (Xei x) (Xv0 x)
  change (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x
          (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (Xv1 x) (Xv0 x)) (Xei x)
        - PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x
          (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (Xv1 x) (Xei x)) (Xv0 x))
      - (PDE.DeTurck.connectionDifference (I := I) g₁' g₀ x
          (PDE.DeTurck.connectionDifference (I := I) g₁' g₀ x (Xv1 x) (Xv0 x)) (Xei x)
        - PDE.DeTurck.connectionDifference (I := I) g₁' g₀ x
          (PDE.DeTurck.connectionDifference (I := I) g₁' g₀ x (Xv1 x) (Xei x)) (Xv0 x)) = _
  rw [sub_sub_sub_comm, h1, h2]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.block3LegSummand_telescope then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.block3LegSummand_telescope"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.block3LegSummand_telescope ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.block3LegSummand_telescope

def connectionDifferenceBiKernelBilin (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M) (x : M)
    (p q : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  (g₀.inner x).comp
    ((PDE.DeTurck.connectionDifference (I := I) gj g₀ x)
      (PDE.DeTurck.connectionDifference (I := I) g₁ g₁' x p q))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceBiKernelBilin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceBiKernelBilin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceBiKernelBilin ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceBiKernelBilin

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
@[simp] theorem connectionDifferenceBiKernelBilin_apply (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M) (x : M)
    (p q v0 v1 : TangentSpace I x) :
    connectionDifferenceBiKernelBilin (I := I) gj g₀ g₁ g₁' x p q v0 v1 =
      g₀.inner x (PDE.DeTurck.connectionDifference (I := I) gj g₀ x
        (PDE.DeTurck.connectionDifference (I := I) g₁ g₁' x p q) v0) v1 := by
  rw [connectionDifferenceBiKernelBilin, ContinuousLinearMap.comp_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceBiKernelBilin_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceBiKernelBilin_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceBiKernelBilin_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceBiKernelBilin_apply

def connectionDifferenceBiSummandFib (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M) (x : M)
    (p q : TangentSpace I x) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  haveI : FiniteDimensional ℝ (Tensor0SSpace 2 I x) := inferInstance
  LinearMap.toContinuousLinearMap
    { toFun := fun D =>
        (Tensor0SSpace.eval D ![p, q]) •
          Tensor0SSpace.ofModel (I := I) (x := x)
            (DifferentialGeometry.Tensor.Multilinear.biForm₂ToModel E (tangentBilinearFormToModel (I := I) x
              (connectionDifferenceBiKernelBilin (I := I) gj g₀ g₁ g₁' x p q)))
      map_add' := fun D D' => by
        rw [Tensor0SSpace.eval_add, add_smul]
      map_smul' := fun c D => by
        rw [Tensor0SSpace.eval_smul, smul_eq_mul,
          RingHom.id_apply, _root_.SemigroupAction.mul_smul] }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceBiSummandFib then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceBiSummandFib"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceBiSummandFib ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceBiSummandFib

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
@[simp] theorem connectionDifferenceBiSummandFib_toModel (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M) (x : M)
    (p q : TangentSpace I x) (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel (connectionDifferenceBiSummandFib (I := I) gj g₀ g₁ g₁' x p q D) v =
      (Tensor0SSpace.eval D ![p, q]) *
        g₀.inner x (PDE.DeTurck.connectionDifference (I := I) gj g₀ x
          (PDE.DeTurck.connectionDifference (I := I) g₁ g₁' x p q)
          ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 0)))
          ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 1)) := by
  rw [connectionDifferenceBiSummandFib, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
    Tensor0SSpace.toModel_smul, smul_apply, Tensor0SSpace.toModel_ofModel,
    DifferentialGeometry.Tensor.Multilinear.biForm₂ToModel_apply, tangentBilinearFormToModel_apply]
  have hkernel := connectionDifferenceBiKernelBilin_apply (I := I) gj g₀ g₁ g₁' x p q
    ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 0))
    ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 1))
  simpa only [smul_eq_mul, tangentSpaceModelContinuousLinearEquiv_symm_apply] using
    congrArg (fun z : ℝ => Tensor0SSpace.eval D ![p, q] * z) hkernel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceBiSummandFib_toModel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceBiSummandFib_toModel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceBiSummandFib_toModel ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceBiSummandFib_toModel

def connectionDifferenceBiContrFibFixedFrame (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
    connectionDifferenceBiSummandFib (I := I) gj g₀ g₁ g₁' x (B a x) (B b x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceBiContrFibFixedFrame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceBiContrFibFixedFrame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceBiContrFibFixedFrame ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceBiContrFibFixedFrame

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
theorem connectionDifferenceBiContrFibFixedFrame_toModel (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M)
    (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel (connectionDifferenceBiContrFibFixedFrame (I := I) gj g₀ g₁ g₁' B x D) v =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        g₀.inner x (PDE.DeTurck.connectionDifference (I := I) gj g₀ x
            (PDE.DeTurck.connectionDifference (I := I) g₁ g₁' x (B a x) (B b x))
            ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 0)))
            ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 1)) *
          Tensor0SSpace.eval D ![B a x, B b x] := by
  classical
  rw [connectionDifferenceBiContrFibFixedFrame, sum_apply, ← Tensor0SSpace.toModelL_apply,
    map_sum, sum_apply]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [sum_apply, Tensor0SSpace.toModelL_apply, ← Tensor0SSpace.toModelL_apply,
    map_sum, sum_apply]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Tensor0SSpace.toModelL_apply, connectionDifferenceBiSummandFib_toModel]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceBiContrFibFixedFrame_toModel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceBiContrFibFixedFrame_toModel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceBiContrFibFixedFrame_toModel ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceBiContrFibFixedFrame_toModel

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
theorem connectionDifferenceBiContrFibFixedFrame_eval
    (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M)
    (D : Tensor0SSpace 2 I x) (v : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.eval (connectionDifferenceBiContrFibFixedFrame (I := I) gj g₀ g₁ g₁' B x D) v =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        g₀.inner x (PDE.DeTurck.connectionDifference (I := I) gj g₀ x
            (PDE.DeTurck.connectionDifference (I := I) g₁ g₁' x (B a x) (B b x)) (v 0)) (v 1) *
          Tensor0SSpace.eval D ![B a x, B b x] := by
  let vE : Fin 2 → E :=
    fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x (v i)
  have h := connectionDifferenceBiContrFibFixedFrame_toModel
    (I := I) gj g₀ g₁ g₁' B x D vE
  simpa [vE, Tensor0SSpace.toModel_apply_tangent] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceBiContrFibFixedFrame_eval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceBiContrFibFixedFrame_eval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceBiContrFibFixedFrame_eval ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceBiContrFibFixedFrame_eval

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem connectionDifferenceBiKernelBilin_homSection_contMDiff (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M)
    {p q : Π b : M, TangentSpace I b}
    (hp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% p))
    (hq : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% q)) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun b : M => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ)
        x (connectionDifferenceBiKernelBilin (I := I) gj g₀ g₁ g₁' x (p x) (q x))) := by
  classical
  apply contMDiff_continuousLinearMap_section_of_apply
    (V₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
    (φ := fun x : M => connectionDifferenceBiKernelBilin (I := I) gj g₀ g₁ g₁' x (p x) (q x))
  intro V0
  apply contMDiff_continuousLinearMap_section_of_apply
    (V₂ := fun _ : M => ℝ)
    (φ := fun x : M => connectionDifferenceBiKernelBilin (I := I) gj g₀ g₁ g₁' x (p x) (q x) (V0 x))
  intro W
  have hinner : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b => PDE.DeTurck.connectionDifference (I := I) g₁ g₁' b (p b) (q b))) :=
    PDE.DeTurck.connectionDifference_contMDiff (I := I) g₁ g₁' hp hq
  have houter : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b => PDE.DeTurck.connectionDifference (I := I) gj g₀ b
        (PDE.DeTurck.connectionDifference (I := I) g₁ g₁' b (p b) (q b)) (V0 b))) :=
    PDE.DeTurck.connectionDifference_contMDiff (I := I) gj g₀ hinner V0.contMDiff
  have h_scalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => g₀.inner x
        (PDE.DeTurck.connectionDifference (I := I) gj g₀ x
          (PDE.DeTurck.connectionDifference (I := I) g₁ g₁' x (p x) (q x)) (V0 x)) (W x)) :=
    contMDiff_g_inner_of_smooth_sections (I := I) g₀
      ⟨fun b => PDE.DeTurck.connectionDifference (I := I) gj g₀ b
        (PDE.DeTurck.connectionDifference (I := I) g₁ g₁' b (p b) (q b)) (V0 b), houter⟩
      ⟨fun b => W b, W.contMDiff⟩
  intro x
  rw [_root_.Bundle.contMDiffAt_section]
  refine (h_scalar.contMDiffAt).congr_of_eventuallyEq ?_
  filter_upwards with y
  change connectionDifferenceBiKernelBilin (I := I) gj g₀ g₁ g₁' y (p y) (q y) (V0 y) (W y) =
    (_root_.FiberBundle.trivializationAt ℝ (Bundle.Trivial M ℝ) x ⟨y, _⟩).2
  rw [connectionDifferenceBiKernelBilin_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceBiKernelBilin_homSection_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceBiKernelBilin_homSection_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceBiKernelBilin_homSection_contMDiff ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceBiKernelBilin_homSection_contMDiff

omit [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem connectionDifferenceBiContrFibFixedFrame_apply_section_contMDiff
    (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (Y : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun x : M => Tensor0SSpace 2 I x⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x
        (connectionDifferenceBiContrFibFixedFrame (I := I) gj g₀ g₁ g₁' B x (Y x))) := by
  classical
  have hsummand : ∀ a b : Fin (Module.finrank ℝ E),
      ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
          (E := fun z : M => Tensor0SSpace 2 I z) x
          (connectionDifferenceBiSummandFib (I := I) gj g₀ g₁ g₁' x (B a x) (B b x) (Y x))) := by
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
      (fun x => connectionDifferenceBiKernelBilin (I := I) gj g₀ g₁ g₁' x (B a x) (B b x))
      (connectionDifferenceBiKernelBilin_homSection_contMDiff (I := I) gj g₀ g₁ g₁' (hB a) (hB b))
    have hsmul := ContMDiff.smul_section (f := fun x => Tensor0SSpace.toModel (Y x)
        ![(B a x : E), (B b x : E)])
      (s := fun x => Tensor0SSpace.ofModel (I := I) (x := x)
        (DifferentialGeometry.Tensor.Multilinear.biForm₂ToModel (TangentSpace I x)
          (connectionDifferenceBiKernelBilin (I := I) gj g₀ g₁ g₁' x (B a x) (B b x))))
      hscalar hbilin
    refine hsmul.congr ?_
    intro x
    rfl
  set S : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯ :=
    fun a b =>
      { toFun := fun x : M => connectionDifferenceBiSummandFib (I := I) gj g₀ g₁ g₁' x (B a x) (B b x) (Y x)
        contMDiff_toFun := hsummand a b } with hS_def
  set Stot : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯ :=
    ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), S a b with hStot_def
  have hStot := Stot.contMDiff
  refine hStot.congr ?_
  intro x
  refine congrArg (TotalSpace.mk' (Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SSpace 2 I z) x) ?_
  rw [connectionDifferenceBiContrFibFixedFrame, hStot_def]
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
  rw [hsum, sum_apply]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [sum_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceBiContrFibFixedFrame_apply_section_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceBiContrFibFixedFrame_apply_section_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceBiContrFibFixedFrame_apply_section_contMDiff ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceBiContrFibFixedFrame_apply_section_contMDiff

omit [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem connectionDifferenceBiContrFibFixedFrame_contMDiff (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (connectionDifferenceBiContrFibFixedFrame (I := I) gj g₀ g₁ g₁' B x))) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I)
    (F₁ := Tensor0SModel 2 ℝ E) (V₁ := fun z : M => Tensor0SSpace 2 I z)
    (F₂ := Tensor0SModel 2 ℝ E) (V₂ := fun z : M => Tensor0SSpace 2 I z)
    (φ := fun x : M => connectionDifferenceBiContrFibFixedFrame (I := I) gj g₀ g₁ g₁' B x)
  intro Y
  exact connectionDifferenceBiContrFibFixedFrame_apply_section_contMDiff (I := I) gj g₀ g₁ g₁' B hB Y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceBiContrFibFixedFrame_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceBiContrFibFixedFrame_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceBiContrFibFixedFrame_contMDiff ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceBiContrFibFixedFrame_contMDiff

def frameConnectionDifferenceBiKernel (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M) (x : M)
    (v0 v1 : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun p => (g₀.inner x).flip v1 |>.comp
        ((PDE.DeTurck.connectionDifference (I := I) gj g₀ x).flip v0 |>.comp
          (PDE.DeTurck.connectionDifference (I := I) g₁ g₁' x p))
      map_add' := fun p p' => by
        ext q
        simp only [ContinuousLinearMap.comp_apply, add_apply,
          (PDE.DeTurck.connectionDifference (I := I) g₁ g₁' x).map_add p p', map_add]
      map_smul' := fun c p => by
        ext q
        simp only [ContinuousLinearMap.comp_apply, smul_apply,
          RingHom.id_apply, (PDE.DeTurck.connectionDifference (I := I) g₁ g₁' x).map_smul c p, map_smul] }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.frameConnectionDifferenceBiKernel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.frameConnectionDifferenceBiKernel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.frameConnectionDifferenceBiKernel ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.frameConnectionDifferenceBiKernel

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
theorem frameConnectionDifferenceBiKernel_apply (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M) (x : M)
    (v0 v1 p q : TangentSpace I x) :
    frameConnectionDifferenceBiKernel (I := I) gj g₀ g₁ g₁' x v0 v1 p q =
      g₀.inner x (PDE.DeTurck.connectionDifference (I := I) gj g₀ x
        (PDE.DeTurck.connectionDifference (I := I) g₁ g₁' x p q) v0) v1 := by
  rw [frameConnectionDifferenceBiKernel, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.flip_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.frameConnectionDifferenceBiKernel_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.frameConnectionDifferenceBiKernel_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.frameConnectionDifferenceBiKernel_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.frameConnectionDifferenceBiKernel_apply

def connectionDifferenceBiContrFib (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  connectionDifferenceBiContrFibFixedFrame (I := I) gj g₀ g₁ g₁' (smoothOrthoFrame (I := I) g₀ x) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceBiContrFib then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceBiContrFib"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceBiContrFib ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceBiContrFib

section

private local instance frameTangentSpaceNormedAddCommGroup (x : M) :
    NormedAddCommGroup (TangentSpace I x) := by
  change NormedAddCommGroup E
  infer_instance

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.frameTangentSpaceNormedAddCommGroup
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.frameTangentSpaceNormedAddCommGroup target :: scope.openDecls } }

private local instance frameTangentSpaceNormedSpace (x : M) :
    NormedSpace ℝ (TangentSpace I x) := by
  change NormedSpace ℝ E
  infer_instance

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.frameTangentSpaceNormedSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.frameTangentSpaceNormedSpace target :: scope.openDecls } }

private def frameBilinFormToModel (x : M) :
    (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) ≃ₗ[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin 2 => TangentSpace I x) ℝ :=
  DifferentialGeometry.Tensor.Multilinear.biForm₂ToModel (TangentSpace I x)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.frameBilinFormToModel
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.frameBilinFormToModel target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M]
    [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
private theorem frameBilinFormToModel_symm_apply (x : M)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => TangentSpace I x) ℝ)
    (v w : TangentSpace I x) :
    (frameBilinFormToModel (I := I) x).symm T v w = T ![v, w] := by
  exact DifferentialGeometry.Tensor.Multilinear.biForm₂ToModel_symm_apply (TangentSpace I x) T v w

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.frameBilinFormToModel_symm_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.frameBilinFormToModel_symm_apply target :: scope.openDecls } }

end

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
theorem connectionDifferenceBiContrFib_eq_fixedFrame_on_neighborhood (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M)
    (x₀ : M) {y : M} (hy : y ∈ smoothOrthoFrameNeighborhood (I := I) (M := M) x₀) :
    connectionDifferenceBiContrFib (I := I) gj g₀ g₁ g₁' y =
      connectionDifferenceBiContrFibFixedFrame (I := I) gj g₀ g₁ g₁' (smoothOrthoFrame (I := I) g₀ x₀) y := by
  classical
  apply ContinuousLinearMap.ext
  intro D
  apply (tensor0SSpaceFiberContinuousLinearEquiv (I := I) 2 y).injective
  apply ContinuousMultilinearMap.ext
  intro v
  change Tensor0SSpace.eval (connectionDifferenceBiContrFib (I := I) gj g₀ g₁ g₁' y D) v =
    Tensor0SSpace.eval
      (connectionDifferenceBiContrFibFixedFrame (I := I) gj g₀ g₁ g₁'
        (smoothOrthoFrame (I := I) g₀ x₀) y D) v
  rw [connectionDifferenceBiContrFib, connectionDifferenceBiContrFibFixedFrame_eval,
    connectionDifferenceBiContrFibFixedFrame_eval]
  let DFiber : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => TangentSpace I y) ℝ :=
    tensor0SSpaceFiberContinuousLinearEquiv (I := I) 2 y D
  have hrewrite : ∀ (Bf : Fin (Module.finrank ℝ E) → TangentSpace I y),
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        g₀.inner y (PDE.DeTurck.connectionDifference (I := I) gj g₀ y
            (PDE.DeTurck.connectionDifference (I := I) g₁ g₁' y (Bf a) (Bf b)) (v 0)) (v 1) *
          Tensor0SSpace.eval D ![Bf a, Bf b] =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        frameConnectionDifferenceBiKernel (I := I) gj g₀ g₁ g₁' y (v 0) (v 1) (Bf a) (Bf b) *
          (frameBilinFormToModel (I := I) y).symm DFiber (Bf a) (Bf b) := by
    intro Bf
    refine Finset.sum_congr rfl (fun a _ => ?_)
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [frameConnectionDifferenceBiKernel_apply (I := I) gj g₀ g₁ g₁' y (v 0) (v 1) (Bf a) (Bf b),
      frameBilinFormToModel_symm_apply (I := I) y DFiber (Bf a) (Bf b)]
    rfl
  rw [hrewrite (fun a => smoothOrthoFrame (I := I) g₀ y a y),
    hrewrite (fun a => smoothOrthoFrame (I := I) g₀ x₀ a y)]
  exact double_frame_bilin_trace_indep (I := I) g₀ y
    (frameConnectionDifferenceBiKernel (I := I) gj g₀ g₁ g₁' y (v 0) (v 1))
    ((frameBilinFormToModel (I := I) y).symm DFiber)
    (fun a => smoothOrthoFrame (I := I) g₀ y a y)
    (fun a => smoothOrthoFrame (I := I) g₀ x₀ a y)
    (fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g₀ y i j)
    (fun i j => smoothOrthoFrame_orthonormal (I := I) g₀ x₀ hy i j)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceBiContrFib_eq_fixedFrame_on_neighborhood then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceBiContrFib_eq_fixedFrame_on_neighborhood"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceBiContrFib_eq_fixedFrame_on_neighborhood ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceBiContrFib_eq_fixedFrame_on_neighborhood

omit [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
theorem connectionDifferenceBiContrFib_contMDiff (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (connectionDifferenceBiContrFib (I := I) gj g₀ g₁ g₁' x))) := by
  classical
  intro x₀
  have h_fixed : ContMDiffAt I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (connectionDifferenceBiContrFibFixedFrame (I := I) gj g₀ g₁ g₁'
          (smoothOrthoFrame (I := I) g₀ x₀) x))) x₀ :=
    connectionDifferenceBiContrFibFixedFrame_contMDiff (I := I) gj g₀ g₁ g₁' (smoothOrthoFrame (I := I) g₀ x₀)
      (fun i => smoothOrthoFrame_smooth (I := I) g₀ x₀ i) x₀
  refine h_fixed.congr_of_eventuallyEq ?_
  filter_upwards [smoothOrthoFrameNeighborhood_mem_nhds (I := I) (M := M) x₀] with y hy
  exact congrArg (TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
    (E := fun z : M => TensorRSSpace 2 2 I z) y)
    (congrArg TensorRSSpace.ofCLM
      (connectionDifferenceBiContrFib_eq_fixedFrame_on_neighborhood (I := I) gj g₀ g₁ g₁' x₀ hy))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceBiContrFib_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceBiContrFib_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceBiContrFib_contMDiff ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceBiContrFib_contMDiff

def connectionDifferenceBiContrCoeffField (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (connectionDifferenceBiContrFib (I := I) gj g₀ g₁ g₁' x))
      contMDiff_toFun := connectionDifferenceBiContrFib_contMDiff (I := I) gj g₀ g₁ g₁' }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceBiContrCoeffField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceBiContrCoeffField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceBiContrCoeffField ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceBiContrCoeffField

omit [I.Boundaryless] [SigmaCompactSpace M] in
@[simp] theorem connectionDifferenceBiContrCoeffField_toSection (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M)
    (x : M) :
    (connectionDifferenceBiContrCoeffField (I := I) (M := M) gj g₀ g₁ g₁').toSection x =
      (show TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (connectionDifferenceBiContrFib (I := I) gj g₀ g₁ g₁' x)) :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceBiContrCoeffField_toSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceBiContrCoeffField_toSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceBiContrCoeffField_toSection ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceBiContrCoeffField_toSection

noncomputable def connectionDifferenceBiContrCoeff (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 :=
  connectionDifferenceBiContrCoeffField (I := I) (M := M) gj g₀ g₁ g₁'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceBiContrCoeff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceBiContrCoeff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceBiContrCoeff ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceBiContrCoeff

omit [I.Boundaryless] [SigmaCompactSpace M] in
@[simp] theorem connectionDifferenceBiContrCoeff_toSection (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M) (x : M) :
    (connectionDifferenceBiContrCoeff (I := I) (M := M) gj g₀ g₁ g₁').toSection x =
      (show TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (connectionDifferenceBiContrFib (I := I) gj g₀ g₁ g₁' x)) :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceBiContrCoeff_toSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceBiContrCoeff_toSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceBiContrCoeff_toSection ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceBiContrCoeff_toSection


omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem connectionDifferenceBiContrCoeff_operatorFieldApplication_eq (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 2 2
          (connectionDifferenceBiContrCoeff (I := I) (M := M) gj g₀ g₁ g₁') W)
        x v =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        g₀.inner x
            (PDE.DeTurck.connectionDifference (I := I) gj g₀ x
              (PDE.DeTurck.connectionDifference (I := I) g₁ g₁' x
                (smoothOrthoFrame (I := I) g₀ x a x)
                (smoothOrthoFrame (I := I) g₀ x b x)) (v 0)) (v 1) *
          unitModel (I := I) (M := M) g₀ 2 W x
            (fun j => if j = 0 then smoothOrthoFrame (I := I) g₀ x a x
              else smoothOrthoFrame (I := I) g₀ x b x) := by
  rw [unitModel, operatorFieldApplication_toSection]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (connectionDifferenceBiContrCoeff (I := I) (M := M) gj g₀ g₁ g₁').toSection x).comp
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x))
        (unitTensor (I := I) (M := M) x) =
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (connectionDifferenceBiContrCoeff (I := I) (M := M) gj g₀ g₁ g₁').toSection x)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x)) from rfl]
  rw [connectionDifferenceBiContrCoeff_toSection]
  rw [show (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (connectionDifferenceBiContrFib (I := I) gj g₀ g₁ g₁' x)))
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x)) =
      connectionDifferenceBiContrFib (I := I) gj g₀ g₁ g₁' x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x)) from rfl]
  change Tensor0SSpace.eval
    (connectionDifferenceBiContrFib (I := I) gj g₀ g₁ g₁' x
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
        (unitTensor (I := I) (M := M) x))) v = _
  rw [connectionDifferenceBiContrFib, connectionDifferenceBiContrFibFixedFrame_eval]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine Finset.sum_congr rfl (fun b _ => ?_)
  congr 1
  rw [unitModel]
  congr 1
  funext j
  fin_cases j <;> simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceBiContrCoeff_operatorFieldApplication_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceBiContrCoeff_operatorFieldApplication_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceBiContrCoeff_operatorFieldApplication_eq ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceBiContrCoeff_operatorFieldApplication_eq


end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
