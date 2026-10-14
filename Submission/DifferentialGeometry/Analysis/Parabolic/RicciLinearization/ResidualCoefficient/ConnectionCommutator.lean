import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorField.Calculus.SecondGradient
import Submission.DifferentialGeometry.Geometry.Metric.DeTurck.ConnectionDifference.Identities
import Submission.DifferentialGeometry.Analysis.Parabolic.RicciLinearization.CovariantJetDecomposition.CorrectionFields.PointwiseBounds
import Submission.DifferentialGeometry.Analysis.Parabolic.RicciLinearization.CovariantJetDecomposition.CoefficientFields
import Submission.DifferentialGeometry.Analysis.Parabolic.RicciLinearization.PalatiniDecomposition.PathLinearization
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurck.SectionDifference.ConnectionBicontraction
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Product.JetIntegral
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.Remainder.Defs
import Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLie.Kernel.L2JetBound
import Submission.DifferentialGeometry.Analysis.Parabolic.RicciLinearization.Curvature.DecompositionMonomialBounds
import Submission.DifferentialGeometry.Analysis.Parabolic.RicciLinearization.ConnectionDifference.Coefficients
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorField.Algebra.InputSlotSymmetrization

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Connection.Realization
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Operator

noncomputable section
set_option backward.isDefEq.respectTransparency false

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators

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
open _root_.Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization

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

def connectionDifferenceIteratedCommKernelBilin (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (p q : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun v0 =>
        g₁.inner x (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x
            (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x q p) v0)
          - g₁.inner x (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x
              (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x q v0) p)
      map_add' := fun v0 v0' => by
        simp only [map_add, add_apply]
        abel
      map_smul' := fun c v0 => by
        rw [RingHom.id_apply]
        simp only [map_smul, smul_apply]
        rw [smul_sub] }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceIteratedCommKernelBilin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceIteratedCommKernelBilin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceIteratedCommKernelBilin ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceIteratedCommKernelBilin

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma connectionDifferenceAACommKernelBilin_apply (g₀ g₁ : SmoothRiemannianMetric I M)
    (x : M) (p q v0 v1 : TangentSpace I x) :
    connectionDifferenceIteratedCommKernelBilin (I := I) g₀ g₁ x p q v0 v1 =
      g₁.inner x (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x
          (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x q p) v0) v1
        - g₁.inner x (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x
            (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x q v0) p) v1 := by
  rw [connectionDifferenceIteratedCommKernelBilin, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
    AddHom.coe_mk, sub_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceAACommKernelBilin_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceAACommKernelBilin_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceAACommKernelBilin_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceAACommKernelBilin_apply

def frameConnectionDifferenceAACommKernel (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (v0 v1 : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun p =>
        haveI : FiniteDimensional ℝ (TangentSpace I x) :=
          inferInstanceAs (FiniteDimensional ℝ E)
        LinearMap.toContinuousLinearMap
          { toFun := fun q => connectionDifferenceIteratedCommKernelBilin (I := I) g₀ g₁ x p q v0 v1
            map_add' := fun q q' => by
              rw [connectionDifferenceAACommKernelBilin_apply, connectionDifferenceAACommKernelBilin_apply,
                connectionDifferenceAACommKernelBilin_apply]
              simp only [map_add, add_apply]
              ring
            map_smul' := fun c q => by
              rw [RingHom.id_apply, connectionDifferenceAACommKernelBilin_apply,
                connectionDifferenceAACommKernelBilin_apply]
              simp only [map_smul, smul_apply, smul_eq_mul]
              ring }
      map_add' := fun p p' => by
        apply ContinuousLinearMap.ext
        intro q
        simp only [add_apply, LinearMap.coe_toContinuousLinearMap']
        simp only [LinearMap.coe_mk, AddHom.coe_mk]
        rw [connectionDifferenceAACommKernelBilin_apply, connectionDifferenceAACommKernelBilin_apply,
          connectionDifferenceAACommKernelBilin_apply]
        simp only [map_add, add_apply]
        ring
      map_smul' := fun c p => by
        rw [RingHom.id_apply]
        apply ContinuousLinearMap.ext
        intro q
        simp only [smul_apply, LinearMap.coe_toContinuousLinearMap']
        simp only [LinearMap.coe_mk, AddHom.coe_mk]
        rw [connectionDifferenceAACommKernelBilin_apply, connectionDifferenceAACommKernelBilin_apply]
        simp only [map_smul, smul_apply, smul_eq_mul]
        ring }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.frameConnectionDifferenceAACommKernel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.frameConnectionDifferenceAACommKernel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.frameConnectionDifferenceAACommKernel ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.frameConnectionDifferenceAACommKernel

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma frameConnectionDifferenceAACommKernel_apply (g₀ g₁ : SmoothRiemannianMetric I M)
    (x : M) (v0 v1 p q : TangentSpace I x) :
    frameConnectionDifferenceAACommKernel (I := I) g₀ g₁ x v0 v1 p q =
      connectionDifferenceIteratedCommKernelBilin (I := I) g₀ g₁ x p q v0 v1 := by
  rw [frameConnectionDifferenceAACommKernel, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
    AddHom.coe_mk, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.frameConnectionDifferenceAACommKernel_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.frameConnectionDifferenceAACommKernel_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.frameConnectionDifferenceAACommKernel_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.frameConnectionDifferenceAACommKernel_apply

def connectionDifferenceAACommSummandFib (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (p q : TangentSpace I x) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  haveI : FiniteDimensional ℝ (Tensor0SSpace 2 I x) := inferInstance
  LinearMap.toContinuousLinearMap
    { toFun := fun D =>
        (Tensor0SSpace.toModel D ![(p : E), (q : E)]) •
          Tensor0SSpace.ofModel (I := I) (x := x)
            (DifferentialGeometry.Tensor.Multilinear.biForm₂ToModel E (connectionDifferenceIteratedCommKernelBilin (I := I) g₀ g₁ x p q))
      map_add' := fun D D' => by
        rw [Tensor0SSpace.toModel_add, add_apply, add_smul]
      map_smul' := fun c D => by
        rw [Tensor0SSpace.toModel_smul, smul_apply, smul_eq_mul,
          RingHom.id_apply, _root_.SemigroupAction.mul_smul] }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceAACommSummandFib then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceAACommSummandFib"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceAACommSummandFib ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceAACommSummandFib

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma connectionDifferenceAACommSummandFib_toModel (g₀ g₁ : SmoothRiemannianMetric I M)
    (x : M) (p q : TangentSpace I x) (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel (connectionDifferenceAACommSummandFib (I := I) g₀ g₁ x p q D) v =
      (Tensor0SSpace.toModel D ![(p : E), (q : E)]) *
        connectionDifferenceIteratedCommKernelBilin (I := I) g₀ g₁ x p q (v 0) (v 1) := by
  with_unfolding_all
    rw [connectionDifferenceAACommSummandFib, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
      AddHom.coe_mk, Tensor0SSpace.toModel_smul, smul_apply,
      Tensor0SSpace.toModel_ofModel, smul_eq_mul]
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceAACommSummandFib_toModel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceAACommSummandFib_toModel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceAACommSummandFib_toModel ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceAACommSummandFib_toModel

def connectionDifferenceAACommBiContrFibFixedFrame (g₀ g₁ : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
    connectionDifferenceAACommSummandFib (I := I) g₀ g₁ x (B a x) (B b x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceAACommBiContrFibFixedFrame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceAACommBiContrFibFixedFrame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceAACommBiContrFibFixedFrame ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceAACommBiContrFibFixedFrame

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
lemma connectionDifferenceAACommBiContrFibFixedFrame_toModel (g₀ g₁ : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M)
    (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel
        (connectionDifferenceAACommBiContrFibFixedFrame (I := I) g₀ g₁ B x D) v =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (Tensor0SSpace.toModel D ![(B a x : E), (B b x : E)]) *
          connectionDifferenceIteratedCommKernelBilin (I := I) g₀ g₁ x (B a x) (B b x) (v 0) (v 1) := by
  classical
  rw [connectionDifferenceAACommBiContrFibFixedFrame, sum_apply,
    ← Tensor0SSpace.toModelL_apply, map_sum, sum_apply]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [sum_apply, Tensor0SSpace.toModelL_apply,
    ← Tensor0SSpace.toModelL_apply, map_sum, sum_apply]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Tensor0SSpace.toModelL_apply, connectionDifferenceAACommSummandFib_toModel]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceAACommBiContrFibFixedFrame_toModel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceAACommBiContrFibFixedFrame_toModel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceAACommBiContrFibFixedFrame_toModel ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceAACommBiContrFibFixedFrame_toModel

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem connectionDifferenceAACommKernelBilin_homSection_contMDiff
    (g₀ g₁ : SmoothRiemannianMetric I M)
    {p q : Π b : M, TangentSpace I b}
    (hp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% p))
    (hq : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% q)) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun b : M => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ) x
        (connectionDifferenceIteratedCommKernelBilin (I := I) g₀ g₁ x (p x) (q x))) := by
  classical
  apply contMDiff_continuousLinearMap_section_of_apply
    (V₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
    (φ := fun x : M => connectionDifferenceIteratedCommKernelBilin (I := I) g₀ g₁ x (p x) (q x))
  intro V0
  apply contMDiff_continuousLinearMap_section_of_apply
    (V₂ := fun _ : M => ℝ)
    (φ := fun x : M => connectionDifferenceIteratedCommKernelBilin (I := I) g₀ g₁ x (p x) (q x) (V0 x))
  intro W
  have hAqp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => PDE.DeTurck.connectionDifference (I := I) g₁ g₀ b (q b) (p b))) :=
    PDE.DeTurck.connectionDifference_contMDiff (I := I) g₁ g₀ hq hp
  have hAAqpV : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => PDE.DeTurck.connectionDifference (I := I) g₁ g₀ b
        (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ b (q b) (p b)) (V0 b))) :=
    PDE.DeTurck.connectionDifference_contMDiff (I := I) g₁ g₀ hAqp V0.contMDiff
  have hAqV : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => PDE.DeTurck.connectionDifference (I := I) g₁ g₀ b (q b) (V0 b))) :=
    PDE.DeTurck.connectionDifference_contMDiff (I := I) g₁ g₀ hq V0.contMDiff
  have hAAqVp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => PDE.DeTurck.connectionDifference (I := I) g₁ g₀ b
        (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ b (q b) (V0 b)) (p b))) :=
    PDE.DeTurck.connectionDifference_contMDiff (I := I) g₁ g₀ hAqV hp
  have hs1 : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => g₁.inner x (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x
        (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (q x) (p x)) (V0 x)) (W x)) :=
    contMDiff_g_inner_of_smooth_sections (I := I) g₁
      ⟨fun b => PDE.DeTurck.connectionDifference (I := I) g₁ g₀ b
        (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ b (q b) (p b)) (V0 b), hAAqpV⟩
      ⟨fun b => W b, W.contMDiff⟩
  have hs2 : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => g₁.inner x (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x
        (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (q x) (V0 x)) (p x)) (W x)) :=
    contMDiff_g_inner_of_smooth_sections (I := I) g₁
      ⟨fun b => PDE.DeTurck.connectionDifference (I := I) g₁ g₀ b
        (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ b (q b) (V0 b)) (p b), hAAqVp⟩
      ⟨fun b => W b, W.contMDiff⟩
  have h_scalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => g₁.inner x (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x
          (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (q x) (p x)) (V0 x)) (W x)
        - g₁.inner x (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x
            (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (q x) (V0 x)) (p x)) (W x)) :=
    hs1.sub hs2
  intro x
  rw [_root_.Bundle.contMDiffAt_section]
  refine (h_scalar.contMDiffAt).congr_of_eventuallyEq ?_
  filter_upwards with y
  change connectionDifferenceIteratedCommKernelBilin (I := I) g₀ g₁ y (p y) (q y) (V0 y) (W y) =
    (_root_.FiberBundle.trivializationAt ℝ (Bundle.Trivial M ℝ) x ⟨y, _⟩).2
  rw [connectionDifferenceAACommKernelBilin_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceAACommKernelBilin_homSection_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceAACommKernelBilin_homSection_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceAACommKernelBilin_homSection_contMDiff ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceAACommKernelBilin_homSection_contMDiff

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem connectionDifferenceAACommBiContrFibFixedFrame_apply_section_contMDiff
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (Y : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun x : M => Tensor0SSpace 2 I x⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x
        (connectionDifferenceAACommBiContrFibFixedFrame (I := I) g₀ g₁ B x (Y x))) := by
  classical
  have hsummand : ∀ a b : Fin (Module.finrank ℝ E),
      ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
          (E := fun z : M => Tensor0SSpace 2 I z) x
          (connectionDifferenceAACommSummandFib (I := I) g₀ g₁ x (B a x) (B b x) (Y x))) := by
    intro a b
    have hscalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
        (fun x : M => Tensor0SSpace.toModel (Y x) ![(B a x : E), (B b x : E)]) := by
      have h := TensorMultilinear.contMDiff_section_apply (n := 2)
        (fun b' => Y b') Y.contMDiff
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
      (fun x => connectionDifferenceIteratedCommKernelBilin (I := I) g₀ g₁ x (B a x) (B b x))
      (connectionDifferenceAACommKernelBilin_homSection_contMDiff (I := I) g₀ g₁ (hB a) (hB b))
    have hsmul := ContMDiff.smul_section (f := fun x : M =>
        Tensor0SSpace.toModel (Y x) ![(B a x : E), (B b x : E)]) hscalar hbilin
    refine hsmul.congr ?_
    intro x
    rfl
  set T2 : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯ :=
    fun a b =>
      { toFun := fun x : M =>
          connectionDifferenceAACommSummandFib (I := I) g₀ g₁ x (B a x) (B b x) (Y x)
        contMDiff_toFun := hsummand a b } with hT2_def
  have hcoe1 : ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), T2 a b :
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
        Π z : M, Tensor0SSpace 2 I z) =
      ∑ a : Fin (Module.finrank ℝ E),
        ((∑ b : Fin (Module.finrank ℝ E), T2 a b :
          Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
            Π z : M, Tensor0SSpace 2 I z) :=
    map_sum (ContMDiffSection.coeAddHom I (Tensor0SModel 2 ℝ E) ∞
      (fun z : M => Tensor0SSpace 2 I z))
      (fun a => ∑ b : Fin (Module.finrank ℝ E), T2 a b) Finset.univ
  have hcoe2 : ∀ a : Fin (Module.finrank ℝ E),
      ((∑ b : Fin (Module.finrank ℝ E), T2 a b :
        Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
          Π z : M, Tensor0SSpace 2 I z) =
      ∑ b : Fin (Module.finrank ℝ E), ((T2 a b : Π z : M, Tensor0SSpace 2 I z)) :=
    fun a => map_sum (ContMDiffSection.coeAddHom I (Tensor0SModel 2 ℝ E) ∞
      (fun z : M => Tensor0SSpace 2 I z)) (fun b => T2 a b) Finset.univ
  have hStot := (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
    T2 a b).contMDiff
  refine hStot.congr ?_
  intro x
  refine congrArg (TotalSpace.mk' (Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SSpace 2 I z) x) ?_
  have hval : (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), T2 a b :
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) x =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        connectionDifferenceAACommSummandFib (I := I) g₀ g₁ x (B a x) (B b x) (Y x) := by
    have h1 : (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), T2 a b :
        Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) x =
        ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          T2 a b : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
            Π z : M, Tensor0SSpace 2 I z) x := rfl
    rw [h1, hcoe1, Finset.sum_apply]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [hcoe2 a, Finset.sum_apply]
    rfl
  rw [connectionDifferenceAACommBiContrFibFixedFrame, sum_apply]
  rw [show ∑ a : Fin (Module.finrank ℝ E), (∑ b : Fin (Module.finrank ℝ E),
      connectionDifferenceAACommSummandFib (I := I) g₀ g₁ x (B a x) (B b x)) (Y x) =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        connectionDifferenceAACommSummandFib (I := I) g₀ g₁ x (B a x) (B b x) (Y x) from
    Finset.sum_congr rfl (fun a _ => sum_apply _ _ _)]
  rw [← hval]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceAACommBiContrFibFixedFrame_apply_section_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceAACommBiContrFibFixedFrame_apply_section_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceAACommBiContrFibFixedFrame_apply_section_contMDiff ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceAACommBiContrFibFixedFrame_apply_section_contMDiff

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem connectionDifferenceAACommBiContrFibFixedFrame_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM
          (connectionDifferenceAACommBiContrFibFixedFrame (I := I) g₀ g₁ B x))) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I)
    (F₁ := Tensor0SModel 2 ℝ E) (V₁ := fun z : M => Tensor0SSpace 2 I z)
    (F₂ := Tensor0SModel 2 ℝ E) (V₂ := fun z : M => Tensor0SSpace 2 I z)
    (φ := fun x : M => connectionDifferenceAACommBiContrFibFixedFrame (I := I) g₀ g₁ B x)
  intro Y
  exact connectionDifferenceAACommBiContrFibFixedFrame_apply_section_contMDiff
    (I := I) g₀ g₁ B hB Y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceAACommBiContrFibFixedFrame_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceAACommBiContrFibFixedFrame_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceAACommBiContrFibFixedFrame_contMDiff ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceAACommBiContrFibFixedFrame_contMDiff

def connectionDifferenceAACommBiContrFib (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  connectionDifferenceAACommBiContrFibFixedFrame (I := I) g₀ g₁ (smoothOrthoFrame (I := I) g₁ x) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceAACommBiContrFib then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceAACommBiContrFib"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceAACommBiContrFib ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceAACommBiContrFib

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
lemma connectionDifferenceAACommBiContrFib_toModel (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel (connectionDifferenceAACommBiContrFib (I := I) g₀ g₁ x D) v =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (Tensor0SSpace.toModel D
          ![(smoothOrthoFrame (I := I) g₁ x a x : E),
            (smoothOrthoFrame (I := I) g₁ x b x : E)]) *
          connectionDifferenceIteratedCommKernelBilin (I := I) g₀ g₁ x
            (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)
            (v 0) (v 1) := by
  rw [connectionDifferenceAACommBiContrFib, connectionDifferenceAACommBiContrFibFixedFrame_toModel]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceAACommBiContrFib_toModel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceAACommBiContrFib_toModel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceAACommBiContrFib_toModel ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceAACommBiContrFib_toModel

omit [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
theorem connectionDifferenceAACommBiContrFib_eq_fixedFrame_on_neighborhood
    (g₀ g₁ : SmoothRiemannianMetric I M) (x₀ : M)
    {y : M} (hy : y ∈ smoothOrthoFrameNeighborhood (I := I) (M := M) x₀) :
    connectionDifferenceAACommBiContrFib (I := I) g₀ g₁ y =
      connectionDifferenceAACommBiContrFibFixedFrame (I := I) g₀ g₁
        (smoothOrthoFrame (I := I) g₁ x₀) y := by
  classical
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  rw [connectionDifferenceAACommBiContrFib, connectionDifferenceAACommBiContrFibFixedFrame_toModel,
    connectionDifferenceAACommBiContrFibFixedFrame_toModel]
  let _ : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
  let e := (tangentSpaceModelContinuousLinearEquiv (I := I) y).toContinuousLinearMap
  let vt : Fin 2 → TangentSpace I y := fun i =>
    (tangentSpaceModelContinuousLinearEquiv (I := I) y).symm (v i)
  let Dmodel : E →L[ℝ] E →L[ℝ] ℝ :=
    (DifferentialGeometry.Tensor.Multilinear.biForm₂ToModel E).symm (Tensor0SSpace.toModel D)
  let Dd : TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ :=
    (((Dmodel.comp e).flip.comp e).flip)
  with_unfolding_all
    change (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (Tensor0SSpace.toModel D
          ![tangentSpaceModelContinuousLinearEquiv (I := I) y
              (smoothOrthoFrame (I := I) g₁ y a y),
            tangentSpaceModelContinuousLinearEquiv (I := I) y
              (smoothOrthoFrame (I := I) g₁ y b y)]) *
          connectionDifferenceIteratedCommKernelBilin (I := I) g₀ g₁ y
            (smoothOrthoFrame (I := I) g₁ y a y) (smoothOrthoFrame (I := I) g₁ y b y)
            (vt 0) (vt 1)) =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (Tensor0SSpace.toModel D
          ![tangentSpaceModelContinuousLinearEquiv (I := I) y
              (smoothOrthoFrame (I := I) g₁ x₀ a y),
            tangentSpaceModelContinuousLinearEquiv (I := I) y
              (smoothOrthoFrame (I := I) g₁ x₀ b y)]) *
          connectionDifferenceIteratedCommKernelBilin (I := I) g₀ g₁ y
            (smoothOrthoFrame (I := I) g₁ x₀ a y) (smoothOrthoFrame (I := I) g₁ x₀ b y)
            (vt 0) (vt 1)
  have hrewrite : ∀ (Bf : Fin (Module.finrank ℝ E) → TangentSpace I y),
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (Tensor0SSpace.toModel D
          ![tangentSpaceModelContinuousLinearEquiv (I := I) y (Bf a),
            tangentSpaceModelContinuousLinearEquiv (I := I) y (Bf b)]) *
          connectionDifferenceIteratedCommKernelBilin (I := I) g₀ g₁ y
            (Bf a) (Bf b) (vt 0) (vt 1) =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        frameConnectionDifferenceAACommKernel (I := I) g₀ g₁ y
            (vt 0) (vt 1) (Bf a) (Bf b) *
          Dd (Bf a) (Bf b) := by
    intro Bf
    refine Finset.sum_congr rfl (fun a _ => ?_)
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [frameConnectionDifferenceAACommKernel_apply]
    dsimp only [Dd, Dmodel, e]
    rw [ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_apply,
      DifferentialGeometry.Tensor.Multilinear.biForm₂ToModel_symm_apply]
    rw [mul_comm]
    rfl
  rw [hrewrite (fun a => smoothOrthoFrame (I := I) g₁ y a y),
    hrewrite (fun a => smoothOrthoFrame (I := I) g₁ x₀ a y)]
  exact double_frame_bilin_trace_indep (I := I) g₁ y
    (frameConnectionDifferenceAACommKernel (I := I) g₀ g₁ y (vt 0) (vt 1)) Dd
    (fun a => smoothOrthoFrame (I := I) g₁ y a y)
    (fun a => smoothOrthoFrame (I := I) g₁ x₀ a y)
    (fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g₁ y i j)
    (fun i j => smoothOrthoFrame_orthonormal (I := I) g₁ x₀ hy i j)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceAACommBiContrFib_eq_fixedFrame_on_neighborhood then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceAACommBiContrFib_eq_fixedFrame_on_neighborhood"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceAACommBiContrFib_eq_fixedFrame_on_neighborhood ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceAACommBiContrFib_eq_fixedFrame_on_neighborhood

omit [CompactSpace M] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem connectionDifferenceAACommBiContrFib_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (connectionDifferenceAACommBiContrFib (I := I) g₀ g₁ x))) := by
  classical
  intro x₀
  have h_fixed : ContMDiffAt I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (connectionDifferenceAACommBiContrFibFixedFrame (I := I) g₀ g₁
          (smoothOrthoFrame (I := I) g₁ x₀) x))) x₀ :=
    connectionDifferenceAACommBiContrFibFixedFrame_contMDiff (I := I) g₀ g₁
      (smoothOrthoFrame (I := I) g₁ x₀)
      (fun i => smoothOrthoFrame_smooth (I := I) g₁ x₀ i) x₀
  refine h_fixed.congr_of_eventuallyEq ?_
  filter_upwards [smoothOrthoFrameNeighborhood_mem_nhds (I := I) (M := M) x₀] with y hy
  exact congrArg (TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
    (E := fun z : M => TensorRSSpace 2 2 I z) y)
    (congrArg TensorRSSpace.ofCLM
      (connectionDifferenceAACommBiContrFib_eq_fixedFrame_on_neighborhood (I := I) g₀ g₁ x₀ hy))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceAACommBiContrFib_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceAACommBiContrFib_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceAACommBiContrFib_contMDiff ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceAACommBiContrFib_contMDiff

def ricciOrderZeroAACommCoeffField (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (connectionDifferenceAACommBiContrFib (I := I) g₀ g₁ x))
      contMDiff_toFun := connectionDifferenceAACommBiContrFib_contMDiff (I := I) g₀ g₁ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciOrderZeroAACommCoeffField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciOrderZeroAACommCoeffField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciOrderZeroAACommCoeffField ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciOrderZeroAACommCoeffField

omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
@[simp] theorem ricciOrderZeroAACommCoeffField_toSection
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (ricciOrderZeroAACommCoeffField (I := I) (M := M) g₀ g₁).toSection x =
      (show TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (connectionDifferenceAACommBiContrFib (I := I) g₀ g₁ x)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciOrderZeroAACommCoeffField_toSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciOrderZeroAACommCoeffField_toSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciOrderZeroAACommCoeffField_toSection ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciOrderZeroAACommCoeffField_toSection

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] in
theorem connectionDifferenceAACommBiContrFib_self (g₀ : SmoothRiemannianMetric I M) (x : M) :
    connectionDifferenceAACommBiContrFib (I := I) g₀ g₀ x = 0 := by
  classical
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  rw [connectionDifferenceAACommBiContrFib, connectionDifferenceAACommBiContrFibFixedFrame_toModel]
  have hconn : PDE.DeTurck.connectionDifference (I := I) g₀ g₀ = 0 :=
    PDE.DeTurck.connectionDifference_self (I := I) g₀
  rw [show (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
      (Tensor0SSpace.toModel D
        ![(smoothOrthoFrame (I := I) g₀ x a x : E),
          (smoothOrthoFrame (I := I) g₀ x b x : E)]) *
        connectionDifferenceIteratedCommKernelBilin (I := I) g₀ g₀ x
          (smoothOrthoFrame (I := I) g₀ x a x) (smoothOrthoFrame (I := I) g₀ x b x)
          (v 0) (v 1)) = 0 from
    Finset.sum_eq_zero (fun a _ => Finset.sum_eq_zero (fun b _ => by
      with_unfolding_all
        simp only [connectionDifferenceIteratedCommKernelBilin,
          LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
          AddHom.coe_mk, hconn, Pi.zero_apply, zero_apply, map_zero,
          sub_self]
        change D.toModel
            ![smoothOrthoFrame g₀ x a x, smoothOrthoFrame g₀ x b x] * 0 = 0
      rw [_root_.MulZeroClass.mul_zero]))]
  simp only [zero_apply, Tensor0SSpace.toModel_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceAACommBiContrFib_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceAACommBiContrFib_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceAACommBiContrFib_self ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connectionDifferenceAACommBiContrFib_self

omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem ricciOrderZeroAACommCoeffField_self (g₀ : SmoothRiemannianMetric I M) :
    ricciOrderZeroAACommCoeffField (I := I) (M := M) g₀ g₀ = 0 := by
  classical
  refine SmoothCcTensor.ext ?_
  refine ContMDiffSection.ext (fun x => ?_)
  rw [ricciOrderZeroAACommCoeffField_toSection, connectionDifferenceAACommBiContrFib_self]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciOrderZeroAACommCoeffField_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciOrderZeroAACommCoeffField_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciOrderZeroAACommCoeffField_self ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciOrderZeroAACommCoeffField_self

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
