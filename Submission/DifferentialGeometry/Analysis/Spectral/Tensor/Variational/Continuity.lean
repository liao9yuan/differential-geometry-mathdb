import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Variational.CovDerivPointwise
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Variational.CovDerivSupport
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Variational.FrameInvariance
import Submission.DifferentialGeometry.Analysis.Integration.L2.SmoothSections.PreHilbert
import Submission.DifferentialGeometry.Analysis.Integration.L2.SmoothSections.Integrability
import Submission.DifferentialGeometry.Geometry.Metric.PointwiseInner.Algebra
import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.TensorRS.Basic
import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Defs
import Submission.DifferentialGeometry.Geometry.Connection.LeviCivita.Defs
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Properties
import Submission.DifferentialGeometry.Geometry.Metric.PointwiseInner.MetricLowering
import Submission.DifferentialGeometry.Tensor.Multilinear.Bundle.Evaluation
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.TensorRS.Riemannian
import Submission.DifferentialGeometry.Geometry.Operator.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.ContinuousOn

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Operator


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators _root_.Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2

open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Tensor.TensorRSRiemannian
open _root_.Submission.DifferentialGeometry.TensorRSNabla

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma tensorCovDeriv_chartBasis_contMDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun b : M =>
        TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun y : M => TensorRSSpace r s I y) b
          (tensorCovDerivAt (I := I) (M := M) g r s S b
            (tangentSpaceModelContinuousLinearEquiv (I := I) b
              (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i b))))
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := by
  classical
  set covLC := tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)
  have hcovLC_inst : CovariantDerivative.ContMDiffCovariantDerivative covLC ∞ :=
    inferInstance
  have hop : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel r s ℝ E)) ∞
      (fun b : M => (⟨b, covLC.toFun (fun y : M => S.toSection y) b⟩ :
        _root_.Bundle.TotalSpace (E →L[ℝ] TensorRSModel r s ℝ E)
          fun b : M => TangentSpace I b →L[ℝ] TensorRSSpace r s I b)) Set.univ :=
    hcovLC_inst.contMDiff.contMDiff (σ := fun y : M => S.toSection y)
      (S.toSection.contMDiff.contMDiffOn)
  have hX_on : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E (E := fun y : M => TangentSpace I y) b
        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i b))
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := by
    have := DifferentialGeometry.Tensor.Coordinates.chartBasisVec_contMDiffOn (I := I) α i
    exact this
  intro x₀ hx₀
  refine ContMDiffAt.contMDiffWithinAt ?_
  have hcov_at : ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel r s ℝ E)) ∞
      (fun b : M => (⟨b, covLC.toFun (fun y : M => S.toSection y) b⟩ :
        _root_.Bundle.TotalSpace (E →L[ℝ] TensorRSModel r s ℝ E)
          fun b : M => TangentSpace I b →L[ℝ] TensorRSSpace r s I b)) x₀ :=
    hop.contMDiffAt (Filter.univ_mem)
  have hX_at : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E (E := fun y : M => TangentSpace I y) b
        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i b)) x₀ :=
    (hX_on x₀ hx₀).contMDiffAt
      ((_root_.FiberBundle.trivializationAt E (TangentSpace I) α).open_baseSet.mem_nhds hx₀)
  exact hcov_at.clm_bundle_apply hX_at

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovDeriv_chartBasis_contMDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovDeriv_chartBasis_contMDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovDeriv_chartBasis_contMDiffOn ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovDeriv_chartBasis_contMDiffOn

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
lemma tensorCovDeriv_chartBasis_trivImage_contMDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ, TensorRSModel r s ℝ E) ∞
      (fun b : M =>
        (_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α
          ⟨b, tensorCovDerivAt (I := I) (M := M) g r s S b
            (tangentSpaceModelContinuousLinearEquiv (I := I) b
              (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i b))⟩).2)
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := by
  classical
  have hsection := tensorCovDeriv_chartBasis_contMDiffOn (I := I) (M := M) g r s S α i
  have hbase_eq : (_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).baseSet =
        (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := by
    change ((_root_.FiberBundle.trivializationAt (Tensor0SModel r ℝ E) (fun x : M => Tensor0SSpace r I x) α).baseSet) ∩
        ((_root_.FiberBundle.trivializationAt (Tensor0SModel s ℝ E) (fun x : M => Tensor0SSpace s I x) α).baseSet) =
          (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet
    change (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet ∩
          (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet =
            (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet
    exact Set.inter_self _
  rw [← hbase_eq]
  rw [← Bundle.Trivialization.contMDiffOn_section_baseSet_iff
        (_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α)]
  rw [hbase_eq]
  exact hsection

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovDeriv_chartBasis_trivImage_contMDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovDeriv_chartBasis_trivImage_contMDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovDeriv_chartBasis_trivImage_contMDiffOn ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovDeriv_chartBasis_trivImage_contMDiffOn

private noncomputable def evalAtBasisLinearLocal (n : ℕ) :
    Tensor0SModel n ℝ E →ₗ[ℝ]
      ((Fin n → Fin (Module.finrank ℝ E)) → ℝ) where
  toFun := fun Φ φ => Φ (fun k : Fin n => (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) (φ k))
  map_add' Φ₁ Φ₂ := by
    funext φ
    simp [add_apply]
  map_smul' c Φ := by
    funext φ
    simp [smul_apply]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.evalAtBasisLinearLocal
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.evalAtBasisLinearLocal target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
@[simp] private lemma evalAtBasisLinearLocal_apply (n : ℕ)
    (Φ : Tensor0SModel n ℝ E)
    (φ : Fin n → Fin (Module.finrank ℝ E)) :
    evalAtBasisLinearLocal (E := E) n Φ φ =
      Φ (fun k : Fin n => (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) (φ k)) := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.evalAtBasisLinearLocal_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.evalAtBasisLinearLocal_apply target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
private lemma evalAtBasisLinearLocal_injective (n : ℕ) :
    Function.Injective (evalAtBasisLinearLocal (E := E) n) := by
  intro Φ₁ Φ₂ h
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  refine Module.Basis.ext_multilinear (e := fun _ : Fin n => DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) ?_
  intro v
  exact congr_fun h v

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.evalAtBasisLinearLocal_injective
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.evalAtBasisLinearLocal_injective target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
private lemma finrank_tensor0SModel_local (n : ℕ) :
    Module.finrank ℝ (Tensor0SModel n ℝ E) =
      (Module.finrank ℝ E) ^ n := by
  induction n with
  | zero =>
      rw [pow_zero]
      rw [(continuousMultilinearCurryFin0 ℝ E ℝ).toLinearEquiv.finrank_eq]
      exact Module.finrank_self ℝ
  | succ n ih =>
      rw [(continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (n + 1) => E) ℝ).toLinearEquiv.finrank_eq]
      let φ : (E →L[ℝ] Tensor0SModel n ℝ E) ≃ₗ[ℝ]
          (E →ₗ[ℝ] Tensor0SModel n ℝ E) :=
        { toFun := fun f => f.toLinearMap
          invFun := fun f => LinearMap.toContinuousLinearMap f
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      rw [φ.finrank_eq, Module.finrank_linearMap, ih]
      ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.finrank_tensor0SModel_local
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.finrank_tensor0SModel_local target :: scope.openDecls } }

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma finrank_basis_pi_local (n : ℕ) :
    Module.finrank ℝ ((Fin n → Fin (Module.finrank ℝ E)) → ℝ) =
      (Module.finrank ℝ E) ^ n := by
  rw [Module.finrank_pi, Fintype.card_pi]
  simp [Fintype.card_fin]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.finrank_basis_pi_local
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.finrank_basis_pi_local target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
private lemma evalAtBasisLinearLocal_bijective (n : ℕ) :
    Function.Bijective (evalAtBasisLinearLocal (E := E) n) := by
  have h_inj := evalAtBasisLinearLocal_injective (E := E) n
  refine ⟨h_inj, ?_⟩
  have h_eq : Module.finrank ℝ (Tensor0SModel n ℝ E) =
      Module.finrank ℝ ((Fin n → Fin (Module.finrank ℝ E)) → ℝ) := by
    rw [finrank_tensor0SModel_local, finrank_basis_pi_local]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h_eq).mp h_inj

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.evalAtBasisLinearLocal_bijective
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.evalAtBasisLinearLocal_bijective target :: scope.openDecls } }

private noncomputable def evalAtBasisCLELocal (n : ℕ) :
    Tensor0SModel n ℝ E ≃L[ℝ]
      ((Fin n → Fin (Module.finrank ℝ E)) → ℝ) :=
  (LinearEquiv.ofBijective (evalAtBasisLinearLocal (E := E) n)
    (evalAtBasisLinearLocal_bijective (E := E) n)).toContinuousLinearEquiv

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.evalAtBasisCLELocal
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.evalAtBasisCLELocal target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
@[simp] private lemma evalAtBasisCLELocal_apply (n : ℕ)
    (Φ : Tensor0SModel n ℝ E)
    (φ : Fin n → Fin (Module.finrank ℝ E)) :
    evalAtBasisCLELocal (E := E) n Φ φ =
      Φ (fun k : Fin n => (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) (φ k)) := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.evalAtBasisCLELocal_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.evalAtBasisCLELocal_apply target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
private lemma contMDiffOn_into_tensor0SModel_of_eval_basis_local
    {n : ℕ} {U : Set M} (Φ : M → Tensor0SModel n ℝ E)
    (h : ∀ φ : Fin n → Fin (Module.finrank ℝ E),
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun b : M =>
        Φ b (fun k : Fin n => (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) (φ k))) U) :
    ContMDiffOn I 𝓘(ℝ, Tensor0SModel n ℝ E) ∞ Φ U := by
  have hpi : ContMDiffOn I 𝓘(ℝ, (Fin n → Fin (Module.finrank ℝ E)) → ℝ) ∞
      (fun b : M => evalAtBasisCLELocal (E := E) n (Φ b)) U := by
    rw [contMDiffOn_pi_space]
    intro φ
    exact h φ
  have hsymm_smooth :
      ContMDiff 𝓘(ℝ, (Fin n → Fin (Module.finrank ℝ E)) → ℝ)
        𝓘(ℝ, Tensor0SModel n ℝ E) ∞
        (evalAtBasisCLELocal (E := E) n).symm :=
    (evalAtBasisCLELocal (E := E) n).symm.toContinuousLinearMap.contMDiff
  have hcomp := hsymm_smooth.comp_contMDiffOn hpi
  refine hcomp.congr ?_
  intro b _
  exact ((evalAtBasisCLELocal (E := E) n).symm_apply_apply (Φ b)).symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.contMDiffOn_into_tensor0SModel_of_eval_basis_local
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.contMDiffOn_into_tensor0SModel_of_eval_basis_local target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
private lemma loweredCompose_at_basis_tuple_local
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α b : M)
    (T : TensorRSModel r s ℝ E)
    (φ : Fin (r + s) → Fin (Module.finrank ℝ E)) :
    loweredCompose (I := I) (M := M) g r s α b T
        (fun i : Fin (r + s) => (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) (φ i)) =
      lowerAllUpperIndices (I := I) (M := M) g r s b T
        (fun i : Fin (r + s) =>
          DifferentialGeometry.Tensor.Tensor0SRiemannian.chartTrivializationLinearMapSymm
            (I := I) (M := M) α b ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) (φ i))) := by
  rw [loweredCompose_apply]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.loweredCompose_at_basis_tuple_local
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.loweredCompose_at_basis_tuple_local target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
private lemma chartGramMatrixInv_entry_contMDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M => (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α b)⁻¹ i j)
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := by
  classical
  have hexp :
      (fun b : M => (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α b)⁻¹ i j)
        = (fun b : M => (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α b).det⁻¹ *
              (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α b).adjugate i j) := by
    funext b
    rw [Matrix.inv_def]
    simp [Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  rw [hexp]
  intro b hb
  have hdet := DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_det_contMDiffOn (I := I) g α b hb
  have hadj := chartGramMatrix_adjugate_entry_contMDiffOn (I := I) g α i j b hb
  have hpos : 0 < (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α b).det :=
    DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_det_pos (I := I) g α hb
  have hpos_ne : (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α b).det ≠ 0 := ne_of_gt hpos
  exact (ContMDiffWithinAt.inv₀ hdet hpos_ne).mul hadj

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartGramMatrixInv_entry_contMDiffOn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartGramMatrixInv_entry_contMDiffOn target :: scope.openDecls } }

private noncomputable def separableFormBundleSectionLocal
    (g : SmoothRiemannianMetric I M) (r : ℕ) (α : M)
    (φ_first : Fin r → Fin (Module.finrank ℝ E)) :
    M → _root_.Bundle.TotalSpace (Tensor0SModel r ℝ E) (fun y : M => Tensor0SSpace r I y) :=
  fun b => TotalSpace.mk' (Tensor0SModel r ℝ E)
    (E := fun y : M => Tensor0SSpace r I y) b
    (Tensor0SSpace.ofModel
      (separableFormAt (I := I) (M := M) g b r
        (fun k : Fin r =>
          DifferentialGeometry.Tensor.Tensor0SRiemannian.chartTrivializationLinearMapSymm
            (I := I) (M := M) α b ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) (φ_first k)))))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.separableFormBundleSectionLocal
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.separableFormBundleSectionLocal target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
private theorem trivializationAt_separableFormBundleSectionLocal_eval_basis
    (g : SmoothRiemannianMetric I M) (r : ℕ) (α : M)
    (φ_first : Fin r → Fin (Module.finrank ℝ E)) {b : M}
    (ψ : Fin r → Fin (Module.finrank ℝ E)) :
    (_root_.FiberBundle.trivializationAt (Tensor0SModel r ℝ E)
        (fun y : M => Tensor0SSpace r I y) α
        (separableFormBundleSectionLocal (I := I) (M := M) g r α φ_first b)).2
        (fun k : Fin r => (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) (ψ k)) =
      ∏ k : Fin r,
        DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α b (φ_first k) (ψ k) := by
  unfold separableFormBundleSectionLocal
  change ((separableFormAt (I := I) (M := M) g b r
        (fun k : Fin r =>
          DifferentialGeometry.Tensor.Tensor0SRiemannian.chartTrivializationLinearMapSymm
            (I := I) (M := M) α b ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) (φ_first k)))).compContinuousLinearMap
        (fun _ : Fin r =>
          DifferentialGeometry.Tensor.Tensor0SRiemannian.chartTrivializationLinearMapSymm
            (I := I) (M := M) α b))
      (fun k : Fin r => (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) (ψ k)) = _
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rw [separableFormAt_apply]
  refine Finset.prod_congr rfl ?_
  intro k _
  rw [DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_apply]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.trivializationAt_separableFormBundleSectionLocal_eval_basis
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.trivializationAt_separableFormBundleSectionLocal_eval_basis target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
private lemma contMDiffOn_separableFormBundleSectionLocal
    (g : SmoothRiemannianMetric I M) (r : ℕ) (α : M)
    (φ_first : Fin r → Fin (Module.finrank ℝ E)) :
    ContMDiffOn I (I.prod 𝓘(ℝ, Tensor0SModel r ℝ E)) ∞
      (separableFormBundleSectionLocal (I := I) (M := M) g r α φ_first)
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := by
  set e : _root_.Bundle.Trivialization (Tensor0SModel r ℝ E)
    (Bundle.TotalSpace.proj :
      Bundle.TotalSpace (Tensor0SModel r ℝ E)
        (fun y : M => Tensor0SSpace r I y) → M) :=
    _root_.FiberBundle.trivializationAt (Tensor0SModel r ℝ E)
      (fun y : M => Tensor0SSpace r I y) α
  have hbaseSet_eq : e.baseSet = (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := rfl
  have h_iff := e.contMDiffOn_section_baseSet_iff (IB := I) (n := ∞)
    (s := fun b => Tensor0SSpace.ofModel
      (separableFormAt (I := I) (M := M) g b r
        (fun k : Fin r =>
          DifferentialGeometry.Tensor.Tensor0SRiemannian.chartTrivializationLinearMapSymm
            (I := I) (M := M) α b ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) (φ_first k)))))
  rw [hbaseSet_eq] at h_iff
  refine h_iff.mpr ?_
  refine contMDiffOn_into_tensor0SModel_of_eval_basis_local
    (I := I) (M := M) _ ?_
  intro ψ
  have h_prod_smooth : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun b : M => ∏ k : Fin r,
        DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α b (φ_first k) (ψ k))
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := by
    refine contMDiffOn_finsetProd (fun k _ => ?_)
    exact DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_entry_contMDiffOn (I := I) g α (φ_first k) (ψ k)
  refine h_prod_smooth.congr (fun b _hb => ?_)
  exact trivializationAt_separableFormBundleSectionLocal_eval_basis
    (I := I) (M := M) g r α φ_first ψ

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.contMDiffOn_separableFormBundleSectionLocal
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.contMDiffOn_separableFormBundleSectionLocal target :: scope.openDecls } }

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private lemma contMDiffOn_lower_chartCov_at_basis
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (i : Fin (Module.finrank ℝ E))
    (φ : Fin (r + s) → Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun b : M => lowerAllUpperIndices (I := I) (M := M) g r s b
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g r s S b
            (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i b)))
        (fun j : Fin (r + s) =>
          DifferentialGeometry.Tensor.Tensor0SRiemannian.chartTrivializationLinearMapSymm
            (I := I) (M := M) α b ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) (φ j))))
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := by
  intro x₀ hx₀
  refine ContMDiffAt.contMDiffWithinAt ?_
  have h_sep_smooth_at :
      ContMDiffAt I (I.prod 𝓘(ℝ, Tensor0SModel r ℝ E)) ∞
        (separableFormBundleSectionLocal (I := I) (M := M) g r α
          (fun k : Fin r => φ (Fin.castAdd s k)))
        x₀ :=
    (contMDiffOn_separableFormBundleSectionLocal (I := I) (M := M) g r α
      (fun k : Fin r => φ (Fin.castAdd s k))).contMDiffAt
      ((_root_.FiberBundle.trivializationAt E (TangentSpace I) α).open_baseSet.mem_nhds hx₀)
  have h_S_smooth_on := tensorCovDeriv_chartBasis_contMDiffOn
    (I := I) (M := M) g r s S α i
  have h_S_smooth_at :
      ContMDiffAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
        (fun b : M =>
          TotalSpace.mk' (TensorRSModel r s ℝ E)
            (E := fun y : M => TensorRSSpace r s I y) b
            (tensorCovDerivAt (I := I) (M := M) g r s S b
              (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i b))) x₀ :=
    h_S_smooth_on.contMDiffAt
      ((_root_.FiberBundle.trivializationAt E (TangentSpace I) α).open_baseSet.mem_nhds hx₀)
  have h_applied : ContMDiffAt I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
      (fun b : M =>
        TotalSpace.mk' (Tensor0SModel s ℝ E)
          (E := fun y : M => Tensor0SSpace s I y) b
          ((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from
              tensorCovDerivAt (I := I) (M := M) g r s S b
              (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i b))
            (Tensor0SSpace.ofModel
              (separableFormAt (I := I) (M := M) g b r
                (fun k : Fin r =>
                  DifferentialGeometry.Tensor.Tensor0SRiemannian.chartTrivializationLinearMapSymm
                    (I := I) (M := M) α b
                    ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) (φ (Fin.castAdd s k)))))))) x₀ :=
    ContMDiffAt.clm_bundle_apply (𝕜 := ℝ) (n := (∞ : WithTop ℕ∞))
      (F₁ := Tensor0SModel r ℝ E) (F₂ := Tensor0SModel s ℝ E)
      (E₁ := fun y : M => Tensor0SSpace r I y)
      (E₂ := fun y : M => Tensor0SSpace s I y)
      (IM := I) (IB := I)
      (b := id)
      (ϕ := fun b : M =>
        (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from
          tensorCovDerivAt (I := I) (M := M) g r s S b
            (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i b)))
      (v := fun b : M =>
        Tensor0SSpace.ofModel
          (separableFormAt (I := I) (M := M) g b r
            (fun k : Fin r =>
              DifferentialGeometry.Tensor.Tensor0SRiemannian.chartTrivializationLinearMapSymm
                (I := I) (M := M) α b
                ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) (φ (Fin.castAdd s k))))))
      h_S_smooth_at h_sep_smooth_at
  have h_tangent_smooth_at : ∀ j : Fin s,
      ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
        (fun b : M =>
          TotalSpace.mk' E (E := fun y : M => TangentSpace I y) b
            (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α (φ (Fin.natAdd r j)) b)) x₀ := by
    intro j
    exact (DifferentialGeometry.Tensor.Coordinates.chartBasisVec_contMDiffOn (I := I) α (φ (Fin.natAdd r j))).contMDiffAt
      ((_root_.FiberBundle.trivializationAt E (TangentSpace I) α).open_baseSet.mem_nhds hx₀)
  have h_eval := TensorMultilinear.contMDiffAt_section_apply (I := I) (M := M)
    (T := fun b : M =>
      (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from
          tensorCovDerivAt (I := I) (M := M) g r s S b
            (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i b))
        (Tensor0SSpace.ofModel
          (separableFormAt (I := I) (M := M) g b r
            (fun k : Fin r =>
              DifferentialGeometry.Tensor.Tensor0SRiemannian.chartTrivializationLinearMapSymm
                (I := I) (M := M) α b
                ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) (φ (Fin.castAdd s k)))))))
    h_applied
    (v := fun (j : Fin s) (b : M) =>
      DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α (φ (Fin.natAdd r j)) b)
    h_tangent_smooth_at
  refine h_eval.congr_of_eventuallyEq ?_
  filter_upwards with b
  rw [lowerAllUpperIndices_apply]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.contMDiffOn_lower_chartCov_at_basis
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.contMDiffOn_lower_chartCov_at_basis target :: scope.openDecls } }

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private lemma contMDiffOn_loweredCompose_chartCov
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ, Tensor0SModel (r + s) ℝ E) ∞
      (fun b : M => loweredCompose (I := I) (M := M) g r s α b
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g r s S b
            (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i b))))
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := by
  refine contMDiffOn_into_tensor0SModel_of_eval_basis_local
    (I := I) (M := M) _ ?_
  intro φ
  refine ContMDiffOn.congr ?_ (fun b _ =>
    (loweredCompose_at_basis_tuple_local
      (I := I) (M := M) g r s α b
      (TensorRSSpace.toModel
        (tensorCovDerivAt (I := I) (M := M) g r s S b
          (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i b))) φ).symm)
  exact contMDiffOn_lower_chartCov_at_basis (I := I) (M := M) g r s S α i φ

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.contMDiffOn_loweredCompose_chartCov
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.contMDiffOn_loweredCompose_chartCov target :: scope.openDecls } }

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private lemma continuousOn_loweredCompose_chartCov
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (i : Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (fun b : M => loweredCompose (I := I) (M := M) g r s α b
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g r s S b
            (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i b))))
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet :=
  (contMDiffOn_loweredCompose_chartCov (I := I) (M := M) g r s S α i).continuousOn

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.continuousOn_loweredCompose_chartCov
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.continuousOn_loweredCompose_chartCov target :: scope.openDecls } }

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private lemma continuousOn_tensorInnerPointwise_chartCov
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (fun b : M => tensorInnerPointwise (I := I) (M := M) g r s b
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g r s S b
            (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i b)))
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g r s T b
            (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j b))))
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := by
  classical
  have hSα := continuousOn_loweredCompose_chartCov (I := I) (M := M) g r s S α i
  have hTα := continuousOn_loweredCompose_chartCov (I := I) (M := M) g r s T α j
  have hchart :=
    DifferentialGeometry.Tensor.TensorRSRiemannian.chartTensorInnerPointwise_continuousOn
      (I := I) (M := M) g α r s
      (fun b : M => TensorRSSpace.toModel
        (tensorCovDerivAt (I := I) (M := M) g r s S b
          (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i b)))
      (fun b : M => TensorRSSpace.toModel
        (tensorCovDerivAt (I := I) (M := M) g r s T b
          (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j b)))
      hSα hTα
  refine ContinuousOn.congr hchart ?_
  intro b hb
  exact tensorInnerPointwise_bridge_identity
    (I := I) (M := M) g α r s hb
    (TensorRSSpace.toModel
      (tensorCovDerivAt (I := I) (M := M) g r s S b
        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i b)))
    (TensorRSSpace.toModel
      (tensorCovDerivAt (I := I) (M := M) g r s T b
        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j b)))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.continuousOn_tensorInnerPointwise_chartCov
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.continuousOn_tensorInnerPointwise_chartCov target :: scope.openDecls } }

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private lemma chartTensorCovDerivPointwiseInner_continuousOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) (α : M) :
    ContinuousOn
      (chartTensorCovDerivPointwiseInner (I := I) (M := M) g α r s S T)
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := by
  classical
  unfold chartTensorCovDerivPointwiseInner
  refine continuousOn_finsetSum _ (fun i _ => ?_)
  refine continuousOn_finsetSum _ (fun j _ => ?_)
  refine ContinuousOn.mul ?_ ?_
  · exact (chartGramMatrixInv_entry_contMDiffOn (I := I) (M := M) g α i j).continuousOn
  · exact continuousOn_tensorInnerPointwise_chartCov (I := I) (M := M) g r s S T α i j

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartTensorCovDerivPointwiseInner_continuousOn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartTensorCovDerivPointwiseInner_continuousOn target :: scope.openDecls } }

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem tensorCovDerivPointwiseInner_continuous
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) :
    Continuous (tensorCovDerivPointwiseInner (I := I) (M := M) g r s S T) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hx_base : x ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt _ _ x
  have hOpen : IsOpen (_root_.FiberBundle.trivializationAt E (TangentSpace I) x).baseSet :=
    (_root_.FiberBundle.trivializationAt E (TangentSpace I) x).open_baseSet
  have h_chart_cont := chartTensorCovDerivPointwiseInner_continuousOn
    (I := I) (M := M) g r s S T x
  have h_cong : ∀ b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x).baseSet,
      tensorCovDerivPointwiseInner (I := I) (M := M) g r s S T b =
        chartTensorCovDerivPointwiseInner (I := I) (M := M) g x r s S T b := by
    intro b hb
    exact (chartTensorCovDerivPointwiseInner_eq_tensorCovDerivPointwiseInner
      (I := I) (M := M) g x r s S T hb).symm
  have h_local : ContinuousOn
      (tensorCovDerivPointwiseInner (I := I) (M := M) g r s S T)
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) x).baseSet :=
    h_chart_cont.congr h_cong
  exact h_local.continuousAt (hOpen.mem_nhds hx_base)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovDerivPointwiseInner_continuous then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovDerivPointwiseInner_continuous"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovDerivPointwiseInner_continuous ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovDerivPointwiseInner_continuous

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorCovDerivPointwiseInner_integrable
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) :
    MeasureTheory.Integrable
      (tensorCovDerivPointwiseInner (I := I) (M := M) g r s S T)
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
  have : MeasureTheory.IsFiniteMeasureOnCompacts
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) g
  exact (tensorCovDerivPointwiseInner_continuous
      (I := I) (M := M) g r s S T).integrable_of_hasCompactSupport
    (tensorCovDerivPointwiseInner_hasCompactSupport
      (I := I) (M := M) g r s S T)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovDerivPointwiseInner_integrable then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovDerivPointwiseInner_integrable"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovDerivPointwiseInner_integrable ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovDerivPointwiseInner_integrable

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
