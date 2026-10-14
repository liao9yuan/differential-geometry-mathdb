import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.VariationalIdentity.ChartTestDecoupling

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Connection


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators _root_.Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2

open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Tensor.TensorRSRiemannian
open _root_.Submission.DifferentialGeometry.TensorRSNabla
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartLocalLaplacian

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

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
private lemma covGradBundle_trivFibre_eq'
    (r s : ℕ) (α : M) (b : M)
    (Φ : TangentSpace I b →L[ℝ] TensorRSSpace r s I b) :
    (_root_.FiberBundle.trivializationAt (E →L[ℝ] TensorRSModel r s ℝ E)
        (fun y : M => TangentSpace I y →L[ℝ] TensorRSSpace r s I y) α
        ⟨b, Φ⟩).2 =
      ((_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b).comp
        (Φ.comp ((_root_.FiberBundle.trivializationAt E (TangentSpace I) α).symmL ℝ b)) :=
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGradBundle_trivFibre_eq'
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGradBundle_trivFibre_eq' target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M] in
theorem tensorChartComponentRaw_covGrad
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin (s + 1) → Fin (Module.finrank ℝ E))
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    tensorChartComponentRaw (I := I) (M := M) g r (s + 1)
        (covGrad (I := I) (M := M) g r s S) α Idx Jdx
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) =
      euclidPartial (E := E) (Jdx 0)
          (chartPushedRaw I α (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx
            (Matrix.vecTail Jdx))) y
        + covDerivLowerOrderTerm (I := I) (M := M) g r s S α (Jdx 0) Idx
            (Matrix.vecTail Jdx) y := by
  classical
  let : TopologicalSpace (_root_.Bundle.TotalSpace (Tensor0SModel r ℝ E)
      (fun z : M => Tensor0SSpace r I z)) := tensor0SBundleTopology r
  let : TopologicalSpace (_root_.Bundle.TotalSpace (Tensor0SModel (s + 1) ℝ E)
      (fun z : M => Tensor0SSpace (s + 1) I z)) := tensor0SBundleTopology (s + 1)
  let : TopologicalSpace (_root_.Bundle.TotalSpace (TensorRSModel r (s + 1) ℝ E)
      (fun z : M => TensorRSSpace r (s + 1) I z)) :=
    tensorRSBundleTopology r (s + 1)
  let : FiberBundle (TensorRSModel r (s + 1) ℝ E)
      (fun z : M => TensorRSSpace r (s + 1) I z) :=
    tensorRSBundleFiber r (s + 1)
  let : VectorBundle ℝ (TensorRSModel r (s + 1) ℝ E)
      (fun z : M => TensorRSSpace r (s + 1) I z) :=
    tensorRSBundle_vector r (s + 1)
  set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
  have hb_chart : b ∈ (chartAt H α).source :=
    symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) α hy
  have hb_base : b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact hb_chart
  have hb_baseS1 : b ∈ (_root_.FiberBundle.trivializationAt (TensorRSModel r (s + 1) ℝ E)
      (fun z : M => TensorRSSpace r (s + 1) I z) α).baseSet := by
    change b ∈ ((_root_.FiberBundle.trivializationAt (Tensor0SModel r ℝ E)
        (fun z : M => Tensor0SSpace r I z) α).baseSet) ∩
      ((_root_.FiberBundle.trivializationAt (Tensor0SModel (s + 1) ℝ E)
        (fun z : M => Tensor0SSpace (s + 1) I z) α).baseSet)
    exact ⟨hb_base, hb_base⟩
  have hy_pre : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
    rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
    exact hy
  have hphi_b : extChartAt I α b = (toEuclidean (E := E)).symm y := by
    rw [hb_def]; exact (extChartAt I α).right_inv hy_pre
  have hb_int :
      extChartAt I α b ∈ interior ((extChartAt I α).target : Set E) := by
    rw [hphi_b, (isOpen_extChartAt_target (I := I) α).interior_eq]
    exact hy_pre
  have hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α := by
    refine ⟨⟨?_, ?_⟩, hb_int⟩
    · rw [extChartAt_source]; exact hb_chart
    · rw [TangentBundle.trivializationAt_baseSet]; exact hb_chart
  set Φ : TangentSpace I b →L[ℝ] TensorRSSpace r s I b :=
    tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)
      (fun z : M => S.toSection z) b with hΦ_def
  rw [tensorChartComponentRaw_def]
  unfold tensorTrivProj
  rw [covGrad_toSection_apply (I := I) (M := M) g r s S b]
  rw [show (tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)
        (fun z : M => S.toSection z) b) = Φ from rfl]
  rw [Bundle.Trivialization.continuousLinearMapAt_apply,
    (_root_.FiberBundle.trivializationAt (TensorRSModel r (s + 1) ℝ E)
        (fun z : M => TensorRSSpace r (s + 1) I z) α).coe_linearMapAt_of_mem
      (R := ℝ) hb_baseS1]
  beta_reduce
  rw [covGradBundleEquiv_trivializationAt_eq (I := I) (M := M) r s α hb_base Φ]
  rw [tensorChartComponentProjection_apply,
    covGradModelEquiv_apply (E := E) r s]
  rw [covGradBundle_trivFibre_eq' (I := I) (M := M) r s α b Φ]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  have hsymmL : (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).symmL ℝ b
      ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) (Jdx 0)) =
      DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α (Jdx 0) b := rfl
  rw [hsymmL]
  rw [show Φ (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α (Jdx 0) b) =
      tensorCovDerivAt (I := I) (M := M) g r s S b
        (tangentSpaceModelContinuousLinearEquiv (I := I) b
          (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α (Jdx 0) b)) from by
      rw [tensorCovDerivAt_def,
        (tangentSpaceModelContinuousLinearEquiv (I := I) b).symm_apply_apply]]
  rw [tensorCovDerivAt_eq_chartTensorRSCovariantDerivative (I := I) (M := M)
    g r s S α (Jdx 0) hb_good]
  exact covDerivComponent_eq_euclidPartial_add_lowerOrder (I := I) (M := M)
    g r s S α (Jdx 0) Idx (Matrix.vecTail Jdx) hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw_covGrad then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw_covGrad"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw_covGrad ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw_covGrad

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
