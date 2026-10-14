import Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.IntegrationByParts.FirstOrder.DirichletPairing
import Submission.DifferentialGeometry.Geometry.Connection.MetricCompatibility.Tensor.Lowering

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Geometry.Connection


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
    CovariantDerivative
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators _root_.Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Elliptic

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Tensor0SNabla _root_.Submission.DifferentialGeometry.TensorRSNabla
    DifferentialGeometry.TensorMetricLowering

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Elliptic.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

private local instance _root_.Submission.DifferentialGeometry.Analysis.Elliptic.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Elliptic.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Elliptic.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Elliptic.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma toModel_liftedTensorSection_zero_eq_apply_unit_reindex
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S : Cₛ^∞⟮I; TensorRSModel 0 s ℝ E, (fun x : M => TensorRSSpace 0 s I x)⟯)
    (y : M) (u : Fin (0 + s) → E) :
    Tensor0SSpace.toModel (liftedTensorSection (I := I) (M := M) g 0 s S y) u =
      Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from S y)
            (Tensor0SSpace.ofModel
              (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ))))
        (fun j : Fin s => u (Fin.natAdd 0 j)) := by
  rw [toModel_liftedTensorSection]
  rw [lowerAllUpperIndices_apply]
  rw [separableFormAt_zero]
  rw [toModel_tensorRS_apply (I := I) (M := M) 0 s y (S y)
    (Tensor0SSpace.ofModel
      (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)))]
  rw [Tensor0SSpace.toModel_ofModel]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.toModel_liftedTensorSection_zero_eq_apply_unit_reindex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.toModel_liftedTensorSection_zero_eq_apply_unit_reindex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.toModel_liftedTensorSection_zero_eq_apply_unit_reindex ``Submission.DifferentialGeometry.Analysis.Elliptic.toModel_liftedTensorSection_zero_eq_apply_unit_reindex

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem tensorInnerPointwise_covDeriv_eq_tensorInnerPointwise_0s_lowered_two
    (g : SmoothRiemannianMetric I M)
    (W S : SmoothCcTensor g 0 2) (x : M) (a b : TangentSpace I x) :
    tensorInnerPointwise (I := I) (M := M) g 0 2 x
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g 0 2 W x
            (tangentSpaceModelContinuousLinearEquiv (I := I) x a)))
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g 0 2 S x
            (tangentSpaceModelContinuousLinearEquiv (I := I) x b))) =
      covariantTensorInnerPointwise (I := I) (M := M) (0 + 2) g x
        (Tensor0SSpace.toModel
          (loweredCovDerivAt (I := I) (M := M) g 0 2 W.toSection x a))
        (Tensor0SSpace.toModel
          (loweredCovDerivAt (I := I) (M := M) g 0 2 S.toSection x b)) := by
  unfold tensorInnerPointwise
  rw [show lowerAllUpperIndices (I := I) (M := M) g 0 2 x
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g 0 2 W x
            (tangentSpaceModelContinuousLinearEquiv (I := I) x a))) =
      Tensor0SSpace.toModel
        (loweredCovDerivAt (I := I) (M := M) g 0 2 W.toSection x a) from
    (loweredCovDerivAt_eq_lower_tensorCovDerivAt (I := I) (M := M) g W.toSection x a).symm]
  rw [show lowerAllUpperIndices (I := I) (M := M) g 0 2 x
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g 0 2 S x
            (tangentSpaceModelContinuousLinearEquiv (I := I) x b))) =
      Tensor0SSpace.toModel
        (loweredCovDerivAt (I := I) (M := M) g 0 2 S.toSection x b) from
    (loweredCovDerivAt_eq_lower_tensorCovDerivAt (I := I) (M := M) g S.toSection x b).symm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.tensorInnerPointwise_covDeriv_eq_tensorInnerPointwise_0s_lowered_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.tensorInnerPointwise_covDeriv_eq_tensorInnerPointwise_0s_lowered_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.tensorInnerPointwise_covDeriv_eq_tensorInnerPointwise_0s_lowered_two ``Submission.DifferentialGeometry.Analysis.Elliptic.tensorInnerPointwise_covDeriv_eq_tensorInnerPointwise_0s_lowered_two

omit [CompactSpace M] [SigmaCompactSpace M] in
theorem tensorCovDerivPointwiseInner_eq_lowered_orthoFrame_diag_sum_two
    (g : SmoothRiemannianMetric I M)
    (T v : SmoothCcTensor g 0 2) (b : M)
    (B : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y)
    (hB_orth : ∀ i j, g.inner b (B i b) (B j b) = if i = j then (1 : ℝ) else 0) :
    tensorCovDerivPointwiseInner (I := I) (M := M) g 0 2 T v b =
      ∑ i : Fin (Module.finrank ℝ E),
        covariantTensorInnerPointwise (I := I) (M := M) (0 + 2) g b
          (Tensor0SSpace.toModel
            (loweredCovDerivAt (I := I) (M := M) g 0 2 T.toSection b (B i b)))
          (Tensor0SSpace.toModel
            (loweredCovDerivAt (I := I) (M := M) g 0 2 v.toSection b (B i b))) := by
  classical
  have hB_li : LinearIndependent ℝ (fun i : Fin (Module.finrank ℝ E) => B i b) := by
    rw [linearIndependent_iff']
    intro fs c hsum k hk_mem
    have h_zero : g.inner b (B k b) (∑ j ∈ fs, c j • B j b) = 0 := by
      rw [hsum]; simp
    rw [map_sum] at h_zero
    have h_pull : ∀ j ∈ fs, g.inner b (B k b) (c j • B j b) =
        c j * g.inner b (B k b) (B j b) := by
      intro j _
      rw [(g.inner b (B k b)).map_smul (c j) (B j b), smul_eq_mul]
    rw [Finset.sum_congr rfl h_pull] at h_zero
    have h_pull2 : ∀ j ∈ fs, c j * g.inner b (B k b) (B j b) =
        c j * (if k = j then (1 : ℝ) else 0) := by
      intro j _
      rw [hB_orth k j]
    rw [Finset.sum_congr rfl h_pull2] at h_zero
    rw [Finset.sum_eq_single_of_mem k hk_mem] at h_zero
    · rw [if_pos rfl, mul_one] at h_zero
      exact h_zero
    · intro j _ hjk
      rw [if_neg (fun h => hjk h.symm), _root_.MulZeroClass.mul_zero]
  have hcard : Fintype.card (Fin (Module.finrank ℝ E)) =
      Module.finrank ℝ (TangentSpace I b) := by
    rw [Fintype.card_fin]
    rfl
  set tangentFrame : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I b) :=
    basisOfLinearIndependentOfCardEqFinrank hB_li hcard with htangentFrame_def
  set frame : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E :=
    tangentFrame.map
      (tangentSpaceModelContinuousLinearEquiv (I := I) b).toLinearEquiv with hframe_def
  have hframe_eq : ∀ i, frame i =
      tangentSpaceModelContinuousLinearEquiv (I := I) b (B i b) := by
    intro i
    rw [hframe_def]
    rw [Module.Basis.map_apply, htangentFrame_def]
    change tangentSpaceModelContinuousLinearEquiv (I := I) b
        ((basisOfLinearIndependentOfCardEqFinrank hB_li hcard :
          Fin (Module.finrank ℝ E) → TangentSpace I b) i) = _
    rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  have hframe_orth : ∀ i j,
      modelInnerAt (I := I) (M := M) g b (frame i) (frame j) =
        if i = j then (1 : ℝ) else 0 := by
    intro i j
    rw [hframe_eq i, hframe_eq j, modelInnerAt_apply,
      (tangentSpaceModelContinuousLinearEquiv (I := I) b).symm_apply_apply,
      (tangentSpaceModelContinuousLinearEquiv (I := I) b).symm_apply_apply]
    exact hB_orth i j
  rw [tensorCovDerivPointwiseInner_eq_orthoFrame_diag_sum
    (I := I) (M := M) g 0 2 T v b frame hframe_orth]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hframe_eq i]
  exact tensorInnerPointwise_covDeriv_eq_tensorInnerPointwise_0s_lowered_two
    (I := I) (M := M) g T v b (B i b) (B i b)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.tensorCovDerivPointwiseInner_eq_lowered_orthoFrame_diag_sum_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.tensorCovDerivPointwiseInner_eq_lowered_orthoFrame_diag_sum_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.tensorCovDerivPointwiseInner_eq_lowered_orthoFrame_diag_sum_two ``Submission.DifferentialGeometry.Analysis.Elliptic.tensorCovDerivPointwiseInner_eq_lowered_orthoFrame_diag_sum_two

end Elliptic
end Analysis
end DifferentialGeometry

end
