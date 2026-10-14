import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChristoffelCorrection.ChristoffelBound
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.NormEstimates.NormComparison
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChartComponent.ComponentL2BoundUniform
import Submission.DifferentialGeometry.Geometry.Connection.ChartTensorNabla.TensorRS.ChartTensorRSCovariantDerivative

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2

open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
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

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
private lemma chartTensorRSInputSlotCorrection_norm_sq_le_of_F_bound
    (r s : ℕ) (g : SmoothRiemannianMetric I M) (α : M)
    (T : Π b' : M, TensorRSSpace r s I b')
    (X : Π b' : M, TangentSpace I b') (b : M) (k : Fin r)
    {M_F : ℝ}
    (hF_bound : ‖chartTensorRSInputSlotCorrection (I := I) r s g α T X b k‖ ≤
        M_F * ‖T b‖) :
    ‖chartTensorRSInputSlotCorrection (I := I) r s g α T X b k‖ ^ 2 ≤
      M_F ^ 2 * ‖T b‖ ^ 2 := by
  classical
  have hLHS_nn : 0 ≤ ‖chartTensorRSInputSlotCorrection (I := I) r s g α T X b k‖ :=
    norm_nonneg _
  have hT_nn : 0 ≤ ‖T b‖ := norm_nonneg _
  have hsq : ‖chartTensorRSInputSlotCorrection (I := I) r s g α T X b k‖ ^ 2 ≤
      (M_F * ‖T b‖) ^ 2 := by
    have := mul_self_le_mul_self hLHS_nn hF_bound
    have h_lhs_sq :
        ‖chartTensorRSInputSlotCorrection (I := I) r s g α T X b k‖ *
        ‖chartTensorRSInputSlotCorrection (I := I) r s g α T X b k‖ =
        ‖chartTensorRSInputSlotCorrection (I := I) r s g α T X b k‖ ^ 2 := by rw [sq]
    have h_rhs_sq : (M_F * ‖T b‖) * (M_F * ‖T b‖) = (M_F * ‖T b‖) ^ 2 := by rw [sq]
    linarith
  have h_expand : (M_F * ‖T b‖) ^ 2 = M_F ^ 2 * ‖T b‖ ^ 2 := by ring
  linarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartTensorRSInputSlotCorrection_norm_sq_le_of_F_bound
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartTensorRSInputSlotCorrection_norm_sq_le_of_F_bound target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
private lemma chartTensorRSOutputSlotCorrection_norm_sq_le_of_F_bound
    (r s : ℕ) (g : SmoothRiemannianMetric I M) (α : M)
    (T : Π b' : M, TensorRSSpace r s I b')
    (X : Π b' : M, TangentSpace I b') (b : M) (l : Fin s)
    {M_F : ℝ}
    (hF_bound : ‖chartTensorRSOutputSlotCorrection (I := I) r s g α T X b l‖ ≤
        M_F * ‖T b‖) :
    ‖chartTensorRSOutputSlotCorrection (I := I) r s g α T X b l‖ ^ 2 ≤
      M_F ^ 2 * ‖T b‖ ^ 2 := by
  classical
  have hLHS_nn : 0 ≤ ‖chartTensorRSOutputSlotCorrection (I := I) r s g α T X b l‖ :=
    norm_nonneg _
  have hT_nn : 0 ≤ ‖T b‖ := norm_nonneg _
  have hsq : ‖chartTensorRSOutputSlotCorrection (I := I) r s g α T X b l‖ ^ 2 ≤
      (M_F * ‖T b‖) ^ 2 := by
    have := mul_self_le_mul_self hLHS_nn hF_bound
    have h_lhs_sq :
        ‖chartTensorRSOutputSlotCorrection (I := I) r s g α T X b l‖ *
        ‖chartTensorRSOutputSlotCorrection (I := I) r s g α T X b l‖ =
        ‖chartTensorRSOutputSlotCorrection (I := I) r s g α T X b l‖ ^ 2 := by rw [sq]
    have h_rhs_sq : (M_F * ‖T b‖) * (M_F * ‖T b‖) = (M_F * ‖T b‖) ^ 2 := by rw [sq]
    linarith
  have h_expand : (M_F * ‖T b‖) ^ 2 = M_F ^ 2 * ‖T b‖ ^ 2 := by ring
  linarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartTensorRSOutputSlotCorrection_norm_sq_le_of_F_bound
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartTensorRSOutputSlotCorrection_norm_sq_le_of_F_bound target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
private lemma section_norm_eq_toFun_norm
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (S : SmoothCcTensor g r s) (b : M) :
    ‖S.toSection b‖ = ‖S.toFun b‖ := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.section_norm_eq_toFun_norm
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.section_norm_eq_toFun_norm target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem
    exists_sum_chart_christoffel_correction_norm_sq_le_const_mul_tensorInnerPointwise_on_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (X : Π b' : M, TangentSpace I b')
    (M_F : ℝ)
    (hM_F_input : ∀ (S : SmoothCcTensor g r s) {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ∀ k : Fin r,
          ‖chartTensorRSInputSlotCorrection (I := I) r s g α
              (fun b' => S.toSection b') X b k‖ ≤
            M_F * ‖S.toSection b‖)
    (hM_F_output : ∀ (S : SmoothCcTensor g r s) {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ∀ l : Fin s,
          ‖chartTensorRSOutputSlotCorrection (I := I) r s g α
              (fun b' => S.toSection b') X b l‖ ≤
            M_F * ‖S.toSection b‖)
    (K_S : ℝ) (hK_S_nn : 0 ≤ K_S)
    (hK_S_bound : ∀ (S : SmoothCcTensor g r s) {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ‖S.toSection b‖ ^ 2 ≤
          K_S * tensorInnerPointwise (I := I) (M := M) g r s b
            (S.toFun b) (S.toFun b)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g r s) {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
          ((∑ k : Fin r, ‖chartTensorRSInputSlotCorrection (I := I) r s g α
                (fun b' => S.toSection b') X b k‖ ^ 2) +
            (∑ l : Fin s, ‖chartTensorRSOutputSlotCorrection (I := I) r s g α
                (fun b' => S.toSection b') X b l‖ ^ 2)) ≤
            C * tensorInnerPointwise (I := I) (M := M) g r s b
              (S.toFun b) (S.toFun b) := by
  classical
  refine ⟨((r : ℝ) + (s : ℝ)) * M_F ^ 2 * K_S, ?_, ?_⟩
  · positivity
  intro S b hb
  have h_sec : ‖S.toSection b‖ ^ 2 ≤
      K_S * tensorInnerPointwise (I := I) (M := M) g r s b
        (S.toFun b) (S.toFun b) := hK_S_bound S hb
  have h_in_each : ∀ k : Fin r,
      ‖chartTensorRSInputSlotCorrection (I := I) r s g α
          (fun b' => S.toSection b') X b k‖ ^ 2 ≤
        M_F ^ 2 * ‖S.toSection b‖ ^ 2 := by
    intro k
    exact chartTensorRSInputSlotCorrection_norm_sq_le_of_F_bound
      (I := I) r s g α (fun b' => S.toSection b') X b k
      (hM_F_input S hb k)
  have h_out_each : ∀ l : Fin s,
      ‖chartTensorRSOutputSlotCorrection (I := I) r s g α
          (fun b' => S.toSection b') X b l‖ ^ 2 ≤
        M_F ^ 2 * ‖S.toSection b‖ ^ 2 := by
    intro l
    exact chartTensorRSOutputSlotCorrection_norm_sq_le_of_F_bound
      (I := I) r s g α (fun b' => S.toSection b') X b l
      (hM_F_output S hb l)
  have h_in_sum : (∑ k : Fin r,
        ‖chartTensorRSInputSlotCorrection (I := I) r s g α
            (fun b' => S.toSection b') X b k‖ ^ 2) ≤
      (r : ℝ) * (M_F ^ 2 * ‖S.toSection b‖ ^ 2) := by
    have h_le := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin r)))
      (f := fun k => ‖chartTensorRSInputSlotCorrection (I := I) r s g α
        (fun b' => S.toSection b') X b k‖ ^ 2)
      (g := fun _ => M_F ^ 2 * ‖S.toSection b‖ ^ 2)
      (fun k _ => h_in_each k)
    have h_sum_const :
        (∑ _k : Fin r, M_F ^ 2 * ‖S.toSection b‖ ^ 2) =
          (r : ℝ) * (M_F ^ 2 * ‖S.toSection b‖ ^ 2) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      simp [nsmul_eq_mul]
    linarith
  have h_out_sum : (∑ l : Fin s,
        ‖chartTensorRSOutputSlotCorrection (I := I) r s g α
            (fun b' => S.toSection b') X b l‖ ^ 2) ≤
      (s : ℝ) * (M_F ^ 2 * ‖S.toSection b‖ ^ 2) := by
    have h_le := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin s)))
      (f := fun l => ‖chartTensorRSOutputSlotCorrection (I := I) r s g α
        (fun b' => S.toSection b') X b l‖ ^ 2)
      (g := fun _ => M_F ^ 2 * ‖S.toSection b‖ ^ 2)
      (fun l _ => h_out_each l)
    have h_sum_const :
        (∑ _l : Fin s, M_F ^ 2 * ‖S.toSection b‖ ^ 2) =
          (s : ℝ) * (M_F ^ 2 * ‖S.toSection b‖ ^ 2) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      simp [nsmul_eq_mul]
    linarith
  have h_combined :
      ((∑ k : Fin r,
          ‖chartTensorRSInputSlotCorrection (I := I) r s g α
              (fun b' => S.toSection b') X b k‖ ^ 2) +
        (∑ l : Fin s,
          ‖chartTensorRSOutputSlotCorrection (I := I) r s g α
              (fun b' => S.toSection b') X b l‖ ^ 2)) ≤
      ((r : ℝ) + (s : ℝ)) * (M_F ^ 2 * ‖S.toSection b‖ ^ 2) := by
    have h_dist : ((r : ℝ) + (s : ℝ)) * (M_F ^ 2 * ‖S.toSection b‖ ^ 2) =
        (r : ℝ) * (M_F ^ 2 * ‖S.toSection b‖ ^ 2) +
          (s : ℝ) * (M_F ^ 2 * ‖S.toSection b‖ ^ 2) := by ring
    linarith
  have h_M_F_sq_nn : 0 ≤ M_F ^ 2 := sq_nonneg _
  have h_rs_M_F_nn : 0 ≤ ((r : ℝ) + (s : ℝ)) * M_F ^ 2 := by positivity
  have h_chain :
      ((r : ℝ) + (s : ℝ)) * (M_F ^ 2 * ‖S.toSection b‖ ^ 2) ≤
        ((r : ℝ) + (s : ℝ)) * (M_F ^ 2 *
          (K_S * tensorInnerPointwise (I := I) (M := M) g r s b
            (S.toFun b) (S.toFun b))) := by
    have h_inner : M_F ^ 2 * ‖S.toSection b‖ ^ 2 ≤
        M_F ^ 2 *
          (K_S * tensorInnerPointwise (I := I) (M := M) g r s b
            (S.toFun b) (S.toFun b)) :=
      mul_le_mul_of_nonneg_left h_sec h_M_F_sq_nn
    have h_rs_nn : 0 ≤ ((r : ℝ) + (s : ℝ)) := by positivity
    exact mul_le_mul_of_nonneg_left h_inner h_rs_nn
  have h_rearrange :
      ((r : ℝ) + (s : ℝ)) * (M_F ^ 2 *
        (K_S * tensorInnerPointwise (I := I) (M := M) g r s b
          (S.toFun b) (S.toFun b))) =
      ((r : ℝ) + (s : ℝ)) * M_F ^ 2 * K_S *
        tensorInnerPointwise (I := I) (M := M) g r s b
          (S.toFun b) (S.toFun b) := by ring
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_sum_chart_christoffel_correction_norm_sq_le_const_mul_tensorInnerPointwise_on_pouTsupport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_sum_chart_christoffel_correction_norm_sq_le_const_mul_tensorInnerPointwise_on_pouTsupport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_sum_chart_christoffel_correction_norm_sq_le_const_mul_tensorInnerPointwise_on_pouTsupport ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_sum_chart_christoffel_correction_norm_sq_le_const_mul_tensorInnerPointwise_on_pouTsupport

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
