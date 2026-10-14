import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Variational.PreHilbert
import Submission.DifferentialGeometry.Geometry.Connection.ChartTensorNabla.TensorRS.ChartTensorRSCovariantDerivative
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Chart.Density
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Basic
import Mathlib.Algebra.Order.Chebyshev

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection


noncomputable section

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace HebeyBlock

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2

open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private lemma intrinsic_sum_norm_sq_le_card_mul_sum_norm_sq
    {ι : Type*} {X : Type*} [SeminormedAddCommGroup X]
    (s : Finset ι) (x : ι → X) :
    ‖∑ i ∈ s, x i‖ ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖x i‖ ^ 2 := by
  classical
  have h_tri : ‖∑ i ∈ s, x i‖ ≤ ∑ i ∈ s, ‖x i‖ := norm_sum_le _ _
  have h_lhs_nn : 0 ≤ ‖∑ i ∈ s, x i‖ := norm_nonneg _
  have h_sq_tri : ‖∑ i ∈ s, x i‖ ^ 2 ≤ (∑ i ∈ s, ‖x i‖) ^ 2 := by
    have := mul_self_le_mul_self h_lhs_nn h_tri
    rw [← sq, ← sq] at this
    exact this
  have h_pmi : (∑ i ∈ s, ‖x i‖) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖x i‖ ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  exact h_sq_tri.trans h_pmi

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.intrinsic_sum_norm_sq_le_card_mul_sum_norm_sq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.HebeyBlock.intrinsic_sum_norm_sq_le_card_mul_sum_norm_sq target :: scope.openDecls } }

private lemma intrinsic_norm_sq_neg_sum_add_sum_le_two_mul
    {r' s' : ℕ} {X : Type*} [SeminormedAddCommGroup X]
    (x : Fin r' → X) (y : Fin s' → X) :
    ‖- (∑ i : Fin r', x i) + (∑ l : Fin s', y l)‖ ^ 2 ≤
      2 * (‖∑ i : Fin r', x i‖ ^ 2 + ‖∑ l : Fin s', y l‖ ^ 2) := by
  classical
  set u : X := ∑ i : Fin r', x i
  set v : X := ∑ l : Fin s', y l
  have h_tri : ‖- u + v‖ ≤ ‖u‖ + ‖v‖ := by
    calc ‖- u + v‖ ≤ ‖- u‖ + ‖v‖ := norm_add_le _ _
      _ = ‖u‖ + ‖v‖ := by rw [norm_neg]
  have h_lhs_nn : 0 ≤ ‖- u + v‖ := norm_nonneg _
  have h_sq : ‖- u + v‖ ^ 2 ≤ (‖u‖ + ‖v‖) ^ 2 := by
    have := mul_self_le_mul_self h_lhs_nn h_tri
    rw [← sq, ← sq] at this
    exact this
  have h_abc : (‖u‖ + ‖v‖) ^ 2 ≤ 2 * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
    have h_id : (‖u‖ + ‖v‖) ^ 2 + (‖u‖ - ‖v‖) ^ 2 =
        2 * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by ring
    have h_diff_nn : 0 ≤ (‖u‖ - ‖v‖) ^ 2 := sq_nonneg _
    linarith
  exact h_sq.trans h_abc

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.intrinsic_norm_sq_neg_sum_add_sum_le_two_mul
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.HebeyBlock.intrinsic_norm_sq_neg_sum_add_sum_le_two_mul target :: scope.openDecls } }

variable (I M) in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem intrinsicG1G3BridgePouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C_bridge : ℝ, 0 ≤ C_bridge ∧
      ∀ (S : SmoothCcTensor g r s) (k : Fin (Module.finrank ℝ E)) {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ‖- (∑ i : Fin r,
              chartTensorRSInputSlotCorrection (I := I) r s g α
                (fun b' => S.toSection b')
                (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k) b i)
          + (∑ l : Fin s,
              chartTensorRSOutputSlotCorrection (I := I) r s g α
                (fun b' => S.toSection b')
                (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k) b l)‖ ^ 2 ≤
          C_bridge *
            ((∑ i : Fin r,
                ‖chartTensorRSInputSlotCorrection (I := I) r s g α
                    (fun b' => S.toSection b')
                    (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k) b i‖ ^ 2) +
              (∑ l : Fin s,
                ‖chartTensorRSOutputSlotCorrection (I := I) r s g α
                    (fun b' => S.toSection b')
                    (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k) b l‖ ^ 2)) := by
  classical
  set C_bridge : ℝ := 2 * ((r : ℝ) + s) with hC_bridge_def
  have hC_bridge_nn : 0 ≤ C_bridge := by
    rw [hC_bridge_def]; positivity
  refine ⟨C_bridge, hC_bridge_nn, ?_⟩
  intro S k b _hb
  set a : Fin r → TensorRSSpace r s I b := fun i =>
    chartTensorRSInputSlotCorrection (I := I) r s g α
      (fun b' => S.toSection b') (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k) b i
    with ha_def
  set c : Fin s → TensorRSSpace r s I b := fun l =>
    chartTensorRSOutputSlotCorrection (I := I) r s g α
      (fun b' => S.toSection b') (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k) b l
    with hc_def
  have h_X_sq_split :
      ‖- (∑ i : Fin r, a i) + (∑ l : Fin s, c l)‖ ^ 2 ≤
        2 * (‖∑ i : Fin r, a i‖ ^ 2 + ‖∑ l : Fin s, c l‖ ^ 2) :=
    intrinsic_norm_sq_neg_sum_add_sum_le_two_mul (r' := r) (s' := s) a c
  have h_sum_a_sq :
      ‖∑ i : Fin r, a i‖ ^ 2 ≤ (r : ℝ) * ∑ i : Fin r, ‖a i‖ ^ 2 := by
    have h := intrinsic_sum_norm_sq_le_card_mul_sum_norm_sq
      (s := (Finset.univ : Finset (Fin r))) a
    have hcard : ((Finset.univ : Finset (Fin r)).card : ℝ) = (r : ℝ) := by
      rw [Finset.card_univ, Fintype.card_fin]
    rw [hcard] at h
    exact h
  have h_sum_c_sq :
      ‖∑ l : Fin s, c l‖ ^ 2 ≤ (s : ℝ) * ∑ l : Fin s, ‖c l‖ ^ 2 := by
    have h := intrinsic_sum_norm_sq_le_card_mul_sum_norm_sq
      (s := (Finset.univ : Finset (Fin s))) c
    have hcard : ((Finset.univ : Finset (Fin s)).card : ℝ) = (s : ℝ) := by
      rw [Finset.card_univ, Fintype.card_fin]
    rw [hcard] at h
    exact h
  have h_a_sum_nn : 0 ≤ ∑ i : Fin r, ‖a i‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have h_c_sum_nn : 0 ≤ ∑ l : Fin s, ‖c l‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have h_X_sq_bound :
      ‖- (∑ i : Fin r, a i) + (∑ l : Fin s, c l)‖ ^ 2 ≤
        2 * (r : ℝ) * (∑ i : Fin r, ‖a i‖ ^ 2) +
          2 * (s : ℝ) * (∑ l : Fin s, ‖c l‖ ^ 2) := by
    have h1 : 2 * (‖∑ i : Fin r, a i‖ ^ 2 + ‖∑ l : Fin s, c l‖ ^ 2) ≤
        2 * ((r : ℝ) * ∑ i : Fin r, ‖a i‖ ^ 2
              + (s : ℝ) * ∑ l : Fin s, ‖c l‖ ^ 2) := by
      have h_add_le :
          ‖∑ i : Fin r, a i‖ ^ 2 + ‖∑ l : Fin s, c l‖ ^ 2 ≤
            (r : ℝ) * (∑ i : Fin r, ‖a i‖ ^ 2) +
              (s : ℝ) * (∑ l : Fin s, ‖c l‖ ^ 2) :=
        add_le_add h_sum_a_sq h_sum_c_sq
      have h_2_nn : (0 : ℝ) ≤ 2 := by norm_num
      exact mul_le_mul_of_nonneg_left h_add_le h_2_nn
    refine h_X_sq_split.trans ?_
    have h_rw :
        2 * ((r : ℝ) * ∑ i : Fin r, ‖a i‖ ^ 2
              + (s : ℝ) * ∑ l : Fin s, ‖c l‖ ^ 2) =
          2 * (r : ℝ) * (∑ i : Fin r, ‖a i‖ ^ 2) +
            2 * (s : ℝ) * (∑ l : Fin s, ‖c l‖ ^ 2) := by ring
    rw [h_rw] at h1
    exact h1
  have h_r_2_le : 2 * (r : ℝ) ≤ 2 * ((r : ℝ) + s) := by
    have : (0 : ℝ) ≤ (s : ℝ) := by positivity
    linarith
  have h_s_2_le : 2 * (s : ℝ) ≤ 2 * ((r : ℝ) + s) := by
    have : (0 : ℝ) ≤ (r : ℝ) := by positivity
    linarith
  have h_dominate :
      2 * (r : ℝ) * (∑ i : Fin r, ‖a i‖ ^ 2) +
        2 * (s : ℝ) * (∑ l : Fin s, ‖c l‖ ^ 2) ≤
      C_bridge *
        ((∑ i : Fin r, ‖a i‖ ^ 2) + (∑ l : Fin s, ‖c l‖ ^ 2)) := by
    have h1 : 2 * (r : ℝ) * (∑ i : Fin r, ‖a i‖ ^ 2) ≤
        2 * ((r : ℝ) + s) * (∑ i : Fin r, ‖a i‖ ^ 2) :=
      mul_le_mul_of_nonneg_right h_r_2_le h_a_sum_nn
    have h2 : 2 * (s : ℝ) * (∑ l : Fin s, ‖c l‖ ^ 2) ≤
        2 * ((r : ℝ) + s) * (∑ l : Fin s, ‖c l‖ ^ 2) :=
      mul_le_mul_of_nonneg_right h_s_2_le h_c_sum_nn
    have h_split :
        C_bridge *
          ((∑ i : Fin r, ‖a i‖ ^ 2) + (∑ l : Fin s, ‖c l‖ ^ 2)) =
        2 * ((r : ℝ) + s) * (∑ i : Fin r, ‖a i‖ ^ 2) +
          2 * ((r : ℝ) + s) * (∑ l : Fin s, ‖c l‖ ^ 2) := by
      rw [hC_bridge_def]; ring
    rw [h_split]
    linarith
  exact h_X_sq_bound.trans h_dominate

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.HebeyBlock.intrinsicG1G3BridgePouTsupport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.HebeyBlock.intrinsicG1G3BridgePouTsupport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.HebeyBlock.intrinsicG1G3BridgePouTsupport ``Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.intrinsicG1G3BridgePouTsupport

variable (I M) in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem norm_sq_triv_neg_sum_add_sum_le_const_mul_sum_norm_sq_on_pouTsupport_intrinsic_h1
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C_bridge : ℝ, 0 ≤ C_bridge ∧
      ∀ (S : SmoothCcTensorH1 g r s) (k : Fin (Module.finrank ℝ E)) {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ‖- (∑ i : Fin r,
              chartTensorRSInputSlotCorrection (I := I) r s g α
                (fun b' => S.toCcTensor.toSection b')
                (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k) b i)
          + (∑ l : Fin s,
              chartTensorRSOutputSlotCorrection (I := I) r s g α
                (fun b' => S.toCcTensor.toSection b')
                (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k) b l)‖ ^ 2 ≤
          C_bridge *
            ((∑ i : Fin r,
                ‖chartTensorRSInputSlotCorrection (I := I) r s g α
                    (fun b' => S.toCcTensor.toSection b')
                    (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k) b i‖ ^ 2) +
              (∑ l : Fin s,
                ‖chartTensorRSOutputSlotCorrection (I := I) r s g α
                    (fun b' => S.toCcTensor.toSection b')
                    (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k) b l‖ ^ 2)) := by
  obtain ⟨C_bridge, hC_nn, h⟩ :=
    intrinsicG1G3BridgePouTsupport (I := I) (M := M) g r s α
  exact ⟨C_bridge, hC_nn, fun S k b hb => h S.toCcTensor k hb⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.HebeyBlock.norm_sq_triv_neg_sum_add_sum_le_const_mul_sum_norm_sq_on_pouTsupport_intrinsic_h1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.HebeyBlock.norm_sq_triv_neg_sum_add_sum_le_const_mul_sum_norm_sq_on_pouTsupport_intrinsic_h1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.HebeyBlock.norm_sq_triv_neg_sum_add_sum_le_const_mul_sum_norm_sq_on_pouTsupport_intrinsic_h1 ``Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.norm_sq_triv_neg_sum_add_sum_le_const_mul_sum_norm_sq_on_pouTsupport_intrinsic_h1

end HebeyBlock
end Sobolev
end Analysis
end DifferentialGeometry

end
