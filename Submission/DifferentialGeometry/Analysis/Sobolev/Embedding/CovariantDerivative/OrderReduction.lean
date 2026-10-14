import Submission.DifferentialGeometry.Analysis.Sobolev.Embedding.CovariantDerivative.Cm

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Topology _root_.Metric _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.NNReal _root_.BigOperators

namespace DifferentialGeometry.Analysis.Sobolev

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Tensor
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.IntrinsicSobolev

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem iteratedCovGradSobolevNorm_zero
    (g : SmoothRiemannianMetric I M) (r s k : ℕ) (T : SmoothCcTensor g r s) :
    iteratedCovGradSobolevNorm g r s k 0 T =
      ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) T‖ := by
  unfold iteratedCovGradSobolevNorm
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.iteratedCovGradSobolevNorm_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.iteratedCovGradSobolevNorm_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.iteratedCovGradSobolevNorm_zero ``Submission.DifferentialGeometry.Analysis.Sobolev.iteratedCovGradSobolevNorm_zero

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem toHs_norm_le_succ
    (g : SmoothRiemannianMetric I M) {r s : ℕ} (σ : ℕ)
    (T' : SmoothCcTensor g r s) :
    ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s) σ T'‖ ≤
      ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s) (σ + 1) T'‖ := by
  rw [tensorPouSobolevHilbert_norm_eq, tensorPouSobolevHilbert_norm_eq]
  refine ENNReal.toReal_mono ?_ (tensorPouSobolevHsNorm_le_succ (I := I) (M := M) g σ T')
  exact (tensorPouSobolevHsNorm_lt_top (I := I) (M := M) g (σ + 1) T').ne

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.toHs_norm_le_succ
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.toHs_norm_le_succ target :: scope.openDecls } }

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem toHs_norm_mono_order
    (g : SmoothRiemannianMetric I M) {r s : ℕ} {σ τ : ℕ} (hστ : σ ≤ τ)
    (T' : SmoothCcTensor g r s) :
    ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s) σ T'‖ ≤
      ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s) τ T'‖ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hστ
  clear hστ
  induction d with
  | zero => simp
  | succ d ih =>
      refine le_trans ih ?_
      rw [show σ + (d + 1) = (σ + d) + 1 from by ring]
      exact toHs_norm_le_succ (I := I) (M := M) g (σ + d) T'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.toHs_norm_mono_order then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.toHs_norm_mono_order"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.toHs_norm_mono_order ``Submission.DifferentialGeometry.Analysis.Sobolev.toHs_norm_mono_order

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem iteratedCovGradSobolevNorm_le_topOrder
    (g : SmoothRiemannianMetric I M) (r s k j : ℕ) (T : SmoothCcTensor g r s) :
    iteratedCovGradSobolevNorm g r s k j T ≤
      ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s + j) (2 * k)
        (iteratedCovGrad g r s j T)‖ := by
  unfold iteratedCovGradSobolevNorm
  exact toHs_norm_mono_order (I := I) (M := M) g
    (by omega : 2 * (k - j) ≤ 2 * k) (iteratedCovGrad g r s j T)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.iteratedCovGradSobolevNorm_le_topOrder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.iteratedCovGradSobolevNorm_le_topOrder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.iteratedCovGradSobolevNorm_le_topOrder ``Submission.DifferentialGeometry.Analysis.Sobolev.iteratedCovGradSobolevNorm_le_topOrder

attribute [-instance] Tensor0SBundle.tensorRSSpaceNormedAddCommGroup
  Tensor0SBundle.tensorRSSpaceNormedSpace in
omit [BoundarylessManifold I M] in
theorem iteratedCovGrad_toSobolev_embedding_Cm_of_rankBound
    (g : SmoothRiemannianMetric I M) (r s k m : ℕ)
    (h_super : 2 * k > Module.finrank ℝ E + 2 * m)
    (Cred : ℝ)
    (h_rank : ∀ (T : SmoothCcTensor g r s), ∀ j ∈ Finset.range (m + 1),
      ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s + j) (2 * k)
        (iteratedCovGrad g r s j T)‖ ≤
        Cred * ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) T‖) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (T : SmoothCcTensor g r s) (x : M),
        (∑ j ∈ Finset.range (m + 1),
            (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r (s + j) I b) :=
              Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g r (s + j)
            ‖(iteratedCovGrad g r s j T).toSection x‖)) ≤
          C * ((m + 1 : ℝ) * Cred) *
            ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) T‖ := by
  classical
  obtain ⟨C, hC_pos, hC⟩ :=
    iteratedCovGrad_toSobolev_embedding_Cm (I := I) (M := M) g r s k m h_super
  refine ⟨C, hC_pos, ?_⟩
  intro T x
  set N : ℝ := ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) T‖ with hN_def
  have hN_nn : 0 ≤ N := norm_nonneg _
  have h_perdeg : ∀ j ∈ Finset.range (m + 1),
      iteratedCovGradSobolevNorm g r s k j T ≤ Cred * N := by
    intro j hj
    exact le_trans
      (iteratedCovGradSobolevNorm_le_topOrder (I := I) (M := M) g r s k j T)
      (h_rank T j hj)
  refine le_trans (hC T x) ?_
  have h_sum_le :
      (∑ j ∈ Finset.range (m + 1), iteratedCovGradSobolevNorm g r s k j T) ≤
        (m + 1 : ℝ) * Cred * N := by
    calc (∑ j ∈ Finset.range (m + 1), iteratedCovGradSobolevNorm g r s k j T)
        ≤ ∑ _j ∈ Finset.range (m + 1), Cred * N := Finset.sum_le_sum h_perdeg
      _ = (Finset.range (m + 1)).card • (Cred * N) := by rw [Finset.sum_const]
      _ = (m + 1 : ℝ) * (Cred * N) := by
          rw [Finset.card_range, nsmul_eq_mul]; push_cast; ring
      _ = (m + 1 : ℝ) * Cred * N := by ring
  calc C * ∑ j ∈ Finset.range (m + 1), iteratedCovGradSobolevNorm g r s k j T
      ≤ C * ((m + 1 : ℝ) * Cred * N) :=
        mul_le_mul_of_nonneg_left h_sum_le (le_of_lt hC_pos)
    _ = C * ((m + 1 : ℝ) * Cred) * N := by ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.iteratedCovGrad_toSobolev_embedding_Cm_of_rankBound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.iteratedCovGrad_toSobolev_embedding_Cm_of_rankBound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.iteratedCovGrad_toSobolev_embedding_Cm_of_rankBound ``Submission.DifferentialGeometry.Analysis.Sobolev.iteratedCovGrad_toSobolev_embedding_Cm_of_rankBound

attribute [-instance] Tensor0SBundle.tensorRSSpaceNormedAddCommGroup
  Tensor0SBundle.tensorRSSpaceNormedSpace in
omit [BoundarylessManifold I M] in
theorem iteratedCovGrad_toSobolev_embedding_C2_of_rankBound
    (g : SmoothRiemannianMetric I M) (k : ℕ)
    (h_super : 2 * k > Module.finrank ℝ E + 4)
    (Cred : ℝ)
    (h_rank : ∀ (T : SmoothCcTensor g 0 2), ∀ j ∈ Finset.range 3,
      ‖SmoothCcTensor.toHs (g := g) (r := 0) (s := 2 + j) (2 * k)
        (iteratedCovGrad g 0 2 j T)‖ ≤
        Cred * ‖SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) (2 * k) T‖) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (T : SmoothCcTensor g 0 2) (x : M),
        (∑ j ∈ Finset.range 3,
            (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
              Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g 0 (2 + j)
            ‖(iteratedCovGrad g 0 2 j T).toSection x‖)) ≤
          C * ((2 + 1 : ℝ) * Cred) *
            ‖SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) (2 * k) T‖ := by
  have h_super' : 2 * k > Module.finrank ℝ E + 2 * 2 := by omega
  exact iteratedCovGrad_toSobolev_embedding_Cm_of_rankBound (I := I) (M := M)
    g 0 2 k 2 h_super' Cred h_rank

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.iteratedCovGrad_toSobolev_embedding_C2_of_rankBound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.iteratedCovGrad_toSobolev_embedding_C2_of_rankBound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.iteratedCovGrad_toSobolev_embedding_C2_of_rankBound ``Submission.DifferentialGeometry.Analysis.Sobolev.iteratedCovGrad_toSobolev_embedding_C2_of_rankBound

end DifferentialGeometry.Analysis.Sobolev

end
