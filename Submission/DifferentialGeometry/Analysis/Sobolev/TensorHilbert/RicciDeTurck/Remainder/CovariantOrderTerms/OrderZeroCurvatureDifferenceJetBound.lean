import Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RicciDeTurck.Remainder.Coefficient.PerOrderEnvelopes
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Iterated.Linear
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurck.SectionDifference.ConnectionBicontraction
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Product.JetIntegral
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTower.Envelope

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Analysis.Spectral

noncomputable section

open _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Filter _root_.Topology _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.DifferentialGeometry.Tensor0SBundle
    ContinuousLinearMap
open scoped _root_.ENNReal _root_.NNReal _root_.BigOperators _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Analysis.Sobolev

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow _root_.Submission.DifferentialGeometry.Analysis.Sobolev
    DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (ricciOrderZeroRiemannCoeff ricciOrderZeroCurvCoeff)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

private theorem sq_le_two_add (t u v c1 c2 : ℝ) (ht : 0 ≤ t) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (htri : t ≤ u + v) (h1 : u ^ 2 ≤ c1) (h2 : v ^ 2 ≤ c2) : t ^ 2 ≤ 2 * (c1 + c2) := by
  have huv : 0 ≤ u + v := by linarith
  nlinarith [mul_le_mul htri htri ht huv, sq_nonneg (u - v), h1, h2, hu, hv]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.sq_le_two_add
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.sq_le_two_add target :: scope.openDecls } }

private theorem ricciOrderZeroRiemannCoeff_backgroundDifference_perOrder_l2_ballUniform_g1
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₁
              - ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 ≤ K i :=
  ricciOrderZeroRiemannCoeff_backgroundDifference_perOrder_l2_ballUniform
    (I := I) (M := M) g₀ a ha_super hR hδ₀

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.ricciOrderZeroRiemannCoeff_backgroundDifference_perOrder_l2_ballUniform_g1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.ricciOrderZeroRiemannCoeff_backgroundDifference_perOrder_l2_ballUniform_g1 target :: scope.openDecls } }

private theorem ricciOrderZeroCurvCoeff_backgroundDifference_perOrder_l2_ballUniform_g1
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (ricciOrderZeroCurvCoeff (I := I) (M := M) g₀ g₁
              - ricciOrderZeroCurvCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 ≤ K i :=
  ricciOrderZeroCurvCoeff_backgroundDifference_perOrder_l2_ballUniform
    (I := I) (M := M) g₀ a ha_super hR hδ₀

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.ricciOrderZeroCurvCoeff_backgroundDifference_perOrder_l2_ballUniform_g1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.ricciOrderZeroCurvCoeff_backgroundDifference_perOrder_l2_ballUniform_g1 target :: scope.openDecls } }

private theorem ricciOrderZeroRiemannCoeff_perOrder_l2_ballUniform_g1
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤ K i := by
  obtain ⟨KD, hKD_nn, hKD⟩ :=
    ricciOrderZeroRiemannCoeff_backgroundDifference_perOrder_l2_ballUniform_g1
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  refine ⟨fun i => 2 * (‖iteratedCovGrad (I := I) g₀ 2 2 i
      (ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 + KD i),
    fun i => by
      linarith [hKD_nn i, sq_nonneg ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₀)‖], ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball i hi
  have hD := hKD g₁ P hδ_le hδ htie hPball i hi
  have hsplit : ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₁ =
      ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₀ +
        (ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₁
          - ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₀) := by
    abel
  rw [hsplit, iteratedCovGrad_add (I := I) g₀ 2 2 i
    (ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₀)
    (ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₁
      - ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₀)]
  exact sq_le_two_add
    ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₀)
      + iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₁
          - ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₀)‖
    ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₀)‖
    ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₁
          - ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₀)‖
    (‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2)
    (KD i)
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (norm_add_le _ _) le_rfl hD

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.ricciOrderZeroRiemannCoeff_perOrder_l2_ballUniform_g1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.ricciOrderZeroRiemannCoeff_perOrder_l2_ballUniform_g1 target :: scope.openDecls } }

private theorem ricciOrderZeroCurvCoeff_perOrder_l2_ballUniform_g1
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (ricciOrderZeroCurvCoeff (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤ K i := by
  obtain ⟨KD, hKD_nn, hKD⟩ :=
    ricciOrderZeroCurvCoeff_backgroundDifference_perOrder_l2_ballUniform_g1
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  refine ⟨fun i => 2 * (‖iteratedCovGrad (I := I) g₀ 2 2 i
      (ricciOrderZeroCurvCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 + KD i),
    fun i => by
      linarith [hKD_nn i, sq_nonneg ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciOrderZeroCurvCoeff (I := I) (M := M) g₀ g₀)‖], ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball i hi
  have hD := hKD g₁ P hδ_le hδ htie hPball i hi
  have hsplit : ricciOrderZeroCurvCoeff (I := I) (M := M) g₀ g₁ =
      ricciOrderZeroCurvCoeff (I := I) (M := M) g₀ g₀ +
        (ricciOrderZeroCurvCoeff (I := I) (M := M) g₀ g₁
          - ricciOrderZeroCurvCoeff (I := I) (M := M) g₀ g₀) := by
    abel
  rw [hsplit, iteratedCovGrad_add (I := I) g₀ 2 2 i
    (ricciOrderZeroCurvCoeff (I := I) (M := M) g₀ g₀)
    (ricciOrderZeroCurvCoeff (I := I) (M := M) g₀ g₁
      - ricciOrderZeroCurvCoeff (I := I) (M := M) g₀ g₀)]
  exact sq_le_two_add
    ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciOrderZeroCurvCoeff (I := I) (M := M) g₀ g₀)
      + iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciOrderZeroCurvCoeff (I := I) (M := M) g₀ g₁
          - ricciOrderZeroCurvCoeff (I := I) (M := M) g₀ g₀)‖
    ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciOrderZeroCurvCoeff (I := I) (M := M) g₀ g₀)‖
    ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciOrderZeroCurvCoeff (I := I) (M := M) g₀ g₁
          - ricciOrderZeroCurvCoeff (I := I) (M := M) g₀ g₀)‖
    (‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciOrderZeroCurvCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2)
    (KD i)
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (norm_add_le _ _) le_rfl hD

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.ricciOrderZeroCurvCoeff_perOrder_l2_ballUniform_g1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.ricciOrderZeroCurvCoeff_perOrder_l2_ballUniform_g1 target :: scope.openDecls } }

theorem ricciOrderZeroBaseCoeff_perOrder_l2_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₁
              - ricciOrderZeroCurvCoeff (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤ K i := by
  obtain ⟨KR, hKR_nn, hKR⟩ :=
    ricciOrderZeroRiemannCoeff_perOrder_l2_ballUniform_g1
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨KC, hKC_nn, hKC⟩ :=
    ricciOrderZeroCurvCoeff_perOrder_l2_ballUniform_g1
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  refine ⟨fun i => 2 * (KR i + KC i), fun i => by linarith [hKR_nn i, hKC_nn i], ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball i hi
  have hR2 := hKR g₁ P hδ_le hδ htie hPball i hi
  have hC2 := hKC g₁ P hδ_le hδ htie hPball i hi
  rw [iteratedCovGrad_sub (I := I) g₀ 2 2 i
    (ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₁)
    (ricciOrderZeroCurvCoeff (I := I) (M := M) g₀ g₁)]
  exact sq_le_two_add
    ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₁)
      - iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciOrderZeroCurvCoeff (I := I) (M := M) g₀ g₁)‖
    ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₁)‖
    ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciOrderZeroCurvCoeff (I := I) (M := M) g₀ g₁)‖
    (KR i) (KC i)
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (norm_sub_le _ _) hR2 hC2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.ricciOrderZeroBaseCoeff_perOrder_l2_ballUniform then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.ricciOrderZeroBaseCoeff_perOrder_l2_ballUniform"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.ricciOrderZeroBaseCoeff_perOrder_l2_ballUniform ``Submission.DifferentialGeometry.Analysis.Sobolev.ricciOrderZeroBaseCoeff_perOrder_l2_ballUniform

end DifferentialGeometry.Analysis.Sobolev

end
