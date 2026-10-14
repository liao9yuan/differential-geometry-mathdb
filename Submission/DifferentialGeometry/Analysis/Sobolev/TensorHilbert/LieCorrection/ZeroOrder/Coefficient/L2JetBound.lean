import Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLie.Coefficient.L2JetBound
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.LieCorrection.Zero.Splitting

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

noncomputable section
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

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
  (deTurckLieEndoTermField deTurckLieEndoTermField_toSection deTurckLieCovariantDerivativeInsertionFib)
open _root_.Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization (metricPerturbationPath)

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

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
private theorem deTurckLieEndomorphismTerm_eq_covariantDerivativeInsertion (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    deTurckLieEndoTermField (I := I) (M := M) g₀ g₁ g_bg =
      deTurckLieCovariantDerivativeInsertionField (I := I) (M := M) g₀ g₁ g_bg := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [deTurckLieEndoTermField_toSection, deTurckLieCovariantDerivativeInsertionField_toSection]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.deTurckLieEndomorphismTerm_eq_covariantDerivativeInsertion
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.deTurckLieEndomorphismTerm_eq_covariantDerivativeInsertion target :: scope.openDecls } }

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private theorem lieCorrectionZeroInsertion_base_eq_neg_covariantDerivativeInsertion (g₀ g₁ : SmoothRiemannianMetric I M) :
    lieCorrectionZeroInsertion (I := I) (M := M) g₀ g₁ g₀ =
      -deTurckLieCovariantDerivativeInsertionField (I := I) (M := M) g₀ g₁ g₀ := by
  have h := insert_base (I := I) (M := M) g₀ g₁ g₀
  rw [sub_self] at h
  rw [eq_neg_of_add_eq_zero_left h, deTurckLieEndomorphismTerm_eq_covariantDerivativeInsertion]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.lieCorrectionZeroInsertion_base_eq_neg_covariantDerivativeInsertion
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.lieCorrectionZeroInsertion_base_eq_neg_covariantDerivativeInsertion target :: scope.openDecls } }

private theorem lieCorrectionZeroInsertionBase_metricPerturbationPath_perOrder_topOrderSeparated
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (_hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
        ∀ (i : ℕ), i ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (lieCorrectionZeroInsertion (I := I) (M := M) g₀
                (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g₀)‖ ^ 2 ≤
            Ktop * (‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T‖ ^ 2 +
              ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T'‖ ^ 2) +
            Kc i * (1 + ∑ j ∈ Finset.range (i + 3),
              (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) := by
  obtain ⟨Ktop, hnn, Kc, hKcnn, h⟩ :=
    deTurckLieCovariantDerivativeInsertionField_metricPerturbationPath_jetL2_perOrder_topOrderSeparated (I := I) (M := M) g₀ g₀ a
      ha_super hR hδ₀
  refine ⟨Ktop, hnn, Kc, hKcnn, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball s hs i hi
  have hb := h T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs i hi
  rw [lieCorrectionZeroInsertion_base_eq_neg_covariantDerivativeInsertion, iteratedCovGrad_neg, norm_neg]
  exact hb

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.lieCorrectionZeroInsertionBase_metricPerturbationPath_perOrder_topOrderSeparated
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.lieCorrectionZeroInsertionBase_metricPerturbationPath_perOrder_topOrderSeparated target :: scope.openDecls } }

end DifferentialGeometry.Analysis.Sobolev

end
