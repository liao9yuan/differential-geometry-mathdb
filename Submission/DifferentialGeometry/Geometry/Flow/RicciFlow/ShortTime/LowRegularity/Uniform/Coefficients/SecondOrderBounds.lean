import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.Grid.SecondOrderBounds
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTower.Lowered
import Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert.LieCorrection.ZeroOrder.MixedConnectionExpansion
import Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert.LieCorrection.ZeroOrder.TraceRadiusFreeBounds

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Integral.Connection
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.CurvatureCoefficientDifferenceJetTower
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

theorem trace_h2_uniform
    (p : ℕ) (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ g₀ : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g₀ Λ →
        MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ →
        MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g₀ gBase Λ →
        ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2),
          (∀ (y : M) (v w : TangentSpace I y),
            g₁.inner y v w = g₀.inner y v w +
              ccTensorBilinSymm (I := I) g₀ P y v w) →
          ∀ {δ : ℝ}, δ ≤ δ₀ → 0 ≤ δ →
          gFibreOpBound (I := I) (M := M) g₀
              (ccTensorBilinSymm (I := I) g₀ P) δ →
          ∀ (σ : Equiv.Perm (Fin (p + 2))) (R : ℝ), 0 ≤ R →
          (∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ R ^ 2 →
          (∑ i ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g₀ (p + 2) p i
              (reindexedPureTrace (I := I) (M := M) g₀ g₁ p σ)‖ ^ 2) ≤
            (B R) ^ 2 := by
  classical
  obtain ⟨C, hC, hpt⟩ := trace_grid_uniform (I := I) (M := M) p hδ₀
  obtain ⟨B, hB_nn, hB⟩ := h2_low_uniform
    (I := I) (M := M) hDim gBase hΛ (r := p + 2) (s := p) C hC
  refine ⟨B, hB_nn, ?_⟩
  intro g₀ hEq hjet1 hjet2 g₁ P htie δ hδ_le hδ_nonneg hbound σ R hR hP
  refine hB g₀ hEq hjet1 hjet2 P
    (reindexedPureTrace (I := I) (M := M) g₀ g₁ p σ) R hR hP ?_
  intro i hi x
  simpa only [lowJetGrid, Combinatorics.antidiagonalTupleGrid] using
    hpt g₀ g₁ P htie hδ_le hδ_nonneg hbound σ i x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.trace_h2_uniform then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.trace_h2_uniform"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.trace_h2_uniform ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.trace_h2_uniform

theorem trace2_h2_uniform
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ g₀ : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g₀ Λ →
        MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ →
        MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g₀ gBase Λ →
        ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2),
          (∀ (y : M) (v w : TangentSpace I y),
            g₁.inner y v w = g₀.inner y v w +
              ccTensorBilinSymm (I := I) g₀ P y v w) →
          ∀ {δ : ℝ}, δ ≤ δ₀ → 0 ≤ δ →
          gFibreOpBound (I := I) (M := M) g₀
              (ccTensorBilinSymm (I := I) g₀ P) δ →
          ∀ (σ : Equiv.Perm (Fin 4)) (R : ℝ), 0 ≤ R →
          (∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ R ^ 2 →
          (∑ i ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g₀ 4 2 i
              (reindexedPureTrace (I := I) (M := M) g₀ g₁ 2 σ)‖ ^ 2) ≤
            (B R) ^ 2 := by
  simpa only [Nat.reduceAdd] using
    trace_h2_uniform (I := I) (M := M) 2 hDim gBase hΛ hδ₀

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.trace2_h2_uniform then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.trace2_h2_uniform"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.trace2_h2_uniform ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.trace2_h2_uniform

theorem sharp_h2_uniform
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ g₀ : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g₀ Λ →
        MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ →
        MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g₀ gBase Λ →
        ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2),
          (∀ (y : M) (v w : TangentSpace I y),
            g₁.inner y v w = g₀.inner y v w +
              ccTensorBilinSymm (I := I) g₀ P y v w) →
          ∀ {δ : ℝ}, δ ≤ δ₀ → 0 ≤ δ →
          gFibreOpBound (I := I) (M := M) g₀
              (ccTensorBilinSymm (I := I) g₀ P) δ →
          ∀ (R : ℝ), 0 ≤ R →
          (∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ R ^ 2 →
          (∑ i ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g₀ 1 1 i
              (sharpFlatEndoCc (I := I) g₀ g₁)‖ ^ 2) ≤
            (B R) ^ 2 := by
  classical
  obtain ⟨C, hC, hpt⟩ := sharpFlat_grid_uniform (I := I) (M := M) hδ₀
  obtain ⟨B, hB_nn, hB⟩ := h2_low_uniform
    (I := I) (M := M) hDim gBase hΛ (r := 1) (s := 1) C hC
  refine ⟨B, hB_nn, ?_⟩
  intro g₀ hEq hjet1 hjet2 g₁ P htie δ hδ_le hδ_nonneg hbound R hR hP
  refine hB g₀ hEq hjet1 hjet2 P (sharpFlatEndoCc (I := I) g₀ g₁)
    R hR hP ?_
  intro i hi x
  have hraw :
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
          ((iteratedCovGrad (I := I) g₀ 1 1 i
            (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x) ≤
        C i * lowJetGrid (I := I) (M := M) g₀ P i x := by
    simpa only [lowJetGrid, Combinatorics.antidiagonalTupleGrid] using
      hpt g₀ g₁ P htie hδ_le hδ_nonneg hbound i x
  have hgrid_nn : ∀ k : ℕ,
      0 ≤ lowJetGrid (I := I) (M := M) g₀ P k x := by
    intro k
    unfold lowJetGrid
    exact Finset.sum_nonneg fun n _ => Finset.sum_nonneg fun e _ =>
      Finset.prod_nonneg fun m _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀
          0 (2 + e m) x _
  have himem : i ∈ Finset.range (i + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_self i)
  have hsingle : lowJetGrid (I := I) (M := M) g₀ P i x ≤
      ∑ k ∈ Finset.range (i + 1),
        lowJetGrid (I := I) (M := M) g₀ P k x :=
    Finset.single_le_sum (fun k _ => hgrid_nn k) himem
  exact hraw.trans (mul_le_mul_of_nonneg_left hsingle (hC i))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.sharp_h2_uniform then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.sharp_h2_uniform"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.sharp_h2_uniform ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.sharp_h2_uniform

theorem connLow_tame_uniform
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ B0 B1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ g₀ : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g₀ Λ →
        MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ →
        MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g₀ gBase Λ →
        ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2),
          (∀ (y : M) (v w : TangentSpace I y),
            g₁.inner y v w = g₀.inner y v w +
              ccTensorBilinSymm (I := I) g₀ P y v w) →
          ∀ {δ : ℝ}, δ ≤ δ₀ → 0 ≤ δ →
          gFibreOpBound (I := I) (M := M) g₀
              (ccTensorBilinSymm (I := I) g₀ P) δ →
          ∀ (R A : ℝ), 0 ≤ R → 0 ≤ A →
          (∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ R ^ 2 →
          (∑ j ∈ Finset.range 4,
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ A ^ 2 →
          (∑ i ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g₀ 0 3 i
              (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁)‖ ^ 2) ≤
            (B0 R + B1 R * A) ^ 2 := by
  classical
  obtain ⟨C, hC, hpt⟩ := connectionDifference_grid_uniform (I := I) (M := M) hδ₀
  obtain ⟨B0, B1, hB0, hB1, hB⟩ := h2_tame_uniform
    (I := I) (M := M) hDim gBase hΛ (r := 0) (s := 3) C hC
  refine ⟨B0, B1, hB0, hB1, ?_⟩
  intro g₀ hEq hjet1 hjet2 g₁ P htie δ hδ_le hδ_nonneg hbound
    R A hR hA hP2 hP3
  have hsingle : ‖iteratedCovGrad (I := I) g₀ 0 2 3 P‖ ^ 2 ≤ A ^ 2 := by
    have hmem : 3 ∈ Finset.range 4 := by norm_num
    exact (Finset.single_le_sum
      (f := fun j : ℕ => ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)
      (fun j _ => sq_nonneg _) hmem).trans hP3
  have htop : ‖iteratedCovGrad (I := I) g₀ 0 2 3 P‖ ≤ A := by
    nlinarith [norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 3 P)]
  refine hB g₀ hEq hjet1 hjet2 P (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁)
    R A hR hA hP2 htop ?_
  intro i hi x
  rw [metricLoweredConnectionDifferenceCoefficient_fiber_norm_sq_eq (I := I) (M := M) g₀ g₁ i x]
  simpa only [lowJetGrid, Combinatorics.antidiagonalTupleGrid] using
    hpt g₀ g₁ P htie hδ_le hδ_nonneg hbound i x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.connLow_tame_uniform then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.connLow_tame_uniform"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.connLow_tame_uniform ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.connLow_tame_uniform

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
