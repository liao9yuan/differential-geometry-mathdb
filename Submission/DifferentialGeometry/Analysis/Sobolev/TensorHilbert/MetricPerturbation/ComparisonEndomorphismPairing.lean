import Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricPerturbation.InverseCometricMultiplier

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization
noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators

namespace DifferentialGeometry.Analysis.Sobolev.TensorHilbert

open _root_.Submission.DifferentialGeometry.Analysis.Laplacian

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.TensorHilbert.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M] in
theorem metricComparisonDifferenceEndomorphism_inner_le_sqrt_mul
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + h y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ) (hδ : metricCauchySchwarzBound (I := I) g₀ h δ)
    (x : M) (v w : TangentSpace I x) :
    |g₀.inner x (metricComparisonDifferenceEndomorphism (I := I) g₀ g₁ x v) w|
      ≤ (δ / (1 - δ)) * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) := by
  set Dv : TangentSpace I x := metricComparisonDifferenceEndomorphism (I := I) g₀ g₁ x v with hDv
  have hcs : |g₀.inner x Dv w|
      ≤ Real.sqrt (g₀.inner x Dv Dv) * Real.sqrt (g₀.inner x w w) :=
    abs_metric_inner_le_sqrt_metric_quadratic (I := I) (M := M) g₀ x Dv w
  have hsqrt : Real.sqrt (g₀.inner x Dv Dv)
      ≤ (δ / (1 - δ)) * Real.sqrt (g₀.inner x v v) := by
    rw [hDv]
    exact sqrt_inner_metricComparisonDifferenceEndomorphism_le (I := I) g₀ g₁ h htie hδ_lt hδ_nn hδ x v
  have hw_nn : 0 ≤ Real.sqrt (g₀.inner x w w) := Real.sqrt_nonneg _
  calc |g₀.inner x Dv w|
      ≤ Real.sqrt (g₀.inner x Dv Dv) * Real.sqrt (g₀.inner x w w) := hcs
    _ ≤ ((δ / (1 - δ)) * Real.sqrt (g₀.inner x v v)) * Real.sqrt (g₀.inner x w w) :=
        mul_le_mul_of_nonneg_right hsqrt hw_nn
    _ = (δ / (1 - δ)) * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) := by ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.TensorHilbert.metricComparisonDifferenceEndomorphism_inner_le_sqrt_mul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.TensorHilbert.metricComparisonDifferenceEndomorphism_inner_le_sqrt_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.TensorHilbert.metricComparisonDifferenceEndomorphism_inner_le_sqrt_mul ``Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert.metricComparisonDifferenceEndomorphism_inner_le_sqrt_mul

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M] in
theorem metricComparisonDifferenceEndomorphism_inner_self_le
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + h y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ) (hδ : metricCauchySchwarzBound (I := I) g₀ h δ)
    (x : M) (v : TangentSpace I x) :
    g₀.inner x (metricComparisonDifferenceEndomorphism (I := I) g₀ g₁ x v) v
      ≤ (δ / (1 - δ)) * g₀.inner x v v := by
  have hbnd := metricComparisonDifferenceEndomorphism_inner_le_sqrt_mul (I := I) g₀ g₁ h htie hδ_lt hδ_nn hδ x v v
  have hle : g₀.inner x (metricComparisonDifferenceEndomorphism (I := I) g₀ g₁ x v) v
      ≤ (δ / (1 - δ)) * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x v v) :=
    le_trans (le_abs_self _) hbnd
  have hv_nn : 0 ≤ g₀.inner x v v := metric_inner_self_nonneg (I := I) (M := M) g₀ x v
  have hsq : Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x v v) = g₀.inner x v v := by
    rw [← Real.sqrt_mul hv_nn, Real.sqrt_mul_self hv_nn]
  calc g₀.inner x (metricComparisonDifferenceEndomorphism (I := I) g₀ g₁ x v) v
      ≤ (δ / (1 - δ)) * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x v v) := hle
    _ = (δ / (1 - δ)) * (Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x v v)) := by ring
    _ = (δ / (1 - δ)) * g₀.inner x v v := by rw [hsq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.TensorHilbert.metricComparisonDifferenceEndomorphism_inner_self_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.TensorHilbert.metricComparisonDifferenceEndomorphism_inner_self_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.TensorHilbert.metricComparisonDifferenceEndomorphism_inner_self_le ``Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert.metricComparisonDifferenceEndomorphism_inner_self_le

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M] in
theorem abs_inner_metricComparisonDifferenceEndomorphism_le
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + h y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ) (hδ : metricCauchySchwarzBound (I := I) g₀ h δ)
    (x : M) (v w : TangentSpace I x) :
    |g₀.inner x (metricComparisonDifferenceEndomorphism (I := I) g₀ g₁ x v) w|
      ≤ (δ / (1 - δ))
          * (Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w)) := by
  have hbnd := metricComparisonDifferenceEndomorphism_inner_le_sqrt_mul (I := I) g₀ g₁ h htie hδ_lt hδ_nn hδ x v w
  rw [mul_assoc] at hbnd
  exact hbnd

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.TensorHilbert.abs_inner_metricComparisonDifferenceEndomorphism_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.TensorHilbert.abs_inner_metricComparisonDifferenceEndomorphism_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.TensorHilbert.abs_inner_metricComparisonDifferenceEndomorphism_le ``Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert.abs_inner_metricComparisonDifferenceEndomorphism_le

end DifferentialGeometry.Analysis.Sobolev.TensorHilbert

end
