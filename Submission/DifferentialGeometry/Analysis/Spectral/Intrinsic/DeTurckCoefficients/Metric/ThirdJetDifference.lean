import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.Christoffel.Perturbation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Operator

noncomputable section

namespace DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients

open scoped _root_.ContDiff _root_.Manifold _root_.Topology _root_.BigOperators
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

local notation "D3Idx" =>
  Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
    Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
      Fin (Module.finrank ℝ E)

def gramD3DiffSup (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) (y : E) : ℝ :=
  ∑ p : D3Idx,
    |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) p.1
        (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) p.2.1
          (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) p.2.2.1
            (chartGramOnE (I := I) g₁ α p.2.2.2.1 p.2.2.2.2))) y -
      DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) p.1
        (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) p.2.1
          (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) p.2.2.1
            (chartGramOnE (I := I) g₂ α p.2.2.2.1 p.2.2.2.2))) y|

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.gramD3DiffSup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.gramD3DiffSup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.gramD3DiffSup ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.gramD3DiffSup

omit [NeZero (Module.finrank ℝ E)] in
theorem gramD3_sub_le
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) (y : E)
    (d c m a b : Fin (Module.finrank ℝ E)) :
    |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) d
        (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) c
          (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (chartGramOnE (I := I) g₁ α a b))) y -
      DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) d
        (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) c
          (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (chartGramOnE (I := I) g₂ α a b))) y| ≤
      gramD3DiffSup (I := I) (M := M) g₁ g₂ α y := by
  classical
  let p : D3Idx := (d, (c, (m, (a, b))))
  have h := Finset.single_le_sum
    (f := fun q : D3Idx =>
      |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) q.1
          (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) q.2.1
            (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) q.2.2.1
              (chartGramOnE (I := I) g₁ α q.2.2.2.1 q.2.2.2.2))) y -
        DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) q.1
          (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) q.2.1
            (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) q.2.2.1
              (chartGramOnE (I := I) g₂ α q.2.2.2.1 q.2.2.2.2))) y|)
    (fun q _ => abs_nonneg _) (Finset.mem_univ p)
  simpa only [gramD3DiffSup, p] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.gramD3_sub_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.gramD3_sub_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.gramD3_sub_le ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.gramD3_sub_le

omit [NeZero (Module.finrank ℝ E)] in
theorem gramD3DiffSup_nonneg
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) (y : E) :
    0 ≤ gramD3DiffSup (I := I) (M := M) g₁ g₂ α y := by
  exact Finset.sum_nonneg fun _ _ => abs_nonneg _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.gramD3DiffSup_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.gramD3DiffSup_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.gramD3DiffSup_nonneg ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.gramD3DiffSup_nonneg

def metricJet3DiffSup (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) (y : E) : ℝ :=
  chartMetricJet2DiffSup (I := I) (M := M) g₁ g₂ α y +
    gramD3DiffSup (I := I) (M := M) g₁ g₂ α y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.metricJet3DiffSup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.metricJet3DiffSup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.metricJet3DiffSup ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.metricJet3DiffSup

omit [NeZero (Module.finrank ℝ E)] in
theorem metricJet3_nonneg
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) (y : E) :
    0 ≤ metricJet3DiffSup (I := I) (M := M) g₁ g₂ α y :=
  add_nonneg (chartMetricJet2DiffSup_nonneg _ _ _ _)
    (gramD3DiffSup_nonneg (I := I) (M := M) g₁ g₂ α y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.metricJet3_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.metricJet3_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.metricJet3_nonneg ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.metricJet3_nonneg

omit [NeZero (Module.finrank ℝ E)] in
theorem metricJet2_le_jet3
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) (y : E) :
    chartMetricJet2DiffSup (I := I) (M := M) g₁ g₂ α y ≤
      metricJet3DiffSup (I := I) (M := M) g₁ g₂ α y :=
  le_add_of_nonneg_right (gramD3DiffSup_nonneg (I := I) (M := M) g₁ g₂ α y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.metricJet2_le_jet3 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.metricJet2_le_jet3"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.metricJet2_le_jet3 ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.metricJet2_le_jet3

omit [NeZero (Module.finrank ℝ E)] in
theorem gramD3_le_jet3
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) (y : E) :
    gramD3DiffSup (I := I) (M := M) g₁ g₂ α y ≤
      metricJet3DiffSup (I := I) (M := M) g₁ g₂ α y :=
  le_add_of_nonneg_left (chartMetricJet2DiffSup_nonneg _ _ _ _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.gramD3_le_jet3 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.gramD3_le_jet3"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.gramD3_le_jet3 ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.gramD3_le_jet3

end DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients
