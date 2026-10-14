import Submission.DifferentialGeometry.Geometry.Metric.DeTurck.Coordinates.Components
import Submission.DifferentialGeometry.Analysis.Parabolic.RicciLinearization.Variation.Christoffel

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Operator


noncomputable section

open _root_.Set _root_.Function
open scoped _root_.Topology _root_.ContDiff _root_.Matrix _root_.Manifold

namespace DifferentialGeometry
namespace PDE
namespace DeTurck
namespace DeTurckLinearization

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]


def chartLinearizedDeTurckVFPrincipal (g : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (k : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
    chartInvGramOnE (I := I) g α a b y *
      chartLinearizedChristoffelPrincipal (I := I) g α h a b k y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.chartLinearizedDeTurckVFPrincipal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.chartLinearizedDeTurckVFPrincipal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.chartLinearizedDeTurckVFPrincipal ``Submission.DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.chartLinearizedDeTurckVFPrincipal

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp] lemma chartLinearizedDeTurckVFPrincipal_def
    (g : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (k : Fin (Module.finrank ℝ E)) (y : E) :
    chartLinearizedDeTurckVFPrincipal (I := I) g α h k y =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α a b y *
          chartLinearizedChristoffelPrincipal (I := I) g α h a b k y := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.chartLinearizedDeTurckVFPrincipal_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.chartLinearizedDeTurckVFPrincipal_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.chartLinearizedDeTurckVFPrincipal_def ``Submission.DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.chartLinearizedDeTurckVFPrincipal_def

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem chartLinearizedDeTurckVFPrincipal_zero
    (g : SmoothRiemannianMetric I M) (α : M)
    (k : Fin (Module.finrank ℝ E)) (y : E) :
    chartLinearizedDeTurckVFPrincipal (I := I) g α
      (0 : ChartMetricPerturbation E) k y = 0 := by
  classical
  rw [chartLinearizedDeTurckVFPrincipal_def]
  calc
    ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α a b y *
          chartLinearizedChristoffelPrincipal (I := I) g α
            (0 : ChartMetricPerturbation E) a b k y
        = ∑ _a : Fin (Module.finrank ℝ E), ∑ _b : Fin (Module.finrank ℝ E),
            (0 : ℝ) := by
          refine Finset.sum_congr rfl (fun a _ => ?_)
          refine Finset.sum_congr rfl (fun b _ => ?_)
          rw [chartLinearizedChristoffelPrincipal_zero, _root_.MulZeroClass.mul_zero]
    _ = 0 := by simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.chartLinearizedDeTurckVFPrincipal_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.chartLinearizedDeTurckVFPrincipal_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.chartLinearizedDeTurckVFPrincipal_zero ``Submission.DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.chartLinearizedDeTurckVFPrincipal_zero

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem chartLinearizedDeTurckVFPrincipal_add
    (g : SmoothRiemannianMetric I M) (α : M)
    (h₁ h₂ : ChartMetricPerturbation E) (k : Fin (Module.finrank ℝ E)) (y : E) :
    chartLinearizedDeTurckVFPrincipal (I := I) g α (h₁ + h₂) k y =
      chartLinearizedDeTurckVFPrincipal (I := I) g α h₁ k y +
        chartLinearizedDeTurckVFPrincipal (I := I) g α h₂ k y := by
  classical
  rw [chartLinearizedDeTurckVFPrincipal_def, chartLinearizedDeTurckVFPrincipal_def,
    chartLinearizedDeTurckVFPrincipal_def]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [chartLinearizedChristoffelPrincipal_add]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.chartLinearizedDeTurckVFPrincipal_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.chartLinearizedDeTurckVFPrincipal_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.chartLinearizedDeTurckVFPrincipal_add ``Submission.DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.chartLinearizedDeTurckVFPrincipal_add

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem chartLinearizedDeTurckVFPrincipal_smul
    (g : SmoothRiemannianMetric I M) (α : M) (c : ℝ)
    (h : ChartMetricPerturbation E) (k : Fin (Module.finrank ℝ E)) (y : E) :
    chartLinearizedDeTurckVFPrincipal (I := I) g α (c • h) k y =
      c • chartLinearizedDeTurckVFPrincipal (I := I) g α h k y := by
  classical
  rw [chartLinearizedDeTurckVFPrincipal_def, chartLinearizedDeTurckVFPrincipal_def,
    smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [chartLinearizedChristoffelPrincipal_smul, smul_eq_mul]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.chartLinearizedDeTurckVFPrincipal_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.chartLinearizedDeTurckVFPrincipal_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.chartLinearizedDeTurckVFPrincipal_smul ``Submission.DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.chartLinearizedDeTurckVFPrincipal_smul

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartLinearizedDeTurckVFPrincipal_contDiffOn_interior
    (g : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (k : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (chartLinearizedDeTurckVFPrincipal (I := I) g α h k)
      (interior (extChartAt I α).target) := by
  classical
  have hrewrite : chartLinearizedDeTurckVFPrincipal (I := I) g α h k =
      fun y : E =>
        ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α a b y *
            chartLinearizedChristoffelPrincipal (I := I) g α h a b k y := by
    funext y
    rw [chartLinearizedDeTurckVFPrincipal_def]
  rw [hrewrite]
  refine ContDiffOn.sum (fun a _ => ?_)
  refine ContDiffOn.sum (fun b _ => ?_)
  refine ContDiffOn.mul ?_ ?_
  · exact (chartInvGramOnE_contDiffOn (I := I) g α a b).mono interior_subset
  · exact (chartLinearizedChristoffelPrincipal_contDiffOn (I := I) g α h a b k).mono
      interior_subset

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.chartLinearizedDeTurckVFPrincipal_contDiffOn_interior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.chartLinearizedDeTurckVFPrincipal_contDiffOn_interior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.chartLinearizedDeTurckVFPrincipal_contDiffOn_interior ``Submission.DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.chartLinearizedDeTurckVFPrincipal_contDiffOn_interior

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartLinearizedDeTurckVFPrincipal_differentiableOn_interior
    (g : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (k : Fin (Module.finrank ℝ E)) :
    DifferentiableOn ℝ (chartLinearizedDeTurckVFPrincipal (I := I) g α h k)
      (interior (extChartAt I α).target) :=
  (chartLinearizedDeTurckVFPrincipal_contDiffOn_interior (I := I) g α h k).differentiableOn
    (by simp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.chartLinearizedDeTurckVFPrincipal_differentiableOn_interior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.chartLinearizedDeTurckVFPrincipal_differentiableOn_interior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.chartLinearizedDeTurckVFPrincipal_differentiableOn_interior ``Submission.DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.chartLinearizedDeTurckVFPrincipal_differentiableOn_interior

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartLinearizedDeTurckVFPrincipal_differentiableAt_interior
    (g : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    DifferentiableAt ℝ (chartLinearizedDeTurckVFPrincipal (I := I) g α h k) y := by
  have hcd : ContDiffOn ℝ ∞ (chartLinearizedDeTurckVFPrincipal (I := I) g α h k)
      (interior (extChartAt I α).target) :=
    chartLinearizedDeTurckVFPrincipal_contDiffOn_interior (I := I) g α h k
  exact (hcd.differentiableOn (by simp)).differentiableAt
    (isOpen_interior.mem_nhds hy)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.chartLinearizedDeTurckVFPrincipal_differentiableAt_interior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.chartLinearizedDeTurckVFPrincipal_differentiableAt_interior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.chartLinearizedDeTurckVFPrincipal_differentiableAt_interior ``Submission.DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.chartLinearizedDeTurckVFPrincipal_differentiableAt_interior

end DeTurckLinearization
end DeTurck
end PDE
end DifferentialGeometry
