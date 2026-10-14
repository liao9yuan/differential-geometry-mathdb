import Submission.DifferentialGeometry.Geometry.Operator.Hessian.Trace.ChartGramRegularity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

def chartDeTurckVFComp (g g' : SmoothRiemannianMetric I M) (α : M)
    (k : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
    chartInvGramOnE (I := I) g α a b y *
      (chartChristoffel (I := I) g α a b k y -
        chartChristoffel (I := I) g' α a b k y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp ``Submission.DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp] lemma chartDeTurckVFComp_def
    (g g' : SmoothRiemannianMetric I M) (α : M)
    (k : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckVFComp (I := I) g g' α k y =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α a b y *
          (chartChristoffel (I := I) g α a b k y -
            chartChristoffel (I := I) g' α a b k y) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp_def ``Submission.DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp_def

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem chartDeTurckVFComp_self
    (g : SmoothRiemannianMetric I M) (α : M)
    (k : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckVFComp (I := I) g g α k y = 0 := by
  classical
  rw [chartDeTurckVFComp_def]
  calc
    ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α a b y *
          (chartChristoffel (I := I) g α a b k y -
            chartChristoffel (I := I) g α a b k y)
        = ∑ a : Fin (Module.finrank ℝ E), ∑ _b : Fin (Module.finrank ℝ E),
            (0 : ℝ) := by
          refine Finset.sum_congr rfl (fun a _ => ?_)
          refine Finset.sum_congr rfl (fun b _ => ?_)
          rw [sub_self, _root_.MulZeroClass.mul_zero]
    _ = 0 := by simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp_self ``Submission.DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp_self

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartDeTurckVFComp_contDiffOn_interior
    (g g' : SmoothRiemannianMetric I M) (α : M)
    (k : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (chartDeTurckVFComp (I := I) g g' α k)
      (interior (extChartAt I α).target) := by
  classical
  have hrewrite : chartDeTurckVFComp (I := I) g g' α k =
      fun y : E =>
        ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α a b y *
            (chartChristoffel (I := I) g α a b k y -
              chartChristoffel (I := I) g' α a b k y) := by
    funext y
    rw [chartDeTurckVFComp_def]
  rw [hrewrite]
  refine ContDiffOn.sum (fun a _ => ?_)
  refine ContDiffOn.sum (fun b _ => ?_)
  refine ContDiffOn.mul ?_ ?_
  · exact (chartInvGramOnE_contDiffOn (I := I) g α a b).mono interior_subset
  · have hg : ContDiffOn ℝ ∞ (chartChristoffel (I := I) g α a b k)
        (interior (extChartAt I α).target) :=
      chartChristoffel_contDiffOn_interior (I := I) g α a b k
    have hg' : ContDiffOn ℝ ∞ (chartChristoffel (I := I) g' α a b k)
        (interior (extChartAt I α).target) :=
      chartChristoffel_contDiffOn_interior (I := I) g' α a b k
    exact hg.sub hg'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp_contDiffOn_interior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp_contDiffOn_interior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp_contDiffOn_interior ``Submission.DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp_contDiffOn_interior

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartDeTurckVFComp_differentiableOn_interior
    (g g' : SmoothRiemannianMetric I M) (α : M)
    (k : Fin (Module.finrank ℝ E)) :
    DifferentiableOn ℝ (chartDeTurckVFComp (I := I) g g' α k)
      (interior (extChartAt I α).target) :=
  (chartDeTurckVFComp_contDiffOn_interior (I := I) g g' α k).differentiableOn
    (by simp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp_differentiableOn_interior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp_differentiableOn_interior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp_differentiableOn_interior ``Submission.DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp_differentiableOn_interior

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartDeTurckVFComp_differentiableAt_interior
    (g g' : SmoothRiemannianMetric I M) (α : M)
    (k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    DifferentiableAt ℝ (chartDeTurckVFComp (I := I) g g' α k) y := by
  have hcd : ContDiffOn ℝ ∞ (chartDeTurckVFComp (I := I) g g' α k)
      (interior (extChartAt I α).target) :=
    chartDeTurckVFComp_contDiffOn_interior (I := I) g g' α k
  exact (hcd.differentiableOn (by simp)).differentiableAt
    (isOpen_interior.mem_nhds hy)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp_differentiableAt_interior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp_differentiableAt_interior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp_differentiableAt_interior ``Submission.DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp_differentiableAt_interior

end DeTurckLinearization
end DeTurck
end PDE
end DifferentialGeometry
