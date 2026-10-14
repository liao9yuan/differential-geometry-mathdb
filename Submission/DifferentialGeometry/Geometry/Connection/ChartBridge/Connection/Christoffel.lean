import Submission.DifferentialGeometry.Geometry.Operator.Laplacian.VossWeylFormula

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set
open scoped _root_.BigOperators _root_.ContDiff _root_.Manifold _root_.Topology

namespace DifferentialGeometry.Geometry.Operator

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def chartChristoffel (g : SmoothRiemannianMetric I M) (α : M)
    (i j k : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
    chartInvGramMatrix (I := I) g α ((extChartAt I α).symm y) k l *
      (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y +
       DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) y -
       DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.chartChristoffel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.chartChristoffel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.chartChristoffel ``Submission.DifferentialGeometry.Geometry.Operator.chartChristoffel

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma chartChristoffel_def
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j k : Fin (Module.finrank ℝ E)) (y : E) :
    chartChristoffel (I := I) g α i j k y =
      (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g α ((extChartAt I α).symm y) k l *
          (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y +
           DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) y -
           DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) y) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.chartChristoffel_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.chartChristoffel_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.chartChristoffel_def ``Submission.DifferentialGeometry.Geometry.Operator.chartChristoffel_def

omit [NeZero (Module.finrank ℝ E)] in
theorem chartChristoffel_symm
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j k : Fin (Module.finrank ℝ E)) (y : E) :
    chartChristoffel (I := I) g α i j k y =
      chartChristoffel (I := I) g α j i k y := by
  classical
  rw [chartChristoffel_def, chartChristoffel_def]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro l _
  congr 1
  have hsym : chartGramOnE (I := I) g α i j =
      chartGramOnE (I := I) g α j i :=
    funext (fun y' => chartGramOnE_symm (I := I) g α i j y')
  rw [show DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) y =
        DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) l (chartGramOnE (I := I) g α j i) y from by
    rw [hsym]]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.chartChristoffel_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.chartChristoffel_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.chartChristoffel_symm ``Submission.DifferentialGeometry.Geometry.Operator.chartChristoffel_symm

end DifferentialGeometry.Geometry.Operator

namespace DifferentialGeometry.Geometry.Connection

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def chartChristoffelBracket (g : SmoothRiemannianMetric I M) (α : M)
    (i j l : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y +
    DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) y -
    DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.chartChristoffelBracket then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.chartChristoffelBracket"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.chartChristoffelBracket ``Submission.DifferentialGeometry.Geometry.Connection.chartChristoffelBracket

def chartChristoffelBracketDeriv (g : SmoothRiemannianMetric I M) (α : M)
    (m i j l : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (chartGramOnE (I := I) g α l j)) y +
    DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j (chartGramOnE (I := I) g α l i)) y -
    DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) l (chartGramOnE (I := I) g α i j)) y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.chartChristoffelBracketDeriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.chartChristoffelBracketDeriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.chartChristoffelBracketDeriv ``Submission.DifferentialGeometry.Geometry.Connection.chartChristoffelBracketDeriv

def chartChristoffelBracketSecondDeriv (g : SmoothRiemannianMetric I M) (α : M)
    (d m i j l : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) d
      (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m
        (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (chartGramOnE (I := I) g α l j))) y +
    DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) d
      (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m
        (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j (chartGramOnE (I := I) g α l i))) y -
    DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) d
      (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m
        (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) l (chartGramOnE (I := I) g α i j))) y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.chartChristoffelBracketSecondDeriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.chartChristoffelBracketSecondDeriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.chartChristoffelBracketSecondDeriv ``Submission.DifferentialGeometry.Geometry.Connection.chartChristoffelBracketSecondDeriv

omit [NeZero (Module.finrank ℝ E)] in
lemma chartChristoffel_eq_sum_invGramOnE_chartChristoffelBracket
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j k : Fin (Module.finrank ℝ E)) (y : E) :
    chartChristoffel (I := I) g α i j k y =
      (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α k l y *
          chartChristoffelBracket (I := I) g α i j l y := by
  rw [chartChristoffel_def]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.chartChristoffel_eq_sum_invGramOnE_chartChristoffelBracket then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.chartChristoffel_eq_sum_invGramOnE_chartChristoffelBracket"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.chartChristoffel_eq_sum_invGramOnE_chartChristoffelBracket ``Submission.DifferentialGeometry.Geometry.Connection.chartChristoffel_eq_sum_invGramOnE_chartChristoffelBracket

end DifferentialGeometry.Geometry.Connection
