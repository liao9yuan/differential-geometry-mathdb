import Submission.DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Green.GradientFormula
import Submission.DifferentialGeometry.Geometry.Operator.Hessian.Basic
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.Christoffel.Perturbation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Operator

set_option autoImplicit false

namespace DifferentialGeometry.Geometry.Connection

open _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Manifold _root_.ContDiff _root_.BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E] [CompleteSpace E]
variable [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem

private lemma traceChristoffelAlg
    {Idx : Type*} [Fintype Idx]
    (gInv : Idx → Idx → ℝ) (D : Idx → Idx → Idx → ℝ)
    (hsym : ∀ i j : Idx, gInv i j = gInv j i) (p : Idx) :
    (∑ a : Idx,
        (1 / 2 : ℝ) *
          ∑ l : Idx, gInv a l * (D p a l + D a p l - D l p a))
      =
    (1 / 2 : ℝ) * ∑ i : Idx, ∑ j : Idx, gInv i j * D p i j := by
  classical
  let S₁ : ℝ := ∑ a : Idx, ∑ l : Idx, gInv a l * D p a l
  let S₂ : ℝ := ∑ a : Idx, ∑ l : Idx, gInv a l * D a p l
  let S₃ : ℝ := ∑ a : Idx, ∑ l : Idx, gInv a l * D l p a
  have hS₃ : S₃ = S₂ := by
    unfold S₂ S₃
    calc
      (∑ a : Idx, ∑ l : Idx, gInv a l * D l p a)
          = ∑ l : Idx, ∑ a : Idx, gInv a l * D l p a := by
            rw [Finset.sum_comm]
      _ = ∑ l : Idx, ∑ a : Idx, gInv l a * D l p a := by
            refine Finset.sum_congr rfl fun l _ => ?_
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [hsym a l]
      _ = ∑ a : Idx, ∑ l : Idx, gInv a l * D a p l := rfl
  have hsplit :
      (∑ a : Idx, ∑ l : Idx, gInv a l * (D p a l + D a p l - D l p a))
        = S₁ + S₂ - S₃ := by
    unfold S₁ S₂ S₃
    simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  calc
    (∑ a : Idx,
        (1 / 2 : ℝ) *
          ∑ l : Idx, gInv a l * (D p a l + D a p l - D l p a))
        =
      (1 / 2 : ℝ) *
        (∑ a : Idx, ∑ l : Idx, gInv a l * (D p a l + D a p l - D l p a)) := by
          rw [Finset.mul_sum]
    _ = (1 / 2 : ℝ) * (S₁ + S₂ - S₃) := by
          rw [hsplit]
    _ = (1 / 2 : ℝ) * S₁ := by
          rw [hS₃]
          ring
    _ = (1 / 2 : ℝ) * ∑ i : Idx, ∑ j : Idx, gInv i j * D p i j := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Connection.traceChristoffelAlg
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Connection.traceChristoffelAlg target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] in
omit [InnerProductSpace ℝ E] in
theorem lcTrace_halfTrace
    (g : SmoothRiemannianMetric I M) (x : M)
    (p : Fin (Module.finrank ℝ E)) :
    (∑ a : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g x p a a (extChartAt I x x))
      =
    (1 / 2 : ℝ) *
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x i j *
            DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) p
              (fun y : E =>
                DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g x ((extChartAt I x).symm y) i j)
              (extChartAt I x x) := by
  classical
  let y₀ : E := extChartAt I x x
  have hsymm_y₀ : (extChartAt I x).symm y₀ = x := by
    simp only [y₀]
    rw [(extChartAt I x).left_inv (mem_extChartAt_source (I := I) x)]
  let gInv : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun i j => chartInvGramMatrix (I := I) g x x i j
  let D :
      Fin (Module.finrank ℝ E) →
        Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun r i j =>
      DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) r (chartGramOnE (I := I) g x i j) y₀
  have hsym : ∀ i j : Fin (Module.finrank ℝ E), gInv i j = gInv j i := by
    intro i j
    exact (chartInvGramMatrix_symm (I := I) g x x j i)
  have hformula :
      ∀ a : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g x p a a y₀ =
          (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
            gInv a l * (D p a l + D a p l - D l p a) := by
    intro a
    rw [chartChristoffel_def]
    simp only [gInv, D, hsymm_y₀]
    refine congrArg (fun t => (1 / 2 : ℝ) * t) ?_
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [show chartGramOnE (I := I) g x l a = chartGramOnE (I := I) g x a l from
          funext fun y => chartGramOnE_symm (I := I) g x l a y,
        show chartGramOnE (I := I) g x l p = chartGramOnE (I := I) g x p l from
          funext fun y => chartGramOnE_symm (I := I) g x l p y]
  calc
    (∑ a : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g x p a a y₀)
        =
      ∑ a : Fin (Module.finrank ℝ E),
        (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
          gInv a l * (D p a l + D a p l - D l p a) := by
          refine Finset.sum_congr rfl fun a _ => hformula a
    _ =
      (1 / 2 : ℝ) * ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E), gInv i j * D p i j := by
          exact traceChristoffelAlg gInv D hsym p
    _ =
      (1 / 2 : ℝ) *
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g x x i j *
              DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) p
                (fun y : E =>
                  DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g x ((extChartAt I x).symm y) i j)
                y₀ := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.lcTrace_halfTrace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.lcTrace_halfTrace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.lcTrace_halfTrace ``Submission.DifferentialGeometry.Geometry.Connection.lcTrace_halfTrace

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] in
omit [InnerProductSpace ℝ E] in
theorem lcTrace_logDensity
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    (p : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) p
        (chartDensityOnE (I := I) g x) (extChartAt I x x) /
      chartDensity (I := I) g x x
      =
    ∑ a : Fin (Module.finrank ℝ E),
      chartChristoffel (I := I) g x p a a (extChartAt I x x) := by
  have hρ :
      chartDensityOnE (I := I) g x (extChartAt I x x) =
        chartDensity (I := I) g x x := by
    change chartDensity (I := I) g x ((extChartAt I x).symm (extChartAt I x x)) =
      chartDensity (I := I) g x x
    rw [(extChartAt I x).left_inv (mem_extChartAt_source (I := I) x)]
  calc
    DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) p
        (chartDensityOnE (I := I) g x) (extChartAt I x x) /
      chartDensity (I := I) g x x
        =
      DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) p
        (chartDensityOnE (I := I) g x) (extChartAt I x x) /
      chartDensityOnE (I := I) g x (extChartAt I x x) := by
          rw [hρ]
    _ =
      (1 / 2 : ℝ) *
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g x x i j *
              DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) p
                (fun y : E =>
                  DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g x ((extChartAt I x).symm y) i j)
                (extChartAt I x x) := by
          exact
            chartDensityOnE_partial_div_eq_half_trace_invGram_partialGram
              (I := I) g x p
    _ =
      ∑ a : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g x p a a (extChartAt I x x) := by
          exact (lcTrace_halfTrace (I := I) g x p).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.lcTrace_logDensity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.lcTrace_logDensity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.lcTrace_logDensity ``Submission.DifferentialGeometry.Geometry.Connection.lcTrace_logDensity

end DifferentialGeometry.Geometry.Connection
