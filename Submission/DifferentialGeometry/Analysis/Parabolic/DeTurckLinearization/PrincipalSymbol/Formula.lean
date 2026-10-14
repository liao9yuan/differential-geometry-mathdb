import Submission.DifferentialGeometry.Analysis.Parabolic.DeTurckLinearization.PrincipalSymbol.Remainder
import Submission.DifferentialGeometry.Analysis.Parabolic.RicciLinearization.Symbol.Formula

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
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

section GramBridge

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma chartGramOnE_extChartAt_self (g : SmoothRiemannianMetric I M) (x : M)
    (k j : Fin (Module.finrank ℝ E)) :
    chartGramOnE (I := I) g x k j (extChartAt I x x) =
      DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g x x k j := by
  rw [chartGramOnE_def, extChartAt_to_inv]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.chartGramOnE_extChartAt_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.chartGramOnE_extChartAt_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.chartGramOnE_extChartAt_self ``Submission.DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.chartGramOnE_extChartAt_self

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma sum_chartGram_mul_chartInvGram_self (g : SmoothRiemannianMetric I M) (x : M)
    (j l : Fin (Module.finrank ℝ E)) :
    ∑ k : Fin (Module.finrank ℝ E),
        DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g x x k j *
          chartInvGramMatrix (I := I) g x x k l =
      (if l = j then (1 : ℝ) else 0) := by
  have hx : x ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact mem_chart_source H x
  have hmul := chartInvGramMatrix_mul_chartGramMatrix (I := I) g x hx
  have hentry : (chartInvGramMatrix (I := I) g x x *
      DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g x x) l j = (1 : Matrix _ _ ℝ) l j := by
    rw [hmul]
  rw [Matrix.one_apply, Matrix.mul_apply] at hentry
  rw [← hentry]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [chartInvGramMatrix_self_symm (I := I) g x l k]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.sum_chartGram_mul_chartInvGram_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.sum_chartGram_mul_chartInvGram_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.sum_chartGram_mul_chartInvGram_self ``Submission.DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.sum_chartGram_mul_chartInvGram_self

end GramBridge

section SymbolComponent


def deTurckCorrectionSymbolComp (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (i j : Fin (Module.finrank ℝ E)) : ℝ :=
  (∑ k : Fin (Module.finrank ℝ E),
      chartGramOnE (I := I) g x k j (extChartAt I x x) *
        ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g x a b (extChartAt I x x) *
            ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g x k l (extChartAt I x x) *
                ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ i * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ a *
                    formComp (I := I) x t l b +
                  (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ i * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ b *
                    formComp (I := I) x t l a -
                  (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ i * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ l *
                    formComp (I := I) x t a b))) +
  (∑ k : Fin (Module.finrank ℝ E),
      chartGramOnE (I := I) g x i k (extChartAt I x x) *
        ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g x a b (extChartAt I x x) *
            ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g x k l (extChartAt I x x) *
                ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ j * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ a *
                    formComp (I := I) x t l b +
                  (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ j * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ b *
                    formComp (I := I) x t l a -
                  (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ j * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ l *
                    formComp (I := I) x t a b)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.deTurckCorrectionSymbolComp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.deTurckCorrectionSymbolComp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.deTurckCorrectionSymbolComp ``Submission.DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.deTurckCorrectionSymbolComp

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp] lemma deTurckCorrectionSymbolComp_def (g : SmoothRiemannianMetric I M) (x : M)
    (ξ : E) (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (i j : Fin (Module.finrank ℝ E)) :
    deTurckCorrectionSymbolComp (I := I) g x ξ t i j =
      (∑ k : Fin (Module.finrank ℝ E),
          chartGramOnE (I := I) g x k j (extChartAt I x x) *
            ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g x a b (extChartAt I x x) *
                ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
                  chartInvGramOnE (I := I) g x k l (extChartAt I x x) *
                    ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ i * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ a *
                        formComp (I := I) x t l b +
                      (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ i * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ b *
                        formComp (I := I) x t l a -
                      (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ i * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ l *
                        formComp (I := I) x t a b))) +
      (∑ k : Fin (Module.finrank ℝ E),
          chartGramOnE (I := I) g x i k (extChartAt I x x) *
            ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g x a b (extChartAt I x x) *
                ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
                  chartInvGramOnE (I := I) g x k l (extChartAt I x x) *
                    ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ j * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ a *
                        formComp (I := I) x t l b +
                      (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ j * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ b *
                        formComp (I := I) x t l a -
                      (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ j * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ l *
                        formComp (I := I) x t a b))) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.deTurckCorrectionSymbolComp_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.deTurckCorrectionSymbolComp_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.deTurckCorrectionSymbolComp_def ``Submission.DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.deTurckCorrectionSymbolComp_def

end SymbolComponent

section ClosedForm

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma block_term_a (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (d m : Fin (Module.finrank ℝ E)) :
    ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g x x a b *
          ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ d * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ a *
            formComp (I := I) x t m b) =
      (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ d *
        raisedFormContractionSnd (I := I) g x ξ t m := by
  calc
    ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x a b *
            ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ d * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ a *
              formComp (I := I) x t m b)
      = ∑ b : Fin (Module.finrank ℝ E),
          (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ d *
            (raisedCovectorComp (I := I) g x ξ b * formComp (I := I) x t m b) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun b _ => ?_)
        rw [raisedCovectorComp_def, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [chartInvGramMatrix_self_symm (I := I) g x a b]
        ring
    _ = (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ d *
          raisedFormContractionSnd (I := I) g x ξ t m := by
        rw [raisedFormContractionSnd_def, Finset.mul_sum]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.block_term_a
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.block_term_a target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma block_term_b (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (d m : Fin (Module.finrank ℝ E)) :
    ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g x x a b *
          ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ d * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ b *
            formComp (I := I) x t m a) =
      (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ d *
        raisedFormContractionSnd (I := I) g x ξ t m := by
  calc
    ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x a b *
            ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ d * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ b *
              formComp (I := I) x t m a)
      = ∑ a : Fin (Module.finrank ℝ E),
          (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ d *
            (raisedCovectorComp (I := I) g x ξ a * formComp (I := I) x t m a) := by
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [raisedCovectorComp_def, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun b _ => ?_)
        ring
    _ = (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ d *
          raisedFormContractionSnd (I := I) g x ξ t m := by
        rw [raisedFormContractionSnd_def, Finset.mul_sum]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.block_term_b
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.block_term_b target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma block_term_trace (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (d m : Fin (Module.finrank ℝ E)) :
    ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g x x a b *
          ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ d * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ m *
            formComp (I := I) x t a b) =
      (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ d * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ m *
        formMetricTrace (I := I) g x t := by
  rw [formMetricTrace_def, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.block_term_trace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.block_term_trace target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma deTurckCorrection_block_contraction (g : SmoothRiemannianMetric I M) (x : M)
    (ξ : E) (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (d m : Fin (Module.finrank ℝ E)) :
    ∑ k : Fin (Module.finrank ℝ E),
        DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g x x k m *
          ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g x x a b *
              ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
                chartInvGramMatrix (I := I) g x x k l *
                  ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ d * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ a *
                      formComp (I := I) x t l b +
                    (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ d * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ b *
                      formComp (I := I) x t l a -
                    (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ d * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ l *
                      formComp (I := I) x t a b)) =
      (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ d *
            raisedFormContractionSnd (I := I) g x ξ t m -
        (1 / 2 : ℝ) * ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ d * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ m *
          formMetricTrace (I := I) g x t) := by
  have hstage1 : ∀ a b : Fin (Module.finrank ℝ E),
      ∑ k : Fin (Module.finrank ℝ E),
          DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g x x k m *
            (chartInvGramMatrix (I := I) g x x a b *
              ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
                chartInvGramMatrix (I := I) g x x k l *
                  ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ d * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ a *
                      formComp (I := I) x t l b +
                    (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ d * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ b *
                      formComp (I := I) x t l a -
                    (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ d * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ l *
                      formComp (I := I) x t a b))) =
        chartInvGramMatrix (I := I) g x x a b *
          ((1 / 2 : ℝ) *
            ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ d * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ a *
                formComp (I := I) x t m b +
              (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ d * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ b *
                formComp (I := I) x t m a -
              (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ d * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ m *
                formComp (I := I) x t a b)) := by
    intro a b
    set P : Fin (Module.finrank ℝ E) → ℝ := fun l =>
      (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ d * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ a *
          formComp (I := I) x t l b +
        (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ d * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ b *
          formComp (I := I) x t l a -
        (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ d * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ l *
          formComp (I := I) x t a b with hP
    calc
      ∑ k : Fin (Module.finrank ℝ E),
            DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g x x k m *
              (chartInvGramMatrix (I := I) g x x a b *
                ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
                  chartInvGramMatrix (I := I) g x x k l * P l))
        = ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
            DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g x x k m *
              (chartInvGramMatrix (I := I) g x x a b *
                ((1 / 2 : ℝ) * (chartInvGramMatrix (I := I) g x x k l * P l))) := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      _ = ∑ l : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
            DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g x x k m *
              (chartInvGramMatrix (I := I) g x x a b *
                ((1 / 2 : ℝ) * (chartInvGramMatrix (I := I) g x x k l * P l))) :=
          Finset.sum_comm
      _ = ∑ l : Fin (Module.finrank ℝ E),
            (if l = m then (1 : ℝ) else 0) *
              (chartInvGramMatrix (I := I) g x x a b * ((1 / 2 : ℝ) * P l)) := by
          refine Finset.sum_congr rfl (fun l _ => ?_)
          rw [← sum_chartGram_mul_chartInvGram_self (I := I) g x m l, Finset.sum_mul]
          refine Finset.sum_congr rfl (fun k _ => ?_)
          ring
      _ = chartInvGramMatrix (I := I) g x x a b * ((1 / 2 : ℝ) * P m) := by
          rw [Finset.sum_eq_single m]
          · rw [if_pos rfl, one_mul]
          · intro l _ hl
            rw [if_neg hl, _root_.MulZeroClass.zero_mul]
          · intro hm
            exact absurd (Finset.mem_univ m) hm
  have reorder :
      (∑ k : Fin (Module.finrank ℝ E),
          DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g x x k m *
            ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              chartInvGramMatrix (I := I) g x x a b *
                ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
                  chartInvGramMatrix (I := I) g x x k l *
                    ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ d * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ a *
                        formComp (I := I) x t l b +
                      (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ d * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ b *
                        formComp (I := I) x t l a -
                      (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ d * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ l *
                        formComp (I := I) x t a b))) =
        ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g x x k m *
              (chartInvGramMatrix (I := I) g x x a b *
                ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
                  chartInvGramMatrix (I := I) g x x k l *
                    ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ d * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ a *
                        formComp (I := I) x t l b +
                      (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ d * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ b *
                        formComp (I := I) x t l a -
                      (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ d * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ l *
                        formComp (I := I) x t a b))) := by
    have hrow : (∑ k : Fin (Module.finrank ℝ E),
          DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g x x k m *
            ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              chartInvGramMatrix (I := I) g x x a b *
                ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
                  chartInvGramMatrix (I := I) g x x k l *
                    ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ d * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ a *
                        formComp (I := I) x t l b +
                      (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ d * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ b *
                        formComp (I := I) x t l a -
                      (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ d * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ l *
                        formComp (I := I) x t a b))) =
        ∑ k : Fin (Module.finrank ℝ E), ∑ a : Fin (Module.finrank ℝ E),
          ∑ b : Fin (Module.finrank ℝ E),
            DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g x x k m *
              (chartInvGramMatrix (I := I) g x x a b *
                ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
                  chartInvGramMatrix (I := I) g x x k l *
                    ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ d * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ a *
                        formComp (I := I) x t l b +
                      (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ d * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ b *
                        formComp (I := I) x t l a -
                      (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ d * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ l *
                        formComp (I := I) x t a b))) := by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [Finset.mul_sum]
    rw [hrow, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.sum_comm]
  rw [reorder]
  rw [show (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        ∑ k : Fin (Module.finrank ℝ E),
          DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g x x k m *
            (chartInvGramMatrix (I := I) g x x a b *
              ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
                chartInvGramMatrix (I := I) g x x k l *
                  ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ d * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ a *
                      formComp (I := I) x t l b +
                    (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ d * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ b *
                      formComp (I := I) x t l a -
                    (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ d * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ l *
                      formComp (I := I) x t a b)))) =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g x x a b *
          ((1 / 2 : ℝ) *
            ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ d * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ a *
                formComp (I := I) x t m b +
              (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ d * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ b *
                formComp (I := I) x t m a -
              (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ d * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ m *
                formComp (I := I) x t a b)) from by
    refine Finset.sum_congr rfl (fun a _ => ?_)
    refine Finset.sum_congr rfl (fun b _ => ?_)
    exact hstage1 a b]
  calc
    ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x a b *
            ((1 / 2 : ℝ) *
              ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ d * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ a *
                  formComp (I := I) x t m b +
                (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ d * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ b *
                  formComp (I := I) x t m a -
                (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ d * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ m *
                  formComp (I := I) x t a b))
      = (1 / 2 : ℝ) * ∑ a : Fin (Module.finrank ℝ E),
          ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g x x a b *
              ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ d * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ a *
                  formComp (I := I) x t m b +
                (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ d * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ b *
                  formComp (I := I) x t m a -
                (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ d * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ m *
                  formComp (I := I) x t a b) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun b _ => ?_)
        ring
    _ = (1 / 2 : ℝ) *
          ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              chartInvGramMatrix (I := I) g x x a b *
                ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ d * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ a *
                  formComp (I := I) x t m b)) +
            (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
                chartInvGramMatrix (I := I) g x x a b *
                  ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ d * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ b *
                    formComp (I := I) x t m a)) -
            (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
                chartInvGramMatrix (I := I) g x x a b *
                  ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ d * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ m *
                    formComp (I := I) x t a b))) := by
        refine congrArg _ ?_
        rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun b _ => ?_)
        ring
    _ = (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ d *
            raisedFormContractionSnd (I := I) g x ξ t m -
          (1 / 2 : ℝ) * ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ d * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ m *
            formMetricTrace (I := I) g x t) := by
        rw [block_term_a (I := I) g x ξ t d m, block_term_b (I := I) g x ξ t d m,
          block_term_trace (I := I) g x ξ t d m]
        ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.deTurckCorrection_block_contraction
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.deTurckCorrection_block_contraction target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem deTurckCorrectionSymbolComp_eq_closedForm (g : SmoothRiemannianMetric I M) (x : M)
    (ξ : E) (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (i j : Fin (Module.finrank ℝ E)) :
    deTurckCorrectionSymbolComp (I := I) g x ξ t i j =
      (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ i *
          raisedFormContractionSnd (I := I) g x ξ t j +
        (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ j *
          raisedFormContractionSnd (I := I) g x ξ t i -
        (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ i * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ j *
          formMetricTrace (I := I) g x t := by
  have hgram : ∀ k j' : Fin (Module.finrank ℝ E),
      chartGramOnE (I := I) g x k j' (extChartAt I x x) =
        DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g x x k j' :=
    fun k j' => chartGramOnE_extChartAt_self (I := I) g x k j'
  have hinv : ∀ a b : Fin (Module.finrank ℝ E),
      chartInvGramOnE (I := I) g x a b (extChartAt I x x) =
        chartInvGramMatrix (I := I) g x x a b :=
    fun a b => chartInvGramOnE_extChartAt_self (I := I) g x a b
  have hksum : ∀ d m : Fin (Module.finrank ℝ E),
      (∑ k : Fin (Module.finrank ℝ E),
          chartGramOnE (I := I) g x k m (extChartAt I x x) *
            ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g x a b (extChartAt I x x) *
                ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
                  chartInvGramOnE (I := I) g x k l (extChartAt I x x) *
                    ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ d * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ a *
                        formComp (I := I) x t l b +
                      (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ d * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ b *
                        formComp (I := I) x t l a -
                      (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ d * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ l *
                        formComp (I := I) x t a b))) =
        (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ d *
              raisedFormContractionSnd (I := I) g x ξ t m -
          (1 / 2 : ℝ) * ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ d * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ m *
            formMetricTrace (I := I) g x t) := by
    intro d m
    rw [← deTurckCorrection_block_contraction (I := I) g x ξ t d m]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hgram k m]
    refine congrArg _ ?_
    refine Finset.sum_congr rfl (fun a _ => ?_)
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [hinv a b]
    refine congrArg _ ?_
    refine congrArg _ ?_
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [hinv k l]
  have hsecond :
      (∑ k : Fin (Module.finrank ℝ E),
          chartGramOnE (I := I) g x i k (extChartAt I x x) *
            ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g x a b (extChartAt I x x) *
                ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
                  chartInvGramOnE (I := I) g x k l (extChartAt I x x) *
                    ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ j * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ a *
                        formComp (I := I) x t l b +
                      (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ j * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ b *
                        formComp (I := I) x t l a -
                      (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ j * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ l *
                        formComp (I := I) x t a b))) =
        ∑ k : Fin (Module.finrank ℝ E),
          chartGramOnE (I := I) g x k i (extChartAt I x x) *
            ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g x a b (extChartAt I x x) *
                ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
                  chartInvGramOnE (I := I) g x k l (extChartAt I x x) *
                    ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ j * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ a *
                        formComp (I := I) x t l b +
                      (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ j * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ b *
                        formComp (I := I) x t l a -
                      (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ j * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ l *
                        formComp (I := I) x t a b)) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [chartGramOnE_symm (I := I) g x i k]
  rw [deTurckCorrectionSymbolComp_def, hsecond, hksum i j, hksum j i]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.deTurckCorrectionSymbolComp_eq_closedForm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.deTurckCorrectionSymbolComp_eq_closedForm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.deTurckCorrectionSymbolComp_eq_closedForm ``Submission.DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.deTurckCorrectionSymbolComp_eq_closedForm

end ClosedForm

section Linearity

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem deTurckCorrectionSymbolComp_add (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t t' : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (i j : Fin (Module.finrank ℝ E)) :
    deTurckCorrectionSymbolComp (I := I) g x ξ (t + t') i j =
      deTurckCorrectionSymbolComp (I := I) g x ξ t i j +
        deTurckCorrectionSymbolComp (I := I) g x ξ t' i j := by
  rw [deTurckCorrectionSymbolComp_eq_closedForm (I := I) g x ξ (t + t') i j,
    deTurckCorrectionSymbolComp_eq_closedForm (I := I) g x ξ t i j,
    deTurckCorrectionSymbolComp_eq_closedForm (I := I) g x ξ t' i j,
    raisedFormContractionSnd_add, raisedFormContractionSnd_add, formMetricTrace_add]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.deTurckCorrectionSymbolComp_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.deTurckCorrectionSymbolComp_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.deTurckCorrectionSymbolComp_add ``Submission.DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.deTurckCorrectionSymbolComp_add

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem deTurckCorrectionSymbolComp_smul (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (a : ℝ) (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (i j : Fin (Module.finrank ℝ E)) :
    deTurckCorrectionSymbolComp (I := I) g x ξ (a • t) i j =
      a * deTurckCorrectionSymbolComp (I := I) g x ξ t i j := by
  rw [deTurckCorrectionSymbolComp_eq_closedForm (I := I) g x ξ (a • t) i j,
    deTurckCorrectionSymbolComp_eq_closedForm (I := I) g x ξ t i j,
    raisedFormContractionSnd_smul, raisedFormContractionSnd_smul, formMetricTrace_smul]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.deTurckCorrectionSymbolComp_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.deTurckCorrectionSymbolComp_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.deTurckCorrectionSymbolComp_smul ``Submission.DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.deTurckCorrectionSymbolComp_smul

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem deTurckCorrectionSymbolComp_zero (g : SmoothRiemannianMetric I M) (x : M)
    (ξ : E) (i j : Fin (Module.finrank ℝ E)) :
    deTurckCorrectionSymbolComp (I := I) g x ξ
      (0 : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ) i j = 0 := by
  rw [deTurckCorrectionSymbolComp_eq_closedForm, raisedFormContractionSnd_zero,
    raisedFormContractionSnd_zero, formMetricTrace_zero]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.deTurckCorrectionSymbolComp_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.deTurckCorrectionSymbolComp_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.deTurckCorrectionSymbolComp_zero ``Submission.DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.deTurckCorrectionSymbolComp_zero

end Linearity

section Symmetry

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem deTurckCorrectionSymbolComp_symm (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (i j : Fin (Module.finrank ℝ E)) :
    deTurckCorrectionSymbolComp (I := I) g x ξ t i j =
      deTurckCorrectionSymbolComp (I := I) g x ξ t j i := by
  rw [deTurckCorrectionSymbolComp_eq_closedForm (I := I) g x ξ t i j,
    deTurckCorrectionSymbolComp_eq_closedForm (I := I) g x ξ t j i]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.deTurckCorrectionSymbolComp_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.deTurckCorrectionSymbolComp_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.deTurckCorrectionSymbolComp_symm ``Submission.DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.deTurckCorrectionSymbolComp_symm

end Symmetry

end DeTurckLinearization
end DeTurck
end PDE
end DifferentialGeometry
