import Submission.DifferentialGeometry.Analysis.Integration.Measure.Chart.Density
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Basic
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Invariance
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Properties
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Jacobian.Derivative
import Submission.DifferentialGeometry.Bundle.PartialMfderiv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.PosDef

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.Bundle _root_.Manifold _root_.Set _root_.MeasureTheory _root_.Matrix
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.Matrix _root_.BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance _root_.Submission.DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

def riemannianMeasureFamily
    {P : Type*}
    [T2Space M] [SigmaCompactSpace M]
    (g_fam : P → SmoothRiemannianMetric I M) : P → MeasureTheory.Measure M :=
  fun t => riemannianVolumeMeasure (I := I) (M := M) (g_fam t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.riemannianMeasureFamily then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.riemannianMeasureFamily"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.riemannianMeasureFamily ``Submission.DifferentialGeometry.Integral.Measure.riemannianMeasureFamily

lemma riemannianMeasureFamily_def
    {P : Type*}
    [T2Space M] [SigmaCompactSpace M]
    (g_fam : P → SmoothRiemannianMetric I M) (t : P) :
    riemannianMeasureFamily (I := I) (M := M) g_fam t =
      riemannianVolumeMeasure (I := I) (M := M) (g_fam t) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.riemannianMeasureFamily_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.riemannianMeasureFamily_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.riemannianMeasureFamily_def ``Submission.DifferentialGeometry.Integral.Measure.riemannianMeasureFamily_def

structure MetricFamilyRegularAt
    (g_fam : ℝ → SmoothRiemannianMetric I M) (t₀ : ℝ) : Prop where
  hasDerivAt_chartGramMatrix :
    ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)) {x : M},
      x ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet →
      ∀ t : ℝ,
        HasDerivAt (fun s : ℝ => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam s) x₀ x i j)
          (deriv (fun s : ℝ => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam s) x₀ x i j) t) t
  continuousOn_chartGramMatrix :
    ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam p.1) x₀ p.2 i j)
        (Set.univ ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet)
  continuousOn_deriv_chartGramMatrix :
    ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun p : ℝ × M =>
          deriv (fun s : ℝ => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam s) x₀ p.2 i j) p.1)
        (Set.univ ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.MetricFamilyRegularAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.MetricFamilyRegularAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.MetricFamilyRegularAt ``Submission.DifferentialGeometry.Integral.Measure.MetricFamilyRegularAt

lemma MetricFamilyRegularAt.at_any
    {g_fam : ℝ → SmoothRiemannianMetric I M} {t : ℝ}
    (hreg : MetricFamilyRegularAt (I := I) g_fam t) (s : ℝ) :
    MetricFamilyRegularAt (I := I) g_fam s :=
  { hasDerivAt_chartGramMatrix := hreg.hasDerivAt_chartGramMatrix
    continuousOn_chartGramMatrix := hreg.continuousOn_chartGramMatrix
    continuousOn_deriv_chartGramMatrix := hreg.continuousOn_deriv_chartGramMatrix }

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Integral.Measure.MetricFamilyRegularAt
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.MetricFamilyRegularAt.at_any then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.MetricFamilyRegularAt.at_any"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.MetricFamilyRegularAt.at_any ``Submission.DifferentialGeometry.Integral.Measure.MetricFamilyRegularAt.at_any

structure FunctionRegularAt (f : ℝ → M → ℝ) (t₀ : ℝ) : Prop where
  hasDerivAt_time :
    ∀ (x : M) (t : ℝ), HasDerivAt (fun s : ℝ => f s x) (deriv (fun s : ℝ => f s x) t) t
  continuous_joint : Continuous (fun p : ℝ × M => f p.1 p.2)
  continuous_deriv_joint :
    Continuous (fun p : ℝ × M => deriv (fun s : ℝ => f s p.2) p.1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.FunctionRegularAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.FunctionRegularAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.FunctionRegularAt ``Submission.DifferentialGeometry.Integral.Measure.FunctionRegularAt

omit [Module.Finite ℝ E] in
theorem FunctionRegularAt.of_contMDiff
    (f : ℝ → M → ℝ)
    (hf : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => f p.1 p.2)) (t₀ : ℝ) :
    FunctionRegularAt f t₀ := by
  let F : C^∞⟮(modelWithCornersSelf ℝ ℝ).prod I, ℝ × M; ℝ⟯ :=
    ⟨fun p => f p.1 p.2, hf⟩
  refine ⟨?_, hf.continuous, ?_⟩
  · intro x t
    have htime : ContDiff ℝ ∞ (fun s => f s x) :=
      contMDiff_iff_contDiff.mp
        (hf.comp (contMDiff_id.prodMk contMDiff_const))
    exact (htime.differentiable (by norm_num)).differentiableAt.hasDerivAt
  · have h := (DifferentialGeometry.contMDiff_partial_deriv_fst I F).continuous
    change Continuous (fun p : ℝ × M => deriv (fun s : ℝ => f s p.2) p.1) at h
    exact h

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Integral.Measure.FunctionRegularAt
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.FunctionRegularAt.of_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.FunctionRegularAt.of_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.FunctionRegularAt.of_contMDiff ``Submission.DifferentialGeometry.Integral.Measure.FunctionRegularAt.of_contMDiff

section ChartDensityFamily

variable {g_fam : ℝ → SmoothRiemannianMetric I M}

def chartGramMatrixFamily
    (g_fam : ℝ → SmoothRiemannianMetric I M) (x₀ x : M) :
    ℝ → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  fun t => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam t) x₀ x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.chartGramMatrixFamily then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.chartGramMatrixFamily"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.chartGramMatrixFamily ``Submission.DifferentialGeometry.Integral.Measure.chartGramMatrixFamily

@[simp] lemma chartGramMatrixFamily_apply
    (g_fam : ℝ → SmoothRiemannianMetric I M) (x₀ x : M) (t : ℝ) :
    chartGramMatrixFamily (I := I) g_fam x₀ x t =
      DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam t) x₀ x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.chartGramMatrixFamily_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.chartGramMatrixFamily_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.chartGramMatrixFamily_apply ``Submission.DifferentialGeometry.Integral.Measure.chartGramMatrixFamily_apply

def chartDensityFamily
    (g_fam : ℝ → SmoothRiemannianMetric I M) (x₀ x : M) :
    ℝ → ℝ :=
  fun t => chartDensity (I := I) (g_fam t) x₀ x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.chartDensityFamily then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.chartDensityFamily"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.chartDensityFamily ``Submission.DifferentialGeometry.Integral.Measure.chartDensityFamily

@[simp] lemma chartDensityFamily_apply
    (g_fam : ℝ → SmoothRiemannianMetric I M) (x₀ x : M) (t : ℝ) :
    chartDensityFamily (I := I) g_fam x₀ x t =
      chartDensity (I := I) (g_fam t) x₀ x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.chartDensityFamily_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.chartDensityFamily_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.chartDensityFamily_apply ``Submission.DifferentialGeometry.Integral.Measure.chartDensityFamily_apply

lemma chartDensityFamily_eq_sqrt_det
    (g_fam : ℝ → SmoothRiemannianMetric I M) (x₀ x : M) (t : ℝ) :
    chartDensityFamily (I := I) g_fam x₀ x t =
      Real.sqrt (chartGramMatrixFamily (I := I) g_fam x₀ x t).det := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.chartDensityFamily_eq_sqrt_det then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.chartDensityFamily_eq_sqrt_det"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.chartDensityFamily_eq_sqrt_det ``Submission.DifferentialGeometry.Integral.Measure.chartDensityFamily_eq_sqrt_det

theorem hasDerivAt_chartDensityFamily_eq_half_trace_inv_mul
    (g_fam : ℝ → SmoothRiemannianMetric I M) (x₀ : M) (t : ℝ) {x : M}
    (hx : x ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet)
    (Gprime : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ)
    (hEntries : ∀ i j : Fin (Module.finrank ℝ E),
      HasDerivAt (fun s => chartGramMatrixFamily (I := I) g_fam x₀ x s i j)
        (Gprime i j) t) :
    HasDerivAt
      (fun s => chartDensityFamily (I := I) g_fam x₀ x s)
      ((1 / 2) *
        trace ((chartGramMatrixFamily (I := I) g_fam x₀ x t)⁻¹ * Gprime) *
        Real.sqrt (chartGramMatrixFamily (I := I) g_fam x₀ x t).det) t := by
  have hpos : 0 < (chartGramMatrixFamily (I := I) g_fam x₀ x t).det := by
    simpa [chartGramMatrixFamily_apply] using
      DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_det_pos (I := I) (g_fam t) x₀ hx
  have hderiv := hasDerivAt_sqrt_det_eq_half_trace_inv_mul
    (G := chartGramMatrixFamily (I := I) g_fam x₀ x)
    (G' := Gprime) (t := t) hEntries hpos
  have hfun :
      (fun s => chartDensityFamily (I := I) g_fam x₀ x s)
        = (fun s => Real.sqrt (chartGramMatrixFamily (I := I) g_fam x₀ x s).det) := by
    funext s
    exact chartDensityFamily_eq_sqrt_det (I := I) g_fam x₀ x s
  rw [hfun]
  exact hderiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.hasDerivAt_chartDensityFamily_eq_half_trace_inv_mul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.hasDerivAt_chartDensityFamily_eq_half_trace_inv_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.hasDerivAt_chartDensityFamily_eq_half_trace_inv_mul ``Submission.DifferentialGeometry.Integral.Measure.hasDerivAt_chartDensityFamily_eq_half_trace_inv_mul

end ChartDensityFamily

variable (I) in
def traceTimeDerivMetric
    (g_fam : ℝ → SmoothRiemannianMetric I M) (t : ℝ) (x : M) : ℝ :=
  Matrix.trace ((DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam t) x x)⁻¹ *
    (Matrix.of fun i j =>
      deriv (fun s => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam s) x x i j) t))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.traceTimeDerivMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.traceTimeDerivMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.traceTimeDerivMetric ``Submission.DifferentialGeometry.Integral.Measure.traceTimeDerivMetric

lemma traceTimeDerivMetric_eq
    (g_fam : ℝ → SmoothRiemannianMetric I M) (t : ℝ) (x : M) :
    traceTimeDerivMetric (I := I) g_fam t x =
      Matrix.trace ((DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam t) x x)⁻¹ *
        (Matrix.of fun i j =>
          deriv (fun s => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam s) x x i j) t)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.traceTimeDerivMetric_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.traceTimeDerivMetric_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.traceTimeDerivMetric_eq ``Submission.DifferentialGeometry.Integral.Measure.traceTimeDerivMetric_eq

theorem continuousOn_deriv_of_hasDerivAt_eq_continuousOn
    {α : Type*} [TopologicalSpace α]
    {S : Set (ℝ × α)} {f D : ℝ → α → ℝ}
    (hderiv :
      ∀ p ∈ S, HasDerivAt (fun t : ℝ => f t p.2) (D p.1 p.2) p.1)
    (hD : ContinuousOn (fun p : ℝ × α => D p.1 p.2) S) :
    ContinuousOn
      (fun p : ℝ × α => deriv (fun t : ℝ => f t p.2) p.1)
      S := by
  have h_eq : Set.EqOn
      (fun p : ℝ × α => deriv (fun t : ℝ => f t p.2) p.1)
      (fun p : ℝ × α => D p.1 p.2) S := by
    intro p hp
    exact (hderiv p hp).deriv
  exact hD.congr h_eq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.continuousOn_deriv_of_hasDerivAt_eq_continuousOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.continuousOn_deriv_of_hasDerivAt_eq_continuousOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.continuousOn_deriv_of_hasDerivAt_eq_continuousOn ``Submission.DifferentialGeometry.Integral.Measure.continuousOn_deriv_of_hasDerivAt_eq_continuousOn

theorem MetricFamilyRegularAt.of_chartGram_timeDeriv
    {g_fam : ℝ → SmoothRiemannianMetric I M} {t₀ : ℝ}
    (h :
      ∀ x₀ i j, ∃ D : ℝ → M → ℝ,
        (∀ t x,
          x ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet →
            HasDerivAt
              (fun s : ℝ => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam s) x₀ x i j)
              (D t x) t) ∧
        ContinuousOn
          (fun p : ℝ × M =>
            DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam p.1) x₀ p.2 i j)
          (Set.univ ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet) ∧
        ContinuousOn
          (fun p : ℝ × M => D p.1 p.2)
          (Set.univ ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet)) :
    MetricFamilyRegularAt (I := I) g_fam t₀ := by
  refine
    { hasDerivAt_chartGramMatrix := ?_
      continuousOn_chartGramMatrix := ?_
      continuousOn_deriv_chartGramMatrix := ?_ }
  · intro x₀ i j x hx t
    rcases h x₀ i j with ⟨D, hD_deriv, -, -⟩
    have hderiv := hD_deriv t x hx
    exact hderiv.congr_deriv hderiv.deriv.symm
  · intro x₀ i j
    rcases h x₀ i j with ⟨D, -, hG_cont, -⟩
    exact hG_cont
  · intro x₀ i j
    rcases h x₀ i j with ⟨D, hD_deriv, -, hD_cont⟩
    refine continuousOn_deriv_of_hasDerivAt_eq_continuousOn
      (S := Set.univ ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet)
      (f := fun t x => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam t) x₀ x i j)
      (D := D) ?_ hD_cont
    intro p hp
    exact hD_deriv p.1 p.2 hp.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.MetricFamilyRegularAt.of_chartGram_timeDeriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.MetricFamilyRegularAt.of_chartGram_timeDeriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.MetricFamilyRegularAt.of_chartGram_timeDeriv ``Submission.DifferentialGeometry.Integral.Measure.MetricFamilyRegularAt.of_chartGram_timeDeriv

theorem FunctionRegularAt_const (c : ℝ) (t₀ : ℝ) :
    FunctionRegularAt (fun _ : ℝ => fun _ : M => c) t₀ := by
  refine
    { hasDerivAt_time := ?_
      continuous_joint := ?_
      continuous_deriv_joint := ?_ }
  · intro _ t
    have hderiv : deriv (fun _ : ℝ => c) t = 0 :=
      (hasDerivAt_const (x := t) (c := c)).deriv
    simpa [hderiv] using (hasDerivAt_const (x := t) (c := c))
  · simpa using (continuous_const : Continuous (fun _ : ℝ × M => c))
  · have hfun :
        (fun p : ℝ × M => deriv (fun _ : ℝ => c) p.1) =
          fun _ : ℝ × M => (0 : ℝ) := by
      funext p
      exact (hasDerivAt_const (x := p.1) (c := c)).deriv
    simpa [hfun] using (continuous_const : Continuous (fun _ : ℝ × M => (0 : ℝ)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.FunctionRegularAt_const then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.FunctionRegularAt_const"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.FunctionRegularAt_const ``Submission.DifferentialGeometry.Integral.Measure.FunctionRegularAt_const

theorem FunctionRegularAt_one (t₀ : ℝ) :
    FunctionRegularAt (fun _ : ℝ => fun _ : M => (1 : ℝ)) t₀ :=
  FunctionRegularAt_const (M := M) 1 t₀

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.FunctionRegularAt_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.FunctionRegularAt_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.FunctionRegularAt_one ``Submission.DifferentialGeometry.Integral.Measure.FunctionRegularAt_one
end Measure
end Integral
end DifferentialGeometry
