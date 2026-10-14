import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.H1Compl.Intrinsic
import Submission.DifferentialGeometry.Analysis.Integration.L2.Pairing.Defs
import Submission.DifferentialGeometry.Geometry.Metric.PointwiseInner.Bounds

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.MeasureTheory _root_.Filter _root_.Function
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.NNReal _root_.Matrix _root_.BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.IntrinsicH1Lp

private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

namespace H1Intrinsic

variable [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]

def dirichletForm (g : SmoothRiemannianMetric I M)
    (u v : H1Intrinsic (I := I) (M := M) g) : ℝ :=
  ∫ x : M,
    g.inner x ((gradL2 (I := I) (M := M) g u : M → E) x)
      ((gradL2 (I := I) (M := M) g v : M → E) x)
    ∂(riemannianVolumeMeasure I M g)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.dirichletForm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.dirichletForm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.dirichletForm ``Submission.DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.dirichletForm

theorem dirichletForm_symm (g : SmoothRiemannianMetric I M)
    (u v : H1Intrinsic (I := I) (M := M) g) :
    dirichletForm (I := I) (M := M) g u v =
      dirichletForm (I := I) (M := M) g v u := by
  unfold dirichletForm
  refine _root_.MeasureTheory.integral_congr_ae ?_
  refine Filter.Eventually.of_forall (fun x => ?_)
  exact g.symm x _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.dirichletForm_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.dirichletForm_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.dirichletForm_symm ``Submission.DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.dirichletForm_symm

theorem dirichletForm_self_nonneg (g : SmoothRiemannianMetric I M)
    (u : H1Intrinsic (I := I) (M := M) g) :
    0 ≤ dirichletForm (I := I) (M := M) g u u := by
  unfold dirichletForm
  apply _root_.MeasureTheory.integral_nonneg
  intro x
  change (0 : ℝ) ≤
    g.inner x ((gradL2 (I := I) (M := M) g u : M → E) x)
      ((gradL2 (I := I) (M := M) g u : M → E) x)
  rcases eq_or_ne ((gradL2 (I := I) (M := M) g u : M → E) x) 0 with h0 | h0
  · have h_zero : g.inner x ((gradL2 (I := I) (M := M) g u : M → E) x)
        ((gradL2 (I := I) (M := M) g u : M → E) x) = 0 := by
      rw [h0]
      change g.inner x (0 : TangentSpace I x) (0 : TangentSpace I x) = 0
      rw [map_zero]
    linarith [h_zero]
  · exact (g.pos x _ h0).le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.dirichletForm_self_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.dirichletForm_self_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.dirichletForm_self_nonneg ``Submission.DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.dirichletForm_self_nonneg

theorem dirichletForm_zero_left (g : SmoothRiemannianMetric I M)
    (u : H1Intrinsic (I := I) (M := M) g) :
    dirichletForm (I := I) (M := M) g 0 u = 0 := by
  unfold dirichletForm
  have h0 : (gradL2 (I := I) (M := M) g (0 : H1Intrinsic (I := I) (M := M) g) :
      Lp E 2 (riemannianVolumeMeasure I M g)) = 0 := by
    rw [(gradL2 (I := I) (M := M) g).map_zero]
  have h_ae : (fun x : M =>
        g.inner x ((gradL2 g (0 : H1Intrinsic g) : M → E) x)
          ((gradL2 g u : M → E) x)) =ᵐ[riemannianVolumeMeasure I M g]
      (fun _ : M => (0 : ℝ)) := by
    have hzero_fn : (fun x : M => ((gradL2 g (0 : H1Intrinsic g) :
          _root_.MeasureTheory.Lp E 2 (riemannianVolumeMeasure I M g)) : M → E) x)
        =ᵐ[riemannianVolumeMeasure I M g] (fun _ : M => (0 : E)) := by
      rw [h0]
      filter_upwards [Lp.coeFn_zero (E := E) (μ := riemannianVolumeMeasure I M g)
        (p := (2 : ℝ≥0∞))] with x hx
      exact hx
    filter_upwards [hzero_fn] with x hx
    rw [hx]
    let w : TangentSpace I x := (gradL2 g u : M → E) x
    let h : g.inner x (0 : TangentSpace I x) w = 0 := by
      rw [map_zero]
      rfl
    exact h
  rw [_root_.MeasureTheory.integral_congr_ae h_ae]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.dirichletForm_zero_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.dirichletForm_zero_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.dirichletForm_zero_left ``Submission.DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.dirichletForm_zero_left

theorem dirichletForm_zero_right (g : SmoothRiemannianMetric I M)
    (u : H1Intrinsic (I := I) (M := M) g) :
    dirichletForm (I := I) (M := M) g u 0 = 0 := by
  rw [dirichletForm_symm (I := I) (M := M) g u 0]
  exact dirichletForm_zero_left (I := I) (M := M) g u

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.dirichletForm_zero_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.dirichletForm_zero_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.dirichletForm_zero_right ``Submission.DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.dirichletForm_zero_right

def shiftedForm (g : SmoothRiemannianMetric I M)
    (u v : H1Intrinsic (I := I) (M := M) g) : ℝ :=
  dirichletForm (I := I) (M := M) g u v +
    ∫ x : M, ((toLp (I := I) (M := M) g u : M → ℝ) x) *
      ((toLp (I := I) (M := M) g v : M → ℝ) x)
    ∂(riemannianVolumeMeasure I M g)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.shiftedForm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.shiftedForm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.shiftedForm ``Submission.DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.shiftedForm

theorem shiftedForm_symm (g : SmoothRiemannianMetric I M)
    (u v : H1Intrinsic (I := I) (M := M) g) :
    shiftedForm (I := I) (M := M) g u v =
      shiftedForm (I := I) (M := M) g v u := by
  unfold shiftedForm
  rw [dirichletForm_symm (I := I) (M := M) g u v]
  congr 1
  refine _root_.MeasureTheory.integral_congr_ae ?_
  refine Filter.Eventually.of_forall (fun x => mul_comm _ _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.shiftedForm_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.shiftedForm_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.shiftedForm_symm ``Submission.DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.shiftedForm_symm

theorem shiftedForm_self_nonneg (g : SmoothRiemannianMetric I M)
    (u : H1Intrinsic (I := I) (M := M) g) :
    0 ≤ shiftedForm (I := I) (M := M) g u u := by
  unfold shiftedForm
  refine add_nonneg (dirichletForm_self_nonneg (I := I) (M := M) g u) ?_
  apply _root_.MeasureTheory.integral_nonneg
  intro x
  exact mul_self_nonneg _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.shiftedForm_self_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.shiftedForm_self_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.shiftedForm_self_nonneg ``Submission.DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.shiftedForm_self_nonneg

theorem shiftedForm_zero_left (g : SmoothRiemannianMetric I M)
    (u : H1Intrinsic (I := I) (M := M) g) :
    shiftedForm (I := I) (M := M) g 0 u = 0 := by
  unfold shiftedForm
  rw [dirichletForm_zero_left (I := I) (M := M) g u]
  rw [zero_add]
  have hzero : (toLp (I := I) (M := M) g (0 : H1Intrinsic (I := I) (M := M) g) :
      Lp ℝ 2 (riemannianVolumeMeasure I M g)) = 0 := by
    rw [(toLp (I := I) (M := M) g).map_zero]
  have h_ae : (fun x : M => ((toLp g (0 : H1Intrinsic g) : M → ℝ) x) *
      ((toLp g u : M → ℝ) x)) =ᵐ[riemannianVolumeMeasure I M g]
      (fun _ : M => (0 : ℝ)) := by
    have hzero_fn : (fun x : M => ((toLp g (0 : H1Intrinsic g) :
          _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure I M g)) : M → ℝ) x)
        =ᵐ[riemannianVolumeMeasure I M g] (fun _ : M => (0 : ℝ)) := by
      rw [hzero]
      filter_upwards [Lp.coeFn_zero (E := ℝ) (μ := riemannianVolumeMeasure I M g)
        (p := (2 : ℝ≥0∞))] with x hx
      exact hx
    filter_upwards [hzero_fn] with x hx
    rw [hx, _root_.MulZeroClass.zero_mul]
  rw [_root_.MeasureTheory.integral_congr_ae h_ae]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.shiftedForm_zero_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.shiftedForm_zero_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.shiftedForm_zero_left ``Submission.DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.shiftedForm_zero_left

theorem shiftedForm_zero_right (g : SmoothRiemannianMetric I M)
    (u : H1Intrinsic (I := I) (M := M) g) :
    shiftedForm (I := I) (M := M) g u 0 = 0 := by
  rw [shiftedForm_symm (I := I) (M := M) g u 0]
  exact shiftedForm_zero_left (I := I) (M := M) g u

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.shiftedForm_zero_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.shiftedForm_zero_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.shiftedForm_zero_right ``Submission.DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.shiftedForm_zero_right

private lemma dirichletForm_integrand_add_left
    (g : SmoothRiemannianMetric I M)
    (u₁ u₂ v : H1Intrinsic (I := I) (M := M) g) :
    (fun x : M => g.inner x ((gradL2 (I := I) (M := M) g (u₁ + u₂) : M → E) x)
        ((gradL2 (I := I) (M := M) g v : M → E) x))
      =ᵐ[riemannianVolumeMeasure I M g]
      (fun x : M => g.inner x ((gradL2 (I := I) (M := M) g u₁ : M → E) x)
        ((gradL2 (I := I) (M := M) g v : M → E) x) +
        g.inner x ((gradL2 (I := I) (M := M) g u₂ : M → E) x)
          ((gradL2 (I := I) (M := M) g v : M → E) x)) := by
  have hgrad_add : (gradL2 (I := I) (M := M) g (u₁ + u₂) :
        _root_.MeasureTheory.Lp E 2 (riemannianVolumeMeasure I M g)) =
      gradL2 (I := I) (M := M) g u₁ + gradL2 (I := I) (M := M) g u₂ :=
    map_add (gradL2 (I := I) (M := M) g) u₁ u₂
  have hfn_add : (fun x : M => ((gradL2 (I := I) (M := M) g (u₁ + u₂) :
        _root_.MeasureTheory.Lp E 2 (riemannianVolumeMeasure I M g)) : M → E) x)
      =ᵐ[riemannianVolumeMeasure I M g]
      (fun x : M => ((gradL2 (I := I) (M := M) g u₁ :
        _root_.MeasureTheory.Lp E 2 (riemannianVolumeMeasure I M g)) : M → E) x +
        ((gradL2 (I := I) (M := M) g u₂ :
          Lp E 2 (riemannianVolumeMeasure I M g)) : M → E) x) := by
    rw [hgrad_add]
    filter_upwards [Lp.coeFn_add (gradL2 (I := I) (M := M) g u₁)
      (gradL2 (I := I) (M := M) g u₂)] with x hx
    exact hx
  filter_upwards [hfn_add] with x hx
  show g.inner x ((gradL2 (I := I) (M := M) g (u₁ + u₂) : M → E) x)
        ((gradL2 (I := I) (M := M) g v : M → E) x) = _
  calc g.inner x ((gradL2 g (u₁ + u₂) : M → E) x) ((gradL2 g v : M → E) x)
      = g.inner x ((gradL2 g u₁ : M → E) x + (gradL2 g u₂ : M → E) x)
          ((gradL2 g v : M → E) x) := by rw [hx]
    _ = (g.inner x ((gradL2 g u₁ : M → E) x) + g.inner x ((gradL2 g u₂ : M → E) x))
          ((gradL2 g v : M → E) x) := by
          congr 1
          exact map_add (g.inner x) _ _
    _ = g.inner x ((gradL2 g u₁ : M → E) x) ((gradL2 g v : M → E) x) +
          g.inner x ((gradL2 g u₂ : M → E) x) ((gradL2 g v : M → E) x) := by
          rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.dirichletForm_integrand_add_left
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.dirichletForm_integrand_add_left target :: scope.openDecls } }

private lemma dirichletForm_integrand_smul_left
    (g : SmoothRiemannianMetric I M) (c : ℝ)
    (u v : H1Intrinsic (I := I) (M := M) g) :
    (fun x : M => g.inner x ((gradL2 (I := I) (M := M) g (c • u) : M → E) x)
        ((gradL2 (I := I) (M := M) g v : M → E) x))
      =ᵐ[riemannianVolumeMeasure I M g]
      (fun x : M => c * g.inner x ((gradL2 (I := I) (M := M) g u : M → E) x)
        ((gradL2 (I := I) (M := M) g v : M → E) x)) := by
  have hgrad_smul : (gradL2 (I := I) (M := M) g (c • u) :
        _root_.MeasureTheory.Lp E 2 (riemannianVolumeMeasure I M g)) =
      c • gradL2 (I := I) (M := M) g u :=
    map_smul (gradL2 (I := I) (M := M) g) c u
  have hfn_smul : (fun x : M => ((gradL2 (I := I) (M := M) g (c • u) :
        _root_.MeasureTheory.Lp E 2 (riemannianVolumeMeasure I M g)) : M → E) x)
      =ᵐ[riemannianVolumeMeasure I M g]
      (fun x : M => c • ((gradL2 (I := I) (M := M) g u :
        Lp E 2 (riemannianVolumeMeasure I M g)) : M → E) x) := by
    rw [hgrad_smul]
    filter_upwards [Lp.coeFn_smul c (gradL2 (I := I) (M := M) g u)] with x hx
    exact hx
  filter_upwards [hfn_smul] with x hx
  show g.inner x ((gradL2 (I := I) (M := M) g (c • u) : M → E) x)
        ((gradL2 (I := I) (M := M) g v : M → E) x) = _
  calc g.inner x ((gradL2 g (c • u) : M → E) x) ((gradL2 g v : M → E) x)
      = g.inner x (c • (gradL2 g u : M → E) x) ((gradL2 g v : M → E) x) := by rw [hx]
    _ = (c • g.inner x ((gradL2 g u : M → E) x)) ((gradL2 g v : M → E) x) := by
          congr 1
          exact map_smul (g.inner x) c _
    _ = c * g.inner x ((gradL2 g u : M → E) x) ((gradL2 g v : M → E) x) := by
          rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.dirichletForm_integrand_smul_left
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.dirichletForm_integrand_smul_left target :: scope.openDecls } }

theorem dirichletForm_add_left (g : SmoothRiemannianMetric I M)
    (u₁ u₂ v : H1Intrinsic (I := I) (M := M) g) :
    dirichletForm (I := I) (M := M) g (u₁ + u₂) v =
      dirichletForm (I := I) (M := M) g u₁ v +
        dirichletForm (I := I) (M := M) g u₂ v := by
  have : _root_.MeasureTheory.IsFiniteMeasure (riemannianVolumeMeasure I M g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  unfold dirichletForm
  rw [_root_.MeasureTheory.integral_congr_ae (dirichletForm_integrand_add_left
    (I := I) (M := M) g u₁ u₂ v)]
  rw [_root_.MeasureTheory.integral_add ?_ ?_]
  · have hL2_u₁ := (u₁.2 : IsH1Pair (I := I) (M := M) g _ _).2.1
    have hL2_v := (v.2 : IsH1Pair (I := I) (M := M) g _ _).2.1
    refine MeasureTheory.Integrable.mono' (g := fun x =>
      Real.sqrt (g.inner x ((gradL2 g u₁ : M → E) x) ((gradL2 g u₁ : M → E) x)) *
        Real.sqrt (g.inner x ((gradL2 g v : M → E) x) ((gradL2 g v : M → E) x)))
      ?_ ?_ ?_
    · exact MemLp.integrable_mul hL2_u₁ hL2_v
    · have hpair_u₁ := (u₁.2 : IsH1Pair (I := I) (M := M) g _ _).2.2
      exact hpair_u₁ _ (Lp.aestronglyMeasurable (gradL2 g v))
    · refine Filter.Eventually.of_forall (fun x => ?_)
      have hCS := abs_metric_inner_le_sqrt_metric_quadratic (I := I) (M := M)
        g x ((gradL2 g u₁ : M → E) x) ((gradL2 g v : M → E) x)
      rwa [show ‖_‖ = |_| from Real.norm_eq_abs _]
  · have hL2_u₂ := (u₂.2 : IsH1Pair (I := I) (M := M) g _ _).2.1
    have hL2_v := (v.2 : IsH1Pair (I := I) (M := M) g _ _).2.1
    refine MeasureTheory.Integrable.mono' (g := fun x =>
      Real.sqrt (g.inner x ((gradL2 g u₂ : M → E) x) ((gradL2 g u₂ : M → E) x)) *
        Real.sqrt (g.inner x ((gradL2 g v : M → E) x) ((gradL2 g v : M → E) x)))
      ?_ ?_ ?_
    · exact MemLp.integrable_mul hL2_u₂ hL2_v
    · have hpair_u₂ := (u₂.2 : IsH1Pair (I := I) (M := M) g _ _).2.2
      exact hpair_u₂ _ (Lp.aestronglyMeasurable (gradL2 g v))
    · refine Filter.Eventually.of_forall (fun x => ?_)
      have hCS := abs_metric_inner_le_sqrt_metric_quadratic (I := I) (M := M)
        g x ((gradL2 g u₂ : M → E) x) ((gradL2 g v : M → E) x)
      rwa [show ‖_‖ = |_| from Real.norm_eq_abs _]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.dirichletForm_add_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.dirichletForm_add_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.dirichletForm_add_left ``Submission.DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.dirichletForm_add_left

theorem dirichletForm_smul_left (g : SmoothRiemannianMetric I M) (c : ℝ)
    (u v : H1Intrinsic (I := I) (M := M) g) :
    dirichletForm (I := I) (M := M) g (c • u) v =
      c * dirichletForm (I := I) (M := M) g u v := by
  unfold dirichletForm
  rw [_root_.MeasureTheory.integral_congr_ae (dirichletForm_integrand_smul_left
    (I := I) (M := M) g c u v)]
  rw [_root_.MeasureTheory.integral_const_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.dirichletForm_smul_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.dirichletForm_smul_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.dirichletForm_smul_left ``Submission.DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.dirichletForm_smul_left

theorem dirichletForm_add_right (g : SmoothRiemannianMetric I M)
    (u v₁ v₂ : H1Intrinsic (I := I) (M := M) g) :
    dirichletForm (I := I) (M := M) g u (v₁ + v₂) =
      dirichletForm (I := I) (M := M) g u v₁ +
        dirichletForm (I := I) (M := M) g u v₂ := by
  rw [dirichletForm_symm (I := I) (M := M) g u (v₁ + v₂),
    dirichletForm_add_left (I := I) (M := M) g v₁ v₂ u]
  rw [dirichletForm_symm (I := I) (M := M) g v₁ u,
    dirichletForm_symm (I := I) (M := M) g v₂ u]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.dirichletForm_add_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.dirichletForm_add_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.dirichletForm_add_right ``Submission.DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.dirichletForm_add_right

theorem dirichletForm_smul_right (g : SmoothRiemannianMetric I M) (c : ℝ)
    (u v : H1Intrinsic (I := I) (M := M) g) :
    dirichletForm (I := I) (M := M) g u (c • v) =
      c * dirichletForm (I := I) (M := M) g u v := by
  rw [dirichletForm_symm (I := I) (M := M) g u (c • v),
    dirichletForm_smul_left (I := I) (M := M) g c v u,
    dirichletForm_symm (I := I) (M := M) g v u]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.dirichletForm_smul_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.dirichletForm_smul_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.dirichletForm_smul_right ``Submission.DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.dirichletForm_smul_right

def dirichletFormLM (g : SmoothRiemannianMetric I M) :
    H1Intrinsic (I := I) (M := M) g →ₗ[ℝ]
      H1Intrinsic (I := I) (M := M) g →ₗ[ℝ] ℝ where
  toFun u :=
    { toFun := fun v => dirichletForm (I := I) (M := M) g u v
      map_add' := fun v₁ v₂ => dirichletForm_add_right (I := I) (M := M) g u v₁ v₂
      map_smul' := fun c v => by
        change dirichletForm (I := I) (M := M) g u (c • v) = _
        rw [dirichletForm_smul_right (I := I) (M := M) g c u v]
        rfl }
  map_add' u₁ u₂ := by
    ext v
    change dirichletForm (I := I) (M := M) g (u₁ + u₂) v = _
    rw [dirichletForm_add_left (I := I) (M := M) g u₁ u₂ v]
    rfl
  map_smul' c u := by
    ext v
    change dirichletForm (I := I) (M := M) g (c • u) v = _
    rw [dirichletForm_smul_left (I := I) (M := M) g c u v]
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.dirichletFormLM then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.dirichletFormLM"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.dirichletFormLM ``Submission.DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.dirichletFormLM

@[simp] lemma dirichletFormLM_apply (g : SmoothRiemannianMetric I M)
    (u v : H1Intrinsic (I := I) (M := M) g) :
    dirichletFormLM (I := I) (M := M) g u v =
      dirichletForm (I := I) (M := M) g u v := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.dirichletFormLM_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.dirichletFormLM_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.dirichletFormLM_apply ``Submission.DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.dirichletFormLM_apply

theorem shiftedForm_add_left (g : SmoothRiemannianMetric I M)
    (u₁ u₂ v : H1Intrinsic (I := I) (M := M) g) :
    shiftedForm (I := I) (M := M) g (u₁ + u₂) v =
      shiftedForm (I := I) (M := M) g u₁ v +
        shiftedForm (I := I) (M := M) g u₂ v := by
  have : _root_.MeasureTheory.IsFiniteMeasure (riemannianVolumeMeasure I M g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  unfold shiftedForm
  rw [dirichletForm_add_left (I := I) (M := M) g u₁ u₂ v]
  have h_to_add : (toLp (I := I) (M := M) g (u₁ + u₂) :
        _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure I M g)) =
      toLp (I := I) (M := M) g u₁ + toLp (I := I) (M := M) g u₂ :=
    map_add (toLp (I := I) (M := M) g) u₁ u₂
  have h_fn_add : (fun x : M => ((toLp (I := I) (M := M) g (u₁ + u₂) :
        _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure I M g)) : M → ℝ) x)
      =ᵐ[riemannianVolumeMeasure I M g]
      (fun x : M => ((toLp (I := I) (M := M) g u₁ :
        _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure I M g)) : M → ℝ) x +
        ((toLp (I := I) (M := M) g u₂ :
          Lp ℝ 2 (riemannianVolumeMeasure I M g)) : M → ℝ) x) := by
    rw [h_to_add]
    filter_upwards [Lp.coeFn_add (toLp (I := I) (M := M) g u₁)
      (toLp (I := I) (M := M) g u₂)] with x hx
    exact hx
  have h_int_eq : ∫ x : M, ((toLp (I := I) (M := M) g (u₁ + u₂) : M → ℝ) x) *
      ((toLp (I := I) (M := M) g v : M → ℝ) x)
      ∂(riemannianVolumeMeasure I M g) =
      ∫ x : M, ((toLp (I := I) (M := M) g u₁ : M → ℝ) x) *
        ((toLp (I := I) (M := M) g v : M → ℝ) x)
        ∂(riemannianVolumeMeasure I M g) +
      ∫ x : M, ((toLp (I := I) (M := M) g u₂ : M → ℝ) x) *
        ((toLp (I := I) (M := M) g v : M → ℝ) x)
        ∂(riemannianVolumeMeasure I M g) := by
    have h_ae : (fun x : M => ((toLp (I := I) (M := M) g (u₁ + u₂) : M → ℝ) x) *
        ((toLp (I := I) (M := M) g v : M → ℝ) x))
        =ᵐ[riemannianVolumeMeasure I M g]
        (fun x : M => ((toLp (I := I) (M := M) g u₁ : M → ℝ) x) *
          ((toLp (I := I) (M := M) g v : M → ℝ) x) +
          ((toLp (I := I) (M := M) g u₂ : M → ℝ) x) *
            ((toLp (I := I) (M := M) g v : M → ℝ) x)) := by
      filter_upwards [h_fn_add] with x hx
      rw [hx, add_mul]
    rw [_root_.MeasureTheory.integral_congr_ae h_ae]
    refine _root_.MeasureTheory.integral_add ?_ ?_
    · exact (MemLp.integrable_mul (Lp.memLp _) (Lp.memLp _) :
        Integrable (fun x : M => ((toLp (I := I) (M := M) g u₁ : M → ℝ) x) *
            ((toLp (I := I) (M := M) g v : M → ℝ) x)) _)
    · exact (MemLp.integrable_mul (Lp.memLp _) (Lp.memLp _) :
        Integrable (fun x : M => ((toLp (I := I) (M := M) g u₂ : M → ℝ) x) *
            ((toLp (I := I) (M := M) g v : M → ℝ) x)) _)
  rw [h_int_eq]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.shiftedForm_add_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.shiftedForm_add_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.shiftedForm_add_left ``Submission.DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.shiftedForm_add_left

theorem shiftedForm_smul_left (g : SmoothRiemannianMetric I M) (c : ℝ)
    (u v : H1Intrinsic (I := I) (M := M) g) :
    shiftedForm (I := I) (M := M) g (c • u) v =
      c * shiftedForm (I := I) (M := M) g u v := by
  unfold shiftedForm
  rw [dirichletForm_smul_left (I := I) (M := M) g c u v]
  have h_to_smul : (toLp (I := I) (M := M) g (c • u) :
        _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure I M g)) =
      c • toLp (I := I) (M := M) g u :=
    map_smul (toLp (I := I) (M := M) g) c u
  have h_fn_smul : (fun x : M => ((toLp (I := I) (M := M) g (c • u) :
        _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure I M g)) : M → ℝ) x)
      =ᵐ[riemannianVolumeMeasure I M g]
      (fun x : M => c * ((toLp (I := I) (M := M) g u :
        Lp ℝ 2 (riemannianVolumeMeasure I M g)) : M → ℝ) x) := by
    rw [h_to_smul]
    filter_upwards [Lp.coeFn_smul c (toLp (I := I) (M := M) g u)] with x hx
    simpa using hx
  have h_int_eq : ∫ x : M, ((toLp (I := I) (M := M) g (c • u) : M → ℝ) x) *
      ((toLp (I := I) (M := M) g v : M → ℝ) x)
      ∂(riemannianVolumeMeasure I M g) =
      c * ∫ x : M, ((toLp (I := I) (M := M) g u : M → ℝ) x) *
        ((toLp (I := I) (M := M) g v : M → ℝ) x)
        ∂(riemannianVolumeMeasure I M g) := by
    have h_ae : (fun x : M => ((toLp (I := I) (M := M) g (c • u) : M → ℝ) x) *
        ((toLp (I := I) (M := M) g v : M → ℝ) x))
        =ᵐ[riemannianVolumeMeasure I M g]
        (fun x : M => c * (((toLp (I := I) (M := M) g u : M → ℝ) x) *
          ((toLp (I := I) (M := M) g v : M → ℝ) x))) := by
      filter_upwards [h_fn_smul] with x hx
      rw [hx]; ring
    rw [_root_.MeasureTheory.integral_congr_ae h_ae, _root_.MeasureTheory.integral_const_mul]
  rw [h_int_eq]; ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.shiftedForm_smul_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.shiftedForm_smul_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.shiftedForm_smul_left ``Submission.DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.shiftedForm_smul_left

theorem shiftedForm_add_right (g : SmoothRiemannianMetric I M)
    (u v₁ v₂ : H1Intrinsic (I := I) (M := M) g) :
    shiftedForm (I := I) (M := M) g u (v₁ + v₂) =
      shiftedForm (I := I) (M := M) g u v₁ +
        shiftedForm (I := I) (M := M) g u v₂ := by
  rw [shiftedForm_symm (I := I) (M := M) g u (v₁ + v₂),
    shiftedForm_add_left (I := I) (M := M) g v₁ v₂ u]
  rw [shiftedForm_symm (I := I) (M := M) g v₁ u,
    shiftedForm_symm (I := I) (M := M) g v₂ u]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.shiftedForm_add_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.shiftedForm_add_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.shiftedForm_add_right ``Submission.DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.shiftedForm_add_right

theorem shiftedForm_smul_right (g : SmoothRiemannianMetric I M) (c : ℝ)
    (u v : H1Intrinsic (I := I) (M := M) g) :
    shiftedForm (I := I) (M := M) g u (c • v) =
      c * shiftedForm (I := I) (M := M) g u v := by
  rw [shiftedForm_symm (I := I) (M := M) g u (c • v),
    shiftedForm_smul_left (I := I) (M := M) g c v u,
    shiftedForm_symm (I := I) (M := M) g v u]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.shiftedForm_smul_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.shiftedForm_smul_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.shiftedForm_smul_right ``Submission.DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.shiftedForm_smul_right

def shiftedFormLM (g : SmoothRiemannianMetric I M) :
    H1Intrinsic (I := I) (M := M) g →ₗ[ℝ]
      H1Intrinsic (I := I) (M := M) g →ₗ[ℝ] ℝ where
  toFun u :=
    { toFun := fun v => shiftedForm (I := I) (M := M) g u v
      map_add' := fun v₁ v₂ => shiftedForm_add_right (I := I) (M := M) g u v₁ v₂
      map_smul' := fun c v => by
        change shiftedForm (I := I) (M := M) g u (c • v) = _
        rw [shiftedForm_smul_right (I := I) (M := M) g c u v]
        rfl }
  map_add' u₁ u₂ := by
    ext v
    change shiftedForm (I := I) (M := M) g (u₁ + u₂) v = _
    rw [shiftedForm_add_left (I := I) (M := M) g u₁ u₂ v]
    rfl
  map_smul' c u := by
    ext v
    change shiftedForm (I := I) (M := M) g (c • u) v = _
    rw [shiftedForm_smul_left (I := I) (M := M) g c u v]
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.shiftedFormLM then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.shiftedFormLM"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.shiftedFormLM ``Submission.DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.shiftedFormLM

@[simp] lemma shiftedFormLM_apply (g : SmoothRiemannianMetric I M)
    (u v : H1Intrinsic (I := I) (M := M) g) :
    shiftedFormLM (I := I) (M := M) g u v =
      shiftedForm (I := I) (M := M) g u v := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.shiftedFormLM_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.shiftedFormLM_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.shiftedFormLM_apply ``Submission.DifferentialGeometry.Analysis.Laplacian.H1Intrinsic.shiftedFormLM_apply

end H1Intrinsic

end Laplacian
end Analysis
end DifferentialGeometry

end
