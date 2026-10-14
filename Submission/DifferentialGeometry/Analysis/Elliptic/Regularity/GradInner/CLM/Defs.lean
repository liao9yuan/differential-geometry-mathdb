import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.LaplacianDomain.L2
import Submission.DifferentialGeometry.Geometry.Metric.PointwiseInner.Bounds
import Submission.DifferentialGeometry.Geometry.Operator.Gradient.NormSquared
import Mathlib.Analysis.Normed.Operator.Extend

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Operator


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem

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

variable [I.Boundaryless] [T2Space M] [CompactSpace M]

omit [NeZero (Module.finrank ℝ E)] [T2Space M]
  [CompactSpace M] in
lemma gradInnerSmooth_continuous
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯)
    (v : SmoothScalar g) :
    Continuous (fun x : M =>
      g.inner x (gradFun (I := I) g ρα x) (gradFun (I := I) g v.toFun x)) := by
  have h := TangentBundle.continuous_g_inner_of_smooth_sections (I := I) (M := M) g
    (gradG (I := I) g ρα) (gradG (I := I) g ⟨v.toFun, v.smooth⟩)
  refine h.congr ?_
  intro x
  change g.inner x (gradFun (I := I) g ρα x) (gradFun (I := I) g v.toFun x) =
    g.inner x (gradFun (I := I) g ρα x) (gradFun (I := I) g v.toFun x)
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.gradInnerSmooth_continuous then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.gradInnerSmooth_continuous"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.gradInnerSmooth_continuous ``Submission.DifferentialGeometry.Analysis.Laplacian.gradInnerSmooth_continuous

omit [NeZero (Module.finrank ℝ E)] in
lemma gradInnerSmooth_memLp_two
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯)
    (v : SmoothScalar g) :
    _root_.MeasureTheory.MemLp (fun x : M =>
        g.inner x (gradFun (I := I) g ρα x) (gradFun (I := I) g v.toFun x)) 2
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
  have : _root_.MeasureTheory.IsFiniteMeasureOnCompacts (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) g
  exact (gradInnerSmooth_continuous (I := I) (M := M) g ρα v).memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.gradInnerSmooth_memLp_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.gradInnerSmooth_memLp_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.gradInnerSmooth_memLp_two ``Submission.DifferentialGeometry.Analysis.Laplacian.gradInnerSmooth_memLp_two

noncomputable def gradInnerSmooth
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯)
    (v : SmoothScalar g) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  (gradInnerSmooth_memLp_two (I := I) (M := M) g ρα v).toLp _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.gradInnerSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.gradInnerSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.gradInnerSmooth ``Submission.DifferentialGeometry.Analysis.Laplacian.gradInnerSmooth

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma gradInnerSmooth_def
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯)
    (v : SmoothScalar g) :
    gradInnerSmooth (I := I) (M := M) g ρα v =
      (gradInnerSmooth_memLp_two (I := I) (M := M) g ρα v).toLp _ := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.gradInnerSmooth_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.gradInnerSmooth_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.gradInnerSmooth_def ``Submission.DifferentialGeometry.Analysis.Laplacian.gradInnerSmooth_def

omit [NeZero (Module.finrank ℝ E)] in
lemma gradInnerSmooth_coeFn
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯)
    (v : SmoothScalar g) :
    (gradInnerSmooth (I := I) (M := M) g ρα v :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      (fun x : M => g.inner x (gradFun (I := I) g ρα x)
        (gradFun (I := I) g v.toFun x)) :=
  MemLp.coeFn_toLp _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.gradInnerSmooth_coeFn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.gradInnerSmooth_coeFn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.gradInnerSmooth_coeFn ``Submission.DifferentialGeometry.Analysis.Laplacian.gradInnerSmooth_coeFn

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
  [CompactSpace M] in
lemma gradInnerSmooth_pt_add
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯)
    (v w : SmoothScalar g) (x : M) :
    g.inner x (gradFun (I := I) g ρα x)
        (gradFun (I := I) g (v + w).toFun x) =
      g.inner x (gradFun (I := I) g ρα x) (gradFun (I := I) g v.toFun x) +
        g.inner x (gradFun (I := I) g ρα x) (gradFun (I := I) g w.toFun x) := by
  have hgrad_add : gradFun (I := I) g (v + w).toFun x =
      gradFun (I := I) g v.toFun x + gradFun (I := I) g w.toFun x := by
    have hfun : (v + w).toFun = v.toFun + w.toFun := rfl
    rw [hfun]
    exact gradFun_add (I := I) g (v.smooth.mdifferentiable (by simp) x)
      (w.smooth.mdifferentiable (by simp) x)
  rw [hgrad_add, ContinuousLinearMap.map_add]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.gradInnerSmooth_pt_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.gradInnerSmooth_pt_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.gradInnerSmooth_pt_add ``Submission.DifferentialGeometry.Analysis.Laplacian.gradInnerSmooth_pt_add

omit [NeZero (Module.finrank ℝ E)] in
omit [T2Space M] [CompactSpace M] in
lemma gradInnerSmooth_pt_smul
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯)
    (c : ℝ) (v : SmoothScalar g) (x : M) :
    g.inner x (gradFun (I := I) g ρα x)
        (gradFun (I := I) g (c • v).toFun x) =
      c * g.inner x (gradFun (I := I) g ρα x) (gradFun (I := I) g v.toFun x) := by
  have hgrad_smul : gradFun (I := I) g (c • v).toFun x =
      c • gradFun (I := I) g v.toFun x := by
    have h := SmoothScalar.grad_g_smul_apply (I := I) (g := g) c v x
    change gradFun (I := I) g (c • v).toFun x =
      c • gradFun (I := I) g v.toFun x at h
    exact h
  rw [hgrad_smul]
  rw [ContinuousLinearMap.map_smul, smul_eq_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.gradInnerSmooth_pt_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.gradInnerSmooth_pt_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.gradInnerSmooth_pt_smul ``Submission.DifferentialGeometry.Analysis.Laplacian.gradInnerSmooth_pt_smul

omit [NeZero (Module.finrank ℝ E)] in
theorem gradInnerSmooth_add
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯)
    (v w : SmoothScalar g) :
    gradInnerSmooth (I := I) (M := M) g ρα (v + w) =
      gradInnerSmooth (I := I) (M := M) g ρα v +
        gradInnerSmooth (I := I) (M := M) g ρα w := by
  apply MeasureTheory.Lp.ext
  have h_sum_coe := MeasureTheory.Lp.coeFn_add
    (gradInnerSmooth (I := I) (M := M) g ρα v)
    (gradInnerSmooth (I := I) (M := M) g ρα w)
  have h_lhs := gradInnerSmooth_coeFn (I := I) (M := M) g ρα (v + w)
  have h_v := gradInnerSmooth_coeFn (I := I) (M := M) g ρα v
  have h_w := gradInnerSmooth_coeFn (I := I) (M := M) g ρα w
  refine h_lhs.trans ?_
  refine EventuallyEq.symm ?_
  filter_upwards [h_sum_coe, h_v, h_w] with x h_sum h_v_eq h_w_eq
  rw [h_sum, Pi.add_apply, h_v_eq, h_w_eq]
  exact (gradInnerSmooth_pt_add (I := I) (M := M) g ρα v w x).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.gradInnerSmooth_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.gradInnerSmooth_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.gradInnerSmooth_add ``Submission.DifferentialGeometry.Analysis.Laplacian.gradInnerSmooth_add

omit [NeZero (Module.finrank ℝ E)] in
theorem gradInnerSmooth_smul
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯)
    (c : ℝ) (v : SmoothScalar g) :
    gradInnerSmooth (I := I) (M := M) g ρα (c • v) =
      c • gradInnerSmooth (I := I) (M := M) g ρα v := by
  apply MeasureTheory.Lp.ext
  have h_smul_coe := MeasureTheory.Lp.coeFn_smul c
    (gradInnerSmooth (I := I) (M := M) g ρα v)
  have h_lhs := gradInnerSmooth_coeFn (I := I) (M := M) g ρα (c • v)
  have h_v := gradInnerSmooth_coeFn (I := I) (M := M) g ρα v
  refine h_lhs.trans ?_
  refine EventuallyEq.symm ?_
  filter_upwards [h_smul_coe, h_v] with x h_smul h_v_eq
  rw [h_smul, Pi.smul_apply, h_v_eq, smul_eq_mul]
  exact (gradInnerSmooth_pt_smul (I := I) (M := M) g ρα c v x).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.gradInnerSmooth_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.gradInnerSmooth_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.gradInnerSmooth_smul ``Submission.DifferentialGeometry.Analysis.Laplacian.gradInnerSmooth_smul

noncomputable def gradInnerSmoothLin
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯) :
    SmoothScalar g →ₗ[ℝ] _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) where
  toFun v := gradInnerSmooth (I := I) (M := M) g ρα v
  map_add' v w := gradInnerSmooth_add (I := I) (M := M) g ρα v w
  map_smul' c v := gradInnerSmooth_smul (I := I) (M := M) g ρα c v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.gradInnerSmoothLin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.gradInnerSmoothLin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.gradInnerSmoothLin ``Submission.DifferentialGeometry.Analysis.Laplacian.gradInnerSmoothLin

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma gradInnerSmoothLin_apply
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯)
    (v : SmoothScalar g) :
    gradInnerSmoothLin (I := I) (M := M) g ρα v =
      gradInnerSmooth (I := I) (M := M) g ρα v := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.gradInnerSmoothLin_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.gradInnerSmoothLin_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.gradInnerSmoothLin_apply ``Submission.DifferentialGeometry.Analysis.Laplacian.gradInnerSmoothLin_apply

omit [NeZero (Module.finrank ℝ E)] [T2Space M]
  in
private lemma exists_gradSupBound
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : M,
        Real.sqrt (g.inner x (gradFun (I := I) g ρα x)
          (gradFun (I := I) g ρα x)) ≤ C := by
  classical
  have hcont : Continuous (fun x : M => Real.sqrt
      (g.inner x (gradFun (I := I) g ρα x) (gradFun (I := I) g ρα x))) := by
    have h_in := gradInnerSmooth_continuous (I := I) (M := M) g ρα
      ⟨ρα, ρα.contMDiff⟩
    exact Real.continuous_sqrt.comp h_in
  have hCpt := (isCompact_univ (X := M)).image hcont
  obtain ⟨C₀, hC₀⟩ := hCpt.bddAbove
  refine ⟨max C₀ 0, le_max_right _ _, fun x => ?_⟩
  have hxC : Real.sqrt (g.inner x (gradFun (I := I) g ρα x)
      (gradFun (I := I) g ρα x)) ≤ C₀ :=
    hC₀ ⟨x, Set.mem_univ _, rfl⟩
  exact hxC.trans (le_max_left _ _)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.exists_gradSupBound
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.exists_gradSupBound target :: scope.openDecls } }

noncomputable def gradSupBound
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯) : ℝ :=
  Classical.choose (exists_gradSupBound (I := I) (M := M) g ρα)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.gradSupBound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.gradSupBound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.gradSupBound ``Submission.DifferentialGeometry.Analysis.Laplacian.gradSupBound

omit [NeZero (Module.finrank ℝ E)] [T2Space M]
  in
lemma gradSupBound_nonneg
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯) :
    0 ≤ gradSupBound (I := I) (M := M) g ρα :=
  (Classical.choose_spec
    (exists_gradSupBound (I := I) (M := M) g ρα)).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.gradSupBound_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.gradSupBound_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.gradSupBound_nonneg ``Submission.DifferentialGeometry.Analysis.Laplacian.gradSupBound_nonneg

omit [NeZero (Module.finrank ℝ E)] [T2Space M]
  in
lemma sqrt_inner_grad_self_le_gradSupBound
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯) (x : M) :
    Real.sqrt (g.inner x (gradFun (I := I) g ρα x)
        (gradFun (I := I) g ρα x)) ≤ gradSupBound (I := I) (M := M) g ρα :=
  (Classical.choose_spec
    (exists_gradSupBound (I := I) (M := M) g ρα)).2 x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.sqrt_inner_grad_self_le_gradSupBound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.sqrt_inner_grad_self_le_gradSupBound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.sqrt_inner_grad_self_le_gradSupBound ``Submission.DifferentialGeometry.Analysis.Laplacian.sqrt_inner_grad_self_le_gradSupBound

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
  [CompactSpace M] in
lemma abs_gradInner_le_sqrt_mul_sqrt
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯)
    (v : SmoothScalar g) (x : M) :
    |g.inner x (gradFun (I := I) g ρα x) (gradFun (I := I) g v.toFun x)| ≤
      Real.sqrt (g.inner x (gradFun (I := I) g ρα x)
          (gradFun (I := I) g ρα x)) *
      Real.sqrt (g.inner x (gradFun (I := I) g v.toFun x)
          (gradFun (I := I) g v.toFun x)) :=
  abs_metric_inner_le_sqrt_metric_quadratic (I := I) (M := M) g x _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.abs_gradInner_le_sqrt_mul_sqrt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.abs_gradInner_le_sqrt_mul_sqrt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.abs_gradInner_le_sqrt_mul_sqrt ``Submission.DifferentialGeometry.Analysis.Laplacian.abs_gradInner_le_sqrt_mul_sqrt

omit [NeZero (Module.finrank ℝ E)] [T2Space M] in
lemma abs_gradInner_le_gradSupBound_mul_sqrt
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯)
    (v : SmoothScalar g) (x : M) :
    |g.inner x (gradFun (I := I) g ρα x) (gradFun (I := I) g v.toFun x)| ≤
      gradSupBound (I := I) (M := M) g ρα *
        Real.sqrt (g.inner x (gradFun (I := I) g v.toFun x)
          (gradFun (I := I) g v.toFun x)) := by
  have h1 := abs_gradInner_le_sqrt_mul_sqrt (I := I) (M := M) g ρα v x
  have h2 := sqrt_inner_grad_self_le_gradSupBound (I := I) (M := M) g ρα x
  have h_sqrt_v_nn : 0 ≤ Real.sqrt (g.inner x (gradFun (I := I) g v.toFun x)
      (gradFun (I := I) g v.toFun x)) := Real.sqrt_nonneg _
  exact h1.trans (mul_le_mul_of_nonneg_right h2 h_sqrt_v_nn)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.abs_gradInner_le_gradSupBound_mul_sqrt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.abs_gradInner_le_gradSupBound_mul_sqrt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.abs_gradInner_le_gradSupBound_mul_sqrt ``Submission.DifferentialGeometry.Analysis.Laplacian.abs_gradInner_le_gradSupBound_mul_sqrt

omit [NeZero (Module.finrank ℝ E)] in
lemma norm_gradInnerSmooth_sq
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯)
    (v : SmoothScalar g) :
    ‖gradInnerSmooth (I := I) (M := M) g ρα v‖ ^ 2 =
      ∫ x, (g.inner x (gradFun (I := I) g ρα x)
            (gradFun (I := I) g v.toFun x)) ^ 2
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  have h := real_inner_self_eq_norm_sq (gradInnerSmooth (I := I) (M := M) g ρα v)
  rw [L2.inner_def (𝕜 := ℝ)] at h
  have hae_coe := gradInnerSmooth_coeFn (I := I) (M := M) g ρα v
  have hae : (fun a : M =>
        @_root_.Inner.inner ℝ _ _
          ((gradInnerSmooth (I := I) (M := M) g ρα v :
              _root_.MeasureTheory.Lp ℝ 2 _) a)
          ((gradInnerSmooth (I := I) (M := M) g ρα v :
              _root_.MeasureTheory.Lp ℝ 2 _) a)) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      (fun a : M =>
        (g.inner a (gradFun (I := I) g ρα a)
          (gradFun (I := I) g v.toFun a)) ^ 2) := by
    filter_upwards [hae_coe] with a hae_a
    rw [hae_a]
    rw [show (g.inner a (gradFun (I := I) g ρα a)
          (gradFun (I := I) g v.toFun a)) ^ 2 =
        g.inner a (gradFun (I := I) g ρα a)
          (gradFun (I := I) g v.toFun a) *
        g.inner a (gradFun (I := I) g ρα a)
          (gradFun (I := I) g v.toFun a) from sq _]
    rfl
  rw [_root_.MeasureTheory.integral_congr_ae hae] at h
  exact h.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.norm_gradInnerSmooth_sq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.norm_gradInnerSmooth_sq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.norm_gradInnerSmooth_sq ``Submission.DifferentialGeometry.Analysis.Laplacian.norm_gradInnerSmooth_sq

omit [NeZero (Module.finrank ℝ E)] [T2Space M] in
lemma sq_gradInner_le_gradSupBound_sq_mul
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯)
    (v : SmoothScalar g) (x : M) :
    (g.inner x (gradFun (I := I) g ρα x) (gradFun (I := I) g v.toFun x)) ^ 2 ≤
      gradSupBound (I := I) (M := M) g ρα ^ 2 *
        g.inner x (gradFun (I := I) g v.toFun x)
          (gradFun (I := I) g v.toFun x) := by
  have h_abs := abs_gradInner_le_gradSupBound_mul_sqrt (I := I) (M := M) g ρα v x
  have h_abs_nn : 0 ≤ |g.inner x (gradFun (I := I) g ρα x)
      (gradFun (I := I) g v.toFun x)| := abs_nonneg _
  have h_rhs_nn : 0 ≤ gradSupBound (I := I) (M := M) g ρα *
      Real.sqrt (g.inner x (gradFun (I := I) g v.toFun x)
        (gradFun (I := I) g v.toFun x)) :=
    mul_nonneg (gradSupBound_nonneg (I := I) (M := M) g ρα) (Real.sqrt_nonneg _)
  have h_sq := mul_self_le_mul_self h_abs_nn h_abs
  have h_lhs_sq : |g.inner x (gradFun (I := I) g ρα x)
        (gradFun (I := I) g v.toFun x)| *
      |g.inner x (gradFun (I := I) g ρα x)
        (gradFun (I := I) g v.toFun x)| =
      (g.inner x (gradFun (I := I) g ρα x)
        (gradFun (I := I) g v.toFun x)) ^ 2 := by
    rw [← sq, sq_abs]
  have h_v_self_nn : 0 ≤ g.inner x (gradFun (I := I) g v.toFun x)
      (gradFun (I := I) g v.toFun x) :=
    metric_inner_self_nonneg (I := I) (M := M) g x _
  have h_rhs_sq : (gradSupBound (I := I) (M := M) g ρα *
        Real.sqrt (g.inner x (gradFun (I := I) g v.toFun x)
          (gradFun (I := I) g v.toFun x))) *
      (gradSupBound (I := I) (M := M) g ρα *
        Real.sqrt (g.inner x (gradFun (I := I) g v.toFun x)
          (gradFun (I := I) g v.toFun x))) =
      gradSupBound (I := I) (M := M) g ρα ^ 2 *
        g.inner x (gradFun (I := I) g v.toFun x)
          (gradFun (I := I) g v.toFun x) := by
    rw [show (gradSupBound (I := I) (M := M) g ρα *
            Real.sqrt _) *
          (gradSupBound (I := I) (M := M) g ρα *
            Real.sqrt _) =
        gradSupBound (I := I) (M := M) g ρα ^ 2 *
          (Real.sqrt _ * Real.sqrt _) from by ring]
    rw [Real.mul_self_sqrt h_v_self_nn]
  rw [h_lhs_sq] at h_sq
  rw [h_rhs_sq] at h_sq
  exact h_sq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.sq_gradInner_le_gradSupBound_sq_mul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.sq_gradInner_le_gradSupBound_sq_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.sq_gradInner_le_gradSupBound_sq_mul ``Submission.DifferentialGeometry.Analysis.Laplacian.sq_gradInner_le_gradSupBound_sq_mul

omit [NeZero (Module.finrank ℝ E)] in
lemma norm_gradInnerSmooth_sq_le_gradSupBound_sq_mul_integral
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯)
    (v : SmoothScalar g) :
    ‖gradInnerSmooth (I := I) (M := M) g ρα v‖ ^ 2 ≤
      gradSupBound (I := I) (M := M) g ρα ^ 2 *
        (∫ x, g.inner x (gradFun (I := I) g v.toFun x)
            (gradFun (I := I) g v.toFun x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
  rw [norm_gradInnerSmooth_sq]
  have hpt : ∀ x : M,
      (g.inner x (gradFun (I := I) g ρα x)
          (gradFun (I := I) g v.toFun x)) ^ 2 ≤
      gradSupBound (I := I) (M := M) g ρα ^ 2 *
        g.inner x (gradFun (I := I) g v.toFun x)
          (gradFun (I := I) g v.toFun x) :=
    sq_gradInner_le_gradSupBound_sq_mul (I := I) (M := M) g ρα v
  have : _root_.MeasureTheory.IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  have hLHS_int : _root_.MeasureTheory.Integrable (fun x : M =>
      (g.inner x (gradFun (I := I) g ρα x)
        (gradFun (I := I) g v.toFun x)) ^ 2)
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    have hcont : Continuous (fun x : M =>
        (g.inner x (gradFun (I := I) g ρα x)
          (gradFun (I := I) g v.toFun x)) ^ 2) :=
      (gradInnerSmooth_continuous (I := I) (M := M) g ρα v).pow 2
    exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hRHS_int : _root_.MeasureTheory.Integrable (fun x : M =>
      g.inner x (gradFun (I := I) g v.toFun x)
        (gradFun (I := I) g v.toFun x))
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    have hcont : Continuous (fun x : M =>
        g.inner x (gradFun (I := I) g v.toFun x)
          (gradFun (I := I) g v.toFun x)) :=
      gradInnerSmooth_continuous (I := I) (M := M) g
        ⟨v.toFun, v.smooth⟩ v
    exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hRHS_const_int : _root_.MeasureTheory.Integrable (fun x : M =>
      gradSupBound (I := I) (M := M) g ρα ^ 2 *
        g.inner x (gradFun (I := I) g v.toFun x)
          (gradFun (I := I) g v.toFun x))
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    hRHS_int.const_mul _
  have h_int_le := _root_.MeasureTheory.integral_mono_ae hLHS_int hRHS_const_int
    (Filter.Eventually.of_forall hpt)
  rw [_root_.MeasureTheory.integral_const_mul] at h_int_le
  exact h_int_le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.norm_gradInnerSmooth_sq_le_gradSupBound_sq_mul_integral then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.norm_gradInnerSmooth_sq_le_gradSupBound_sq_mul_integral"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.norm_gradInnerSmooth_sq_le_gradSupBound_sq_mul_integral ``Submission.DifferentialGeometry.Analysis.Laplacian.norm_gradInnerSmooth_sq_le_gradSupBound_sq_mul_integral

omit [NeZero (Module.finrank ℝ E)] in
lemma integral_inner_grad_self_le_h1_norm_sq
    {g : SmoothRiemannianMetric I M} (v : SmoothScalar g) :
    (∫ x, g.inner x (gradFun (I := I) g v.toFun x)
        (gradFun (I := I) g v.toFun x)
      ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤
    ‖v‖ ^ 2 := by
  rw [SmoothScalar.norm_sq_eq_inner_self]
  unfold smoothScalarH1Inner
  have h_l2_nonneg :=
    SmoothScalar.integral_mul_self_nonneg (I := I) (M := M) (g := g) v
  have h_grad_eq :
      (∫ x, g.inner x ((gradG (I := I) g ⟨v.toFun, v.smooth⟩ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ((gradG (I := I) g ⟨v.toFun, v.smooth⟩ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      (∫ x, g.inner x (gradFun (I := I) g v.toFun x)
          (gradFun (I := I) g v.toFun x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
    refine _root_.MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro x
    rfl
  linarith [h_grad_eq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.integral_inner_grad_self_le_h1_norm_sq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.integral_inner_grad_self_le_h1_norm_sq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.integral_inner_grad_self_le_h1_norm_sq ``Submission.DifferentialGeometry.Analysis.Laplacian.integral_inner_grad_self_le_h1_norm_sq

omit [NeZero (Module.finrank ℝ E)] in
theorem norm_gradInnerSmooth_le
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯)
    (v : SmoothScalar g) :
    ‖gradInnerSmooth (I := I) (M := M) g ρα v‖ ≤
      gradSupBound (I := I) (M := M) g ρα * ‖v‖ := by
  have h_sq : ‖gradInnerSmooth (I := I) (M := M) g ρα v‖ ^ 2 ≤
      (gradSupBound (I := I) (M := M) g ρα * ‖v‖) ^ 2 := by
    calc ‖gradInnerSmooth (I := I) (M := M) g ρα v‖ ^ 2
        ≤ gradSupBound (I := I) (M := M) g ρα ^ 2 *
            (∫ x, g.inner x (gradFun (I := I) g v.toFun x)
                (gradFun (I := I) g v.toFun x)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g)) :=
          norm_gradInnerSmooth_sq_le_gradSupBound_sq_mul_integral
            (I := I) (M := M) g ρα v
      _ ≤ gradSupBound (I := I) (M := M) g ρα ^ 2 * ‖v‖ ^ 2 := by
          have h_int_le := integral_inner_grad_self_le_h1_norm_sq (g := g) v
          have h_C_sq_nn : 0 ≤ gradSupBound (I := I) (M := M) g ρα ^ 2 := sq_nonneg _
          exact mul_le_mul_of_nonneg_left h_int_le h_C_sq_nn
      _ = (gradSupBound (I := I) (M := M) g ρα * ‖v‖) ^ 2 := by ring
  have h_lhs_nn : 0 ≤ ‖gradInnerSmooth (I := I) (M := M) g ρα v‖ := norm_nonneg _
  have h_rhs_nn : 0 ≤ gradSupBound (I := I) (M := M) g ρα * ‖v‖ :=
    mul_nonneg (gradSupBound_nonneg (I := I) (M := M) g ρα) (norm_nonneg _)
  exact abs_le_of_sq_le_sq' h_sq h_rhs_nn |>.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.norm_gradInnerSmooth_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.norm_gradInnerSmooth_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.norm_gradInnerSmooth_le ``Submission.DifferentialGeometry.Analysis.Laplacian.norm_gradInnerSmooth_le

omit [NeZero (Module.finrank ℝ E)] in
theorem gradInnerSmooth_norm_le
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (v : SmoothScalar g),
      ‖gradInnerSmooth (I := I) (M := M) g ρα v‖ ≤ C * ‖v‖ :=
  ⟨gradSupBound (I := I) (M := M) g ρα,
    gradSupBound_nonneg (I := I) (M := M) g ρα,
    norm_gradInnerSmooth_le (I := I) (M := M) g ρα⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.gradInnerSmooth_norm_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.gradInnerSmooth_norm_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.gradInnerSmooth_norm_le ``Submission.DifferentialGeometry.Analysis.Laplacian.gradInnerSmooth_norm_le

noncomputable def gradInnerCLMOnSmooth
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯) :
    SmoothScalar g →L[ℝ] _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  (gradInnerSmoothLin (I := I) (M := M) g ρα).mkContinuous
    (gradSupBound (I := I) (M := M) g ρα)
    (fun v => norm_gradInnerSmooth_le (I := I) (M := M) g ρα v)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.gradInnerCLMOnSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.gradInnerCLMOnSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.gradInnerCLMOnSmooth ``Submission.DifferentialGeometry.Analysis.Laplacian.gradInnerCLMOnSmooth

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma gradInnerCLMOnSmooth_apply
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯)
    (v : SmoothScalar g) :
    gradInnerCLMOnSmooth (I := I) (M := M) g ρα v =
      gradInnerSmooth (I := I) (M := M) g ρα v := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.gradInnerCLMOnSmooth_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.gradInnerCLMOnSmooth_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.gradInnerCLMOnSmooth_apply ``Submission.DifferentialGeometry.Analysis.Laplacian.gradInnerCLMOnSmooth_apply

omit [NeZero (Module.finrank ℝ E)] in
private lemma denseRange_toComplL_smoothScalar
    (g : SmoothRiemannianMetric I M) :
    DenseRange (UniformSpace.Completion.toComplL :
      SmoothScalar g →L[ℝ] H1Compl g) := by
  rw [show (UniformSpace.Completion.toComplL : SmoothScalar g → H1Compl g) =
      ((↑) : SmoothScalar g → UniformSpace.Completion (SmoothScalar g)) from
      UniformSpace.Completion.coe_toComplL]
  exact UniformSpace.Completion.denseRange_coe

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.denseRange_toComplL_smoothScalar
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.denseRange_toComplL_smoothScalar target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
private lemma isUniformInducing_toComplL_smoothScalar
    (g : SmoothRiemannianMetric I M) :
    IsUniformInducing
      (UniformSpace.Completion.toComplL :
        SmoothScalar g →L[ℝ] H1Compl g) := by
  rw [show (UniformSpace.Completion.toComplL : SmoothScalar g → H1Compl g) =
      ((↑) : SmoothScalar g → UniformSpace.Completion (SmoothScalar g)) from
      UniformSpace.Completion.coe_toComplL]
  exact UniformSpace.Completion.isUniformInducing_coe (SmoothScalar g)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.isUniformInducing_toComplL_smoothScalar
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.isUniformInducing_toComplL_smoothScalar target :: scope.openDecls } }

noncomputable def gradInnerCLM
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯) :
    H1Compl g →L[ℝ] _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  ContinuousLinearMap.extend (gradInnerCLMOnSmooth (I := I) (M := M) g ρα)
    (UniformSpace.Completion.toComplL :
      SmoothScalar g →L[ℝ] H1Compl g)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.gradInnerCLM then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.gradInnerCLM"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.gradInnerCLM ``Submission.DifferentialGeometry.Analysis.Laplacian.gradInnerCLM

omit [NeZero (Module.finrank ℝ E)] in
theorem gradInnerCLM_smoothToH1Compl
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯)
    (v : SmoothScalar g) :
    gradInnerCLM (I := I) (M := M) g ρα
        (smoothToH1Compl (I := I) (M := M) g v) =
      gradInnerSmooth (I := I) (M := M) g ρα v := by
  unfold gradInnerCLM
  have h := ContinuousLinearMap.extend_eq
    (gradInnerCLMOnSmooth (I := I) (M := M) g ρα)
    (e := UniformSpace.Completion.toComplL)
    (denseRange_toComplL_smoothScalar (I := I) (M := M) g)
    (isUniformInducing_toComplL_smoothScalar (I := I) (M := M) g) v
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.gradInnerCLM_smoothToH1Compl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.gradInnerCLM_smoothToH1Compl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.gradInnerCLM_smoothToH1Compl ``Submission.DifferentialGeometry.Analysis.Laplacian.gradInnerCLM_smoothToH1Compl

end Laplacian
end Analysis
end DifferentialGeometry

end
