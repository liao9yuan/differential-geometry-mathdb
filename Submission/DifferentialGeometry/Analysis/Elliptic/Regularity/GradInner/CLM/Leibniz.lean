import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.GradInner.CLM.Defs
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.LaplacianDomain.Multiplication.H1Completion
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.SmoothScalar.MulLp
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.LaplacianDomain.L2
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.LaplacianDomain.Chart.VariationalData
import Submission.DifferentialGeometry.Geometry.Operator.Gradient.NormSquared

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Operator


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Topology _root_.Function
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators
  RealInnerProductSpace InnerProductSpace Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace GradInnerCLMLeibniz

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainChartData
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart

private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerCLMLeibniz.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerCLMLeibniz.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.GradInnerCLMLeibniz.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerCLMLeibniz.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerCLMLeibniz.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.GradInnerCLMLeibniz.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerCLMLeibniz.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerCLMLeibniz.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.GradInnerCLMLeibniz.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerCLMLeibniz.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerCLMLeibniz.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.GradInnerCLMLeibniz.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [I.Boundaryless] [T2Space M] [CompactSpace M]

noncomputable def gradRhoSqSmooth
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯) :
    C^∞⟮I, M; ℝ⟯ :=
  ⟨normGradSqFun (I := I) g (ρα : M → ℝ),
    normGradSqFun_contMDiff (I := I) g ρα.contMDiff⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerCLMLeibniz.gradRhoSqSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerCLMLeibniz.gradRhoSqSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerCLMLeibniz.gradRhoSqSmooth ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerCLMLeibniz.gradRhoSqSmooth

omit [T2Space M] [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma gradRhoSqSmooth_apply
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯) (x : M) :
    (gradRhoSqSmooth (I := I) (M := M) g ρα : M → ℝ) x =
      g.inner x (gradFun (I := I) g ρα x) (gradFun (I := I) g ρα x) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerCLMLeibniz.gradRhoSqSmooth_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerCLMLeibniz.gradRhoSqSmooth_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerCLMLeibniz.gradRhoSqSmooth_apply ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerCLMLeibniz.gradRhoSqSmooth_apply

omit [T2Space M] [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma gradInner_leibniz_pointwise
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯)
    (v : SmoothScalar g) (x : M) :
    (ρα : M → ℝ) x *
        g.inner x (gradFun (I := I) g ρα x)
          (gradFun (I := I) g v.toFun x) =
      g.inner x (gradFun (I := I) g ρα x)
          (gradFun (I := I) g
            (smoothScalarMulFun (I := I) (M := M) g ρα v).toFun x) -
        (gradRhoSqSmooth (I := I) (M := M) g ρα : M → ℝ) x * v.toFun x := by
  classical
  have h_grad := gradFun_smoothScalarMulFun (I := I) (M := M) g ρα v x
  rw [h_grad]
  rw [ContinuousLinearMap.map_add, ContinuousLinearMap.map_smul,
    ContinuousLinearMap.map_smul]
  simp only [smul_eq_mul, gradRhoSqSmooth_apply]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerCLMLeibniz.gradInner_leibniz_pointwise then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerCLMLeibniz.gradInner_leibniz_pointwise"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerCLMLeibniz.gradInner_leibniz_pointwise ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerCLMLeibniz.gradInner_leibniz_pointwise

omit [NeZero (Module.finrank ℝ E)] in
theorem gradInner_leibniz_smooth_Lp
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    smoothMulLp (I := I) (M := M) g ρα
        (gradInnerSmooth (I := I) (M := M) g ρα v) =
      gradInnerSmooth (I := I) (M := M) g ρα
          (smoothScalarMulFun (I := I) (M := M) g ρα v) -
        smoothMulLp (I := I) (M := M) g
          (gradRhoSqSmooth (I := I) (M := M) g ρα)
          (smoothToLp (I := I) (M := M) g v) := by
  classical
  apply MeasureTheory.Lp.ext
  have h_lhs_aeEq : (smoothMulLp (I := I) (M := M) g ρα
        (gradInnerSmooth (I := I) (M := M) g ρα v) :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      fun x : M => (ρα : M → ℝ) x *
        g.inner x (gradFun (I := I) g ρα x)
          (gradFun (I := I) g v.toFun x) := by
    have h1 := smoothMulLp_apply_coeFn (I := I) (M := M) g ρα
      (gradInnerSmooth (I := I) (M := M) g ρα v)
    have h2 := gradInnerSmooth_coeFn (I := I) (M := M) g ρα v
    refine h1.trans ?_
    filter_upwards [h2] with x hx
    rw [hx]
  have h_rhs1_aeEq : (gradInnerSmooth (I := I) (M := M) g ρα
        (smoothScalarMulFun (I := I) (M := M) g ρα v) :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      fun x : M =>
        g.inner x (gradFun (I := I) g ρα x)
          (gradFun (I := I) g
            (smoothScalarMulFun (I := I) (M := M) g ρα v).toFun x) :=
    gradInnerSmooth_coeFn (I := I) (M := M) g ρα
      (smoothScalarMulFun (I := I) (M := M) g ρα v)
  have h_rhs2_aeEq : (smoothMulLp (I := I) (M := M) g
        (gradRhoSqSmooth (I := I) (M := M) g ρα)
        (smoothToLp (I := I) (M := M) g v) :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      fun x : M =>
        (gradRhoSqSmooth (I := I) (M := M) g ρα : M → ℝ) x * v.toFun x := by
    have h1 := smoothMulLp_apply_coeFn (I := I) (M := M) g
      (gradRhoSqSmooth (I := I) (M := M) g ρα)
      (smoothToLp (I := I) (M := M) g v)
    have h2 : ((smoothToLp (I := I) (M := M) g v :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =ᵐ[
          riemannianVolumeMeasure (I := I) (M := M) g] v.toFun :=
      MeasureTheory.MemLp.coeFn_toLp v.memLp_two
    refine h1.trans ?_
    filter_upwards [h2] with x hx
    rw [hx]
  have h_diff_coe := MeasureTheory.Lp.coeFn_sub
    (gradInnerSmooth (I := I) (M := M) g ρα
      (smoothScalarMulFun (I := I) (M := M) g ρα v))
    (smoothMulLp (I := I) (M := M) g
      (gradRhoSqSmooth (I := I) (M := M) g ρα)
      (smoothToLp (I := I) (M := M) g v))
  refine h_lhs_aeEq.trans ?_
  refine EventuallyEq.symm ?_
  filter_upwards [h_diff_coe, h_rhs1_aeEq, h_rhs2_aeEq]
    with x hx_diff hx_rhs1 hx_rhs2
  rw [hx_diff, Pi.sub_apply, hx_rhs1, hx_rhs2]
  exact (gradInner_leibniz_pointwise (I := I) (M := M) g ρα v x).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerCLMLeibniz.gradInner_leibniz_smooth_Lp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerCLMLeibniz.gradInner_leibniz_smooth_Lp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerCLMLeibniz.gradInner_leibniz_smooth_Lp ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerCLMLeibniz.gradInner_leibniz_smooth_Lp

noncomputable def leibnizLhsCLM
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯) :
    H1Compl g →L[ℝ] _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  (smoothMulLp (I := I) (M := M) g ρα).comp
    (gradInnerCLM (I := I) (M := M) g ρα)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerCLMLeibniz.leibnizLhsCLM then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerCLMLeibniz.leibnizLhsCLM"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerCLMLeibniz.leibnizLhsCLM ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerCLMLeibniz.leibnizLhsCLM

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma leibnizLhsCLM_apply
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯) (u_h : H1Compl g) :
    leibnizLhsCLM (I := I) (M := M) g ρα u_h =
      smoothMulLp (I := I) (M := M) g ρα
        (gradInnerCLM (I := I) (M := M) g ρα u_h) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerCLMLeibniz.leibnizLhsCLM_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerCLMLeibniz.leibnizLhsCLM_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerCLMLeibniz.leibnizLhsCLM_apply ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerCLMLeibniz.leibnizLhsCLM_apply

noncomputable def leibnizRhsCLM
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯) :
    H1Compl g →L[ℝ] _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  (gradInnerCLM (I := I) (M := M) g ρα).comp
    (smoothMulH1Compl (I := I) (M := M) g ρα) -
  (smoothMulLp (I := I) (M := M) g
    (gradRhoSqSmooth (I := I) (M := M) g ρα)).comp
    (H1ComplToLp (I := I) (M := M) g)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerCLMLeibniz.leibnizRhsCLM then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerCLMLeibniz.leibnizRhsCLM"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerCLMLeibniz.leibnizRhsCLM ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerCLMLeibniz.leibnizRhsCLM

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma leibnizRhsCLM_apply
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯) (u_h : H1Compl g) :
    leibnizRhsCLM (I := I) (M := M) g ρα u_h =
      gradInnerCLM (I := I) (M := M) g ρα
          (smoothMulH1Compl (I := I) (M := M) g ρα u_h) -
        smoothMulLp (I := I) (M := M) g
          (gradRhoSqSmooth (I := I) (M := M) g ρα)
          (H1ComplToLp (I := I) (M := M) g u_h) := by
  unfold leibnizRhsCLM
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerCLMLeibniz.leibnizRhsCLM_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerCLMLeibniz.leibnizRhsCLM_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerCLMLeibniz.leibnizRhsCLM_apply ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerCLMLeibniz.leibnizRhsCLM_apply

omit [NeZero (Module.finrank ℝ E)] in
private lemma leibnizCLM_agree_on_smooth
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    leibnizLhsCLM (I := I) (M := M) g ρα
        (smoothToH1Compl (I := I) (M := M) g v) =
      leibnizRhsCLM (I := I) (M := M) g ρα
          (smoothToH1Compl (I := I) (M := M) g v) := by
  classical
  rw [leibnizLhsCLM_apply, leibnizRhsCLM_apply]
  rw [gradInnerCLM_smoothToH1Compl]
  rw [smoothMulH1Compl_smoothToH1Compl, gradInnerCLM_smoothToH1Compl,
    H1ComplToLp_smoothToH1Compl]
  exact gradInner_leibniz_smooth_Lp (I := I) (M := M) g ρα v

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerCLMLeibniz.leibnizCLM_agree_on_smooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.GradInnerCLMLeibniz.leibnizCLM_agree_on_smooth target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
private lemma denseRange_smoothToH1Compl_aux
    (g : SmoothRiemannianMetric I M) :
    DenseRange (smoothToH1Compl (I := I) (M := M) g) := by
  unfold smoothToH1Compl
  rw [show (UniformSpace.Completion.toComplL : SmoothScalar g → H1Compl g) =
      ((↑) : SmoothScalar g → UniformSpace.Completion (SmoothScalar g)) from
      UniformSpace.Completion.coe_toComplL]
  exact UniformSpace.Completion.denseRange_coe

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerCLMLeibniz.denseRange_smoothToH1Compl_aux
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.GradInnerCLMLeibniz.denseRange_smoothToH1Compl_aux target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
theorem leibnizLhsCLM_eq_leibnizRhsCLM
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯) :
    leibnizLhsCLM (I := I) (M := M) g ρα =
      leibnizRhsCLM (I := I) (M := M) g ρα := by
  classical
  apply ContinuousLinearMap.ext
  intro u_h
  have h_eq_on_range :
      ∀ v : SmoothScalar g,
        (leibnizLhsCLM (I := I) (M := M) g ρα :
            H1Compl g → _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
          (smoothToH1Compl (I := I) (M := M) g v) =
        (leibnizRhsCLM (I := I) (M := M) g ρα :
            H1Compl g → _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
          (smoothToH1Compl (I := I) (M := M) g v) :=
    leibnizCLM_agree_on_smooth (I := I) (M := M) g ρα
  have h_eq_funs : (leibnizLhsCLM (I := I) (M := M) g ρα :
        H1Compl g → _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) =
      (leibnizRhsCLM (I := I) (M := M) g ρα :
        H1Compl g → _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) := by
    apply DenseRange.equalizer (denseRange_smoothToH1Compl_aux
      (I := I) (M := M) g) (leibnizLhsCLM (I := I) (M := M) g ρα).continuous
      (leibnizRhsCLM (I := I) (M := M) g ρα).continuous
    funext v
    exact h_eq_on_range v
  exact congr_fun h_eq_funs u_h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerCLMLeibniz.leibnizLhsCLM_eq_leibnizRhsCLM then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerCLMLeibniz.leibnizLhsCLM_eq_leibnizRhsCLM"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerCLMLeibniz.leibnizLhsCLM_eq_leibnizRhsCLM ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerCLMLeibniz.leibnizLhsCLM_eq_leibnizRhsCLM

omit [NeZero (Module.finrank ℝ E)] in
theorem gradInner_leibniz_H1Compl
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯) (u_h : H1Compl g) :
    smoothMulLp (I := I) (M := M) g ρα
        (gradInnerCLM (I := I) (M := M) g ρα u_h) =
      gradInnerCLM (I := I) (M := M) g ρα
          (smoothMulH1Compl (I := I) (M := M) g ρα u_h) -
        smoothMulLp (I := I) (M := M) g
          (gradRhoSqSmooth (I := I) (M := M) g ρα)
          (H1ComplToLp (I := I) (M := M) g u_h) := by
  have h := congr_fun (congrArg DFunLike.coe
    (leibnizLhsCLM_eq_leibnizRhsCLM (I := I) (M := M) g ρα)) u_h
  rw [leibnizLhsCLM_apply, leibnizRhsCLM_apply] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerCLMLeibniz.gradInner_leibniz_H1Compl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerCLMLeibniz.gradInner_leibniz_H1Compl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerCLMLeibniz.gradInner_leibniz_H1Compl ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerCLMLeibniz.gradInner_leibniz_H1Compl

omit [NeZero (Module.finrank ℝ E)] in
lemma chartPushedRawLpFromLp_coeFn_sub
    (g : SmoothRiemannianMetric I M) (α : M)
    (F G : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    ((chartPushedRawLpFromLp (I := I) (M := M) g α (F - G) :
        Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) =ᵐ[
        (chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      (fun y => ((chartPushedRawLpFromLp (I := I) (M := M) g α F :
        Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y -
        ((chartPushedRawLpFromLp (I := I) (M := M) g α G :
          Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y) := by
  classical
  have h_FG_coeFn := chartPushedRawLpFromLp_coeFn (I := I) (M := M) g α (F - G)
  have h_F_coeFn := chartPushedRawLpFromLp_coeFn (I := I) (M := M) g α F
  have h_G_coeFn := chartPushedRawLpFromLp_coeFn (I := I) (M := M) g α G
  set diffFun : M → ℝ := fun x =>
    ((F : _root_.MeasureTheory.Lp ℝ 2 _) : M → ℝ) x - ((G : _root_.MeasureTheory.Lp ℝ 2 _) : M → ℝ) x with hdiffFun_def
  have h_sub_coe : ((F - G : _root_.MeasureTheory.Lp ℝ 2 _) : M → ℝ) =ᵐ[
      riemannianVolumeMeasure (I := I) (M := M) g] diffFun :=
    MeasureTheory.Lp.coeFn_sub F G
  have h_FG_meas : Measurable ((F - G : _root_.MeasureTheory.Lp ℝ 2 _) : M → ℝ) :=
    (Lp.stronglyMeasurable (F - G)).measurable
  have hF_meas : Measurable ((F : _root_.MeasureTheory.Lp ℝ 2 _) : M → ℝ) :=
    (Lp.stronglyMeasurable F).measurable
  have hG_meas : Measurable ((G : _root_.MeasureTheory.Lp ℝ 2 _) : M → ℝ) :=
    (Lp.stronglyMeasurable G).measurable
  have hdiff_meas : Measurable diffFun := hF_meas.sub hG_meas
  have h_chartPushedRaw_FG :
      chartPushedRaw (I := I) α ((F - G : _root_.MeasureTheory.Lp ℝ 2 _) : M → ℝ) =ᵐ[
        (chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      chartPushedRaw (I := I) α diffFun :=
    chartPushedRaw_aeEq_of_aeEq (I := I) (M := M) g α
      h_FG_meas hdiff_meas h_sub_coe
  have h_chartPushedRaw_diff_pointwise :
      ∀ y : EuclN,
        chartPushedRaw (I := I) α diffFun y =
          chartPushedRaw (I := I) α ((F : _root_.MeasureTheory.Lp ℝ 2 _) : M → ℝ) y -
            chartPushedRaw (I := I) α ((G : _root_.MeasureTheory.Lp ℝ 2 _) : M → ℝ) y := by
    intro y
    by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
    · rw [chartPushedRaw_apply_of_mem (I := I) (M := M) (α := α) diffFun hy,
        chartPushedRaw_apply_of_mem (I := I) (M := M) (α := α)
          ((F : _root_.MeasureTheory.Lp ℝ 2 _) : M → ℝ) hy,
        chartPushedRaw_apply_of_mem (I := I) (M := M) (α := α)
          ((G : _root_.MeasureTheory.Lp ℝ 2 _) : M → ℝ) hy]
    · rw [chartPushedRaw_apply_of_notMem (I := I) (M := M) (α := α) diffFun hy,
        chartPushedRaw_apply_of_notMem (I := I) (M := M) (α := α)
          ((F : _root_.MeasureTheory.Lp ℝ 2 _) : M → ℝ) hy,
        chartPushedRaw_apply_of_notMem (I := I) (M := M) (α := α)
          ((G : _root_.MeasureTheory.Lp ℝ 2 _) : M → ℝ) hy]
      ring
  filter_upwards [h_FG_coeFn, h_F_coeFn, h_G_coeFn, h_chartPushedRaw_FG]
    with y hy_FG hy_F hy_G hy_chart
  rw [hy_FG, hy_chart, h_chartPushedRaw_diff_pointwise y]
  rw [← hy_F, ← hy_G]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerCLMLeibniz.chartPushedRawLpFromLp_coeFn_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerCLMLeibniz.chartPushedRawLpFromLp_coeFn_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerCLMLeibniz.chartPushedRawLpFromLp_coeFn_sub ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerCLMLeibniz.chartPushedRawLpFromLp_coeFn_sub

omit [NeZero (Module.finrank ℝ E)] in
private lemma chartPushedRawLpFromLp_smoothMulLp_coeFn
    (g : SmoothRiemannianMetric I M) (_h : NeZero (Module.finrank ℝ E))
    (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    (F : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    ((chartPushedRawLpFromLp (I := I) (M := M) g α
        (smoothMulLp (I := I) (M := M) g φ F) :
        Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) =ᵐ[
        (chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      (fun y =>
        chartPushedRaw (I := I) α (fun x : M => (φ : M → ℝ) x) y *
        ((chartPushedRawLpFromLp (I := I) (M := M) g α F :
          Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y) := by
  let := _h
  classical
  have h_smoothMulLp_coeFn := chartPushedRawLpFromLp_coeFn (I := I) (M := M) g α
    (smoothMulLp (I := I) (M := M) g φ F)
  have h_F_coeFn := chartPushedRawLpFromLp_coeFn (I := I) (M := M) g α F
  have h_M_aeEq : ((smoothMulLp (I := I) (M := M) g φ F :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      (fun x : M => (φ : M → ℝ) x * ((F : _root_.MeasureTheory.Lp ℝ 2 _) : M → ℝ) x) :=
    smoothMulLp_apply_coeFn (I := I) (M := M) g φ F
  have hF_meas : Measurable ((F : _root_.MeasureTheory.Lp ℝ 2 _) : M → ℝ) :=
    (Lp.stronglyMeasurable F).measurable
  have h_smoothMulLp_meas :
      Measurable ((smoothMulLp (I := I) (M := M) g φ F :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) :=
    (Lp.stronglyMeasurable _).measurable
  have h_prod_meas :
      Measurable (fun x : M => (φ : M → ℝ) x * ((F : _root_.MeasureTheory.Lp ℝ 2 _) : M → ℝ) x) :=
    φ.contMDiff.continuous.measurable.mul hF_meas
  have h_chartPushedRaw_aeEq :
      chartPushedRaw (I := I) α
        ((smoothMulLp (I := I) (M := M) g φ F :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =ᵐ[
        (chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      chartPushedRaw (I := I) α
        (fun x : M => (φ : M → ℝ) x * ((F : _root_.MeasureTheory.Lp ℝ 2 _) : M → ℝ) x) :=
    chartPushedRaw_aeEq_of_aeEq (I := I) (M := M) g α
      h_smoothMulLp_meas h_prod_meas h_M_aeEq
  have h_pointwise : ∀ y : EuclN,
      chartPushedRaw (I := I) α
          (fun x : M => (φ : M → ℝ) x * ((F : _root_.MeasureTheory.Lp ℝ 2 _) : M → ℝ) x) y =
        chartPushedRaw (I := I) α (fun x : M => (φ : M → ℝ) x) y *
          chartPushedRaw (I := I) α ((F : _root_.MeasureTheory.Lp ℝ 2 _) : M → ℝ) y := by
    intro y
    by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
    · rw [chartPushedRaw_apply_of_mem (I := I) (M := M) (α := α) _ hy,
        chartPushedRaw_apply_of_mem (I := I) (M := M) (α := α)
          (fun x : M => (φ : M → ℝ) x) hy,
        chartPushedRaw_apply_of_mem (I := I) (M := M) (α := α)
          ((F : _root_.MeasureTheory.Lp ℝ 2 _) : M → ℝ) hy]
    · rw [chartPushedRaw_apply_of_notMem (I := I) (M := M) (α := α) _ hy,
        chartPushedRaw_apply_of_notMem (I := I) (M := M) (α := α)
          (fun x : M => (φ : M → ℝ) x) hy,
        chartPushedRaw_apply_of_notMem (I := I) (M := M) (α := α)
          ((F : _root_.MeasureTheory.Lp ℝ 2 _) : M → ℝ) hy]
      ring
  filter_upwards [h_smoothMulLp_coeFn, h_F_coeFn, h_chartPushedRaw_aeEq]
    with y hy_smoothMul hy_F hy_chart
  rw [hy_smoothMul, hy_chart, h_pointwise y]
  rw [← hy_F]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerCLMLeibniz.chartPushedRawLpFromLp_smoothMulLp_coeFn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.GradInnerCLMLeibniz.chartPushedRawLpFromLp_smoothMulLp_coeFn target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
theorem chartPushedRawLpFromLp_gradInner_leibniz_H1Compl
    (g : SmoothRiemannianMetric I M) (_h : NeZero (Module.finrank ℝ E))
    (α : M) (ρα : C^∞⟮I, M; ℝ⟯)
    (u_h : H1Compl g) :
    ((chartPushedRawLpFromLp (I := I) (M := M) g α
        (smoothMulLp (I := I) (M := M) g ρα
          (gradInnerCLM (I := I) (M := M) g ρα u_h)) :
        Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) =ᵐ[
        (chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      (fun y =>
        ((chartPushedRawLpFromLp (I := I) (M := M) g α
          (gradInnerCLM (I := I) (M := M) g ρα
            (smoothMulH1Compl (I := I) (M := M) g ρα u_h)) :
          Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y -
        chartPushedRaw (I := I) α
          (fun x : M => (gradRhoSqSmooth (I := I) (M := M) g ρα : M → ℝ) x) y *
        ((chartPushedRawLpFromLp (I := I) (M := M) g α
          (H1ComplToLp (I := I) (M := M) g u_h) :
          Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y) := by
  let := _h
  classical
  have h_M_eq := gradInner_leibniz_H1Compl (I := I) (M := M) g ρα u_h
  rw [h_M_eq]
  have h_sub_chartPushed := chartPushedRawLpFromLp_coeFn_sub
    (I := I) (M := M) g α
    (gradInnerCLM (I := I) (M := M) g ρα
      (smoothMulH1Compl (I := I) (M := M) g ρα u_h))
    (smoothMulLp (I := I) (M := M) g
      (gradRhoSqSmooth (I := I) (M := M) g ρα)
      (H1ComplToLp (I := I) (M := M) g u_h))
  have h_smoothMul_chartPushed := chartPushedRawLpFromLp_smoothMulLp_coeFn
    (I := I) (M := M) g inferInstance α (gradRhoSqSmooth (I := I) (M := M) g ρα)
    (H1ComplToLp (I := I) (M := M) g u_h)
  filter_upwards [h_sub_chartPushed, h_smoothMul_chartPushed]
    with y hy_sub hy_smooth
  rw [hy_sub, hy_smooth]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerCLMLeibniz.chartPushedRawLpFromLp_gradInner_leibniz_H1Compl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerCLMLeibniz.chartPushedRawLpFromLp_gradInner_leibniz_H1Compl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerCLMLeibniz.chartPushedRawLpFromLp_gradInner_leibniz_H1Compl ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerCLMLeibniz.chartPushedRawLpFromLp_gradInner_leibniz_H1Compl

omit [NeZero (Module.finrank ℝ E)] in
theorem chartPushedRawLpFromLp_gradInner_leibniz_smoothToH1Compl
    (g : SmoothRiemannianMetric I M) (_h : NeZero (Module.finrank ℝ E))
    (α : M) (ρα : C^∞⟮I, M; ℝ⟯)
    (v : SmoothScalar g) :
    ((chartPushedRawLpFromLp (I := I) (M := M) g α
        (smoothMulLp (I := I) (M := M) g ρα
          (gradInnerSmooth (I := I) (M := M) g ρα v)) :
        Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) =ᵐ[
        (chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      (fun y =>
        ((chartPushedRawLpFromLp (I := I) (M := M) g α
          (gradInnerSmooth (I := I) (M := M) g ρα
            (smoothScalarMulFun (I := I) (M := M) g ρα v)) :
          Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y -
        chartPushedRaw (I := I) α
          (fun x : M => (gradRhoSqSmooth (I := I) (M := M) g ρα : M → ℝ) x) y *
        ((chartPushedRawLpFromLp (I := I) (M := M) g α
          (smoothToLp (I := I) (M := M) g v) :
          Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y) := by
  let := _h
  classical
  have h_gen := chartPushedRawLpFromLp_gradInner_leibniz_H1Compl
    (I := I) (M := M) g inferInstance α ρα
      (smoothToH1Compl (I := I) (M := M) g v)
  have h_grad_smooth : gradInnerCLM (I := I) (M := M) g ρα
        (smoothToH1Compl (I := I) (M := M) g v) =
      gradInnerSmooth (I := I) (M := M) g ρα v :=
    gradInnerCLM_smoothToH1Compl (I := I) (M := M) g ρα v
  rw [h_grad_smooth] at h_gen
  have h_smoothMul_smooth : smoothMulH1Compl (I := I) (M := M) g ρα
        (smoothToH1Compl (I := I) (M := M) g v) =
      smoothToH1Compl (I := I) (M := M) g
        (smoothScalarMulFun (I := I) (M := M) g ρα v) :=
    smoothMulH1Compl_smoothToH1Compl (I := I) (M := M) g ρα v
  rw [h_smoothMul_smooth] at h_gen
  have h_grad_smooth_2 : gradInnerCLM (I := I) (M := M) g ρα
        (smoothToH1Compl (I := I) (M := M) g
          (smoothScalarMulFun (I := I) (M := M) g ρα v)) =
      gradInnerSmooth (I := I) (M := M) g ρα
        (smoothScalarMulFun (I := I) (M := M) g ρα v) :=
    gradInnerCLM_smoothToH1Compl (I := I) (M := M) g ρα _
  rw [h_grad_smooth_2] at h_gen
  have h_H1ComplToLp_smooth : H1ComplToLp (I := I) (M := M) g
        (smoothToH1Compl (I := I) (M := M) g v) =
      smoothToLp (I := I) (M := M) g v :=
    H1ComplToLp_smoothToH1Compl (I := I) (M := M) g v
  rw [h_H1ComplToLp_smooth] at h_gen
  exact h_gen

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerCLMLeibniz.chartPushedRawLpFromLp_gradInner_leibniz_smoothToH1Compl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerCLMLeibniz.chartPushedRawLpFromLp_gradInner_leibniz_smoothToH1Compl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerCLMLeibniz.chartPushedRawLpFromLp_gradInner_leibniz_smoothToH1Compl ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerCLMLeibniz.chartPushedRawLpFromLp_gradInner_leibniz_smoothToH1Compl

end GradInnerCLMLeibniz
end Laplacian
end Analysis
end DifferentialGeometry

end
