import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.GradInner.Laplacian.ChristoffelDischarge
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.GradInner.Laplacian.DensityExtension

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.MeasureTheory _root_.Filter _root_.Topology _root_.Function
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.Matrix _root_.InnerProductSpace _root_.BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace GradInnerVariationalIntegralForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem

open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLpIdentity
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianRhs
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaChristoffelDischarge
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.HessianBridgeSmoothLp
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDomain
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmooth
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmoothCanonical
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDensityExtension

private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerVariationalIntegralForm.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerVariationalIntegralForm.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.GradInnerVariationalIntegralForm.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerVariationalIntegralForm.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerVariationalIntegralForm.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.GradInnerVariationalIntegralForm.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerVariationalIntegralForm.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerVariationalIntegralForm.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.GradInnerVariationalIntegralForm.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerVariationalIntegralForm.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerVariationalIntegralForm.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.GradInnerVariationalIntegralForm.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lpInner_H1ComplToLp_oneSubLap_eq_lpInner_smooth_preimage
    (g : SmoothRiemannianMetric I M)
    {w_lift : H1Compl (I := I) (M := M) g}
    (hw_lift : w_lift ∈ laplacianDomain (I := I) (M := M) g)
    (w : SmoothScalar g) :
    ⟪H1ComplToLp (I := I) (M := M) g w_lift,
        smoothToLp (I := I) (M := M) g w.oneSubLapClassical⟫_ℝ =
      ⟪smoothToLp (I := I) (M := M) g w,
        laplacianDomain.preimage (I := I) (M := M) g ⟨w_lift, hw_lift⟩⟫_ℝ := by
  classical
  have h_LHS : ⟪H1ComplToLp (I := I) (M := M) g w_lift,
        smoothToLp (I := I) (M := M) g w.oneSubLapClassical⟫_ℝ =
      ⟪w_lift, smoothToH1Compl (I := I) (M := M) g w⟫_ℝ := by
    rw [show ⟪w_lift, smoothToH1Compl (I := I) (M := M) g w⟫_ℝ =
        ⟪smoothToH1Compl (I := I) (M := M) g w, w_lift⟫_ℝ from
      real_inner_comm _ _]
    rw [show smoothToH1Compl (I := I) (M := M) g w =
        resolvent (I := I) (M := M) g
          (smoothToLp (I := I) (M := M) g w.oneSubLapClassical) from
      smoothToH1Compl_eq_resolvent_oneSubLap (I := I) (M := M) w]
    exact (resolvent_inner_eq_lpFunctional (I := I) (M := M) g
      (smoothToLp (I := I) (M := M) g w.oneSubLapClassical) w_lift).symm
  have h_RHS : ⟪smoothToLp (I := I) (M := M) g w,
        laplacianDomain.preimage (I := I) (M := M) g ⟨w_lift, hw_lift⟩⟫_ℝ =
      ⟪w_lift, smoothToH1Compl (I := I) (M := M) g w⟫_ℝ := by
    rw [show smoothToLp (I := I) (M := M) g w =
        H1ComplToLp (I := I) (M := M) g
          (smoothToH1Compl (I := I) (M := M) g w) from
      (H1ComplToLp_smoothToH1Compl (I := I) (M := M) g w).symm]
    have h_var := (resolvent_inner_eq_lpFunctional (I := I) (M := M) g
      (laplacianDomain.preimage (I := I) (M := M) g ⟨w_lift, hw_lift⟩)
      (smoothToH1Compl (I := I) (M := M) g w)).symm
    rw [h_var]
    congr 1
    exact resolvent_laplacianDomain_preimage_eq (I := I) (M := M) g ⟨w_lift, hw_lift⟩
  rw [h_LHS, h_RHS]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerVariationalIntegralForm.lpInner_H1ComplToLp_oneSubLap_eq_lpInner_smooth_preimage then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerVariationalIntegralForm.lpInner_H1ComplToLp_oneSubLap_eq_lpInner_smooth_preimage"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerVariationalIntegralForm.lpInner_H1ComplToLp_oneSubLap_eq_lpInner_smooth_preimage ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerVariationalIntegralForm.lpInner_H1ComplToLp_oneSubLap_eq_lpInner_smooth_preimage

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lpInner_gradInner_smooth_oneSubLap_eq_lpInner_smooth_preimage
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    {w_lift : H1Compl (I := I) (M := M) g}
    (hw_lift : w_lift ∈ laplacianDomain (I := I) (M := M) g)
    (h_witness : H1ComplToLp (I := I) (M := M) g w_lift =
      gradInnerCLM (I := I) (M := M) g φ u_h)
    (w : SmoothScalar g) :
    ⟪gradInnerCLM (I := I) (M := M) g φ u_h,
        smoothToLp (I := I) (M := M) g w.oneSubLapClassical⟫_ℝ =
      ⟪smoothToLp (I := I) (M := M) g w,
        laplacianDomain.preimage (I := I) (M := M) g ⟨w_lift, hw_lift⟩⟫_ℝ := by
  rw [← h_witness]
  exact lpInner_H1ComplToLp_oneSubLap_eq_lpInner_smooth_preimage
    (I := I) (M := M) g hw_lift w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerVariationalIntegralForm.lpInner_gradInner_smooth_oneSubLap_eq_lpInner_smooth_preimage then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerVariationalIntegralForm.lpInner_gradInner_smooth_oneSubLap_eq_lpInner_smooth_preimage"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerVariationalIntegralForm.lpInner_gradInner_smooth_oneSubLap_eq_lpInner_smooth_preimage ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerVariationalIntegralForm.lpInner_gradInner_smooth_oneSubLap_eq_lpInner_smooth_preimage

omit [NeZero (Module.finrank ℝ E)] in
theorem integral_H1ComplToLp_oneSubLap_eq_integral_preimage_smooth
    (g : SmoothRiemannianMetric I M)
    {w_lift : H1Compl (I := I) (M := M) g}
    (hw_lift : w_lift ∈ laplacianDomain (I := I) (M := M) g)
    (w : SmoothScalar g) :
    ∫ x, ((H1ComplToLp (I := I) (M := M) g w_lift :
              Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x *
            (w.toFun x - ΔG (I := I) g ⟨w.toFun, w.smooth⟩ x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, w.toFun x *
            ((laplacianDomain.preimage (I := I) (M := M) g
                ⟨w_lift, hw_lift⟩ :
                Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  have h_abs := lpInner_H1ComplToLp_oneSubLap_eq_lpInner_smooth_preimage
    (I := I) (M := M) g hw_lift w
  rw [L2.inner_def, L2.inner_def] at h_abs
  have h_LHS_coe :
      ((smoothToLp (I := I) (M := M) g w.oneSubLapClassical :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =ᵐ[
          riemannianVolumeMeasure (I := I) (M := M) g]
        (fun x : M => w.toFun x - ΔG (I := I) g ⟨w.toFun, w.smooth⟩ x) := by
    have h := MemLp.coeFn_toLp w.oneSubLapClassical.memLp_two
    filter_upwards [h] with x hx
    change ((w.oneSubLapClassical.memLp_two.toLp _ :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x = _
    rw [hx]
    rfl
  have h_RHS_coe :
      ((smoothToLp (I := I) (M := M) g w :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =ᵐ[
          riemannianVolumeMeasure (I := I) (M := M) g]
        (fun x : M => w.toFun x) := MemLp.coeFn_toLp w.memLp_two
  have h_LHS_integral :
      ∫ a, @_root_.Inner.inner ℝ ℝ _
            (((H1ComplToLp (I := I) (M := M) g w_lift :
                Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
                M → ℝ) a)
            (((smoothToLp (I := I) (M := M) g w.oneSubLapClassical :
                Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
                M → ℝ) a)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        ∫ x, ((H1ComplToLp (I := I) (M := M) g w_lift :
              Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x *
              (w.toFun x - ΔG (I := I) g ⟨w.toFun, w.smooth⟩ x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    refine _root_.MeasureTheory.integral_congr_ae ?_
    filter_upwards [h_LHS_coe] with x hx
    have h_inner_apply :
        @_root_.Inner.inner ℝ ℝ _
            (((H1ComplToLp (I := I) (M := M) g w_lift :
                Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
                M → ℝ) x)
            (((smoothToLp (I := I) (M := M) g w.oneSubLapClassical :
                Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
                M → ℝ) x) =
          ((smoothToLp (I := I) (M := M) g w.oneSubLapClassical :
                Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x *
            ((H1ComplToLp (I := I) (M := M) g w_lift :
                Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x := rfl
    rw [h_inner_apply]
    change _ * _ = _ * _
    rw [hx]
    ring
  have h_RHS_integral :
      ∫ a, @_root_.Inner.inner ℝ ℝ _
            (((smoothToLp (I := I) (M := M) g w :
                Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
                M → ℝ) a)
            (((laplacianDomain.preimage (I := I) (M := M) g
                ⟨w_lift, hw_lift⟩ :
                Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
                M → ℝ) a)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        ∫ x, w.toFun x *
              ((laplacianDomain.preimage (I := I) (M := M) g
                  ⟨w_lift, hw_lift⟩ :
                  Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    refine _root_.MeasureTheory.integral_congr_ae ?_
    filter_upwards [h_RHS_coe] with x hx
    have h_inner_apply :
        @_root_.Inner.inner ℝ ℝ _
            (((smoothToLp (I := I) (M := M) g w :
                Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
                M → ℝ) x)
            (((laplacianDomain.preimage (I := I) (M := M) g
                ⟨w_lift, hw_lift⟩ :
                Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
                M → ℝ) x) =
          ((laplacianDomain.preimage (I := I) (M := M) g
                ⟨w_lift, hw_lift⟩ :
                Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x *
            ((smoothToLp (I := I) (M := M) g w :
                Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x := rfl
    rw [h_inner_apply]
    change _ * _ = _ * _
    rw [hx]
    ring
  rw [← h_LHS_integral, ← h_RHS_integral]
  exact h_abs

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerVariationalIntegralForm.integral_H1ComplToLp_oneSubLap_eq_integral_preimage_smooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerVariationalIntegralForm.integral_H1ComplToLp_oneSubLap_eq_integral_preimage_smooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerVariationalIntegralForm.integral_H1ComplToLp_oneSubLap_eq_integral_preimage_smooth ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerVariationalIntegralForm.integral_H1ComplToLp_oneSubLap_eq_integral_preimage_smooth

omit [NeZero (Module.finrank ℝ E)] in
theorem integral_gradInner_oneSubLap_smooth_eq_integral_preimage_smooth
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    {w_lift : H1Compl (I := I) (M := M) g}
    (hw_lift : w_lift ∈ laplacianDomain (I := I) (M := M) g)
    (h_witness : H1ComplToLp (I := I) (M := M) g w_lift =
      gradInnerCLM (I := I) (M := M) g φ u_h)
    (w : SmoothScalar g) :
    ∫ x, ((gradInnerCLM (I := I) (M := M) g φ u_h :
              Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x *
            (w.toFun x - ΔG (I := I) g ⟨w.toFun, w.smooth⟩ x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, w.toFun x *
            ((laplacianDomain.preimage (I := I) (M := M) g
                ⟨w_lift, hw_lift⟩ :
                Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  rw [← h_witness]
  exact integral_H1ComplToLp_oneSubLap_eq_integral_preimage_smooth
    (I := I) (M := M) g hw_lift w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerVariationalIntegralForm.integral_gradInner_oneSubLap_smooth_eq_integral_preimage_smooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerVariationalIntegralForm.integral_gradInner_oneSubLap_smooth_eq_integral_preimage_smooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerVariationalIntegralForm.integral_gradInner_oneSubLap_smooth_eq_integral_preimage_smooth ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerVariationalIntegralForm.integral_gradInner_oneSubLap_smooth_eq_integral_preimage_smooth

omit [NeZero (Module.finrank ℝ E)] in
theorem integral_gradInner_oneSubLap_smooth_eq_integral_smoothCase
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (w : SmoothScalar g) :
    ∫ x, ((gradInnerCLM (I := I) (M := M) g φ
              (smoothToH1Compl (I := I) (M := M) g v) :
              Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x *
            (w.toFun x - ΔG (I := I) g ⟨w.toFun, w.smooth⟩ x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, w.toFun x *
            ((smoothToLp (I := I) (M := M) g
                (gradInnerSmoothBundle (I := I) (M := M) g φ v).oneSubLapClassical :
                Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  set w_lift : H1Compl (I := I) (M := M) g :=
    smoothGradInnerPreimage (I := I) (M := M) g φ v with hw_lift_def
  have hw_lift_mem : w_lift ∈ laplacianDomain (I := I) (M := M) g := by
    rw [hw_lift_def]
    exact smoothGradInnerPreimage_mem_laplacianDomain (I := I) (M := M) g φ v
  have hw_lift_eq : H1ComplToLp (I := I) (M := M) g w_lift =
      gradInnerCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) := by
    rw [hw_lift_def]
    exact H1ComplToLp_smoothGradInnerPreimage (I := I) (M := M) g φ v
  have h_main :=
    integral_gradInner_oneSubLap_smooth_eq_integral_preimage_smooth
      (I := I) (M := M) g φ hw_lift_mem hw_lift_eq w
  have h_preimage_eq :
      laplacianDomain.preimage (I := I) (M := M) g ⟨w_lift, hw_lift_mem⟩ =
        smoothToLp (I := I) (M := M) g
          (gradInnerSmoothBundle (I := I) (M := M) g φ v).oneSubLapClassical := by
    apply resolvent_injective (I := I) (M := M) g
    have h_lhs := resolvent_laplacianDomain_preimage_eq (I := I) (M := M) g
      ⟨w_lift, hw_lift_mem⟩
    rw [h_lhs]
    change w_lift = _
    rw [hw_lift_def]
    unfold smoothGradInnerPreimage
    exact smoothToH1Compl_eq_resolvent_oneSubLap (I := I) (M := M)
      (gradInnerSmoothBundle (I := I) (M := M) g φ v)
  rw [h_preimage_eq] at h_main
  exact h_main

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerVariationalIntegralForm.integral_gradInner_oneSubLap_smooth_eq_integral_smoothCase then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerVariationalIntegralForm.integral_gradInner_oneSubLap_smooth_eq_integral_smoothCase"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerVariationalIntegralForm.integral_gradInner_oneSubLap_smooth_eq_integral_smoothCase ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerVariationalIntegralForm.integral_gradInner_oneSubLap_smooth_eq_integral_smoothCase

theorem integral_gradInner_oneSubLap_smooth_eq_integral_rhs_of_variational
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (hvar_id :
      gradInnerCLM (I := I) (M := M) g φ u_h =
        H1ComplToLp (I := I) (M := M) g
          (resolvent (I := I) (M := M) g
            (gradInnerLaplacianRhs
              (I := I) (M := M) g φ hu_h)))
    (w : SmoothScalar g) :
    ∫ x, ((gradInnerCLM (I := I) (M := M) g φ u_h :
              Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x *
            (w.toFun x - ΔG (I := I) g ⟨w.toFun, w.smooth⟩ x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, w.toFun x *
            ((gradInnerLaplacianRhs
                (I := I) (M := M) g φ hu_h :
                Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  set F : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
    gradInnerLaplacianRhs (I := I) (M := M) g φ hu_h with hF_def
  set w_lift : H1Compl (I := I) (M := M) g :=
    resolvent (I := I) (M := M) g F with hw_lift_def
  have hw_lift_mem : w_lift ∈ laplacianDomain (I := I) (M := M) g := by
    rw [hw_lift_def]
    exact (laplacianDomain_mem_iff (I := I) (M := M) g).mpr ⟨F, rfl⟩
  have h_preimage_eq :
      laplacianDomain.preimage (I := I) (M := M) g ⟨w_lift, hw_lift_mem⟩ = F := by
    apply resolvent_injective (I := I) (M := M) g
    rw [resolvent_laplacianDomain_preimage_eq]
  have hw_lift_eq : H1ComplToLp (I := I) (M := M) g w_lift =
      gradInnerCLM (I := I) (M := M) g φ u_h := by
    rw [hw_lift_def]
    exact hvar_id.symm
  have h_main :=
    integral_gradInner_oneSubLap_smooth_eq_integral_preimage_smooth
      (I := I) (M := M) g φ hw_lift_mem hw_lift_eq w
  rw [h_preimage_eq] at h_main
  exact h_main

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerVariationalIntegralForm.integral_gradInner_oneSubLap_smooth_eq_integral_rhs_of_variational then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerVariationalIntegralForm.integral_gradInner_oneSubLap_smooth_eq_integral_rhs_of_variational"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerVariationalIntegralForm.integral_gradInner_oneSubLap_smooth_eq_integral_rhs_of_variational ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerVariationalIntegralForm.integral_gradInner_oneSubLap_smooth_eq_integral_rhs_of_variational

theorem integral_gradInner_oneSubLap_smooth_eq_integral_rhs_smooth_of_pairing
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_discharge : christoffelDischargeSmoothCase (I := I) (M := M) g φ v)
    (w : SmoothScalar g) :
    ∫ x, ((gradInnerCLM (I := I) (M := M) g φ
              (smoothToH1Compl (I := I) (M := M) g v) :
              Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x *
            (w.toFun x - ΔG (I := I) g ⟨w.toFun, w.smooth⟩ x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, w.toFun x *
            ((gradInnerLaplacianRhs (I := I) (M := M) g φ
                (smoothToH1Compl_mem_laplacianDomainPow_two
                  (I := I) (M := M) g v) :
                Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  have hvar_id :=
    gradInnerCLM_eq_H1ComplToLp_resolvent_smoothCase_of_discharge
      (I := I) (M := M) g φ v h_discharge
  exact integral_gradInner_oneSubLap_smooth_eq_integral_rhs_of_variational
    (I := I) (M := M) g φ
    (smoothToH1Compl_mem_laplacianDomainPow_two (I := I) (M := M) g v)
    hvar_id w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerVariationalIntegralForm.integral_gradInner_oneSubLap_smooth_eq_integral_rhs_smooth_of_pairing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerVariationalIntegralForm.integral_gradInner_oneSubLap_smooth_eq_integral_rhs_smooth_of_pairing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerVariationalIntegralForm.integral_gradInner_oneSubLap_smooth_eq_integral_rhs_smooth_of_pairing ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerVariationalIntegralForm.integral_gradInner_oneSubLap_smooth_eq_integral_rhs_smooth_of_pairing

theorem integral_gradInner_oneSubLap_smooth_eq_integral_rhs_of_density
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_smooth_seq : ℕ → SmoothScalar g)
    (h_convergence_H1Compl : _root_.Filter.Tendsto
      (fun n => smoothToH1Compl (I := I) (M := M) g (h_smooth_seq n))
      _root_.Filter.atTop (𝓝 u_h))
    (h_convergence_candidate : _root_.Filter.Tendsto
      (fun n => gradInnerLaplacianRhs (I := I) (M := M) g φ
        (smoothToH1Compl_mem_laplacianDomainPow_two
          (I := I) (M := M) g (h_smooth_seq n)))
      _root_.Filter.atTop (𝓝 (gradInnerLaplacianRhs
        (I := I) (M := M) g φ hu_h)))
    (h_smooth_identity : ∀ n,
      gradInnerLaplacianRhs (I := I) (M := M) g φ
          (smoothToH1Compl_mem_laplacianDomainPow_two
            (I := I) (M := M) g (h_smooth_seq n)) =
        smoothToLp (I := I) (M := M) g
          (gradInnerSmoothBundle (I := I) (M := M) g φ
            (h_smooth_seq n)).oneSubLapClassical)
    (w : SmoothScalar g) :
    ∫ x, ((gradInnerCLM (I := I) (M := M) g φ u_h :
              Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x *
            (w.toFun x - ΔG (I := I) g ⟨w.toFun, w.smooth⟩ x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, w.toFun x *
            ((gradInnerLaplacianRhs
                (I := I) (M := M) g φ hu_h :
                Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  have hvar_id :=
    gradInnerCLM_eq_H1ComplToLp_resolvent_of_smooth_approximation
      (I := I) (M := M) g φ hu_h h_smooth_seq h_convergence_H1Compl
      h_convergence_candidate h_smooth_identity
  exact integral_gradInner_oneSubLap_smooth_eq_integral_rhs_of_variational
    (I := I) (M := M) g φ hu_h hvar_id w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerVariationalIntegralForm.integral_gradInner_oneSubLap_smooth_eq_integral_rhs_of_density then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerVariationalIntegralForm.integral_gradInner_oneSubLap_smooth_eq_integral_rhs_of_density"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerVariationalIntegralForm.integral_gradInner_oneSubLap_smooth_eq_integral_rhs_of_density ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerVariationalIntegralForm.integral_gradInner_oneSubLap_smooth_eq_integral_rhs_of_density

omit [NeZero (Module.finrank ℝ E)] in
theorem integral_gradInner_oneSubLap_contMDiff_eq_integral_preimage
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    {w_lift : H1Compl (I := I) (M := M) g}
    (hw_lift : w_lift ∈ laplacianDomain (I := I) (M := M) g)
    (h_witness : H1ComplToLp (I := I) (M := M) g w_lift =
      gradInnerCLM (I := I) (M := M) g φ u_h)
    {w : M → ℝ} (hw : ContMDiff I 𝓘(ℝ, ℝ) ∞ w) :
    ∫ x, ((gradInnerCLM (I := I) (M := M) g φ u_h :
              Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x *
            (w x - ΔG (I := I) g ⟨_, hw⟩ x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, w x *
            ((laplacianDomain.preimage (I := I) (M := M) g
                ⟨w_lift, hw_lift⟩ :
                Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  exact integral_gradInner_oneSubLap_smooth_eq_integral_preimage_smooth
    (I := I) (M := M) g φ hw_lift h_witness ⟨w, hw⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerVariationalIntegralForm.integral_gradInner_oneSubLap_contMDiff_eq_integral_preimage then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerVariationalIntegralForm.integral_gradInner_oneSubLap_contMDiff_eq_integral_preimage"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerVariationalIntegralForm.integral_gradInner_oneSubLap_contMDiff_eq_integral_preimage ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerVariationalIntegralForm.integral_gradInner_oneSubLap_contMDiff_eq_integral_preimage

omit [NeZero (Module.finrank ℝ E)] in
theorem integral_grad_inner_oneSubLap_smooth_pointwise
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (w : SmoothScalar g) :
    ∫ x, g.inner x (gradFun (I := I) g (φ : M → ℝ) x)
            (gradFun (I := I) g v.toFun x) *
            (w.toFun x - ΔG (I := I) g ⟨w.toFun, w.smooth⟩ x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, w.toFun x *
            ((gradInnerSmoothBundle (I := I) (M := M) g φ v).toFun x -
              ΔG (I := I) g ⟨(gradInnerSmoothBundle (I := I) (M := M) g φ v).toFun,
                (gradInnerSmoothBundle (I := I) (M := M) g φ v).smooth⟩ x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  have h_main :=
    integral_gradInner_oneSubLap_smooth_eq_integral_smoothCase
      (I := I) (M := M) g φ v w
  have h_LHS_coeFn :
      ((gradInnerCLM (I := I) (M := M) g φ
          (smoothToH1Compl (I := I) (M := M) g v) :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      (fun x : M => g.inner x (gradFun (I := I) g (φ : M → ℝ) x)
        (gradFun (I := I) g v.toFun x)) := by
    rw [gradInnerCLM_smoothToH1Compl (I := I) (M := M) g φ v]
    exact gradInnerSmooth_coeFn (I := I) (M := M) g φ v
  have h_RHS_coeFn :
      ((smoothToLp (I := I) (M := M) g
          (gradInnerSmoothBundle (I := I) (M := M) g φ v).oneSubLapClassical :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      (fun x : M => (gradInnerSmoothBundle (I := I) (M := M) g φ v).toFun x -
            ΔG (I := I) g ⟨(gradInnerSmoothBundle (I := I) (M := M) g φ v).toFun,
              (gradInnerSmoothBundle (I := I) (M := M) g φ v).smooth⟩ x) := by
    have h := MemLp.coeFn_toLp
      (gradInnerSmoothBundle (I := I) (M := M) g φ v).oneSubLapClassical.memLp_two
    filter_upwards [h] with x hx
    change ((((gradInnerSmoothBundle (I := I) (M := M) g φ v).oneSubLapClassical.memLp_two.toLp
        _ :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x) = _
    rw [hx]
    rfl
  have h_LHS_int_ae :
      (fun x : M =>
          ((gradInnerCLM (I := I) (M := M) g φ
              (smoothToH1Compl (I := I) (M := M) g v) :
              Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x *
            (w.toFun x - ΔG (I := I) g ⟨w.toFun, w.smooth⟩ x)) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      (fun x : M => g.inner x (gradFun (I := I) g (φ : M → ℝ) x)
            (gradFun (I := I) g v.toFun x) *
          (w.toFun x - ΔG (I := I) g ⟨w.toFun, w.smooth⟩ x)) := by
    filter_upwards [h_LHS_coeFn] with x hx
    rw [hx]
  have h_RHS_int_ae :
      (fun x : M =>
          w.toFun x *
          ((smoothToLp (I := I) (M := M) g
              (gradInnerSmoothBundle (I := I) (M := M) g φ v).oneSubLapClassical :
              Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      (fun x : M => w.toFun x *
          ((gradInnerSmoothBundle (I := I) (M := M) g φ v).toFun x -
            ΔG (I := I) g ⟨(gradInnerSmoothBundle (I := I) (M := M) g φ v).toFun,
              (gradInnerSmoothBundle (I := I) (M := M) g φ v).smooth⟩ x)) := by
    filter_upwards [h_RHS_coeFn] with x hx
    rw [hx]
  have h_LHS_eq :=
    _root_.MeasureTheory.integral_congr_ae h_LHS_int_ae
  have h_RHS_eq :=
    _root_.MeasureTheory.integral_congr_ae h_RHS_int_ae
  rw [← h_LHS_eq, ← h_RHS_eq]
  exact h_main

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerVariationalIntegralForm.integral_grad_inner_oneSubLap_smooth_pointwise then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerVariationalIntegralForm.integral_grad_inner_oneSubLap_smooth_pointwise"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerVariationalIntegralForm.integral_grad_inner_oneSubLap_smooth_pointwise ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerVariationalIntegralForm.integral_grad_inner_oneSubLap_smooth_pointwise

omit [NeZero (Module.finrank ℝ E)] in
theorem integral_gradInner_oneSubLap_contMDiffMap_eq_integral_preimage
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    {w_lift : H1Compl (I := I) (M := M) g}
    (hw_lift : w_lift ∈ laplacianDomain (I := I) (M := M) g)
    (h_witness : H1ComplToLp (I := I) (M := M) g w_lift =
      gradInnerCLM (I := I) (M := M) g φ u_h)
    (w : C^∞⟮I, M; ℝ⟯) :
    ∫ x, ((gradInnerCLM (I := I) (M := M) g φ u_h :
              Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x *
            ((w : M → ℝ) x - ΔG (I := I) g w x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, (w : M → ℝ) x *
            ((laplacianDomain.preimage (I := I) (M := M) g
                ⟨w_lift, hw_lift⟩ :
                Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  exact integral_gradInner_oneSubLap_smooth_eq_integral_preimage_smooth
    (I := I) (M := M) g φ hw_lift h_witness ⟨(w : M → ℝ), w.contMDiff⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerVariationalIntegralForm.integral_gradInner_oneSubLap_contMDiffMap_eq_integral_preimage then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerVariationalIntegralForm.integral_gradInner_oneSubLap_contMDiffMap_eq_integral_preimage"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerVariationalIntegralForm.integral_gradInner_oneSubLap_contMDiffMap_eq_integral_preimage ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerVariationalIntegralForm.integral_gradInner_oneSubLap_contMDiffMap_eq_integral_preimage

omit [NeZero (Module.finrank ℝ E)] in
theorem weak_oneSubLap_holds_of_image_in_laplacianDomain
    (g : SmoothRiemannianMetric I M)
    {A : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    {w_lift : H1Compl (I := I) (M := M) g}
    (hw_lift : w_lift ∈ laplacianDomain (I := I) (M := M) g)
    (h_A_eq : H1ComplToLp (I := I) (M := M) g w_lift = A) :
    ∀ w : SmoothScalar g,
      ∫ x, (A : M → ℝ) x * (w.toFun x - ΔG (I := I) g ⟨w.toFun, w.smooth⟩ x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, w.toFun x *
            ((laplacianDomain.preimage (I := I) (M := M) g
                ⟨w_lift, hw_lift⟩ :
                Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  intro w
  rw [← h_A_eq]
  exact integral_H1ComplToLp_oneSubLap_eq_integral_preimage_smooth
    (I := I) (M := M) g hw_lift w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerVariationalIntegralForm.weak_oneSubLap_holds_of_image_in_laplacianDomain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerVariationalIntegralForm.weak_oneSubLap_holds_of_image_in_laplacianDomain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerVariationalIntegralForm.weak_oneSubLap_holds_of_image_in_laplacianDomain ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerVariationalIntegralForm.weak_oneSubLap_holds_of_image_in_laplacianDomain

end GradInnerVariationalIntegralForm
end Laplacian
end Analysis
end DifferentialGeometry

end
