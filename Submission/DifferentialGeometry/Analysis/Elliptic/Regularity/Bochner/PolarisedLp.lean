import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.Bochner.PolarisedLpSmooth
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.GradInner.Laplacian.VariationalIdentity

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
namespace BochnerPolarisedLp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem

open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLpIdentity
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.HessianPairingChart
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.HessianPairingLapDom
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianRhs
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.BochnerPolarised
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLpSmooth
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDomain

private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLp.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLp.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLp.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLp.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLp.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLp.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLp.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLp.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLp.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLp.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLp.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLp.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem H1ComplToLp_injOn_laplacianDomain
    (g : SmoothRiemannianMetric I M)
    {w₁ w₂ : H1Compl (I := I) (M := M) g}
    (hw₁ : w₁ ∈ laplacianDomain (I := I) (M := M) g)
    (hw₂ : w₂ ∈ laplacianDomain (I := I) (M := M) g)
    (heq : H1ComplToLp (I := I) (M := M) g w₁ =
      H1ComplToLp (I := I) (M := M) g w₂) :
    w₁ = w₂ := by
  classical
  set f₁ := laplacianDomain.preimage (I := I) (M := M) g ⟨w₁, hw₁⟩ with hf₁_def
  set f₂ := laplacianDomain.preimage (I := I) (M := M) g ⟨w₂, hw₂⟩ with hf₂_def
  have hw₁_eq : w₁ = resolvent (I := I) (M := M) g f₁ := by
    rw [hf₁_def]
    exact (resolvent_laplacianDomain_preimage_eq (I := I) (M := M) g ⟨w₁, hw₁⟩).symm
  have hw₂_eq : w₂ = resolvent (I := I) (M := M) g f₂ := by
    rw [hf₂_def]
    exact (resolvent_laplacianDomain_preimage_eq (I := I) (M := M) g ⟨w₂, hw₂⟩).symm
  have h_var₁ : ∀ v : H1Compl g,
      ⟪w₁, v⟫_ℝ = ⟪H1ComplToLp (I := I) (M := M) g v, f₁⟫_ℝ := by
    intro v
    rw [hw₁_eq]
    exact resolvent_inner_eq_lpFunctional (I := I) (M := M) g f₁ v
  have h_var₂ : ∀ v : H1Compl g,
      ⟪w₂, v⟫_ℝ = ⟪H1ComplToLp (I := I) (M := M) g v, f₂⟫_ℝ := by
    intro v
    rw [hw₂_eq]
    exact resolvent_inner_eq_lpFunctional (I := I) (M := M) g f₂ v
  have h_diff_var : ∀ v : H1Compl g,
      ⟪w₁ - w₂, v⟫_ℝ =
        ⟪H1ComplToLp (I := I) (M := M) g v, f₁ - f₂⟫_ℝ := by
    intro v
    rw [inner_sub_left, inner_sub_right]
    rw [h_var₁ v, h_var₂ v]
  specialize h_diff_var (w₁ - w₂)
  have h_H1ComplToLp_diff : H1ComplToLp (I := I) (M := M) g (w₁ - w₂) = 0 := by
    rw [(H1ComplToLp (I := I) (M := M) g).map_sub]
    rw [heq, sub_self]
  rw [h_H1ComplToLp_diff, inner_zero_left] at h_diff_var
  rw [real_inner_self_eq_norm_sq] at h_diff_var
  have h_norm_zero : ‖w₁ - w₂‖ = 0 := by
    have h_pow_zero : ‖w₁ - w₂‖ ^ 2 = 0 := h_diff_var
    exact pow_eq_zero_iff (two_ne_zero) |>.mp h_pow_zero
  have h_sub_zero : w₁ - w₂ = 0 := norm_eq_zero.mp h_norm_zero
  exact sub_eq_zero.mp h_sub_zero

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLp.H1ComplToLp_injOn_laplacianDomain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLp.H1ComplToLp_injOn_laplacianDomain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLp.H1ComplToLp_injOn_laplacianDomain ``Submission.DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLp.H1ComplToLp_injOn_laplacianDomain

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem preimageLift_smoothCase
    (g : SmoothRiemannianMetric I M) (v : SmoothScalar g) :
    preimageLift (I := I) (M := M) g
        (smoothToH1Compl_mem_laplacianDomainPow_two (I := I) (M := M) g v) =
      smoothToH1Compl (I := I) (M := M) g v.oneSubLapClassical := by
  classical
  set u_h := smoothToH1Compl (I := I) (M := M) g v
  set hu_h := smoothToH1Compl_mem_laplacianDomainPow_two (I := I) (M := M) g v
  set hu_dom : u_h ∈ laplacianDomain (I := I) (M := M) g :=
    laplacianDomainPow_succ_subset_laplacianDomain
      (I := I) (M := M) g 1 hu_h
  have h_pl_dom : preimageLift (I := I) (M := M) g hu_h ∈
      laplacianDomain (I := I) (M := M) g :=
    preimageLift_mem_laplacianDomain (I := I) (M := M) g hu_h
  have h_st_dom : smoothToH1Compl (I := I) (M := M) g v.oneSubLapClassical ∈
      laplacianDomain (I := I) (M := M) g :=
    smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v.oneSubLapClassical
  have h_pl_H1ComplToLp :
      H1ComplToLp (I := I) (M := M) g
          (preimageLift (I := I) (M := M) g hu_h) =
        laplacianDomain.preimage (I := I) (M := M) g
          ⟨u_h, hu_dom⟩ :=
    H1ComplToLp_preimageLift (I := I) (M := M) g hu_h
  have h_st_H1ComplToLp :
      H1ComplToLp (I := I) (M := M) g
          (smoothToH1Compl (I := I) (M := M) g v.oneSubLapClassical) =
        smoothToLp (I := I) (M := M) g v.oneSubLapClassical :=
    H1ComplToLp_smoothToH1Compl (I := I) (M := M) g v.oneSubLapClassical
  have h_preimage_eq :
      laplacianDomain.preimage (I := I) (M := M) g ⟨u_h, hu_dom⟩ =
        smoothToLp (I := I) (M := M) g v.oneSubLapClassical := by
    apply resolvent_injective (I := I) (M := M) g
    rw [resolvent_laplacianDomain_preimage_eq]
    exact smoothToH1Compl_eq_resolvent_oneSubLap (I := I) (M := M) v
  have h_H1ComplToLp_eq :
      H1ComplToLp (I := I) (M := M) g
          (preimageLift (I := I) (M := M) g hu_h) =
        H1ComplToLp (I := I) (M := M) g
          (smoothToH1Compl (I := I) (M := M) g v.oneSubLapClassical) := by
    rw [h_pl_H1ComplToLp, h_st_H1ComplToLp, h_preimage_eq]
  exact H1ComplToLp_injOn_laplacianDomain (I := I) (M := M) g h_pl_dom h_st_dom
    h_H1ComplToLp_eq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLp.preimageLift_smoothCase then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLp.preimageLift_smoothCase"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLp.preimageLift_smoothCase ``Submission.DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLp.preimageLift_smoothCase

omit [NeZero (Module.finrank ℝ E)] in
theorem gradInnerLapU_smoothCase
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    gradInnerLapU (I := I) (M := M) g φ
        (smoothToH1Compl_mem_laplacianDomainPow_two
          (I := I) (M := M) g v) =
      smoothToLp (I := I) (M := M) g
          (gradInnerSmoothBundle (I := I) (M := M) g φ v) -
        smoothToLp (I := I) (M := M) g
          (gradInnerSmoothBundle (I := I) (M := M) g φ
            v.oneSubLapClassical) := by
  classical
  rw [gradInnerLapU_eq_sub]
  rw [gradInnerCLM_smoothToH1Compl_eq_smoothToLp]
  rw [preimageLift_smoothCase]
  rw [gradInnerCLM_smoothToH1Compl_eq_smoothToLp]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLp.gradInnerLapU_smoothCase then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLp.gradInnerLapU_smoothCase"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLp.gradInnerLapU_smoothCase ``Submission.DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLp.gradInnerLapU_smoothCase

omit [NeZero (Module.finrank ℝ E)] in
omit [CompactSpace M] [SigmaCompactSpace M] in
theorem v_sub_oneSubLap_eq_lap
    (g : SmoothRiemannianMetric I M) (v : SmoothScalar g) (x : M) :
    v.toFun x - v.oneSubLapClassical.toFun x = ΔG (I := I) g ⟨v.toFun, v.smooth⟩ x := by
  rw [SmoothScalar.oneSubLapClassical_toFun, Pi.sub_apply]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLp.v_sub_oneSubLap_eq_lap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLp.v_sub_oneSubLap_eq_lap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLp.v_sub_oneSubLap_eq_lap ``Submission.DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLp.v_sub_oneSubLap_eq_lap

omit [CompactSpace M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem gradInnerSmoothBundle_sub_oneSubLap_apply
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (b : M) :
    (gradInnerSmoothBundle (I := I) (M := M) g φ v).toFun b -
        (gradInnerSmoothBundle (I := I) (M := M) g φ
          v.oneSubLapClassical).toFun b =
      g.inner b (gradFun (I := I) g (φ : M → ℝ) b)
        (gradFun (I := I) g (ΔG (I := I) g ⟨v.toFun, v.smooth⟩) b) := by
  classical
  rw [gradInnerSmoothBundle_apply, gradInnerSmoothBundle_apply]
  have hv_diff : MDifferentiableAt I 𝓘(ℝ, ℝ) v.toFun b :=
    v.smooth.mdifferentiable (by simp) b
  have hvl_diff : MDifferentiableAt I 𝓘(ℝ, ℝ) v.oneSubLapClassical.toFun b :=
    v.oneSubLapClassical.smooth.mdifferentiable (by simp) b
  have hΔv_diff : MDifferentiableAt I 𝓘(ℝ, ℝ) (ΔG (I := I) g ⟨v.toFun, v.smooth⟩) b :=
    (Δ_g_contMDiff (I := I) g ⟨v.toFun, v.smooth⟩).mdifferentiable (by simp) b
  have h_inner_sub : g.inner b
        (gradFun (I := I) g (φ : M → ℝ) b)
        (gradFun (I := I) g v.toFun b) -
      g.inner b
        (gradFun (I := I) g (φ : M → ℝ) b)
        (gradFun (I := I) g v.oneSubLapClassical.toFun b) =
      g.inner b
        (gradFun (I := I) g (φ : M → ℝ) b)
        (gradFun (I := I) g v.toFun b -
          gradFun (I := I) g v.oneSubLapClassical.toFun b) := by
    rw [(g.inner b (gradFun (I := I) g (φ : M → ℝ) b)).map_sub]
  rw [h_inner_sub]
  have h_grad_sub : gradFun (I := I) g v.toFun b -
        gradFun (I := I) g v.oneSubLapClassical.toFun b =
      gradFun (I := I) g
        (fun y : M => v.toFun y - v.oneSubLapClassical.toFun y) b := by
    rw [DifferentialGeometry.Geometry.Connection.gradFun_sub
      (I := I) g hv_diff hvl_diff]
  rw [h_grad_sub]
  have h_fun_eq : (fun y : M => v.toFun y - v.oneSubLapClassical.toFun y) =
      (fun y : M => ΔG (I := I) g ⟨v.toFun, v.smooth⟩ y) := by
    funext y
    exact v_sub_oneSubLap_eq_lap (I := I) (M := M) g v y
  rw [h_fun_eq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLp.gradInnerSmoothBundle_sub_oneSubLap_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLp.gradInnerSmoothBundle_sub_oneSubLap_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLp.gradInnerSmoothBundle_sub_oneSubLap_apply ``Submission.DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLp.gradInnerSmoothBundle_sub_oneSubLap_apply

noncomputable def smoothLaplacianAsScalar
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) : SmoothScalar g where
  toFun := ΔG (I := I) g φ
  smooth := Δ_g_contMDiff (I := I) g φ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLp.smoothLaplacianAsScalar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLp.smoothLaplacianAsScalar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLp.smoothLaplacianAsScalar ``Submission.DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLp.smoothLaplacianAsScalar

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M] in
@[simp] lemma smoothLaplacianAsScalar_toFun
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) :
    (smoothLaplacianAsScalar (I := I) (M := M) g φ).toFun =
      ΔG (I := I) g φ := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLp.smoothLaplacianAsScalar_toFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLp.smoothLaplacianAsScalar_toFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLp.smoothLaplacianAsScalar_toFun ``Submission.DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLp.smoothLaplacianAsScalar_toFun

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M] in
lemma smoothLaplacianBundle_toFun_eq_smoothLaplacianAsScalar
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) :
    ((smoothLaplacianBundle (I := I) (M := M) g φ) : M → ℝ) =
      (smoothLaplacianAsScalar (I := I) (M := M) g φ).toFun := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLp.smoothLaplacianBundle_toFun_eq_smoothLaplacianAsScalar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLp.smoothLaplacianBundle_toFun_eq_smoothLaplacianAsScalar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLp.smoothLaplacianBundle_toFun_eq_smoothLaplacianAsScalar ``Submission.DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLp.smoothLaplacianBundle_toFun_eq_smoothLaplacianAsScalar

omit [CompactSpace M] in
omit [SigmaCompactSpace M] in
theorem oneSubLapClassical_gradInner_apply
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (x : M) :
    (gradInnerSmoothBundle (I := I) (M := M) g φ v).oneSubLapClassical.toFun x =
      g.inner x
        (gradFun (I := I) g (φ : M → ℝ) x)
        (gradFun (I := I) g v.toFun x)
      - g.inner x
          (gradFun (I := I) g v.toFun x)
          (gradFun (I := I) g (ΔG (I := I) g φ) x)
      - g.inner x
          (gradFun (I := I) g (φ : M → ℝ) x)
          (gradFun (I := I) g (ΔG (I := I) g ⟨v.toFun, v.smooth⟩) x)
      - 2 * hessPairingChart (I := I) g φ
          ⟨v.toFun, v.smooth⟩ x
      - 2 * ricciTensor (I := I) g x
            (gradFun (I := I) g (φ : M → ℝ) x)
            (gradFun (I := I) g v.toFun x) := by
  classical
  rw [SmoothScalar.oneSubLapClassical_toFun, Pi.sub_apply]
  rw [gradInnerSmoothBundle_apply]
  have h_Δ_eq := Δ_g_gradInnerSmoothBundle_eq_contMDiff_g_inner
    (I := I) (M := M) g φ v x
  rw [h_Δ_eq]
  have h_polar := bochner_polarised_pointwise_oneSubLap (I := I) (M := M) g
    φ ⟨v.toFun, v.smooth⟩ x
  exact h_polar

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLp.oneSubLapClassical_gradInner_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLp.oneSubLapClassical_gradInner_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLp.oneSubLapClassical_gradInner_apply ``Submission.DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLp.oneSubLapClassical_gradInner_apply

theorem gradInnerLaplacianRhs_smooth_of_hessPairing
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_hess :
      hessPairingLpOnLapDom (I := I) (M := M) g φ
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1
            (smoothToH1Compl_mem_laplacianDomainPow_two
              (I := I) (M := M) g v)) =
        hessPairingSmoothLp (I := I) (M := M) g φ v) :
    gradInnerLaplacianRhs (I := I) (M := M) g φ
        (smoothToH1Compl_mem_laplacianDomainPow_two
          (I := I) (M := M) g v) =
      smoothToLp (I := I) (M := M) g
        (gradInnerSmoothBundle (I := I) (M := M) g φ v).oneSubLapClassical := by
  classical
  unfold gradInnerLaplacianRhs
  rw [gradInnerCLM_smoothToH1Compl_eq_smoothToLp (I := I) (M := M) g φ v]
  rw [gradInnerCLM_smoothToH1Compl_eq_smoothToLp (I := I) (M := M) g
      (smoothLaplacianBundle (I := I) (M := M) g φ) v]
  rw [gradInnerLapU_smoothCase (I := I) (M := M) g φ v]
  rw [ricciPairingCLM_smoothToH1Compl_eq_smoothToLp (I := I) (M := M) g φ v]
  rw [h_hess]
  apply MeasureTheory.Lp.ext
  set A1 := smoothToLp (I := I) (M := M) g
      (gradInnerSmoothBundle (I := I) (M := M) g φ v) with hA1_def
  set A2 := smoothToLp (I := I) (M := M) g
      (gradInnerSmoothBundle (I := I) (M := M) g
        (smoothLaplacianBundle (I := I) (M := M) g φ) v) with hA2_def
  set A3 := smoothToLp (I := I) (M := M) g
      (gradInnerSmoothBundle (I := I) (M := M) g φ v) -
    smoothToLp (I := I) (M := M) g
      (gradInnerSmoothBundle (I := I) (M := M) g φ v.oneSubLapClassical) with hA3_def
  set A4 := ricciPairingSmooth (I := I) (M := M) g φ v with hA4_def
  set A5 := hessPairingSmoothLp (I := I) (M := M) g φ v with hA5_def
  set RHS := smoothToLp (I := I) (M := M) g
      (gradInnerSmoothBundle (I := I) (M := M) g φ v).oneSubLapClassical with hRHS_def
  have h_A1_coe : ((smoothToLp (I := I) (M := M) g
        (gradInnerSmoothBundle (I := I) (M := M) g φ v) :
        _root_.MeasureTheory.Lp ℝ 2 _) : M → ℝ) =ᵐ[
      riemannianVolumeMeasure (I := I) (M := M) g]
      (gradInnerSmoothBundle (I := I) (M := M) g φ v).toFun :=
    MemLp.coeFn_toLp
      (gradInnerSmoothBundle (I := I) (M := M) g φ v).memLp_two
  have h_A2_coe : ((smoothToLp (I := I) (M := M) g
        (gradInnerSmoothBundle (I := I) (M := M) g
          (smoothLaplacianBundle (I := I) (M := M) g φ) v) :
        _root_.MeasureTheory.Lp ℝ 2 _) : M → ℝ) =ᵐ[
      riemannianVolumeMeasure (I := I) (M := M) g]
      (gradInnerSmoothBundle (I := I) (M := M) g
        (smoothLaplacianBundle (I := I) (M := M) g φ) v).toFun :=
    MemLp.coeFn_toLp
      (gradInnerSmoothBundle (I := I) (M := M) g
        (smoothLaplacianBundle (I := I) (M := M) g φ) v).memLp_two
  have h_A3a_coe : ((smoothToLp (I := I) (M := M) g
        (gradInnerSmoothBundle (I := I) (M := M) g φ v) :
        _root_.MeasureTheory.Lp ℝ 2 _) : M → ℝ) =ᵐ[
      riemannianVolumeMeasure (I := I) (M := M) g]
      (gradInnerSmoothBundle (I := I) (M := M) g φ v).toFun :=
    MemLp.coeFn_toLp
      (gradInnerSmoothBundle (I := I) (M := M) g φ v).memLp_two
  have h_A3b_coe : ((smoothToLp (I := I) (M := M) g
        (gradInnerSmoothBundle (I := I) (M := M) g φ v.oneSubLapClassical) :
        _root_.MeasureTheory.Lp ℝ 2 _) : M → ℝ) =ᵐ[
      riemannianVolumeMeasure (I := I) (M := M) g]
      (gradInnerSmoothBundle (I := I) (M := M) g φ v.oneSubLapClassical).toFun :=
    MemLp.coeFn_toLp
      (gradInnerSmoothBundle (I := I) (M := M) g φ v.oneSubLapClassical).memLp_two
  have h_A4_coe := ricciPairingSmooth_coeFn (I := I) (M := M) g φ v
  have h_A5_coe := hessPairingSmoothLp_coeFn (I := I) (M := M) g φ v
  have h_RHS_coe : ((smoothToLp (I := I) (M := M) g
        (gradInnerSmoothBundle (I := I) (M := M) g φ v).oneSubLapClassical :
        _root_.MeasureTheory.Lp ℝ 2 _) : M → ℝ) =ᵐ[
      riemannianVolumeMeasure (I := I) (M := M) g]
      (gradInnerSmoothBundle (I := I) (M := M) g φ v).oneSubLapClassical.toFun :=
    MemLp.coeFn_toLp
      (gradInnerSmoothBundle (I := I) (M := M) g φ v).oneSubLapClassical.memLp_two
  have h_A3_diff_coe : (A3 : M → ℝ) =ᵐ[
      riemannianVolumeMeasure (I := I) (M := M) g]
    fun b : M =>
      (gradInnerSmoothBundle (I := I) (M := M) g φ v).toFun b -
        (gradInnerSmoothBundle (I := I) (M := M) g φ v.oneSubLapClassical).toFun b := by
    change ((smoothToLp (I := I) (M := M) g
        (gradInnerSmoothBundle (I := I) (M := M) g φ v) -
      smoothToLp (I := I) (M := M) g
        (gradInnerSmoothBundle (I := I) (M := M) g φ v.oneSubLapClassical) : _root_.MeasureTheory.Lp ℝ 2 _) :
        M → ℝ) =ᵐ[_] _
    have h_sub := MeasureTheory.Lp.coeFn_sub
      (smoothToLp (I := I) (M := M) g
        (gradInnerSmoothBundle (I := I) (M := M) g φ v))
      (smoothToLp (I := I) (M := M) g
        (gradInnerSmoothBundle (I := I) (M := M) g φ v.oneSubLapClassical))
    refine h_sub.trans ?_
    filter_upwards [h_A3a_coe, h_A3b_coe] with b h_a h_b
    rw [Pi.sub_apply]
    rw [h_a, h_b]
  set LHS := A1 - A2 - A3 - (2 : ℝ) • A4 - (2 : ℝ) • A5 with hLHS_def
  have h_step1 : ((A1 - A2 : _root_.MeasureTheory.Lp ℝ 2 _) : M → ℝ) =ᵐ[
      riemannianVolumeMeasure (I := I) (M := M) g]
    fun b => (gradInnerSmoothBundle (I := I) (M := M) g φ v).toFun b -
      (gradInnerSmoothBundle (I := I) (M := M) g
        (smoothLaplacianBundle (I := I) (M := M) g φ) v).toFun b := by
    refine (MeasureTheory.Lp.coeFn_sub A1 A2).trans ?_
    filter_upwards [h_A1_coe, h_A2_coe] with b h_a1 h_a2
    rw [Pi.sub_apply, h_a1, h_a2]
  have h_step2 : ((A1 - A2 - A3 : _root_.MeasureTheory.Lp ℝ 2 _) : M → ℝ) =ᵐ[
      riemannianVolumeMeasure (I := I) (M := M) g]
    fun b => ((gradInnerSmoothBundle (I := I) (M := M) g φ v).toFun b -
      (gradInnerSmoothBundle (I := I) (M := M) g
        (smoothLaplacianBundle (I := I) (M := M) g φ) v).toFun b) -
      ((gradInnerSmoothBundle (I := I) (M := M) g φ v).toFun b -
        (gradInnerSmoothBundle (I := I) (M := M) g φ v.oneSubLapClassical).toFun b) := by
    refine (MeasureTheory.Lp.coeFn_sub (A1 - A2) A3).trans ?_
    filter_upwards [h_step1, h_A3_diff_coe] with b h_12 h_3
    rw [Pi.sub_apply, h_12, h_3]
  have h_A4_smul_coe : (((2 : ℝ) • A4 : _root_.MeasureTheory.Lp ℝ 2 _) : M → ℝ) =ᵐ[
      riemannianVolumeMeasure (I := I) (M := M) g]
    fun b => 2 * ricciTensor (I := I) g b
      (gradFun (I := I) g (φ : M → ℝ) b)
      (gradFun (I := I) g v.toFun b) := by
    refine (MeasureTheory.Lp.coeFn_smul (2 : ℝ) A4).trans ?_
    filter_upwards [h_A4_coe] with b h_a4
    rw [Pi.smul_apply, h_a4]
    rfl
  have h_step3 : ((A1 - A2 - A3 - (2 : ℝ) • A4 : _root_.MeasureTheory.Lp ℝ 2 _) : M → ℝ) =ᵐ[
      riemannianVolumeMeasure (I := I) (M := M) g]
    fun b => (((gradInnerSmoothBundle (I := I) (M := M) g φ v).toFun b -
        (gradInnerSmoothBundle (I := I) (M := M) g
          (smoothLaplacianBundle (I := I) (M := M) g φ) v).toFun b) -
        ((gradInnerSmoothBundle (I := I) (M := M) g φ v).toFun b -
          (gradInnerSmoothBundle (I := I) (M := M) g φ v.oneSubLapClassical).toFun b)) -
      2 * ricciTensor (I := I) g b
        (gradFun (I := I) g (φ : M → ℝ) b)
        (gradFun (I := I) g v.toFun b) := by
    refine (MeasureTheory.Lp.coeFn_sub (A1 - A2 - A3) ((2 : ℝ) • A4)).trans ?_
    filter_upwards [h_step2, h_A4_smul_coe] with b h_123 h_4
    rw [Pi.sub_apply, h_123, h_4]
  have h_A5_smul_coe : (((2 : ℝ) • A5 : _root_.MeasureTheory.Lp ℝ 2 _) : M → ℝ) =ᵐ[
      riemannianVolumeMeasure (I := I) (M := M) g]
    fun b => 2 * hessPairingChart (I := I) g φ
      ⟨v.toFun, v.smooth⟩ b := by
    refine (MeasureTheory.Lp.coeFn_smul (2 : ℝ) A5).trans ?_
    filter_upwards [h_A5_coe] with b h_a5
    rw [Pi.smul_apply, h_a5]
    rfl
  have h_LHS_coe : (LHS : M → ℝ) =ᵐ[
      riemannianVolumeMeasure (I := I) (M := M) g]
    fun b => ((((gradInnerSmoothBundle (I := I) (M := M) g φ v).toFun b -
          (gradInnerSmoothBundle (I := I) (M := M) g
            (smoothLaplacianBundle (I := I) (M := M) g φ) v).toFun b) -
          ((gradInnerSmoothBundle (I := I) (M := M) g φ v).toFun b -
            (gradInnerSmoothBundle (I := I) (M := M) g φ v.oneSubLapClassical).toFun b)) -
          2 * ricciTensor (I := I) g b
            (gradFun (I := I) g (φ : M → ℝ) b)
            (gradFun (I := I) g v.toFun b)) -
        2 * hessPairingChart (I := I) g φ
          ⟨v.toFun, v.smooth⟩ b := by
    refine (MeasureTheory.Lp.coeFn_sub (A1 - A2 - A3 - (2 : ℝ) • A4) ((2 : ℝ) • A5)).trans ?_
    filter_upwards [h_step3, h_A5_smul_coe] with b h_1234 h_5
    rw [Pi.sub_apply, h_1234, h_5]
  have h_RHS_coe' : (RHS : M → ℝ) =ᵐ[
      riemannianVolumeMeasure (I := I) (M := M) g]
    fun b => (gradInnerSmoothBundle (I := I) (M := M) g φ v).oneSubLapClassical.toFun b := by
    change ((smoothToLp (I := I) (M := M) g
      (gradInnerSmoothBundle (I := I) (M := M) g φ v).oneSubLapClassical :
      _root_.MeasureTheory.Lp ℝ 2 _) : M → ℝ) =ᵐ[_] _
    exact h_RHS_coe
  refine h_LHS_coe.trans ?_
  refine EventuallyEq.symm ?_
  refine h_RHS_coe'.trans ?_
  refine Filter.Eventually.of_forall ?_
  intro b
  beta_reduce
  rw [oneSubLapClassical_gradInner_apply (I := I) (M := M) g φ v b]
  simp only [gradInnerSmoothBundle_apply]
  have h_phi_sym : g.inner b
        (gradFun (I := I) g
          ((smoothLaplacianBundle (I := I) (M := M) g φ) : M → ℝ) b)
        (gradFun (I := I) g v.toFun b) =
      g.inner b
        (gradFun (I := I) g v.toFun b)
        (gradFun (I := I) g (ΔG (I := I) g φ) b) := by
    rw [show ((smoothLaplacianBundle (I := I) (M := M) g φ) : M → ℝ) =
        ΔG (I := I) g φ from rfl]
    exact g.symm b _ _
  rw [h_phi_sym]
  have h_diff_eq : g.inner b
        (gradFun (I := I) g (φ : M → ℝ) b)
        (gradFun (I := I) g v.toFun b) -
      g.inner b
        (gradFun (I := I) g (φ : M → ℝ) b)
        (gradFun (I := I) g v.oneSubLapClassical.toFun b) =
      g.inner b
        (gradFun (I := I) g (φ : M → ℝ) b)
        (gradFun (I := I) g (ΔG (I := I) g ⟨v.toFun, v.smooth⟩) b) := by
    have h := gradInnerSmoothBundle_sub_oneSubLap_apply (I := I) (M := M) g φ v b
    rw [gradInnerSmoothBundle_apply, gradInnerSmoothBundle_apply] at h
    exact h
  linarith [h_diff_eq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLp.gradInnerLaplacianRhs_smooth_of_hessPairing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLp.gradInnerLaplacianRhs_smooth_of_hessPairing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLp.gradInnerLaplacianRhs_smooth_of_hessPairing ``Submission.DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLp.gradInnerLaplacianRhs_smooth_of_hessPairing

theorem gradInnerLaplacianRhs_smooth_eq_of_hessPairing
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_hess :
      hessPairingLpOnLapDom (I := I) (M := M) g φ
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1
            (smoothToH1Compl_mem_laplacianDomainPow_two
              (I := I) (M := M) g v)) =
        hessPairingSmoothLp (I := I) (M := M) g φ v) :
    gradInnerLaplacianRhs (I := I) (M := M) g φ
        (smoothToH1Compl_mem_laplacianDomainPow_two (I := I) (M := M) g v) =
      smoothToLp (I := I) (M := M) g
        (gradInnerSmoothBundle (I := I) (M := M) g φ v).oneSubLapClassical := by
  exact gradInnerLaplacianRhs_smooth_of_hessPairing
    (I := I) (M := M) g φ v h_hess

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLp.gradInnerLaplacianRhs_smooth_eq_of_hessPairing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLp.gradInnerLaplacianRhs_smooth_eq_of_hessPairing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLp.gradInnerLaplacianRhs_smooth_eq_of_hessPairing ``Submission.DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLp.gradInnerLaplacianRhs_smooth_eq_of_hessPairing

end BochnerPolarisedLp
end Laplacian
end Analysis
end DifferentialGeometry

end
