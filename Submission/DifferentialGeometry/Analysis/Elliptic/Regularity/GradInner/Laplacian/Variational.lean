import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.GradInner.Laplacian.Rhs.Pairings
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.Hessian.Pairing.LaplacianDomain
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.Hessian.Pairing.Chart
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.Ricci.PairingCLM

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
namespace GradInnerLaplacianVariational

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem

open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLpIdentity
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianRhs
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.HessianPairingLapDom
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.HessianPairingChart
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM

private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

noncomputable def gradInnerLapU
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  gradInnerCLM (I := I) (M := M) g φ
    (u_h - preimageLift (I := I) (M := M) g hu_h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.gradInnerLapU then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.gradInnerLapU"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.gradInnerLapU ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.gradInnerLapU

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma gradInnerLapU_def
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    gradInnerLapU (I := I) (M := M) g φ hu_h =
      gradInnerCLM (I := I) (M := M) g φ
        (u_h - preimageLift (I := I) (M := M) g hu_h) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.gradInnerLapU_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.gradInnerLapU_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.gradInnerLapU_def ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.gradInnerLapU_def

omit [NeZero (Module.finrank ℝ E)] in
lemma gradInnerLapU_eq_sub
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    gradInnerLapU (I := I) (M := M) g φ hu_h =
      gradInnerCLM (I := I) (M := M) g φ u_h -
        gradInnerCLM (I := I) (M := M) g φ
          (preimageLift (I := I) (M := M) g hu_h) := by
  unfold gradInnerLapU
  rw [map_sub]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.gradInnerLapU_eq_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.gradInnerLapU_eq_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.gradInnerLapU_eq_sub ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.gradInnerLapU_eq_sub

noncomputable def gradInnerLaplacianRhs
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  gradInnerCLM (I := I) (M := M) g φ u_h
    - gradInnerCLM (I := I) (M := M) g
        (smoothLaplacianBundle (I := I) (M := M) g φ) u_h
    - gradInnerLapU (I := I) (M := M) g φ hu_h
    - (2 : ℝ) • ricciPairingCLM (I := I) (M := M) g φ u_h
    - (2 : ℝ) • hessPairingLpOnLapDom (I := I) (M := M) g φ
        (laplacianDomainPow_succ_subset_laplacianDomain
          (I := I) (M := M) g 1 hu_h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.gradInnerLaplacianRhs then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.gradInnerLaplacianRhs"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.gradInnerLaplacianRhs ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.gradInnerLaplacianRhs

@[simp] theorem gradInnerLaplacianRhs_def
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    gradInnerLaplacianRhs (I := I) (M := M) g φ hu_h =
      gradInnerCLM (I := I) (M := M) g φ u_h
        - gradInnerCLM (I := I) (M := M) g
            (smoothLaplacianBundle (I := I) (M := M) g φ) u_h
        - gradInnerLapU (I := I) (M := M) g φ hu_h
        - (2 : ℝ) • ricciPairingCLM (I := I) (M := M) g φ u_h
        - (2 : ℝ) • hessPairingLpOnLapDom (I := I) (M := M) g φ
            (laplacianDomainPow_succ_subset_laplacianDomain
              (I := I) (M := M) g 1 hu_h) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.gradInnerLaplacianRhs_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.gradInnerLaplacianRhs_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.gradInnerLaplacianRhs_def ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.gradInnerLaplacianRhs_def

theorem gradInnerLaplacianRhs_explicit
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    gradInnerLaplacianRhs (I := I) (M := M) g φ hu_h =
      - gradInnerCLM (I := I) (M := M) g
            (smoothLaplacianBundle (I := I) (M := M) g φ) u_h
        + gradInnerCLM (I := I) (M := M) g φ
            (preimageLift (I := I) (M := M) g hu_h)
        - (2 : ℝ) • ricciPairingCLM (I := I) (M := M) g φ u_h
        - (2 : ℝ) • hessPairingLpOnLapDom (I := I) (M := M) g φ
            (laplacianDomainPow_succ_subset_laplacianDomain
              (I := I) (M := M) g 1 hu_h) := by
  unfold gradInnerLaplacianRhs
  rw [gradInnerLapU_eq_sub]
  abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.gradInnerLaplacianRhs_explicit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.gradInnerLaplacianRhs_explicit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.gradInnerLaplacianRhs_explicit ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.gradInnerLaplacianRhs_explicit

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem gradInnerCLM_mem_image_laplacianDomain_smooth
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    gradInnerCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) ∈
      Set.image (H1ComplToLp (I := I) (M := M) g)
        (laplacianDomain (I := I) (M := M) g : Set (H1Compl g)) :=
  gradInnerCLM_smoothToH1Compl_mem_image_laplacianDomain
    (I := I) (M := M) g φ v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.gradInnerCLM_mem_image_laplacianDomain_smooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.gradInnerCLM_mem_image_laplacianDomain_smooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.gradInnerCLM_mem_image_laplacianDomain_smooth ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.gradInnerCLM_mem_image_laplacianDomain_smooth

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem gradInnerCLM_mem_image_laplacianDomain_of_preimage
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    {w_lift : H1Compl (I := I) (M := M) g}
    (hw_lift_dom : w_lift ∈ laplacianDomain (I := I) (M := M) g)
    (hw_lift_eq : H1ComplToLp (I := I) (M := M) g w_lift =
      gradInnerCLM (I := I) (M := M) g φ u_h) :
    gradInnerCLM (I := I) (M := M) g φ u_h ∈
      Set.image (H1ComplToLp (I := I) (M := M) g)
        (laplacianDomain (I := I) (M := M) g : Set (H1Compl g)) :=
  ⟨w_lift, hw_lift_dom, hw_lift_eq⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.gradInnerCLM_mem_image_laplacianDomain_of_preimage
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.gradInnerCLM_mem_image_laplacianDomain_of_preimage target :: scope.openDecls } }

theorem gradInnerLaplacianRhs_norm_le
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    ‖gradInnerLaplacianRhs (I := I) (M := M) g φ hu_h‖ ≤
      ‖gradInnerCLM (I := I) (M := M) g φ u_h‖ +
      ‖gradInnerCLM (I := I) (M := M) g
        (smoothLaplacianBundle (I := I) (M := M) g φ) u_h‖ +
      ‖gradInnerLapU (I := I) (M := M) g φ hu_h‖ +
      2 * ‖ricciPairingCLM (I := I) (M := M) g φ u_h‖ +
      2 * ‖hessPairingLpOnLapDom (I := I) (M := M) g φ
        (laplacianDomainPow_succ_subset_laplacianDomain
          (I := I) (M := M) g 1 hu_h)‖ := by
  unfold gradInnerLaplacianRhs
  have hstep1 := norm_sub_le
    (gradInnerCLM (I := I) (M := M) g φ u_h
      - gradInnerCLM (I := I) (M := M) g
          (smoothLaplacianBundle (I := I) (M := M) g φ) u_h
      - gradInnerLapU (I := I) (M := M) g φ hu_h
      - (2 : ℝ) • ricciPairingCLM (I := I) (M := M) g φ u_h)
    ((2 : ℝ) • hessPairingLpOnLapDom (I := I) (M := M) g φ
      (laplacianDomainPow_succ_subset_laplacianDomain (I := I) (M := M) g 1 hu_h))
  have hstep2 := norm_sub_le
    (gradInnerCLM (I := I) (M := M) g φ u_h
      - gradInnerCLM (I := I) (M := M) g
          (smoothLaplacianBundle (I := I) (M := M) g φ) u_h
      - gradInnerLapU (I := I) (M := M) g φ hu_h)
    ((2 : ℝ) • ricciPairingCLM (I := I) (M := M) g φ u_h)
  have hstep3 := norm_sub_le
    (gradInnerCLM (I := I) (M := M) g φ u_h
      - gradInnerCLM (I := I) (M := M) g
          (smoothLaplacianBundle (I := I) (M := M) g φ) u_h)
    (gradInnerLapU (I := I) (M := M) g φ hu_h)
  have hstep4 := norm_sub_le (gradInnerCLM (I := I) (M := M) g φ u_h)
    (gradInnerCLM (I := I) (M := M) g
      (smoothLaplacianBundle (I := I) (M := M) g φ) u_h)
  have h_smul_ricci :
      ‖(2 : ℝ) • ricciPairingCLM (I := I) (M := M) g φ u_h‖ =
      2 * ‖ricciPairingCLM (I := I) (M := M) g φ u_h‖ := by
    rw [norm_smul]; simp
  have h_smul_hess :
      ‖(2 : ℝ) • hessPairingLpOnLapDom (I := I) (M := M) g φ
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)‖ =
      2 * ‖hessPairingLpOnLapDom (I := I) (M := M) g φ
        (laplacianDomainPow_succ_subset_laplacianDomain
          (I := I) (M := M) g 1 hu_h)‖ := by
    rw [norm_smul]; simp
  linarith [hstep1, hstep2, hstep3, hstep4, h_smul_ricci, h_smul_hess]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.gradInnerLaplacianRhs_norm_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.gradInnerLaplacianRhs_norm_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.gradInnerLaplacianRhs_norm_le ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.gradInnerLaplacianRhs_norm_le

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma gradInnerCLM_smoothToH1Compl_eq_smoothToLp
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    gradInnerCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) =
      smoothToLp (I := I) (M := M) g
        (gradInnerSmoothBundle (I := I) (M := M) g φ v) := by
  rw [gradInnerCLM_smoothToH1Compl]
  exact gradInnerSmooth_eq_smoothToLp_bundle (I := I) (M := M) g φ v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.gradInnerCLM_smoothToH1Compl_eq_smoothToLp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.gradInnerCLM_smoothToH1Compl_eq_smoothToLp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.gradInnerCLM_smoothToH1Compl_eq_smoothToLp ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.gradInnerCLM_smoothToH1Compl_eq_smoothToLp

omit [NeZero (Module.finrank ℝ E)] in
lemma ricciPairingCLM_smoothToH1Compl_eq_smoothToLp
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    ricciPairingCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) =
      smoothToLp (I := I) (M := M) g
        (smoothRicciPairingBundle (I := I) (M := M) g φ v) := by
  rw [ricciPairingCLM_smoothToH1Compl]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.ricciPairingCLM_smoothToH1Compl_eq_smoothToLp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.ricciPairingCLM_smoothToH1Compl_eq_smoothToLp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.ricciPairingCLM_smoothToH1Compl_eq_smoothToLp ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.ricciPairingCLM_smoothToH1Compl_eq_smoothToLp

noncomputable def smoothGradInnerPreimage
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    H1Compl (I := I) (M := M) g :=
  smoothToH1Compl (I := I) (M := M) g
    (gradInnerSmoothBundle (I := I) (M := M) g φ v)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.smoothGradInnerPreimage then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.smoothGradInnerPreimage"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.smoothGradInnerPreimage ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.smoothGradInnerPreimage

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem smoothGradInnerPreimage_mem_laplacianDomain
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    smoothGradInnerPreimage (I := I) (M := M) g φ v ∈
      laplacianDomain (I := I) (M := M) g := by
  unfold smoothGradInnerPreimage
  exact smoothToH1Compl_mem_laplacianDomain
    (I := I) (M := M)
    (gradInnerSmoothBundle (I := I) (M := M) g φ v)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.smoothGradInnerPreimage_mem_laplacianDomain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.smoothGradInnerPreimage_mem_laplacianDomain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.smoothGradInnerPreimage_mem_laplacianDomain ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.smoothGradInnerPreimage_mem_laplacianDomain

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem H1ComplToLp_smoothGradInnerPreimage
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    H1ComplToLp (I := I) (M := M) g
        (smoothGradInnerPreimage (I := I) (M := M) g φ v) =
      gradInnerCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) := by
  unfold smoothGradInnerPreimage
  rw [H1ComplToLp_smoothToH1Compl]
  rw [gradInnerCLM_smoothToH1Compl_eq_smoothToLp]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.H1ComplToLp_smoothGradInnerPreimage then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.H1ComplToLp_smoothGradInnerPreimage"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.H1ComplToLp_smoothGradInnerPreimage ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.H1ComplToLp_smoothGradInnerPreimage

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem gradInnerCLM_eq_H1ComplToLp_smoothGradInnerPreimage
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    gradInnerCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) =
      H1ComplToLp (I := I) (M := M) g
        (smoothGradInnerPreimage (I := I) (M := M) g φ v) := by
  rw [H1ComplToLp_smoothGradInnerPreimage]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.gradInnerCLM_eq_H1ComplToLp_smoothGradInnerPreimage then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.gradInnerCLM_eq_H1ComplToLp_smoothGradInnerPreimage"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.gradInnerCLM_eq_H1ComplToLp_smoothGradInnerPreimage ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.gradInnerCLM_eq_H1ComplToLp_smoothGradInnerPreimage

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem exists_laplacianDomain_preimage_gradInnerCLM_smoothToH1Compl
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    ∃ w_lift : H1Compl (I := I) (M := M) g,
      w_lift ∈ laplacianDomain (I := I) (M := M) g ∧
      H1ComplToLp (I := I) (M := M) g w_lift =
        gradInnerCLM (I := I) (M := M) g φ
          (smoothToH1Compl (I := I) (M := M) g v) := by
  refine ⟨smoothGradInnerPreimage (I := I) (M := M) g φ v, ?_, ?_⟩
  · exact smoothGradInnerPreimage_mem_laplacianDomain (I := I) (M := M) g φ v
  · exact H1ComplToLp_smoothGradInnerPreimage (I := I) (M := M) g φ v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.exists_laplacianDomain_preimage_gradInnerCLM_smoothToH1Compl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.exists_laplacianDomain_preimage_gradInnerCLM_smoothToH1Compl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.exists_laplacianDomain_preimage_gradInnerCLM_smoothToH1Compl ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.exists_laplacianDomain_preimage_gradInnerCLM_smoothToH1Compl

theorem gradInnerCLM_eq_H1ComplToLp_resolvent_of_variational
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (hvar_id :
      gradInnerCLM (I := I) (M := M) g φ u_h =
        H1ComplToLp (I := I) (M := M) g
          (resolvent (I := I) (M := M) g
            (gradInnerLaplacianRhs
              (I := I) (M := M) g φ hu_h))) :
    gradInnerCLM (I := I) (M := M) g φ u_h ∈
      Set.image (H1ComplToLp (I := I) (M := M) g)
        (laplacianDomain (I := I) (M := M) g : Set (H1Compl g)) := by
  classical
  refine ⟨resolvent (I := I) (M := M) g
    (gradInnerLaplacianRhs (I := I) (M := M) g φ hu_h),
    ?_, hvar_id.symm⟩
  exact (laplacianDomain_mem_iff (I := I) (M := M) g).mpr
    ⟨gradInnerLaplacianRhs (I := I) (M := M) g φ hu_h, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.gradInnerCLM_eq_H1ComplToLp_resolvent_of_variational then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.gradInnerCLM_eq_H1ComplToLp_resolvent_of_variational"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.gradInnerCLM_eq_H1ComplToLp_resolvent_of_variational ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.gradInnerCLM_eq_H1ComplToLp_resolvent_of_variational

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem smoothGradInnerPreimage_eq_resolvent
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    smoothGradInnerPreimage (I := I) (M := M) g φ v =
      resolvent (I := I) (M := M) g
        (smoothToLp (I := I) (M := M) g
          (gradInnerSmoothBundle (I := I) (M := M) g φ v).oneSubLapClassical) := by
  unfold smoothGradInnerPreimage
  exact smoothToH1Compl_eq_resolvent_oneSubLap (I := I) (M := M)
    (gradInnerSmoothBundle (I := I) (M := M) g φ v)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.smoothGradInnerPreimage_eq_resolvent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.smoothGradInnerPreimage_eq_resolvent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.smoothGradInnerPreimage_eq_resolvent ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.smoothGradInnerPreimage_eq_resolvent

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem gradInnerCLM_smoothToH1Compl_eq_H1ComplToLp_resolvent
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    gradInnerCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) =
      H1ComplToLp (I := I) (M := M) g
        (resolvent (I := I) (M := M) g
          (smoothToLp (I := I) (M := M) g
            (gradInnerSmoothBundle (I := I) (M := M) g φ v).oneSubLapClassical)) := by
  rw [gradInnerCLM_eq_H1ComplToLp_smoothGradInnerPreimage]
  rw [smoothGradInnerPreimage_eq_resolvent]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.gradInnerCLM_smoothToH1Compl_eq_H1ComplToLp_resolvent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.gradInnerCLM_smoothToH1Compl_eq_H1ComplToLp_resolvent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.gradInnerCLM_smoothToH1Compl_eq_H1ComplToLp_resolvent ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.gradInnerCLM_smoothToH1Compl_eq_H1ComplToLp_resolvent

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem gradInnerCLM_smoothToH1Compl_eq_resolventL2
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    gradInnerCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) =
      resolventL2 (I := I) (M := M) g
        (smoothToLp (I := I) (M := M) g
          (gradInnerSmoothBundle (I := I) (M := M) g φ v).oneSubLapClassical) := by
  rw [gradInnerCLM_smoothToH1Compl_eq_H1ComplToLp_resolvent]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.gradInnerCLM_smoothToH1Compl_eq_resolventL2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.gradInnerCLM_smoothToH1Compl_eq_resolventL2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.gradInnerCLM_smoothToH1Compl_eq_resolventL2 ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.gradInnerCLM_smoothToH1Compl_eq_resolventL2

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem hessPairingChart_polar
    (g : SmoothRiemannianMetric I M) (φ v : C^∞⟮I, M; ℝ⟯) (b : M) :
    4 * hessPairingChart (I := I) g φ v b =
      chartHessFrobeniusSq (I := I) g (fun x : M => φ x + v x) b -
        chartHessFrobeniusSq (I := I) g (fun x : M => φ x - v x) b := by
  rw [hessPairingChart_def]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.hessPairingChart_polar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.hessPairingChart_polar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.hessPairingChart_polar ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.hessPairingChart_polar

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem chartHessFrobeniusSq_polar_eq_hessPairing
    (g : SmoothRiemannianMetric I M) (φ v : C^∞⟮I, M; ℝ⟯) (b : M) :
    chartHessFrobeniusSq (I := I) g (fun x : M => φ x + v x) b -
        chartHessFrobeniusSq (I := I) g (fun x : M => φ x - v x) b =
      4 * hessPairingChart (I := I) g φ v b :=
  (hessPairingChart_polar (I := I) (M := M) g φ v b).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.chartHessFrobeniusSq_polar_eq_hessPairing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.chartHessFrobeniusSq_polar_eq_hessPairing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.chartHessFrobeniusSq_polar_eq_hessPairing ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.chartHessFrobeniusSq_polar_eq_hessPairing

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M] in
theorem g_inner_polar
    (g : SmoothRiemannianMetric I M) (b : M) (u w : TangentSpace I b) :
    g.inner b (u + w) (u + w) - g.inner b (u - w) (u - w) =
      4 * g.inner b u w := by
  classical
  have h_inner_sym : g.inner b w u = g.inner b u w := g.symm b _ _
  have hp1 : g.inner b (u + w) (u + w) =
      g.inner b u u + g.inner b u w + g.inner b w u + g.inner b w w := by
    rw [ContinuousLinearMap.map_add (g.inner b) u w]
    rw [add_apply]
    rw [(g.inner b u).map_add, (g.inner b w).map_add]
    ring
  have hp2 : g.inner b (u - w) (u - w) =
      g.inner b u u - g.inner b u w - g.inner b w u + g.inner b w w := by
    rw [ContinuousLinearMap.map_sub (g.inner b) u w]
    rw [sub_apply]
    rw [(g.inner b u).map_sub, (g.inner b w).map_sub]
    ring
  rw [hp1, hp2, h_inner_sym]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.g_inner_polar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.g_inner_polar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.g_inner_polar ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.g_inner_polar

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem ricciTensor_polar
    (g : SmoothRiemannianMetric I M) (b : M) (u w : TangentSpace I b) :
    ricciTensor (I := I) g b (u + w) (u + w) -
        ricciTensor (I := I) g b (u - w) (u - w) =
      4 * ricciTensor (I := I) g b u w := by
  classical
  have h_sym : ricciTensor (I := I) g b w u =
      ricciTensor (I := I) g b u w :=
    ricciTensor_symm (I := I) g b w u
  have hp1 : ricciTensor (I := I) g b (u + w) (u + w) =
      ricciTensor (I := I) g b u u + ricciTensor (I := I) g b u w +
        ricciTensor (I := I) g b w u + ricciTensor (I := I) g b w w := by
    rw [ContinuousLinearMap.map_add (ricciTensor (I := I) g b) u w]
    rw [add_apply]
    rw [(ricciTensor (I := I) g b u).map_add,
      (ricciTensor (I := I) g b w).map_add]
    ring
  have hp2 : ricciTensor (I := I) g b (u - w) (u - w) =
      ricciTensor (I := I) g b u u - ricciTensor (I := I) g b u w -
        ricciTensor (I := I) g b w u + ricciTensor (I := I) g b w w := by
    rw [ContinuousLinearMap.map_sub (ricciTensor (I := I) g b) u w]
    rw [sub_apply]
    rw [(ricciTensor (I := I) g b u).map_sub,
      (ricciTensor (I := I) g b w).map_sub]
    ring
  rw [hp1, hp2, h_sym]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.ricciTensor_polar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.ricciTensor_polar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.ricciTensor_polar ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.ricciTensor_polar

theorem gradInnerCLM_smoothToH1Compl_eq_resolvent_of_rhs_identification
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_identify :
      gradInnerLaplacianRhs (I := I) (M := M) g φ
          (smoothToH1Compl_mem_laplacianDomainPow_two (I := I) (M := M) g v) =
        smoothToLp (I := I) (M := M) g
          (gradInnerSmoothBundle (I := I) (M := M) g φ v).oneSubLapClassical) :
    gradInnerCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) =
      H1ComplToLp (I := I) (M := M) g
        (resolvent (I := I) (M := M) g
          (gradInnerLaplacianRhs (I := I) (M := M) g φ
            (smoothToH1Compl_mem_laplacianDomainPow_two
              (I := I) (M := M) g v))) := by
  rw [gradInnerCLM_smoothToH1Compl_eq_H1ComplToLp_resolvent]
  rw [h_identify]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.gradInnerCLM_smoothToH1Compl_eq_resolvent_of_rhs_identification then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.gradInnerCLM_smoothToH1Compl_eq_resolvent_of_rhs_identification"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.gradInnerCLM_smoothToH1Compl_eq_resolvent_of_rhs_identification ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational.gradInnerCLM_smoothToH1Compl_eq_resolvent_of_rhs_identification

end GradInnerLaplacianVariational
end Laplacian
end Analysis
end DifferentialGeometry

end
