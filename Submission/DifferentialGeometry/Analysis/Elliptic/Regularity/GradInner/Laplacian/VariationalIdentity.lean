import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.GradInner.Laplacian.Variational

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.MeasureTheory _root_.Filter _root_.Topology _root_.Function
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.Matrix _root_.InnerProductSpace _root_.BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace GradInnerLaplacianDomain

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
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational

private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDomain.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDomain.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDomain.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDomain.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDomain.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDomain.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDomain.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDomain.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDomain.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDomain.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDomain.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDomain.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

noncomputable def gradInnerLaplacianPreimage
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    H1Compl (I := I) (M := M) g :=
  resolvent (I := I) (M := M) g
    (gradInnerLaplacianRhs (I := I) (M := M) g φ hu_h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDomain.gradInnerLaplacianPreimage then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDomain.gradInnerLaplacianPreimage"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDomain.gradInnerLaplacianPreimage ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDomain.gradInnerLaplacianPreimage

theorem gradInnerLaplacianPreimage_mem_laplacianDomain
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    gradInnerLaplacianPreimage (I := I) (M := M) g φ hu_h ∈
      laplacianDomain (I := I) (M := M) g := by
  unfold gradInnerLaplacianPreimage
  exact (laplacianDomain_mem_iff (I := I) (M := M) g).mpr
    ⟨gradInnerLaplacianRhs (I := I) (M := M) g φ hu_h, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDomain.gradInnerLaplacianPreimage_mem_laplacianDomain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDomain.gradInnerLaplacianPreimage_mem_laplacianDomain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDomain.gradInnerLaplacianPreimage_mem_laplacianDomain ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDomain.gradInnerLaplacianPreimage_mem_laplacianDomain

theorem gradInnerCLM_mem_image_laplacianDomain_of_variational
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (hvar_id :
      gradInnerCLM (I := I) (M := M) g φ u_h =
        H1ComplToLp (I := I) (M := M) g
          (gradInnerLaplacianPreimage (I := I) (M := M) g φ hu_h)) :
    gradInnerCLM (I := I) (M := M) g φ u_h ∈
      Set.image (H1ComplToLp (I := I) (M := M) g)
        (laplacianDomain (I := I) (M := M) g : Set (H1Compl g)) :=
  ⟨gradInnerLaplacianPreimage (I := I) (M := M) g φ hu_h,
    gradInnerLaplacianPreimage_mem_laplacianDomain
      (I := I) (M := M) g φ hu_h, hvar_id.symm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDomain.gradInnerCLM_mem_image_laplacianDomain_of_variational then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDomain.gradInnerCLM_mem_image_laplacianDomain_of_variational"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDomain.gradInnerCLM_mem_image_laplacianDomain_of_variational ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDomain.gradInnerCLM_mem_image_laplacianDomain_of_variational

theorem gradInnerLaplacianPreimage_eq_resolvent
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    gradInnerLaplacianPreimage (I := I) (M := M) g φ hu_h =
      resolvent (I := I) (M := M) g
        (gradInnerLaplacianRhs
          (I := I) (M := M) g φ hu_h) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDomain.gradInnerLaplacianPreimage_eq_resolvent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDomain.gradInnerLaplacianPreimage_eq_resolvent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDomain.gradInnerLaplacianPreimage_eq_resolvent ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDomain.gradInnerLaplacianPreimage_eq_resolvent

theorem variational_identity_implies_mem_image
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
        (laplacianDomain (I := I) (M := M) g : Set (H1Compl g)) :=
  gradInnerCLM_eq_H1ComplToLp_resolvent_of_variational
    (I := I) (M := M) g φ hu_h hvar_id

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDomain.variational_identity_implies_mem_image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDomain.variational_identity_implies_mem_image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDomain.variational_identity_implies_mem_image ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDomain.variational_identity_implies_mem_image

theorem gradInnerCLM_smoothToH1Compl_eq_resolventL2_of_rhs_identification
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_identify : gradInnerLaplacianRhs (I := I) (M := M) g φ
          (smoothToH1Compl_mem_laplacianDomainPow_two (I := I) (M := M) g v) =
        smoothToLp (I := I) (M := M) g
          (gradInnerSmoothBundle (I := I) (M := M) g φ v).oneSubLapClassical) :
    gradInnerCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) =
      H1ComplToLp (I := I) (M := M) g
        (resolvent (I := I) (M := M) g
          (gradInnerLaplacianRhs (I := I) (M := M) g φ
            (smoothToH1Compl_mem_laplacianDomainPow_two
              (I := I) (M := M) g v))) :=
  gradInnerCLM_smoothToH1Compl_eq_resolvent_of_rhs_identification
    (I := I) (M := M) g φ v h_identify

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDomain.gradInnerCLM_smoothToH1Compl_eq_resolventL2_of_rhs_identification then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDomain.gradInnerCLM_smoothToH1Compl_eq_resolventL2_of_rhs_identification"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDomain.gradInnerCLM_smoothToH1Compl_eq_resolventL2_of_rhs_identification ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDomain.gradInnerCLM_smoothToH1Compl_eq_resolventL2_of_rhs_identification

theorem gradInnerCLM_smoothToH1Compl_mem_image_laplacianDomain_of_rhs_identification
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_identify : gradInnerLaplacianRhs (I := I) (M := M) g φ
          (smoothToH1Compl_mem_laplacianDomainPow_two (I := I) (M := M) g v) =
        smoothToLp (I := I) (M := M) g
          (gradInnerSmoothBundle (I := I) (M := M) g φ v).oneSubLapClassical) :
    gradInnerCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) ∈
      Set.image (H1ComplToLp (I := I) (M := M) g)
        (laplacianDomain (I := I) (M := M) g : Set (H1Compl g)) :=
  variational_identity_implies_mem_image (I := I) (M := M) g φ
    (smoothToH1Compl_mem_laplacianDomainPow_two (I := I) (M := M) g v)
    (gradInnerCLM_smoothToH1Compl_eq_resolventL2_of_rhs_identification
      (I := I) (M := M) g φ v h_identify)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDomain.gradInnerCLM_smoothToH1Compl_mem_image_laplacianDomain_of_rhs_identification then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDomain.gradInnerCLM_smoothToH1Compl_mem_image_laplacianDomain_of_rhs_identification"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDomain.gradInnerCLM_smoothToH1Compl_mem_image_laplacianDomain_of_rhs_identification ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDomain.gradInnerCLM_smoothToH1Compl_mem_image_laplacianDomain_of_rhs_identification

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem gradInnerCLM_smoothCase_mem_image_laplacianDomain
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    gradInnerCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) ∈
      Set.image (H1ComplToLp (I := I) (M := M) g)
        (laplacianDomain (I := I) (M := M) g : Set (H1Compl g)) :=
  gradInnerCLM_mem_image_laplacianDomain_smooth (I := I) (M := M) g φ v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDomain.gradInnerCLM_smoothCase_mem_image_laplacianDomain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDomain.gradInnerCLM_smoothCase_mem_image_laplacianDomain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDomain.gradInnerCLM_smoothCase_mem_image_laplacianDomain ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDomain.gradInnerCLM_smoothCase_mem_image_laplacianDomain

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem mem_image_laplacianDomain_iff_smoothMulH1Compl_mem_pow_two
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    gradInnerCLM (I := I) (M := M) g φ u_h ∈
      Set.image (H1ComplToLp (I := I) (M := M) g)
        (laplacianDomain (I := I) (M := M) g : Set (H1Compl g)) ↔
      smoothMulH1Compl (I := I) (M := M) g φ u_h ∈
        laplacianDomainPow (I := I) (M := M) g 2 := by
  rw [← smoothMulH1Compl_mem_pow_two_iff_gradInnerCLM_mem_image
    (I := I) (M := M) g φ hu_h]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDomain.mem_image_laplacianDomain_iff_smoothMulH1Compl_mem_pow_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDomain.mem_image_laplacianDomain_iff_smoothMulH1Compl_mem_pow_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDomain.mem_image_laplacianDomain_iff_smoothMulH1Compl_mem_pow_two ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDomain.mem_image_laplacianDomain_iff_smoothMulH1Compl_mem_pow_two

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem gradInnerCLM_mem_image_laplacianDomain_of_iteratedClosure
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_sM : smoothMulH1Compl (I := I) (M := M) g φ u_h ∈
      laplacianDomainPow (I := I) (M := M) g 2) :
    gradInnerCLM (I := I) (M := M) g φ u_h ∈
      Set.image (H1ComplToLp (I := I) (M := M) g)
        (laplacianDomain (I := I) (M := M) g : Set (H1Compl g)) :=
  gradInnerCLM_mem_image_of_smoothMulH1Compl_mem_pow_two
    (I := I) (M := M) g φ hu_h h_sM

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDomain.gradInnerCLM_mem_image_laplacianDomain_of_iteratedClosure then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDomain.gradInnerCLM_mem_image_laplacianDomain_of_iteratedClosure"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDomain.gradInnerCLM_mem_image_laplacianDomain_of_iteratedClosure ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDomain.gradInnerCLM_mem_image_laplacianDomain_of_iteratedClosure

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem smoothMulH1Compl_mem_pow_two_iff_gradInnerCLM_mem_image_laplacianDomain
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    smoothMulH1Compl (I := I) (M := M) g φ u_h ∈
      laplacianDomainPow (I := I) (M := M) g 2 ↔
    gradInnerCLM (I := I) (M := M) g φ u_h ∈
      Set.image (H1ComplToLp (I := I) (M := M) g)
        (laplacianDomain (I := I) (M := M) g : Set (H1Compl g)) :=
  smoothMulH1Compl_mem_pow_two_iff_gradInnerCLM_mem_image
    (I := I) (M := M) g φ hu_h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDomain.smoothMulH1Compl_mem_pow_two_iff_gradInnerCLM_mem_image_laplacianDomain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDomain.smoothMulH1Compl_mem_pow_two_iff_gradInnerCLM_mem_image_laplacianDomain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDomain.smoothMulH1Compl_mem_pow_two_iff_gradInnerCLM_mem_image_laplacianDomain ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDomain.smoothMulH1Compl_mem_pow_two_iff_gradInnerCLM_mem_image_laplacianDomain

theorem smoothMulH1Compl_mem_pow_two_of_variational_identity
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (hvar_id :
      gradInnerCLM (I := I) (M := M) g φ u_h =
        H1ComplToLp (I := I) (M := M) g
          (resolvent (I := I) (M := M) g
            (gradInnerLaplacianRhs
              (I := I) (M := M) g φ hu_h))) :
    smoothMulH1Compl (I := I) (M := M) g φ u_h ∈
      laplacianDomainPow (I := I) (M := M) g 2 := by
  have h_image := variational_identity_implies_mem_image
    (I := I) (M := M) g φ hu_h hvar_id
  exact (smoothMulH1Compl_mem_pow_two_iff_gradInnerCLM_mem_image_laplacianDomain
    (I := I) (M := M) g φ hu_h).mpr h_image

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDomain.smoothMulH1Compl_mem_pow_two_of_variational_identity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDomain.smoothMulH1Compl_mem_pow_two_of_variational_identity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDomain.smoothMulH1Compl_mem_pow_two_of_variational_identity ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDomain.smoothMulH1Compl_mem_pow_two_of_variational_identity

end GradInnerLaplacianDomain
end Laplacian
end Analysis
end DifferentialGeometry

end
