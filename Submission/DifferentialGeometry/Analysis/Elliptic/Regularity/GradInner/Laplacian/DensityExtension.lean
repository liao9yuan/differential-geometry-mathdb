import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.GradInner.Laplacian.Smooth

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
namespace GradInnerLaplacianDensityExtension

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
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDomain
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmooth

private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDensityExtension.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDensityExtension.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDensityExtension.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDensityExtension.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDensityExtension.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDensityExtension.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDensityExtension.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDensityExtension.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDensityExtension.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDensityExtension.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDensityExtension.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDensityExtension.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

theorem gradInnerCLM_eq_H1ComplToLp_resolvent_of_smooth_approximation
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
            (h_smooth_seq n)).oneSubLapClassical) :
    gradInnerCLM (I := I) (M := M) g φ u_h =
      H1ComplToLp (I := I) (M := M) g
        (resolvent (I := I) (M := M) g
          (gradInnerLaplacianRhs
            (I := I) (M := M) g φ hu_h)) := by
  classical
  have h_LHS_convergence : _root_.Filter.Tendsto
      (fun n => gradInnerCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g (h_smooth_seq n)))
      atTop (𝓝 (gradInnerCLM (I := I) (M := M) g φ u_h)) := by
    exact ((gradInnerCLM (I := I) (M := M) g φ).continuous.tendsto _).comp
      h_convergence_H1Compl
  have h_RHS_convergence : _root_.Filter.Tendsto
      (fun n => H1ComplToLp (I := I) (M := M) g
        (resolvent (I := I) (M := M) g
          (gradInnerLaplacianRhs (I := I) (M := M) g φ
            (smoothToH1Compl_mem_laplacianDomainPow_two
              (I := I) (M := M) g (h_smooth_seq n)))))
      atTop (𝓝 (H1ComplToLp (I := I) (M := M) g
        (resolvent (I := I) (M := M) g
          (gradInnerLaplacianRhs
            (I := I) (M := M) g φ hu_h)))) := by
    have h_resolvent_cont :
        Continuous (resolvent (I := I) (M := M) g) :=
      (resolvent (I := I) (M := M) g).continuous
    have h_H1ComplToLp_cont :
        Continuous (H1ComplToLp (I := I) (M := M) g) :=
      (H1ComplToLp (I := I) (M := M) g).continuous
    have h_composition_cont :
        Continuous (fun f => H1ComplToLp (I := I) (M := M) g
          (resolvent (I := I) (M := M) g f)) :=
      h_H1ComplToLp_cont.comp h_resolvent_cont
    exact (h_composition_cont.tendsto _).comp h_convergence_candidate
  have h_smooth_eq : ∀ n,
      gradInnerCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g (h_smooth_seq n)) =
      H1ComplToLp (I := I) (M := M) g
        (resolvent (I := I) (M := M) g
          (gradInnerLaplacianRhs (I := I) (M := M) g φ
            (smoothToH1Compl_mem_laplacianDomainPow_two
              (I := I) (M := M) g (h_smooth_seq n)))) := fun n =>
    gradInnerCLM_smoothToH1Compl_eq_resolvent_of_rhs_identification
      (I := I) (M := M) g φ (h_smooth_seq n) (h_smooth_identity n)
  have h_seq_eq : (fun n => gradInnerCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g (h_smooth_seq n))) =
      (fun n => H1ComplToLp (I := I) (M := M) g
        (resolvent (I := I) (M := M) g
          (gradInnerLaplacianRhs (I := I) (M := M) g φ
            (smoothToH1Compl_mem_laplacianDomainPow_two
              (I := I) (M := M) g (h_smooth_seq n))))) := by
    funext n
    exact h_smooth_eq n
  rw [h_seq_eq] at h_LHS_convergence
  exact tendsto_nhds_unique h_LHS_convergence h_RHS_convergence

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDensityExtension.gradInnerCLM_eq_H1ComplToLp_resolvent_of_smooth_approximation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDensityExtension.gradInnerCLM_eq_H1ComplToLp_resolvent_of_smooth_approximation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDensityExtension.gradInnerCLM_eq_H1ComplToLp_resolvent_of_smooth_approximation ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDensityExtension.gradInnerCLM_eq_H1ComplToLp_resolvent_of_smooth_approximation

theorem gradInnerCLM_mem_image_laplacianDomain_of_smooth_approximation
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
            (h_smooth_seq n)).oneSubLapClassical) :
    gradInnerCLM (I := I) (M := M) g φ u_h ∈
      Set.image (H1ComplToLp (I := I) (M := M) g)
        (laplacianDomain (I := I) (M := M) g : Set (H1Compl g)) := by
  classical
  refine ⟨resolvent (I := I) (M := M) g
    (gradInnerLaplacianRhs (I := I) (M := M) g φ hu_h),
    ?_, ?_⟩
  · exact (laplacianDomain_mem_iff (I := I) (M := M) g).mpr
      ⟨gradInnerLaplacianRhs (I := I) (M := M) g φ hu_h, rfl⟩
  · exact (gradInnerCLM_eq_H1ComplToLp_resolvent_of_smooth_approximation
      (I := I) (M := M) g φ hu_h h_smooth_seq h_convergence_H1Compl
      h_convergence_candidate h_smooth_identity).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDensityExtension.gradInnerCLM_mem_image_laplacianDomain_of_smooth_approximation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDensityExtension.gradInnerCLM_mem_image_laplacianDomain_of_smooth_approximation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDensityExtension.gradInnerCLM_mem_image_laplacianDomain_of_smooth_approximation ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDensityExtension.gradInnerCLM_mem_image_laplacianDomain_of_smooth_approximation

theorem smoothMulH1Compl_mem_pow_two_of_smooth_approximation
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
            (h_smooth_seq n)).oneSubLapClassical) :
    smoothMulH1Compl (I := I) (M := M) g φ u_h ∈
      laplacianDomainPow (I := I) (M := M) g 2 := by
  classical
  rw [smoothMulH1Compl_mem_pow_two_iff_gradInnerCLM_mem_image
    (I := I) (M := M) g φ hu_h]
  exact gradInnerCLM_mem_image_laplacianDomain_of_smooth_approximation
    (I := I) (M := M) g φ hu_h h_smooth_seq h_convergence_H1Compl
    h_convergence_candidate h_smooth_identity

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDensityExtension.smoothMulH1Compl_mem_pow_two_of_smooth_approximation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDensityExtension.smoothMulH1Compl_mem_pow_two_of_smooth_approximation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDensityExtension.smoothMulH1Compl_mem_pow_two_of_smooth_approximation ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDensityExtension.smoothMulH1Compl_mem_pow_two_of_smooth_approximation

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem gradInnerCLM_smoothSeq_convergence
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (h_smooth_seq : ℕ → SmoothScalar g)
    (h_convergence_H1Compl : _root_.Filter.Tendsto
      (fun n => smoothToH1Compl (I := I) (M := M) g (h_smooth_seq n))
      _root_.Filter.atTop (𝓝 u_h)) :
    _root_.Filter.Tendsto
      (fun n => gradInnerCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g (h_smooth_seq n)))
      atTop (𝓝 (gradInnerCLM (I := I) (M := M) g φ u_h)) :=
  ((gradInnerCLM (I := I) (M := M) g φ).continuous.tendsto _).comp h_convergence_H1Compl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDensityExtension.gradInnerCLM_smoothSeq_convergence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDensityExtension.gradInnerCLM_smoothSeq_convergence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDensityExtension.gradInnerCLM_smoothSeq_convergence ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDensityExtension.gradInnerCLM_smoothSeq_convergence

omit [NeZero (Module.finrank ℝ E)] in
theorem ricciPairingCLM_smoothSeq_convergence
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (h_smooth_seq : ℕ → SmoothScalar g)
    (h_convergence_H1Compl : _root_.Filter.Tendsto
      (fun n => smoothToH1Compl (I := I) (M := M) g (h_smooth_seq n))
      _root_.Filter.atTop (𝓝 u_h)) :
    _root_.Filter.Tendsto
      (fun n => ricciPairingCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g (h_smooth_seq n)))
      atTop (𝓝 (ricciPairingCLM (I := I) (M := M) g φ u_h)) :=
  ((ricciPairingCLM (I := I) (M := M) g φ).continuous.tendsto _).comp h_convergence_H1Compl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDensityExtension.ricciPairingCLM_smoothSeq_convergence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDensityExtension.ricciPairingCLM_smoothSeq_convergence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDensityExtension.ricciPairingCLM_smoothSeq_convergence ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDensityExtension.ricciPairingCLM_smoothSeq_convergence

end GradInnerLaplacianDensityExtension
end Laplacian
end Analysis
end DifferentialGeometry

end
