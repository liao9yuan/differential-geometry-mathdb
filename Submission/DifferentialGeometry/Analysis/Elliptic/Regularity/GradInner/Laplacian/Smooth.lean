import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.Bochner.PolarisedLp

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
namespace GradInnerLaplacianSmooth

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
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLp

private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmooth.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmooth.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmooth.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmooth.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmooth.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmooth.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmooth.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmooth.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmooth.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmooth.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmooth.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmooth.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

theorem gradInnerCLM_eq_H1ComplToLp_resolvent_smooth_of_hessHypothesis
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_hess :
      hessPairingLpOnLapDom (I := I) (M := M) g φ
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1
            (smoothToH1Compl_mem_laplacianDomainPow_two
              (I := I) (M := M) g v)) =
        hessPairingSmoothLp (I := I) (M := M) g φ v) :
    gradInnerCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) =
      H1ComplToLp (I := I) (M := M) g
        (resolvent (I := I) (M := M) g
          (gradInnerLaplacianRhs (I := I) (M := M) g φ
            (smoothToH1Compl_mem_laplacianDomainPow_two
              (I := I) (M := M) g v))) :=
  gradInnerCLM_smoothToH1Compl_eq_resolvent_of_rhs_identification (I := I) (M := M) g φ v
    (gradInnerLaplacianRhs_smooth_eq_of_hessPairing
      (I := I) (M := M) g φ v h_hess)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmooth.gradInnerCLM_eq_H1ComplToLp_resolvent_smooth_of_hessHypothesis then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmooth.gradInnerCLM_eq_H1ComplToLp_resolvent_smooth_of_hessHypothesis"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmooth.gradInnerCLM_eq_H1ComplToLp_resolvent_smooth_of_hessHypothesis ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmooth.gradInnerCLM_eq_H1ComplToLp_resolvent_smooth_of_hessHypothesis

theorem gradInnerCLM_smoothToH1Compl_mem_image_laplacianDomain_of_hessHypothesis
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_hess :
      hessPairingLpOnLapDom (I := I) (M := M) g φ
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1
            (smoothToH1Compl_mem_laplacianDomainPow_two
              (I := I) (M := M) g v)) =
        hessPairingSmoothLp (I := I) (M := M) g φ v) :
    gradInnerCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) ∈
      Set.image (H1ComplToLp (I := I) (M := M) g)
        (laplacianDomain (I := I) (M := M) g : Set (H1Compl g)) :=
  gradInnerCLM_smoothToH1Compl_mem_image_laplacianDomain_of_rhs_identification
    (I := I) (M := M) g φ v
    (gradInnerLaplacianRhs_smooth_eq_of_hessPairing
      (I := I) (M := M) g φ v h_hess)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmooth.gradInnerCLM_smoothToH1Compl_mem_image_laplacianDomain_of_hessHypothesis then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmooth.gradInnerCLM_smoothToH1Compl_mem_image_laplacianDomain_of_hessHypothesis"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmooth.gradInnerCLM_smoothToH1Compl_mem_image_laplacianDomain_of_hessHypothesis ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmooth.gradInnerCLM_smoothToH1Compl_mem_image_laplacianDomain_of_hessHypothesis

theorem smoothMulH1Compl_smoothToH1Compl_mem_laplacianDomainPow_two_of_rhs_identification
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_hess :
      hessPairingLpOnLapDom (I := I) (M := M) g φ
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1
            (smoothToH1Compl_mem_laplacianDomainPow_two
              (I := I) (M := M) g v)) =
        hessPairingSmoothLp (I := I) (M := M) g φ v) :
    smoothMulH1Compl (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) ∈
      laplacianDomainPow (I := I) (M := M) g 2 :=
  smoothMulH1Compl_mem_pow_two_of_variational_identity
    (I := I) (M := M) g φ
    (smoothToH1Compl_mem_laplacianDomainPow_two (I := I) (M := M) g v)
    (gradInnerCLM_eq_H1ComplToLp_resolvent_smooth_of_hessHypothesis
      (I := I) (M := M) g φ v h_hess)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmooth.smoothMulH1Compl_smoothToH1Compl_mem_laplacianDomainPow_two_of_rhs_identification then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmooth.smoothMulH1Compl_smoothToH1Compl_mem_laplacianDomainPow_two_of_rhs_identification"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmooth.smoothMulH1Compl_smoothToH1Compl_mem_laplacianDomainPow_two_of_rhs_identification ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmooth.smoothMulH1Compl_smoothToH1Compl_mem_laplacianDomainPow_two_of_rhs_identification

theorem smoothCase_variational_identity_of_hessHypothesis
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_hess :
      hessPairingLpOnLapDom (I := I) (M := M) g φ
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1
            (smoothToH1Compl_mem_laplacianDomainPow_two
              (I := I) (M := M) g v)) =
        hessPairingSmoothLp (I := I) (M := M) g φ v) :
    gradInnerCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) =
      H1ComplToLp (I := I) (M := M) g
        (resolvent (I := I) (M := M) g
          (gradInnerLaplacianRhs (I := I) (M := M) g φ
            (smoothToH1Compl_mem_laplacianDomainPow_two
              (I := I) (M := M) g v))) :=
  gradInnerCLM_eq_H1ComplToLp_resolvent_smooth_of_hessHypothesis
    (I := I) (M := M) g φ v h_hess

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmooth.smoothCase_variational_identity_of_hessHypothesis then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmooth.smoothCase_variational_identity_of_hessHypothesis"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmooth.smoothCase_variational_identity_of_hessHypothesis ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmooth.smoothCase_variational_identity_of_hessHypothesis

end GradInnerLaplacianSmooth
end Laplacian
end Analysis
end DifferentialGeometry

end
