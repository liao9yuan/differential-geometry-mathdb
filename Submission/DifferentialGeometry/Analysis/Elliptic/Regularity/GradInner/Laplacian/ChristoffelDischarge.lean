import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.Hessian.SmoothCase.LpClass
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
namespace GradInnerLaplacianSmoothCanonical

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
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.HessianBridgeSmoothLp
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaChristoffelDischarge
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianRhs
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDomain
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLp
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmooth

private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmoothCanonical.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmoothCanonical.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmoothCanonical.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmoothCanonical.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmoothCanonical.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmoothCanonical.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmoothCanonical.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmoothCanonical.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmoothCanonical.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmoothCanonical.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmoothCanonical.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmoothCanonical.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

theorem gradInnerCLM_eq_H1ComplToLp_resolvent_smooth_of_christoffel_discharge
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_transfer : perChartAeTransferableSmoothCase (I := I) (M := M) g φ v)
    (h_discharge : christoffelDischargeSmoothCase (I := I) (M := M) g φ v) :
    gradInnerCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) =
      H1ComplToLp (I := I) (M := M) g
        (resolvent (I := I) (M := M) g
          (gradInnerLaplacianRhs (I := I) (M := M) g φ
            (smoothToH1Compl_mem_laplacianDomainPow_two
              (I := I) (M := M) g v))) :=
  gradInnerCLM_eq_H1ComplToLp_resolvent_smooth_of_hessHypothesis
    (I := I) (M := M) g φ v
    (hessPairingLpOnLapDom_eq_hessPairingSmoothLp_smoothCase_connector
      (I := I) (M := M) g φ v h_transfer h_discharge)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmoothCanonical.gradInnerCLM_eq_H1ComplToLp_resolvent_smooth_of_christoffel_discharge then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmoothCanonical.gradInnerCLM_eq_H1ComplToLp_resolvent_smooth_of_christoffel_discharge"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmoothCanonical.gradInnerCLM_eq_H1ComplToLp_resolvent_smooth_of_christoffel_discharge ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmoothCanonical.gradInnerCLM_eq_H1ComplToLp_resolvent_smooth_of_christoffel_discharge

theorem gradInnerCLM_smoothToH1Compl_mem_image_laplacianDomain_of_christoffel_discharge
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_transfer : perChartAeTransferableSmoothCase (I := I) (M := M) g φ v)
    (h_discharge : christoffelDischargeSmoothCase (I := I) (M := M) g φ v) :
    gradInnerCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) ∈
      Set.image (H1ComplToLp (I := I) (M := M) g)
        (laplacianDomain (I := I) (M := M) g : Set (H1Compl g)) :=
  gradInnerCLM_smoothToH1Compl_mem_image_laplacianDomain_of_hessHypothesis
    (I := I) (M := M) g φ v
    (hessPairingLpOnLapDom_eq_hessPairingSmoothLp_smoothCase_connector
      (I := I) (M := M) g φ v h_transfer h_discharge)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmoothCanonical.gradInnerCLM_smoothToH1Compl_mem_image_laplacianDomain_of_christoffel_discharge then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmoothCanonical.gradInnerCLM_smoothToH1Compl_mem_image_laplacianDomain_of_christoffel_discharge"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmoothCanonical.gradInnerCLM_smoothToH1Compl_mem_image_laplacianDomain_of_christoffel_discharge ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmoothCanonical.gradInnerCLM_smoothToH1Compl_mem_image_laplacianDomain_of_christoffel_discharge

theorem smoothMulH1Compl_smoothToH1Compl_mem_laplacianDomainPow_two_of_christoffel_discharge
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_transfer : perChartAeTransferableSmoothCase (I := I) (M := M) g φ v)
    (h_discharge : christoffelDischargeSmoothCase (I := I) (M := M) g φ v) :
    smoothMulH1Compl (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) ∈
      laplacianDomainPow (I := I) (M := M) g 2 :=
  smoothMulH1Compl_smoothToH1Compl_mem_laplacianDomainPow_two_of_rhs_identification
    (I := I) (M := M) g φ v
    (hessPairingLpOnLapDom_eq_hessPairingSmoothLp_smoothCase_connector
      (I := I) (M := M) g φ v h_transfer h_discharge)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmoothCanonical.smoothMulH1Compl_smoothToH1Compl_mem_laplacianDomainPow_two_of_christoffel_discharge then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmoothCanonical.smoothMulH1Compl_smoothToH1Compl_mem_laplacianDomainPow_two_of_christoffel_discharge"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmoothCanonical.smoothMulH1Compl_smoothToH1Compl_mem_laplacianDomainPow_two_of_christoffel_discharge ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmoothCanonical.smoothMulH1Compl_smoothToH1Compl_mem_laplacianDomainPow_two_of_christoffel_discharge

theorem smoothCase_variational_identity_of_christoffel_discharge
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_transfer : perChartAeTransferableSmoothCase (I := I) (M := M) g φ v)
    (h_discharge : christoffelDischargeSmoothCase (I := I) (M := M) g φ v) :
    gradInnerCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) =
      H1ComplToLp (I := I) (M := M) g
        (resolvent (I := I) (M := M) g
          (gradInnerLaplacianRhs (I := I) (M := M) g φ
            (smoothToH1Compl_mem_laplacianDomainPow_two
              (I := I) (M := M) g v))) :=
  gradInnerCLM_eq_H1ComplToLp_resolvent_smooth_of_christoffel_discharge
    (I := I) (M := M) g φ v h_transfer h_discharge

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmoothCanonical.smoothCase_variational_identity_of_christoffel_discharge then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmoothCanonical.smoothCase_variational_identity_of_christoffel_discharge"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmoothCanonical.smoothCase_variational_identity_of_christoffel_discharge ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmoothCanonical.smoothCase_variational_identity_of_christoffel_discharge

theorem gradInnerCLM_eq_H1ComplToLp_resolvent_smoothCase_of_discharge
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_discharge : christoffelDischargeSmoothCase (I := I) (M := M) g φ v) :
    gradInnerCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) =
      H1ComplToLp (I := I) (M := M) g
        (resolvent (I := I) (M := M) g
          (gradInnerLaplacianRhs (I := I) (M := M) g φ
            (smoothToH1Compl_mem_laplacianDomainPow_two
              (I := I) (M := M) g v))) :=
  gradInnerCLM_eq_H1ComplToLp_resolvent_smooth_of_christoffel_discharge
    (I := I) (M := M) g φ v
    (perChartAeTransferableSmoothCase_holds (I := I) (M := M) g φ v) h_discharge

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmoothCanonical.gradInnerCLM_eq_H1ComplToLp_resolvent_smoothCase_of_discharge then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmoothCanonical.gradInnerCLM_eq_H1ComplToLp_resolvent_smoothCase_of_discharge"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmoothCanonical.gradInnerCLM_eq_H1ComplToLp_resolvent_smoothCase_of_discharge ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmoothCanonical.gradInnerCLM_eq_H1ComplToLp_resolvent_smoothCase_of_discharge

theorem gradInnerCLM_smoothToH1Compl_mem_image_laplacianDomain_of_discharge
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_discharge : christoffelDischargeSmoothCase (I := I) (M := M) g φ v) :
    gradInnerCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) ∈
      Set.image (H1ComplToLp (I := I) (M := M) g)
        (laplacianDomain (I := I) (M := M) g : Set (H1Compl g)) :=
  gradInnerCLM_smoothToH1Compl_mem_image_laplacianDomain_of_christoffel_discharge
    (I := I) (M := M) g φ v
    (perChartAeTransferableSmoothCase_holds (I := I) (M := M) g φ v) h_discharge

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmoothCanonical.gradInnerCLM_smoothToH1Compl_mem_image_laplacianDomain_of_discharge then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmoothCanonical.gradInnerCLM_smoothToH1Compl_mem_image_laplacianDomain_of_discharge"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmoothCanonical.gradInnerCLM_smoothToH1Compl_mem_image_laplacianDomain_of_discharge ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmoothCanonical.gradInnerCLM_smoothToH1Compl_mem_image_laplacianDomain_of_discharge

theorem smoothMulH1Compl_smoothToH1Compl_mem_laplacianDomainPow_two_of_discharge
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_discharge : christoffelDischargeSmoothCase (I := I) (M := M) g φ v) :
    smoothMulH1Compl (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) ∈
      laplacianDomainPow (I := I) (M := M) g 2 :=
  smoothMulH1Compl_smoothToH1Compl_mem_laplacianDomainPow_two_of_christoffel_discharge
    (I := I) (M := M) g φ v
    (perChartAeTransferableSmoothCase_holds (I := I) (M := M) g φ v) h_discharge

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmoothCanonical.smoothMulH1Compl_smoothToH1Compl_mem_laplacianDomainPow_two_of_discharge then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmoothCanonical.smoothMulH1Compl_smoothToH1Compl_mem_laplacianDomainPow_two_of_discharge"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmoothCanonical.smoothMulH1Compl_smoothToH1Compl_mem_laplacianDomainPow_two_of_discharge ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmoothCanonical.smoothMulH1Compl_smoothToH1Compl_mem_laplacianDomainPow_two_of_discharge

theorem smoothCase_variational_identity_of_discharge
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_discharge : christoffelDischargeSmoothCase (I := I) (M := M) g φ v) :
    gradInnerCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) =
      H1ComplToLp (I := I) (M := M) g
        (resolvent (I := I) (M := M) g
          (gradInnerLaplacianRhs (I := I) (M := M) g φ
            (smoothToH1Compl_mem_laplacianDomainPow_two
              (I := I) (M := M) g v))) :=
  gradInnerCLM_eq_H1ComplToLp_resolvent_smoothCase_of_discharge
    (I := I) (M := M) g φ v h_discharge

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmoothCanonical.smoothCase_variational_identity_of_discharge then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmoothCanonical.smoothCase_variational_identity_of_discharge"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmoothCanonical.smoothCase_variational_identity_of_discharge ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmoothCanonical.smoothCase_variational_identity_of_discharge

end GradInnerLaplacianSmoothCanonical
end Laplacian
end Analysis
end DifferentialGeometry

end
