import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Ricci.Naturality
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.DeTurck.PullbackEvaluationChainRule
import Submission.DifferentialGeometry.Geometry.Metric.Pullback.Evaluation.Derivative
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.Perturbation.DeTurckNonlinearity
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.Spectrum.EigenCombination
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.Reconstruction.TensorHilbertSobolev
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.Christoffel.Perturbation
import Submission.DifferentialGeometry.Analysis.Parabolic.DeTurckRicci.VectorField.MetricContinuity
import Submission.DifferentialGeometry.Geometry.Connection.ChartBridge.Curvature.Ricci
import Submission.DifferentialGeometry.Geometry.Connection.ChartBridge.Curvature.BasisIdentity
import Submission.DifferentialGeometry.Geometry.Connection.ChartBridge.Curvature.BasisIdentityOffCenter
import Submission.DifferentialGeometry.Analysis.ODE.TimeDependentFlow.ChartLocalExistence.ChartLocalPicard
import Submission.DifferentialGeometry.Analysis.ODE.TimeDependentFlow.ChartLocalExistence.ChartOverlapUniqueness
import Submission.DifferentialGeometry.Analysis.ODE.TimeDependentFlow.Regularity.IntegralCurveFromJointC1
import Submission.DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothDependence.GlobalClosedManifold

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

open _root_.Submission.DifferentialGeometry.Geometry.Connection
namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Manifold _root_.ContDiff _root_.NNReal _root_.ENNReal _root_.Topology _root_.BigOperators
open _root_.Submission.DifferentialGeometry.PDE.DeTurck
open _root_.Submission.DifferentialGeometry.Analysis.ODE
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Pullback
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization

open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

theorem differentiableOn_and_deriv_eq_of_hasDerivWithinAt_Ici
    (f : ℝ → ℝ) {T : ℝ} (e : ℝ → ℝ)
    (h_int : ∀ t ∈ Set.Ioo (0 : ℝ) T, HasDerivWithinAt f (e t) (Set.Ici 0) t) :
    DifferentiableOn ℝ f (Set.Ioo 0 T) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) T, deriv f t = e t) := by
  have hsub : Set.Ioo (0 : ℝ) T ⊆ Set.Ici (0 : ℝ) := fun y hy => le_of_lt hy.1
  have h_within : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasDerivWithinAt f (e t) (Set.Ioo 0 T) t := fun t ht => (h_int t ht).mono hsub
  refine ⟨fun t ht => (h_within t ht).differentiableWithinAt, fun t ht => ?_⟩
  have hopen : IsOpen (Set.Ioo (0 : ℝ) T) := isOpen_Ioo
  rw [← derivWithin_of_isOpen hopen ht]
  exact (h_within t ht).derivWithin (hopen.uniqueDiffWithinAt ht)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.differentiableOn_and_deriv_eq_of_hasDerivWithinAt_Ici then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.differentiableOn_and_deriv_eq_of_hasDerivWithinAt_Ici"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.differentiableOn_and_deriv_eq_of_hasDerivWithinAt_Ici ``Submission.DifferentialGeometry.PDE.RicciFlow.differentiableOn_and_deriv_eq_of_hasDerivWithinAt_Ici

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem ricci_flow_pde_at_zero
    (g_fam : ℝ → SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T) (x : M)
    (v w : TangentSpace I x)
    (h_cont : ContinuousOn (fun s : ℝ => (g_fam s).inner x v w) (Set.Ico 0 T))
    (h_ric_cont : ContinuousWithinAt
      (fun s : ℝ => (-2) * ricciTensor (I := I) (g_fam s) x v w) (Set.Ioi 0) 0)
    (h_interior : ∀ t ∈ Set.Ioo (0 : ℝ) T, HasDerivWithinAt
      (fun s : ℝ => (g_fam s).inner x v w)
      ((-2) * ricciTensor (I := I) (g_fam t) x v w) (Set.Ici 0) t) :
    HasDerivWithinAt (fun s : ℝ => (g_fam s).inner x v w)
      ((-2) * ricciTensor (I := I) (g_fam 0) x v w) (Set.Ici 0) 0 := by
  set f : ℝ → ℝ := fun s : ℝ => (g_fam s).inner x v w with hf
  set e : ℝ → ℝ := fun s : ℝ => (-2) * ricciTensor (I := I) (g_fam s) x v w with he
  have h_int : ∀ t ∈ Set.Ioo (0 : ℝ) T, HasDerivWithinAt f (e t) (Set.Ici 0) t :=
    h_interior
  obtain ⟨h_diff, h_derivEq⟩ := differentiableOn_and_deriv_eq_of_hasDerivWithinAt_Ici f e h_int
  refine hasDerivWithinAt_Ici_of_tendsto_deriv (s := Set.Ioo 0 T) h_diff ?_ ?_ ?_
  · have h0 : (0 : ℝ) ∈ Set.Ico (0 : ℝ) T := ⟨le_rfl, hT⟩
    exact (h_cont.continuousWithinAt h0).mono Set.Ioo_subset_Ico_self
  · exact Ioo_mem_nhdsGT hT
  · have h_eventuallyEq : (fun s : ℝ => deriv f s) =ᶠ[nhdsWithin 0 (Set.Ioi 0)] e :=
      Filter.eventuallyEq_of_mem (Ioo_mem_nhdsGT hT) h_derivEq
    exact (h_ric_cont.tendsto).congr' h_eventuallyEq.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.ricci_flow_pde_at_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ricci_flow_pde_at_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ricci_flow_pde_at_zero ``Submission.DifferentialGeometry.PDE.RicciFlow.ricci_flow_pde_at_zero

end DifferentialGeometry.PDE.RicciFlow
