import Submission.DifferentialGeometry.Geometry.Comparison.Volume.Family.SmallBall
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.Persistence.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

open _root_.Submission.DifferentialGeometry.Geometry.Connection
namespace DifferentialGeometry.PDE.RicciFlow.Perelman

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison

universe u uE uH

variable {M : Type u}
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M]
variable [T3Space M] [ConnectedSpace M] [CompactSpace M]
variable [I.Boundaryless] [BoundarylessManifold I M]

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete Real E

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.instCompleteSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.instMeasurableSpace_differentialGeometry : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.instBorelSpace_differentialGeometry : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.instBorelSpace_differentialGeometry target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
omit [ConnectedSpace M] [BoundarylessManifold I M] in
theorem early_vol_low
    [T2Space (TangentBundle I M)]
    {omega : Real} (h0omega : 0 < omega)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 omega h0omega))
    (hS : IsSolutionOn (I := I) S)
    {rho : Real} :
    ∃ tau kappa : Real, 0 < tau ∧ tau < omega ∧ 0 < kappa ∧
      ∀ (t : RealTimeInterval.FlowTime (RealTimeInterval.closedOpen 0 omega h0omega)),
        (t : Real) ≤ tau →
        ∀ (p : M) {r : Real}, 0 < r → r ≤ rho → r ^ 2 ≤ (t : Real) →
          ENNReal.ofReal kappa * ENNReal.ofReal r ^ Module.finrank Real E ≤
            DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure
              (I := I) (M := M) (S.base.metric t)
              {x : M | DifferentialGeometry.riemannianEDistOf
                (I := I) (S.base.metric t) p x < ENNReal.ofReal r} := by
  simpa only [SolutionOn.family_metric] using
    family_vol_low (I := I) (M := M) (rho := rho) h0omega S.family.metric hS.smoothMetric

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.early_vol_low then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.early_vol_low"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.early_vol_low ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.early_vol_low

omit [NeZero (Module.finrank ℝ E)] in
omit [ConnectedSpace M] [BoundarylessManifold I M] in
theorem early_ball_low
    [T2Space (TangentBundle I M)]
    {omega : Real} (h0omega : 0 < omega)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 omega h0omega))
    (hS : IsSolutionOn (I := I) S)
    {rho : Real} :
    ∃ tau kappa : Real, 0 < tau ∧ tau < omega ∧ 0 < kappa ∧
      ∀ (t : RealTimeInterval.FlowTime (RealTimeInterval.closedOpen 0 omega h0omega)),
        (t : Real) ≤ tau →
        ∀ B : FlowMetricBall S t, B.radius ≤ rho → B.radius ^ 2 ≤ (t : Real) →
          B.IsKappaNoncollapsed kappa := by
  classical
  obtain ⟨tau, kappa, htau0, htauomega, hkappa, hvol⟩ :=
    early_vol_low (I := I) (M := M) (rho := rho) h0omega S hS
  refine ⟨tau, kappa, htau0, htauomega, hkappa, ?_⟩
  intro t ht B hBrho hsq
  refine ⟨hkappa, ?_⟩
  simpa only [FlowMetricBall.volume, FlowMetricBall.set, FlowMetricBall.setAt,
    DifferentialGeometry.Integral.Measure.volumeMeasureOn_eq_metric,
    SolutionOn.family_metric] using
      hvol t ht B.center B.radius_pos hBrho hsq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.early_ball_low then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.early_ball_low"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.early_ball_low ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.early_ball_low

omit [NeZero (Module.finrank Real E)] [ConnectedSpace M]
  [I.Boundaryless] [BoundarylessManifold I M] in
private theorem kappa_mono
    {D : RealTimeInterval} {S : SolutionOn (I := I) (M := M) D}
    {t : RealTimeInterval.FlowTime D} {B : FlowMetricBall S t}
    {kappa kappa' : Real} (hkappa : 0 < kappa) (hle : kappa ≤ kappa')
    (hB : B.IsKappaNoncollapsed kappa') :
    B.IsKappaNoncollapsed kappa := by
  rcases hB with ⟨_, hvol⟩
  refine ⟨hkappa, ?_⟩
  exact (mul_le_mul' (ENNReal.ofReal_le_ofReal hle) le_rfl).trans hvol

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.kappa_mono
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.kappa_mono target :: scope.openDecls } }

theorem no_local_open
    [T2Space (TangentBundle I M)]
    {omega : Real} (h0omega : 0 < omega)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 omega h0omega))
    (hS : IsSolutionOn (I := I) S)
    (hDim : Module.finrank Real E = 3)
    {rho : Real} (hrho : 0 < rho) :
    NoLocalCollapsing S rho := by
  classical
  obtain ⟨tau, kappa0, htau0, htauomega, hkappa0, hearly⟩ :=
    early_ball_low (I := I) (M := M) (rho := rho) h0omega S hS
  have htau2 : 0 < tau / 2 := half_pos htau0
  have htau2tau : tau / 2 < tau := half_lt_self htau0
  obtain ⟨kappa1, hkappa1, hafter⟩ :=
    noncollapse_after (I := I) (M := M) h0omega S hS hDim
      htau2 htau2tau hrho
  let kappa : Real := _root_.Min.min kappa0 kappa1
  have hkappa : 0 < kappa := lt_min hkappa0 hkappa1
  refine ⟨kappa, hkappa, hrho, ?_⟩
  intro t B hBrho hB
  by_cases ht : (t : Real) ≤ tau
  · have hsq : B.radius ^ 2 ≤ (t : Real) := by
      have hleft_mem :
          (t : Real) - B.radius ^ 2 ∈
            (RealTimeInterval.closedOpen 0 omega h0omega).carrier := by
        exact hB.1 ⟨le_rfl, by nlinarith [sq_nonneg B.radius]⟩
      have hleft_nonneg : 0 ≤ (t : Real) - B.radius ^ 2 := by
        simpa [RealTimeInterval.closedOpen] using hleft_mem.1
      nlinarith
    exact kappa_mono (I := I) (M := M) hkappa (min_le_left _ _)
      (hearly t ht B hBrho hsq)
  · have htau_le : tau ≤ (t : Real) := le_of_not_ge ht
    exact kappa_mono (I := I) (M := M) hkappa (min_le_right _ _)
      (hafter t htau_le B hBrho hB)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.no_local_open then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.no_local_open"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.no_local_open ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.no_local_open

end

end DifferentialGeometry.PDE.RicciFlow.Perelman
