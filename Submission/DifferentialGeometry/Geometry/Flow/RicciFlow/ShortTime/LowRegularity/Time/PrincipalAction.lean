import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.PrincipalOperator.TimeDependentH2
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Regularity.DuhamelBootstrap

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.NNReal _root_.InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open _root_.Submission.DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private abbrev metricH1 (g : SmoothRiemannianMetric I M) :=
  TensorHs (I := I) (M := M) g 0 2 (1 : ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.metricH1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.metricH1 target :: scope.openDecls } }

private abbrev metricH2 (g : SmoothRiemannianMetric I M) :=
  TensorHs (I := I) (M := M) g 0 2 (2 : ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.metricH2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.metricH2 target :: scope.openDecls } }

private abbrev metricThirdOrderSobolev (g : SmoothRiemannianMetric I M) :=
  TensorHs (I := I) (M := M) g 0 2 ((1 : ℝ) + 2)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.metricThirdOrderSobolev
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.metricThirdOrderSobolev target :: scope.openDecls } }

private abbrev metricH4 (g : SmoothRiemannianMetric I M) :=
  TensorHs (I := I) (M := M) g 0 2 (4 : ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.metricH4
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.metricH4 target :: scope.openDecls } }

def orderOneH2Iso (g : SmoothRiemannianMetric I M) :
    TensorHs (I := I) (M := M) g 0 2 ((1 : ℝ) + 1) ≃ₗᵢ[ℝ]
      metricH2 (I := I) (M := M) g := by
  rw [show (1 : ℝ) + 1 = 2 by norm_num]
  exact LinearIsometryEquiv.refl ℝ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.orderOneH2Iso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.orderOneH2Iso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.orderOneH2Iso ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.orderOneH2Iso

def lowRegularityStateL2
    (g : SmoothRiemannianMetric I M) {T R : ℝ}
    (hT : 0 < T)
    (f : timeL2 (metricH1 (I := I) (M := M) g) T)
    (hR : 0 ≤ R)
    (hball : ∀ᵐ t ∂timeMeasure T,
      ‖tensorHsInclusion (I := I) (M := M)
        (g := g) (r := 0) (s := 2)
        (show (1 : ℝ) + 1 ≤ (1 : ℝ) + 2 by linarith)
        (maximalRegularityDuhamelSolutionField (I := I) (M := M)
          (1 : ℝ) hT
          (0 : metricThirdOrderSobolev (I := I) (M := M) g) f t)‖ ≤ R) :
    timeL2 (metricH2 (I := I) (M := M) g) T :=
  (orderOneH2Iso (I := I) (M := M) g).toLinearIsometry.toContinuousLinearMap.compLpL
    2 (timeMeasure T)
      (duhamelReprL2 (I := I) (M := M)
        g 0 2 (1 : ℝ) hT 0 f hR hball)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowRegularityStateL2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowRegularityStateL2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowRegularityStateL2 ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowRegularityStateL2

omit [BoundarylessManifold I M] in
theorem lowRegularityState_ae
    (g : SmoothRiemannianMetric I M) {T R : ℝ}
    (hT : 0 < T)
    (f : timeL2 (metricH1 (I := I) (M := M) g) T)
    (hR : 0 ≤ R)
    (hball : ∀ᵐ t ∂timeMeasure T,
      ‖tensorHsInclusion (I := I) (M := M)
        (g := g) (r := 0) (s := 2)
        (show (1 : ℝ) + 1 ≤ (1 : ℝ) + 2 by linarith)
        (maximalRegularityDuhamelSolutionField (I := I) (M := M)
          (1 : ℝ) hT
          (0 : metricThirdOrderSobolev (I := I) (M := M) g) f t)‖ ≤ R) :
    lowRegularityStateL2 (I := I) (M := M)
        g hT f hR hball =ᵐ[timeMeasure T]
      fun t => orderOneH2Iso (I := I) (M := M) g
        (tensorHsInclusion (I := I) (M := M)
          (g := g) (r := 0) (s := 2)
          (show (1 : ℝ) + 1 ≤ (1 : ℝ) + 2 by linarith)
          (maximalRegularityDuhamelSolutionField (I := I) (M := M)
            (1 : ℝ) hT
            (0 : metricThirdOrderSobolev (I := I) (M := M) g) f t)) := by
  have hmap :=
    (orderOneH2Iso (I := I) (M := M) g).toLinearIsometry.toContinuousLinearMap.coeFn_compLpL
      (p := 2) (μ := timeMeasure T)
      (duhamelReprL2 (I := I) (M := M)
        g 0 2 (1 : ℝ) hT 0 f hR hball)
  have hcoe := duhamelReprL2_ae (I := I) (M := M)
    g 0 2 (1 : ℝ) hT 0 f hR hball
  have hfield := duhamelRepr_field_ae (I := I) (M := M)
    g 0 2 (1 : ℝ) hT 0 f
  filter_upwards [hmap, hcoe, hfield] with t hm hc hf
  simpa only [lowRegularityStateL2] using
    hm.trans (congrArg
      (orderOneH2Iso (I := I) (M := M) g) (hc.trans hf))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowRegularityState_ae then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowRegularityState_ae"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowRegularityState_ae ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowRegularityState_ae

omit [BoundarylessManifold I M] in
theorem lowRegularityState_ae_le
    (g : SmoothRiemannianMetric I M) {T R : ℝ}
    (hT : 0 < T)
    (f : timeL2 (metricH1 (I := I) (M := M) g) T)
    (hR : 0 ≤ R)
    (hball : ∀ᵐ t ∂timeMeasure T,
      ‖tensorHsInclusion (I := I) (M := M)
        (g := g) (r := 0) (s := 2)
        (show (1 : ℝ) + 1 ≤ (1 : ℝ) + 2 by linarith)
        (maximalRegularityDuhamelSolutionField (I := I) (M := M)
          (1 : ℝ) hT
          (0 : metricThirdOrderSobolev (I := I) (M := M) g) f t)‖ ≤ R) :
    ∀ᵐ t ∂timeMeasure T,
      ‖lowRegularityStateL2 (I := I) (M := M)
        g hT f hR hball t‖ ≤ R := by
  filter_upwards [
    lowRegularityState_ae (I := I) (M := M)
      g hT f hR hball,
    hball] with t ht hbound
  rw [ht, LinearIsometryEquiv.norm_map]
  exact hbound

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowRegularityState_ae_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowRegularityState_ae_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowRegularityState_ae_le ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowRegularityState_ae_le

def lowRegularityPrincipalSecondOrderActionTime
    (g : SmoothRiemannianMetric I M) {T R : ℝ}
    (hT : 0 < T)
    (f : timeL2 (metricH1 (I := I) (M := M) g) T)
    (hR : 0 ≤ R)
    (hball : ∀ᵐ t ∂timeMeasure T,
      ‖tensorHsInclusion (I := I) (M := M)
        (g := g) (r := 0) (s := 2)
        (show (1 : ℝ) + 1 ≤ (1 : ℝ) + 2 by linarith)
        (maximalRegularityDuhamelSolutionField (I := I) (M := M)
          (1 : ℝ) hT
          (0 : metricThirdOrderSobolev (I := I) (M := M) g) f t)‖ ≤ R) :
    ℝ → (metricH4 (I := I) (M := M) g →L[ℝ]
      metricH2 (I := I) (M := M) g) :=
  timeDependentPrincipalOperatorH2 (I := I) (M := M) g hR
    (lowRegularityStateL2 (I := I) (M := M)
      g hT f hR hball)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowRegularityPrincipalSecondOrderActionTime then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowRegularityPrincipalSecondOrderActionTime"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowRegularityPrincipalSecondOrderActionTime ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowRegularityPrincipalSecondOrderActionTime

theorem lowRegularityPrincipalSecondOrderActionTime_ae
    (g : SmoothRiemannianMetric I M) {T R : ℝ}
    (hT : 0 < T)
    (f : timeL2 (metricH1 (I := I) (M := M) g) T)
    (hR : 0 ≤ R)
    (hball : ∀ᵐ t ∂timeMeasure T,
      ‖tensorHsInclusion (I := I) (M := M)
        (g := g) (r := 0) (s := 2)
        (show (1 : ℝ) + 1 ≤ (1 : ℝ) + 2 by linarith)
        (maximalRegularityDuhamelSolutionField (I := I) (M := M)
          (1 : ℝ) hT
          (0 : metricThirdOrderSobolev (I := I) (M := M) g) f t)‖ ≤ R) :
    lowRegularityPrincipalSecondOrderActionTime (I := I) (M := M)
        g hT f hR hball =ᵐ[timeMeasure T]
      fun t => lowRegularityPrincipalOperatorH2 (I := I) (M := M) g
        (orderOneH2Iso (I := I) (M := M) g
          (tensorHsInclusion (I := I) (M := M)
            (g := g) (r := 0) (s := 2)
            (show (1 : ℝ) + 1 ≤ (1 : ℝ) + 2 by linarith)
            (maximalRegularityDuhamelSolutionField (I := I) (M := M)
              (1 : ℝ) hT
              (0 : metricThirdOrderSobolev (I := I) (M := M) g) f t))) := by
  have hstate := lowRegularityState_ae_le (I := I) (M := M)
    g hT f hR hball
  have hprincipal := timeDependentPrincipalOperatorH2_ae_eq (I := I) (M := M)
    g hR
      (lowRegularityStateL2 (I := I) (M := M)
        g hT f hR hball) hstate
  have hfield := lowRegularityState_ae (I := I) (M := M)
    g hT f hR hball
  filter_upwards [hprincipal, hfield] with t hp hf
  simpa only [lowRegularityPrincipalSecondOrderActionTime] using hp.trans (congrArg
    (lowRegularityPrincipalOperatorH2 (I := I) (M := M) g) hf)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowRegularityPrincipalSecondOrderActionTime_ae then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowRegularityPrincipalSecondOrderActionTime_ae"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowRegularityPrincipalSecondOrderActionTime_ae ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowRegularityPrincipalSecondOrderActionTime_ae

theorem lowRegularityPrincipalSecondOrderActionTime_measurable_bounded_and_ae_eq
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ (ρ : ℝ) (C : NNReal), 0 < ρ ∧
      ∀ {R : ℝ} (hR : 0 ≤ R), R ≤ ρ →
        ∀ {T : ℝ} (hT : 0 < T)
          (f : timeL2 (metricH1 (I := I) (M := M) g) T)
          (hball : ∀ᵐ t ∂timeMeasure T,
            ‖tensorHsInclusion (I := I) (M := M)
              (g := g) (r := 0) (s := 2)
              (show (1 : ℝ) + 1 ≤ (1 : ℝ) + 2 by linarith)
              (maximalRegularityDuhamelSolutionField (I := I) (M := M)
                (1 : ℝ) hT
                (0 : metricThirdOrderSobolev (I := I) (M := M) g) f t)‖ ≤ R),
          _root_.MeasureTheory.AEStronglyMeasurable
              (lowRegularityPrincipalSecondOrderActionTime (I := I) (M := M)
                g hT f hR hball)
              (timeMeasure T) ∧
            (∀ᵐ t ∂timeMeasure T,
              ‖lowRegularityPrincipalSecondOrderActionTime (I := I) (M := M)
                g hT f hR hball t‖ ≤ (C : ℝ) * R) ∧
            lowRegularityPrincipalSecondOrderActionTime (I := I) (M := M)
                g hT f hR hball =ᵐ[timeMeasure T]
              fun t => lowRegularityPrincipalOperatorH2 (I := I) (M := M) g
                (orderOneH2Iso (I := I) (M := M) g
                  (tensorHsInclusion (I := I) (M := M)
                    (g := g) (r := 0) (s := 2)
                    (show (1 : ℝ) + 1 ≤ (1 : ℝ) + 2 by linarith)
                    (maximalRegularityDuhamelSolutionField (I := I) (M := M)
                      (1 : ℝ) hT
                      (0 : metricThirdOrderSobolev (I := I) (M := M) g) f t))) := by
  obtain ⟨ρ, C, hρ, hdata⟩ :=
    exists_timeDependentPrincipalOperatorH2_bounds (I := I) (M := M) hDim g
  refine ⟨ρ, C, hρ, ?_⟩
  intro R hR hRρ T hT f hball
  have hstate := lowRegularityState_ae_le (I := I) (M := M)
    g hT f hR hball
  obtain ⟨hmeas, hbound, _⟩ := hdata hR hRρ
    (lowRegularityStateL2 (I := I) (M := M)
      g hT f hR hball) hstate
  exact ⟨by
      simpa only [lowRegularityPrincipalSecondOrderActionTime] using hmeas,
    by
      simpa only [lowRegularityPrincipalSecondOrderActionTime] using hbound,
    lowRegularityPrincipalSecondOrderActionTime_ae (I := I) (M := M)
      g hT f hR hball⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowRegularityPrincipalSecondOrderActionTime_measurable_bounded_and_ae_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowRegularityPrincipalSecondOrderActionTime_measurable_bounded_and_ae_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowRegularityPrincipalSecondOrderActionTime_measurable_bounded_and_ae_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowRegularityPrincipalSecondOrderActionTime_measurable_bounded_and_ae_eq

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
