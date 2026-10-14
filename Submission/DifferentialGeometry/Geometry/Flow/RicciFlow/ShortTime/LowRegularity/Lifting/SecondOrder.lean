import Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Nonautonomous.L2.Lifting
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Time.LowOrderOperators
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Basic.ExponentCongruence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.NNReal _root_.InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open _root_.Submission.DifferentialGeometry.Analysis.Calculus
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Tensor.RSTensor
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open _root_.Submission.DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private abbrev metricH2 (g : SmoothRiemannianMetric I M) :=
  TensorHs (I := I) (M := M) g 0 2 (2 : ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.metricH2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.metricH2 target :: scope.openDecls } }

private abbrev metricThirdOrderSobolev (g : SmoothRiemannianMetric I M) :=
  TensorHs (I := I) (M := M) g 0 2 (3 : ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.metricThirdOrderSobolev
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.metricThirdOrderSobolev target :: scope.openDecls } }

private abbrev incl32 (g : SmoothRiemannianMetric I M) :
    metricThirdOrderSobolev (I := I) (M := M) g →L[ℝ] metricH2 (I := I) (M := M) g :=
  tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
    (by norm_num)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.incl32
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.incl32 target :: scope.openDecls } }

theorem lowRadialHs_eq_self
    (g : SmoothRiemannianMetric I M) {ρ : ℝ} (hρ : 0 ≤ ρ)
    {v : metricH2 (I := I) (M := M) g}
    (hsymm : symmHs (I := I) (M := M) g (by norm_num : (0 : ℝ) ≤ 2) v = v)
    (hv : ‖v‖ ≤ ρ) :
    lowRadialHs (I := I) (M := M) g ρ v = v := by
  refine (lowRadialHs_eq (I := I) (M := M) g hρ v).trans ?_
  refine Eq.trans (congrArg (ballRetraction ρ) hsymm) ?_
  exact ballRetraction_eq_self_of_mem hv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowRadialHs_eq_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowRadialHs_eq_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowRadialHs_eq_self ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowRadialHs_eq_self

theorem lowRadialH3_eq_self
    (g : SmoothRiemannianMetric I M) {ρ : ℝ} (hρ : 0 < ρ)
    {u : metricThirdOrderSobolev (I := I) (M := M) g}
    (hsymm : symmHs (I := I) (M := M) g (by norm_num : (0 : ℝ) ≤ 3) u = u)
    (hu : ‖incl32 (I := I) (M := M) g u‖ ≤ ρ) :
    lowRadialH3 (I := I) (M := M) g ρ u = u := by
  refine (lowRadialH3_eq (I := I) (M := M) g hρ u).trans ?_
  refine Eq.trans
    (congrArg (lowScaleCutoff (incl32 (I := I) (M := M) g) ρ) hsymm) ?_
  exact lowScaleCutoff_eq_self _
    (tensorHsInclusion_injective (I := I) (M := M) (g := g)
      (r := 0) (s := 2) (by norm_num)) hu

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowRadialH3_eq_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowRadialH3_eq_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowRadialH3_eq_self ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowRadialH3_eq_self

theorem low_radial_retractions_eq_self_almost_everywhere
    (g : SmoothRiemannianMetric I M) {T ρ R : ℝ} (hρ : 0 < ρ) (hRρ : R ≤ ρ)
    {u : ℝ → metricThirdOrderSobolev (I := I) (M := M) g}
    (hsymm : ∀ᵐ t ∂timeMeasure T,
      symmHs (I := I) (M := M) g (by norm_num : (0 : ℝ) ≤ 3) (u t) = u t)
    (hball : ∀ᵐ t ∂timeMeasure T,
      ‖incl32 (I := I) (M := M) g (u t)‖ ≤ R) :
    (∀ᵐ t ∂timeMeasure T,
        lowRadialH3 (I := I) (M := M) g ρ (u t) = u t) ∧
      (∀ᵐ t ∂timeMeasure T,
        lowRadialHs (I := I) (M := M) g ρ
            (incl32 (I := I) (M := M) g (u t)) =
          incl32 (I := I) (M := M) g (u t)) := by
  constructor
  · filter_upwards [hsymm, hball] with t hs hb
    exact lowRadialH3_eq_self (I := I) (M := M) g hρ hs (hb.trans hRρ)
  · filter_upwards [hsymm, hball] with t hs hb
    refine lowRadialHs_eq_self (I := I) (M := M) g hρ.le ?_ (hb.trans hRρ)
    have hcomm := DFunLike.congr_fun
      (symmHs_incl (I := I) (M := M) g
        (τ := (2 : ℝ)) (σ := (3 : ℝ))
        (by norm_num) (by norm_num) (by norm_num)) (u t)
    simp only [ContinuousLinearMap.comp_apply] at hcomm
    refine hcomm.symm.trans ?_
    exact congrArg (incl32 (I := I) (M := M) g) hs

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.low_radial_retractions_eq_self_almost_everywhere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.low_radial_retractions_eq_self_almost_everywhere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.low_radial_retractions_eq_self_almost_everywhere ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.low_radial_retractions_eq_self_almost_everywhere

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem liftCompat_congr {g : SmoothRiemannianMetric I M}
    {aLo aHi pLo pHi qLo qHi : ℝ}
    (hLo : pLo = qLo) (hHi : pHi = qHi)
    (hOrd : aLo ≤ aHi) (hp : pLo ≤ pHi) (hq : qLo ≤ qHi)
    (AHi : TensorHs (I := I) (M := M) g 0 2 qHi →L[ℝ]
      TensorHs (I := I) (M := M) g 0 2 aHi)
    (ALo : TensorHs (I := I) (M := M) g 0 2 qLo →L[ℝ]
      TensorHs (I := I) (M := M) g 0 2 aLo)
    (hsq : (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          hOrd).comp AHi =
        ALo.comp
          (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            hq)) :
    (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          hOrd).comp
        (AHi.comp (tensorHsCongrL (I := I) (M := M) g 0 2 hHi)) =
      (ALo.comp (tensorHsCongrL (I := I) (M := M) g 0 2 hLo)).comp
        (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2) hp) := by
  have hnat := tensorHsCongrL_incl (I := I) (M := M) (g := g) (r := 0) (s := 2)
    hLo hHi hp hq
  rw [ContinuousLinearMap.comp_assoc, hnat,
    ← ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc, hsq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.liftCompat_congr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.liftCompat_congr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.liftCompat_congr ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.liftCompat_congr

omit [BoundarylessManifold I M] in
theorem exists_compatible_cross_scale_solution
    {g : SmoothRiemannianMetric I M} {T aLo aHi : ℝ}
    (hlo : aLo = aHi - 1) (hOrd : aLo ≤ aHi)
    (hOrdA1 : aLo + 1 ≤ aHi + 1) (hOrdSt : aLo + 2 ≤ aHi + 2)
    (hT : 0 < T) (hT1 : T ≤ 1)
    (A2Hi : ℝ → TensorHs (I := I) (M := M) g 0 2 (aHi + 2) →L[ℝ]
      TensorHs (I := I) (M := M) g 0 2 aHi)
    (hA2Hi : _root_.MeasureTheory.AEStronglyMeasurable A2Hi (timeMeasure T))
    (C2Hi : NNReal) (hC2Hi : ∀ᵐ t ∂timeMeasure T, ‖A2Hi t‖ ≤ (C2Hi : ℝ))
    (A1Hi : ℝ → TensorHs (I := I) (M := M) g 0 2 (aHi + 1) →L[ℝ]
      TensorHs (I := I) (M := M) g 0 2 aHi)
    (hA1Hi : _root_.MeasureTheory.MemLp A1Hi 2 (timeMeasure T))
    (f0Hi : timeL2 (TensorHs (I := I) (M := M) g 0 2 aHi) T)
    (hsmallHi : (C2Hi : ℝ) * (1 + T) +
      2 * Real.sqrt (1 + T) * ‖hA1Hi.toLp A1Hi‖ < 1)
    (A2Lo : ℝ → TensorHs (I := I) (M := M) g 0 2 (aLo + 2) →L[ℝ]
      TensorHs (I := I) (M := M) g 0 2 aLo)
    (hA2Lo : _root_.MeasureTheory.AEStronglyMeasurable A2Lo (timeMeasure T))
    (C2Lo : NNReal) (hC2Lo : ∀ᵐ t ∂timeMeasure T, ‖A2Lo t‖ ≤ (C2Lo : ℝ))
    (A1Lo : ℝ → TensorHs (I := I) (M := M) g 0 2 (aLo + 1) →L[ℝ]
      TensorHs (I := I) (M := M) g 0 2 aLo)
    (hA1Lo : _root_.MeasureTheory.MemLp A1Lo 2 (timeMeasure T))
    (f0Lo : timeL2 (TensorHs (I := I) (M := M) g 0 2 aLo) T)
    (hsmallLo : (C2Lo : ℝ) * (1 + T) +
      2 * Real.sqrt (1 + T) * ‖hA1Lo.toLp A1Lo‖ < 1)
    (hA2compat : ∀ᵐ t ∂timeMeasure T,
      (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          hOrd).comp (A2Hi t) =
        (A2Lo t).comp
          (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            hOrdSt))
    (hA1compat : ∀ᵐ t ∂timeMeasure T,
      (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          hOrd).comp (A1Hi t) =
        (A1Lo t).comp
          (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            hOrdA1))
    (hf0 : timeL2Inclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
        hOrd f0Hi = f0Lo)
    (fLo : timeL2 (TensorHs (I := I) (M := M) g 0 2 aLo) T)
    (hfLo : fLo =
      nonautL2Map (I := I) (M := M) hT hT1
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
          A2Lo hA2Lo C2Lo hC2Lo A1Lo hA1Lo fLo + f0Lo) :
    ∃ (uHi : MaximalRegularitySolutionSpace (I := I) (M := M)
        (g := g) (r := 0) (s := 2) aHi T)
      (fHi : timeL2 (TensorHs (I := I) (M := M) g 0 2 aHi) T),
      uHi = maximalRegularityDuhamelMap (I := I) (M := M) aHi hT 0 fHi ∧
        fHi =
          nonautL2Map (I := I) (M := M) hT hT1
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
              A2Hi hA2Hi C2Hi hC2Hi A1Hi hA1Hi fHi +
            f0Hi ∧
        timeH1.trace0 _ T uHi = 0 ∧
        timeH1.timeDeriv _ T uHi =
          timeScaleLaplacian (I := I) (M := M) aHi
              (maximalRegularityDuhamelSolutionField (I := I) (M := M) aHi hT 0 fHi) +
            (timeOp A2Hi hA2Hi C2Hi hC2Hi
                (maximalRegularityDuhamelSolutionField (I := I) (M := M) aHi hT 0 fHi) +
              a1L2Term (I := I) (M := M) hT hT1
                (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
                A1Hi hA1Hi fHi +
              f0Hi) ∧
        timeL2Inclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            hOrd fHi = fLo ∧
        timeL2Inclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            hOrdSt
            (maximalRegularityDuhamelSolutionField (I := I) (M := M) aHi hT 0 fHi) =
          maximalRegularityDuhamelSolutionField (I := I) (M := M) aLo hT 0 fLo ∧
        (∀ᵐ t ∂timeMeasure T,
          tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
              hOrd (fHi t) = fLo t) ∧
        (∀ᵐ t ∂timeMeasure T,
          tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
              hOrdSt
              (maximalRegularityDuhamelSolutionField (I := I) (M := M)
                aHi hT 0 fHi t) =
            maximalRegularityDuhamelSolutionField (I := I) (M := M) aLo hT 0 fLo t) := by
  subst hlo
  obtain ⟨uHi, fHi, huHi, hfHi, htrace, hderiv, hforce, hfield⟩ :=
    nonautL2_lift (I := I) (M := M) hT hT1
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
      A2Hi hA2Hi C2Hi hC2Hi A1Hi hA1Hi f0Hi hsmallHi
      A2Lo hA2Lo C2Lo hC2Lo A1Lo hA1Lo f0Lo hsmallLo
      hA2compat hA1compat hf0 fLo hfLo
  refine ⟨uHi, fHi, huHi, hfHi, htrace, hderiv, hforce, hfield, ?_, ?_⟩
  · have hcoe :
        timeL2Inclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            hOrd fHi =ᵐ[timeMeasure T]
          fun t =>
            tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
              hOrd (fHi t) :=
      (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
        hOrd).coeFn_compLpL (p := 2) (μ := timeMeasure T) fHi
    have hcoe2 :
        fLo =ᵐ[timeMeasure T]
          fun t =>
            tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
              hOrd (fHi t) := by
      rw [← hforce]
      exact hcoe
    filter_upwards [hcoe2] with t ht
    exact ht.symm
  · have hcoe :
        timeL2Inclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            hOrdSt
            (maximalRegularityDuhamelSolutionField (I := I) (M := M)
              aHi hT 0 fHi) =ᵐ[timeMeasure T]
          fun t =>
            tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
              hOrdSt
              (maximalRegularityDuhamelSolutionField (I := I) (M := M)
                aHi hT 0 fHi t) :=
      (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
        hOrdSt).coeFn_compLpL (p := 2) (μ := timeMeasure T)
          (maximalRegularityDuhamelSolutionField (I := I) (M := M) aHi hT 0 fHi)
    have hcoe2 :
        maximalRegularityDuhamelSolutionField (I := I) (M := M)
            (aHi - 1) hT 0 fLo =ᵐ[timeMeasure T]
          fun t =>
            tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
              hOrdSt
              (maximalRegularityDuhamelSolutionField (I := I) (M := M)
                aHi hT 0 fHi t) := by
      rw [← hfield]
      exact hcoe
    filter_upwards [hcoe2] with t ht
    exact ht.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_compatible_cross_scale_solution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_compatible_cross_scale_solution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_compatible_cross_scale_solution ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_compatible_cross_scale_solution

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
