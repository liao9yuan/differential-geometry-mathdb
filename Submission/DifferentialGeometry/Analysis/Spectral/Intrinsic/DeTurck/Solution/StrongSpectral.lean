import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.Solution.SmoothStrongPair
import Submission.DifferentialGeometry.Analysis.ODE.Gronwall.ClosedEdge

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators _root_.NNReal

namespace DifferentialGeometry.Analysis.Spectral

open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

structure StrongSpectralSolution
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {L : ℝ≥0}
    (Nfun : TensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2) →
      TensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ))
    (hLip : LipschitzWith L Nfun) {T : ℝ}
    (Phi : ℝ → SmoothCcTensor g₀ 0 2) where
  force : timeL2 (TensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T
  lowRegularity : timeH1 (TensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T
  highRegularity : timeL2 (TensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) T
  trace_zero : timeH1.trace0 _ T lowRegularity = 0
  scale_link :
    timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (show (a : ℝ) ≤ (a : ℝ) + 2 by linarith) highRegularity =
      timeH1.toTimeL2
        (TensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T lowRegularity
  heat_eq : timeH1.timeDeriv _ T lowRegularity =
    timeScaleLaplacian (I := I) (M := M) (a : ℝ) highRegularity + force
  force_eq : force = nemytskii (I := I) (M := M) hLip highRegularity
  highRegularity_ae_eq :
    (highRegularity : ℝ → TensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
      =ᵐ[timeMeasure T] fun t =>
        smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (Phi t)
  path_rep : ∀ t ∈ _root_.Set.Icc (0 : ℝ) T,
    lowRegularity.toFun t = smoothCcToTensorHs (I := I) (M := M) g₀ (a : ℝ) (Phi t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.StrongSpectralSolution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.StrongSpectralSolution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.StrongSpectralSolution ``Submission.DifferentialGeometry.Analysis.Spectral.StrongSpectralSolution

attribute [-simp] StrongSpectralSolution.mk.sizeOf_spec

noncomputable def strongSpectralSolutionOfSmoothPath
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {L : ℝ≥0}
    {Nfun : TensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2) →
      TensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)}
    (hLip : LipschitzWith L Nfun) {T : ℝ} (hT : 0 < T)
    (Phi : ℝ → SmoothCcTensor g₀ 0 2)
    (D : ℝ → TensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ))
    (hhi : _root_.MeasureTheory.MemLp
      (fun t => smoothCcToTensorHs (I := I) (M := M) g₀
        ((a : ℝ) + 2) (Phi t)) 2 (timeMeasure T))
    (hD : _root_.MeasureTheory.MemLp D 2 (timeMeasure T))
    (hlo : ContinuousOn
      (fun t => smoothCcToTensorHs (I := I) (M := M) g₀ (a : ℝ) (Phi t))
      (_root_.Set.Icc (0 : ℝ) T))
    (hzero : smoothCcToTensorHs (I := I) (M := M) g₀
      (a : ℝ) (Phi 0) = 0)
    (hderiv : ∀ t ∈ _root_.Set.Ioo (0 : ℝ) T,
      HasDerivAt
        (fun s => smoothCcToTensorHs (I := I) (M := M) g₀ (a : ℝ) (Phi s))
        (D t) t)
    (hpde : ∀ t ∈ _root_.Set.Ioo (0 : ℝ) T,
      D t = tensorScaleLaplacian (I := I) (M := M) (a : ℝ)
          (smoothCcToTensorHs (I := I) (M := M) g₀
            ((a : ℝ) + 2) (Phi t)) +
        Nfun (smoothCcToTensorHs (I := I) (M := M) g₀
          ((a : ℝ) + 2) (Phi t))) :
    StrongSpectralSolution (I := I) (M := M) (T := T) g₀ a Nfun hLip Phi := by
  let Fhi : ℝ → TensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2) := fun t =>
    smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (Phi t)
  let Flow : ℝ → TensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ) := fun t =>
    smoothCcToTensorHs (I := I) (M := M) g₀ (a : ℝ) (Phi t)
  let hi : timeL2 (TensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) T :=
    hhi.toLp Fhi
  let derivL2 : timeL2 (TensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T :=
    hD.toLp D
  let lo : timeH1 (TensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T :=
    timeH1.mk 0 derivL2
  let force : timeL2 (TensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T :=
    nemytskii (I := I) (M := M) hLip hi
  have hhiRep :
      (hi : ℝ → TensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
        =ᵐ[timeMeasure T] Fhi := by
    simpa only [hi, Fhi] using hhi.coeFn_toLp
  have hDRep :
      (derivL2 : ℝ → TensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ))
        =ᵐ[timeMeasure T] D := by
    simpa only [derivL2] using hD.coeFn_toLp
  have hmem : ∀ᵐ t ∂(timeMeasure T), t ∈ _root_.Set.Ioo (0 : ℝ) T := by
    have hrestrict : timeMeasure T = volume.restrict (_root_.Set.Ioo (0 : ℝ) T) := by
      rw [timeMeasure,
        Measure.restrict_congr_set (MeasureTheory.Ioo_ae_eq_Icc).symm]
    rw [hrestrict]
    exact _root_.MeasureTheory.ae_restrict_mem measurableSet_Ioo
  have htoFun : ∀ t ∈ _root_.Set.Icc (0 : ℝ) T, lo.toFun t = Flow t := by
    intro t ht
    have hzeroMem : (0 : ℝ) ∈ _root_.Set.Icc (0 : ℝ) T := ⟨le_rfl, hT.le⟩
    have hrepVol : ∀ᵐ s ∂volume,
        s ∈ _root_.Set.Icc (0 : ℝ) T → derivL2 s = D s := by
      exact (_root_.MeasureTheory.ae_restrict_iff' measurableSet_Icc).1 hDRep
    have hintEq : (∫ s in (0 : ℝ)..t, derivL2 s) = ∫ s in (0 : ℝ)..t, D s := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [hrepVol] with s hs hsI
      exact hs ((Set.uIoc_subset_uIcc).trans
        (_root_.Set.uIcc_subset_Icc hzeroMem ht) hsI)
    have hDint : _root_.MeasureTheory.IntegrableOn D (_root_.Set.Icc (0 : ℝ) T) volume := by
      change _root_.MeasureTheory.Integrable D (volume.restrict (_root_.Set.Icc (0 : ℝ) T))
      simpa only [timeMeasure] using hD.integrable (by norm_num)
    have hint : IntervalIntegrable D _root_.MeasureTheory.MeasureSpace.volume 0 t :=
      MeasureTheory.IntegrableOn.intervalIntegrable
        (hDint.mono_set (_root_.Set.uIcc_subset_Icc hzeroMem ht))
    have hFTC : (∫ s in (0 : ℝ)..t, D s) = Flow t - Flow 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
        (hlo.mono (_root_.Set.Icc_subset_Icc le_rfl ht.2))
        (fun s hs => hderiv s
          ⟨hs.1, lt_of_lt_of_le hs.2 ht.2⟩) hint
    simp only [lo, timeH1.toFun_apply, timeH1.initial_mk, timeH1.deriv_mk]
    rw [hintEq, hFTC, show Flow 0 = 0 by simpa only [Flow] using hzero]
    simp
  refine
    { force := force
      lowRegularity := lo
      highRegularity := hi
      trace_zero := ?_
      scale_link := ?_
      heat_eq := ?_
      force_eq := rfl
      highRegularity_ae_eq := by simpa only [Fhi] using hhiRep
      path_rep := by simpa only [Flow] using htoFun }
  · simp only [lo, timeH1.trace0_mk]
  · refine Lp.ext ?_
    have hinclAE :
        ⇑(timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            (show (a : ℝ) ≤ (a : ℝ) + 2 by linarith) hi) =ᵐ[timeMeasure T]
          fun t => tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            (show (a : ℝ) ≤ (a : ℝ) + 2 by linarith) (hi t) :=
      (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (show (a : ℝ) ≤ (a : ℝ) + 2 by linarith)).coeFn_compLpL
          (p := 2) (μ := timeMeasure T) hi
    have hloAE :
        ⇑(timeH1.toTimeL2 (TensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T lo)
            =ᵐ[timeMeasure T] lo.toFun := by
      rw [timeH1.toTimeL2_apply, timeH1.toFunL2]
      exact DifferentialGeometry.Analysis.Parabolic.TimeSobolev.coeFn_ofContinuousOn
        lo.continuousOn_toFun
    filter_upwards [hinclAE, hhiRep, hloAE, hmem] with t hit hhit hlot ht
    rw [hit, hhit, hlot, htoFun t (Set.mem_Icc_of_Ioo ht)]
    exact tensorHsInclusion_smoothCcToTensorHs (I := I) (M := M) g₀
      (show (a : ℝ) ≤ (a : ℝ) + 2 by linarith) (Phi t)
  · refine Lp.ext ?_
    have hderivAE :
        ⇑(timeH1.timeDeriv (TensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T lo)
            =ᵐ[timeMeasure T] D := by
      simpa only [lo, derivL2, timeH1.timeDeriv_mk] using hD.coeFn_toLp
    have hLap := timeScaleLaplacian_coeFn (I := I) (M := M) (τ := (a : ℝ)) hi
    have hforce := nemytskii_coeFn (I := I) (M := M) hLip hi
    have hadd := Lp.coeFn_add
      (timeScaleLaplacian (I := I) (M := M) (a : ℝ) hi) force
    filter_upwards [hderivAE, hhiRep, hLap, hforce, hadd, hmem]
      with t hdt hhit hLapt hft haddt ht
    have hforce_t : force t = Nfun (hi t) := by
      simpa only [force] using hft
    rw [hdt, haddt, Pi.add_apply, hLapt, hhit, hforce_t, hhit, hpde t ht]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.strongSpectralSolutionOfSmoothPath then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.strongSpectralSolutionOfSmoothPath"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.strongSpectralSolutionOfSmoothPath ``Submission.DifferentialGeometry.Analysis.Spectral.strongSpectralSolutionOfSmoothPath

theorem smooth_paths_eq_of_strong_spectral_solutions
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {L : ℝ≥0}
    {Nfun : TensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2) →
      TensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)}
    (hLip : LipschitzWith L Nfun) {C₁ C₂ : ℝ≥0}
    (hsingle : ∀ (v v' :
      TensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)),
      ‖Nfun v - Nfun v'‖ ≤
        (C₁ : ℝ) * _root_.Max.max
            ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) v‖
            ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) v'‖ * ‖v - v'‖ +
          (C₂ : ℝ) *
            ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (v - v')‖)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hsmall :
      (C₁ : ℝ) * Real.sqrt (1 + T) * ρ * (1 + T) +
          (C₂ : ℝ) * (2 * Real.sqrt T) < 1)
    (Phi₁ Phi₂ : ℝ → SmoothCcTensor g₀ 0 2)
    (d₁ : StrongSpectralSolution (I := I) (M := M) (T := T) g₀ a Nfun hLip Phi₁)
    (d₂ : StrongSpectralSolution (I := I) (M := M) (T := T) g₀ a Nfun hLip Phi₂)
    (hball₁ : ‖d₁.force‖ ≤ ρ) (hball₂ : ‖d₂.force‖ ≤ ρ) :
    ∀ t ∈ _root_.Set.Icc (0 : ℝ) T, Phi₁ t = Phi₂ t := by
  have huniq := deTurckStrong_unique (I := I) (M := M) g₀ a hLip hsingle
    hT hT1 hρ hsmall d₁.force d₂.force d₁.lowRegularity d₂.lowRegularity
      d₁.highRegularity d₂.highRegularity
    d₁.trace_zero d₂.trace_zero d₁.scale_link d₂.scale_link
    d₁.heat_eq d₂.heat_eq d₁.force_eq d₂.force_eq hball₁ hball₂
  intro t ht
  have hu := congrArg
    (fun u : timeH1 (TensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T =>
      u.toFun t) huniq.2.2
  change d₁.lowRegularity.toFun t = d₂.lowRegularity.toFun t at hu
  rw [d₁.path_rep t ht, d₂.path_rep t ht] at hu
  apply ccToHs_injective (I := I) (M := M) g₀ 2 (a : ℝ)
  simpa only [ccHs_eq_smoothHs] using hu

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.smooth_paths_eq_of_strong_spectral_solutions then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.smooth_paths_eq_of_strong_spectral_solutions"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.smooth_paths_eq_of_strong_spectral_solutions ``Submission.DifferentialGeometry.Analysis.Spectral.smooth_paths_eq_of_strong_spectral_solutions

end DifferentialGeometry.Analysis.Spectral

end
