import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Regularity.DirectJets
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Background.Energy.AllOrderMassBounds
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Solution.UniformBounds
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.Solution.AllOrderMassBounds
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.RHS.Decomposition.Remainder
import Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.LinearMap
import Submission.DifferentialGeometry.Geometry.Metric.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.NNReal _root_.InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open _root_.Submission.DifferentialGeometry.Integral.Connection
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic (lowerState zero_mem_lowerState)
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
  (deTurckSmoothRemainder gFibreOpBound_ccTensor02Symm
    maxreg_solution_jointly_smooth_representative_of_tame_nemytskii
    smoothCcToTensorHs tensorResolventL2_isCompactOperator)

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral (ccTensor02Symm) in
noncomputable def deTurckRemainderSectionBackground (g g_bg : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g S) δ) :
    SmoothCcTensor g 0 2 :=
  deTurckSmoothRemainder (I := I) g g_bg
    (ccTensor02Symm (I := I) (M := M) g S) hδ_lt
    (gFibreOpBound_ccTensor02Symm (I := I) (M := M) g S hδ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.deTurckRemainderSectionBackground then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.deTurckRemainderSectionBackground"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.deTurckRemainderSectionBackground ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.deTurckRemainderSectionBackground


structure BackgroundSmoothRicciDeTurckSolution (g g_bg : SmoothRiemannianMetric I M)
    (K : LowRegularityBoundParameters) (T : ℝ) where
  carrier : MaximalRegularitySolutionSpace (I := I) (M := M)
    (g := g) (r := 0) (s := 2) (2 : ℝ) T
  modePath : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ
  radius : ℝ
  trace_zero : timeH1.trace0 _ T carrier = 0
  mode_smooth : ∀ i, ContDiff ℝ ∞ (modePath i)
  mode_mass : ∀ (j : ℕ) (τ : ℝ), 0 ≤ τ →
    ∃ B : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable B ∧
      ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
        tensorSobolevWeight (I := I) (M := M) i τ *
            (iteratedDeriv j (modePath i) t) ^ 2 ≤ B i
  mode_eq : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ i,
    tensorL2Coeff (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
        (tensorHsToL2 (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
          (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) (timeH1.toFun carrier t)) i =
      perModeConvolution (TensorEigenIdx.lambda (I := I) (M := M) i) (modePath i) t
  state_bound : ∀ t ∈ Set.Icc (0 : ℝ) T, ‖timeH1.toFun carrier t‖ ≤
    lowRegularityStateRadius K.top K.slope K.outer K.realize
  radius_pos : 0 < radius
  realize_bound : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ S : SmoothCcTensor g 0 2,
    SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2) S =
        tensorHsToL2 (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
          (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) (timeH1.toFun carrier t) →
      ‖smoothCcToTensorHs (I := I) (M := M) g ((2 : ℝ) + 2) S‖ ≤ radius
  force_coeff : ∀ (F : ℝ → SmoothCcTensor g 0 2) {δ : ℝ}
      (hδ_lt : δ < 1)
      (hδ : ∀ t : ℝ, gFibreOpBound (I := I) (M := M) g
        (ccTensorBilinSymm (I := I) g (F t)) δ)
      (_h_pin : ∀ t ∈ Set.Icc (0 : ℝ) T,
        SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2) (F t) =
          tensorHsToL2 (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
            (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) (timeH1.toFun carrier t))
      (_hball : ∀ t ∈ Set.Ico (0 : ℝ) T,
        ‖smoothCcToTensorHs (I := I) (M := M) g ((2 : ℝ) + 2) (F t)‖ ≤ radius),
    ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ i,
      modePath i t = tensorL2Coeff (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
        (SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2)
          (deTurckRemainderSectionBackground (I := I) (M := M) g g_bg (F t) hδ_lt (hδ t))) i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.BackgroundSmoothRicciDeTurckSolution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.BackgroundSmoothRicciDeTurckSolution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.BackgroundSmoothRicciDeTurckSolution ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.BackgroundSmoothRicciDeTurckSolution

attribute [-simp] BackgroundSmoothRicciDeTurckSolution.mk.sizeOf_spec

theorem exists_background_smooth_ricciDeTurck_solution_of_all_order_mode_bounds
    (g g_bg : SmoothRiemannianMetric I M) (K : LowRegularityBoundParameters)
    (hK : HasLowRegularityBoundsAt (I := I) (M := M) g g_bg K)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (uLo : MaximalRegularitySolutionSpace (I := I) (M := M) ((1 : ℕ) : ℝ) T)
    (gforce : timeL2
      (TensorHs (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ)) T)
    (hsol : IsBackgroundLowRegularitySolution (I := I) (M := M)
      g g_bg K hK hT hT1 uLo gforce)
    (hmass : ∀ σ : ℝ, ∃ Cσ : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T,
      Summable (fun i => tensorSobolevWeight (I := I) (M := M) i σ *
          (perModeConvolution (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u) t) ^ 2) ∧
        ∑' i, tensorSobolevWeight (I := I) (M := M) i σ *
            (perModeConvolution (TensorEigenIdx.lambda (I := I) (M := M) i)
              (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u) t) ^ 2 ≤ Cσ) :
    Nonempty (BackgroundSmoothRicciDeTurckSolution (I := I) (M := M) g g_bg K T) := by
  let R := lowRegularityStateRadius K.top K.slope K.outer K.realize
  have hR : 0 < R :=
    lowRegularityStateRadius_pos K.top_nonneg K.slope_nonneg K.outer_pos K.realize_pos
  let hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g (((1 : ℕ) : ℝ) + 1) S‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) K.threshold :=
    lowRegularityMetricRealization (I := I) (M := M) g K.realize_pos.le hK.metric_realization
  have hforce : gforce =ᵐ[timeMeasure T]
      fun t => deTurckRemainderOnLowerState (I := I) (M := M) g g_bg hR K.threshold_lt hreal
        (aeSetLift (zero_mem_lowerState (I := I) (M := M) g 1 hR.le)
          (maximalRegularityDuhamelSolutionField (I := I) (M := M) ((1 : ℕ) : ℝ) hT
            (0 : TensorHs (I := I) (M := M) g 0 2 (((1 : ℕ) : ℝ) + 2))
            gforce) t) := by
    simpa only [R, hreal, boundedDeTurckRemainderOnLowerState] using hsol.force_eq
  obtain ⟨carrier, _fHi, modePath, radius, htrace, _hmap, _hpin,
      hsmooth, hjet, hmode, hradius, hrealize, hforceCoeff, hstate⟩ :=
    direct_jet_of_mass (I := I) (M := M) g g_bg hR K.threshold_lt hreal
      hK.smoothCore_continuous hT gforce (by simpa only [R] using hsol.field_mem)
      hforce hmass
  refine ⟨{
    carrier := carrier
    modePath := modePath
    radius := radius
    trace_zero := htrace
    mode_smooth := hsmooth
    mode_mass := hjet
    mode_eq := hmode
    state_bound := ?_
    radius_pos := hradius
    realize_bound := hrealize
    force_coeff := ?_ }⟩
  · intro t ht
    simpa only [R] using hstate t ht
  · intro F δ hδ_lt hδ hpin _hball
    simpa only [deTurckRemainderSectionBackground] using hforceCoeff F hδ_lt hδ hpin

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_background_smooth_ricciDeTurck_solution_of_all_order_mode_bounds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_background_smooth_ricciDeTurck_solution_of_all_order_mode_bounds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_background_smooth_ricciDeTurck_solution_of_all_order_mode_bounds ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_background_smooth_ricciDeTurck_solution_of_all_order_mode_bounds

theorem exists_jointly_smooth_ricciDeTurck_metric_solution_of_spectral_solution (g g_bg : SmoothRiemannianMetric I M)
    (K : LowRegularityBoundParameters)
    (hK : HasLowRegularityBoundsAt (I := I) (M := M) g g_bg K) {T : ℝ}
    (hT : 0 < T) (hT1 : T ≤ 1)
    (P : BackgroundSmoothRicciDeTurckSolution (I := I) (M := M) g g_bg K T) :
    ∃ g_DT : ℝ → SmoothRiemannianMetric I M,
      IsQuasilinearMetricParabolicSolution (I := I)
        (deTurckRicciRHS (I := I) g_bg) g T g_DT ∧
      JointChartGramSmooth (I := I) T g_DT := by
  have hrepr : ∀ (S : SmoothCcTensor g 0 2) {δ : ℝ} (hδ_lt : δ < 1)
      (hδ : gFibreOpBound (I := I) (M := M) g
        (ccTensorBilinSymm (I := I) g S) δ)
      (x : M) (v w : TangentSpace I x),
    ccTensorBilinSymm (I := I) g
        (deTurckRemainderSectionBackground (I := I) (M := M) g g_bg S hδ_lt hδ +
          _root_.Submission.DifferentialGeometry.Analysis.Elliptic.rawTensorConnLapSmooth
            (I := I) g 0 2 S) x v w =
      deTurckRicciRHS (I := I) g_bg
        (tensorSectionRealizeMetric (I := I) g S hδ_lt hδ) x v w := by
    intro S δ hδ_lt hδ x v w
    simpa only [deTurckRemainderSectionBackground] using
      deTurck_rem_repr (I := I) (M := M) g g_bg S hδ_lt hδ x v w
  have hthreshold : K.threshold ≤ 1 :=
    hK.threshold_le_third.trans (by norm_num)
  obtain ⟨C, hC_pos, hCraw, hcap⟩ :=
    realize_h2_bound (I := I) (M := M) g K.realize_pos hthreshold hK.metric_realization
  have horder : (((1 : ℕ) : ℝ) + 1) = (2 : ℝ) := by norm_num
  rw [horder] at hCraw
  have hC : ∀ S : SmoothCcTensor g 0 2,
      gFibreOpBound (I := I) (M := M) g
        (ccTensorBilinSymm (I := I) g S)
        (C * ‖smoothCcToTensorHs (I := I) (M := M) g (2 : ℝ) S‖) := by
    exact hCraw
  have hstate : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ‖timeH1.toFun P.carrier t‖ ≤ 1 / (2 * C) := by
    intro t ht
    exact (P.state_bound t ht).trans
      ((lowRegularityStateRadius_le_quarter_realization_radius (Ctop := K.top) (B1 := K.slope)
        (ρ := K.outer) (P := K.realize)).trans hcap)
  obtain ⟨F, δ, hδ_lt, hδ, hF0, _hpin, hflow, hJ⟩ :=
    maxreg_solution_jointly_smooth_representative_of_tame_nemytskii
      (I := I) (M := M) g 2
      (deTurckRicciRHS (I := I) g_bg)
      (deTurckRemainderSectionBackground (I := I) (M := M) g g_bg) hrepr hT hT1
      P.carrier P.trace_zero P.modePath P.mode_smooth P.mode_mass P.mode_eq
      C hC_pos hC hstate P.realize_bound P.force_coeff
  refine ⟨fun t : ℝ => tensorSectionRealizeMetric (I := I) g
      (F t) hδ_lt (hδ t), ⟨hT, ?_, ?_⟩, hJ⟩
  · apply SmoothRiemannianMetric.ext_inner
    intro x v w
    simp only [tensorSectionRealizeMetric_inner, hF0,
      ccTensorBilinSymm_zero_apply, add_zero]
  · intro t ht x v w
    have heq : (fun s : ℝ =>
        (tensorSectionRealizeMetric (I := I) g (F s) hδ_lt (hδ s)).inner x v w) =
        fun s : ℝ => g.inner x v w +
          ccTensorBilinSymm (I := I) g (F s) x v w := by
      funext s
      rw [tensorSectionRealizeMetric_inner]
    rw [heq]
    exact (hflow t ht x v w).const_add (g.inner x v w)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_jointly_smooth_ricciDeTurck_metric_solution_of_spectral_solution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_jointly_smooth_ricciDeTurck_metric_solution_of_spectral_solution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_jointly_smooth_ricciDeTurck_metric_solution_of_spectral_solution ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_jointly_smooth_ricciDeTurck_metric_solution_of_spectral_solution

theorem exists_cross_scale_field_of_background_lowRegularity_solution
    (g g_bg : SmoothRiemannianMetric I M)
    (K : LowRegularityBoundParameters)
    (hK : HasLowRegularityBoundsAt (I := I) (M := M) g g_bg K)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (u : MaximalRegularitySolutionSpace (I := I) (M := M) ((1 : ℕ) : ℝ) T)
    (gforce : timeL2
      (TensorHs (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ)) T)
    (hsol : IsBackgroundLowRegularitySolution (I := I) (M := M) g g_bg K hK hT hT1 u gforce) :
    ∃ v : CrossScaleField (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ) T,
      v.lowRegularity = u ∧
        v.highRegularity = maximalRegularityDuhamelSolutionField (I := I) (M := M)
          ((1 : ℕ) : ℝ) hT 0 gforce ∧
        (∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
              (show ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1 by linarith)
              (v.repr t) = u.toFun t) ∧
        ∀ t ∈ Set.Icc (0 : ℝ) T, ‖v.repr t‖ ≤
          lowRegularityStateRadius K.top K.slope K.outer K.realize := by
  let v := duhamelCross (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ)
    hT 0 gforce
  have hvlo : v.lowRegularity = u := by
    change maximalRegularityDuhamelMap (I := I) (M := M) ((1 : ℕ) : ℝ)
      hT 0 gforce = u
    exact hsol.map_eq.symm
  have hfield : ∀ᵐ t ∂(timeMeasure T),
      ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
          (maximalRegularityDuhamelSolutionField (I := I) (M := M) ((1 : ℕ) : ℝ)
            hT 0 gforce t)‖ ≤
        lowRegularityStateRadius K.top K.slope K.outer K.realize := by
    filter_upwards [hsol.field_mem] with t ht
    change maximalRegularityDuhamelSolutionField (I := I) (M := M) ((1 : ℕ) : ℝ)
        hT 0 gforce t ∈ lowerState (I := I) (M := M) g 1
          (lowRegularityStateRadius K.top K.slope K.outer K.realize)
    exact ht
  refine ⟨v, hvlo, rfl, ?_, ?_⟩
  · intro t ht
    rw [crossRepr_toFun (I := I) (M := M) v hT ht, hvlo]
  · exact crossRepr_ball (I := I) (M := M) v hT
      (lowRegularityStateRadius_pos K.top_nonneg K.slope_nonneg K.outer_pos
        K.realize_pos).le hfield

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_cross_scale_field_of_background_lowRegularity_solution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_cross_scale_field_of_background_lowRegularity_solution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_cross_scale_field_of_background_lowRegularity_solution ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_cross_scale_field_of_background_lowRegularity_solution

theorem exists_background_smooth_ricciDeTurck_solution_of_adapted_solution
    (g g_bg : SmoothRiemannianMetric I M) (K : LowRegularityBoundParameters)
    {T Rcap Ctop₂ Kr2 Kr1 Kcap : ℝ}
    (hT : 0 < T) (hT1 : T ≤ 1)
    (uLo : MaximalRegularitySolutionSpace (I := I) (M := M) ((1 : ℕ) : ℝ) T)
    (gforce : timeL2
      (TensorHs (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ)) T)
    (hlo : IsAdaptedBackgroundLowRegularitySolution (I := I) (M := M) g g_bg K hT hT1
      uLo gforce Rcap Ctop₂ Kr2 Kr1 Kcap) :
    Nonempty (BackgroundSmoothRicciDeTurckSolution (I := I) (M := M) g g_bg K T) := by
  have hsolve := hlo.toIsBackgroundLowRegularitySolutionAt
  exact exists_background_smooth_ricciDeTurck_solution_of_all_order_mode_bounds (I := I) (M := M) g g_bg K hsolve.bounds
    hT hT1 uLo gforce hsolve.solve
      (per_mode_limit_weighted_energy_bound_all_orders_background (I := I) (M := M)
        g g_bg K hT hT1 uLo gforce hlo)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_background_smooth_ricciDeTurck_solution_of_adapted_solution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_background_smooth_ricciDeTurck_solution_of_adapted_solution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_background_smooth_ricciDeTurck_solution_of_adapted_solution ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_background_smooth_ricciDeTurck_solution_of_adapted_solution

theorem exists_uniform_jointly_smooth_ricciDeTurck_metric_solution (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ T : ℝ, 0 < T ∧
      ∀ (g : SmoothRiemannianMetric I M),
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        (∀ a : ℕ, a ≤ 3 →
          MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
        ∃ g_DT : ℝ → SmoothRiemannianMetric I M,
          IsQuasilinearMetricParabolicSolution (I := I)
            (deTurckRicciRHS (I := I) gBase) g T g_DT ∧
      JointChartGramSmooth (I := I) T g_DT := by
  obtain ⟨K, _hKuniform, T, hT, hT1, hsolve⟩ :=
    exists_uniform_background_lowRegularity_solution_with_all_order_weighted_energy_bounds (I := I) (M := M) hDim gBase hΛ
  refine ⟨T, hT, ?_⟩
  intro g hEq hjet
  obtain ⟨u, gforce, hsolveAt, hmass⟩ := hsolve g hEq hjet
  obtain ⟨P⟩ := exists_background_smooth_ricciDeTurck_solution_of_all_order_mode_bounds (I := I) (M := M) g gBase K
    hsolveAt.bounds hT hT1 u gforce hsolveAt.solve hmass
  exact exists_jointly_smooth_ricciDeTurck_metric_solution_of_spectral_solution (I := I) (M := M) g gBase K
    hsolveAt.bounds hT hT1 P

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_uniform_jointly_smooth_ricciDeTurck_metric_solution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_uniform_jointly_smooth_ricciDeTurck_metric_solution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_uniform_jointly_smooth_ricciDeTurck_metric_solution ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_uniform_jointly_smooth_ricciDeTurck_metric_solution

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
