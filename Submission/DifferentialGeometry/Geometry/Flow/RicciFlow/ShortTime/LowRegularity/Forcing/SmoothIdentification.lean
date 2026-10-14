import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Solution.Dense

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow _root_.Submission.DifferentialGeometry.Analysis.Parabolic
    DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.NNReal _root_.InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Integral.Connection
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M]

theorem symm_h2_of_state
    (g₀ : SmoothRiemannianMetric I M) {R : ℝ}
    (S : SmoothCcTensor g₀ 0 2)
    (hS : ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
      (smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 2) S)‖ ≤ R) :
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1)
      (ccTensor02Symm (I := I) (M := M) g₀ S)‖ ≤ R := by
  calc
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1)
        (ccTensor02Symm (I := I) (M := M) g₀ S)‖ ≤
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) S‖ :=
      norm_smoothCcToTensorHs_ccTensor02Symm_le (I := I) (M := M) g₀
        (((1 : ℕ) : ℝ) + 1) S
    _ = ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
        (smoothCcToTensorHs (I := I) (M := M) g₀
          (((1 : ℕ) : ℝ) + 2) S)‖ := by
      rw [tensorHsInclusion_smoothCcToTensorHs]
    _ ≤ R := hS

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.symm_h2_of_state then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.symm_h2_of_state"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.symm_h2_of_state ``Submission.DifferentialGeometry.PDE.RicciFlow.symm_h2_of_state

theorem deTurckRemainderOnLowerState_on_smoothCore
    (g₀ g_bg : SmoothRiemannianMetric I M) {R δ : ℝ}
    (hR : 0 < R) (hδ : δ < 1)
    (hreal : ∀ S : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀
        (((1 : ℕ) : ℝ) + 1) S‖ ≤ R →
        metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ S) δ)
    (hcore : Continuous (deTurckRemainderOnSmoothCore (I := I) (M := M) g₀ g_bg hδ hreal))
    (x : smoothCore (I := I) (M := M) g₀ R) :
    deTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hR hδ hreal x.1 =
      deTurckRemainderOnSmoothCore (I := I) (M := M) g₀ g_bg hδ hreal x := by
  simpa only [deTurckRemainderOnLowerState] using
    (smoothCore_dense (I := I) (M := M) g₀ hR).extend_eq hcore x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.deTurckRemainderOnLowerState_on_smoothCore then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.deTurckRemainderOnLowerState_on_smoothCore"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.deTurckRemainderOnLowerState_on_smoothCore ``Submission.DifferentialGeometry.PDE.RicciFlow.deTurckRemainderOnLowerState_on_smoothCore

theorem deTurckRemainderOnLowerState_on_smooth
    (g₀ g_bg : SmoothRiemannianMetric I M) {R δ : ℝ}
    (hR : 0 < R) (hδ : δ < 1)
    (hreal : ∀ P : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀
        (((1 : ℕ) : ℝ) + 1) P‖ ≤ R →
        metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ P) δ)
    (hcore : Continuous (deTurckRemainderOnSmoothCore (I := I) (M := M) g₀ g_bg hδ hreal))
    (S : SmoothCcTensor g₀ 0 2)
    (hS : ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
      (smoothCcToTensorHs (I := I) (M := M) g₀
        (((1 : ℕ) : ℝ) + 2) S)‖ ≤ R) :
    deTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hR hδ hreal
        ⟨smoothCcToTensorHs (I := I) (M := M) g₀
          (((1 : ℕ) : ℝ) + 2) S, hS⟩ =
      deTurckSmoothRemainderTensorHs (I := I) (M := M) g₀ g_bg 1
        (ccTensor02Symm (I := I) (M := M) g₀ S) hδ
        (hreal _ (symm_h2_of_state (I := I) (M := M) g₀ S hS)) := by
  let u : lowerState (I := I) (M := M) g₀ 1 R :=
    ⟨smoothCcToTensorHs (I := I) (M := M) g₀
      (((1 : ℕ) : ℝ) + 2) S, hS⟩
  let x : smoothCore (I := I) (M := M) g₀ R := ⟨u, ⟨S, rfl⟩⟩
  have hrep : coreRep g₀ x = S := by
    apply smoothHs_inj (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 2)
    rw [coreRep_spec]
  have hx := deTurckRemainderOnLowerState_on_smoothCore (I := I) (M := M) g₀ g_bg hR hδ hreal hcore x
  unfold deTurckRemainderOnSmoothCore at hx
  simpa only [u, x, hrep] using hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.deTurckRemainderOnLowerState_on_smooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.deTurckRemainderOnLowerState_on_smooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.deTurckRemainderOnLowerState_on_smooth ``Submission.DifferentialGeometry.PDE.RicciFlow.deTurckRemainderOnLowerState_on_smooth

theorem exists_zero_state_deTurck_remainder_spectral_bound
    (g₀ g_bg : SmoothRiemannianMetric I M) {R δ : ℝ}
    (hR : 0 < R) (hδ : δ < 1)
    (hreal : ∀ P : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀
        (((1 : ℕ) : ℝ) + 1) P‖ ≤ R →
        metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ P) δ)
    (hcore : Continuous (deTurckRemainderOnSmoothCore (I := I) (M := M) g₀ g_bg hδ hreal)) :
    ∃ Cseed : ℕ → ℝ, (∀ n, 0 ≤ Cseed n) ∧
      ∀ (n : ℕ) (F : Finset
          (DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
            (I := I) (M := M) g₀ 0 2)),
        ∑ i ∈ F, tensorSobolevWeight (I := I) (M := M) i (n : ℝ) *
            ((deTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hR hδ hreal
              ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1 hR.le⟩).coeff i) ^ 2 ≤
          Cseed n ^ 2 := by
  classical
  have hzero_embed :
      (0 : TensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2)) =
        smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 2)
          (0 : SmoothCcTensor g₀ 0 2) := by
    refine TensorHs.ext ?_
    funext i
    rw [TensorHs.zero_coeff, smoothCcToTensorHs_coeff,
      show SmoothCcTensor.toL2 (0 : SmoothCcTensor g₀ 0 2) = 0 from map_zero _,
      tensorL2Coeff_eq_inner, inner_zero_right]
  have hS : ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
      (smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 2)
        (0 : SmoothCcTensor g₀ 0 2))‖ ≤ R := by
    rw [← hzero_embed]
    simpa only [map_zero, norm_zero] using hR.le
  have hsub : (⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1 hR.le⟩ :
        lowerState (I := I) (M := M) g₀ 1 R) =
      ⟨smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 2)
        (0 : SmoothCcTensor g₀ 0 2), hS⟩ := Subtype.ext hzero_embed
  have hN := deTurckRemainderOnLowerState_on_smooth (I := I) (M := M) g₀ g_bg hR hδ hreal hcore
    (0 : SmoothCcTensor g₀ 0 2) hS
  refine ⟨fun n => ‖smoothCcToTensorHs (I := I) (M := M) g₀ (n : ℝ)
      (deTurckSmoothRemainder (I := I) g₀ g_bg
        (ccTensor02Symm (I := I) (M := M) g₀ (0 : SmoothCcTensor g₀ 0 2)) hδ
        (hreal _ (symm_h2_of_state (I := I) (M := M) g₀
          (0 : SmoothCcTensor g₀ 0 2) hS)))‖,
    fun n => norm_nonneg _, ?_⟩
  intro n F
  have hcoeff : ∀ i, (deTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hR hδ hreal
        ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1 hR.le⟩).coeff i =
      (ccTensorToHs (I := I) (M := M) g₀ 2 (n : ℝ)
        (deTurckSmoothRemainder (I := I) g₀ g_bg
          (ccTensor02Symm (I := I) (M := M) g₀ (0 : SmoothCcTensor g₀ 0 2)) hδ
          (hreal _ (symm_h2_of_state (I := I) (M := M) g₀
            (0 : SmoothCcTensor g₀ 0 2) hS)))).coeff i := by
    intro i
    rw [hsub, hN, deTurckSmoothN_coeff, ccTensorToHs_coeff]
  have hbridge : ccTensorToHs (I := I) (M := M) g₀ 2 (n : ℝ)
        (deTurckSmoothRemainder (I := I) g₀ g_bg
          (ccTensor02Symm (I := I) (M := M) g₀ (0 : SmoothCcTensor g₀ 0 2)) hδ
          (hreal _ (symm_h2_of_state (I := I) (M := M) g₀
            (0 : SmoothCcTensor g₀ 0 2) hS))) =
      smoothCcToTensorHs (I := I) (M := M) g₀ (n : ℝ)
        (deTurckSmoothRemainder (I := I) g₀ g_bg
          (ccTensor02Symm (I := I) (M := M) g₀ (0 : SmoothCcTensor g₀ 0 2)) hδ
          (hreal _ (symm_h2_of_state (I := I) (M := M) g₀
            (0 : SmoothCcTensor g₀ 0 2) hS))) :=
    TensorHs.ext (funext (fun _ => rfl))
  calc ∑ i ∈ F, tensorSobolevWeight (I := I) (M := M) i (n : ℝ) *
        ((deTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hR hδ hreal
          ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1 hR.le⟩).coeff i) ^ 2
      = ∑ i ∈ F, tensorSobolevWeight (I := I) (M := M) i (n : ℝ) *
          ((ccTensorToHs (I := I) (M := M) g₀ 2 (n : ℝ)
            (deTurckSmoothRemainder (I := I) g₀ g_bg
              (ccTensor02Symm (I := I) (M := M) g₀ (0 : SmoothCcTensor g₀ 0 2)) hδ
              (hreal _ (symm_h2_of_state (I := I) (M := M) g₀
                (0 : SmoothCcTensor g₀ 0 2) hS)))).coeff i) ^ 2 :=
        Finset.sum_congr rfl (fun i _ => by rw [hcoeff i])
    _ ≤ ‖ccTensorToHs (I := I) (M := M) g₀ 2 (n : ℝ)
          (deTurckSmoothRemainder (I := I) g₀ g_bg
            (ccTensor02Symm (I := I) (M := M) g₀ (0 : SmoothCcTensor g₀ 0 2)) hδ
            (hreal _ (symm_h2_of_state (I := I) (M := M) g₀
              (0 : SmoothCcTensor g₀ 0 2) hS)))‖ ^ 2 :=
        cc_partial_le_norm (I := I) (M := M) g₀ 2 (n : ℝ) _ F
    _ = ‖smoothCcToTensorHs (I := I) (M := M) g₀ (n : ℝ)
          (deTurckSmoothRemainder (I := I) g₀ g_bg
            (ccTensor02Symm (I := I) (M := M) g₀ (0 : SmoothCcTensor g₀ 0 2)) hδ
            (hreal _ (symm_h2_of_state (I := I) (M := M) g₀
              (0 : SmoothCcTensor g₀ 0 2) hS)))‖ ^ 2 := by rw [hbridge]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.exists_zero_state_deTurck_remainder_spectral_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.exists_zero_state_deTurck_remainder_spectral_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.exists_zero_state_deTurck_remainder_spectral_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.exists_zero_state_deTurck_remainder_spectral_bound

theorem deTurck_remainder_forcing_eq_smooth_remainder_ae
    (g₀ g_bg : SmoothRiemannianMetric I M) {R δ T : ℝ}
    (hR : 0 < R) (hδ : δ < 1)
    (hreal : ∀ P : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀
        (((1 : ℕ) : ℝ) + 1) P‖ ≤ R →
        metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ P) δ)
    (hcore : Continuous (deTurckRemainderOnSmoothCore (I := I) (M := M) g₀ g_bg hδ hreal))
    (field : timeL2 (TensorHs (I := I) (M := M) g₀ 0 2
      (((1 : ℕ) : ℝ) + 2)) T)
    (gforce : timeL2 (TensorHs (I := I) (M := M) g₀ 0 2
      ((1 : ℕ) : ℝ)) T)
    (hstate : ∀ᵐ t ∂(timeMeasure T),
      field t ∈ lowerState (I := I) (M := M) g₀ 1 R)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hR hδ hreal
        (aeSetLift (zero_mem_lowerState (I := I) (M := M) g₀ 1 hR.le) field t)))
    (F : ℝ → SmoothCcTensor g₀ 0 2)
    (hpin : ∀ᵐ t ∂(timeMeasure T),
      smoothCcToTensorHs (I := I) (M := M) g₀
        (((1 : ℕ) : ℝ) + 2) (F t) = field t)
    (hball : ∀ t : ℝ,
      ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
        (smoothCcToTensorHs (I := I) (M := M) g₀
          (((1 : ℕ) : ℝ) + 2) (F t))‖ ≤ R) :
    gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSmoothRemainderTensorHs (I := I) (M := M) g₀ g_bg 1
        (ccTensor02Symm (I := I) (M := M) g₀ (F t)) hδ
        (hreal _ (symm_h2_of_state (I := I) (M := M) g₀ (F t) (hball t)))) := by
  filter_upwards [hforce, hstate, hpin] with t htforce htstate htpin
  let uF : lowerState (I := I) (M := M) g₀ 1 R :=
    ⟨smoothCcToTensorHs (I := I) (M := M) g₀
      (((1 : ℕ) : ℝ) + 2) (F t), hball t⟩
  have hlift : aeSetLift
      (zero_mem_lowerState (I := I) (M := M) g₀ 1 hR.le) field t = uF := by
    apply Subtype.ext
    simp only [aeSetLift, dif_pos htstate, uF]
    exact htpin.symm
  rw [htforce, hlift]
  simpa only [uF] using
    deTurckRemainderOnLowerState_on_smooth (I := I) (M := M) g₀ g_bg hR hδ hreal hcore (F t) (hball t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.deTurck_remainder_forcing_eq_smooth_remainder_ae then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.deTurck_remainder_forcing_eq_smooth_remainder_ae"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.deTurck_remainder_forcing_eq_smooth_remainder_ae ``Submission.DifferentialGeometry.PDE.RicciFlow.deTurck_remainder_forcing_eq_smooth_remainder_ae

end DifferentialGeometry.PDE.RicciFlow

end
