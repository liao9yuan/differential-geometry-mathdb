import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.Reconstruction.HeatOutput

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Spectral
namespace MetricRealization

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Tensor
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.MetricRealization.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.MetricRealization.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.MetricRealization.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.MetricRealization.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

def MemAllTensorHs (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (u : TensorL2 r s g) : Prop :=
  ∀ σ : ℝ, ∀ hσ : 0 ≤ σ,
    ∃ v : TensorHs (I := I) (M := M) g r s σ,
      tensorHsToL2 (I := I) (M := M) (g := g) (r := r) (s := s)
          (tensorResolventL2_isCompactOperator
            (I := I) (M := M) g r s) hσ v = u

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.MetricRealization.MemAllTensorHs then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.MetricRealization.MemAllTensorHs"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.MetricRealization.MemAllTensorHs ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.MemAllTensorHs

theorem tensorHs_coeff_eq_spectralCoeff_of_toL2_eq (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (u : TensorL2 r s g) {σ : ℝ} (hσ : 0 ≤ σ)
    (v : TensorHs (I := I) (M := M) g r s σ)
    (hv : tensorHsToL2 (I := I) (M := M) (g := g) (r := r) (s := s)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
        hσ v = u)
    (i : TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s) :
    v.coeff i = spectralCoeff (I := I) (M := M) g r s u i := by
  have h :=
    tensorHsToL2_tensorL2Coeff
      (I := I) (M := M)
      (h_compact := tensorResolventL2_isCompactOperator
        (I := I) (M := M) g r s) hσ v i
  rw [hv] at h
  rw [spectralCoeff_apply]
  exact h.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.MetricRealization.tensorHs_coeff_eq_spectralCoeff_of_toL2_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.MetricRealization.tensorHs_coeff_eq_spectralCoeff_of_toL2_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.MetricRealization.tensorHs_coeff_eq_spectralCoeff_of_toL2_eq ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.tensorHs_coeff_eq_spectralCoeff_of_toL2_eq

theorem spectralWeighted_summable_of_mem (g : SmoothRiemannianMetric I M)
    (r s : ℕ) (u : TensorL2 r s g) (h_mem : MemAllTensorHs (I := I) (M := M) g r s u)
    {σ : ℝ} (hσ : 0 ≤ σ) :
    Summable (fun i : TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s =>
      tensorSobolevWeight (I := I) (M := M) i σ *
        (spectralCoeff (I := I) (M := M) g r s u i) ^ 2) := by
  obtain ⟨v, hv⟩ := h_mem σ hσ
  have hsumm := v.weighted_summable
  have h_eq :
      (fun i : TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s =>
        tensorSobolevWeight (I := I) (M := M) i σ * (v.coeff i) ^ 2) =
      (fun i => tensorSobolevWeight (I := I) (M := M) i σ *
        (spectralCoeff (I := I) (M := M) g r s u i) ^ 2) := by
    funext i
    rw [tensorHs_coeff_eq_spectralCoeff_of_toL2_eq (I := I) (M := M) g r s u hσ v hv i]
  rwa [h_eq] at hsumm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.MetricRealization.spectralWeighted_summable_of_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.MetricRealization.spectralWeighted_summable_of_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.MetricRealization.spectralWeighted_summable_of_mem ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.spectralWeighted_summable_of_mem

theorem chosenTensorHs_zero_coeff_eq (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (u : TensorL2 r s g) (h_mem : MemAllTensorHs (I := I) (M := M) g r s u)
    (i : TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s) :
    (Classical.choose (h_mem 0 (le_refl (0 : ℝ)))).coeff i =
      spectralCoeff (I := I) (M := M) g r s u i :=
  tensorHs_coeff_eq_spectralCoeff_of_toL2_eq (I := I) (M := M) g r s u (le_refl (0 : ℝ))
    (Classical.choose (h_mem 0 (le_refl (0 : ℝ))))
    (Classical.choose_spec (h_mem 0 (le_refl (0 : ℝ)))) i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.MetricRealization.chosenTensorHs_zero_coeff_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.MetricRealization.chosenTensorHs_zero_coeff_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.MetricRealization.chosenTensorHs_zero_coeff_eq ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.chosenTensorHs_zero_coeff_eq

theorem spectral_smooth_realizes_as_smooth_of_mem_all_and_finite_support
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (u : TensorL2 r s g)
    (h_mem : MemAllTensorHs (I := I) (M := M) g r s u)
    (hu_fs : (Function.support (spectralCoeff (I := I) (M := M) g r s u)).Finite) :
    ∃ T : SmoothCcTensor g r s, (T : TensorL2 r s g) = u := by
  obtain ⟨v₀, hv₀⟩ := h_mem 0 (le_refl (0 : ℝ))
  have h_coeff : v₀.coeff = spectralCoeff (I := I) (M := M) g r s u := by
    funext i
    exact tensorHs_coeff_eq_spectralCoeff_of_toL2_eq (I := I) (M := M) g r s u (le_refl (0 : ℝ)) v₀ hv₀ i
  have hv₀_fs : (Function.support v₀.coeff).Finite := by
    rw [h_coeff]; exact hu_fs
  refine ⟨tensorHsSmoothRepr (I := I) (M := M) v₀ hv₀_fs, ?_⟩
  rw [tensorHsSmoothRepr_toL2 (I := I) (M := M)
    (le_refl (0 : ℝ)) v₀ hv₀_fs]
  exact hv₀

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.MetricRealization.spectral_smooth_realizes_as_smooth_of_mem_all_and_finite_support then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.MetricRealization.spectral_smooth_realizes_as_smooth_of_mem_all_and_finite_support"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.MetricRealization.spectral_smooth_realizes_as_smooth_of_mem_all_and_finite_support ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.spectral_smooth_realizes_as_smooth_of_mem_all_and_finite_support

def IteratedGardingExtensionBound (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    Prop :=
  ∀ k : ℕ, ∃ σ : ℝ, ∃ _hσ : 0 ≤ σ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ (T : TensorHs (I := I) (M := M) g r s σ)
      (hT_fs : (Function.support T.coeff).Finite),
      (wtwokTwoNorm (I := I) (M := M) g k
          (tensorHsSmoothRepr (I := I) (M := M) T hT_fs)).toReal ≤
        C * ‖T‖

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.MetricRealization.IteratedGardingExtensionBound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.MetricRealization.IteratedGardingExtensionBound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.MetricRealization.IteratedGardingExtensionBound ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.IteratedGardingExtensionBound

def EigenvalueTailSummable (g : SmoothRiemannianMetric I M) (r s : ℕ) : Prop :=
  ∃ p : ℝ, 0 < p ∧
    Summable (fun i : TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s =>
      (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (-p))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.MetricRealization.EigenvalueTailSummable then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.MetricRealization.EigenvalueTailSummable"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.MetricRealization.EigenvalueTailSummable ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.EigenvalueTailSummable

omit [NeZero (Module.finrank ℝ E)] in
private lemma eigenvalueTail_eq_weight
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (p : ℝ)
    (i : TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s) :
    (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (-p) =
      tensorSobolevWeight (I := I) (M := M) i (-p) := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.eigenvalueTail_eq_weight
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.MetricRealization.eigenvalueTail_eq_weight target :: scope.openDecls } }

theorem spectralCoeff_weightedPow_summable
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (u : TensorL2 r s g)
    (h_mem : MemAllTensorHs (I := I) (M := M) g r s u)
    (h_tail : EigenvalueTailSummable (I := I) (M := M) g r s)
    (N : ℕ) :
    Summable (fun i : TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s =>
      |spectralCoeff (I := I) (M := M) g r s u i| *
        tensorSobolevWeight (I := I) (M := M) i (N : ℝ)) := by
  obtain ⟨p, hp_pos, h_tail_p⟩ := h_tail
  have hp_nonneg : (0 : ℝ) ≤ p := hp_pos.le
  have hσ_nonneg : (0 : ℝ) ≤ 2 * (N : ℝ) + p := by positivity
  have h_spec :
      Summable (fun i : TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s =>
        tensorSobolevWeight (I := I) (M := M) i (2 * (N : ℝ) + p) *
          (spectralCoeff (I := I) (M := M) g r s u i) ^ 2) :=
    spectralWeighted_summable_of_mem (I := I) (M := M) g r s u h_mem hσ_nonneg
  have h_tailp :
      Summable (fun i : TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s =>
        tensorSobolevWeight (I := I) (M := M) i (-p)) := by
    simpa only [eigenvalueTail_eq_weight] using h_tail_p
  have h_dom :
      Summable (fun i : TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s =>
        (1 / 2) * (tensorSobolevWeight (I := I) (M := M) i (2 * (N : ℝ) + p) *
            (spectralCoeff (I := I) (M := M) g r s u i) ^ 2) +
          (1 / 2) * tensorSobolevWeight (I := I) (M := M) i (-p)) :=
    (h_spec.mul_left _).add (h_tailp.mul_left _)
  refine Summable.of_nonneg_of_le ?_ ?_ h_dom
  · intro i
    have hw : 0 ≤ tensorSobolevWeight (I := I) (M := M) i (N : ℝ) :=
      tensorSobolevWeight_nonneg (I := I) (M := M) i (N : ℝ)
    positivity
  · intro i
    set c := spectralCoeff (I := I) (M := M) g r s u i with hc_def
    set wN := tensorSobolevWeight (I := I) (M := M) i (N : ℝ) with hwN_def
    have hwN_nonneg : 0 ≤ wN := tensorSobolevWeight_nonneg (I := I) (M := M) i (N : ℝ)
    have hwp_pos : 0 < tensorSobolevWeight (I := I) (M := M) i p :=
      tensorSobolevWeight_pos (I := I) (M := M) i p
    have h_split :
        tensorSobolevWeight (I := I) (M := M) i (2 * (N : ℝ) + p) =
          wN * wN * tensorSobolevWeight (I := I) (M := M) i p := by
      rw [hwN_def]
      rw [show (2 * (N : ℝ) + p) = ((N : ℝ) + (N : ℝ)) + p by ring,
        TensorHs.tensorSobolevWeight_add (I := I) (M := M) i ((N : ℝ) + (N : ℝ)) p,
        TensorHs.tensorSobolevWeight_add (I := I) (M := M) i (N : ℝ) (N : ℝ)]
    have h_neg :
        tensorSobolevWeight (I := I) (M := M) i (-p) =
          (tensorSobolevWeight (I := I) (M := M) i p)⁻¹ :=
      TensorHs.tensorSobolevWeight_neg (I := I) (M := M) i p
    set wp := tensorSobolevWeight (I := I) (M := M) i p with hwp_def
    rw [h_split, h_neg]
    have hwp_ne : wp ≠ 0 := ne_of_gt hwp_pos
    have key : 2 * (|c| * wN) ≤ wN * wN * wp * c ^ 2 + wp⁻¹ := by
      set a := Real.sqrt wp with ha_def
      have hsqrt_sq : a ^ 2 = wp := Real.sq_sqrt (le_of_lt hwp_pos)
      have hsqrt_pos : 0 < a := Real.sqrt_pos.mpr hwp_pos
      have hsqrt_ne : a ≠ 0 := ne_of_gt hsqrt_pos
      have hc_sq : c ^ 2 = |c| ^ 2 := (sq_abs c).symm
      have h_amgm : 2 * (a * wN * |c|) * a⁻¹ ≤ (a * wN * |c|) ^ 2 + a⁻¹ ^ 2 :=
        two_mul_le_add_sq (a * wN * |c|) a⁻¹
      have hinv_mul : a⁻¹ * a = 1 := inv_mul_cancel₀ hsqrt_ne
      have hinv_sq : a⁻¹ ^ 2 = wp⁻¹ := by rw [inv_pow, hsqrt_sq]
      have hcross : 2 * (a * wN * |c|) * a⁻¹ = 2 * (|c| * wN) := by
        have : a * wN * |c| * a⁻¹ = (a⁻¹ * a) * (wN * |c|) := by ring
        rw [show 2 * (a * wN * |c|) * a⁻¹ = 2 * (a * wN * |c| * a⁻¹) by ring,
          this, hinv_mul, one_mul]
        ring
      have hlead : (a * wN * |c|) ^ 2 = wN * wN * wp * c ^ 2 := by
        rw [mul_pow, mul_pow, hsqrt_sq, ← hc_sq]; ring
      rw [hcross, hlead, hinv_sq] at h_amgm
      exact h_amgm
    nlinarith [key, hwN_nonneg, abs_nonneg c, hwp_pos.le]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.MetricRealization.spectralCoeff_weightedPow_summable then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.MetricRealization.spectralCoeff_weightedPow_summable"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.MetricRealization.spectralCoeff_weightedPow_summable ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.spectralCoeff_weightedPow_summable

def TensorSuperCriticalReconstruct (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    Prop :=
  ∀ w : TensorL2 r s g,
    (∀ k : ℕ, ∀ (α : M) (P₀ : TensorCompIdx (E := E) r s),
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (2 * k) 2
        (fun y => (tensorL2ChartComponent (I := I) (M := M) g r s w α P₀ y))
        (chartTargetEuclid (I := I) (M := M) α)) →
    ∃ T : SmoothCcTensor g r s, (T : TensorL2 r s g) = w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.MetricRealization.TensorSuperCriticalReconstruct then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.MetricRealization.TensorSuperCriticalReconstruct"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.MetricRealization.TensorSuperCriticalReconstruct ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.TensorSuperCriticalReconstruct

def SpectralChartRegularity (g : SmoothRiemannianMetric I M) (r s : ℕ) : Prop :=
  ∀ u : TensorL2 r s g, MemAllTensorHs (I := I) (M := M) g r s u →
    ∀ k : ℕ, ∀ (α : M) (P₀ : TensorCompIdx (E := E) r s),
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (2 * k) 2
        (fun y => (tensorL2ChartComponent (I := I) (M := M) g r s u α P₀ y))
        (chartTargetEuclid (I := I) (M := M) α)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.MetricRealization.SpectralChartRegularity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.MetricRealization.SpectralChartRegularity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.MetricRealization.SpectralChartRegularity ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.SpectralChartRegularity

theorem spectralSmooth_realizesAsSmooth_of_reduction
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_regularity : SpectralChartRegularity (I := I) (M := M) g r s)
    (h_recon : TensorSuperCriticalReconstruct (I := I) (M := M) g r s) :
    SpectralSmoothRealizesAsSmooth (I := I) (M := M) g r s := by
  intro u h_mem
  have h_memAll : MemAllTensorHs (I := I) (M := M) g r s u := h_mem
  exact h_recon u (fun k α P₀ => h_regularity u h_memAll k α P₀)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.MetricRealization.spectralSmooth_realizesAsSmooth_of_reduction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.MetricRealization.spectralSmooth_realizesAsSmooth_of_reduction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.MetricRealization.spectralSmooth_realizesAsSmooth_of_reduction ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.spectralSmooth_realizesAsSmooth_of_reduction

end MetricRealization
end Spectral
end Analysis
end DifferentialGeometry

end
