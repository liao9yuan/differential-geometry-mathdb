import Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Duhamel.ZeroCrossTerm
import Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.Interpolation.TimeL2Limit

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace QuasiLinear

open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open _root_.Submission.DifferentialGeometry.Analysis.Spectral

theorem memLp_clm_affine
    {T : ℝ} {X Y Z : Type*}
    [NormedAddCommGroup X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (u : timeL2 X T) (A : ℝ → Y →L[ℝ] Z)
    (hA : _root_.MeasureTheory.AEStronglyMeasurable A (timeMeasure T))
    {L Z₀ : ℝ} (hL : 0 ≤ L) (hZ₀ : 0 ≤ Z₀)
    (hbound : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ Z₀ + L * ‖u t‖) :
    ∃ hmem : _root_.MeasureTheory.MemLp A 2 (timeMeasure T),
      ‖hmem.toLp A‖ ≤ L * ‖u‖ + Real.sqrt T * Z₀ := by
  let U : ℝ → ℝ := fun t => ‖(u : ℝ → X) t‖
  let C : ℝ → ℝ := fun _ => Z₀
  have hU : _root_.MeasureTheory.MemLp U 2 (timeMeasure T) := by
    simpa only [U] using (Lp.memLp u).norm
  have hC : _root_.MeasureTheory.MemLp C 2 (timeMeasure T) := by
    simpa only [C] using (_root_.MeasureTheory.memLp_const (μ := timeMeasure T) Z₀)
  have hCU : _root_.MeasureTheory.MemLp (C + L • U) 2 (timeMeasure T) :=
    hC.add (hU.const_smul L)
  have hmajor :
      ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ ‖(C + L • U) t‖ := by
    filter_upwards [hbound] with t ht
    have hnonneg : 0 ≤ Z₀ + L * ‖u t‖ :=
      add_nonneg hZ₀ (mul_nonneg hL (norm_nonneg _))
    simpa only [C, U, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Real.norm_eq_abs, abs_of_nonneg hnonneg] using ht
  let hmem : _root_.MeasureTheory.MemLp A 2 (timeMeasure T) := hCU.mono hA hmajor
  refine ⟨hmem, ?_⟩
  have hdom :
      ∀ᵐ t ∂timeMeasure T,
        ‖(hmem.toLp A) t‖ ≤ ‖(hCU.toLp (C + L • U)) t‖ := by
    filter_upwards [hmem.coeFn_toLp, hCU.coeFn_toLp, hmajor] with t hAt hCUt ht
    simpa only [hAt, hCUt] using ht
  have hCnorm : ‖hC.toLp C‖ = Real.sqrt T * Z₀ := by
    have heq :
        hC.toLp C = TimeSobolev.const T Z₀ := by
      unfold TimeSobolev.const
      apply MemLp.toLp_congr
      exact Filter.Eventually.of_forall (fun _ => rfl)
    rw [heq, TimeSobolev.norm_const, Real.norm_eq_abs, abs_of_nonneg hZ₀]
  have hUnorm : ‖hU.toLp U‖ = ‖u‖ := by
    rw [Lp.norm_toLp, Lp.norm_def]
    simp only [U, _root_.MeasureTheory.eLpNorm_norm]
  calc
    ‖hmem.toLp A‖ ≤ ‖hCU.toLp (C + L • U)‖ :=
      Lp.norm_le_norm_of_ae_le hdom
    _ = ‖hC.toLp C + L • hU.toLp U‖ := by
      rw [hC.toLp_add (hU.const_smul L), hU.toLp_const_smul]
    _ ≤ ‖hC.toLp C‖ + ‖L • hU.toLp U‖ := norm_add_le _ _
    _ = L * ‖u‖ + Real.sqrt T * Z₀ := by
      rw [hCnorm, norm_smul, Real.norm_eq_abs, abs_of_nonneg hL, hUnorm]
      ac_rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.memLp_clm_affine then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.memLp_clm_affine"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.memLp_clm_affine ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.memLp_clm_affine

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem duhamel_incl
    {g : SmoothRiemannianMetric I M} {r s : ℕ} {a T : ℝ}
    (hT : 0 < T) (hT1 : T ≤ 1)
    (hcompact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (u₀ : TensorHs (I := I) (M := M) g r s (a + 2))
    (f : timeL2 (TensorHs (I := I) (M := M) g r s a) T) :
    timeL2Inclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        (show a + 1 ≤ a + 2 by linarith)
        (maximalRegularityDuhamelSolutionField (I := I) (M := M)
          a hT u₀ f) =
      maximalRegularityDuhamelSolutionFieldHa1 (I := I) (M := M)
        a hT u₀ f := by
  refine timeModeCoeff_injective (I := I) (M := M) hcompact (fun i => ?_)
  rw [timeModeCoeff_timeL2Inclusion (I := I) (M := M),
    maximalRegularityDuhamelSolutionField, maximalRegularityDuhamelSolutionFieldHa1,
    timeModeCoeff_add (I := I) (M := M),
    timeModeCoeff_add (I := I) (M := M),
    maximalRegularityHomogeneousSolutionField_timeModeCoeff (I := I) (M := M)
      (a := a) (T := T) hT.le u₀ i,
    maximalRegularityHomogeneousSolutionFieldHa1_timeModeCoeff (I := I) (M := M)
      (a := a) (T := T) hT.le u₀ i,
    maximalRegularitySolutionField_timeModeCoeff (I := I) (M := M)
      (h_compact := hcompact) (a := a) hT.le f i,
    maximalRegularitySolutionFieldHa1_timeModeCoeff (I := I) (M := M)
      (h_compact := hcompact) (a := a) hT hT1 f i]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.duhamel_incl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.duhamel_incl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.duhamel_incl ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.duhamel_incl

end QuasiLinear
end Parabolic
end Analysis
end DifferentialGeometry

end
