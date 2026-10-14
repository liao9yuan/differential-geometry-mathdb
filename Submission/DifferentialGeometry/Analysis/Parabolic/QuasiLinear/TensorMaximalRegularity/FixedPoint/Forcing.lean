import Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Solution.Space
import Mathlib.Topology.MetricSpace.Contracting

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace QuasiLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity

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

variable {g : SmoothRiemannianMetric I M} {r s : ℕ}
variable {a : ℝ} {T : ℝ}

section Nemytskii

variable {L : ℝ≥0}
  {N : TensorHs (I := I) (M := M) g r s (a + 2) →
    TensorHs (I := I) (M := M) g r s a}

omit [NeZero (Module.finrank ℝ E)] in
theorem memLp_comp_nemytskii (hN : LipschitzWith L N)
    (f : timeL2 (TensorHs (I := I) (M := M) g r s (a + 2)) T) :
    MemLp (fun t => N (f t)) 2 (timeMeasure T) := by
  have hshift : LipschitzWith L (fun x => N x - N 0) := by
    have hsubL := hN.sub (LipschitzWith.const (N 0))
    rwa [add_zero] at hsubL
  have hshift0 : (fun x => N x - N 0) (0 : TensorHs (I := I) (M := M) g r s
      (a + 2)) = 0 := by simp
  have hcomp : _root_.MeasureTheory.MemLp ((fun x => N x - N 0) ∘ fun t => f t) 2 (timeMeasure T) :=
    hshift.comp_memLp hshift0 (Lp.memLp f)
  have hconst : _root_.MeasureTheory.MemLp (fun _ : ℝ => N 0) 2 (timeMeasure T) :=
    _root_.MeasureTheory.memLp_const (N 0)
  have hsum : _root_.MeasureTheory.MemLp (fun t => (N (f t) - N 0) + N 0) 2 (timeMeasure T) :=
    hcomp.add hconst
  have hfun : (fun t => N (f t)) =
      fun t => (N (f t) - N 0) + N 0 := by
    funext t; abel
  rw [hfun]
  exact hsum

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.memLp_comp_nemytskii then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.memLp_comp_nemytskii"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.memLp_comp_nemytskii ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.memLp_comp_nemytskii

def nemytskii (hN : LipschitzWith L N) :
    timeL2 (TensorHs (I := I) (M := M) g r s (a + 2)) T →
      timeL2 (TensorHs (I := I) (M := M) g r s a) T :=
  fun f => (memLp_comp_nemytskii (I := I) (M := M) hN f).toLp (fun t => N (f t))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.nemytskii then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.nemytskii"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.nemytskii ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.nemytskii

omit [NeZero (Module.finrank ℝ E)] in
theorem nemytskii_coeFn (hN : LipschitzWith L N)
    (f : timeL2 (TensorHs (I := I) (M := M) g r s (a + 2)) T) :
    nemytskii (I := I) (M := M) hN f =ᵐ[timeMeasure T] fun t => N (f t) :=
  (memLp_comp_nemytskii (I := I) (M := M) hN f).coeFn_toLp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.nemytskii_coeFn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.nemytskii_coeFn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.nemytskii_coeFn ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.nemytskii_coeFn

omit [NeZero (Module.finrank ℝ E)] in
theorem nemytskii_dist_sq_le (hN : LipschitzWith L N)
    (f f' : timeL2 (TensorHs (I := I) (M := M) g r s (a + 2)) T) :
    ‖nemytskii (I := I) (M := M) hN f - nemytskii (I := I) (M := M) hN f'‖ ^ 2 ≤
      (L : ℝ) ^ 2 * ‖f - f'‖ ^ 2 := by
  rw [TimeSobolev.norm_sq_eq_integral, TimeSobolev.norm_sq_eq_integral,
    ← MeasureTheory.integral_const_mul]
  have hdiff : ⇑(nemytskii (I := I) (M := M) hN f -
        nemytskii (I := I) (M := M) hN f') =ᵐ[timeMeasure T]
      fun t => N (f t) - N (f' t) := by
    have hsub := Lp.coeFn_sub (nemytskii (I := I) (M := M) hN f)
      (nemytskii (I := I) (M := M) hN f')
    have hf := nemytskii_coeFn (I := I) (M := M) hN f
    have hf' := nemytskii_coeFn (I := I) (M := M) hN f'
    filter_upwards [hsub, hf, hf'] with t ht htf htf'
    rw [ht, Pi.sub_apply, htf, htf']
  have hfdiff : ⇑(f - f') =ᵐ[timeMeasure T] fun t => f t - f' t :=
    Lp.coeFn_sub f f'
  have hint_fdiff : _root_.MeasureTheory.Integrable (fun t => ‖(f - f') t‖ ^ 2) (timeMeasure T) :=
    (_root_.MeasureTheory.memLp_two_iff_integrable_sq_norm
      (Lp.aestronglyMeasurable (f - f'))).mp (Lp.memLp (f - f'))
  refine _root_.MeasureTheory.integral_mono_ae ?_ ?_ ?_
  · exact (_root_.MeasureTheory.memLp_two_iff_integrable_sq_norm
      (Lp.aestronglyMeasurable (nemytskii (I := I) (M := M) hN f -
        nemytskii (I := I) (M := M) hN f'))).mp
      (Lp.memLp (nemytskii (I := I) (M := M) hN f -
        nemytskii (I := I) (M := M) hN f'))
  · exact hint_fdiff.const_mul ((L : ℝ) ^ 2)
  · filter_upwards [hdiff, hfdiff] with t ht htf
    rw [ht]
    have hlip : ‖N (f t) - N (f' t)‖ ≤ (L : ℝ) * ‖f t - f' t‖ := by
      rw [← dist_eq_norm, ← dist_eq_norm]
      exact hN.dist_le_mul (f t) (f' t)
    have hnn : 0 ≤ ‖N (f t) - N (f' t)‖ := norm_nonneg _
    have hsq : ‖N (f t) - N (f' t)‖ ^ 2 ≤ ((L : ℝ) * ‖f t - f' t‖) ^ 2 := by
      have hrhs_nn : 0 ≤ (L : ℝ) * ‖f t - f' t‖ :=
        mul_nonneg L.coe_nonneg (norm_nonneg _)
      nlinarith [hlip, hnn, hrhs_nn]
    calc ‖N (f t) - N (f' t)‖ ^ 2
        ≤ ((L : ℝ) * ‖f t - f' t‖) ^ 2 := hsq
      _ = (L : ℝ) ^ 2 * ‖(f - f') t‖ ^ 2 := by rw [htf, mul_pow]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.nemytskii_dist_sq_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.nemytskii_dist_sq_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.nemytskii_dist_sq_le ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.nemytskii_dist_sq_le

omit [NeZero (Module.finrank ℝ E)] in
theorem nemytskii_lipschitzWith (hN : LipschitzWith L N) :
    LipschitzWith L (nemytskii (I := I) (M := M) (T := T) hN) := by
  refine LipschitzWith.of_dist_le_mul (fun f f' => ?_)
  rw [dist_eq_norm, dist_eq_norm]
  have hsq := nemytskii_dist_sq_le (I := I) (M := M) hN f f'
  have hrhs_nn : 0 ≤ (L : ℝ) * ‖f - f'‖ := mul_nonneg L.coe_nonneg (norm_nonneg _)
  have hsq' : ‖nemytskii (I := I) (M := M) hN f -
        nemytskii (I := I) (M := M) hN f'‖ ^ 2 ≤ ((L : ℝ) * ‖f - f'‖) ^ 2 := by
    rw [mul_pow]; exact hsq
  have h := Real.sqrt_le_sqrt hsq'
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hrhs_nn] at h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.nemytskii_lipschitzWith then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.nemytskii_lipschitzWith"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.nemytskii_lipschitzWith ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.nemytskii_lipschitzWith

end Nemytskii

omit [NeZero (Module.finrank ℝ E)] in
theorem maximalRegularitySolutionField_add (hT : 0 ≤ T)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (f f' : timeL2 (TensorHs (I := I) (M := M) g r s a) T) :
    maximalRegularitySolutionField (I := I) (M := M) a hT (f + f') =
      maximalRegularitySolutionField (I := I) (M := M) a hT f +
        maximalRegularitySolutionField (I := I) (M := M) a hT f' := by
  refine timeModeCoeff_injective (I := I) (M := M) h_compact
    (fun i => ?_)
  rw [maximalRegularitySolutionField_timeModeCoeff (I := I) (M := M)
      (h_compact := h_compact) (a := a) hT (f + f') i,
    timeModeCoeff_add (I := I) (M := M),
    maximalRegularitySolutionField_timeModeCoeff (I := I) (M := M)
      (h_compact := h_compact) (a := a) hT f i,
    maximalRegularitySolutionField_timeModeCoeff (I := I) (M := M)
      (h_compact := h_compact) (a := a) hT f' i]
  rw [solutionModeCoeff, solutionModeCoeff, solutionModeCoeff,
    timeModeCoeff_add (I := I) (M := M), map_add]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.maximalRegularitySolutionField_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.maximalRegularitySolutionField_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.maximalRegularitySolutionField_add ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.maximalRegularitySolutionField_add

omit [NeZero (Module.finrank ℝ E)] in
theorem maximalRegularitySolutionField_sub (hT : 0 ≤ T)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (f f' : timeL2 (TensorHs (I := I) (M := M) g r s a) T) :
    maximalRegularitySolutionField (I := I) (M := M) a hT (f - f') =
      maximalRegularitySolutionField (I := I) (M := M) a hT f -
        maximalRegularitySolutionField (I := I) (M := M) a hT f' := by
  have hadd := maximalRegularitySolutionField_add (I := I) (M := M)
    (h_compact := h_compact) (a := a) hT (f - f') f'
  rw [sub_add_cancel] at hadd
  rw [hadd, add_sub_cancel_right]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.maximalRegularitySolutionField_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.maximalRegularitySolutionField_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.maximalRegularitySolutionField_sub ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.maximalRegularitySolutionField_sub

omit [NeZero (Module.finrank ℝ E)] in
theorem maximalRegularityDuhamelSolutionField_sub (hT : 0 < T)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (u₀ : TensorHs (I := I) (M := M) g r s (a + 2))
    (gforce gforce' : timeL2 (TensorHs (I := I) (M := M) g r s a) T) :
    maximalRegularityDuhamelSolutionField (I := I) (M := M) a hT u₀ gforce -
        maximalRegularityDuhamelSolutionField (I := I) (M := M) a hT u₀ gforce' =
      maximalRegularitySolutionField (I := I) (M := M) a hT.le
        (gforce - gforce') := by
  rw [maximalRegularitySolutionField_sub (I := I) (M := M)
    (h_compact := h_compact) (a := a) hT.le gforce gforce']
  rw [maximalRegularityDuhamelSolutionField, maximalRegularityDuhamelSolutionField]
  abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.maximalRegularityDuhamelSolutionField_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.maximalRegularityDuhamelSolutionField_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.maximalRegularityDuhamelSolutionField_sub ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.maximalRegularityDuhamelSolutionField_sub

omit [NeZero (Module.finrank ℝ E)] in
theorem maximalRegularityDuhamelSolutionField_dist_le (hT : 0 < T)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (u₀ : TensorHs (I := I) (M := M) g r s (a + 2))
    (gforce gforce' : timeL2 (TensorHs (I := I) (M := M) g r s a) T) :
    ‖maximalRegularityDuhamelSolutionField (I := I) (M := M) a hT u₀ gforce -
        maximalRegularityDuhamelSolutionField (I := I) (M := M) a hT u₀ gforce'‖ ≤
      (1 + T) * ‖gforce - gforce'‖ := by
  rw [maximalRegularityDuhamelSolutionField_sub (I := I) (M := M)
    (h_compact := h_compact) (a := a) hT u₀ gforce gforce']
  exact maximalRegularityOp_norm_Ha2_le (I := I) (M := M)
    (h_compact := h_compact) (a := a) hT (gforce - gforce')

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.maximalRegularityDuhamelSolutionField_dist_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.maximalRegularityDuhamelSolutionField_dist_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.maximalRegularityDuhamelSolutionField_dist_le ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.maximalRegularityDuhamelSolutionField_dist_le

section FixedPoint

def quasilinearDuhamelMap (a : ℝ) {T : ℝ} (hT : 0 < T)
    (u₀ : TensorHs (I := I) (M := M) g r s (a + 2))
    {L : ℝ≥0}
    {N : TensorHs (I := I) (M := M) g r s (a + 2) →
      TensorHs (I := I) (M := M) g r s a}
    (hN : LipschitzWith L N) :
    timeL2 (TensorHs (I := I) (M := M) g r s a) T →
      timeL2 (TensorHs (I := I) (M := M) g r s a) T :=
  fun gforce => nemytskii (I := I) (M := M) hN
    (maximalRegularityDuhamelSolutionField (I := I) (M := M) a hT u₀ gforce)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.quasilinearDuhamelMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.quasilinearDuhamelMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.quasilinearDuhamelMap ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.quasilinearDuhamelMap

omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem quasilinearDuhamelMap_apply (hT : 0 < T)
    (u₀ : TensorHs (I := I) (M := M) g r s (a + 2))
    {L : ℝ≥0}
    {N : TensorHs (I := I) (M := M) g r s (a + 2) →
      TensorHs (I := I) (M := M) g r s a}
    (hN : LipschitzWith L N)
    (gforce : timeL2 (TensorHs (I := I) (M := M) g r s a) T) :
    quasilinearDuhamelMap (I := I) (M := M) a hT u₀ hN gforce =
      nemytskii (I := I) (M := M) hN
        (maximalRegularityDuhamelSolutionField (I := I) (M := M) a hT u₀ gforce) :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.quasilinearDuhamelMap_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.quasilinearDuhamelMap_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.quasilinearDuhamelMap_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.quasilinearDuhamelMap_apply

omit [NeZero (Module.finrank ℝ E)] in
theorem quasilinearDuhamelMap_dist_le (hT : 0 < T)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (u₀ : TensorHs (I := I) (M := M) g r s (a + 2))
    {L : ℝ≥0}
    {N : TensorHs (I := I) (M := M) g r s (a + 2) →
      TensorHs (I := I) (M := M) g r s a}
    (hN : LipschitzWith L N)
    (gforce gforce' : timeL2 (TensorHs (I := I) (M := M) g r s a) T) :
    dist (quasilinearDuhamelMap (I := I) (M := M) a hT u₀ hN gforce)
        (quasilinearDuhamelMap (I := I) (M := M) a hT u₀ hN
          gforce') ≤
      (L : ℝ) * (1 + T) * _root_.Dist.dist gforce gforce' := by
  have hnem := (nemytskii_lipschitzWith (I := I) (M := M) hN).dist_le_mul
    (maximalRegularityDuhamelSolutionField (I := I) (M := M) a hT u₀ gforce)
    (maximalRegularityDuhamelSolutionField (I := I) (M := M) a hT u₀ gforce')
  have hfield : _root_.Dist.dist
      (maximalRegularityDuhamelSolutionField (I := I) (M := M) a hT u₀ gforce)
      (maximalRegularityDuhamelSolutionField (I := I) (M := M) a hT u₀ gforce') ≤
        (1 + T) * _root_.Dist.dist gforce gforce' := by
    rw [dist_eq_norm, dist_eq_norm]
    exact maximalRegularityDuhamelSolutionField_dist_le (I := I) (M := M)
      (h_compact := h_compact) (a := a) hT u₀ gforce gforce'
  calc _root_.Dist.dist
        (quasilinearDuhamelMap (I := I) (M := M) a hT u₀ hN gforce)
        (quasilinearDuhamelMap (I := I) (M := M) a hT u₀ hN
          gforce')
      ≤ (L : ℝ) * _root_.Dist.dist
          (maximalRegularityDuhamelSolutionField (I := I) (M := M) a hT u₀ gforce)
          (maximalRegularityDuhamelSolutionField (I := I) (M := M) a hT u₀
            gforce') := hnem
    _ ≤ (L : ℝ) * ((1 + T) * _root_.Dist.dist gforce gforce') :=
        mul_le_mul_of_nonneg_left hfield L.coe_nonneg
    _ = (L : ℝ) * (1 + T) * _root_.Dist.dist gforce gforce' := by ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.quasilinearDuhamelMap_dist_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.quasilinearDuhamelMap_dist_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.quasilinearDuhamelMap_dist_le ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.quasilinearDuhamelMap_dist_le

theorem quasilinear_contraction_const_lt_one {L : ℝ≥0} {T : ℝ} (hT1 : T ≤ 1)
    (hL : 2 * (L : ℝ) < 1) :
    (L : ℝ) * (1 + T) < 1 := by
  have hLnn : (0 : ℝ) ≤ (L : ℝ) := L.coe_nonneg
  have h1T : (1 : ℝ) + T ≤ 2 := by linarith
  calc (L : ℝ) * (1 + T) ≤ (L : ℝ) * 2 :=
        mul_le_mul_of_nonneg_left h1T hLnn
    _ = 2 * (L : ℝ) := by ring
    _ < 1 := hL

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.quasilinear_contraction_const_lt_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.quasilinear_contraction_const_lt_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.quasilinear_contraction_const_lt_one ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.quasilinear_contraction_const_lt_one

omit [NeZero (Module.finrank ℝ E)] in
theorem quasilinearDuhamelMap_contracting (hT : 0 < T) (hT1 : T ≤ 1)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (u₀ : TensorHs (I := I) (M := M) g r s (a + 2))
    {L : ℝ≥0}
    {N : TensorHs (I := I) (M := M) g r s (a + 2) →
      TensorHs (I := I) (M := M) g r s a}
    (hN : LipschitzWith L N) (hL : 2 * (L : ℝ) < 1) :
    ContractingWith
      (NNReal.mk ((L : ℝ) * (1 + T))
        (mul_nonneg L.coe_nonneg (by linarith [hT.le])))
      (quasilinearDuhamelMap (I := I) (M := M) a hT u₀ hN) := by
  refine ⟨?_, ?_⟩
  · exact NNReal.coe_lt_coe.mp (by
      simpa only [NNReal.coe_mk, NNReal.coe_one] using quasilinear_contraction_const_lt_one
        (L := L) (T := T) hT1 hL)
  · refine LipschitzWith.of_dist_le_mul (fun gforce gforce' => ?_)
    have h := quasilinearDuhamelMap_dist_le (I := I) (M := M)
      (h_compact := h_compact) (a := a) hT u₀ hN gforce gforce'
    simpa only [NNReal.coe_mk] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.quasilinearDuhamelMap_contracting then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.quasilinearDuhamelMap_contracting"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.quasilinearDuhamelMap_contracting ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.quasilinearDuhamelMap_contracting

end FixedPoint

omit [NeZero (Module.finrank ℝ E)] in
theorem quasilinear_strong_existence {L : ℝ≥0}
    {N : TensorHs (I := I) (M := M) g r s (a + 2) →
      TensorHs (I := I) (M := M) g r s a}
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (hT : 0 < T) (hT1 : T ≤ 1)
    (u₀ : TensorHs (I := I) (M := M) g r s (a + 2))
    (hN : LipschitzWith L N) (hL : 2 * (L : ℝ) < 1) :
    ∃ (u : MaximalRegularitySolutionSpace (I := I) (M := M) a T)
      (gforce : timeL2 (TensorHs (I := I) (M := M) g r s a) T),
      u = maximalRegularityDuhamelMap (I := I) (M := M) a hT u₀ gforce ∧
        gforce = nemytskii (I := I) (M := M) hN
            (maximalRegularityDuhamelSolutionField (I := I) (M := M) a hT u₀
              gforce) ∧
        TimeSobolev.timeH1.trace0 _ T u =
            tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
              (show a ≤ a + 2 by linarith) u₀ ∧
        TimeSobolev.timeH1.timeDeriv _ T u =
          timeScaleLaplacian (I := I) (M := M) a
              (maximalRegularityDuhamelSolutionField (I := I) (M := M) a hT u₀
                gforce) +
            nemytskii (I := I) (M := M) hN
              (maximalRegularityDuhamelSolutionField (I := I) (M := M) a hT u₀
                gforce) := by
  have hcontr := quasilinearDuhamelMap_contracting (I := I) (M := M)
    (h_compact := h_compact) (a := a) hT hT1 u₀ hN hL
  set gStar := ContractingWith.fixedPoint
    (quasilinearDuhamelMap (I := I) (M := M) a hT u₀ hN) hcontr
    with hgStar_def
  have hgStar_fix :
      quasilinearDuhamelMap (I := I) (M := M) a hT u₀ hN gStar =
        gStar :=
    ContractingWith.fixedPoint_isFixedPt hcontr
  have hgStar_eq : gStar = nemytskii (I := I) (M := M) hN
      (maximalRegularityDuhamelSolutionField (I := I) (M := M) a hT u₀ gStar) := by
    rw [← quasilinearDuhamelMap_apply (I := I) (M := M) (a := a) hT u₀ hN
      gStar, hgStar_fix]
  refine ⟨maximalRegularityDuhamelMap (I := I) (M := M) a hT u₀ gStar,
    gStar, rfl, hgStar_eq, ?_, ?_⟩
  · exact maximalRegularityDuhamelMap_trace0 (I := I) (M := M) (a := a) (T := T)
      hT u₀ gStar
  · rw [maximalRegularityDuhamelMap_timeDeriv_eq (I := I) (M := M)
      (h_compact := h_compact) (a := a) (T := T) hT u₀ gStar]
    exact congrArg₂ (· + ·) rfl hgStar_eq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.quasilinear_strong_existence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.quasilinear_strong_existence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.quasilinear_strong_existence ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.quasilinear_strong_existence

omit [NeZero (Module.finrank ℝ E)] in
theorem quasilinear_strong_unique {L : ℝ≥0}
    {N : TensorHs (I := I) (M := M) g r s (a + 2) →
      TensorHs (I := I) (M := M) g r s a}
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (hT : 0 < T) (hT1 : T ≤ 1)
    (u₀ : TensorHs (I := I) (M := M) g r s (a + 2))
    (hN : LipschitzWith L N) (hL : 2 * (L : ℝ) < 1)
    {gforce₁ gforce₂ : timeL2 (TensorHs (I := I) (M := M) g r s a) T}
    (hg₁ : gforce₁ = nemytskii (I := I) (M := M) hN
      (maximalRegularityDuhamelSolutionField (I := I) (M := M) a hT u₀ gforce₁))
    (hg₂ : gforce₂ = nemytskii (I := I) (M := M) hN
      (maximalRegularityDuhamelSolutionField (I := I) (M := M) a hT u₀ gforce₂)) :
    gforce₁ = gforce₂ ∧
      maximalRegularityDuhamelMap (I := I) (M := M) a hT u₀ gforce₁ =
        maximalRegularityDuhamelMap (I := I) (M := M) a hT u₀ gforce₂ := by
  have hcontr := quasilinearDuhamelMap_contracting (I := I) (M := M)
    (h_compact := h_compact) (a := a) hT hT1 u₀ hN hL
  have hfix₁ :
      Function.IsFixedPt
        (quasilinearDuhamelMap (I := I) (M := M) a hT u₀ hN)
        gforce₁ := by
    change quasilinearDuhamelMap (I := I) (M := M) a hT u₀ hN
        gforce₁ = gforce₁
    rw [quasilinearDuhamelMap_apply (I := I) (M := M) (a := a) hT u₀ hN
      gforce₁]
    exact hg₁.symm
  have hfix₂ :
      Function.IsFixedPt
        (quasilinearDuhamelMap (I := I) (M := M) a hT u₀ hN)
        gforce₂ := by
    change quasilinearDuhamelMap (I := I) (M := M) a hT u₀ hN
        gforce₂ = gforce₂
    rw [quasilinearDuhamelMap_apply (I := I) (M := M) (a := a) hT u₀ hN
      gforce₂]
    exact hg₂.symm
  have hgeq : gforce₁ = gforce₂ := by
    rw [ContractingWith.fixedPoint_unique hcontr hfix₁,
      ContractingWith.fixedPoint_unique hcontr hfix₂]
  exact ⟨hgeq, by rw [hgeq]⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.quasilinear_strong_unique then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.quasilinear_strong_unique"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.quasilinear_strong_unique ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.quasilinear_strong_unique

end QuasiLinear
end Parabolic
end Analysis
end DifferentialGeometry

end
