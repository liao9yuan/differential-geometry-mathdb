import Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.FixedPoint.Forcing

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
  {N : TensorHs (I := I) (M := M) g r s (a + 1) →
    TensorHs (I := I) (M := M) g r s a}

omit [NeZero (Module.finrank ℝ E)] in
theorem memLp_comp_nemytskiiHa1 (hN : LipschitzWith L N)
    (f : timeL2 (TensorHs (I := I) (M := M) g r s (a + 1)) T) :
    MemLp (fun t => N (f t)) 2 (timeMeasure T) := by
  have hshift : LipschitzWith L (fun x => N x - N 0) := by
    have hsubL := hN.sub (LipschitzWith.const (N 0))
    rwa [add_zero] at hsubL
  have hshift0 : (fun x => N x - N 0) (0 : TensorHs (I := I) (M := M) g r s
      (a + 1)) = 0 := by simp
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
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.memLp_comp_nemytskiiHa1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.memLp_comp_nemytskiiHa1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.memLp_comp_nemytskiiHa1 ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.memLp_comp_nemytskiiHa1

def nemytskiiHa1 (hN : LipschitzWith L N) :
    timeL2 (TensorHs (I := I) (M := M) g r s (a + 1)) T →
      timeL2 (TensorHs (I := I) (M := M) g r s a) T :=
  fun f => (memLp_comp_nemytskiiHa1 (I := I) (M := M) hN f).toLp (fun t => N (f t))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.nemytskiiHa1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.nemytskiiHa1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.nemytskiiHa1 ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.nemytskiiHa1

omit [NeZero (Module.finrank ℝ E)] in
theorem nemytskiiHa1_coeFn (hN : LipschitzWith L N)
    (f : timeL2 (TensorHs (I := I) (M := M) g r s (a + 1)) T) :
    nemytskiiHa1 (I := I) (M := M) hN f =ᵐ[timeMeasure T] fun t => N (f t) :=
  (memLp_comp_nemytskiiHa1 (I := I) (M := M) hN f).coeFn_toLp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.nemytskiiHa1_coeFn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.nemytskiiHa1_coeFn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.nemytskiiHa1_coeFn ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.nemytskiiHa1_coeFn

omit [NeZero (Module.finrank ℝ E)] in
theorem nemytskiiHa1_dist_sq_le (hN : LipschitzWith L N)
    (f f' : timeL2 (TensorHs (I := I) (M := M) g r s (a + 1)) T) :
    ‖nemytskiiHa1 (I := I) (M := M) hN f -
        nemytskiiHa1 (I := I) (M := M) hN f'‖ ^ 2 ≤
      (L : ℝ) ^ 2 * ‖f - f'‖ ^ 2 := by
  rw [TimeSobolev.norm_sq_eq_integral, TimeSobolev.norm_sq_eq_integral,
    ← MeasureTheory.integral_const_mul]
  have hdiff : ⇑(nemytskiiHa1 (I := I) (M := M) hN f -
        nemytskiiHa1 (I := I) (M := M) hN f') =ᵐ[timeMeasure T]
      fun t => N (f t) - N (f' t) := by
    have hsub := Lp.coeFn_sub (nemytskiiHa1 (I := I) (M := M) hN f)
      (nemytskiiHa1 (I := I) (M := M) hN f')
    have hf := nemytskiiHa1_coeFn (I := I) (M := M) hN f
    have hf' := nemytskiiHa1_coeFn (I := I) (M := M) hN f'
    filter_upwards [hsub, hf, hf'] with t ht htf htf'
    rw [ht, Pi.sub_apply, htf, htf']
  have hfdiff : ⇑(f - f') =ᵐ[timeMeasure T] fun t => f t - f' t :=
    Lp.coeFn_sub f f'
  have hint_fdiff : _root_.MeasureTheory.Integrable (fun t => ‖(f - f') t‖ ^ 2) (timeMeasure T) :=
    (_root_.MeasureTheory.memLp_two_iff_integrable_sq_norm
      (Lp.aestronglyMeasurable (f - f'))).mp (Lp.memLp (f - f'))
  refine _root_.MeasureTheory.integral_mono_ae ?_ ?_ ?_
  · exact (_root_.MeasureTheory.memLp_two_iff_integrable_sq_norm
      (Lp.aestronglyMeasurable (nemytskiiHa1 (I := I) (M := M) hN f -
        nemytskiiHa1 (I := I) (M := M) hN f'))).mp
      (Lp.memLp (nemytskiiHa1 (I := I) (M := M) hN f -
        nemytskiiHa1 (I := I) (M := M) hN f'))
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
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.nemytskiiHa1_dist_sq_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.nemytskiiHa1_dist_sq_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.nemytskiiHa1_dist_sq_le ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.nemytskiiHa1_dist_sq_le

omit [NeZero (Module.finrank ℝ E)] in
theorem nemytskiiHa1_lipschitzWith (hN : LipschitzWith L N) :
    LipschitzWith L (nemytskiiHa1 (I := I) (M := M) (T := T) hN) := by
  refine LipschitzWith.of_dist_le_mul (fun f f' => ?_)
  rw [dist_eq_norm, dist_eq_norm]
  have hsq := nemytskiiHa1_dist_sq_le (I := I) (M := M) hN f f'
  have hrhs_nn : 0 ≤ (L : ℝ) * ‖f - f'‖ := mul_nonneg L.coe_nonneg (norm_nonneg _)
  have hsq' : ‖nemytskiiHa1 (I := I) (M := M) hN f -
        nemytskiiHa1 (I := I) (M := M) hN f'‖ ^ 2 ≤
      ((L : ℝ) * ‖f - f'‖) ^ 2 := by
    rw [mul_pow]; exact hsq
  have h := Real.sqrt_le_sqrt hsq'
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hrhs_nn] at h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.nemytskiiHa1_lipschitzWith then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.nemytskiiHa1_lipschitzWith"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.nemytskiiHa1_lipschitzWith ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.nemytskiiHa1_lipschitzWith

end Nemytskii

omit [NeZero (Module.finrank ℝ E)] in
theorem maximalRegularityDuhamelSolutionFieldHa1_sub (hT : 0 < T) (hT1 : T ≤ 1)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (u₀ : TensorHs (I := I) (M := M) g r s (a + 2))
    (gforce gforce' : timeL2 (TensorHs (I := I) (M := M) g r s a) T) :
    maximalRegularityDuhamelSolutionFieldHa1 (I := I) (M := M) a hT u₀ gforce -
        maximalRegularityDuhamelSolutionFieldHa1 (I := I) (M := M) a hT u₀ gforce' =
      maximalRegularitySolutionFieldHa1 (I := I) (M := M) a hT
        (gforce - gforce') := by
  rw [maximalRegularitySolutionFieldHa1_sub (I := I) (M := M)
    (h_compact := h_compact) (a := a) hT hT1 gforce gforce']
  rw [maximalRegularityDuhamelSolutionFieldHa1, maximalRegularityDuhamelSolutionFieldHa1]
  abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.maximalRegularityDuhamelSolutionFieldHa1_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.maximalRegularityDuhamelSolutionFieldHa1_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.maximalRegularityDuhamelSolutionFieldHa1_sub ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.maximalRegularityDuhamelSolutionFieldHa1_sub

omit [NeZero (Module.finrank ℝ E)] in
theorem maximalRegularityDuhamelSolutionFieldHa1_dist_le (hT : 0 < T) (hT1 : T ≤ 1)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (u₀ : TensorHs (I := I) (M := M) g r s (a + 2))
    (gforce gforce' : timeL2 (TensorHs (I := I) (M := M) g r s a) T) :
    ‖maximalRegularityDuhamelSolutionFieldHa1 (I := I) (M := M) a hT u₀ gforce -
        maximalRegularityDuhamelSolutionFieldHa1 (I := I) (M := M) a hT u₀ gforce'‖ ≤
      2 * Real.sqrt T * ‖gforce - gforce'‖ := by
  rw [maximalRegularityDuhamelSolutionFieldHa1_sub (I := I) (M := M)
    (h_compact := h_compact) (a := a) hT hT1 u₀ gforce gforce']
  exact maximalRegularitySolutionFieldHa1_norm_le (I := I) (M := M)
    (h_compact := h_compact) (a := a) hT hT1 (gforce - gforce')

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.maximalRegularityDuhamelSolutionFieldHa1_dist_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.maximalRegularityDuhamelSolutionFieldHa1_dist_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.maximalRegularityDuhamelSolutionFieldHa1_dist_le ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.maximalRegularityDuhamelSolutionFieldHa1_dist_le

section FixedPoint

def quasilinearDuhamelMapHa1 (a : ℝ) {T : ℝ} (hT : 0 < T)
    (u₀ : TensorHs (I := I) (M := M) g r s (a + 2))
    {L : ℝ≥0}
    {N : TensorHs (I := I) (M := M) g r s (a + 1) →
      TensorHs (I := I) (M := M) g r s a}
    (hN : LipschitzWith L N) :
    timeL2 (TensorHs (I := I) (M := M) g r s a) T →
      timeL2 (TensorHs (I := I) (M := M) g r s a) T :=
  fun gforce => nemytskiiHa1 (I := I) (M := M) hN
    (maximalRegularityDuhamelSolutionFieldHa1 (I := I) (M := M) a hT u₀ gforce)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.quasilinearDuhamelMapHa1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.quasilinearDuhamelMapHa1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.quasilinearDuhamelMapHa1 ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.quasilinearDuhamelMapHa1

omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem quasilinearDuhamelMapHa1_apply (hT : 0 < T)
    (u₀ : TensorHs (I := I) (M := M) g r s (a + 2))
    {L : ℝ≥0}
    {N : TensorHs (I := I) (M := M) g r s (a + 1) →
      TensorHs (I := I) (M := M) g r s a}
    (hN : LipschitzWith L N)
    (gforce : timeL2 (TensorHs (I := I) (M := M) g r s a) T) :
    quasilinearDuhamelMapHa1 (I := I) (M := M) a hT u₀ hN gforce =
      nemytskiiHa1 (I := I) (M := M) hN
        (maximalRegularityDuhamelSolutionFieldHa1 (I := I) (M := M) a hT u₀ gforce) :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.quasilinearDuhamelMapHa1_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.quasilinearDuhamelMapHa1_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.quasilinearDuhamelMapHa1_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.quasilinearDuhamelMapHa1_apply

omit [NeZero (Module.finrank ℝ E)] in
theorem quasilinearDuhamelMapHa1_dist_le (hT : 0 < T) (hT1 : T ≤ 1)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (u₀ : TensorHs (I := I) (M := M) g r s (a + 2))
    {L : ℝ≥0}
    {N : TensorHs (I := I) (M := M) g r s (a + 1) →
      TensorHs (I := I) (M := M) g r s a}
    (hN : LipschitzWith L N)
    (gforce gforce' : timeL2 (TensorHs (I := I) (M := M) g r s a) T) :
    dist (quasilinearDuhamelMapHa1 (I := I) (M := M) a hT u₀ hN gforce)
        (quasilinearDuhamelMapHa1 (I := I) (M := M) a hT u₀ hN gforce') ≤
      (L : ℝ) * (2 * Real.sqrt T) * _root_.Dist.dist gforce gforce' := by
  have hnem := (nemytskiiHa1_lipschitzWith (I := I) (M := M) hN).dist_le_mul
    (maximalRegularityDuhamelSolutionFieldHa1 (I := I) (M := M) a hT u₀ gforce)
    (maximalRegularityDuhamelSolutionFieldHa1 (I := I) (M := M) a hT u₀ gforce')
  have hfield : _root_.Dist.dist
      (maximalRegularityDuhamelSolutionFieldHa1 (I := I) (M := M) a hT u₀ gforce)
      (maximalRegularityDuhamelSolutionFieldHa1 (I := I) (M := M) a hT u₀ gforce') ≤
        (2 * Real.sqrt T) * _root_.Dist.dist gforce gforce' := by
    rw [dist_eq_norm, dist_eq_norm]
    exact maximalRegularityDuhamelSolutionFieldHa1_dist_le (I := I) (M := M)
      (h_compact := h_compact) (a := a) hT hT1 u₀ gforce gforce'
  calc _root_.Dist.dist
        (quasilinearDuhamelMapHa1 (I := I) (M := M) a hT u₀ hN gforce)
        (quasilinearDuhamelMapHa1 (I := I) (M := M) a hT u₀ hN gforce')
      ≤ (L : ℝ) * _root_.Dist.dist
          (maximalRegularityDuhamelSolutionFieldHa1 (I := I) (M := M) a hT u₀ gforce)
          (maximalRegularityDuhamelSolutionFieldHa1 (I := I) (M := M) a hT u₀
            gforce') := hnem
    _ ≤ (L : ℝ) * ((2 * Real.sqrt T) * _root_.Dist.dist gforce gforce') :=
        mul_le_mul_of_nonneg_left hfield L.coe_nonneg
    _ = (L : ℝ) * (2 * Real.sqrt T) * _root_.Dist.dist gforce gforce' := by ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.quasilinearDuhamelMapHa1_dist_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.quasilinearDuhamelMapHa1_dist_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.quasilinearDuhamelMapHa1_dist_le ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.quasilinearDuhamelMapHa1_dist_le

def smallTimeHorizon (L : ℝ≥0) : ℝ :=
  _root_.Min.min 1 (1 / (4 * ((L : ℝ) + 1) ^ 2))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.smallTimeHorizon then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.smallTimeHorizon"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.smallTimeHorizon ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.smallTimeHorizon

theorem smallTimeHorizon_pos (L : ℝ≥0) : 0 < smallTimeHorizon L := by
  refine lt_min one_pos ?_
  have hpos : (0 : ℝ) < 4 * ((L : ℝ) + 1) ^ 2 := by positivity
  positivity

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.smallTimeHorizon_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.smallTimeHorizon_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.smallTimeHorizon_pos ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.smallTimeHorizon_pos

theorem smallTimeHorizon_le_one (L : ℝ≥0) : smallTimeHorizon L ≤ 1 :=
  min_le_left _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.smallTimeHorizon_le_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.smallTimeHorizon_le_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.smallTimeHorizon_le_one ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.smallTimeHorizon_le_one

theorem smallTime_contraction_const_lt_one {L : ℝ≥0} {T : ℝ}
    (hTL : T ≤ smallTimeHorizon L) :
    (L : ℝ) * (2 * Real.sqrt T) < 1 := by
  have hLnn : (0 : ℝ) ≤ (L : ℝ) := L.coe_nonneg
  have hLp1_pos : (0 : ℝ) < (L : ℝ) + 1 := by linarith
  have hTbd : T ≤ 1 / (4 * ((L : ℝ) + 1) ^ 2) :=
    le_trans hTL (min_le_right _ _)
  have hden_pos : (0 : ℝ) < 2 * ((L : ℝ) + 1) := by linarith
  have hsqrtT_le : Real.sqrt T ≤ 1 / (2 * ((L : ℝ) + 1)) := by
    rw [show (1 : ℝ) / (2 * ((L : ℝ) + 1)) =
      Real.sqrt ((1 / (2 * ((L : ℝ) + 1))) ^ 2) from
        (Real.sqrt_sq (by positivity)).symm]
    refine Real.sqrt_le_sqrt (le_trans hTbd ?_)
    have heq : (1 : ℝ) / (4 * ((L : ℝ) + 1) ^ 2) =
        (1 / (2 * ((L : ℝ) + 1))) ^ 2 := by
      rw [div_pow, one_pow, mul_pow]
      norm_num
    rw [heq]
  have hsqrtT_nn : 0 ≤ Real.sqrt T := Real.sqrt_nonneg _
  calc (L : ℝ) * (2 * Real.sqrt T)
      = 2 * (L : ℝ) * Real.sqrt T := by ring
    _ ≤ 2 * (L : ℝ) * (1 / (2 * ((L : ℝ) + 1))) := by
        apply mul_le_mul_of_nonneg_left hsqrtT_le (by positivity)
    _ = (L : ℝ) / ((L : ℝ) + 1) := by
        rw [mul_one_div, mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)]
    _ < 1 := by
        rw [div_lt_one hLp1_pos]; linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.smallTime_contraction_const_lt_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.smallTime_contraction_const_lt_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.smallTime_contraction_const_lt_one ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.smallTime_contraction_const_lt_one

omit [NeZero (Module.finrank ℝ E)] in
theorem quasilinearDuhamelMapHa1_contracting (hT : 0 < T)
    {L : ℝ≥0} (hTL : T ≤ smallTimeHorizon L)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (u₀ : TensorHs (I := I) (M := M) g r s (a + 2))
    {N : TensorHs (I := I) (M := M) g r s (a + 1) →
      TensorHs (I := I) (M := M) g r s a}
    (hN : LipschitzWith L N) :
    ContractingWith
      (NNReal.mk ((L : ℝ) * (2 * Real.sqrt T))
        (mul_nonneg L.coe_nonneg (by positivity)))
      (quasilinearDuhamelMapHa1 (I := I) (M := M) a hT
        u₀ hN) := by
  refine ⟨?_, ?_⟩
  · exact NNReal.coe_lt_coe.mp (by
      simpa only [NNReal.coe_mk, NNReal.coe_one] using
        smallTime_contraction_const_lt_one (L := L) (T := T) hTL)
  · refine LipschitzWith.of_dist_le_mul (fun gforce gforce' => ?_)
    have h := quasilinearDuhamelMapHa1_dist_le (I := I) (M := M)
      (h_compact := h_compact) (a := a) hT
      (le_trans hTL (smallTimeHorizon_le_one L)) u₀ hN gforce gforce'
    simpa only [NNReal.coe_mk] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.quasilinearDuhamelMapHa1_contracting then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.quasilinearDuhamelMapHa1_contracting"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.quasilinearDuhamelMapHa1_contracting ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.quasilinearDuhamelMapHa1_contracting

end FixedPoint

omit [NeZero (Module.finrank ℝ E)] in
theorem quasilinear_strong_existence_smallTime {L : ℝ≥0}
    {N : TensorHs (I := I) (M := M) g r s (a + 1) →
      TensorHs (I := I) (M := M) g r s a}
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (u₀ : TensorHs (I := I) (M := M) g r s (a + 2))
    (hN : LipschitzWith L N) :
    ∃ T_L : ℝ, 0 < T_L ∧ ∀ {T : ℝ} (hT : 0 < T) (_hTL : T ≤ T_L),
      ∃ (u : MaximalRegularitySolutionSpace (I := I) (M := M) a T)
        (gforce : timeL2 (TensorHs (I := I) (M := M) g r s a) T),
        u = maximalRegularityDuhamelMap (I := I) (M := M) a hT u₀ gforce ∧
          gforce = nemytskiiHa1 (I := I) (M := M) hN
              (maximalRegularityDuhamelSolutionFieldHa1 (I := I) (M := M) a hT u₀ gforce) ∧
          TimeSobolev.timeH1.trace0 _ T u =
              tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
                (show a ≤ a + 2 by linarith) u₀ ∧
          TimeSobolev.timeH1.timeDeriv _ T u =
            timeScaleLaplacian (I := I) (M := M) a
                (maximalRegularityDuhamelSolutionField (I := I) (M := M) a hT u₀ gforce) +
              nemytskiiHa1 (I := I) (M := M) hN
                (maximalRegularityDuhamelSolutionFieldHa1 (I := I) (M := M) a hT u₀
                  gforce) := by
  refine ⟨smallTimeHorizon L, smallTimeHorizon_pos L, ?_⟩
  intro T hT hTL
  have hcontr := quasilinearDuhamelMapHa1_contracting (I := I) (M := M)
    (h_compact := h_compact) (a := a) hT hTL u₀ hN
  set gStar := ContractingWith.fixedPoint
    (quasilinearDuhamelMapHa1 (I := I) (M := M) a hT u₀ hN) hcontr
    with hgStar_def
  have hgStar_fix :
      quasilinearDuhamelMapHa1 (I := I) (M := M) a hT u₀ hN gStar =
        gStar :=
    ContractingWith.fixedPoint_isFixedPt hcontr
  have hgStar_eq : gStar = nemytskiiHa1 (I := I) (M := M) hN
      (maximalRegularityDuhamelSolutionFieldHa1 (I := I) (M := M) a hT u₀ gStar) := by
    rw [← quasilinearDuhamelMapHa1_apply (I := I) (M := M) (a := a) hT u₀ hN
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
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.quasilinear_strong_existence_smallTime then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.quasilinear_strong_existence_smallTime"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.quasilinear_strong_existence_smallTime ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.quasilinear_strong_existence_smallTime

end QuasiLinear
end Parabolic
end Analysis
end DifferentialGeometry

end
