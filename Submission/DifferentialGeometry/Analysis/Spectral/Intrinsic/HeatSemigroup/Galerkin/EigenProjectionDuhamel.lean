import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.Projection.TimeL2EigenProjection
import Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Solution.Space

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators _root_.NNReal
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral hiding TensorEigenIdx
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open _root_.Submission.DifferentialGeometry.Analysis.Spectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

variable (g : SmoothRiemannianMetric I M)

open scoped _root_.Classical in
omit [BoundarylessManifold I M] in
theorem spatialProj_coeff (σ : ℝ) (N : ℕ)
    (W : TensorHs (I := I) (M := M) g 0 2 σ)
    (i : TensorEigenIdx (I := I) (M := M) g 0 2) :
    (spatialEigenProj (I := I) (M := M) g σ N W).coeff i =
      if i ∈ eigenIdxFinset (I := I) (M := M) g N then W.coeff i else 0 := by
  rw [spatialEigenProj_apply, finiteEigenComboHs_coeff]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.spatialProj_coeff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.spatialProj_coeff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.spatialProj_coeff ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.spatialProj_coeff

open scoped _root_.Classical in
omit [BoundarylessManifold I M] in
theorem spatialProj_idem (σ : ℝ) (N : ℕ)
    (W : TensorHs (I := I) (M := M) g 0 2 σ) :
    spatialEigenProj (I := I) (M := M) g σ N
        (spatialEigenProj (I := I) (M := M) g σ N W) =
      spatialEigenProj (I := I) (M := M) g σ N W := by
  classical
  refine TensorHs.ext (funext fun i => ?_)
  simp only [spatialProj_coeff]
  by_cases hi : i ∈ eigenIdxFinset (I := I) (M := M) g N <;> simp [hi]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.spatialProj_idem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.spatialProj_idem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.spatialProj_idem ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.spatialProj_idem

omit [BoundarylessManifold I M] in
theorem spatialProj_lip (σ : ℝ) (N : ℕ) :
    LipschitzWith 1 (spatialEigenProj (I := I) (M := M) g σ N) := by
  refine LipschitzWith.of_dist_le_mul (fun W W' => ?_)
  rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm, ← map_sub]
  exact norm_spatialEigenProj_apply_le (I := I) (M := M) g σ N (W - W')

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.spatialProj_lip then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.spatialProj_lip"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.spatialProj_lip ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.spatialProj_lip

open scoped _root_.Classical in
omit [BoundarylessManifold I M] in
theorem timeProj_modeCoeff (σ T : ℝ) (N : ℕ)
    (f : timeL2 (TensorHs (I := I) (M := M) g 0 2 σ) T)
    (i : TensorEigenIdx (I := I) (M := M) g 0 2) :
    timeModeCoeff (I := I) (M := M)
        (timeL2EigenProj (I := I) (M := M) g σ T N f) i =
      if i ∈ eigenIdxFinset (I := I) (M := M) g N then
        timeModeCoeff (I := I) (M := M) f i else 0 := by
  classical
  have hL := timeModeCoeff_coeFn (I := I) (M := M)
    (timeL2EigenProj (I := I) (M := M) g σ T N f) i
  have hP : ⇑(timeL2EigenProj (I := I) (M := M) g σ T N f) =ᵐ[timeMeasure T]
      fun t => spatialEigenProj (I := I) (M := M) g σ N (f t) :=
    ContinuousLinearMap.coeFn_compLpL _ f
  by_cases hi : i ∈ eigenIdxFinset (I := I) (M := M) g N
  · rw [if_pos hi]
    refine MeasureTheory.Lp.ext ?_
    filter_upwards [hL, hP, timeModeCoeff_coeFn (I := I) (M := M) f i]
      with t h1 h2 h3
    rw [h1, h2, spatialProj_coeff, if_pos hi, h3]
  · rw [if_neg hi]
    refine MeasureTheory.Lp.ext ?_
    filter_upwards [hL, hP, MeasureTheory.Lp.coeFn_zero ℝ 2 (timeMeasure T)]
      with t h1 h2 h3
    rw [h1, h2, spatialProj_coeff, if_neg hi, h3, Pi.zero_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.timeProj_modeCoeff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.timeProj_modeCoeff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.timeProj_modeCoeff ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.timeProj_modeCoeff

open scoped _root_.Classical in
omit [BoundarylessManifold I M] in
theorem proj_solutionModeCoeff {a T : ℝ} (hT : 0 ≤ T) (N : ℕ)
    (f : timeL2 (TensorHs (I := I) (M := M) g 0 2 a) T)
    (i : TensorEigenIdx (I := I) (M := M) g 0 2) :
    solutionModeCoeff (I := I) (M := M) (a := a) hT
        (timeL2EigenProj (I := I) (M := M) g a T N f) i =
      if i ∈ eigenIdxFinset (I := I) (M := M) g N then
        solutionModeCoeff (I := I) (M := M) (a := a) hT f i else 0 := by
  classical
  rw [solutionModeCoeff, timeProj_modeCoeff]
  by_cases hi : i ∈ eigenIdxFinset (I := I) (M := M) g N
  · rw [if_pos hi, if_pos hi, solutionModeCoeff]
  · rw [if_neg hi, if_neg hi, map_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.proj_solutionModeCoeff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.proj_solutionModeCoeff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.proj_solutionModeCoeff ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.proj_solutionModeCoeff

open scoped _root_.Classical in
omit [BoundarylessManifold I M] in
theorem proj_derivModeCoeff {a T : ℝ} (hT : 0 ≤ T) (N : ℕ)
    (f : timeL2 (TensorHs (I := I) (M := M) g 0 2 a) T)
    (i : TensorEigenIdx (I := I) (M := M) g 0 2) :
    derivModeCoeff (I := I) (M := M) (a := a) hT
        (timeL2EigenProj (I := I) (M := M) g a T N f) i =
      if i ∈ eigenIdxFinset (I := I) (M := M) g N then
        derivModeCoeff (I := I) (M := M) (a := a) hT f i else 0 := by
  classical
  rw [derivModeCoeff, timeProj_modeCoeff]
  by_cases hi : i ∈ eigenIdxFinset (I := I) (M := M) g N
  · rw [if_pos hi, if_pos hi, derivModeCoeff]
  · rw [if_neg hi, if_neg hi, map_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.proj_derivModeCoeff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.proj_derivModeCoeff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.proj_derivModeCoeff ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.proj_derivModeCoeff

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma homModeCoeFn {a T : ℝ}
    (u₀ : TensorHs (I := I) (M := M) g 0 2 (a + 2))
    (i : TensorEigenIdx (I := I) (M := M) g 0 2) :
    ⇑(homModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i) =ᵐ[timeMeasure T]
      fun t => Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
        u₀.coeff i :=
  coeFn_ofContinuousOn _

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.homModeCoeFn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.homModeCoeFn target :: scope.openDecls } }

open scoped _root_.Classical in
omit [BoundarylessManifold I M] in
theorem proj_homModeCoeff {a T : ℝ} (N : ℕ)
    (u₀ : TensorHs (I := I) (M := M) g 0 2 (a + 2))
    (i : TensorEigenIdx (I := I) (M := M) g 0 2) :
    homModeCoeff (I := I) (M := M) (a := a) (T := T)
        (spatialEigenProj (I := I) (M := M) g (a + 2) N u₀) i =
      if i ∈ eigenIdxFinset (I := I) (M := M) g N then
        homModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i else 0 := by
  classical
  have hL := homModeCoeFn (I := I) (M := M) (a := a) (T := T) g
    (spatialEigenProj (I := I) (M := M) g (a + 2) N u₀) i
  by_cases hi : i ∈ eigenIdxFinset (I := I) (M := M) g N
  · rw [if_pos hi]
    refine MeasureTheory.Lp.ext ?_
    filter_upwards [hL, homModeCoeFn (I := I) (M := M) (a := a) (T := T) g u₀ i]
      with t h1 h2
    rw [h1, h2, spatialProj_coeff, if_pos hi]
  · rw [if_neg hi]
    refine MeasureTheory.Lp.ext ?_
    filter_upwards [hL, MeasureTheory.Lp.coeFn_zero ℝ 2 (timeMeasure T)]
      with t h1 h2
    rw [h1, h2, spatialProj_coeff, if_neg hi, _root_.MulZeroClass.mul_zero, Pi.zero_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.proj_homModeCoeff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.proj_homModeCoeff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.proj_homModeCoeff ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.proj_homModeCoeff

omit [BoundarylessManifold I M] in
theorem proj_solutionField_comm {a T : ℝ} (hT : 0 ≤ T) (N : ℕ)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g 0 2))
    (f : timeL2 (TensorHs (I := I) (M := M) g 0 2 a) T) :
    maximalRegularitySolutionField (I := I) (M := M) a hT
        (timeL2EigenProj (I := I) (M := M) g a T N f) =
      timeL2EigenProj (I := I) (M := M) g (a + 2) T N
        (maximalRegularitySolutionField (I := I) (M := M) a hT f) := by
  classical
  refine timeModeCoeff_injective (I := I) (M := M) h_compact (fun i => ?_)
  rw [maximalRegularitySolutionField_timeModeCoeff (I := I) (M := M) (a := a) hT
      h_compact (timeL2EigenProj (I := I) (M := M) g a T N f) i,
    proj_solutionModeCoeff (I := I) (M := M) g hT N f i,
    timeProj_modeCoeff (I := I) (M := M) g (a + 2) T N
      (maximalRegularitySolutionField (I := I) (M := M) a hT f) i,
    maximalRegularitySolutionField_timeModeCoeff (I := I) (M := M) (a := a) hT
      h_compact f i]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.proj_solutionField_comm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.proj_solutionField_comm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.proj_solutionField_comm ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.proj_solutionField_comm

omit [BoundarylessManifold I M] in
theorem proj_derivField_comm {a T : ℝ} (hT : 0 ≤ T) (N : ℕ)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g 0 2))
    (f : timeL2 (TensorHs (I := I) (M := M) g 0 2 a) T) :
    maximalRegularityDerivField (I := I) (M := M) a hT
        (timeL2EigenProj (I := I) (M := M) g a T N f) =
      timeL2EigenProj (I := I) (M := M) g a T N
        (maximalRegularityDerivField (I := I) (M := M) a hT f) := by
  classical
  refine timeModeCoeff_injective (I := I) (M := M) h_compact (fun i => ?_)
  rw [maximalRegularityDerivField_timeModeCoeff (I := I) (M := M) (a := a) hT
      h_compact (timeL2EigenProj (I := I) (M := M) g a T N f) i,
    proj_derivModeCoeff (I := I) (M := M) g hT N f i,
    timeProj_modeCoeff (I := I) (M := M) g a T N
      (maximalRegularityDerivField (I := I) (M := M) a hT f) i,
    maximalRegularityDerivField_timeModeCoeff (I := I) (M := M) (a := a) hT
      h_compact f i]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.proj_derivField_comm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.proj_derivField_comm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.proj_derivField_comm ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.proj_derivField_comm

omit [BoundarylessManifold I M] in
theorem proj_homField_comm {a T : ℝ} (hT : 0 ≤ T) (N : ℕ)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g 0 2))
    (u₀ : TensorHs (I := I) (M := M) g 0 2 (a + 2)) :
    maximalRegularityHomogeneousSolutionField (I := I) (M := M) a T
        (spatialEigenProj (I := I) (M := M) g (a + 2) N u₀) =
      timeL2EigenProj (I := I) (M := M) g (a + 2) T N
        (maximalRegularityHomogeneousSolutionField (I := I) (M := M) a T u₀) := by
  classical
  refine timeModeCoeff_injective (I := I) (M := M) h_compact (fun i => ?_)
  rw [maximalRegularityHomogeneousSolutionField_timeModeCoeff (I := I) (M := M) (a := a) (T := T)
      hT (spatialEigenProj (I := I) (M := M) g (a + 2) N u₀) i,
    proj_homModeCoeff (I := I) (M := M) g N u₀ i,
    timeProj_modeCoeff (I := I) (M := M) g (a + 2) T N
      (maximalRegularityHomogeneousSolutionField (I := I) (M := M) a T u₀) i,
    maximalRegularityHomogeneousSolutionField_timeModeCoeff (I := I) (M := M) (a := a) (T := T)
      hT u₀ i]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.proj_homField_comm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.proj_homField_comm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.proj_homField_comm ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.proj_homField_comm

omit [BoundarylessManifold I M] in
theorem proj_duhamel_comm {a T : ℝ} (hT : 0 < T) (N : ℕ)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g 0 2))
    (u₀ : TensorHs (I := I) (M := M) g 0 2 (a + 2))
    (f : timeL2 (TensorHs (I := I) (M := M) g 0 2 a) T) :
    maximalRegularityDuhamelSolutionField (I := I) (M := M) a hT
        (spatialEigenProj (I := I) (M := M) g (a + 2) N u₀)
        (timeL2EigenProj (I := I) (M := M) g a T N f) =
      timeL2EigenProj (I := I) (M := M) g (a + 2) T N
        (maximalRegularityDuhamelSolutionField (I := I) (M := M) a hT u₀ f) := by
  rw [maximalRegularityDuhamelSolutionField, maximalRegularityDuhamelSolutionField, map_add,
    proj_homField_comm (I := I) (M := M) g hT.le N h_compact u₀,
    proj_solutionField_comm (I := I) (M := M) g hT.le N h_compact f]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.proj_duhamel_comm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.proj_duhamel_comm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.proj_duhamel_comm ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.proj_duhamel_comm

omit [BoundarylessManifold I M] in
theorem projDuhamel_zero {a T : ℝ} (hT : 0 < T) (N : ℕ)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g 0 2))
    (f : timeL2 (TensorHs (I := I) (M := M) g 0 2 a) T) :
    maximalRegularityDuhamelSolutionField (I := I) (M := M) a hT
        (0 : TensorHs (I := I) (M := M) g 0 2 (a + 2))
        (timeL2EigenProj (I := I) (M := M) g a T N f) =
      timeL2EigenProj (I := I) (M := M) g (a + 2) T N
        (maximalRegularityDuhamelSolutionField (I := I) (M := M) a hT
          (0 : TensorHs (I := I) (M := M) g 0 2 (a + 2)) f) := by
  have h := proj_duhamel_comm (I := I) (M := M) g hT N h_compact
    (0 : TensorHs (I := I) (M := M) g 0 2 (a + 2)) f
  rwa [map_zero] at h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.projDuhamel_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.projDuhamel_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.projDuhamel_zero ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.projDuhamel_zero

omit [BoundarylessManifold I M] in
theorem proj_maximalRegularityOp_deriv {a T : ℝ} (hT : 0 < T) (N : ℕ)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g 0 2))
    (f : timeL2 (TensorHs (I := I) (M := M) g 0 2 a) T) :
    timeH1.timeDeriv _ T
        (maximalRegularityOp (I := I) (M := M) a hT
          (timeL2EigenProj (I := I) (M := M) g a T N f)) =
      timeL2EigenProj (I := I) (M := M) g a T N
        (timeH1.timeDeriv _ T
          (maximalRegularityOp (I := I) (M := M) a hT f)) := by
  rw [maximalRegularityOp_timeDeriv, maximalRegularityOp_timeDeriv,
    proj_derivField_comm (I := I) (M := M) g hT.le N h_compact f]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.proj_maximalRegularityOp_deriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.proj_maximalRegularityOp_deriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.proj_maximalRegularityOp_deriv ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.proj_maximalRegularityOp_deriv

omit [BoundarylessManifold I M] in
theorem projSolution_mode_zero {a T : ℝ} (hT : 0 ≤ T) (N : ℕ)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g 0 2))
    (f : timeL2 (TensorHs (I := I) (M := M) g 0 2 a) T)
    {i : TensorEigenIdx (I := I) (M := M) g 0 2}
    (hi : i ∉ eigenIdxFinset (I := I) (M := M) g N) :
    timeModeCoeff (I := I) (M := M)
      (maximalRegularitySolutionField (I := I) (M := M) a hT
        (timeL2EigenProj (I := I) (M := M) g a T N f)) i = 0 := by
  rw [maximalRegularitySolutionField_timeModeCoeff (I := I) (M := M) (a := a) hT
      h_compact (timeL2EigenProj (I := I) (M := M) g a T N f) i,
    proj_solutionModeCoeff (I := I) (M := M) g hT N f i, if_neg hi]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.projSolution_mode_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.projSolution_mode_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.projSolution_mode_zero ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.projSolution_mode_zero

omit [BoundarylessManifold I M] in
theorem projSolution_fixed {a T : ℝ} (hT : 0 ≤ T) (N : ℕ)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g 0 2))
    (f : timeL2 (TensorHs (I := I) (M := M) g 0 2 a) T) :
    timeL2EigenProj (I := I) (M := M) g (a + 2) T N
        (maximalRegularitySolutionField (I := I) (M := M) a hT
          (timeL2EigenProj (I := I) (M := M) g a T N f)) =
      maximalRegularitySolutionField (I := I) (M := M) a hT
        (timeL2EigenProj (I := I) (M := M) g a T N f) := by
  classical
  refine timeModeCoeff_injective (I := I) (M := M) h_compact (fun i => ?_)
  rw [timeProj_modeCoeff (I := I) (M := M) g (a + 2) T N
      (maximalRegularitySolutionField (I := I) (M := M) a hT
        (timeL2EigenProj (I := I) (M := M) g a T N f)) i]
  by_cases hi : i ∈ eigenIdxFinset (I := I) (M := M) g N
  · rw [if_pos hi]
  · rw [if_neg hi,
      projSolution_mode_zero (I := I) (M := M) g hT N h_compact f hi]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.projSolution_fixed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.projSolution_fixed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.projSolution_fixed ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.projSolution_fixed

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
