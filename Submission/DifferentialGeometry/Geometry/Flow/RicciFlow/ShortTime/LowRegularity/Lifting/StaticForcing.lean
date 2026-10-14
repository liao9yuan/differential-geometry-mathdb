import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Lifting.SecondOrder
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Lifting.SmallTimeBounds
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.Remainder.ZeroOrderBounds
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Solution.FixedPoint

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.NNReal _root_.InnerProductSpace _root_.BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Tensor.RSTensor
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Integral.Connection
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization

section TimeConst

variable {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [CompleteSpace X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [CompleteSpace Y]

def timeConstL2 (T : ℝ) (x : X) : timeL2 X T :=
  (_root_.MeasureTheory.memLp_const (μ := timeMeasure T) (p := 2) x).toLp _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.timeConstL2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.timeConstL2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.timeConstL2 ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.timeConstL2

omit [InnerProductSpace ℝ X] [CompleteSpace X] in
theorem timeConstL2_coeFn (T : ℝ) (x : X) :
    timeConstL2 T x =ᵐ[timeMeasure T] fun _ => x :=
  MemLp.coeFn_toLp _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.timeConstL2_coeFn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.timeConstL2_coeFn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.timeConstL2_coeFn ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.timeConstL2_coeFn

omit [InnerProductSpace ℝ X] [CompleteSpace X] in
theorem norm_timeConstL2_le (T : ℝ) (x : X) :
    ‖timeConstL2 T x‖ ≤ ‖x‖ * Real.sqrt T :=
  norm_toLp_le_bd (_root_.MeasureTheory.memLp_const (μ := timeMeasure T) (p := 2) x) (norm_nonneg x)
    (Filter.Eventually.of_forall fun _ => le_rfl)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.norm_timeConstL2_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.norm_timeConstL2_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.norm_timeConstL2_le ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.norm_timeConstL2_le

omit [CompleteSpace X] [CompleteSpace Y] in
theorem compLpL_timeConstL2 (L : X →L[ℝ] Y) (T : ℝ) (x : X) :
    L.compLpL 2 (timeMeasure T) (timeConstL2 T x) = timeConstL2 T (L x) := by
  refine Lp.ext ?_
  have h1 := L.coeFn_compLpL (p := 2) (μ := timeMeasure T) (timeConstL2 T x)
  have h2 := timeConstL2_coeFn (X := X) T x
  have h3 := timeConstL2_coeFn (X := Y) T (L x)
  filter_upwards [h1, h2, h3] with t ht1 ht2 ht3
  rw [ht1, ht2, ht3]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.compLpL_timeConstL2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.compLpL_timeConstL2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.compLpL_timeConstL2 ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.compLpL_timeConstL2

end TimeConst

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem timeL2Inclusion_const {g : SmoothRiemannianMetric I M} {τ σ : ℝ}
    (hτσ : τ ≤ σ) (T : ℝ) (x : TensorHs (I := I) (M := M) g 0 2 σ) :
    timeL2Inclusion (I := I) (M := M) (g := g) (r := 0) (s := 2) hτσ
        (timeConstL2 T x) =
      timeConstL2 T
        (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          hτσ x) :=
  compLpL_timeConstL2 _ T x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.timeL2Inclusion_const then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.timeL2Inclusion_const"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.timeL2Inclusion_const ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.timeL2Inclusion_const

def staticForce (g₀ g_bg : SmoothRiemannianMetric I M) (σ : ℝ) :
    TensorHs (I := I) (M := M) g₀ 0 2 σ :=
  smoothCcToTensorHs (I := I) (M := M) g₀ σ
    (deTurckRHSSection (I := I) g_bg g₀)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.staticForce then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.staticForce"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.staticForce ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.staticForce

theorem staticForce_incl (g₀ g_bg : SmoothRiemannianMetric I M) {τ σ : ℝ}
    (hτσ : τ ≤ σ) :
    tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2) hτσ
        (staticForce (I := I) (M := M) g₀ g_bg σ) =
      staticForce (I := I) (M := M) g₀ g_bg τ :=
  tensorHsInclusion_smoothCcToTensorHs (I := I) (M := M) g₀ hτσ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.staticForce_incl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.staticForce_incl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.staticForce_incl ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.staticForce_incl

theorem staticForce_congr (g₀ g_bg : SmoothRiemannianMetric I M) {a b : ℝ}
    (hab : a = b) :
    tensorHsCongr (I := I) (M := M) g₀ 0 2 hab
        (staticForce (I := I) (M := M) g₀ g_bg a) =
      staticForce (I := I) (M := M) g₀ g_bg b := by
  cases hab
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.staticForce_congr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.staticForce_congr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.staticForce_congr ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.staticForce_congr

theorem staticForcing_eq_zeroStateDeTurckRemainderH2 (g₀ g_bg : SmoothRiemannianMetric I M) :
    zeroStateDeTurckRemainderH2 (I := I) (M := M) g₀ g_bg =
      staticForce (I := I) (M := M) g₀ g_bg (2 : ℝ) := by
  refine Eq.trans (congrArg (ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ))
    (deTurckRem_zero (I := I) (M := M) g₀ g_bg _ _)) ?_
  exact TensorHs.ext (funext fun _ => rfl)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.staticForcing_eq_zeroStateDeTurckRemainderH2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.staticForcing_eq_zeroStateDeTurckRemainderH2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.staticForcing_eq_zeroStateDeTurckRemainderH2 ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.staticForcing_eq_zeroStateDeTurckRemainderH2

theorem lowerScaleForce_eq_static (g : SmoothRiemannianMetric I M) :
    lowerScaleForce (I := I) (M := M) g =
      staticForce (I := I) (M := M) g g (1 : ℝ) := by
  refine Eq.trans (congrArg
    (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
      (by norm_num : (1 : ℝ) ≤ (2 : ℝ)))
    (staticForcing_eq_zeroStateDeTurckRemainderH2 (I := I) (M := M) g g)) ?_
  exact staticForce_incl (I := I) (M := M) g g _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowerScaleForce_eq_static then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowerScaleForce_eq_static"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowerScaleForce_eq_static ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowerScaleForce_eq_static

theorem deTurckRemainderOnLowerState_zero_eq_staticForce (g₀ g_bg : SmoothRiemannianMetric I M) {R δ : ℝ}
    (hR : 0 < R) (hδ : δ < 1)
    (hreal : ∀ T : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) T‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hcore : Continuous (deTurckRemainderOnSmoothCore (I := I) (M := M) g₀ g_bg hδ hreal)) :
    deTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hR hδ hreal
        ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1 hR.le⟩ =
      staticForce (I := I) (M := M) g₀ g_bg ((1 : ℕ) : ℝ) :=
  deTurckRemainderOnLowerState_zero_eq_deTurckRHS (I := I) (M := M) g₀ g_bg hR hδ hreal hcore

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.deTurckRemainderOnLowerState_zero_eq_staticForce then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.deTurckRemainderOnLowerState_zero_eq_staticForce"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.deTurckRemainderOnLowerState_zero_eq_staticForce ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.deTurckRemainderOnLowerState_zero_eq_staticForce

theorem deTurckRemainderOnLowerState_zero_h1_eq_staticForce (g₀ g_bg : SmoothRiemannianMetric I M) {R δ : ℝ}
    (hR : 0 < R) (hδ : δ < 1)
    (hreal : ∀ T : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) T‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hcore : Continuous (deTurckRemainderOnSmoothCore (I := I) (M := M) g₀ g_bg hδ hreal)) :
    tensorHsCongr (I := I) (M := M) g₀ 0 2
        (show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num)
        (deTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hR hδ hreal
          ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1 hR.le⟩) =
      staticForce (I := I) (M := M) g₀ g_bg (1 : ℝ) := by
  refine Eq.trans (congrArg
    (fun v => tensorHsCongr (I := I) (M := M) g₀ 0 2
      (show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num) v)
    (deTurckRemainderOnLowerState_zero_eq_staticForce (I := I) (M := M) g₀ g_bg hR hδ hreal hcore)) ?_
  exact staticForce_congr (I := I) (M := M) g₀ g_bg _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.deTurckRemainderOnLowerState_zero_h1_eq_staticForce then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.deTurckRemainderOnLowerState_zero_h1_eq_staticForce"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.deTurckRemainderOnLowerState_zero_h1_eq_staticForce ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.deTurckRemainderOnLowerState_zero_h1_eq_staticForce

def liftForceHi (g₀ g_bg : SmoothRiemannianMetric I M) (T : ℝ) :
    timeL2 (TensorHs (I := I) (M := M) g₀ 0 2 (2 : ℝ)) T :=
  timeConstL2 T (staticForce (I := I) (M := M) g₀ g_bg (2 : ℝ))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.liftForceHi then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.liftForceHi"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.liftForceHi ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.liftForceHi

def liftForceLo (g₀ g_bg : SmoothRiemannianMetric I M) (T : ℝ) :
    timeL2 (TensorHs (I := I) (M := M) g₀ 0 2 (1 : ℝ)) T :=
  timeConstL2 T (staticForce (I := I) (M := M) g₀ g_bg (1 : ℝ))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.liftForceLo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.liftForceLo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.liftForceLo ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.liftForceLo

theorem timeConst_static_incl (g₀ g_bg : SmoothRiemannianMetric I M) {τ σ : ℝ}
    (hτσ : τ ≤ σ) (T : ℝ) :
    timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2) hτσ
        (timeConstL2 T (staticForce (I := I) (M := M) g₀ g_bg σ)) =
      timeConstL2 T (staticForce (I := I) (M := M) g₀ g_bg τ) := by
  rw [timeL2Inclusion_const, staticForce_incl]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.timeConst_static_incl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.timeConst_static_incl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.timeConst_static_incl ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.timeConst_static_incl

theorem lift_force_incl (g₀ g_bg : SmoothRiemannianMetric I M) (T : ℝ) :
    timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (by norm_num : (1 : ℝ) ≤ (2 : ℝ))
        (liftForceHi (I := I) (M := M) g₀ g_bg T) =
      liftForceLo (I := I) (M := M) g₀ g_bg T :=
  timeConst_static_incl (I := I) (M := M) g₀ g_bg _ T

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lift_force_incl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lift_force_incl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lift_force_incl ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lift_force_incl

theorem norm_liftForceHi_le (g₀ g_bg : SmoothRiemannianMetric I M) (T : ℝ)
    {D : ℝ} (hD : ‖staticForce (I := I) (M := M) g₀ g_bg (2 : ℝ)‖ ≤ D) :
    ‖liftForceHi (I := I) (M := M) g₀ g_bg T‖ ≤ D * Real.sqrt T :=
  (norm_timeConstL2_le T _).trans
    (mul_le_mul_of_nonneg_right hD (Real.sqrt_nonneg T))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.norm_liftForceHi_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.norm_liftForceHi_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.norm_liftForceHi_le ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.norm_liftForceHi_le

theorem norm_liftForceLo_le (g₀ g_bg : SmoothRiemannianMetric I M) (T : ℝ)
    {D : ℝ} (hD : ‖staticForce (I := I) (M := M) g₀ g_bg (1 : ℝ)‖ ≤ D) :
    ‖liftForceLo (I := I) (M := M) g₀ g_bg T‖ ≤ D * Real.sqrt T :=
  (norm_timeConstL2_le T _).trans
    (mul_le_mul_of_nonneg_right hD (Real.sqrt_nonneg T))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.norm_liftForceLo_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.norm_liftForceLo_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.norm_liftForceLo_le ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.norm_liftForceLo_le

theorem liftForceLo_lowerScale (g : SmoothRiemannianMetric I M) (T : ℝ) :
    liftForceLo (I := I) (M := M) g g T =
      timeConstL2 T (lowerScaleForce (I := I) (M := M) g) := by
  rw [liftForceLo, lowerScaleForce_eq_static]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.liftForceLo_lowerScale then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.liftForceLo_lowerScale"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.liftForceLo_lowerScale ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.liftForceLo_lowerScale

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
