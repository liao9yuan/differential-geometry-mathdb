import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.MetricLaplacianDifference.Core
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.Positivity.PositiveDefinitePerturbation
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.Metric.UniformEquivalence
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.Metric.C1Continuity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

noncomputable section
set_option backward.isDefEq.respectTransparency false

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators _root_.InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Spectral

open _root_.Submission.DifferentialGeometry.Integral.L2

open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

section LapDiffOperator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete Real E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instCompleteSpace_differentialGeometry target :: scope.openDecls } }
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

noncomputable def lapDiffA2
    {D : RealTimeInterval}
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (T : D.RegularTime) (s : Real) :
    TensorHs (I := I) (M := M) (g_fam (T : Real)) 0 0 2 →L[Real]
      TensorL2 0 0 (g_fam (T : Real)) :=
  lapDiffOp (I := I) (M := M) (g_fam (T : Real))
    (g_fam ((T : Real) - s))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.lapDiffA2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.lapDiffA2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.lapDiffA2 ``Submission.DifferentialGeometry.Analysis.Spectral.lapDiffA2

end LapDiffOperator

section MetricShortTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instCompleteSpace_differentialGeometry_1 : CompleteSpace E := FiniteDimensional.complete Real E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instCompleteSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instCompleteSpace_differentialGeometry_1 target :: scope.openDecls } }

omit [NeZero (Module.finrank Real E)] [BoundarylessManifold I M] in
omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
private theorem lapDiff_rho
    {D : RealTimeInterval}
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam)
    (T : D.RegularTime) :
    _root_.Filter.Tendsto
      (fun s : Real =>
        CheegerGromovCompactness.metricDerivNormSupOn (I := I) Set.univ 1
          (g_fam ((T : Real) - s))
          (g_fam (T : Real)) (g_fam (T : Real)))
      (𝓝 0) (𝓝 0) := by
  have hshift :
      _root_.Filter.Tendsto (fun s : Real => (T : Real) - s)
        (𝓝 0) (𝓝 (T : Real)) := by
    simpa only [id_eq, sub_zero] using
      (tendsto_const_nhds.sub
        (_root_.Filter.tendsto_id : _root_.Filter.Tendsto (fun s : Real => s) (𝓝 0) (𝓝 0)))
  exact (CheegerGromovCompactness.metric_c1_tendsto
    (I := I) g_fam hG T).comp hshift

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.lapDiff_rho
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.lapDiff_rho target :: scope.openDecls } }

omit [NeZero (Module.finrank Real E)] [BoundarylessManifold I M] in
omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem lapDiff_fibreSmall
    {D : RealTimeInterval}
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam)
    (T : D.RegularTime) :
    ∀ᶠ s in 𝓝 (0 : Real),
      MetricRealization.metricCauchySchwarzBound (I := I) (g_fam (T : Real))
        (fun x : M =>
          (g_fam ((T : Real) - s)).inner x - (g_fam (T : Real)).inner x)
        (1 / 4 : Real) := by
  let q : SmoothRiemannianMetric I M := g_fam (T : Real)
  let rho : Real → Real := fun s =>
    CheegerGromovCompactness.metricDerivNormSupOn (I := I) Set.univ 1
      (g_fam ((T : Real) - s)) q q
  have hrho : _root_.Filter.Tendsto rho (𝓝 0) (𝓝 0) := by
    simpa only [rho, q] using lapDiff_rho (I := I) g_fam hG T
  have hsmall : ∀ᶠ s in 𝓝 (0 : Real), rho s < (1 / 4 : Real) :=
    hrho.eventually_lt_const (by norm_num)
  filter_upwards [hsmall] with s hs
  intro x v w
  have hnorm :
      CheegerGromovCompactness.metricDerivNorm (I := I) 0
          (g_fam ((T : Real) - s)) q q x ≤ rho s := by
    simpa only [rho] using
      (CheegerGromovCompactness.derivNorm_le_sup (I := I) (K := Set.univ)
        isCompact_univ (a := 0) (p := 1) (by omega)
        (g_fam ((T : Real) - s)) q q (Set.mem_univ x))
  have heval := CheegerGromovCompactness.metricDifference_abs_le (I := I)
    (g_fam ((T : Real) - s)) q q x v w
  have hfinal :
      |(g_fam ((T : Real) - s)).inner x v w - q.inner x v w| ≤
        (1 / 4 : Real) * Real.sqrt (q.inner x v v) * Real.sqrt (q.inner x w w) :=
    heval.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hnorm.trans hs.le) (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _))
  simpa only [q, sub_apply] using hfinal

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.lapDiff_fibreSmall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.lapDiff_fibreSmall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.lapDiff_fibreSmall ``Submission.DifferentialGeometry.Analysis.Spectral.lapDiff_fibreSmall

omit [NeZero (Module.finrank Real E)] [BoundarylessManifold I M] in
omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem lapDiff_short
    {D : RealTimeInterval}
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam)
    (T : D.RegularTime) :
    ∃ tau : Real, 0 < tau ∧ tau ≤ 1 ∧
      ∀ s ∈ Set.Icc (0 : Real) tau,
        (T : Real) - s ∈ D.regular ∧
          MetricRealization.metricCauchySchwarzBound (I := I) (g_fam (T : Real))
            (fun x : M =>
              (g_fam ((T : Real) - s)).inner x -
                (g_fam (T : Real)).inner x)
            (1 / 4 : Real) := by
  have hshift :
      _root_.Filter.Tendsto (fun s : Real => (T : Real) - s)
        (𝓝 0) (𝓝 (T : Real)) := by
    simpa only [id_eq, sub_zero] using
      (tendsto_const_nhds.sub
        (_root_.Filter.tendsto_id : _root_.Filter.Tendsto (fun s : Real => s) (𝓝 0) (𝓝 0)))
  have hreg :
      ∀ᶠ s in 𝓝 (0 : Real), (T : Real) - s ∈ D.regular :=
    hshift.eventually (D.regular_isOpen.mem_nhds T.2)
  have hsmall := lapDiff_fibreSmall (I := I) (M := M) g_fam hG T
  let U : Set Real := {s |
    (T : Real) - s ∈ D.regular ∧
      MetricRealization.metricCauchySchwarzBound (I := I) (g_fam (T : Real))
        (fun x : M =>
          (g_fam ((T : Real) - s)).inner x -
            (g_fam (T : Real)).inner x)
        (1 / 4 : Real)}
  have hU : U ∈ 𝓝 (0 : Real) := by
    change ∀ᶠ s in 𝓝 (0 : Real),
      (T : Real) - s ∈ D.regular ∧
        MetricRealization.metricCauchySchwarzBound (I := I) (g_fam (T : Real))
          (fun x : M =>
            (g_fam ((T : Real) - s)).inner x -
              (g_fam (T : Real)).inner x)
          (1 / 4 : Real)
    filter_upwards [hreg, hsmall] with s hs hr
    exact ⟨hs, hr⟩
  obtain ⟨delta, hdelta, hball⟩ := Metric.mem_nhds_iff.mp hU
  let tau : Real := _root_.Min.min 1 (delta / 2)
  have htau : 0 < tau := by
    dsimp only [tau]
    exact lt_min zero_lt_one (half_pos hdelta)
  have htau_one : tau ≤ 1 := min_le_left _ _
  have htau_delta : tau < delta :=
    (min_le_right (1 : Real) (delta / 2)).trans_lt (half_lt_self hdelta)
  refine ⟨tau, htau, htau_one, ?_⟩
  intro s hs
  have hsball : s ∈ Metric.ball (0 : Real) delta := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hs.1]
    exact hs.2.trans_lt htau_delta
  change s ∈ U
  exact hball hsball

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.lapDiff_short then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.lapDiff_short"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.lapDiff_short ``Submission.DifferentialGeometry.Analysis.Spectral.lapDiff_short

end MetricShortTime

section LapDiffOperator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instCompleteSpace_differentialGeometry_2 : CompleteSpace E := FiniteDimensional.complete Real E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instCompleteSpace_differentialGeometry_2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instCompleteSpace_differentialGeometry_2 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry_2 : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry_2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry_2 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry_2 : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry_2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry_2 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry_3 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry_3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry_3 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry_3 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry_3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry_3 target :: scope.openDecls } }

theorem eventually_lapDiffA2_apply_scalarH2Core
    {D : RealTimeInterval}
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam)
    (T : D.RegularTime) :
    ∀ᶠ s in 𝓝 (0 : Real),
      ∀ v : ScalarH2Core (I := I) (M := M) (g_fam (T : Real)),
        lapDiffA2 (I := I) (M := M) g_fam T s v.1 =
          lapDiffCore (I := I) (M := M) (g_fam (T : Real))
            (g_fam ((T : Real) - s)) v := by
  let rho : Real → Real := fun s =>
    CheegerGromovCompactness.metricDerivNormSupOn (I := I) Set.univ 1
      (g_fam ((T : Real) - s))
      (g_fam (T : Real)) (g_fam (T : Real))
  have hrho : _root_.Filter.Tendsto rho (𝓝 0) (𝓝 0) := by
    simpa only [rho] using lapDiff_rho (I := I) g_fam hG T
  have hsmall :
      ∀ᶠ s in 𝓝 (0 : Real),
        (Module.finrank Real E : Real) * rho s < (1 / 2 : Real) :=
    (hrho.const_mul (Module.finrank Real E : Real)).eventually_lt_const
      (by norm_num)
  filter_upwards [hsmall] with s hs
  intro v
  exact lapDiffOp_apply_scalarH2Core (I := I) (M := M)
    (g_fam (T : Real)) (g_fam ((T : Real) - s)) v hs.le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.eventually_lapDiffA2_apply_scalarH2Core then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.eventually_lapDiffA2_apply_scalarH2Core"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.eventually_lapDiffA2_apply_scalarH2Core ``Submission.DifferentialGeometry.Analysis.Spectral.eventually_lapDiffA2_apply_scalarH2Core

theorem lapDiffA2_bound
    {D : RealTimeInterval}
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam)
    (T : D.RegularTime) :
    ∃ omega : Real → Real,
      _root_.Filter.Tendsto omega (𝓝 0) (𝓝 0) ∧
      ∀ᶠ s in 𝓝 (0 : Real),
        ∀ v : TensorHs (I := I) (M := M)
            (g_fam (T : Real)) 0 0 2,
          (Function.support v.coeff).Finite →
            ‖lapDiffA2 (I := I) (M := M) g_fam T s v‖ <=
              omega s * ‖v‖ := by
  obtain ⟨C, hC, hop⟩ :=
    lapDiffOp_norm (I := I) (M := M) (g_fam (T : Real))
  let rho : Real → Real := fun s =>
    CheegerGromovCompactness.metricDerivNormSupOn (I := I) Set.univ 1
      (g_fam ((T : Real) - s))
      (g_fam (T : Real)) (g_fam (T : Real))
  let omega : Real → Real := fun s => Real.sqrt C * |rho s|
  have hrho : _root_.Filter.Tendsto rho (𝓝 0) (𝓝 0) := by
    simpa only [rho] using lapDiff_rho (I := I) g_fam hG T
  have homega : _root_.Filter.Tendsto omega (𝓝 0) (𝓝 0) := by
    simpa only [omega, abs_zero, _root_.MulZeroClass.mul_zero] using
      hrho.abs.const_mul (Real.sqrt C)
  have hsmall :
      ∀ᶠ s in 𝓝 (0 : Real),
        (Module.finrank Real E : Real) * rho s < (1 / 2 : Real) :=
    (hrho.const_mul (Module.finrank Real E : Real)).eventually_lt_const
      (by norm_num)
  refine ⟨omega, homega, ?_⟩
  filter_upwards [hsmall] with s hs
  intro v hv
  calc
    ‖lapDiffA2 (I := I) (M := M) g_fam T s v‖ <=
        ‖lapDiffA2 (I := I) (M := M) g_fam T s‖ * ‖v‖ :=
      (lapDiffA2 (I := I) (M := M) g_fam T s).le_opNorm v
    _ <= omega s * ‖v‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg v)
      simpa only [lapDiffA2, omega, rho] using
        hop (g_fam ((T : Real) - s)) hs.le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.lapDiffA2_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.lapDiffA2_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.lapDiffA2_bound ``Submission.DifferentialGeometry.Analysis.Spectral.lapDiffA2_bound

theorem lapDiffA2_zero
    {D : RealTimeInterval}
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam)
    (T : D.RegularTime) :
    Tendsto (fun s : Real => ‖lapDiffA2 (I := I) (M := M) g_fam T s‖)
      (𝓝 0) (𝓝 0) := by
  obtain ⟨C, hC, hop⟩ :=
    lapDiffOp_norm (I := I) (M := M) (g_fam (T : Real))
  let rho : Real → Real := fun s =>
    CheegerGromovCompactness.metricDerivNormSupOn (I := I) Set.univ 1
      (g_fam ((T : Real) - s))
      (g_fam (T : Real)) (g_fam (T : Real))
  have hrho : _root_.Filter.Tendsto rho (𝓝 0) (𝓝 0) := by
    simpa only [rho] using lapDiff_rho (I := I) g_fam hG T
  have hupper :
      Tendsto (fun s => Real.sqrt C * |rho s|) (𝓝 0) (𝓝 0) := by
    simpa only [abs_zero, _root_.MulZeroClass.mul_zero] using
      hrho.abs.const_mul (Real.sqrt C)
  have hsmall :
      ∀ᶠ s in 𝓝 (0 : Real),
        (Module.finrank Real E : Real) * rho s < (1 / 2 : Real) :=
    (hrho.const_mul (Module.finrank Real E : Real)).eventually_lt_const
      (by norm_num)
  apply squeeze_zero'
    (Filter.Eventually.of_forall fun s => norm_nonneg
      (lapDiffA2 (I := I) (M := M) g_fam T s))
    _ hupper
  filter_upwards [hsmall] with s hs
  simpa only [lapDiffA2, rho] using
    hop (g_fam ((T : Real) - s)) hs.le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.lapDiffA2_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.lapDiffA2_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.lapDiffA2_zero ``Submission.DifferentialGeometry.Analysis.Spectral.lapDiffA2_zero

end LapDiffOperator

end Spectral
end Analysis
end DifferentialGeometry

end
