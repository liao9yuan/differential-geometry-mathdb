import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.Defs
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Scaling.Parabolic
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Scaling
import Submission.DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry.Tensor0SBundle _root_.MeasureTheory _root_.Set
open scoped _root_.Manifold _root_.ContDiff _root_.ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
variable [IsManifold I 1 M]
variable [T2Space M] [SigmaCompactSpace M]

def parabolicFlowTime
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (tau R : Real) (htau : tau ∈ D.carrier)
    (s : (parabolicInterval D tau R htau).FlowTime) : D.FlowTime :=
  ⟨parabolicTime tau R (s : Real), s.2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.parabolicFlowTime then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.parabolicFlowTime"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.parabolicFlowTime ``Submission.DifferentialGeometry.PDE.RicciFlow.parabolicFlowTime

@[simp] theorem parabolicFlowTime_coe
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (tau R : Real) (htau : tau ∈ D.carrier)
    (s : (parabolicInterval D tau R htau).FlowTime) :
    (parabolicFlowTime tau R htau s : Real) = parabolicTime tau R (s : Real) := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.parabolicFlowTime_coe then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.parabolicFlowTime_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.parabolicFlowTime_coe ``Submission.DifferentialGeometry.PDE.RicciFlow.parabolicFlowTime_coe

namespace Perelman

variable {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}

def parabolicBall
    (S : SolutionOn (I := I) (M := M) D)
    (tau R : Real) (hR : 0 < R) (htau : tau ∈ D.carrier)
    (s : (parabolicInterval D tau R htau).FlowTime)
    (B : FlowMetricBall S (parabolicFlowTime tau R htau s)) :
    FlowMetricBall (parabolicSolution (I := I) S tau R hR htau) s where
  center := B.center
  radius := Real.sqrt R * B.radius
  radius_pos := mul_pos (Real.sqrt_pos.2 hR) B.radius_pos

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.parabolicBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.parabolicBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.parabolicBall ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.parabolicBall

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I 1 M] [T2Space M]
    [SigmaCompactSpace M] in
theorem parabolicBall_setAt
    (S : SolutionOn (I := I) (M := M) D)
    (tau R : Real) (hR : 0 < R) (htau : tau ∈ D.carrier)
    (s : (parabolicInterval D tau R htau).FlowTime)
    (B : FlowMetricBall S (parabolicFlowTime tau R htau s))
    (q : Real) :
    (parabolicBall S tau R hR htau s B).setAt q =
      B.setAt (parabolicTime tau R q) := by
  simpa only [FlowMetricBall.setAt, parabolicBall, parabolicSolution_metric] using
    (_root_.Submission.DifferentialGeometry.edistBall_scale (I := I) R hR
      (S.base.metric (parabolicTime tau R q)) B.center B.radius)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.parabolicBall_setAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.parabolicBall_setAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.parabolicBall_setAt ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.parabolicBall_setAt

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I 1 M] [T2Space M]
    [SigmaCompactSpace M] in
theorem parabolicBall_set
    (S : SolutionOn (I := I) (M := M) D)
    (tau R : Real) (hR : 0 < R) (htau : tau ∈ D.carrier)
    (s : (parabolicInterval D tau R htau).FlowTime)
    (B : FlowMetricBall S (parabolicFlowTime tau R htau s)) :
    (parabolicBall S tau R hR htau s B).set = B.set := by
  unfold FlowMetricBall.set
  simpa only [parabolicFlowTime_coe] using
    parabolicBall_setAt (I := I) S tau R hR htau s B (s : Real)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.parabolicBall_set then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.parabolicBall_set"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.parabolicBall_set ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.parabolicBall_set

omit [CompleteSpace E] in
theorem parabolicBall_volume
    (S : SolutionOn (I := I) (M := M) D)
    (tau R : Real) (hR : 0 < R) (htau : tau ∈ D.carrier)
    (s : (parabolicInterval D tau R htau).FlowTime)
    (B : FlowMetricBall S (parabolicFlowTime tau R htau s)) :
    (parabolicBall S tau R hR htau s B).volume =
      ENNReal.ofReal (Real.sqrt R) ^ Module.finrank Real E * B.volume := by
  change
    DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure
        (I := I) (M := M)
        (scaleMetric (I := I) R hR
          (S.base.metric (parabolicTime tau R (s : Real))))
        (parabolicBall S tau R hR htau s B).set =
      ENNReal.ofReal (Real.sqrt R) ^ Module.finrank Real E *
        DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure
          (I := I) (M := M)
          (S.base.metric (parabolicTime tau R (s : Real))) B.set
  rw [parabolicBall_set (I := I) S tau R hR htau s B]
  exact DifferentialGeometry.Integral.Measure.volume_scale_apply
    (I := I) (M := M) R hR
      (S.base.metric (parabolicTime tau R (s : Real))) B.set

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.parabolicBall_volume then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.parabolicBall_volume"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.parabolicBall_volume ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.parabolicBall_volume

omit [CompleteSpace E] in
theorem parabolicBall_kappa
    (S : SolutionOn (I := I) (M := M) D)
    (tau R : Real) (hR : 0 < R) (htau : tau ∈ D.carrier)
    (s : (parabolicInterval D tau R htau).FlowTime)
    (B : FlowMetricBall S (parabolicFlowTime tau R htau s))
    (kappa : Real) (hB : B.IsKappaNoncollapsed kappa) :
    (parabolicBall S tau R hR htau s B).IsKappaNoncollapsed kappa := by
  refine ⟨hB.1, ?_⟩
  change
    ENNReal.ofReal kappa *
        ENNReal.ofReal (Real.sqrt R * B.radius) ^ Module.finrank Real E ≤
      (parabolicBall S tau R hR htau s B).volume
  rw [ENNReal.ofReal_mul (Real.sqrt_nonneg R), mul_pow]
  rw [parabolicBall_volume (I := I) S tau R hR htau s B]
  calc
    ENNReal.ofReal kappa *
          (ENNReal.ofReal (Real.sqrt R) ^ Module.finrank Real E *
            ENNReal.ofReal B.radius ^ Module.finrank Real E) =
        ENNReal.ofReal (Real.sqrt R) ^ Module.finrank Real E *
          (ENNReal.ofReal kappa *
            ENNReal.ofReal B.radius ^ Module.finrank Real E) := by
      ac_rfl
    _ ≤ ENNReal.ofReal (Real.sqrt R) ^ Module.finrank Real E * B.volume :=
      mul_le_mul_right hB.2 _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.parabolicBall_kappa then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.parabolicBall_kappa"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.parabolicBall_kappa ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.parabolicBall_kappa

private theorem parabolicWindow
    (tau R : Real) (hR : 0 < R) (s q r : Real)
    (hq : q ∈ Set.Icc (s - (Real.sqrt R * r) ^ 2) s) :
    parabolicTime tau R q ∈
      Set.Icc (parabolicTime tau R s - r ^ 2) (parabolicTime tau R s) := by
  have hrad : (Real.sqrt R * r) ^ 2 = R * r ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hR.le]
  have hlo : s - R * r ^ 2 ≤ q := by
    simpa only [hrad] using hq.1
  have hlo_div : (s - R * r ^ 2) / R ≤ q / R :=
    (div_le_div_iff_of_pos_right hR).2 hlo
  have hsplit : (s - R * r ^ 2) / R = s / R - r ^ 2 := by
    field_simp [ne_of_gt hR]
  rw [hsplit] at hlo_div
  have hhi_div : q / R ≤ s / R :=
    (div_le_div_iff_of_pos_right hR).2 hq.2
  unfold parabolicTime
  constructor <;> linarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.parabolicWindow
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.parabolicWindow target :: scope.openDecls } }

omit [SigmaCompactSpace M] in
theorem parabolicBall_rm
    (S : SolutionOn (I := I) (M := M) D)
    (tau R : Real) (hR : 0 < R) (htau : tau ∈ D.carrier)
    (s : (parabolicInterval D tau R htau).FlowTime)
    (B : FlowMetricBall S (parabolicFlowTime tau R htau s))
    (hB : B.IsRmControlled) :
    (parabolicBall S tau R hR htau s B).IsRmControlled := by
  rcases hB with ⟨hwindow, hcurv⟩
  constructor
  · intro q hq
    have hq_old := parabolicWindow tau R hR (s : Real) q B.radius hq
    exact hwindow hq_old
  · intro q hq x hx
    have hq_old := parabolicWindow tau R hR (s : Real) q B.radius hq
    have hx_old : x ∈ B.setAt (parabolicTime tau R q) := by
      rw [← parabolicBall_setAt (I := I) S tau R hR htau s B q]
      exact hx
    have hold := hcurv (parabolicTime tau R q) hq_old x hx_old
    unfold FlowMetricBall.rmNormSq
    rw [parabolicRmNormSq]
    have hscale :
        (Real.sqrt R * B.radius) ^ 4 * R⁻¹ ^ 2 = B.radius ^ 4 := by
      rw [mul_pow]
      calc
        Real.sqrt R ^ 4 * B.radius ^ 4 * R⁻¹ ^ 2 =
            (Real.sqrt R ^ 2) ^ 2 * B.radius ^ 4 * R⁻¹ ^ 2 := by ring
        _ = R ^ 2 * B.radius ^ 4 * R⁻¹ ^ 2 := by
          rw [Real.sq_sqrt hR.le]
        _ = B.radius ^ 4 := by field_simp [ne_of_gt hR]
    calc
      (Real.sqrt R * B.radius) ^ 4 *
          (R⁻¹ ^ 2 *
            Tensor0SBundle.normSq0S (I := I)
              (S.base.metric (parabolicTime tau R q)) x 4
              (S.base.rm04 (parabolicTime tau R q) x)) =
          ((Real.sqrt R * B.radius) ^ 4 * R⁻¹ ^ 2) *
            Tensor0SBundle.normSq0S (I := I)
              (S.base.metric (parabolicTime tau R q)) x 4
              (S.base.rm04 (parabolicTime tau R q) x) := by ring
      _ = B.radius ^ 4 *
            Tensor0SBundle.normSq0S (I := I)
              (S.base.metric (parabolicTime tau R q)) x 4
              (S.base.rm04 (parabolicTime tau R q) x) := by rw [hscale]
      _ ≤ 1 := hold

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.parabolicBall_rm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.parabolicBall_rm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.parabolicBall_rm ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.parabolicBall_rm

def backBall
    (S : SolutionOn (I := I) (M := M) D)
    (tau R : Real) (hR : 0 < R) (htau : tau ∈ D.carrier)
    (s : (parabolicInterval D tau R htau).FlowTime)
    (B : FlowMetricBall (parabolicSolution (I := I) S tau R hR htau) s) :
    FlowMetricBall S (parabolicFlowTime tau R htau s) where
  center := B.center
  radius := B.radius / Real.sqrt R
  radius_pos := div_pos B.radius_pos (Real.sqrt_pos.2 hR)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.backBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.backBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.backBall ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.backBall

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I 1 M] [T2Space M]
    [SigmaCompactSpace M] in
theorem parabolicBall_back
    (S : SolutionOn (I := I) (M := M) D)
    (tau R : Real) (hR : 0 < R) (htau : tau ∈ D.carrier)
    (s : (parabolicInterval D tau R htau).FlowTime)
    (B : FlowMetricBall (parabolicSolution (I := I) S tau R hR htau) s) :
    parabolicBall S tau R hR htau s (backBall S tau R hR htau s B) = B := by
  cases B with
  | mk center radius radius_pos =>
      simp only [parabolicBall, backBall]
      congr
      field_simp [ne_of_gt (Real.sqrt_pos.2 hR)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.parabolicBall_back then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.parabolicBall_back"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.parabolicBall_back ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.parabolicBall_back

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I 1 M] [T2Space M]
    [SigmaCompactSpace M] in
theorem backBall_setAt
    (S : SolutionOn (I := I) (M := M) D)
    (tau R : Real) (hR : 0 < R) (htau : tau ∈ D.carrier)
    (s : (parabolicInterval D tau R htau).FlowTime)
    (B : FlowMetricBall (parabolicSolution (I := I) S tau R hR htau) s)
    (q : Real) :
    (backBall S tau R hR htau s B).setAt (parabolicTime tau R q) =
      B.setAt q := by
  have h := parabolicBall_setAt (I := I) S tau R hR htau s
    (backBall S tau R hR htau s B) q
  rw [parabolicBall_back (I := I) S tau R hR htau s B] at h
  exact h.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.backBall_setAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.backBall_setAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.backBall_setAt ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.backBall_setAt

omit [CompleteSpace E] in
theorem backBall_volume
    (S : SolutionOn (I := I) (M := M) D)
    (tau R : Real) (hR : 0 < R) (htau : tau ∈ D.carrier)
    (s : (parabolicInterval D tau R htau).FlowTime)
    (B : FlowMetricBall (parabolicSolution (I := I) S tau R hR htau) s) :
    B.volume = ENNReal.ofReal (Real.sqrt R) ^ Module.finrank Real E *
      (backBall S tau R hR htau s B).volume := by
  have h := parabolicBall_volume (I := I) S tau R hR htau s
    (backBall S tau R hR htau s B)
  rw [parabolicBall_back (I := I) S tau R hR htau s B] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.backBall_volume then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.backBall_volume"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.backBall_volume ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.backBall_volume

omit [CompleteSpace E] in
theorem backBall_kappa
    (S : SolutionOn (I := I) (M := M) D)
    (tau R : Real) (hR : 0 < R) (htau : tau ∈ D.carrier)
    (s : (parabolicInterval D tau R htau).FlowTime)
    (B : FlowMetricBall (parabolicSolution (I := I) S tau R hR htau) s)
    (kappa : Real) (hB : B.IsKappaNoncollapsed kappa) :
    (backBall S tau R hR htau s B).IsKappaNoncollapsed kappa := by
  refine ⟨hB.1, ?_⟩
  let a : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt R)
  let n : Nat := Module.finrank Real E
  have ha0 : a ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.2 hR))
  have hatop : a ≠ (∞ : ℝ≥0∞) := ENNReal.ofReal_ne_top
  have hfac0 : a ^ n ≠ 0 := pow_ne_zero n ha0
  have hfactop : a ^ n ≠ (∞ : ℝ≥0∞) := ENNReal.pow_ne_top hatop
  have hradius :
      B.radius = Real.sqrt R * (backBall S tau R hR htau s B).radius := by
    dsimp [backBall]
    field_simp [ne_of_gt (Real.sqrt_pos.2 hR)]
  have hscaled := hB.2
  rw [hradius, ENNReal.ofReal_mul (Real.sqrt_nonneg R), mul_pow,
    backBall_volume (I := I) S tau R hR htau s B] at hscaled
  have hscaled' :
      a ^ n *
          (ENNReal.ofReal kappa *
            ENNReal.ofReal (backBall S tau R hR htau s B).radius ^ n) ≤
        a ^ n * (backBall S tau R hR htau s B).volume := by
    simpa only [a, n, mul_assoc, mul_left_comm, mul_comm] using hscaled
  exact (ENNReal.mul_le_mul_iff_right hfac0 hfactop).mp hscaled'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.backBall_kappa then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.backBall_kappa"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.backBall_kappa ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.backBall_kappa

private theorem backWindow
    (tau R : Real) (hR : 0 < R) (s q r : Real)
    (hq : q ∈ Set.Icc
      (parabolicTime tau R s - (r / Real.sqrt R) ^ 2) (parabolicTime tau R s)) :
    parabolicBackward tau R q ∈ Set.Icc (s - r ^ 2) s := by
  have hrad : (r / Real.sqrt R) ^ 2 = r ^ 2 / R := by
    rw [div_pow, Real.sq_sqrt hR.le]
  have hlo0 := hq.1
  rw [hrad] at hlo0
  unfold parabolicTime at hlo0
  have hlo_div : (s - r ^ 2) / R ≤ q - tau := by
    rw [sub_div]
    linarith
  have hlo := (div_le_iff₀ hR).1 hlo_div
  have hhi0 := hq.2
  unfold parabolicTime at hhi0
  have hhi_div : q - tau ≤ s / R := by linarith
  have hhi := (le_div_iff₀ hR).1 hhi_div
  constructor
  · simpa [parabolicBackward, mul_comm] using hlo
  · simpa [parabolicBackward, mul_comm] using hhi

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.backWindow
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.backWindow target :: scope.openDecls } }

omit [SigmaCompactSpace M] in
theorem backBall_rm
    (S : SolutionOn (I := I) (M := M) D)
    (tau R : Real) (hR : 0 < R) (htau : tau ∈ D.carrier)
    (s : (parabolicInterval D tau R htau).FlowTime)
    (B : FlowMetricBall (parabolicSolution (I := I) S tau R hR htau) s)
    (hB : B.IsRmControlled) :
    (backBall S tau R hR htau s B).IsRmControlled := by
  rcases hB with ⟨hwindow, hcurv⟩
  constructor
  · intro q hq
    let q' : Real := parabolicBackward tau R q
    have hq_new : q' ∈ Set.Icc (s - B.radius ^ 2) (s : Real) :=
      backWindow tau R hR (s : Real) q B.radius hq
    have hmem := hwindow hq_new
    change parabolicTime tau R q' ∈ D.carrier at hmem
    simpa only [q', parabolicTime_back (ne_of_gt hR)] using hmem
  · intro q hq x hx
    let q' : Real := parabolicBackward tau R q
    have hq_new : q' ∈ Set.Icc (s - B.radius ^ 2) (s : Real) :=
      backWindow tau R hR (s : Real) q B.radius hq
    have hset := backBall_setAt (I := I) S tau R hR htau s B q'
    rw [parabolicTime_back (ne_of_gt hR)] at hset
    have hx_new : x ∈ B.setAt q' := by
      rw [← hset]
      exact hx
    have hold := hcurv q' hq_new x hx_new
    unfold FlowMetricBall.rmNormSq at hold ⊢
    rw [parabolicRmNormSq, parabolicTime_back (ne_of_gt hR)] at hold
    change (B.radius / Real.sqrt R) ^ 4 *
      Tensor0SBundle.normSq0S (I := I) (S.base.metric q) x 4
        (S.base.rm04 q x) ≤ 1
    have hscale :
        (B.radius / Real.sqrt R) ^ 4 = B.radius ^ 4 * R⁻¹ ^ 2 := by
      rw [div_pow]
      have hsqrt : Real.sqrt R ^ 4 = R ^ 2 := by
        calc
          Real.sqrt R ^ 4 = (Real.sqrt R ^ 2) ^ 2 := by ring
          _ = R ^ 2 := by rw [Real.sq_sqrt hR.le]
      rw [hsqrt, div_eq_mul_inv, inv_pow]
    rw [hscale]
    simpa only [mul_assoc] using hold

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.backBall_rm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.backBall_rm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.backBall_rm ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.backBall_rm

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I 1 M] [T2Space M]
    [SigmaCompactSpace M] in
theorem backBall_parabolic
    (S : SolutionOn (I := I) (M := M) D)
    (tau R : Real) (hR : 0 < R) (htau : tau ∈ D.carrier)
    (s : (parabolicInterval D tau R htau).FlowTime)
    (B : FlowMetricBall S (parabolicFlowTime tau R htau s)) :
    backBall S tau R hR htau s (parabolicBall S tau R hR htau s B) = B := by
  cases B with
  | mk center radius radius_pos =>
      simp only [parabolicBall, backBall]
      congr
      field_simp [ne_of_gt (Real.sqrt_pos.2 hR)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.backBall_parabolic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.backBall_parabolic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.backBall_parabolic ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.backBall_parabolic

omit [SigmaCompactSpace M] in
theorem parabolicBall_rm_iff
    (S : SolutionOn (I := I) (M := M) D)
    (tau R : Real) (hR : 0 < R) (htau : tau ∈ D.carrier)
    (s : (parabolicInterval D tau R htau).FlowTime)
    (B : FlowMetricBall S (parabolicFlowTime tau R htau s)) :
    (parabolicBall S tau R hR htau s B).IsRmControlled ↔ B.IsRmControlled := by
  constructor
  · intro h
    have hback := backBall_rm (I := I) S tau R hR htau s
      (parabolicBall S tau R hR htau s B) h
    rw [backBall_parabolic (I := I) S tau R hR htau s B] at hback
    exact hback
  · exact parabolicBall_rm (I := I) S tau R hR htau s B

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.parabolicBall_rm_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.parabolicBall_rm_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.parabolicBall_rm_iff ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.parabolicBall_rm_iff

omit [CompleteSpace E] in
theorem parabolicBall_kappa_iff
    (S : SolutionOn (I := I) (M := M) D)
    (tau R : Real) (hR : 0 < R) (htau : tau ∈ D.carrier)
    (s : (parabolicInterval D tau R htau).FlowTime)
    (B : FlowMetricBall S (parabolicFlowTime tau R htau s))
    (kappa : Real) :
    (parabolicBall S tau R hR htau s B).IsKappaNoncollapsed kappa ↔
      B.IsKappaNoncollapsed kappa := by
  constructor
  · intro h
    have hback := backBall_kappa (I := I) S tau R hR htau s
      (parabolicBall S tau R hR htau s B) kappa h
    rw [backBall_parabolic (I := I) S tau R hR htau s B] at hback
    exact hback
  · exact parabolicBall_kappa (I := I) S tau R hR htau s B kappa

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.parabolicBall_kappa_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.parabolicBall_kappa_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.parabolicBall_kappa_iff ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.parabolicBall_kappa_iff

theorem parabolic_noncollapse
    (S : SolutionOn (I := I) (M := M) D)
    (tau R : Real) (hR : 0 < R) (htau : tau ∈ D.carrier)
    (kappa rho : Real)
    (hS : KappaNoncollapsedBelowScale S kappa rho) :
    KappaNoncollapsedBelowScale
      (parabolicSolution (I := I) S tau R hR htau) kappa
      (Real.sqrt R * rho) := by
  refine ⟨mul_pos (Real.sqrt_pos.2 hR) hS.1, ?_⟩
  intro s B hscale hRm
  let B₀ := backBall S tau R hR htau s B
  have hradius : B₀.radius ≤ rho := by
    dsimp [B₀, backBall]
    apply (div_le_iff₀ (Real.sqrt_pos.2 hR)).2
    simpa only [mul_comm] using hscale
  have hRm₀ : B₀.IsRmControlled :=
    backBall_rm (I := I) S tau R hR htau s B hRm
  have hk₀ := hS.2 (parabolicFlowTime tau R htau s) B₀ hradius hRm₀
  have hk := parabolicBall_kappa (I := I) S tau R hR htau s B₀ kappa hk₀
  rw [parabolicBall_back (I := I) S tau R hR htau s B] at hk
  exact hk

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.parabolic_noncollapse then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.parabolic_noncollapse"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.parabolic_noncollapse ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.parabolic_noncollapse

theorem parabolic_no_local
    (S : SolutionOn (I := I) (M := M) D)
    (tau R : Real) (hR : 0 < R) (htau : tau ∈ D.carrier)
    (rho : Real) (hS : NoLocalCollapsing S rho) :
    NoLocalCollapsing (parabolicSolution (I := I) S tau R hR htau)
      (Real.sqrt R * rho) := by
  rcases hS with ⟨kappa, hkappa, hbelow⟩
  exact ⟨kappa, hkappa,
    parabolic_noncollapse (I := I) S tau R hR htau kappa rho hbelow⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.parabolic_no_local then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.parabolic_no_local"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.parabolic_no_local ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.parabolic_no_local

end Perelman

end DifferentialGeometry.PDE.RicciFlow

end
