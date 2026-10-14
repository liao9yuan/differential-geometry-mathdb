import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.AllScales
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.Parabolic
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Basic
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Family.Metric
import Submission.DifferentialGeometry.Geometry.Metric.Distance.Ball

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Submission.DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

private theorem sub_mem_Icc {a r x τ : Real} (h : x ∈ Set.Icc (a - r ^ 2) a) :
    x - τ ∈ Set.Icc ((a - τ) - r ^ 2) (a - τ) := by
  constructor <;> linarith [h.1, h.2]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.sub_mem_Icc
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.sub_mem_Icc target :: scope.openDecls } }

private theorem add_mem_Icc {a r x τ : Real}
    (h : x ∈ Set.Icc ((a - τ) - r ^ 2) (a - τ)) :
    x + τ ∈ Set.Icc (a - r ^ 2) a := by
  constructor <;> linarith [h.1, h.2]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.add_mem_Icc
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.add_mem_Icc target :: scope.openDecls } }

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.MeasureTheory _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Integral.Measure
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M]
variable [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

namespace FlowMetricBall

omit [FiniteDimensional Real E] [IsManifold I 1 M] [T2Space M] [SigmaCompactSpace M] in
theorem setAt_timeShift (S : SolutionOn (I := I) (M := M) D) (τ : Real)
    {t : D.FlowTime} {t' : (D.timeShift τ).FlowTime}
    (B : FlowMetricBall S t) (B' : FlowMetricBall (S.timeShift τ) t')
    (hcenter : B'.center = B.center) (hradius : B'.radius = B.radius) (s : Real) :
    B'.setAt s = B.setAt (s + τ) := by
  simp only [setAt, hcenter, hradius, SolutionOn.timeShift_base_metric]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.setAt_timeShift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.setAt_timeShift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.setAt_timeShift ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.setAt_timeShift

omit [FiniteDimensional Real E] [IsManifold I 1 M] [T2Space M] [SigmaCompactSpace M] in
theorem set_timeShift (S : SolutionOn (I := I) (M := M) D) (τ : Real)
    {t : D.FlowTime} {t' : (D.timeShift τ).FlowTime} (ht : (t' : Real) + τ = (t : Real))
    (B : FlowMetricBall S t) (B' : FlowMetricBall (S.timeShift τ) t')
    (hcenter : B'.center = B.center) (hradius : B'.radius = B.radius) :
    B'.set = B.set := by
  change B'.setAt (t' : Real) = B.setAt (t : Real)
  rw [setAt_timeShift (S := S) τ B B' hcenter hradius, ht]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.set_timeShift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.set_timeShift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.set_timeShift ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.set_timeShift

omit [SigmaCompactSpace M] in
theorem rmNormSq_timeShift (S : SolutionOn (I := I) (M := M) D) (τ s : Real) (x : M) :
    rmNormSq (S.timeShift τ) s x = rmNormSq S (s + τ) x :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.rmNormSq_timeShift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.rmNormSq_timeShift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.rmNormSq_timeShift ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.rmNormSq_timeShift

omit [SigmaCompactSpace M] in
theorem isRmControlled_timeShift_iff (S : SolutionOn (I := I) (M := M) D) (τ : Real)
    {t : D.FlowTime} {t' : (D.timeShift τ).FlowTime} (ht : (t' : Real) + τ = (t : Real))
    (B : FlowMetricBall S t) (B' : FlowMetricBall (S.timeShift τ) t')
    (hcenter : B'.center = B.center) (hradius : B'.radius = B.radius) :
    B'.IsRmControlled ↔ B.IsRmControlled := by
  have ht' : (t' : Real) = (t : Real) - τ := by linarith [ht]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro s hs
      have hs' : s - τ ∈ Set.Icc ((t' : Real) - B'.radius ^ 2) (t' : Real) := by
        rw [ht', hradius]
        exact sub_mem_Icc hs
      have hcar := h.1 hs'
      rw [RealTimeInterval.timeShift_carrier, Set.mem_ofPred_eq] at hcar
      simpa only [sub_add_cancel] using hcar
    · intro s hs x hx
      have hs' : s - τ ∈ Set.Icc ((t' : Real) - B'.radius ^ 2) (t' : Real) := by
        rw [ht', hradius]
        exact sub_mem_Icc hs
      have hx' : x ∈ B'.setAt (s - τ) := by
        rw [setAt_timeShift (S := S) τ B B' hcenter hradius, sub_add_cancel]
        exact hx
      have hk := h.2 (s - τ) hs' x hx'
      simpa only [hradius, rmNormSq_timeShift, sub_add_cancel] using hk
  · intro h
    refine ⟨?_, ?_⟩
    · intro s hs
      rw [RealTimeInterval.timeShift_carrier, Set.mem_ofPred_eq]
      have hs' : s + τ ∈ Set.Icc ((t : Real) - B.radius ^ 2) (t : Real) := by
        rw [ht', hradius] at hs
        exact add_mem_Icc hs
      exact h.1 hs'
    · intro s hs x hx
      have hs' : s + τ ∈ Set.Icc ((t : Real) - B.radius ^ 2) (t : Real) := by
        rw [ht', hradius] at hs
        exact add_mem_Icc hs
      have hx' : x ∈ B.setAt (s + τ) := by
        rw [← setAt_timeShift (S := S) τ B B' hcenter hradius s]
        exact hx
      have hk := h.2 (s + τ) hs' x hx'
      simpa only [hradius, rmNormSq_timeShift] using hk

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.isRmControlled_timeShift_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.isRmControlled_timeShift_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.isRmControlled_timeShift_iff ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.isRmControlled_timeShift_iff

omit [SigmaCompactSpace M] in
theorem isSpatiallyRmControlled_timeShift_iff (S : SolutionOn (I := I) (M := M) D)
    (τ : Real) {t : D.FlowTime} {t' : (D.timeShift τ).FlowTime}
    (ht : (t' : Real) + τ = (t : Real))
    (B : FlowMetricBall S t) (B' : FlowMetricBall (S.timeShift τ) t')
    (hcenter : B'.center = B.center) (hradius : B'.radius = B.radius) :
    B'.IsSpatiallyRmControlled ↔ B.IsSpatiallyRmControlled := by
  have hset : B'.set = B.set := set_timeShift (S := S) τ ht B B' hcenter hradius
  constructor
  · intro h x hx
    have hx' : x ∈ B'.set := by rwa [hset]
    have hk := h x hx'
    simpa only [hradius, rmNormSq_timeShift, ht] using hk
  · intro h x hx
    have hx' : x ∈ B.set := by rwa [← hset]
    have hk := h x hx'
    simpa only [hradius, rmNormSq_timeShift, ht] using hk

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.isSpatiallyRmControlled_timeShift_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.isSpatiallyRmControlled_timeShift_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.isSpatiallyRmControlled_timeShift_iff ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.isSpatiallyRmControlled_timeShift_iff

omit [SigmaCompactSpace M] in
theorem isParabolicallyRmControlled_timeShift_iff (S : SolutionOn (I := I) (M := M) D)
    (τ : Real) {t : D.FlowTime} {t' : (D.timeShift τ).FlowTime}
    (ht : (t' : Real) + τ = (t : Real))
    (B : FlowMetricBall S t) (B' : FlowMetricBall (S.timeShift τ) t')
    (hcenter : B'.center = B.center) (hradius : B'.radius = B.radius) :
    B'.IsParabolicallyRmControlled ↔ B.IsParabolicallyRmControlled := by
  have ht' : (t' : Real) = (t : Real) - τ := by linarith [ht]
  have hset : B'.set = B.set := set_timeShift (S := S) τ ht B B' hcenter hradius
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro s hs
      have hs' : s - τ ∈ Set.Icc ((t' : Real) - B'.radius ^ 2) (t' : Real) := by
        rw [ht', hradius]
        exact sub_mem_Icc hs
      have hcar := h.1 hs'
      rw [RealTimeInterval.timeShift_carrier, Set.mem_ofPred_eq] at hcar
      simpa only [sub_add_cancel] using hcar
    · intro s hs x hx
      have hs' : s - τ ∈ Set.Icc ((t' : Real) - B'.radius ^ 2) (t' : Real) := by
        rw [ht', hradius]
        exact sub_mem_Icc hs
      have hx' : x ∈ B'.set := by rwa [hset]
      have hk := h.2 (s - τ) hs' x hx'
      simpa only [hradius, rmNormSq_timeShift, sub_add_cancel] using hk
  · intro h
    refine ⟨?_, ?_⟩
    · intro s hs
      rw [RealTimeInterval.timeShift_carrier, Set.mem_ofPred_eq]
      have hs' : s + τ ∈ Set.Icc ((t : Real) - B.radius ^ 2) (t : Real) := by
        rw [ht', hradius] at hs
        exact add_mem_Icc hs
      exact h.1 hs'
    · intro s hs x hx
      have hs' : s + τ ∈ Set.Icc ((t : Real) - B.radius ^ 2) (t : Real) := by
        rw [ht', hradius] at hs
        exact add_mem_Icc hs
      have hx' : x ∈ B.set := by rwa [← hset]
      have hk := h.2 (s + τ) hs' x hx'
      simpa only [hradius, rmNormSq_timeShift] using hk

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.isParabolicallyRmControlled_timeShift_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.isParabolicallyRmControlled_timeShift_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.isParabolicallyRmControlled_timeShift_iff ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.isParabolicallyRmControlled_timeShift_iff

omit [T2Space M] [SigmaCompactSpace M] in
theorem isScalarControlled_timeShift_iff (S : SolutionOn (I := I) (M := M) D)
    (τ : Real) {t : D.FlowTime} {t' : (D.timeShift τ).FlowTime}
    (ht : (t' : Real) + τ = (t : Real))
    (B : FlowMetricBall S t) (B' : FlowMetricBall (S.timeShift τ) t')
    (hcenter : B'.center = B.center) (hradius : B'.radius = B.radius) :
    B'.IsScalarControlled ↔ B.IsScalarControlled := by
  have hset : B'.set = B.set := set_timeShift (S := S) τ ht B B' hcenter hradius
  constructor
  · intro h x hx
    have hx' : x ∈ B'.set := by rwa [hset]
    have hk := h x hx'
    simpa only [hradius, SolutionOn.timeShift_scalar, ht] using hk
  · intro h x hx
    have hx' : x ∈ B.set := by rwa [← hset]
    have hk := h x hx'
    simpa only [hradius, SolutionOn.timeShift_scalar, ht] using hk

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.isScalarControlled_timeShift_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.isScalarControlled_timeShift_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.isScalarControlled_timeShift_iff ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.isScalarControlled_timeShift_iff

theorem isKappaNoncollapsed_timeShift_iff (S : SolutionOn (I := I) (M := M) D)
    (τ : Real) {t : D.FlowTime} {t' : (D.timeShift τ).FlowTime}
    (ht : (t' : Real) + τ = (t : Real))
    (B : FlowMetricBall S t) (B' : FlowMetricBall (S.timeShift τ) t')
    (hcenter : B'.center = B.center) (hradius : B'.radius = B.radius) (kappa : Real) :
    B'.IsKappaNoncollapsed kappa ↔ B.IsKappaNoncollapsed kappa := by
  have hvol : B'.volume = B.volume := by
    unfold volume
    have hm : (S.timeShift τ).family.metric (t' : Real) = S.family.metric (t : Real) := by
      rw [SolutionOn.timeShift_family_metric, ht]
    have hs : B'.set = B.set := set_timeShift (S := S) τ ht B B' hcenter hradius
    rw [volumeMeasureOn_eq_metric, volumeMeasureOn_eq_metric, hm, hs]
  simp only [IsKappaNoncollapsed, hradius, hvol]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.isKappaNoncollapsed_timeShift_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.isKappaNoncollapsed_timeShift_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.isKappaNoncollapsed_timeShift_iff ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.isKappaNoncollapsed_timeShift_iff

omit [FiniteDimensional Real E] [IsManifold I 1 M] [T2Space M] [SigmaCompactSpace M] in
theorem setAt_metric_eq (S S' : SolutionOn (I := I) (M := M) D) {t : D.FlowTime}
    (B : FlowMetricBall S t) (B' : FlowMetricBall S' t)
    (hcenter : B'.center = B.center) (hradius : B'.radius = B.radius)
    (s : Real) (hmetric : S'.base.metric s = S.base.metric s) :
    B'.setAt s = B.setAt s := by
  simp only [setAt, hcenter, hradius, hmetric]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.setAt_metric_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.setAt_metric_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.setAt_metric_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.setAt_metric_eq

omit [SigmaCompactSpace M] in
theorem isRmControlled_of_metric_eqOn (S S' : SolutionOn (I := I) (M := M) D)
    {t : D.FlowTime} (B : FlowMetricBall S t) (B' : FlowMetricBall S' t)
    (hcenter : B'.center = B.center) (hradius : B'.radius = B.radius)
    (hmetric : ∀ s ∈ Set.Icc ((t : Real) - B.radius ^ 2) (t : Real),
      S'.base.metric s = S.base.metric s)
    (hB : B.IsRmControlled) : B'.IsRmControlled := by
  refine ⟨?_, ?_⟩
  · intro s hs
    exact hB.1 (by simpa only [hradius] using hs)
  · intro s hs x hx
    have hx' : x ∈ B.setAt s := by
      rw [← setAt_metric_eq (S := S) (S' := S') B B' hcenter hradius s
        (hmetric s (by simpa only [hradius] using hs))]
      exact hx
    have hk := hB.2 s (by simpa only [hradius] using hs) x hx'
    simpa only [hradius, rmNormSq, SolutionFamily.rm04,
      hmetric s (by simpa only [hradius] using hs)] using hk

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.isRmControlled_of_metric_eqOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.isRmControlled_of_metric_eqOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.isRmControlled_of_metric_eqOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.isRmControlled_of_metric_eqOn

omit [SigmaCompactSpace M] in
theorem isSpatiallyRmControlled_of_metric_eq (S S' : SolutionOn (I := I) (M := M) D)
    {t : D.FlowTime} (B : FlowMetricBall S t) (B' : FlowMetricBall S' t)
    (hcenter : B'.center = B.center) (hradius : B'.radius = B.radius)
    (hmetric : S'.base.metric (t : Real) = S.base.metric (t : Real))
    (hB : B.IsSpatiallyRmControlled) : B'.IsSpatiallyRmControlled := by
  intro x hx
  have hx' : x ∈ B.set := by
    change x ∈ B.setAt (t : Real)
    rw [← setAt_metric_eq (S := S) (S' := S') B B' hcenter hradius (t : Real) hmetric]
    exact hx
  have hk := hB x hx'
  simpa only [hradius, rmNormSq, SolutionFamily.rm04, hmetric] using hk

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.isSpatiallyRmControlled_of_metric_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.isSpatiallyRmControlled_of_metric_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.isSpatiallyRmControlled_of_metric_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.isSpatiallyRmControlled_of_metric_eq

theorem isKappaNoncollapsed_of_metric_eq (S S' : SolutionOn (I := I) (M := M) D)
    {t : D.FlowTime} (B : FlowMetricBall S t) (B' : FlowMetricBall S' t)
    (hcenter : B'.center = B.center) (hradius : B'.radius = B.radius)
    (hmetric : S'.base.metric (t : Real) = S.base.metric (t : Real))
    (kappa : Real) (hB : B.IsKappaNoncollapsed kappa) : B'.IsKappaNoncollapsed kappa := by
  have hvol : B'.volume = B.volume := by
    unfold volume
    have hs : B'.set = B.set := by
      change B'.setAt (t : Real) = B.setAt (t : Real)
      rw [setAt_metric_eq (S := S) (S' := S') B B' hcenter hradius (t : Real) hmetric]
    rw [volumeMeasureOn_eq_metric, volumeMeasureOn_eq_metric, SolutionOn.family_metric,
      SolutionOn.family_metric, hmetric, hs]
  simp only [IsKappaNoncollapsed, hradius, hvol]
  exact hB

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.isKappaNoncollapsed_of_metric_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.isKappaNoncollapsed_of_metric_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.isKappaNoncollapsed_of_metric_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.isKappaNoncollapsed_of_metric_eq

omit [FiniteDimensional Real E] [IsManifold I 1 M] [T2Space M] [SigmaCompactSpace M] in
theorem set_eq_riemannianBallOf (S : SolutionOn (I := I) (M := M) D) {time : D.FlowTime}
    (B : FlowMetricBall S time) :
    B.set = riemannianBallOf (I := I) (S.base.metric (time : Real)) B.center B.radius :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.set_eq_riemannianBallOf then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.set_eq_riemannianBallOf"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.set_eq_riemannianBallOf ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.set_eq_riemannianBallOf

theorem volume_eq_riemannianVolumeMeasure (S : SolutionOn (I := I) (M := M) D)
    {time : D.FlowTime} (B : FlowMetricBall S time) :
    B.volume = riemannianVolumeMeasure (I := I) (M := M) (S.base.metric (time : Real))
      B.set := by
  unfold volume
  rw [volumeMeasureOn_eq_metric, SolutionOn.family_metric]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.volume_eq_riemannianVolumeMeasure then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.volume_eq_riemannianVolumeMeasure"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.volume_eq_riemannianVolumeMeasure ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.volume_eq_riemannianVolumeMeasure

theorem isKappaNoncollapsed_iff_volumeMeasure (S : SolutionOn (I := I) (M := M) D)
    {time : D.FlowTime} (B : FlowMetricBall S time) (kappa : Real) :
    B.IsKappaNoncollapsed kappa ↔
      0 < kappa ∧ ENNReal.ofReal (kappa * B.radius ^ Module.finrank Real E) ≤
        riemannianVolumeMeasure (I := I) (M := M) (S.base.metric (time : Real)) B.set := by
  have hvol := volume_eq_riemannianVolumeMeasure (S := S) B
  constructor
  · rintro ⟨hkappa, hle⟩
    refine ⟨hkappa, ?_⟩
    rw [← hvol, ENNReal.ofReal_mul hkappa.le, ENNReal.ofReal_pow B.radius_pos.le]
    exact hle
  · rintro ⟨hkappa, hle⟩
    refine ⟨hkappa, ?_⟩
    rw [hvol, ← ENNReal.ofReal_pow B.radius_pos.le, ← ENNReal.ofReal_mul hkappa.le]
    exact hle

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.isKappaNoncollapsed_iff_volumeMeasure then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.isKappaNoncollapsed_iff_volumeMeasure"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.isKappaNoncollapsed_iff_volumeMeasure ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.isKappaNoncollapsed_iff_volumeMeasure

theorem isKappaNoncollapsed_iff_riemannianBallOf (S : SolutionOn (I := I) (M := M) D)
    {time : D.FlowTime} (B : FlowMetricBall S time) (kappa : Real) :
    B.IsKappaNoncollapsed kappa ↔
      0 < kappa ∧ ENNReal.ofReal (kappa * B.radius ^ Module.finrank Real E) ≤
        riemannianVolumeMeasure (I := I) (M := M) (S.base.metric (time : Real))
          (riemannianBallOf (I := I) (S.base.metric (time : Real)) B.center B.radius) := by
  rw [isKappaNoncollapsed_iff_volumeMeasure, set_eq_riemannianBallOf]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.isKappaNoncollapsed_iff_riemannianBallOf then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.isKappaNoncollapsed_iff_riemannianBallOf"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.isKappaNoncollapsed_iff_riemannianBallOf ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.isKappaNoncollapsed_iff_riemannianBallOf

end FlowMetricBall

theorem kappaNoncollapsedBelowScale_timeShift_iff (S : SolutionOn (I := I) (M := M) D)
    (τ kappa rho : Real) :
    KappaNoncollapsedBelowScale (S.timeShift τ) kappa rho ↔
      KappaNoncollapsedBelowScale S kappa rho := by
  constructor
  · intro h
    refine ⟨h.1, fun t B hr hB => ?_⟩
    let t' : (D.timeShift τ).FlowTime := ⟨(t : Real) - τ, by
      change (t : Real) - τ + τ ∈ D.carrier
      rw [sub_add_cancel]
      exact t.2⟩
    have ht : (t' : Real) + τ = (t : Real) := by dsimp only [t']; ring
    let B' : FlowMetricBall (S.timeShift τ) t' := ⟨B.center, B.radius, B.radius_pos⟩
    have hB' : B'.IsRmControlled :=
      (FlowMetricBall.isRmControlled_timeShift_iff (S := S) τ (ht := ht) (B := B) (B' := B')
        (hcenter := rfl) (hradius := rfl)).2 hB
    have hk := h.2 t' B' hr hB'
    exact (FlowMetricBall.isKappaNoncollapsed_timeShift_iff (S := S) τ (ht := ht) (B := B)
      (B' := B') (hcenter := rfl) (hradius := rfl) kappa).1 hk
  · intro h
    refine ⟨h.1, fun t B hr hB => ?_⟩
    let t' : D.FlowTime := ⟨(t : Real) + τ, t.2⟩
    have ht : (t : Real) + τ = (t' : Real) := rfl
    let B' : FlowMetricBall S t' := ⟨B.center, B.radius, B.radius_pos⟩
    have hB' : B'.IsRmControlled :=
      (FlowMetricBall.isRmControlled_timeShift_iff (S := S) τ (ht := ht) (B := B') (B' := B)
        (hcenter := rfl) (hradius := rfl)).1 hB
    have hk := h.2 t' B' hr hB'
    exact (FlowMetricBall.isKappaNoncollapsed_timeShift_iff (S := S) τ (ht := ht) (B := B')
      (B' := B) (hcenter := rfl) (hradius := rfl) kappa).2 hk

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.kappaNoncollapsedBelowScale_timeShift_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.kappaNoncollapsedBelowScale_timeShift_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.kappaNoncollapsedBelowScale_timeShift_iff ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.kappaNoncollapsedBelowScale_timeShift_iff

theorem noLocalCollapsing_timeShift_iff (S : SolutionOn (I := I) (M := M) D)
    (τ rho : Real) :
    NoLocalCollapsing (S.timeShift τ) rho ↔ NoLocalCollapsing S rho := by
  constructor
  · rintro ⟨kappa, hkappa, hbelow⟩
    exact ⟨kappa, hkappa,
      (kappaNoncollapsedBelowScale_timeShift_iff (S := S) τ kappa rho).1 hbelow⟩
  · rintro ⟨kappa, hkappa, hbelow⟩
    exact ⟨kappa, hkappa,
      (kappaNoncollapsedBelowScale_timeShift_iff (S := S) τ kappa rho).2 hbelow⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.noLocalCollapsing_timeShift_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.noLocalCollapsing_timeShift_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.noLocalCollapsing_timeShift_iff ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.noLocalCollapsing_timeShift_iff

theorem kappaNoncollapsedOnAllScales_timeShift_iff (S : SolutionOn (I := I) (M := M) D)
    (τ kappa : Real) :
    KappaNoncollapsedOnAllScales (S.timeShift τ) kappa ↔
      KappaNoncollapsedOnAllScales S kappa := by
  constructor
  · intro h
    refine ⟨h.1, fun t B hB => ?_⟩
    let t' : (D.timeShift τ).FlowTime := ⟨(t : Real) - τ, by
      change (t : Real) - τ + τ ∈ D.carrier
      rw [sub_add_cancel]
      exact t.2⟩
    have ht : (t' : Real) + τ = (t : Real) := by dsimp only [t']; ring
    let B' : FlowMetricBall (S.timeShift τ) t' := ⟨B.center, B.radius, B.radius_pos⟩
    have hB' : B'.IsRmControlled :=
      (FlowMetricBall.isRmControlled_timeShift_iff (S := S) τ (ht := ht) (B := B) (B' := B')
        (hcenter := rfl) (hradius := rfl)).2 hB
    have hk := h.2 t' B' hB'
    exact (FlowMetricBall.isKappaNoncollapsed_timeShift_iff (S := S) τ (ht := ht) (B := B)
      (B' := B') (hcenter := rfl) (hradius := rfl) kappa).1 hk
  · intro h
    refine ⟨h.1, fun t B hB => ?_⟩
    let t' : D.FlowTime := ⟨(t : Real) + τ, t.2⟩
    have ht : (t : Real) + τ = (t' : Real) := rfl
    let B' : FlowMetricBall S t' := ⟨B.center, B.radius, B.radius_pos⟩
    have hB' : B'.IsRmControlled :=
      (FlowMetricBall.isRmControlled_timeShift_iff (S := S) τ (ht := ht) (B := B') (B' := B)
        (hcenter := rfl) (hradius := rfl)).1 hB
    have hk := h.2 t' B' hB'
    exact (FlowMetricBall.isKappaNoncollapsed_timeShift_iff (S := S) τ (ht := ht) (B := B')
      (B' := B) (hcenter := rfl) (hradius := rfl) kappa).2 hk

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.kappaNoncollapsedOnAllScales_timeShift_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.kappaNoncollapsedOnAllScales_timeShift_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.kappaNoncollapsedOnAllScales_timeShift_iff ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.kappaNoncollapsedOnAllScales_timeShift_iff

theorem spatiallyKappaNoncollapsedBelowScale_timeShift_iff
    (S : SolutionOn (I := I) (M := M) D) (τ kappa rho : Real) :
    SpatiallyKappaNoncollapsedBelowScale (S.timeShift τ) kappa rho ↔
      SpatiallyKappaNoncollapsedBelowScale S kappa rho := by
  constructor
  · intro h
    refine ⟨h.1, fun t B hr hB => ?_⟩
    let t' : (D.timeShift τ).FlowTime := ⟨(t : Real) - τ, by
      change (t : Real) - τ + τ ∈ D.carrier
      rw [sub_add_cancel]
      exact t.2⟩
    have ht : (t' : Real) + τ = (t : Real) := by dsimp only [t']; ring
    let B' : FlowMetricBall (S.timeShift τ) t' := ⟨B.center, B.radius, B.radius_pos⟩
    have hB' : B'.IsSpatiallyRmControlled :=
      (FlowMetricBall.isSpatiallyRmControlled_timeShift_iff (S := S) τ (ht := ht) (B := B)
        (B' := B') (hcenter := rfl) (hradius := rfl)).2 hB
    have hk := h.2 t' B' hr hB'
    exact (FlowMetricBall.isKappaNoncollapsed_timeShift_iff (S := S) τ (ht := ht) (B := B)
      (B' := B') (hcenter := rfl) (hradius := rfl) kappa).1 hk
  · intro h
    refine ⟨h.1, fun t B hr hB => ?_⟩
    let t' : D.FlowTime := ⟨(t : Real) + τ, t.2⟩
    have ht : (t : Real) + τ = (t' : Real) := rfl
    let B' : FlowMetricBall S t' := ⟨B.center, B.radius, B.radius_pos⟩
    have hB' : B'.IsSpatiallyRmControlled :=
      (FlowMetricBall.isSpatiallyRmControlled_timeShift_iff (S := S) τ (ht := ht) (B := B')
        (B' := B) (hcenter := rfl) (hradius := rfl)).1 hB
    have hk := h.2 t' B' hr hB'
    exact (FlowMetricBall.isKappaNoncollapsed_timeShift_iff (S := S) τ (ht := ht) (B := B')
      (B' := B) (hcenter := rfl) (hradius := rfl) kappa).2 hk

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.spatiallyKappaNoncollapsedBelowScale_timeShift_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.spatiallyKappaNoncollapsedBelowScale_timeShift_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.spatiallyKappaNoncollapsedBelowScale_timeShift_iff ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.spatiallyKappaNoncollapsedBelowScale_timeShift_iff

theorem spatialNoLocalCollapsing_timeShift_iff (S : SolutionOn (I := I) (M := M) D)
    (τ rho : Real) :
    SpatialNoLocalCollapsing (S.timeShift τ) rho ↔ SpatialNoLocalCollapsing S rho := by
  constructor
  · rintro ⟨kappa, hkappa, hbelow⟩
    exact ⟨kappa, hkappa,
      (spatiallyKappaNoncollapsedBelowScale_timeShift_iff (S := S) τ kappa rho).1 hbelow⟩
  · rintro ⟨kappa, hkappa, hbelow⟩
    exact ⟨kappa, hkappa,
      (spatiallyKappaNoncollapsedBelowScale_timeShift_iff (S := S) τ kappa rho).2 hbelow⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.spatialNoLocalCollapsing_timeShift_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.spatialNoLocalCollapsing_timeShift_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.spatialNoLocalCollapsing_timeShift_iff ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.spatialNoLocalCollapsing_timeShift_iff

theorem parabolicallyKappaNoncollapsedBelowScale_timeShift_iff
    (S : SolutionOn (I := I) (M := M) D) (τ kappa rho : Real) :
    ParabolicallyKappaNoncollapsedBelowScale (S.timeShift τ) kappa rho ↔
      ParabolicallyKappaNoncollapsedBelowScale S kappa rho := by
  constructor
  · intro h
    refine ⟨h.1, fun t B hr hB => ?_⟩
    let t' : (D.timeShift τ).FlowTime := ⟨(t : Real) - τ, by
      change (t : Real) - τ + τ ∈ D.carrier
      rw [sub_add_cancel]
      exact t.2⟩
    have ht : (t' : Real) + τ = (t : Real) := by dsimp only [t']; ring
    let B' : FlowMetricBall (S.timeShift τ) t' := ⟨B.center, B.radius, B.radius_pos⟩
    have hB' : B'.IsParabolicallyRmControlled :=
      (FlowMetricBall.isParabolicallyRmControlled_timeShift_iff (S := S) τ (ht := ht) (B := B)
        (B' := B') (hcenter := rfl) (hradius := rfl)).2 hB
    have hk := h.2 t' B' hr hB'
    exact (FlowMetricBall.isKappaNoncollapsed_timeShift_iff (S := S) τ (ht := ht) (B := B)
      (B' := B') (hcenter := rfl) (hradius := rfl) kappa).1 hk
  · intro h
    refine ⟨h.1, fun t B hr hB => ?_⟩
    let t' : D.FlowTime := ⟨(t : Real) + τ, t.2⟩
    have ht : (t : Real) + τ = (t' : Real) := rfl
    let B' : FlowMetricBall S t' := ⟨B.center, B.radius, B.radius_pos⟩
    have hB' : B'.IsParabolicallyRmControlled :=
      (FlowMetricBall.isParabolicallyRmControlled_timeShift_iff (S := S) τ (ht := ht) (B := B')
        (B' := B) (hcenter := rfl) (hradius := rfl)).1 hB
    have hk := h.2 t' B' hr hB'
    exact (FlowMetricBall.isKappaNoncollapsed_timeShift_iff (S := S) τ (ht := ht) (B := B')
      (B' := B) (hcenter := rfl) (hradius := rfl) kappa).2 hk

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.parabolicallyKappaNoncollapsedBelowScale_timeShift_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.parabolicallyKappaNoncollapsedBelowScale_timeShift_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.parabolicallyKappaNoncollapsedBelowScale_timeShift_iff ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.parabolicallyKappaNoncollapsedBelowScale_timeShift_iff

theorem parabolicNoLocalCollapsing_timeShift_iff (S : SolutionOn (I := I) (M := M) D)
    (τ rho : Real) :
    ParabolicNoLocalCollapsing (S.timeShift τ) rho ↔ ParabolicNoLocalCollapsing S rho := by
  constructor
  · rintro ⟨kappa, hkappa, hbelow⟩
    exact ⟨kappa, hkappa,
      (parabolicallyKappaNoncollapsedBelowScale_timeShift_iff (S := S) τ kappa rho).1 hbelow⟩
  · rintro ⟨kappa, hkappa, hbelow⟩
    exact ⟨kappa, hkappa,
      (parabolicallyKappaNoncollapsedBelowScale_timeShift_iff (S := S) τ kappa rho).2 hbelow⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.parabolicNoLocalCollapsing_timeShift_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.parabolicNoLocalCollapsing_timeShift_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.parabolicNoLocalCollapsing_timeShift_iff ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.parabolicNoLocalCollapsing_timeShift_iff

theorem stronglyScalarKappaNoncollapsedBelowScale_timeShift_iff
    (S : SolutionOn (I := I) (M := M) D) (τ kappa rho : Real) :
    StronglyScalarKappaNoncollapsedBelowScale (S.timeShift τ) kappa rho ↔
      StronglyScalarKappaNoncollapsedBelowScale S kappa rho := by
  constructor
  · intro h
    refine ⟨h.1, fun t B hr hsc B₂ hc₂ hr₂ => ?_⟩
    let t' : (D.timeShift τ).FlowTime := ⟨(t : Real) - τ, by
      change (t : Real) - τ + τ ∈ D.carrier
      rw [sub_add_cancel]
      exact t.2⟩
    have ht : (t' : Real) + τ = (t : Real) := by dsimp only [t']; ring
    let B' : FlowMetricBall (S.timeShift τ) t' := ⟨B.center, B.radius, B.radius_pos⟩
    let B₂' : FlowMetricBall (S.timeShift τ) t' := ⟨B₂.center, B₂.radius, B₂.radius_pos⟩
    have hsc' : B'.IsScalarControlled :=
      (FlowMetricBall.isScalarControlled_timeShift_iff (S := S) τ (ht := ht) (B := B) (B' := B')
        (hcenter := rfl) (hradius := rfl)).2 hsc
    have hk := h.2 t' B' hr hsc' B₂' hc₂ hr₂
    exact (FlowMetricBall.isKappaNoncollapsed_timeShift_iff (S := S) τ (ht := ht) (B := B₂)
      (B' := B₂') (hcenter := rfl) (hradius := rfl) kappa).1 hk
  · intro h
    refine ⟨h.1, fun t B hr hsc B₂ hc₂ hr₂ => ?_⟩
    let t' : D.FlowTime := ⟨(t : Real) + τ, t.2⟩
    have ht : (t : Real) + τ = (t' : Real) := rfl
    let B' : FlowMetricBall S t' := ⟨B.center, B.radius, B.radius_pos⟩
    let B₂' : FlowMetricBall S t' := ⟨B₂.center, B₂.radius, B₂.radius_pos⟩
    have hsc' : B'.IsScalarControlled :=
      (FlowMetricBall.isScalarControlled_timeShift_iff (S := S) τ (ht := ht) (B := B') (B' := B)
        (hcenter := rfl) (hradius := rfl)).1 hsc
    have hk := h.2 t' B' hr hsc' B₂' hc₂ hr₂
    exact (FlowMetricBall.isKappaNoncollapsed_timeShift_iff (S := S) τ (ht := ht) (B := B₂')
      (B' := B₂) (hcenter := rfl) (hradius := rfl) kappa).2 hk

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.stronglyScalarKappaNoncollapsedBelowScale_timeShift_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.stronglyScalarKappaNoncollapsedBelowScale_timeShift_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.stronglyScalarKappaNoncollapsedBelowScale_timeShift_iff ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.stronglyScalarKappaNoncollapsedBelowScale_timeShift_iff

theorem strongScalarNoLocalCollapsing_timeShift_iff (S : SolutionOn (I := I) (M := M) D)
    (τ rho : Real) :
    StrongScalarNoLocalCollapsing (S.timeShift τ) rho ↔
      StrongScalarNoLocalCollapsing S rho := by
  constructor
  · rintro ⟨kappa, hkappa, hbelow⟩
    exact ⟨kappa, hkappa,
      (stronglyScalarKappaNoncollapsedBelowScale_timeShift_iff (S := S) τ kappa rho).1 hbelow⟩
  · rintro ⟨kappa, hkappa, hbelow⟩
    exact ⟨kappa, hkappa,
      (stronglyScalarKappaNoncollapsedBelowScale_timeShift_iff (S := S) τ kappa rho).2 hbelow⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.strongScalarNoLocalCollapsing_timeShift_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.strongScalarNoLocalCollapsing_timeShift_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.strongScalarNoLocalCollapsing_timeShift_iff ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.strongScalarNoLocalCollapsing_timeShift_iff

theorem kappaNoncollapsedBelowScale_of_metric_eqOn (S S' : SolutionOn (I := I) (M := M) D)
    (kappa rho : Real) (h : KappaNoncollapsedBelowScale S kappa rho)
    (hm : ∀ (t : D.FlowTime) (r : Real), 0 < r → r ≤ rho →
      ∀ s ∈ Set.Icc ((t : Real) - r ^ 2) (t : Real),
        S'.base.metric s = S.base.metric s) :
    KappaNoncollapsedBelowScale S' kappa rho := by
  refine ⟨h.1, fun t B' hr hB' => ?_⟩
  let B : FlowMetricBall S t := ⟨B'.center, B'.radius, B'.radius_pos⟩
  have hB : B.IsRmControlled :=
    FlowMetricBall.isRmControlled_of_metric_eqOn (S := S') (S' := S) B' B rfl rfl
      (fun s hs => (hm t B'.radius B'.radius_pos hr s hs).symm) hB'
  have hk := h.2 t B hr hB
  exact FlowMetricBall.isKappaNoncollapsed_of_metric_eq (S := S) (S' := S') B B' rfl rfl
    (hm t B'.radius B'.radius_pos hr (t : Real)
      ⟨by linarith [sq_nonneg B'.radius], le_rfl⟩) kappa hk

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.kappaNoncollapsedBelowScale_of_metric_eqOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.kappaNoncollapsedBelowScale_of_metric_eqOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.kappaNoncollapsedBelowScale_of_metric_eqOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.kappaNoncollapsedBelowScale_of_metric_eqOn

theorem spatiallyKappaNoncollapsedBelowScale_of_metric_eqOn
    (S S' : SolutionOn (I := I) (M := M) D)
    (kappa rho : Real) (h : SpatiallyKappaNoncollapsedBelowScale S kappa rho)
    (hm : ∀ (t : D.FlowTime) (r : Real), 0 < r → r ≤ rho →
      S'.base.metric (t : Real) = S.base.metric (t : Real)) :
    SpatiallyKappaNoncollapsedBelowScale S' kappa rho := by
  refine ⟨h.1, fun t B' hr hB' => ?_⟩
  let B : FlowMetricBall S t := ⟨B'.center, B'.radius, B'.radius_pos⟩
  have hB : B.IsSpatiallyRmControlled :=
    FlowMetricBall.isSpatiallyRmControlled_of_metric_eq (S := S') (S' := S) B' B rfl rfl
      (hm t B'.radius B'.radius_pos hr).symm hB'
  have hk := h.2 t B hr hB
  exact FlowMetricBall.isKappaNoncollapsed_of_metric_eq (S := S) (S' := S') B B' rfl rfl
    (hm t B'.radius B'.radius_pos hr) kappa hk

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.spatiallyKappaNoncollapsedBelowScale_of_metric_eqOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.spatiallyKappaNoncollapsedBelowScale_of_metric_eqOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.spatiallyKappaNoncollapsedBelowScale_of_metric_eqOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.spatiallyKappaNoncollapsedBelowScale_of_metric_eqOn

end

end DifferentialGeometry.PDE.RicciFlow.Perelman
