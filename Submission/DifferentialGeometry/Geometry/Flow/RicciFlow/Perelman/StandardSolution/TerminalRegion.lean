import Submission.DifferentialGeometry.Geometry.Curvature.Metric.Defs
import Submission.DifferentialGeometry.Geometry.Metric.DerivativeENorm

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Function _root_.TopologicalSpace _root_.Filter _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Geometry.Metric
open scoped _root_.Manifold _root_.ContDiff _root_.Topology _root_.ENNReal
namespace DifferentialGeometry.PDE.RicciFlow
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

def terminalRegularRegion (g : ℝ → SmoothRiemannianMetric I M) (a s : ℝ) : _root_.TopologicalSpace.Opens M :=
  ⟨{x | ∃ U : _root_.TopologicalSpace.Opens M, x ∈ U ∧ ∃ a' ∈ _root_.Set.Ico a s, ∃ K : ℝ, 0 ≤ K ∧
    ∀ y ∈ U, ∀ t ∈ _root_.Set.Ico a' s, Real.sqrt (normSq0S (g t) y 4 (metricRm04 (g t) y)) ≤ K}, by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    obtain ⟨U, hxU, a', ha', K, hK, hb⟩ := hx
    exact Filter.mem_of_superset (U.isOpen.mem_nhds hxU)
      (fun y hy => ⟨U, hy, a', ha', K, hK, hb⟩)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.terminalRegularRegion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.terminalRegularRegion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.terminalRegularRegion ``Submission.DifferentialGeometry.PDE.RicciFlow.terminalRegularRegion

theorem mem_terminalRegularRegion (g : ℝ → SmoothRiemannianMetric I M) (a s : ℝ) (x : M) :
    x ∈ terminalRegularRegion g a s ↔
      ∃ U : _root_.TopologicalSpace.Opens M, x ∈ U ∧ ∃ a' ∈ _root_.Set.Ico a s, ∃ K : ℝ, 0 ≤ K ∧
        ∀ y ∈ U, ∀ t ∈ _root_.Set.Ico a' s,
          Real.sqrt (normSq0S (g t) y 4 (metricRm04 (g t) y)) ≤ K := Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.mem_terminalRegularRegion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.mem_terminalRegularRegion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.mem_terminalRegularRegion ``Submission.DifferentialGeometry.PDE.RicciFlow.mem_terminalRegularRegion

theorem subset_terminalRegularRegion_of_bound
    (g : ℝ → SmoothRiemannianMetric I M) (a s : ℝ) (U : _root_.TopologicalSpace.Opens M)
    (a' : ℝ) (ha' : a' ∈ _root_.Set.Ico a s) (K : ℝ) (hK : 0 ≤ K)
    (hb : ∀ y ∈ U, ∀ t ∈ _root_.Set.Ico a' s,
      Real.sqrt (normSq0S (g t) y 4 (metricRm04 (g t) y)) ≤ K) :
    U ≤ terminalRegularRegion g a s := fun _ hy => ⟨U, hy, a', ha', K, hK, hb⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.subset_terminalRegularRegion_of_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.subset_terminalRegularRegion_of_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.subset_terminalRegularRegion_of_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.subset_terminalRegularRegion_of_bound

theorem terminalRegularRegion_eq_top_of_uniform_bound
    (g : ℝ → SmoothRiemannianMetric I M) (a s : ℝ) (has : a < s)
    (K : ℝ) (hK : 0 ≤ K)
    (hb : ∀ t ∈ _root_.Set.Ico a s, ∀ y : M,
      Real.sqrt (normSq0S (g t) y 4 (metricRm04 (g t) y)) ≤ K) :
    terminalRegularRegion g a s = ⊤ := by
  apply top_unique
  exact subset_terminalRegularRegion_of_bound g a s ⊤ a ⟨le_rfl, has⟩ K hK
    (fun y _ t ht => hb t ht y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.terminalRegularRegion_eq_top_of_uniform_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.terminalRegularRegion_eq_top_of_uniform_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.terminalRegularRegion_eq_top_of_uniform_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.terminalRegularRegion_eq_top_of_uniform_bound

theorem terminalRegularRegion_const (g : SmoothRiemannianMetric I M)
    (a s : ℝ) (has : a < s) : terminalRegularRegion (fun _ => g) a s = ⊤ := by
  apply top_unique
  intro x _
  let f : M → ℝ := fun y => Real.sqrt (normSq0S g y 4 (metricRm04 g y))
  have hf : Continuous f := Real.continuous_sqrt.comp (DifferentialGeometry.Tensor.RSTensor.normSq0S_smooth g (metricRm04 g)).continuous
  let U : _root_.TopologicalSpace.Opens M := ⟨{y | f y < f x + 1}, isOpen_lt hf continuous_const⟩
  refine ⟨U, ?_, a, ⟨le_rfl, has⟩, f x + 1, ?_, ?_⟩
  · change f x < f x + 1; linarith
  · have hx : 0 ≤ f x := Real.sqrt_nonneg _; linarith
  · intro y hy t _
    exact hy.le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.terminalRegularRegion_const then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.terminalRegularRegion_const"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.terminalRegularRegion_const ``Submission.DifferentialGeometry.PDE.RicciFlow.terminalRegularRegion_const

def IsTerminalLimitMetric (g : ℝ → SmoothRiemannianMetric I M) (a s : ℝ)
    (gLimit : SmoothRiemannianMetric I (terminalRegularRegion g a s)) : Prop :=
  ∀ K : Set (terminalRegularRegion g a s), IsCompact K → ∀ j : ℕ,
    _root_.Filter.Tendsto (fun t => metricDerivENormSupOn K j
      ((g t).restrictOpen (terminalRegularRegion g a s)) gLimit gLimit) (𝓝[<] s) (𝓝 0)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IsTerminalLimitMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IsTerminalLimitMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IsTerminalLimitMetric ``Submission.DifferentialGeometry.PDE.RicciFlow.IsTerminalLimitMetric

theorem isTerminalLimitMetric_const (g : SmoothRiemannianMetric I M) (a s : ℝ) :
    IsTerminalLimitMetric (fun _ => g) a s (g.restrictOpen (terminalRegularRegion (fun _ => g) a s)) := by
  intro K _ j
  simpa only [metricDerivENormSupOn_self] using
    (tendsto_const_nhds : _root_.Filter.Tendsto (fun _ : ℝ => (0 : ℝ≥0∞)) (𝓝[<] s) (𝓝 0))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.isTerminalLimitMetric_const then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.isTerminalLimitMetric_const"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.isTerminalLimitMetric_const ``Submission.DifferentialGeometry.PDE.RicciFlow.isTerminalLimitMetric_const
end DifferentialGeometry.PDE.RicciFlow
