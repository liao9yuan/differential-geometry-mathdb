import Submission.DifferentialGeometry.Topology.ThreeManifold.CutCap
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Basic
import Submission.DifferentialGeometry.Geometry.Metric.Pullback.PartialDiffeomorph.OpenSubtype
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Basic
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.Defs

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Topology (ClosedOrientedManifold SphericalCutCapTransition)
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery

universe u

def metricSmoothUpTo (M : ClosedOrientedManifold.{u} 3)
    (g : ℝ → SmoothRiemannianMetric (𝓡 3) M.Carrier) (J : Set ℝ) : Prop :=
  ∀ p : M.Carrier, ∀ t ∈ J,
    ∃ U : Set M.Carrier, IsOpen U ∧ p ∈ U ∧
      U ⊆ (_root_.FiberBundle.trivializationAt (EuclideanSpace ℝ (Fin 3)) (TangentSpace (𝓡 3)) p).baseSet ∧
      ∃ V : Set ℝ, IsOpen V ∧ t ∈ V ∧
      ∃ A : ℝ × M.Carrier → Matrix (Fin 3) (Fin 3) ℝ,
        (∀ i j : Fin 3, ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3))
          𝓘(ℝ, ℝ) ∞ (fun z => A z i j) (V ×ˢ U)) ∧
        ∀ s ∈ V ∩ J, ∀ x ∈ U, ∀ i j : Fin 3,
          A (s, x) i j = (g s).inner x
            ((_root_.FiberBundle.trivializationAt (EuclideanSpace ℝ (Fin 3)) (TangentSpace (𝓡 3)) p).symmL ℝ x
              (EuclideanSpace.single i (1 : ℝ)))
            ((_root_.FiberBundle.trivializationAt (EuclideanSpace ℝ (Fin 3)) (TangentSpace (𝓡 3)) p).symmL ℝ x
              (EuclideanSpace.single j (1 : ℝ)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.metricSmoothUpTo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.metricSmoothUpTo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.metricSmoothUpTo ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.metricSmoothUpTo

structure IncomingSlab (M : ClosedOrientedManifold.{u} 3) (a s : ℝ) where
  lt : a < s
  flow : SolutionOn (I := 𝓡 3) (M := M.Carrier) (RealTimeInterval.closedOpen a s lt)
  equation : IsSolutionOn flow
  smoothUpTo : metricSmoothUpTo M flow.base.metric (_root_.Set.Ico a s)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.IncomingSlab then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.IncomingSlab"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.IncomingSlab ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.IncomingSlab

namespace IncomingSlab

variable {M : ClosedOrientedManifold.{u} 3} {a s : ℝ} (G : IncomingSlab M a s)

def riemannNorm (t : ℝ) (x : M.Carrier) : ℝ :=
  Real.sqrt (normSq0S (G.flow.base.metric t) x 4 (G.flow.base.rm04 t x))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.IncomingSlab.riemannNorm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.IncomingSlab.riemannNorm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.IncomingSlab.riemannNorm ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.IncomingSlab.riemannNorm

def terminalRegularRegion : Set M.Carrier :=
  {x | ∃ U : Set M.Carrier, IsOpen U ∧ x ∈ U ∧
    ∃ a' ∈ _root_.Set.Ico a s, ∃ K : ℝ, 0 ≤ K ∧
      ∀ y ∈ U, ∀ t ∈ _root_.Set.Ico a' s, G.riemannNorm t y ≤ K}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.IncomingSlab.terminalRegularRegion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.IncomingSlab.terminalRegularRegion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.IncomingSlab.terminalRegularRegion ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.IncomingSlab.terminalRegularRegion

theorem isOpen_terminalRegularRegion : IsOpen G.terminalRegularRegion := by
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨U, hU, hxU, a', ha', K, hK, hbound⟩
  apply Filter.mem_of_superset (hU.mem_nhds hxU)
  intro y hy
  exact ⟨U, hU, hy, a', ha', K, hK, hbound⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.IncomingSlab.isOpen_terminalRegularRegion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.IncomingSlab.isOpen_terminalRegularRegion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.IncomingSlab.isOpen_terminalRegularRegion ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.IncomingSlab.isOpen_terminalRegularRegion

def terminalRegularOpen : TopologicalSpace.Opens M.Carrier :=
  ⟨G.terminalRegularRegion, G.isOpen_terminalRegularRegion⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.IncomingSlab.terminalRegularOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.IncomingSlab.terminalRegularOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.IncomingSlab.terminalRegularOpen ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.IncomingSlab.terminalRegularOpen

def terminalMetricConverges
    (gbar : SmoothRiemannianMetric (𝓡 3) G.terminalRegularOpen) : Prop :=
  letI : SecondCountableTopology M.Carrier :=
    ChartedSpace.secondCountable_of_sigmaCompact (EuclideanSpace ℝ (Fin 3)) M.Carrier
  letI : LocallyCompactSpace G.terminalRegularOpen :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin 3)) G.terminalRegularOpen
  ∀ K : Set G.terminalRegularOpen, IsCompact K → ∀ j : ℕ, ∀ ε : ℝ, 0 < ε →
    ∃ d ∈ _root_.Set.Ico a s, ∀ t ∈ _root_.Set.Ioo d s, ∀ x ∈ K,
      DifferentialGeometry.CheegerGromovCompactness.metricDerivNorm j
        ((G.flow.base.metric t).restrictOpen G.terminalRegularOpen) gbar gbar x < ε

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.IncomingSlab.terminalMetricConverges then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.IncomingSlab.terminalMetricConverges"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.IncomingSlab.terminalMetricConverges ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.IncomingSlab.terminalMetricConverges

structure TerminalLimitMetric where
  metric : SmoothRiemannianMetric (𝓡 3) G.terminalRegularOpen
  converges : G.terminalMetricConverges metric

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.IncomingSlab.TerminalLimitMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.IncomingSlab.TerminalLimitMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.IncomingSlab.TerminalLimitMetric ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.IncomingSlab.TerminalLimitMetric

end IncomingSlab

structure MetricCutCapEvent (M Q : ClosedOrientedManifold.{u} 3) (a s : ℝ) where
  transition : SphericalCutCapTransition M Q
  incoming : IncomingSlab M a s
  terminal : incoming.TerminalLimitMetric
  outputMetric : SmoothRiemannianMetric (𝓡 3) Q.Carrier
  unchanged : Set transition.tubes.core
  unchanged_compact : IsCompact unchanged
  unchanged_retained : unchanged ⊆ transition.retainedCore
  [unchangedCharts : ChartedSpace (EuclideanHalfSpace 3) unchanged]
  [unchangedSmooth : IsManifold (𝓡∂ 3) ∞ unchanged]
  unchanged_induced : _root_.Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞
    (fun x : unchanged => (x.1.1 : M.Carrier))
  terminalInclusion : C(unchanged, incoming.terminalRegularOpen)
  terminalInclusion_eq : ∀ x : unchanged, (terminalInclusion x).1 = x.1.1
  terminalInclusion_smooth : _root_.Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ terminalInclusion
  outputInclusion : C(unchanged, Q.Carrier)
  outputInclusion_eq : ∀ x : unchanged,
    transition.presentation (transition.capping.coreInclusion x.1) = Sum.inl (outputInclusion x)
  outputInclusion_smooth : _root_.Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ outputInclusion
  unchanged_metric_eq : ∀ x : unchanged, ∀ v w : TangentSpace (𝓡∂ 3) x,
    terminal.metric.inner (terminalInclusion x)
        (mfderiv (𝓡∂ 3) (𝓡 3) terminalInclusion x v)
        (mfderiv (𝓡∂ 3) (𝓡 3) terminalInclusion x w) =
      outputMetric.inner (outputInclusion x)
        (mfderiv (𝓡∂ 3) (𝓡 3) outputInclusion x v)
        (mfderiv (𝓡∂ 3) (𝓡 3) outputInclusion x w)
  unchanged_contains_outside : ∀ x : transition.tubes.core,
    x ∈ transition.retainedCore → x.1 ∉ transition.tubes.surgeryRegion → x ∈ unchanged
  every_component_meets_unchanged : ∀ c : ConnectedComponents Q.Carrier,
    ∃ x : unchanged, ConnectedComponents.mk (outputInclusion x) = c

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.MetricCutCapEvent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.MetricCutCapEvent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.MetricCutCapEvent ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.MetricCutCapEvent

attribute [instance] MetricCutCapEvent.unchangedCharts MetricCutCapEvent.unchangedSmooth

namespace MetricCutCapEvent

theorem unchanged_isEmpty_of_isEmpty {M Q : ClosedOrientedManifold.{u} 3} {a s : ℝ}
    (E : MetricCutCapEvent M Q a s) (h : IsEmpty Q.Carrier) : IsEmpty E.unchanged :=
  ⟨fun x => h.false (E.outputInclusion x)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.MetricCutCapEvent.unchanged_isEmpty_of_isEmpty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.MetricCutCapEvent.unchanged_isEmpty_of_isEmpty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.MetricCutCapEvent.unchanged_isEmpty_of_isEmpty ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.MetricCutCapEvent.unchanged_isEmpty_of_isEmpty

end MetricCutCapEvent

end DifferentialGeometry.PDE.RicciFlow.Surgery
