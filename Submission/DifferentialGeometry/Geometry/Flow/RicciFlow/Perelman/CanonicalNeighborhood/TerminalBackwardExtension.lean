import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BlowupConvergence
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalChartJets
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalCurvatureJets
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.FlowOfMetric
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.IteratedCovariantDerivativeFields
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CrossModelBallCapture

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open scoped _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

section FlowOn

variable {N : Type u} [TopologicalSpace N] [ChartedSpace ThreeSpace N]
  [IsManifold I3 ∞ N] [T2Space N] [SigmaCompactSpace N]

def flowOn (D : RealTimeInterval) (g : ℝ → SmoothRiemannianMetric I3 N) :
    SolutionOn (I := I3) (M := N) D :=
  { base := { metric := g } }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.flowOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.flowOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.flowOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.flowOn

omit [T2Space N] [SigmaCompactSpace N] in
@[simp] theorem flowOn_metric (D : RealTimeInterval)
    (g : ℝ → SmoothRiemannianMetric I3 N) (t : ℝ) :
    (flowOn (N := N) D g).base.metric t = g t :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.flowOn_metric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.flowOn_metric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.flowOn_metric ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.flowOn_metric

end FlowOn

structure StaticTerminalLimit (X : FlowSequence.{u}) (depthBound : ℝ) where
  carrier_window : ∀ i, Set.Icc (-depthBound) 0 ⊆ (X.interval i).carrier
  regular_window : ∀ i, Set.Ioo (-depthBound) 0 ⊆ (X.interval i).regular
  space : PointedRiemannianManifold.{u, 0, 0} I3
  subseq : ℕ → ℕ
  strictMono : StrictMono subseq
  maps : PointedRiemannianConvergenceMaps (X.atTime 0) space subseq
  converges : MetricConvergenceData maps
  canonical_domains : ∀ k,
    converges.domain k = CanonicalMetricCompactness.canonicalSourceData maps k
  capture : MetricSourceCapture maps
  precompact : ∀ i, IsCompact (closure (maps.partialDiffeomorph i).source)
  connected_domains : ∀ i, IsConnected (maps.partialDiffeomorph i).source
  nested : ∀ i,
    closure (maps.partialDiffeomorph i).source ⊆ (maps.partialDiffeomorph (i + 1)).source
  connected : ConnectedSpace space.M
  complete : MetricComplete space
  nonnegative : SecLower space.metric 0 Set.univ
  slab_bounds : ∀ K : Set space.M, IsCompact K → ∀ width : ℝ, 0 < width →
    width < depthBound → ∃ C : ℝ, ∀ᶠ i in Filter.atTop,
      ∀ t ∈ Set.Icc (-width) 0, ∀ y ∈ K,
        PointedFlowData.rmNormSq (X.term (subseq i)) t ((maps.partialDiffeomorph i) y) ≤ C

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StaticTerminalLimit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StaticTerminalLimit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StaticTerminalLimit ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StaticTerminalLimit

theorem StaticTerminalLimit.window_subset_carrier {X : FlowSequence.{u}} {depthBound : ℝ}
    (L : StaticTerminalLimit X depthBound) {delta : ℝ} (hle : delta ≤ depthBound) (i : ℕ) :
    Set.Icc (-delta) 0 ⊆ (X.interval i).carrier :=
  (Set.Icc_subset_Icc (by linarith) le_rfl).trans (L.carrier_window i)

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StaticTerminalLimit
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StaticTerminalLimit.window_subset_carrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StaticTerminalLimit.window_subset_carrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StaticTerminalLimit.window_subset_carrier ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StaticTerminalLimit.window_subset_carrier

theorem StaticTerminalLimit.open_window_subset_regular {X : FlowSequence.{u}} {depthBound : ℝ}
    (L : StaticTerminalLimit X depthBound) {delta : ℝ} (hle : delta ≤ depthBound) (i : ℕ) :
    Set.Ioo (-delta) 0 ⊆ (X.interval i).regular :=
  (Set.Ioo_subset_Ioo (by linarith) le_rfl).trans (L.regular_window i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StaticTerminalLimit.open_window_subset_regular then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StaticTerminalLimit.open_window_subset_regular"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StaticTerminalLimit.open_window_subset_regular ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StaticTerminalLimit.open_window_subset_regular

structure TerminalBackwardSlab {X : FlowSequence.{u}} {depthBound : ℝ}
    (L : StaticTerminalLimit X depthBound) (D : RealTimeInterval) where
  solution : SolutionOn (I := I3) (M := L.space.M) D
  isSolution : IsSolutionOn solution
  terminal : solution.base.metric 0 = L.space.metric
  subseq : ℕ → ℕ
  strictMono : StrictMono subseq
  convergence : ConvergesOn (subsequenceMaps L.maps subseq strictMono) solution
  complete : ∀ t ∈ D.carrier,
    MetricComplete { L.space with metric := solution.base.metric t }
  nonnegative : ∀ t ∈ D.carrier, SecLower (solution.base.metric t) 0 Set.univ
  compact_time_bound : ∀ a b : ℝ, a ≤ b → Set.Icc a b ⊆ D.carrier →
    ∃ C : ℝ, ∀ t ∈ Set.Icc a b, ∀ x, FlowMetricBall.rmNormSq solution t x ≤ C

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalBackwardSlab then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalBackwardSlab"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalBackwardSlab ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalBackwardSlab

def TerminalBackwardSlab.pointed {X : FlowSequence.{u}} {depthBound : ℝ}
    {L : StaticTerminalLimit X depthBound} {D : RealTimeInterval}
    (B : TerminalBackwardSlab L D) : PointedFlowData.{u, 0, 0} I3 D where
  M := L.space.M
  topology := L.space.topology
  charted := L.space.charted
  smooth := L.space.smooth
  sigmaCompact := L.space.sigmaCompact
  t2 := L.space.t2
  t2TangentBundle := L.space.t2TangentBundle
  basepoint := L.space.basepoint
  S := B.solution
  isSolution := B.isSolution

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalBackwardSlab
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalBackwardSlab.pointed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalBackwardSlab.pointed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalBackwardSlab.pointed ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalBackwardSlab.pointed

theorem TerminalBackwardSlab.pointed_atTime_zero {X : FlowSequence.{u}} {depthBound : ℝ}
    {L : StaticTerminalLimit X depthBound} {D : RealTimeInterval}
    (B : TerminalBackwardSlab L D) : B.pointed.atTime 0 = L.space :=
  congrArg
    (fun m =>
      ({ M := L.space.M
         topology := L.space.topology
         charted := L.space.charted
         smooth := L.space.smooth
         sigmaCompact := L.space.sigmaCompact
         t2 := L.space.t2
         t2TangentBundle := L.space.t2TangentBundle
         basepoint := L.space.basepoint
         metric := m } : PointedRiemannianManifold.{u, 0, 0} I3))
    B.terminal

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalBackwardSlab.pointed_atTime_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalBackwardSlab.pointed_atTime_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalBackwardSlab.pointed_atTime_zero ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalBackwardSlab.pointed_atTime_zero

def IsSlabLimit {X : FlowSequence.{u}} {depthBound : ℝ}
    (L : StaticTerminalLimit X depthBound) (delta : ℝ) (hd : 0 < delta)
    (g : ℝ → SmoothRiemannianMetric I3 L.space.M) : Prop :=
  g 0 = L.space.metric ∧ ∃ k : ℕ → ℕ, ∃ hk : StrictMono k,
    ConvergesOn (subsequenceMaps L.maps k hk)
      (flowOn (N := L.space.M)
        (RealTimeInterval.closed (-delta) 0 (by linarith)) g)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.IsSlabLimit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.IsSlabLimit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.IsSlabLimit ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.IsSlabLimit

def SlabComparison {X : FlowSequence.{u}} {depthBound : ℝ}
    (L : StaticTerminalLimit X depthBound) (delta : ℝ) (k : ℕ → ℕ)
    (g : ℝ → SmoothRiemannianMetric I3 L.space.M) : Prop :=
  ∀ K : Set L.space.M, IsCompact K → ∀ a b : ℝ, a ≤ b →
    Set.Icc a b ⊆ Set.Icc (-delta) 0 → ∀ order : ℕ, ∀ eps : ℝ, 0 < eps →
      ∀ᶠ i in Filter.atTop,
        Nonempty (MetricComparisonOn (fun s => g s)
          (fun s => (X.term (L.subseq (k i))).S.base.metric s)
          (L.maps.partialDiffeomorph (k i)) K (Set.Icc a b) order eps)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SlabComparison then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SlabComparison"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SlabComparison ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SlabComparison

theorem convergesOn_of_slabComparison {X : FlowSequence.{u}} {depthBound : ℝ}
    (L : StaticTerminalLimit X depthBound) {delta : ℝ} (hd : 0 < delta)
    (hle : delta ≤ depthBound) {k : ℕ → ℕ} (hk : StrictMono k)
    {g : ℝ → SmoothRiemannianMetric I3 L.space.M}
    (hcomp : SlabComparison L delta k g) :
    ConvergesOn (subsequenceMaps L.maps k hk)
      (flowOn (N := L.space.M)
        (RealTimeInterval.closed (-delta) 0 (by linarith)) g) := by
  intro K hK a b hab hsub order eps heps
  obtain ⟨k0, hk0⟩ := L.maps.source_subset hK
  filter_upwards [hcomp K hK a b hab hsub order eps heps,
    Filter.eventually_ge_atTop k0] with i hi hik0
  refine ⟨fun t ht => L.window_subset_carrier hle _ (hsub ht), ?_, hi⟩
  exact hk0 (k i) (hik0.trans (StrictMono.le_apply hk))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.convergesOn_of_slabComparison then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.convergesOn_of_slabComparison"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.convergesOn_of_slabComparison ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.convergesOn_of_slabComparison

theorem isSlabLimit_of_slabComparison {X : FlowSequence.{u}} {depthBound : ℝ}
    (L : StaticTerminalLimit X depthBound) {delta : ℝ} (hd : 0 < delta)
    (hle : delta ≤ depthBound) {k : ℕ → ℕ} (hk : StrictMono k)
    {g : ℝ → SmoothRiemannianMetric I3 L.space.M} (hg0 : g 0 = L.space.metric)
    (hcomp : SlabComparison L delta k g) :
    IsSlabLimit L delta hd g :=
  ⟨hg0, k, hk, convergesOn_of_slabComparison L hd hle hk hcomp⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.isSlabLimit_of_slabComparison then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.isSlabLimit_of_slabComparison"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.isSlabLimit_of_slabComparison ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.isSlabLimit_of_slabComparison

def SlabLimitExists {X : FlowSequence.{u}} {depthBound : ℝ}
    (L : StaticTerminalLimit X depthBound) (delta : ℝ) : Prop :=
  ∃ g : ℝ → SmoothRiemannianMetric I3 L.space.M, g 0 = L.space.metric ∧
    ∃ k : ℕ → ℕ, StrictMono k ∧ SlabComparison L delta k g

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SlabLimitExists then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SlabLimitExists"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SlabLimitExists ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SlabLimitExists

def SlabLimitIsFlow {X : FlowSequence.{u}} {depthBound : ℝ}
    (L : StaticTerminalLimit X depthBound) (delta : ℝ) (hd : 0 < delta) : Prop :=
  ∀ g : ℝ → SmoothRiemannianMetric I3 L.space.M, IsSlabLimit L delta hd g →
    IsSolutionOn (flowOn (N := L.space.M)
      (RealTimeInterval.closed (-delta) 0 (by linarith)) g)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SlabLimitIsFlow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SlabLimitIsFlow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SlabLimitIsFlow ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SlabLimitIsFlow

def SlabLimitSliceGeometry {X : FlowSequence.{u}} {depthBound : ℝ}
    (L : StaticTerminalLimit X depthBound) (delta : ℝ) (hd : 0 < delta) : Prop :=
  ∀ g : ℝ → SmoothRiemannianMetric I3 L.space.M, IsSlabLimit L delta hd g →
    (∀ t ∈ Set.Icc (-delta) 0, MetricComplete { L.space with metric := g t }) ∧
      ∀ t ∈ Set.Icc (-delta) 0, SecLower (g t) 0 Set.univ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SlabLimitSliceGeometry then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SlabLimitSliceGeometry"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SlabLimitSliceGeometry ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SlabLimitSliceGeometry

def SlabLimitCurvatureBound {X : FlowSequence.{u}} {depthBound : ℝ}
    (L : StaticTerminalLimit X depthBound) (delta : ℝ) (hd : 0 < delta) : Prop :=
  ∀ g : ℝ → SmoothRiemannianMetric I3 L.space.M, IsSlabLimit L delta hd g →
    ∀ a b : ℝ, a ≤ b → Set.Icc a b ⊆ Set.Icc (-delta) 0 → ∃ C : ℝ,
      ∀ t ∈ Set.Icc a b, ∀ x : L.space.M,
        FlowMetricBall.rmNormSq (flowOn (N := L.space.M)
          (RealTimeInterval.closed (-delta) 0 (by linarith)) g) t x ≤ C

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SlabLimitCurvatureBound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SlabLimitCurvatureBound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SlabLimitCurvatureBound ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SlabLimitCurvatureBound

theorem exists_terminalBackwardFlow_of_delta {X : FlowSequence.{u}} {depthBound : ℝ}
    (L : StaticTerminalLimit X depthBound) {delta : ℝ} (hd : 0 < delta)
    (hle : delta ≤ depthBound)
    (h1 : SlabLimitExists L delta) (h2 : SlabLimitIsFlow L delta hd) :
    ∃ g : ℝ → SmoothRiemannianMetric I3 L.space.M,
      IsSlabLimit L delta hd g ∧
        IsSolutionOn (flowOn (N := L.space.M)
          (RealTimeInterval.closed (-delta) 0 (by linarith)) g) := by
  obtain ⟨g, hg0, k, hk, hcomp⟩ := h1
  have hlim : IsSlabLimit L delta hd g :=
    isSlabLimit_of_slabComparison L hd hle hk hg0 hcomp
  exact ⟨g, hlim, h2 g hlim⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_terminalBackwardFlow_of_delta then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_terminalBackwardFlow_of_delta"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_terminalBackwardFlow_of_delta ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_terminalBackwardFlow_of_delta

theorem exists_terminalBackwardSlab_of_delta {X : FlowSequence.{u}} {depthBound : ℝ}
    (L : StaticTerminalLimit X depthBound) {delta : ℝ} (hd : 0 < delta)
    (hle : delta ≤ depthBound)
    (h1 : SlabLimitExists L delta) (h2 : SlabLimitIsFlow L delta hd)
    (h3 : SlabLimitSliceGeometry L delta hd) (h4 : SlabLimitCurvatureBound L delta hd) :
    Nonempty (TerminalBackwardSlab L
      (RealTimeInterval.closed (-delta) 0 (by linarith))) := by
  obtain ⟨g, hlim, hflow⟩ := exists_terminalBackwardFlow_of_delta L hd hle h1 h2
  have hgeometry := h3 g hlim
  have hbound := h4 g hlim
  obtain ⟨hg0, k, hk, hconv⟩ := hlim
  refine ⟨{ solution := flowOn (N := L.space.M)
              (RealTimeInterval.closed (-delta) 0 (by linarith)) g
            isSolution := hflow
            terminal := hg0
            subseq := k
            strictMono := hk
            convergence := hconv
            complete := ?_
            nonnegative := ?_
            compact_time_bound := ?_ }⟩
  · exact fun t ht => hgeometry.1 t ht
  · exact fun t ht => hgeometry.2 t ht
  · exact fun a b hab hsub => hbound a b hab hsub

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_terminalBackwardSlab_of_delta then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_terminalBackwardSlab_of_delta"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_terminalBackwardSlab_of_delta ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_terminalBackwardSlab_of_delta

def TerminalSlabAnalyticInputs {X : FlowSequence.{u}} {depthBound : ℝ}
    (L : StaticTerminalLimit X depthBound) : Prop :=
  ∃ delta : ℝ, ∃ hd : 0 < delta, delta ≤ depthBound ∧
    SlabLimitExists L delta ∧ SlabLimitIsFlow L delta hd ∧
      SlabLimitSliceGeometry L delta hd ∧ SlabLimitCurvatureBound L delta hd

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalSlabAnalyticInputs then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalSlabAnalyticInputs"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalSlabAnalyticInputs ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalSlabAnalyticInputs

theorem exists_terminalBackwardSlab {X : FlowSequence.{u}} {depthBound : ℝ}
    (L : StaticTerminalLimit X depthBound) (h : TerminalSlabAnalyticInputs L) :
    ∃ delta : ℝ, ∃ hd : 0 < delta,
      Nonempty (TerminalBackwardSlab L
        (RealTimeInterval.closed (-delta) 0 (by linarith))) := by
  obtain ⟨delta, hd, hle, h1, h2, h3, h4⟩ := h
  exact ⟨delta, hd, exists_terminalBackwardSlab_of_delta L hd hle h1 h2 h3 h4⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_terminalBackwardSlab then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_terminalBackwardSlab"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_terminalBackwardSlab ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_terminalBackwardSlab

theorem terminalJetContinuous_of_terminalBackwardSlab
    {X : FlowSequence.{u}}
    {depthBound : ℝ} {L : StaticTerminalLimit X depthBound} {delta : ℝ}
    (hd : 0 < delta)
    (B : TerminalBackwardSlab L (RealTimeInterval.closed (-delta) 0 (by linarith))) :
    TerminalJetContinuous (I := I3) B.pointed 0 := by
  intro k x v
  exact solution_nablaKRm04_eval_continuousWithinAt_terminal
    B.solution B.isSolution (a := -delta) (b := 0)
    (by linarith) (fun t ht => ht) (fun t ht => ht) k x v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalJetContinuous_of_terminalBackwardSlab then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalJetContinuous_of_terminalBackwardSlab"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalJetContinuous_of_terminalBackwardSlab ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalJetContinuous_of_terminalBackwardSlab

def FlowSequence.ofPointedFlowSeq (Y : PointedFlowSeq.{u, 0, 0} (I := I3)) :
    FlowSequence.{u} where
  interval _ := Y.D
  term i := Y.term i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.ofPointedFlowSeq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.ofPointedFlowSeq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.ofPointedFlowSeq ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.ofPointedFlowSeq

@[simp] theorem FlowSequence.ofPointedFlowSeq_interval
    (Y : PointedFlowSeq.{u, 0, 0} (I := I3)) (i : ℕ) :
    (FlowSequence.ofPointedFlowSeq Y).interval i = Y.D :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.ofPointedFlowSeq_interval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.ofPointedFlowSeq_interval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.ofPointedFlowSeq_interval ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.ofPointedFlowSeq_interval

@[simp] theorem FlowSequence.ofPointedFlowSeq_atTime
    (Y : PointedFlowSeq.{u, 0, 0} (I := I3)) (t : ℝ) :
    (FlowSequence.ofPointedFlowSeq Y).atTime t = Y.atTime t :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.ofPointedFlowSeq_atTime then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.ofPointedFlowSeq_atTime"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.ofPointedFlowSeq_atTime ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.ofPointedFlowSeq_atTime

theorem ancient_carrier_window {a : ℝ} : Set.Icc a 0 ⊆ ancientTimeInterval.carrier :=
  fun _ ht => ht.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ancient_carrier_window then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ancient_carrier_window"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ancient_carrier_window ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ancient_carrier_window

theorem ancient_regular_window {a : ℝ} : Set.Ioo a 0 ⊆ ancientTimeInterval.regular :=
  fun _ ht => ht.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ancient_regular_window then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ancient_regular_window"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ancient_regular_window ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ancient_regular_window

def TerminalSlabBounds {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {Y : NormalizedSequence.{u} eps kappa sigma Phi} (L : TerminalLimit Y)
    (depthBound : ℝ) : Prop :=
  ∀ K : Set L.space.M, IsCompact K → ∀ width : ℝ, 0 < width →
    width < depthBound → ∃ C : ℝ, ∀ᶠ i in Filter.atTop,
      ∀ t ∈ Set.Icc (-width) 0, ∀ y ∈ K,
        PointedFlowData.rmNormSq (Y.term (L.subseq i)) t
          ((L.maps.partialDiffeomorph i) y) ≤ C

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalSlabBounds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalSlabBounds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalSlabBounds ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalSlabBounds

def TerminalLimit.toStatic {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {Y : NormalizedSequence.{u} eps kappa sigma Phi} (L : TerminalLimit Y)
    {depthBound : ℝ} (hdepth : depthBound ≤ 2 * modelDepth eps)
    (hb : TerminalSlabBounds L depthBound) :
    StaticTerminalLimit Y.toFlowSequence depthBound where
  carrier_window i := by
    rw [Y.carrier_eq i]
    have h := Y.depth_buffer i
    exact Set.Icc_subset_Icc (by linarith) le_rfl
  regular_window i := by
    rw [Y.regular_eq i]
    have h := Y.depth_buffer i
    exact Set.Ioo_subset_Ioo (by linarith) le_rfl
  space := L.space
  subseq := L.subseq
  strictMono := L.strictMono
  maps := L.maps
  converges := L.converges
  canonical_domains := L.canonical_domains
  capture := L.capture
  precompact := L.precompact
  connected_domains := L.connected_domains
  nested := L.nested
  connected := L.connected
  complete := L.complete
  nonnegative := L.nonnegative
  slab_bounds := hb

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalLimit.toStatic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalLimit.toStatic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalLimit.toStatic ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalLimit.toStatic

def TerminalBackwardSlab.toBackwardExtension {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {Y : NormalizedSequence.{u} eps kappa sigma Phi} {L : TerminalLimit Y}
    {depthBound : ℝ} {hdepth : depthBound ≤ 2 * modelDepth eps}
    {hb : TerminalSlabBounds L depthBound} {D : RealTimeInterval}
    (B : TerminalBackwardSlab (L.toStatic hdepth hb) D) : BackwardExtension L D where
  solution := B.solution
  isSolution := B.isSolution
  terminal := B.terminal
  subseq := B.subseq
  strictMono := B.strictMono
  convergence := B.convergence
  complete := B.complete
  nonnegative := B.nonnegative
  compact_time_bound := B.compact_time_bound

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalBackwardSlab.toBackwardExtension then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalBackwardSlab.toBackwardExtension"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalBackwardSlab.toBackwardExtension ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalBackwardSlab.toBackwardExtension

theorem first_backward_slab_of_terminal {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {Y : NormalizedSequence.{u} eps kappa sigma Phi} (L : TerminalLimit Y)
    {depthBound : ℝ} (hdepth : depthBound ≤ 2 * modelDepth eps)
    (hb : TerminalSlabBounds L depthBound)
    (h : TerminalSlabAnalyticInputs (L.toStatic hdepth hb)) :
    ∃ delta : ℝ, ∃ hd : 0 < delta,
      Nonempty (BackwardExtension L
        (RealTimeInterval.closed (-delta) 0 (by linarith))) := by
  obtain ⟨delta, hd, hslab⟩ := exists_terminalBackwardSlab (L.toStatic hdepth hb) h
  exact ⟨delta, hd, ⟨TerminalBackwardSlab.toBackwardExtension hslab.some⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.first_backward_slab_of_terminal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.first_backward_slab_of_terminal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.first_backward_slab_of_terminal ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.first_backward_slab_of_terminal

def TerminalLimitSlabInputs {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) (L : TerminalLimit X) : Prop :=
  ∃ (depthBound : ℝ) (hdepth : depthBound ≤ 2 * modelDepth eps)
    (hb : TerminalSlabBounds L depthBound),
    0 < depthBound ∧ TerminalSlabAnalyticInputs (L.toStatic hdepth hb)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalLimitSlabInputs then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalLimitSlabInputs"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalLimitSlabInputs ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalLimitSlabInputs

theorem first_backward_slab_of_terminal_limit_slab_inputs {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (h : ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ (X : NormalizedSequence.{u} eps kappa sigma Phi) (L : TerminalLimit X),
        TerminalLimitSlabInputs X L) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ (X : NormalizedSequence.{u} eps kappa sigma Phi) (L : TerminalLimit X),
        ∃ delta : ℝ, ∃ hd : 0 < delta,
          Nonempty (BackwardExtension L (RealTimeInterval.closed (-delta) 0 (by linarith))) := by
  obtain ⟨epsStar, hpos, hI⟩ := h
  refine ⟨epsStar, hpos, fun eps heps hle X L => ?_⟩
  obtain ⟨depthBound, hdepth, hb, _hd0, han⟩ := hI eps heps hle X L
  exact first_backward_slab_of_terminal L hdepth hb han

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.first_backward_slab_of_terminal_limit_slab_inputs then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.first_backward_slab_of_terminal_limit_slab_inputs"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.first_backward_slab_of_terminal_limit_slab_inputs ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.first_backward_slab_of_terminal_limit_slab_inputs

theorem metricSourceCapture_of_metric_lower_crossModel
    {X : PointedRiemannianSeq.{u, 0, 0} I3} {P : PointedRiemannianManifold.{u, 0, 0} I3}
    {f : ℕ → ℕ} (F : PointedRiemannianConvergenceMaps X P f)
    (hcomplete : MetricComplete P) {L : ℝ} (hL : 0 < L)
    (hlower : ∀ R : ℝ, 0 < R → ∀ᶠ i in Filter.atTop,
      riemannianClosedBallOf (I := I3) P.metric P.basepoint R ⊆
        (F.partialDiffeomorph i).source ∧
      ∀ y ∈ riemannianClosedBallOf (I := I3) P.metric P.basepoint R,
        ∀ v : TangentSpace I3 y,
          P.metric.inner y v v ≤ L ^ 2 * (X.obj (f i)).metric.inner
            (F.partialDiffeomorph i y)
            (mfderiv I3 I3 (F.partialDiffeomorph i) y v)
            (mfderiv I3 I3 (F.partialDiffeomorph i) y v)) :
    MetricSourceCapture F := by
  have hrs : RiemannianMetricComplete (I := I3) P.metric :=
    ⟨MetricComplete.complete P hcomplete⟩
  intro r hr
  have hR : 0 < L * r + 1 := by positivity
  have hrr : r ≤ (L * r + 1) / L := by
    rw [le_div_iff₀ hL]
    linarith [hr.le, hL]
  have hK : IsCompact
      (riemannianClosedBallOf (I := I3) P.metric P.basepoint (L * r + 1)) :=
    RiemannianMetricComplete.closedEBall_isCompact hrs P.basepoint (L * r + 1)
  filter_upwards [hlower (L * r + 1) hR] with i hi
  obtain ⟨hsrc, hbd⟩ := hi
  have hcap := ball_subset_image_of_metric_lower_crossModel (J := I3) (I := I3)
    P.metric ((X.obj (f i)).metric) (F.partialDiffeomorph i) P.basepoint hR hL hK hsrc hbd
  have hbase : (F.partialDiffeomorph i) P.basepoint = (X.obj (f i)).basepoint :=
    F.basepoint_map i
  intro z hz
  have hz' : z ∈ riemannianBallOf (I := I3) ((X.obj (f i)).metric)
      ((F.partialDiffeomorph i) P.basepoint) ((L * r + 1) / L) := by
    rw [hbase]
    exact riemannianBallOf_mono _ _ hrr hz
  obtain ⟨w, hw, hwz⟩ := hcap hz'
  exact ⟨w, hsrc hw, hwz⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.metricSourceCapture_of_metric_lower_crossModel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.metricSourceCapture_of_metric_lower_crossModel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.metricSourceCapture_of_metric_lower_crossModel ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.metricSourceCapture_of_metric_lower_crossModel

theorem isCompact_closure_source_of_subset_closedBall
    {X : PointedRiemannianSeq.{u, 0, 0} I3} {P : PointedRiemannianManifold.{u, 0, 0} I3}
    {f : ℕ → ℕ} (F : PointedRiemannianConvergenceMaps X P f)
    (hcomplete : MetricComplete P)
    (hbounded : ∀ i, ∃ R : ℝ,
      (F.partialDiffeomorph i).source ⊆
        riemannianClosedBallOf (I := I3) P.metric P.basepoint R) :
    ∀ i, IsCompact (closure (F.partialDiffeomorph i).source) := by
  have hrs : RiemannianMetricComplete (I := I3) P.metric :=
    ⟨MetricComplete.complete P hcomplete⟩
  intro i
  obtain ⟨R, hR⟩ := hbounded i
  have hK := RiemannianMetricComplete.closedEBall_isCompact hrs P.basepoint R
  exact IsCompact.of_isClosed_subset hK isClosed_closure
    ((closure_mono hR).trans (le_of_eq hK.isClosed.closure_eq))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.isCompact_closure_source_of_subset_closedBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.isCompact_closure_source_of_subset_closedBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.isCompact_closure_source_of_subset_closedBall ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.isCompact_closure_source_of_subset_closedBall

theorem metricScalarAt_limit_le_of_eventually_le
    {X : PointedRiemannianSeq.{u, 0, 0} I3} {P : PointedRiemannianManifold.{u, 0, 0} I3}
    {f : ℕ → ℕ} (F : PointedRiemannianConvergenceMaps X P f)
    (conv : MetricConvergenceData F)
    (hcanonical : ∀ k, conv.domain k =
      CanonicalMetricCompactness.canonicalSourceData F k)
    (C : ℝ) (h : ∀ x : P.M, ∀ᶠ i in Filter.atTop,
      metricScalarAt (I := I3) (X.obj (f i)).metric (F.partialDiffeomorph i x) ≤ C) :
    ∀ x : P.M, metricScalarAt (I := I3) P.metric x ≤ C :=
  fun x => le_of_tendsto
    (DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalar_tendsto_of_metricCG_canonical_domains
      (I := I3) (X := X) (L := P) (subseq := f) (Phi := F) conv hcanonical x)
    (h x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.metricScalarAt_limit_le_of_eventually_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.metricScalarAt_limit_le_of_eventually_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.metricScalarAt_limit_le_of_eventually_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.metricScalarAt_limit_le_of_eventually_le

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
