import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.W.Functional
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.RicciNorm
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Family.Metric
import Submission.DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

noncomputable section

universe u uE uH

open _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry.Tensor0SBundle _root_.MeasureTheory
open scoped _root_.Manifold _root_.ContDiff _root_.ENNReal

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M]
variable [T2Space M] [SigmaCompactSpace M]
variable {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
variable {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}

structure FlowMetricBall (S : SolutionOn (I := I) (M := M) D)
    (time : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.FlowTime D) where
  center : M
  radius : Real
  radius_pos : 0 < radius

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall

namespace FlowMetricBall

variable {S : SolutionOn (I := I) (M := M) D}
variable {time : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.FlowTime D}
variable {time : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.FlowTime D}

def setAt (B : FlowMetricBall S time) (t : Real) : Set M :=
  {x : M | DifferentialGeometry.riemannianEDistOf
    (I := I) (S.base.metric t) B.center x < ENNReal.ofReal B.radius}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.setAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.setAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.setAt ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.setAt

def set (B : FlowMetricBall S time) : Set M :=
  B.setAt (time : Real)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.set then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.set"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.set ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.set

def volume (B : FlowMetricBall S time) : ℝ≥0∞ :=
  DifferentialGeometry.Integral.Measure.volumeMeasureOn
    (I := I) (M := M) S.family time B.set

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.volume then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.volume"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.volume ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.volume

def rmNormSq (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M) : Real :=
  Tensor0SBundle.normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.rmNormSq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.rmNormSq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.rmNormSq ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.rmNormSq

def IsRmControlled (B : FlowMetricBall S time) : Prop :=
  Set.Icc ((time : Real) - B.radius ^ 2) (time : Real) ⊆ D.carrier ∧
    ∀ t ∈ Set.Icc ((time : Real) - B.radius ^ 2) (time : Real), ∀ x ∈ B.setAt t,
      B.radius ^ 4 * rmNormSq S t x ≤ 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.IsRmControlled then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.IsRmControlled"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.IsRmControlled ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.IsRmControlled

def IsKappaNoncollapsed (kappa : Real) (B : FlowMetricBall S time) : Prop :=
  0 < kappa ∧
    ENNReal.ofReal kappa * ENNReal.ofReal B.radius ^ Module.finrank Real E ≤ B.volume

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.IsKappaNoncollapsed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.IsKappaNoncollapsed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.IsKappaNoncollapsed ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.IsKappaNoncollapsed

def Nested (small large : FlowMetricBall S time) : Prop :=
  small.set ⊆ large.set

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.Nested then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.Nested"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.Nested ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.Nested

theorem volume_mono {small large : FlowMetricBall S time} (h : small.Nested large) :
    small.volume ≤ large.volume := by
  unfold volume
  exact _root_.MeasureTheory.measure_mono h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.volume_mono then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.volume_mono"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.volume_mono ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.volume_mono

end FlowMetricBall

def KappaNoncollapsedBelowScale
    (S : SolutionOn (I := I) (M := M) D) (kappa rho : Real) : Prop :=
  0 < rho ∧ ∀ (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.FlowTime D)
    (B : FlowMetricBall S t), B.radius ≤ rho →
    B.IsRmControlled → B.IsKappaNoncollapsed kappa

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaNoncollapsedBelowScale then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaNoncollapsedBelowScale"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaNoncollapsedBelowScale ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaNoncollapsedBelowScale

def NoLocalCollapsing
    (S : SolutionOn (I := I) (M := M) D) (rho : Real) : Prop :=
  ∃ kappa : Real, 0 < kappa ∧ KappaNoncollapsedBelowScale S kappa rho

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.NoLocalCollapsing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.NoLocalCollapsing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.NoLocalCollapsing ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.NoLocalCollapsing

end

end DifferentialGeometry.PDE.RicciFlow.Perelman
