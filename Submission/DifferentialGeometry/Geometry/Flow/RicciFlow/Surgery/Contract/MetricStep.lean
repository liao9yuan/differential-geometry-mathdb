import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FiniteHistory
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoff
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.Metric
import Submission.DifferentialGeometry.Geometry.Metric.Sphere.Round.Metric
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.Defs
import Submission.DifferentialGeometry.Geometry.Metric.Distance.Ball
import Submission.DifferentialGeometry.Geometry.Metric.CurveSpeedCalculus
import Submission.DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperator.Metric
import Submission.DifferentialGeometry.Geometry.Operator.Laplacian.Basic
import Submission.DifferentialGeometry.Geometry.Operator.Gradient.NormSquared
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Invariance
import Submission.DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Composition
import Submission.DifferentialGeometry.Analysis.TimeInterval
import Mathlib.Data.ENNReal.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Topology.Covering.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Topology _root_.Filter
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open _root_.Submission.DifferentialGeometry (SmoothRiemannianMetric)

universe u

def curvatureNormSq {M : Type u} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    (g : SmoothRiemannianMetric ThreeModel M) (x : M)
    (A : DifferentialGeometry.Geometry.Curvature.Tensor04At (I := ThreeModel) (M := M) x) : ℝ :=
  DifferentialGeometry.Tensor0SBundle.normSq0S (I := ThreeModel) (M := M) g x 4 A

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.curvatureNormSq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.curvatureNormSq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.curvatureNormSq ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.curvatureNormSq

abbrev ModelBall (L : ℝ) : TopologicalSpace.Opens ThreeSpace :=
  ⟨Metric.ball (0 : ThreeSpace) L, Metric.isOpen_ball⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ModelBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ModelBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ModelBall ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ModelBall

noncomputable def riemannianBallVolume {M : Type u} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric ThreeModel M) (p : M) (r : ℝ) : ℝ :=
  ((DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := ThreeModel) (M := M) g)
    (DifferentialGeometry.riemannianBallOf (I := ThreeModel) g p r)).toReal

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.riemannianBallVolume then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.riemannianBallVolume"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.riemannianBallVolume ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.riemannianBallVolume

noncomputable def reducedAction {M : Type u} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    (g : ℝ → SmoothRiemannianMetric ThreeModel M) (t₀ : ℝ) (τ : ℝ) (γ : ℝ → M) : ℝ :=
  ∫ s in (0 : ℝ)..τ,
    Real.sqrt s *
      (metricScalarAt (g (t₀ - s)) (γ s) +
        DifferentialGeometry.Geometry.riemannianCurveSpeed (g (t₀ - s)) γ s ^ 2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.reducedAction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.reducedAction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.reducedAction ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.reducedAction

noncomputable def reducedLength {M : Type u} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    (g : ℝ → SmoothRiemannianMetric ThreeModel M) (t₀ : ℝ)
    (admissible : (ℝ → M) → Prop) (p : M) (τ : ℝ) (x : M) : ℝ :=
  _root_.InfSet.sInf {r : ℝ | ∃ γ : ℝ → M,
    admissible γ ∧ γ 0 = p ∧ γ τ = x ∧ reducedAction g t₀ τ γ = r}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.reducedLength then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.reducedLength"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.reducedLength ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.reducedLength

noncomputable def reducedVolume {M : Type u} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    [T2Space M] [SigmaCompactSpace M]
    (g : ℝ → SmoothRiemannianMetric ThreeModel M) (t₀ : ℝ)
    (admissible : (ℝ → M) → Prop) (p : M) (τ : ℝ) (V : Set M) : ℝ≥0∞ :=
  ∫⁻ x in V, ENNReal.ofReal
    ((4 * Real.pi * τ) ^ (-(3 / 2 : ℝ)) *
      Real.exp (-(reducedLength g t₀ admissible p τ x) / (2 * Real.sqrt τ)))
    ∂(DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := ThreeModel) (M := M)
      (g (t₀ - τ)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.reducedVolume then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.reducedVolume"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.reducedVolume ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.reducedVolume

theorem modelBall_mono {L L' : ℝ} (h : L' ≤ L) : ModelBall L' ≤ ModelBall L :=
  Metric.ball_subset_ball h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.modelBall_mono then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.modelBall_mono"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.modelBall_mono ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.modelBall_mono

def localStabilityInitialJetHypothesis
    (L : ℕ → ℝ) (v : ℕ → ℝ) (hv : ∀ i, 0 < v i)
    (γ : SmoothRiemannianMetric ThreeModel ThreeSpace)
    (ℓ : (i : ℕ) → SolutionOn (I := ThreeModel) (M := ↥(ModelBall (L i)))
      (RealTimeInterval.closed (0 : ℝ) (v i) (le_of_lt (hv i)))) : Prop :=
  ∀ A : Set ThreeSpace, IsCompact A → ∀ p : ℕ,
    _root_.Filter.Tendsto (fun i : ℕ => metricDerivNormSupOn (Subtype.val ⁻¹' A) p ((ℓ i).base.metric 0)
      (γ.restrictOpen (ModelBall (L i))) (γ.restrictOpen (ModelBall (L i)))) _root_.Filter.atTop (𝓝 0)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.localStabilityInitialJetHypothesis then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.localStabilityInitialJetHypothesis"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.localStabilityInitialJetHypothesis ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.localStabilityInitialJetHypothesis

def localStabilityCauchyConclusion
    (L : ℕ → ℝ) (v : ℕ → ℝ) (hv : ∀ i, 0 < v i)
    (γ : SmoothRiemannianMetric ThreeModel ThreeSpace)
    (ℓ : (i : ℕ) → SolutionOn (I := ThreeModel) (M := ↥(ModelBall (L i)))
      (RealTimeInterval.closed (0 : ℝ) (v i) (le_of_lt (hv i)))) : Prop :=
  ∀ A : Set ThreeSpace, IsCompact A → ∀ m : ℕ, 4 ≤ m → ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ i j : ℕ, N ≤ i → N ≤ j → ∀ r : ℝ, ∀ hr : r ≤ _root_.Min.min (L i) (L j),
      ∀ u ∈ Set.Icc (0 : ℝ) (_root_.Min.min (v i) (v j)),
        metricDerivNormSupOn (I := ThreeModel) (M := ↥(ModelBall r))
          (Subtype.val ⁻¹' A) m
          (((ℓ i).base.metric u).restrictOpenOfSubset
            (modelBall_mono (le_trans hr (min_le_left (L i) (L j)))))
          (((ℓ j).base.metric u).restrictOpenOfSubset
            (modelBall_mono (le_trans hr (min_le_right (L i) (L j)))))
          ((γ.restrictOpen (ModelBall r)))
        ≤ ε

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.localStabilityCauchyConclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.localStabilityCauchyConclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.localStabilityCauchyConclusion ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.localStabilityCauchyConclusion

def localStabilityLimitFlowConclusion
    (L : ℕ → ℝ) (v : ℕ → ℝ) (hv : ∀ i, 0 < v i)
    (γ : SmoothRiemannianMetric ThreeModel ThreeSpace)
    (ℓ : (i : ℕ) → SolutionOn (I := ThreeModel) (M := ↥(ModelBall (L i)))
      (RealTimeInterval.closed (0 : ℝ) (v i) (le_of_lt (hv i)))) : Prop :=
  ∃ γLim : ℝ → SmoothRiemannianMetric ThreeModel ThreeSpace,
    γLim 0 = γ ∧
      ∀ A : Set ThreeSpace, IsCompact A → ∀ m : ℕ, 4 ≤ m → ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, ∀ i j : ℕ, N ≤ i → N ≤ j → ∀ r : ℝ,
          ∀ hr : r ≤ _root_.Min.min (L i) (L j),
          ∀ u ∈ Set.Icc (0 : ℝ) (_root_.Min.min (v i) (v j)), ∀ a : ℕ, a ≤ m →
            ∀ x : ↥(ModelBall r), (x : ThreeSpace) ∈ A →
              metricDerivNorm (I := ThreeModel) (M := ↥(ModelBall r)) a
                (((ℓ i).base.metric u).restrictOpenOfSubset
                  (modelBall_mono (le_trans hr (min_le_left (L i) (L j)))))
                ((γLim u).restrictOpen (ModelBall r))
                ((γ.restrictOpen (ModelBall r))) x ≤ ε

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.localStabilityLimitFlowConclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.localStabilityLimitFlowConclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.localStabilityLimitFlowConclusion ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.localStabilityLimitFlowConclusion

def isLocalStabilityInput : Prop :=
  ∀ θ : ℝ, 0 < θ → θ < 1 → ∀ K : ℝ, 0 < K →
    ∀ (L : ℕ → ℝ) (_hLpos : ∀ i, 0 < L i) (_hLtop : _root_.Filter.Tendsto L _root_.Filter.atTop _root_.Filter.atTop)
      (v : ℕ → ℝ) (hv : ∀ i, 0 < v i) (_hvθ : ∀ i, v i ≤ θ)
      (γ : SmoothRiemannianMetric ThreeModel ThreeSpace)
      (ℓ : (i : ℕ) → SolutionOn (I := ThreeModel) (M := ↥(ModelBall (L i)))
        (RealTimeInterval.closed (0 : ℝ) (v i) (le_of_lt (hv i)))),
      (∀ i, DifferentialGeometry.PDE.RicciFlow.IsSolutionOn (ℓ i)) →
      (∀ i, ∀ x : ↥(ModelBall (L i)),
        curvatureNormSq ((ℓ i).base.metric (v i)) x
          (DifferentialGeometry.Geometry.Curvature.metricRm04At (I := ThreeModel)
            (M := ↥(ModelBall (L i))) ((ℓ i).base.metric (v i)) x) ≤ K ^ 2) →
      localStabilityInitialJetHypothesis L v hv γ ℓ →
      localStabilityCauchyConclusion L v hv γ ℓ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isLocalStabilityInput then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isLocalStabilityInput"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isLocalStabilityInput ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isLocalStabilityInput

structure StandardCapModel where
  solution : SmoothRiemannianMetric ThreeModel ThreeSpace
  initial : solution = standardCapMetric
  tip : ThreeSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.StandardCapModel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.StandardCapModel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.StandardCapModel ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.StandardCapModel

structure CapClass where
  horizon : ℝ
  horizon_pos : 0 < horizon
  initialParameter : ℝ
  initialParameter_pos : 0 < initialParameter
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  comparisonConstant : ℝ
  comparisonConstant_pos : 0 < comparisonConstant
  volumeConstant : ℝ
  volumeConstant_pos : 0 < volumeConstant
  scaleLower : ℝ
  scaleLower_pos : 0 < scaleLower
  scaleUpper : ℝ
  scale_lt : scaleLower < scaleUpper

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CapClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CapClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CapClass ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CapClass

structure OldData where
  horizon : ℝ
  horizon_pos : 0 < horizon
  initialParameter : ℝ
  initialParameter_pos : 0 < initialParameter
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  comparisonConstant : ℝ
  comparisonConstant_pos : 0 < comparisonConstant
  volumeConstant : ℝ
  volumeConstant_pos : 0 < volumeConstant
  scaleLower : ℝ
  scaleLower_pos : 0 < scaleLower
  noncollapsing : ℝ
  noncollapsing_pos : 0 < noncollapsing
  olderLength : ℝ
  olderLength_pos : 0 < olderLength
  energyBound : ℝ
  olderLength_le_energy : olderLength ≤ energyBound

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OldData then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OldData"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OldData ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OldData

structure PreparedCapSeed (H : ObservedHistory.{u}) (L : ℝ) (N : ℕ) (ζ : ℝ) where
  chart : PartialDiffeomorph ThreeModel ThreeModel ThreeSpace (H.stage 0).Carrier ∞
  ball_subset_source : Metric.ball (0 : ThreeSpace) L ⊆ chart.source
  scale : ℝ
  scale_pos : 0 < scale
  order : ℕ
  order_lower : N ≤ order
  accuracy_pos : 0 < ζ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.PreparedCapSeed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.PreparedCapSeed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.PreparedCapSeed ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.PreparedCapSeed

structure BackwardRealization {M : Type u} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    (metric : ℝ → SmoothRiemannianMetric ThreeModel M) (t s : ℝ) where
  chart : PartialDiffeomorph ThreeModel ThreeModel ThreeSpace M ∞
  zero_mem_source : (0 : ThreeSpace) ∈ chart.source
  ball_subset_source : Metric.ball (0 : ThreeSpace) (4 * s) ⊆ chart.source
  curvature_bound : ∀ u ∈ _root_.Set.Icc (t - 4 * s ^ 2) t,
    ∀ x ∈ Metric.ball (0 : ThreeSpace) (4 * s),
      curvatureNormSq (metric u) (chart x)
        (DifferentialGeometry.Geometry.Curvature.metricRm04At (I := ThreeModel)
          (M := M) (metric u) (chart x)) ≤ (s ^ 2)⁻¹

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardRealization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardRealization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardRealization ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardRealization

inductive TrackedFace where
  | incoming
  | observed

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TrackedFace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TrackedFace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TrackedFace ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TrackedFace

structure TrackedChart (P : OrientedThreeStage.{u}) (G : ℝ → P.Metric)
    (J : PartialDiffeomorph ThreeModel ThreeModel ThreeSpace P.Carrier ∞) (q L K : ℝ) where
  time : ℝ
  time_nonneg : 0 ≤ time
  time_le : time ≤ q
  face : TrackedFace
  flow : ℝ → ThreeSpace → P.Carrier
  flow_zero : Set.EqOn (flow 0) ⇑J (Metric.ball (0 : ThreeSpace) L)
  flow_injective : ∀ s ∈ _root_.Set.Icc (0 : ℝ) time, Function.Injective (flow s)
  domain : Set ThreeSpace
  domain_open : IsOpen domain
  wide : ∀ x : ThreeSpace, ‖x‖ ≤ L → x ∈ domain
  normalized_metric : ℝ → SmoothRiemannianMetric ThreeModel ThreeSpace
  normalized_metric_eq : ∀ s ∈ _root_.Set.Icc (0 : ℝ) time,
    ∀ (x : ThreeSpace) (V W : TangentSpace ThreeModel x),
      (normalized_metric s).inner x V W = (q - s)⁻¹ *
        (G (q - s)).inner (flow s x)
          (mfderiv ThreeModel ThreeModel (flow s) x V)
          (mfderiv ThreeModel ThreeModel (flow s) x W)
  curvature_bound : ∀ s ∈ _root_.Set.Icc (0 : ℝ) time, ∀ x : ThreeSpace, ‖x‖ ≤ L →
    curvatureNormSq (normalized_metric s) x
      (DifferentialGeometry.Geometry.Curvature.metricRm04At (I := ThreeModel)
        (M := ThreeSpace) (normalized_metric s) x) ≤ K ^ 2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TrackedChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TrackedChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TrackedChart ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TrackedChart

structure AdmissibleDatum (c : CapClass) where
  history : ObservedHistory.{u}
  eventCount_pos : 0 < history.eventCount
  horizon_le : history.horizon ≤ c.horizon
  ambientMetric : ℝ → (history.stage 0).Metric
  precision : ℝ
  precision_pos : 0 < precision
  scale : ℝ
  scale_pos : 0 < scale

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.AdmissibleDatum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.AdmissibleDatum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.AdmissibleDatum ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.AdmissibleDatum

def ProtectedSurvives {c : CapClass} (D : AdmissibleDatum.{u} c) (a : ℝ)
    (i : Fin D.history.eventCount) : Prop :=
  Nonempty (BackwardRealization
    (fun u => (D.history.event i).incoming.flow.base.metric u) (D.history.time i.succ) (a / 4))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ProtectedSurvives then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ProtectedSurvives"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ProtectedSurvives ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ProtectedSurvives

def IsLossEvent {c : CapClass} (D : AdmissibleDatum.{u} c) (a : ℝ)
    (i : Fin D.history.eventCount) : Prop :=
  ¬ ProtectedSurvives D a i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.IsLossEvent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.IsLossEvent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.IsLossEvent ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.IsLossEvent

def IsStoppingFace {c : CapClass} (D : AdmissibleDatum.{u} c) (a θ : ℝ) (T : ℝ) : Prop :=
  T ∈ _root_.Set.Icc a (a + θ / D.scale) ∧
    ((∃ i : Fin D.history.eventCount, IsLossEvent D a i ∧ T = D.history.time i.succ ∧
        ∀ j : Fin D.history.eventCount, IsLossEvent D a j → a < D.history.time j.succ →
          T ≤ D.history.time j.succ) ∨
      ((¬ ∃ i : Fin D.history.eventCount, IsLossEvent D a i ∧ a < D.history.time i.succ ∧
          D.history.time i.succ ≤ a + θ / D.scale) ∧
        T = _root_.Min.min D.history.horizon (a + θ / D.scale)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.IsStoppingFace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.IsStoppingFace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.IsStoppingFace ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.IsStoppingFace

def isBufferedControlInput : Prop :=
  ∀ c : CapClass, ∀ θ : ℝ, 0 < θ → θ < 1 →
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ a : ℝ, 1 < a → ∀ L : ℝ, a + 3 < L →
        ∃ L₀ : ℝ, L + 2 < L₀ ∧ ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∃ ζ₀ : ℝ, 0 < ζ₀ ∧
          ∃ δ₀ : ℝ, 0 < δ₀ ∧
            ∀ D : AdmissibleDatum.{u} c, D.precision ≤ δ₀ →
              ∀ seed : PreparedCapSeed D.history L₀ N₀ ζ₀,
                ∀ T : ℝ, IsStoppingFace D a θ T →
                  ∃ C : TrackedChart (D.history.stage 0) D.ambientMetric seed.chart T L K,
                    ((∃ i : Fin D.history.eventCount, IsLossEvent D a i ∧
                        T = D.history.time i.succ) → C.face = TrackedFace.incoming) ∧
                    ((¬ ∃ i : Fin D.history.eventCount, IsLossEvent D a i ∧
                        T = D.history.time i.succ) → C.face = TrackedFace.observed) ∧
                    Nonempty (BackwardRealization (fun u => D.ambientMetric u) T (L / 4))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isBufferedControlInput then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isBufferedControlInput"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isBufferedControlInput ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isBufferedControlInput

structure CapEscapeModel where
  horizon : ℝ
  horizon_pos : 0 < horizon
  radius : ℝ
  radius_pos : 0 < radius
  tolerance : ℝ
  tolerance_pos : 0 < tolerance
  action : ℝ → (ℝ → ThreeSpace) → ℝ≥0∞

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CapEscapeModel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CapEscapeModel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CapEscapeModel ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CapEscapeModel

def isCapEscapeCostBarrier (C : CapEscapeModel) : Prop :=
  ∀ H : ℝ, 0 < H →
    ∃ A : ℝ, A < C.radius ∧ ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧
      ∀ v : ℝ, 0 < v → v ≤ θ →
      ∀ ξ : ℝ → ThreeSpace,
        (∀ u ∈ _root_.Set.Icc 0 v, _root_.Dist.dist (ξ u) (0 : ThreeSpace) ≤ C.radius) →
        ENNReal.ofReal H < C.action v ξ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isCapEscapeCostBarrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isCapEscapeCostBarrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isCapEscapeCostBarrier ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isCapEscapeCostBarrier

structure CapEscapeTransfer (H : ObservedHistory.{u}) where
  insertionTime : ℝ
  duration : ℝ
  duration_pos : 0 < duration
  depth : ℝ
  depth_pos : 0 < depth
  comparison : CapEscapeModel
  barrier : isCapEscapeCostBarrier comparison

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CapEscapeTransfer then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CapEscapeTransfer"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CapEscapeTransfer ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CapEscapeTransfer

structure VariationalStrip (H : ObservedHistory.{u}) where
  pole : (H.stage 0).Carrier
  start : ℝ
  finish : ℝ
  start_nonneg : 0 ≤ start
  finish_le_horizon : finish ≤ H.horizon
  start_lt_finish : start < finish
  radius : ℝ
  radius_pos : 0 < radius
  metricAt : ℝ → (H.stage 0).Metric
  admissible : (ℝ → (H.stage 0).Carrier) → Prop
  regular : (ℝ → (H.stage 0).Carrier) → Prop
  regular_admissible : ∀ γ, regular γ → admissible γ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.VariationalStrip then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.VariationalStrip"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.VariationalStrip ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.VariationalStrip

namespace VariationalStrip

noncomputable def reducedLength {H : ObservedHistory.{u}} (S : VariationalStrip H) (u : ℝ)
    (x : (H.stage 0).Carrier) : ℝ :=
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.reducedLength
    S.metricAt S.finish S.admissible S.pole (S.finish - u) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.VariationalStrip.reducedLength then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.VariationalStrip.reducedLength"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.VariationalStrip.reducedLength ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.VariationalStrip.reducedLength

end VariationalStrip

def isSurgeryVariationalInput : Prop :=
  ∀ (H : ObservedHistory.{u}) (S : VariationalStrip H),
    (∀ u ∈ _root_.Set.Ioo S.start S.finish,
      LowerSemicontinuousOn (fun x => S.reducedLength u x)
        (_root_.Set.univ : Set (H.stage 0).Carrier) ∧
      (∃ x : (H.stage 0).Carrier,
        IsLeast (_root_.Set.range (fun y => S.reducedLength u y)) (S.reducedLength u x)) ∧
      (∀ x : (H.stage 0).Carrier,
        IsLeast (_root_.Set.range (fun y => S.reducedLength u y)) (S.reducedLength u x) →
          ∃ γ : ℝ → (H.stage 0).Carrier,
            S.admissible γ ∧ γ 0 = S.pole ∧ γ (S.finish - u) = x ∧
              reducedAction S.metricAt S.finish (S.finish - u) γ = S.reducedLength u x)) ∧
    (∀ u ∈ _root_.Set.Ioo S.start S.finish, ∀ x : (H.stage 0).Carrier,
      IsLeast (_root_.Set.range (fun y => S.reducedLength u y)) (S.reducedLength u x) →
      (∀ γ : ℝ → (H.stage 0).Carrier, S.admissible γ → γ 0 = S.pole →
        γ (S.finish - u) = x →
        reducedAction S.metricAt S.finish (S.finish - u) γ = S.reducedLength u x →
        S.regular γ) →
      ∀ η : ℝ, 0 < η →
        ∃ (U : TopologicalSpace.Opens (H.stage 0).Carrier) (hxU : x ∈ U)
          (F : ℝ → ↥U → ℝ) (hF : ∀ σ : ℝ, ContMDiff ThreeModel 𝓘(ℝ, ℝ) ∞ (F σ)),
          F u ⟨x, hxU⟩ = S.reducedLength u x ∧
          (∀ y : ↥U, y ≠ ⟨x, hxU⟩ →
            F u y < S.reducedLength u (y : (H.stage 0).Carrier)) ∧
          deriv (fun σ : ℝ => F σ ⟨x, hxU⟩) u +
            DifferentialGeometry.Geometry.Operator.ΔG (I := ThreeModel) (M := ↥U)
              ((S.metricAt u).restrictOpen U) (⟨F u, hF u⟩ : C^∞⟮ThreeModel, ↥U; ℝ⟯) ⟨x, hxU⟩
            ≤ 6 + η ∧
          Real.sqrt (DifferentialGeometry.Geometry.Operator.normGradSqFun (I := ThreeModel)
            (M := ↥U) ((S.metricAt u).restrictOpen U) (F u) ⟨x, hxU⟩) ≤ η) ∧
    (∀ u ∈ _root_.Set.Ioo S.start S.finish,
      LowerSemicontinuousWithinAt
        (fun τ : ℝ => _root_.InfSet.sInf (_root_.Set.range (fun x => S.reducedLength (S.finish - τ) x)) - 6 * τ)
        (_root_.Set.Ioo S.start S.finish) (S.finish - u))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isSurgeryVariationalInput then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isSurgeryVariationalInput"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isSurgeryVariationalInput ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isSurgeryVariationalInput

structure JacobianStrip (H : ObservedHistory.{u}) where
  pole : (H.stage 0).Carrier
  start : ℝ
  poleTime : ℝ
  start_nonneg : 0 ≤ start
  start_lt : start < poleTime
  poleTime_le_horizon : poleTime ≤ H.horizon
  radius : ℝ
  radius_pos : 0 < radius
  metricAt : ℝ → (H.stage 0).Metric
  admissible : (ℝ → (H.stage 0).Carrier) → Prop
  regular : (ℝ → (H.stage 0).Carrier) → Prop
  regular_admissible : ∀ γ, regular γ → admissible γ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.JacobianStrip then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.JacobianStrip"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.JacobianStrip ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.JacobianStrip

noncomputable def regularMinimizingSet {H : ObservedHistory.{u}}
    (g : ℝ → (H.stage 0).Metric) (t₀ : ℝ)
    (admissible regular : (ℝ → (H.stage 0).Carrier) → Prop) (p : (H.stage 0).Carrier)
    (τ : ℝ) : Set (H.stage 0).Carrier :=
  {x | ∃ γ : ℝ → (H.stage 0).Carrier,
    admissible γ ∧ regular γ ∧ γ 0 = p ∧ γ τ = x ∧
      reducedAction g t₀ τ γ = reducedLength g t₀ admissible p τ x}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.regularMinimizingSet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.regularMinimizingSet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.regularMinimizingSet ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.regularMinimizingSet

def isJacobianInput : Prop :=
  ∀ _d : OldData, ∃ modul : ℝ → ℝ,
    (∀ v : ℝ, 0 < v → 0 < modul v) ∧ Monotone modul ∧
    (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ v : ℝ, 0 < v → v < δ → modul v < ε) ∧
    ∀ (H : ObservedHistory.{u}) (S : JacobianStrip H) (s : ℝ),
      s ∈ _root_.Set.Ioo S.start S.poleTime → S.radius ^ 2 < S.poleTime - s →
      letI : MeasurableSpace (H.stage 0).Carrier := borel (H.stage 0).Carrier
      ∀ (V : Set (H.stage 0).Carrier), MeasurableSet V →
      V ⊆ regularMinimizingSet S.metricAt S.poleTime S.admissible S.regular S.pole
        (S.poleTime - s) →
      ∀ v : ℝ, 0 < v →
        riemannianBallVolume (S.metricAt S.poleTime) S.pole S.radius < v * S.radius ^ 3 →
          reducedVolume S.metricAt S.poleTime S.admissible S.pole (S.poleTime - s) V ≤
            ENNReal.ofReal (modul v)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isJacobianInput then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isJacobianInput"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isJacobianInput ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isJacobianInput

def isOldTubeInput (d : OldData) : Prop :=
  ∀ ρ : ℝ, 0 < ρ →
    ∃ s : ℝ, 0 < s ∧ s ≤ _root_.Min.min (d.epsilon / 2) (Real.sqrt (d.energyBound / 24)) ∧
      ∃ dOld : ℝ, 0 < dOld ∧
        ∀ (H : ObservedHistory.{u}) (P : CutoffParameters) (i : Fin H.eventCount) (t : ℝ)
          (x : (H.stage i.castSucc).Carrier),
          P.delta t ≤ dOld →
          H.time i.castSucc + (H.time i.succ - H.time i.castSucc) / 3 ≤ t →
          t ≤ H.time i.castSucc + 2 * (H.time i.succ - H.time i.castSucc) / 3 →
          metricScalarAt ((H.event i).incoming.flow.base.metric t) x ≤ ρ →
          Nonempty (BackwardRealization
            (fun u => (H.event i).incoming.flow.base.metric u) t s)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isOldTubeInput then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isOldTubeInput"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isOldTubeInput ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isOldTubeInput

structure EnlargementStrip (H : ObservedHistory.{u}) where
  pole : (H.stage 0).Carrier
  poleTime : ℝ
  poleTime_nonneg : 0 ≤ poleTime
  poleTime_le_horizon : poleTime ≤ H.horizon
  radius : ℝ
  radius_pos : 0 < radius

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.EnlargementStrip then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.EnlargementStrip"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.EnlargementStrip ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.EnlargementStrip

structure SourceGeometry where
  carrier : Type u
  [topology : TopologicalSpace carrier]
  [charts : ChartedSpace ThreeSpace carrier]
  [smooth : IsManifold ThreeModel ∞ carrier]
  metric : SmoothRiemannianMetric ThreeModel carrier

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SourceGeometry then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SourceGeometry"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SourceGeometry ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SourceGeometry

attribute [instance] SourceGeometry.topology SourceGeometry.charts SourceGeometry.smooth

structure SourcePatch {H : ObservedHistory.{u}}
    (S : EnlargementStrip H) where
  geometry : SourceGeometry.{u}
  embedding : geometry.carrier → (H.stage 0).Carrier
  embedding_injective : Function.Injective embedding
  metric_bound : ∀ x : geometry.carrier, ∀ v : TangentSpace ThreeModel x,
    2 * geometry.metric.inner x v v
      ≤ (H.initialMetric 0).inner (embedding x)
        (mfderiv ThreeModel ThreeModel embedding x v)
        (mfderiv ThreeModel ThreeModel embedding x v)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SourcePatch then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SourcePatch"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SourcePatch ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SourcePatch

inductive SourceCause where
  | frontier
  | curvatureContact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SourceCause then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SourceCause"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SourceCause ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SourceCause

structure EnlargementConclusion {H : ObservedHistory.{u}}
    (S : EnlargementStrip H) where
  patch : SourcePatch S
  cause : SourceCause

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.EnlargementConclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.EnlargementConclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.EnlargementConclusion ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.EnlargementConclusion

def isEnlargementInput : Prop :=
  ∀ d : OldData, 0 < d.noncollapsing →
    ∃ α : ℝ, 0 < α ∧ α ≤ 1 / 100 ∧ ∃ sstar : ℝ, 0 < sstar ∧
      sstar ≤ d.epsilon / 2 ∧
        ∀ (H : ObservedHistory.{u}) (S : EnlargementStrip H),
          S.radius < _root_.Min.min (α * d.scaleLower) (sstar / 4) →
          Nonempty (EnlargementConclusion S)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isEnlargementInput then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isEnlargementInput"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isEnlargementInput ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isEnlargementInput

structure RoundCovering (Z : Type u) [TopologicalSpace Z] [ChartedSpace ThreeSpace Z]
    [IsManifold ThreeModel ∞ Z] (k : SmoothRiemannianMetric ThreeModel Z) where
  cover : C(Sphere 3, Z)
  cover_isCoveringMap : IsCoveringMap (cover : Sphere 3 → Z)
  isRound : ∀ x : Z, ∃ e : PartialDiffeomorph (𝓡 3) (𝓡 3) (Sphere 3) Z ∞,
    x ∈ e.target ∧ ∀ y ∈ e.source, ∀ (V W : TangentSpace (𝓡 3) y),
      k.inner (e y) (mfderiv (𝓡 3) (𝓡 3) e y V) (mfderiv (𝓡 3) (𝓡 3) e y W) =
        (DifferentialGeometry.Geometry.roundMetric
          (E := EuclideanSpace ℝ (Fin 4)) (n := 3)).inner y V W

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RoundCovering then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RoundCovering"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RoundCovering ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RoundCovering

def sphereThreeBasePoint : Sphere 3 :=
  ⟨EuclideanSpace.single 0 1, by simp⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereThreeBasePoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereThreeBasePoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereThreeBasePoint ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereThreeBasePoint

def RoundCovering.degree {Z : Type u} [TopologicalSpace Z] [ChartedSpace ThreeSpace Z]
    [IsManifold ThreeModel ∞ Z] {k : SmoothRiemannianMetric ThreeModel Z}
    (C : RoundCovering Z k) : ℕ :=
  (C.cover ⁻¹' {C.cover sphereThreeBasePoint}).ncard

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RoundCovering
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RoundCovering.degree then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RoundCovering.degree"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RoundCovering.degree ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RoundCovering.degree

theorem RoundCovering.degree_eq_one_of_injective {Z : Type u} [TopologicalSpace Z]
    [ChartedSpace ThreeSpace Z] [IsManifold ThreeModel ∞ Z]
    {k : SmoothRiemannianMetric ThreeModel Z} (C : RoundCovering Z k)
    (h : Function.Injective C.cover) : C.degree = 1 := by
  rw [RoundCovering.degree, Set.ncard_eq_one]
  refine ⟨sphereThreeBasePoint, ?_⟩
  apply Set.eq_singleton_iff_unique_mem.mpr
  refine ⟨rfl, ?_⟩
  intro y hy
  exact h hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RoundCovering.degree_eq_one_of_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RoundCovering.degree_eq_one_of_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RoundCovering.degree_eq_one_of_injective ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RoundCovering.degree_eq_one_of_injective

def isRoundDegreeInput : Prop :=
  ∀ _d : OldData, ∃ Nold : ℕ, 1 ≤ Nold ∧
    ∀ (H : ObservedHistory.{u}) (_S : EnlargementStrip H), ∀ Z : Type u,
      ∀ [TopologicalSpace Z] [ChartedSpace ThreeSpace Z] [IsManifold ThreeModel ∞ Z],
        ∀ k : SmoothRiemannianMetric ThreeModel Z,
          Nonempty (RoundCovering Z k) →
            ∃ C : RoundCovering Z k, 1 ≤ C.degree ∧ C.degree ≤ Nold

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isRoundDegreeInput then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isRoundDegreeInput"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isRoundDegreeInput ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isRoundDegreeInput

def isCommonLocalRealization : Prop :=
  isLocalStabilityInput ∧ isBufferedControlInput.{u} ∧ isSurgeryVariationalInput.{u} ∧
    isJacobianInput.{u} ∧ (∃ d : OldData, isOldTubeInput.{u} d) ∧
      isEnlargementInput.{u} ∧ isRoundDegreeInput.{u}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isCommonLocalRealization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isCommonLocalRealization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isCommonLocalRealization ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isCommonLocalRealization

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
