import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.DirectedSubsequence.Existence
import Submission.DifferentialGeometry.Topology.Exhaustion
import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Limit.Metric.Convergence
import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Limit.Metric.CompatibleChainLimits
import Submission.DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Composition
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Bounds
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Restriction
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Self

import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Subsequence
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Pullback
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.Metric.UniformEquivalence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable [I.Boundaryless]
variable [NeZero (Module.finrank ℝ E)]

def HasLimitReferenceMetric
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    {Phi : PointedRiemannianConvergenceMaps (I := I) X L subseq}
    (C : PointedRiemannianConverges (I := I) X L subseq Phi) : Prop :=
  forall k : Nat,
    let D := C.metrics.domain k
    letI : TopologicalSpace (MetricSourceDomain (I := I) Phi k) := D.topology
    letI : ChartedSpace H (MetricSourceDomain (I := I) Phi k) := D.charted
    letI : IsManifold I ∞ (MetricSourceDomain (I := I) Phi k) := D.smooth
    D.referenceMetric = D.limitMetric

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HasLimitReferenceMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HasLimitReferenceMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HasLimitReferenceMetric ``Submission.DifferentialGeometry.CheegerGromovCompactness.HasLimitReferenceMetric

def HasUniformPullbackMetricBounds
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    {Phi : PointedRiemannianConvergenceMaps (I := I) X L subseq}
    (C : PointedRiemannianConverges (I := I) X L subseq Phi) : Prop :=
  (exists Crel : Real, 1 <= Crel ∧
    forall k : Nat,
      let D := C.metrics.domain k
      letI : TopologicalSpace (MetricSourceDomain (I := I) Phi k) := D.topology
      letI : ChartedSpace H (MetricSourceDomain (I := I) Phi k) := D.charted
      letI : IsManifold I ∞ (MetricSourceDomain (I := I) Phi k) := D.smooth
      MetricUniformEquivalentOn (I := I)
        (Set.univ : Set (MetricSourceDomain (I := I) Phi k))
        D.limitMetric D.pullbackMetric Crel) ∧
  (forall q : Nat, exists Cq : Real, 0 <= Cq ∧
    forall (k : Nat) (x : MetricSourceDomain (I := I) Phi k),
      let D := C.metrics.domain k
      letI : TopologicalSpace (MetricSourceDomain (I := I) Phi k) := D.topology
      letI : ChartedSpace H (MetricSourceDomain (I := I) Phi k) := D.charted
      letI : T2Space (MetricSourceDomain (I := I) Phi k) := D.t2
      letI : IsManifold I ∞ (MetricSourceDomain (I := I) Phi k) := D.smooth
      letI : SigmaCompactSpace (MetricSourceDomain (I := I) Phi k) := D.sigmaCompact
      metricCovDerivNorm (I := I) q D.pullbackMetric D.limitMetric x <= Cq)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HasUniformPullbackMetricBounds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HasUniformPullbackMetricBounds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HasUniformPullbackMetricBounds ``Submission.DifferentialGeometry.CheegerGromovCompactness.HasUniformPullbackMetricBounds

structure ConvergentMetricChain
    {M : ℕ → Type u} [∀ j, MetricSpace (M j)] [∀ j, ChartedSpace H (M j)]
    [∀ j, IsManifold I ∞ (M j)] [∀ j, SigmaCompactSpace (M j)] [∀ j, T2Space (M j)]
    (b : ∀ j, M j)
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (g : ∀ j, SmoothRiemannianMetric I (M j)) where
  start : ℕ
  one_le_start : 1 ≤ start
  zeroOrderApproximation : ∀ n k, PartialDiffeomorphMetricApproximation (I := I)
    (Metric.closedBall (b (start + n)) ((2 : ℝ) ^ (start + n))) (1 / 2) 0
    (chainComp (I := I) (Mf := M) Ψ (start + n) k)
    (g (start + n)) (g ((start + n) + k))
  sourceCoverage : ∀ n k,
    (ballOpen b (fun s => (2 : ℝ) ^ s) (start + n) : Set (M (start + n))) ⊆
      (chainComp (I := I) (Mf := M) Ψ (start + n) k).source
  successorCoverage : ∀ n,
    (chainComp (I := I) (Mf := M) Ψ (start + n) 1 :
      M (start + n) → M (start + (n + 1))) ''
        (ballOpen b (fun s => (2 : ℝ) ^ s) (start + n) : Set (M (start + n))) ⊆
      (ballOpen b (fun s => (2 : ℝ) ^ s) (start + (n + 1)) :
        Set (M (start + (n + 1))))
  limitMetric : ∀ n, SmoothRiemannianMetric I
    (ballOpen b (fun s => (2 : ℝ) ^ s) (start + n))
  derivativesConverge : ∀ ε : ℝ, 0 < ε → ∀ p : ℕ, ∃ n₀ : ℕ,
    ∀ n : ℕ, n₀ ≤ n →
      letI : SigmaCompactSpace
          (ballOpen b (fun s => (2 : ℝ) ^ s) (start + n)) :=
        isSigmaCompact_iff_sigmaCompactSpace.mp
          (Geometry.isSigmaCompact_of_isOpen I
            (ballOpen b (fun s => (2 : ℝ) ^ s) (start + n)).isOpen)
      ∀ l q : ℕ, q ≤ p →
        ∀ x : ballOpen b (fun s => (2 : ℝ) ^ s) (start + n),
          metricDerivNorm (I := I) q
            (chainPullbackSeq (I := I) Ψ g
              (ballOpen b (fun s => (2 : ℝ) ^ s) (start + n)) (sourceCoverage n) l)
            (limitMetric n) (limitMetric n) x ≤ ε
  successorIsometry : ∀ n,
    let F : ballOpen b (fun s => (2 : ℝ) ^ s) (start + n) →
        ballOpen b (fun s => (2 : ℝ) ^ s) (start + (n + 1)) :=
      PartialDiffeomorph.opensMap
        (chainComp (I := I) (Mf := M) Ψ (start + n) 1)
          (successorCoverage n)
    ∀ (x : ballOpen b (fun s => (2 : ℝ) ^ s) (start + n))
      (v w : TangentSpace I x),
      (limitMetric n).inner x v w =
        (limitMetric (n + 1)).inner (F x)
          (mfderiv I I F x v) (mfderiv I I F x w)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.ConvergentMetricChain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.ConvergentMetricChain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.ConvergentMetricChain ``Submission.DifferentialGeometry.CheegerGromovCompactness.ConvergentMetricChain

omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] in
theorem ConvergentMetricChain.tail_metric_derivatives_converge
    {M : ℕ → Type u} [∀ j, MetricSpace (M j)] [∀ j, ChartedSpace H (M j)]
    [∀ j, IsManifold I ∞ (M j)] [∀ j, SigmaCompactSpace (M j)] [∀ j, T2Space (M j)]
    (b : ∀ j, M j)
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (D : ConvergentMetricChain (I := I) b Ψ g) :
    ∀ ε : ℝ, 0 < ε → ∀ p : ℕ, ∃ n₀ : ℕ,
      ∀ n, n₀ ≤ n → ∀ q, q ≤ p → ∀ x : tailBallOpen b D.start n,
        metricDerivNorm (I := I) q
          ((g (D.start + n)).restrictOpen (I := I) (tailBallOpen b D.start n))
          (tailMetric (I := I) b D.start D.limitMetric n)
          (tailMetric (I := I) b D.start D.limitMetric n) x ≤ ε := by
  intro ε hε p
  obtain ⟨n₀, hn₀⟩ := D.derivativesConverge ε hε p
  refine ⟨n₀, fun n hn q hqp x => ?_⟩
  let U := ballOpen b (fun s => (2 : ℝ) ^ s) (D.start + n)
  let V := tailBallOpen b D.start n
  let : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
  let : SigmaCompactSpace V := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I V.isOpen)
  let inc : V → U := TopologicalSpace.Opens.inclusion
    (tail_ball_le_large b D.start n)
  have hbig := hn₀ n hn 0 q hqp (inc x)
  rw [chain_pullback_zero (I := I) Ψ g U (D.sourceCoverage n)] at hbig
  calc
    metricDerivNorm (I := I) q
        ((g (D.start + n)).restrictOpen (I := I) V)
        (tailMetric (I := I) b D.start D.limitMetric n)
        (tailMetric (I := I) b D.start D.limitMetric n) x =
      metricDerivNorm (I := I) q
        ((g (D.start + n)).restrictOpen (I := I) U)
        (D.limitMetric n) (D.limitMetric n) (inc x) := by
          simpa only [U, V, inc, tailMetric,
            SmoothRiemannianMetric.restrictOpen_flat] using
            metricDerivNorm_flat (I := I) (tail_ball_le_large b D.start n)
              ((g (D.start + n)).restrictOpen (I := I) U)
              (D.limitMetric n) (D.limitMetric n) q x
    _ ≤ ε := hbig

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.CheegerGromovCompactness.ConvergentMetricChain
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.ConvergentMetricChain.tail_metric_derivatives_converge then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.ConvergentMetricChain.tail_metric_derivatives_converge"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.ConvergentMetricChain.tail_metric_derivatives_converge ``Submission.DifferentialGeometry.CheegerGromovCompactness.ConvergentMetricChain.tail_metric_derivatives_converge

private def tailCollar
    {M : ℕ → Type u} [∀ j, MetricSpace (M j)]
    (b : ∀ j, M j) (j₀ n : ℕ) :
    Set (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n)) :=
  {x | _root_.Dist.dist (x : M (j₀ + n)) (b (j₀ + n)) ≤ (2 : ℝ) ^ n}

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.tailCollar
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.tailCollar target :: scope.openDecls } }

private theorem tailCollar_compact
    {M : ℕ → Type u} [∀ j, MetricSpace (M j)] [∀ j, ProperSpace (M j)]
    (b : ∀ j, M j) (j₀ n : ℕ) (hj₀ : 1 ≤ j₀) :
    IsCompact (tailCollar b j₀ n) := by
  rw [Subtype.isCompact_iff]
  have hpow : (2 : ℝ) ^ n < (2 : ℝ) ^ (j₀ + n) := by
    apply pow_lt_pow_right₀ one_lt_two
    omega
  have hval : Subtype.val '' tailCollar b j₀ n =
      Metric.closedBall (b (j₀ + n)) ((2 : ℝ) ^ n) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa only [tailCollar, Set.mem_ofPred_eq, Metric.mem_closedBall, dist_comm] using hx
    · intro hy
      have hy' : _root_.Dist.dist y (b (j₀ + n)) ≤ (2 : ℝ) ^ n := by
        simpa only [Metric.mem_closedBall, dist_comm] using hy
      refine ⟨⟨y, ?_⟩, ?_, rfl⟩
      · change _root_.Dist.dist y (b (j₀ + n)) < (2 : ℝ) ^ (j₀ + n)
        exact hy'.trans_lt hpow
      · exact hy'
  rw [hval]
  exact _root_.ProperSpace.isCompact_closedBall _ _

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.tailCollar_compact
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.tailCollar_compact target :: scope.openDecls } }

private theorem tailBall_mem
    {M : ℕ → Type u} [∀ j, MetricSpace (M j)]
    (b : ∀ j, M j) (j₀ n : ℕ) (x : tailBallOpen b j₀ n) :
    TopologicalSpace.Opens.inclusion (tail_ball_le_large b j₀ n) x ∈
      tailCollar b j₀ n := by
  change _root_.Dist.dist (x : M (j₀ + n)) (b (j₀ + n)) ≤ (2 : ℝ) ^ n
  exact x.2.le

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.tailBall_mem
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.tailBall_mem target :: scope.openDecls } }

def HasUniformMetricChainBounds
    {M : ℕ → Type u} [∀ j, MetricSpace (M j)] [∀ j, ChartedSpace H (M j)]
    [∀ j, IsManifold I ∞ (M j)] [∀ j, SigmaCompactSpace (M j)] [∀ j, T2Space (M j)]
    (b : ∀ j, M j)
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (D : ConvergentMetricChain (I := I) b Ψ g) : Prop :=
  (∃ Crel : ℝ, 1 ≤ Crel ∧ ∀ n : ℕ,
    MetricUniformEquivalentOn (I := I)
      (Set.univ : Set (tailBallOpen b D.start n))
      (tailMetric (I := I) b D.start D.limitMetric n)
      ((g (D.start + n)).restrictOpen (I := I) (tailBallOpen b D.start n)) Crel) ∧
  (∀ q : ℕ, ∃ Cq : ℝ, 0 ≤ Cq ∧
    ∀ (n : ℕ) (x : tailBallOpen b D.start n),
      metricCovDerivNorm (I := I) q
        ((g (D.start + n)).restrictOpen (I := I) (tailBallOpen b D.start n))
        (tailMetric (I := I) b D.start D.limitMetric n) x ≤ Cq)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HasUniformMetricChainBounds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HasUniformMetricChainBounds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HasUniformMetricChainBounds ``Submission.DifferentialGeometry.CheegerGromovCompactness.HasUniformMetricChainBounds

omit [I.Boundaryless] in
omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
private theorem alignedProper
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)} (k : ℕ)
    (P : ProperMetricOn (I := I) (X.obj k)) :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : MetricSpace (X.obj k).M := ProperMetricOn.alignedMetricSpace (X.obj k) P
    ProperSpace (X.obj k).M := by
  let : TopologicalSpace (X.obj k).M := (X.obj k).topology
  let : MetricSpace (X.obj k).M := ProperMetricOn.alignedMetricSpace (X.obj k) P
  constructor
  intro x r
  have hcompact :
      @IsCompact (X.obj k).M
        P.ms.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
        (letI : MetricSpace (X.obj k).M := P.ms
         Metric.closedBall x r) := by
    let : MetricSpace (X.obj k).M := P.ms
    let : ProperSpace (X.obj k).M := P.proper
    exact _root_.ProperSpace.isCompact_closedBall x r
  rw [ProperMetricOn.top_eq (X.obj k) P] at hcompact
  exact hcompact

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.alignedProper
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.alignedProper target :: scope.openDecls } }

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
noncomputable def tailMemberMaps
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (P : ∀ k, ProperMetricOn (I := I) (X.obj k)) (σ : ℕ → ℕ) :
    letI : ∀ j, TopologicalSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).topology
    letI : ∀ j, ChartedSpace H (X.obj (σ j)).M := fun j => (X.obj (σ j)).charted
    letI : ∀ j, IsManifold I ∞ (X.obj (σ j)).M := fun j => (X.obj (σ j)).smooth
    letI : ∀ j, T2Space (X.obj (σ j)).M := fun j => (X.obj (σ j)).t2
    letI : ∀ j, SigmaCompactSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).sigmaCompact
    letI : ∀ j, MetricSpace (X.obj (σ j)).M := fun j =>
      ProperMetricOn.alignedMetricSpace (X.obj (σ j)) (P (σ j))
    letI : ∀ j, IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.obj (σ j)).M := fun j => by
      change IsManifold I ∞ (X.obj (σ j)).M
      infer_instance
    letI : ∀ j, Bundle.RiemannianBundle
        (fun x : (X.obj (σ j)).M => TangentSpace I x) :=
      fun j => (X.obj (σ j)).riemBundle
    letI : ∀ j, IsRiemannianManifold I (X.obj (σ j)).M := fun j => by
      refine ⟨fun x y => ?_⟩
      have hreal := (P (σ j)).realizes x y
      rw [edist_dist, ← hreal]
      rfl
    ∀ (Ψ : ∀ j, PartialDiffeomorph I I (X.obj (σ j)).M
        (X.obj (σ (j + 1))).M (∞ : WithTop ℕ∞))
      (hbase : ∀ j, (Ψ j : (X.obj (σ j)).M → (X.obj (σ (j + 1))).M)
        (X.obj (σ j)).basepoint = (X.obj (σ (j + 1))).basepoint)
      (j₀ : ℕ)
      (D₀ : ∀ n k, PartialDiffeomorphMetricApproximation (I := I)
        (Metric.closedBall (X.obj (σ (j₀ + n))).basepoint ((2 : ℝ) ^ (j₀ + n)))
        (1 / 2) 0
        (chainComp (I := I) (Mf := fun j => (X.obj (σ j)).M) Ψ (j₀ + n) k)
        (X.obj (σ (j₀ + n))).metric (X.obj (σ ((j₀ + n) + k))).metric),
      let b := fun j => (X.obj (σ j)).basepoint
      let g := fun j => (X.obj (σ j)).metric
      letI : ∀ n, Nonempty (tailBallOpen b j₀ n) := fun n => tail_ball_nonempty b j₀ n
      let S := tailBallSystem (I := I) b Ψ hbase g (by
        intro j x v
        with_unfolding_all exact
          (DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
            (I := I) (g j) x v)) j₀ D₀
      letI : ∀ n, SigmaCompactSpace (tailBallOpen b j₀ n) := fun n =>
        isSigmaCompact_iff_sigmaCompactSpace.mp
          (Geometry.isSigmaCompact_of_isOpen I (tailBallOpen b j₀ n).isOpen)
      ∀ (gTail : ∀ n, SmoothRiemannianMetric I (tailBallOpen b j₀ n))
        (hgTail : S.MetricCocycle gTail),
        PointedRiemannianConvergenceMaps (I := I) X
          (pointedDirectLimitOfMetricCocycle S (tailCenter b j₀ 0) gTail hgTail)
          (fun n => σ (j₀ + n)) := by
  letI : ∀ j, TopologicalSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).topology
  letI : ∀ j, ChartedSpace H (X.obj (σ j)).M := fun j => (X.obj (σ j)).charted
  letI : ∀ j, IsManifold I ∞ (X.obj (σ j)).M := fun j => (X.obj (σ j)).smooth
  letI : ∀ j, T2Space (X.obj (σ j)).M := fun j => (X.obj (σ j)).t2
  letI : ∀ j, SigmaCompactSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).sigmaCompact
  letI : ∀ j, MetricSpace (X.obj (σ j)).M := fun j =>
    ProperMetricOn.alignedMetricSpace (X.obj (σ j)) (P (σ j))
  letI : ∀ j, IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.obj (σ j)).M := fun j => by
    change IsManifold I ∞ (X.obj (σ j)).M
    infer_instance
  letI : ∀ j, Bundle.RiemannianBundle
      (fun x : (X.obj (σ j)).M => TangentSpace I x) :=
    fun j => (X.obj (σ j)).riemBundle
  letI : ∀ j, IsRiemannianManifold I (X.obj (σ j)).M := fun j => by
    refine ⟨fun x y => ?_⟩
    have hreal := (P (σ j)).realizes x y
    rw [edist_dist, ← hreal]
    rfl
  intro Ψ hbase j₀ D₀
  let b := fun j => (X.obj (σ j)).basepoint
  let g := fun j => (X.obj (σ j)).metric
  letI : ∀ n, Nonempty (tailBallOpen b j₀ n) := fun n => tail_ball_nonempty b j₀ n
  let S := tailBallSystem (I := I) b Ψ hbase g (by
    intro j x v
    with_unfolding_all exact
      (DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := I) (g j) x v)) j₀ D₀
  letI : ∀ n, SigmaCompactSpace (tailBallOpen b j₀ n) := fun n =>
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen I (tailBallOpen b j₀ n).isOpen)
  dsimp only
  intro gTail hgTail
  let Φ : ∀ n, PartialDiffeomorph I I S.toSeqSystem.Lim
      (X.obj (σ (j₀ + n))).M (∞ : WithTop ℕ∞) := fun n =>
    PartialDiffeomorph.liftTargetOpen (S.inclPartialDiffeo n) rfl
  refine
    { partialDiffeomorph := Φ
      source_exhausts := ?_
      base_mem := fun n => ?_
      basepoint_map := fun n => ?_ }
  · change ExhaustsByOpen (fun k => Set.range (S.toSeqSystem.incl k))
    exact range_exhausts S
  · change S.toSeqSystem.incl 0 (tailCenter b j₀ 0) ∈
      Set.range (S.toSeqSystem.incl n)
    exact ⟨S.toSeqSystem.map (Nat.zero_le n) (tailCenter b j₀ 0),
      S.toSeqSystem.incl_comp (Nat.zero_le n) (tailCenter b j₀ 0)⟩
  · calc
      Φ n (S.toSeqSystem.incl 0 (tailCenter b j₀ 0)) =
          (S.toSeqSystem.map (Nat.zero_le n) (tailCenter b j₀ 0) :
            (X.obj (σ (j₀ + n))).M) :=
        congrArg Subtype.val
          (S.invIncl_incl_le (Nat.zero_le n) (tailCenter b j₀ 0))
      _ = (X.obj (σ (j₀ + n))).basepoint := by
        exact congrArg Subtype.val
          (tail_ball_system_map_center (I := I) b Ψ hbase g (by
            intro j x v
            with_unfolding_all exact
              (Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
                (I := I) (g j) x v)) j₀ D₀ n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.tailMemberMaps then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.tailMemberMaps"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.tailMemberMaps ``Submission.DifferentialGeometry.CheegerGromovCompactness.tailMemberMaps

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
noncomputable def tailMemberConvergence
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (P : ∀ k, ProperMetricOn (I := I) (X.obj k)) (σ : ℕ → ℕ) :
    letI : ∀ j, TopologicalSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).topology
    letI : ∀ j, ChartedSpace H (X.obj (σ j)).M := fun j => (X.obj (σ j)).charted
    letI : ∀ j, IsManifold I ∞ (X.obj (σ j)).M := fun j => (X.obj (σ j)).smooth
    letI : ∀ j, T2Space (X.obj (σ j)).M := fun j => (X.obj (σ j)).t2
    letI : ∀ j, SigmaCompactSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).sigmaCompact
    letI : ∀ j, MetricSpace (X.obj (σ j)).M := fun j =>
      ProperMetricOn.alignedMetricSpace (X.obj (σ j)) (P (σ j))
    letI : ∀ j, IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.obj (σ j)).M := fun j => by
      change IsManifold I ∞ (X.obj (σ j)).M
      infer_instance
    letI : ∀ j, Bundle.RiemannianBundle
        (fun x : (X.obj (σ j)).M => TangentSpace I x) :=
      fun j => (X.obj (σ j)).riemBundle
    letI : ∀ j, IsRiemannianManifold I (X.obj (σ j)).M := fun j => by
      refine ⟨fun x y => ?_⟩
      have hreal := (P (σ j)).realizes x y
      rw [edist_dist, ← hreal]
      rfl
    ∀ (Ψ : ∀ j, PartialDiffeomorph I I (X.obj (σ j)).M
        (X.obj (σ (j + 1))).M (∞ : WithTop ℕ∞))
      (hbase : ∀ j, (Ψ j : (X.obj (σ j)).M → (X.obj (σ (j + 1))).M)
        (X.obj (σ j)).basepoint = (X.obj (σ (j + 1))).basepoint)
      (j₀ : ℕ)
      (D₀ : ∀ n k, PartialDiffeomorphMetricApproximation (I := I)
        (Metric.closedBall (X.obj (σ (j₀ + n))).basepoint ((2 : ℝ) ^ (j₀ + n)))
        (1 / 2) 0
        (chainComp (I := I) (Mf := fun j => (X.obj (σ j)).M) Ψ (j₀ + n) k)
        (X.obj (σ (j₀ + n))).metric (X.obj (σ ((j₀ + n) + k))).metric),
      let b := fun j => (X.obj (σ j)).basepoint
      let g := fun j => (X.obj (σ j)).metric
      letI : ∀ n, Nonempty (tailBallOpen b j₀ n) := fun n => tail_ball_nonempty b j₀ n
      let S := tailBallSystem (I := I) b Ψ hbase g (by
        intro j x v
        with_unfolding_all exact
          (DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
            (I := I) (g j) x v)) j₀ D₀
      letI : ∀ n, SigmaCompactSpace (tailBallOpen b j₀ n) := fun n =>
        isSigmaCompact_iff_sigmaCompactSpace.mp
          (Geometry.isSigmaCompact_of_isOpen I (tailBallOpen b j₀ n).isOpen)
      ∀ (gTail : ∀ n, SmoothRiemannianMetric I (tailBallOpen b j₀ n))
        (hgTail : S.MetricCocycle gTail),
        PointedRiemannianConverges (I := I)
            (chainAmbientSeq (I := I) j₀ (tailBallOpen b j₀) S
              (tailCenter b j₀ 0) g)
            (pointedDirectLimitOfMetricCocycle S (tailCenter b j₀ 0) gTail hgTail) id
            (chainAmbientMaps (I := I) j₀ (tailBallOpen b j₀) S
              (tailCenter b j₀ 0) g gTail hgTail) →
          PointedRiemannianConverges (I := I) X
            (pointedDirectLimitOfMetricCocycle S (tailCenter b j₀ 0) gTail hgTail)
            (fun n => σ (j₀ + n))
            (tailMemberMaps (I := I) P σ Ψ hbase j₀ D₀ gTail hgTail) := by
  letI : ∀ j, TopologicalSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).topology
  letI : ∀ j, ChartedSpace H (X.obj (σ j)).M := fun j => (X.obj (σ j)).charted
  letI : ∀ j, IsManifold I ∞ (X.obj (σ j)).M := fun j => (X.obj (σ j)).smooth
  letI : ∀ j, T2Space (X.obj (σ j)).M := fun j => (X.obj (σ j)).t2
  letI : ∀ j, SigmaCompactSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).sigmaCompact
  letI : ∀ j, MetricSpace (X.obj (σ j)).M := fun j =>
    ProperMetricOn.alignedMetricSpace (X.obj (σ j)) (P (σ j))
  letI : ∀ j, IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.obj (σ j)).M := fun j => by
    change IsManifold I ∞ (X.obj (σ j)).M
    infer_instance
  letI : ∀ j, Bundle.RiemannianBundle
      (fun x : (X.obj (σ j)).M => TangentSpace I x) :=
    fun j => (X.obj (σ j)).riemBundle
  letI : ∀ j, IsRiemannianManifold I (X.obj (σ j)).M := fun j => by
    refine ⟨fun x y => ?_⟩
    have hreal := (P (σ j)).realizes x y
    rw [edist_dist, ← hreal]
    rfl
  intro Ψ hbase j₀ D₀
  let b := fun j => (X.obj (σ j)).basepoint
  let g := fun j => (X.obj (σ j)).metric
  letI : ∀ n, Nonempty (tailBallOpen b j₀ n) := fun n => tail_ball_nonempty b j₀ n
  let S := tailBallSystem (I := I) b Ψ hbase g (by
    intro j x v
    with_unfolding_all exact
      (DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := I) (g j) x v)) j₀ D₀
  letI : ∀ n, SigmaCompactSpace (tailBallOpen b j₀ n) := fun n =>
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen I (tailBallOpen b j₀ n).isOpen)
  dsimp only
  intro gTail hgTail C
  let XTail := X.subseq (fun n => σ (j₀ + n))
  let bTail : ∀ n, (XTail.obj n).M := fun n =>
    (S.toSeqSystem.map (Nat.zero_le n) (tailCenter b j₀ 0) :
      (X.obj (σ (j₀ + n))).M)
  let L := pointedDirectLimitOfMetricCocycle S (tailCenter b j₀ 0) gTail hgTail
  let Φr : PointedRiemannianConvergenceMaps (I := I) (XTail.repoint bTail) L id := by
    change PointedRiemannianConvergenceMaps (I := I)
      (chainAmbientSeq (I := I) j₀ (tailBallOpen b j₀) S
        (tailCenter b j₀ 0) g) L id
    exact chainAmbientMaps (I := I) j₀ (tailBallOpen b j₀) S
      (tailCenter b j₀ 0) g gTail hgTail
  have hbase' : ∀ n,
      letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : TopologicalSpace (XTail.obj (id n)).M := (XTail.obj (id n)).topology
      letI : ChartedSpace H (XTail.obj (id n)).M := (XTail.obj (id n)).charted
      Φr.partialDiffeomorph n L.basepoint = (XTail.obj (id n)).basepoint := by
    intro n
    with_unfolding_all
      change ((Function.invFun (S.toSeqSystem.incl n)
          (S.toSeqSystem.incl 0 (tailCenter b j₀ 0)) :
            tailBallOpen b j₀ n) :
          (X.obj (σ (j₀ + n))).M) =
        (X.obj (σ (j₀ + n))).basepoint
    have hfirst :=
      congrArg Subtype.val
        (S.invIncl_incl_le (Nat.zero_le n) (tailCenter b j₀ 0))
    with_unfolding_all rw [hfirst]
    exact congrArg Subtype.val
      (tail_ball_system_map_center (I := I) b Ψ hbase g (by
        intro j x v
        with_unfolding_all exact
          (Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
            (I := I) (g j) x v)) j₀ D₀ n)
  have Cr : PointedRiemannianConverges (I := I) (XTail.repoint bTail) L id Φr := by
    change PointedRiemannianConverges (I := I)
      (chainAmbientSeq (I := I) j₀ (tailBallOpen b j₀) S
        (tailCenter b j₀ 0) g) L id
      (chainAmbientMaps (I := I) j₀ (tailBallOpen b j₀) S
        (tailCenter b j₀ 0) g gTail hgTail)
    exact C
  have Cu := Cr.unrepoint bTail hbase'
  exact Cu.ofSubseq (fun n => σ (j₀ + n))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.tailMemberConvergence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.tailMemberConvergence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.tailMemberConvergence ``Submission.DifferentialGeometry.CheegerGromovCompactness.tailMemberConvergence

namespace CanonicalMetricCompactness

noncomputable def canonicalReferenceMetric
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Phi : PointedRiemannianConvergenceMaps (I := I) X L subseq) (k : Nat) :
    letI : TopologicalSpace (MetricSourceDomain (I := I) Phi k) :=
      metricSourceDomainTopology (I := I) Phi k
    letI : ChartedSpace H (MetricSourceDomain (I := I) Phi k) :=
      metricSourceDomainChartedSpace (I := I) Phi k
    letI : IsManifold I ∞ (MetricSourceDomain (I := I) Phi k) :=
      metric_source_domain_smooth (I := I) Phi k
    SmoothRiemannianMetric I (MetricSourceDomain (I := I) Phi k) := by
  letI : TopologicalSpace L.M := L.topology
  letI : ChartedSpace H L.M := L.charted
  letI : T2Space L.M := L.t2
  letI : IsManifold I ∞ L.M := L.smooth
  letI : SigmaCompactSpace L.M := L.sigmaCompact
  letI : TopologicalSpace (MetricSourceDomain (I := I) Phi k) :=
    metricSourceDomainTopology (I := I) Phi k
  letI : ChartedSpace H (MetricSourceDomain (I := I) Phi k) :=
    metricSourceDomainChartedSpace (I := I) Phi k
  letI : T2Space (MetricSourceDomain (I := I) Phi k) :=
    metric_source_domain_t2 (I := I) Phi k
  letI : IsManifold I ∞ (MetricSourceDomain (I := I) Phi k) :=
    metric_source_domain_smooth (I := I) Phi k
  letI : SigmaCompactSpace (MetricSourceDomain (I := I) Phi k) :=
    metric_source_domain_sigma_compact (I := I) Phi k (PointedRiemannianConvergenceMaps.isSigmaCompact_source (I := I) Phi k)
  exact L.metric.restrictOpen (I := I) (metricSourceOpenSubset (I := I) Phi k)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.CanonicalMetricCompactness.canonicalReferenceMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.CanonicalMetricCompactness.canonicalReferenceMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.CanonicalMetricCompactness.canonicalReferenceMetric ``Submission.DifferentialGeometry.CheegerGromovCompactness.CanonicalMetricCompactness.canonicalReferenceMetric

noncomputable def canonicalSourceData
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Phi : PointedRiemannianConvergenceMaps (I := I) X L subseq) (k : Nat) :
    MetricSourceData (I := I) Phi k :=
  MetricSourceData.ofRestrictPullback (I := I)
    (Φ := Phi) (k := k) (PointedRiemannianConvergenceMaps.isSigmaCompact_source (I := I) Phi k)
    (canonicalReferenceMetric (I := I) Phi k)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.CanonicalMetricCompactness.canonicalSourceData then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.CanonicalMetricCompactness.canonicalSourceData"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.CanonicalMetricCompactness.canonicalSourceData ``Submission.DifferentialGeometry.CheegerGromovCompactness.CanonicalMetricCompactness.canonicalSourceData

end CanonicalMetricCompactness

omit [I.Boundaryless] [NeZero (Module.finrank ℝ E)] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [CompleteSpace E] in
private theorem chain_limit_metric_eq_pullback
    {M : ℕ → Type u} [∀ j, MetricSpace (M j)] [∀ j, ChartedSpace H (M j)]
    [∀ j, IsManifold I ∞ (M j)] [∀ j, SigmaCompactSpace (M j)] [∀ j, T2Space (M j)]
    (j₀ : ℕ) (U : ∀ n, TopologicalSpace.Opens (M (j₀ + n))) [∀ n, Nonempty (U n)]
    [∀ n, SigmaCompactSpace (U n)]
    (S : SmoothSeqSystem I (fun n => U n)) (O₀ : U 0)
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (gInf : ∀ n, SmoothRiemannianMetric I (U n))
    (hgInf : S.MetricCocycle gInf) (k : ℕ) :
    let Φ := chainAmbientMaps (I := I) j₀ U S O₀ g gInf hgInf
    let D := CanonicalMetricCompactness.canonicalSourceData (I := I) Φ k
    letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) := D.topology
    letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) := D.charted
    letI : T2Space (MetricSourceDomain (I := I) Φ k) := D.t2
    letI : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) := D.smooth
    letI : SigmaCompactSpace (MetricSourceDomain (I := I) Φ k) := D.sigmaCompact
    D.limitMetric = Diffeomorph.pullbackMetric (I := I) (gInf k)
      (metricSourceTargetDiffeomorph (I := I) Φ k) := by
  let Φ := chainAmbientMaps (I := I) j₀ U S O₀ g gInf hgInf
  let D := CanonicalMetricCompactness.canonicalSourceData (I := I) Φ k
  let : TopologicalSpace (pointedDirectLimitOfMetricCocycle S O₀ gInf hgInf).M :=
    (pointedDirectLimitOfMetricCocycle S O₀ gInf hgInf).topology
  let : ChartedSpace H (pointedDirectLimitOfMetricCocycle S O₀ gInf hgInf).M :=
    (pointedDirectLimitOfMetricCocycle S O₀ gInf hgInf).charted
  let : TopologicalSpace
      ((chainAmbientSeq (I := I) j₀ U S O₀ g).obj (id k)).M :=
    ((chainAmbientSeq (I := I) j₀ U S O₀ g).obj (id k)).topology
  let : ChartedSpace H
      ((chainAmbientSeq (I := I) j₀ U S O₀ g).obj (id k)).M :=
    ((chainAmbientSeq (I := I) j₀ U S O₀ g).obj (id k)).charted
  let : TopologicalSpace (MetricSourceDomain (I := I) Φ k) := D.topology
  let : ChartedSpace H (MetricSourceDomain (I := I) Φ k) := D.charted
  let : T2Space (MetricSourceDomain (I := I) Φ k) := D.t2
  let : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) := D.smooth
  let : SigmaCompactSpace (MetricSourceDomain (I := I) Φ k) := D.sigmaCompact
  let : TopologicalSpace (MetricTargetDomain (I := I) Φ k) :=
    metricTargetDomainTopology (I := I) Φ k
  let : ChartedSpace H (MetricTargetDomain (I := I) Φ k) :=
    metricTargetDomainChartedSpace (I := I) Φ k
  let : T2Space (MetricTargetDomain (I := I) Φ k) :=
    metric_target_domain_t2 (I := I) Φ k
  let : IsManifold I ∞ (MetricTargetDomain (I := I) Φ k) :=
    metric_target_domain_smooth (I := I) Φ k
  let : SigmaCompactSpace (MetricTargetDomain (I := I) Φ k) :=
    metric_target_domain_sigma_compact (I := I) Φ k (PointedRiemannianConvergenceMaps.isSigmaCompact_target (I := I) Φ k)
  let F := metricSourceTargetDiffeomorph (I := I) Φ k
  have metric_ext : ∀ (g₁ g₂ : SmoothRiemannianMetric I
      (MetricSourceDomain (I := I) Φ k)),
      (∀ (x : MetricSourceDomain (I := I) Φ k) (v w : TangentSpace I x),
        g₁.inner x v w = g₂.inner x v w) → g₁ = g₂ := by
    intro g₁ g₂ h
    obtain ⟨i₁, s₁, p₁, b₁, c₁⟩ := g₁
    obtain ⟨i₂, s₂, p₂, b₂, c₂⟩ := g₂
    have hi : i₁ = i₂ :=
      funext fun x => ContinuousLinearMap.ext fun v => ContinuousLinearMap.ext fun w => h x v w
    subst hi
    rfl
  apply metric_ext
  intro x v w
  let z : (pointedDirectLimitOfMetricCocycle S O₀ gInf hgInf).M := x
  with_unfolding_all
    change (S.limitMetric gInf hgInf).inner
      z v w =
    (gInf k).inner (F x : U k)
      (mfderiv I I F x v) (mfderiv I I F x w)
  have hz : z ∈ Set.range (S.toSeqSystem.incl k) := x.2
  rw [S.limitMetric_of_mem gInf hgInf k hz v w]
  with_unfolding_all
    change (gInf k).inner (Function.invFun (S.toSeqSystem.incl k) z)
        (mfderiv I I (Function.invFun (S.toSeqSystem.incl k)) z v)
        (mfderiv I I (Function.invFun (S.toSeqSystem.incl k)) z w) =
      (gInf k).inner
        (metricSourceTargetDiffeomorph (I := I) Φ k x : U k)
        (mfderiv I I (metricSourceTargetDiffeomorph (I := I) Φ k) x v)
        (mfderiv I I (metricSourceTargetDiffeomorph (I := I) Φ k) x w)
  have hFv :
      mfderiv I I (metricSourceTargetDiffeomorph (I := I) Φ k) x v =
        mfderiv I I (Φ.map k) z v := by
    convert! metric_source_target_diffeomorph_mfderiv (I := I) Φ k x v using 1
  have hFw :
      mfderiv I I (metricSourceTargetDiffeomorph (I := I) Φ k) x w =
        mfderiv I I (Φ.map k) z w := by
    convert! metric_source_target_diffeomorph_mfderiv (I := I) Φ k x w using 1
  rw [hFv, hFw]
  have hxSource : z ∈ (S.inclPartialDiffeo k).source := by
    change z ∈ Set.range (S.toSeqSystem.incl k)
    exact x.2
  have hFx : (F x : U k) = Function.invFun (S.toSeqSystem.incl k) z := by
    apply Subtype.ext
    have hmapPoint : Φ.map k z =
        ((Function.invFun (S.toSeqSystem.incl k) z : U k) : M (j₀ + k)) := rfl
    exact (metric_source_target_diffeomorph_apply (I := I) Φ k x).trans hmapPoint
  have hmapv : mfderiv I I (Φ.map k) z v =
      mfderiv I I
        (S.inclPartialDiffeo k : (pointedDirectLimitOfMetricCocycle S O₀ gInf hgInf).M → U k)
        z v := by
    change mfderiv I I
      (PartialDiffeomorph.liftTargetOpen (S.inclPartialDiffeo k) rfl :
        (pointedDirectLimitOfMetricCocycle S O₀ gInf hgInf).M → M (j₀ + k)) z v = _
    exact PartialDiffeomorph.mfderiv_liftTargetOpen
      (S.inclPartialDiffeo k) rfl hxSource v
  have hmapw : mfderiv I I (Φ.map k) z w =
      mfderiv I I
        (S.inclPartialDiffeo k : (pointedDirectLimitOfMetricCocycle S O₀ gInf hgInf).M → U k)
        z w := by
    change mfderiv I I
      (PartialDiffeomorph.liftTargetOpen (S.inclPartialDiffeo k) rfl :
        (pointedDirectLimitOfMetricCocycle S O₀ gInf hgInf).M → M (j₀ + k)) z w = _
    exact PartialDiffeomorph.mfderiv_liftTargetOpen
      (S.inclPartialDiffeo k) rfl hxSource w
  rw [hFx, hmapv, hmapw]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.chain_limit_metric_eq_pullback
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.chain_limit_metric_eq_pullback target :: scope.openDecls } }

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private theorem covFlat_eq
    {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {U V : TopologicalSpace.Opens M} (hVU : V ≤ U)
    [SigmaCompactSpace U] [T2Space U] [T2Space V]
    (h gRef : SmoothRiemannianMetric I U) (a : ℕ) (x : V) :
    metricCovDerivNorm (I := I) a
        (h.restrictOpenOfSubset (I := I) hVU)
        (gRef.restrictOpenOfSubset (I := I) hVU) x =
      metricCovDerivNorm (I := I) a h gRef
        (TopologicalSpace.Opens.inclusion hVU x) := by
  let W := nestedOpen (M := M) (U := U) (V := V)
  let : SigmaCompactSpace W := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I W.isOpen)
  let : IsManifold I 1 V := IsManifold.of_le (I := I) (M := V) (n := ∞) (by decide)
  let : IsManifold I 2 V := IsManifold.of_le (I := I) (M := V) (n := ∞) (by decide)
  let : IsManifold I ((∞ : WithTop ℕ∞) + 1) V := by
    change IsManifold I ∞ V
    infer_instance
  let : IsManifold I 1 W := IsManifold.of_le (I := I) (M := W) (n := ∞) (by decide)
  let : IsManifold I 2 W := IsManifold.of_le (I := I) (M := W) (n := ∞) (by decide)
  let : IsManifold I ((∞ : WithTop ℕ∞) + 1) W := by
    change IsManifold I ∞ W
    infer_instance
  let F := flatNestedDiffeo (H := H) (I := I) (M := M) hVU
  rw [restrictSubset_pull (I := I) hVU h, restrictSubset_pull (I := I) hVU gRef]
  calc
    metricCovDerivNorm (I := I) a
        (Diffeomorph.pullbackMetric (I := I) (h.restrictOpen (I := I) W) F)
        (Diffeomorph.pullbackMetric (I := I) (gRef.restrictOpen (I := I) W) F) x =
      metricCovDerivNorm (I := I) a
        (h.restrictOpen (I := I) W) (gRef.restrictOpen (I := I) W) (F x) :=
      metricCovDerivNorm_pullback (I := I) a
        (h.restrictOpen (I := I) W) (gRef.restrictOpen (I := I) W) F x
    _ = metricCovDerivNorm (I := I) a h gRef ((F x : W) : U) :=
      covNorm_restrictOpen (I := I) h gRef W a (F x)
    _ = metricCovDerivNorm (I := I) a h gRef
        (TopologicalSpace.Opens.inclusion hVU x) := by rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.covFlat_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.covFlat_eq target :: scope.openDecls } }

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] in
theorem ConvergentMetricChain.uniform_metric_bounds
    {M : ℕ → Type u} [∀ j, MetricSpace (M j)] [∀ j, ChartedSpace H (M j)]
    [∀ j, IsManifold I ∞ (M j)] [∀ j, SigmaCompactSpace (M j)] [∀ j, T2Space (M j)]
    [∀ j, ProperSpace (M j)]
    (b : ∀ j, M j)
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (D : ConvergentMetricChain (I := I) b Ψ g) :
    HasUniformMetricChainBounds (I := I) b Ψ g D := by
  classical
  constructor
  · set dim : ℝ := (Module.finrank ℝ E : ℝ) with hdim
    have hdim0 : 0 ≤ dim := by rw [hdim]; positivity
    set ε₀ : ℝ := 1 / (2 * dim + 2) with hε₀
    have hε₀pos : 0 < ε₀ := by rw [hε₀]; positivity
    obtain ⟨n₀, hn₀⟩ := D.tail_metric_derivatives_converge b Ψ g ε₀ hε₀pos 0
    have htail : ∀ n, n₀ ≤ n →
        MetricUniformEquivalentOn (I := I)
          (Set.univ : Set (tailBallOpen b D.start n))
          (tailMetric (I := I) b D.start D.limitMetric n)
          ((g (D.start + n)).restrictOpen (I := I) (tailBallOpen b D.start n)) 2 := by
      intro n hn
      have htwo : (2 : ℝ) = (1 - (1 / 2 : ℝ))⁻¹ := by norm_num
      rw [htwo]
      refine metricUniformEquivalentOn_of_metricDerivNorm
        ((g (D.start + n)).restrictOpen (I := I) (tailBallOpen b D.start n))
        (tailMetric (I := I) b D.start D.limitMetric n) (by norm_num) (by norm_num) ?_
      intro x _
      have hfr : (Module.finrank ℝ (TangentSpace I x) : ℝ) = dim := by
        rw [hdim]
        rfl
      rw [hfr]
      have hmd := hn₀ n hn 0 (le_refl 0) x
      calc
        dim * metricDerivNorm (I := I) 0
            ((g (D.start + n)).restrictOpen (I := I) (tailBallOpen b D.start n))
            (tailMetric (I := I) b D.start D.limitMetric n)
            (tailMetric (I := I) b D.start D.limitMetric n) x ≤ dim * ε₀ :=
          mul_le_mul_of_nonneg_left hmd hdim0
        _ ≤ 1 / 2 := by
          rw [hε₀, mul_one_div, div_le_iff₀ (by positivity)]
          nlinarith
    have hhead : ∀ n : ℕ, ∃ Cn : ℝ,
        MetricUniformEquivalentOn (I := I)
          (Set.univ : Set (tailBallOpen b D.start n))
          (tailMetric (I := I) b D.start D.limitMetric n)
          ((g (D.start + n)).restrictOpen (I := I) (tailBallOpen b D.start n)) Cn := by
      intro n
      let U := ballOpen b (fun s => (2 : ℝ) ^ s) (D.start + n)
      let V := tailBallOpen b D.start n
      let : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
        (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
      let inc : V → U := TopologicalSpace.Opens.inclusion
        (tail_ball_le_large b D.start n)
      obtain ⟨Cn, hCn⟩ := equivOn_compact (I := I)
        (tailCollar_compact b D.start n D.one_le_start)
        (D.limitMetric n) ((g (D.start + n)).restrictOpen (I := I) U)
      refine ⟨Cn, hCn.1, fun x _ v => ?_⟩
      have hx := hCn.2 (inc x) (tailBall_mem b D.start n x) v
      with_unfolding_all exact hx
    choose Chead hChead using hhead
    have hChead0 : ∀ n, 0 ≤ Chead n := fun n =>
      le_trans zero_le_one (hChead n).1
    let Crel : ℝ := 2 + ∑ n ∈ Finset.range n₀, Chead n
    have hsum0 : 0 ≤ ∑ n ∈ Finset.range n₀, Chead n :=
      Finset.sum_nonneg fun n _ => hChead0 n
    refine ⟨Crel, by dsimp only [Crel]; linarith, fun n => ?_⟩
    by_cases hn : n₀ ≤ n
    · exact metricUniformEquivalentOn_of_le (htail n hn) (by
        dsimp only [Crel]
        linarith)
    · have hnlt : n < n₀ := Nat.lt_of_not_le hn
      refine metricUniformEquivalentOn_of_le (hChead n) ?_
      have hsingle : Chead n ≤ ∑ j ∈ Finset.range n₀, Chead j :=
        Finset.single_le_sum (fun j _ => hChead0 j) (Finset.mem_range.mpr hnlt)
      dsimp only [Crel]
      linarith
  · intro q
    obtain ⟨n₀, hn₀⟩ := D.tail_metric_derivatives_converge b Ψ g 1 one_pos q
    set dim : ℝ := (Module.finrank ℝ E : ℝ) with hdim
    let Ctail : ℝ := Real.sqrt dim + 1
    have hsqrt0 : 0 ≤ Real.sqrt dim := Real.sqrt_nonneg _
    have hCtail0 : 0 ≤ Ctail := by
      dsimp only [Ctail]
      positivity
    have htail : ∀ n, n₀ ≤ n → ∀ x : tailBallOpen b D.start n,
        metricCovDerivNorm (I := I) q
          ((g (D.start + n)).restrictOpen (I := I) (tailBallOpen b D.start n))
          (tailMetric (I := I) b D.start D.limitMetric n) x ≤ Ctail := by
      intro n hn x
      have hdiff := hn₀ n hn q (le_refl q) x
      refine (covNorm_le_add (I := I) q
        ((g (D.start + n)).restrictOpen (I := I) (tailBallOpen b D.start n))
        (tailMetric (I := I) b D.start D.limitMetric n)
        (tailMetric (I := I) b D.start D.limitMetric n) x).trans ?_
      cases q with
      | zero =>
          have hself := covNorm0_le (I := I)
            (tailMetric (I := I) b D.start D.limitMetric n)
            (tailMetric (I := I) b D.start D.limitMetric n) x
            (C := 1) (le_refl 1) (by
              intro v
              simp only [inv_one, one_mul]
              exact ⟨le_rfl, le_rfl⟩)
          rw [← hdim] at hself
          dsimp only [Ctail]
          linarith
      | succ a =>
          rw [covNorm_self_succ (I := I)]
          dsimp only [Ctail]
          linarith
    have hhead : ∀ n : ℕ, ∃ Cn : ℝ, 0 ≤ Cn ∧
        ∀ x : tailBallOpen b D.start n,
          metricCovDerivNorm (I := I) q
            ((g (D.start + n)).restrictOpen (I := I) (tailBallOpen b D.start n))
            (tailMetric (I := I) b D.start D.limitMetric n) x ≤ Cn := by
      intro n
      let U := ballOpen b (fun s => (2 : ℝ) ^ s) (D.start + n)
      let V := tailBallOpen b D.start n
      let : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
        (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
      let inc : V → U := TopologicalSpace.Opens.inclusion
        (tail_ball_le_large b D.start n)
      obtain ⟨Cn, hCn⟩ := metricCovDerivNorm_bddOn (I := I)
        (tailCollar_compact b D.start n D.one_le_start) q
        ((g (D.start + n)).restrictOpen (I := I) U) (D.limitMetric n)
      refine ⟨max 0 Cn, le_max_left _ _, fun x => ?_⟩
      have hflat := covFlat_eq (I := I) (tail_ball_le_large b D.start n)
        ((g (D.start + n)).restrictOpen (I := I) U) (D.limitMetric n) q x
      have heq :
          metricCovDerivNorm (I := I) q
              ((g (D.start + n)).restrictOpen (I := I) V)
              (tailMetric (I := I) b D.start D.limitMetric n) x =
            metricCovDerivNorm (I := I) q
              ((g (D.start + n)).restrictOpen (I := I) U) (D.limitMetric n) (inc x) := by
        simpa only [U, V, inc, tailMetric,
          SmoothRiemannianMetric.restrictOpen_flat] using hflat
      rw [heq]
      exact (hCn (inc x) (tailBall_mem b D.start n x)).trans (le_max_right _ _)
    choose Chead hChead0 hChead using hhead
    let Cq : ℝ := Ctail + ∑ n ∈ Finset.range n₀, Chead n
    have hsum0 : 0 ≤ ∑ n ∈ Finset.range n₀, Chead n :=
      Finset.sum_nonneg fun n hn => hChead0 n
    refine ⟨Cq, by dsimp only [Cq]; linarith, fun n x => ?_⟩
    by_cases hn : n₀ ≤ n
    · exact (htail n hn x).trans (by
        dsimp only [Cq]
        linarith)
    · have hnlt : n < n₀ := Nat.lt_of_not_le hn
      have hsingle : Chead n ≤ ∑ j ∈ Finset.range n₀, Chead j :=
        Finset.single_le_sum (fun j _ => hChead0 j) (Finset.mem_range.mpr hnlt)
      exact (hChead n x).trans (by
        dsimp only [Cq]
        linarith)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.ConvergentMetricChain.uniform_metric_bounds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.ConvergentMetricChain.uniform_metric_bounds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.ConvergentMetricChain.uniform_metric_bounds ``Submission.DifferentialGeometry.CheegerGromovCompactness.ConvergentMetricChain.uniform_metric_bounds

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
structure CanonicalMetricCompactness
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) where
  compactness : MetricCompactLimit (I := I) X
  domain_eq_canonical : forall k : Nat,
    compactness.convergence.metrics.domain k =
      CanonicalMetricCompactness.canonicalSourceData (I := I) compactness.maps k
  reference_eq_limit : forall k : Nat,
    let D := compactness.convergence.metrics.domain k
    letI : TopologicalSpace (MetricSourceDomain (I := I) compactness.maps k) := D.topology
    letI : ChartedSpace H (MetricSourceDomain (I := I) compactness.maps k) := D.charted
    letI : IsManifold I ∞ (MetricSourceDomain (I := I) compactness.maps k) := D.smooth
    D.referenceMetric = D.limitMetric
  uniformly_equivalent : exists Crel : Real, 1 <= Crel ∧
    forall k : Nat,
      let D := compactness.convergence.metrics.domain k
      letI : TopologicalSpace (MetricSourceDomain (I := I) compactness.maps k) := D.topology
      letI : ChartedSpace H (MetricSourceDomain (I := I) compactness.maps k) := D.charted
      letI : IsManifold I ∞ (MetricSourceDomain (I := I) compactness.maps k) := D.smooth
      MetricUniformEquivalentOn (I := I)
        (Set.univ : Set (MetricSourceDomain (I := I) compactness.maps k))
        D.limitMetric D.pullbackMetric Crel
  covariant_derivatives_bounded : forall q : Nat, exists Cq : Real, 0 <= Cq ∧
    forall (k : Nat) (x : MetricSourceDomain (I := I) compactness.maps k),
      let D := compactness.convergence.metrics.domain k
      letI : TopologicalSpace (MetricSourceDomain (I := I) compactness.maps k) := D.topology
      letI : ChartedSpace H (MetricSourceDomain (I := I) compactness.maps k) := D.charted
      letI : T2Space (MetricSourceDomain (I := I) compactness.maps k) := D.t2
      letI : IsManifold I ∞ (MetricSourceDomain (I := I) compactness.maps k) := D.smooth
      letI : SigmaCompactSpace (MetricSourceDomain (I := I) compactness.maps k) :=
        D.sigmaCompact
      metricCovDerivNorm (I := I) q D.pullbackMetric D.limitMetric x <= Cq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.CanonicalMetricCompactness then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.CanonicalMetricCompactness"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.CanonicalMetricCompactness ``Submission.DifferentialGeometry.CheegerGromovCompactness.CanonicalMetricCompactness

namespace CanonicalMetricCompactness

def ofSubsequence
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (f : Nat -> Nat) (hf : StrictMono f)
    (D : CanonicalMetricCompactness (I := I) (X.subseq f)) :
    CanonicalMetricCompactness (I := I) X where
  compactness := D.compactness.ofSeqSubseq f hf
  domain_eq_canonical := by
    intro k
    change MetricSourceData.ofSeqSubseq (I := I) f k
        (D.compactness.convergence.metrics.domain k) =
      canonicalSourceData (I := I) (D.compactness.maps.ofSeqSubseq f) k
    rw [D.domain_eq_canonical k]
    rfl
  reference_eq_limit := by
    intro k
    with_unfolding_all exact D.reference_eq_limit k
  uniformly_equivalent := by
    obtain ⟨Crel, hCrel, hrel⟩ := D.uniformly_equivalent
    refine ⟨Crel, hCrel, fun k => ?_⟩
    with_unfolding_all exact hrel k
  covariant_derivatives_bounded := by
    intro q
    obtain ⟨Cq, hCq, hcov⟩ := D.covariant_derivatives_bounded q
    refine ⟨Cq, hCq, fun k x => ?_⟩
    with_unfolding_all exact hcov k x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.CanonicalMetricCompactness.ofSubsequence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.CanonicalMetricCompactness.ofSubsequence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.CanonicalMetricCompactness.ofSubsequence ``Submission.DifferentialGeometry.CheegerGromovCompactness.CanonicalMetricCompactness.ofSubsequence

end CanonicalMetricCompactness

structure ConnectedCanonicalMetricCompactness
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) where
  canonical : CanonicalMetricCompactness (I := I) X
  connected :
    letI : TopologicalSpace canonical.compactness.limit.M :=
      canonical.compactness.limit.topology
    ConnectedSpace canonical.compactness.limit.M
  source_precompact :
    letI : TopologicalSpace canonical.compactness.limit.M :=
      canonical.compactness.limit.topology
    ∀ n, IsCompact (closure (canonical.compactness.maps.source n))
  source_connected :
    letI : TopologicalSpace canonical.compactness.limit.M :=
      canonical.compactness.limit.topology
    ∀ n, IsConnected (canonical.compactness.maps.source n)
  source_closure_subset :
    letI : TopologicalSpace canonical.compactness.limit.M :=
      canonical.compactness.limit.topology
    ∀ n, closure (canonical.compactness.maps.source n) ⊆
      canonical.compactness.maps.source (n + 1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.ConnectedCanonicalMetricCompactness then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.ConnectedCanonicalMetricCompactness"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.ConnectedCanonicalMetricCompactness ``Submission.DifferentialGeometry.CheegerGromovCompactness.ConnectedCanonicalMetricCompactness

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
noncomputable def connectedCanonicalMetricCompactnessOfConvergentChain
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (P : ∀ k, ProperMetricOn (I := I) (X.obj k))
    (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (Ψ : letI : ∀ j, TopologicalSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).topology
         letI : ∀ j, ChartedSpace H (X.obj (σ j)).M := fun j => (X.obj (σ j)).charted
         letI : ∀ j, IsManifold I ∞ (X.obj (σ j)).M := fun j => (X.obj (σ j)).smooth
         ∀ j, PartialDiffeomorph I I ((X.obj (σ j)).M) ((X.obj (σ (j + 1))).M)
           (∞ : WithTop ℕ∞))
    (hbase : ∀ j, Ψ j (X.obj (σ j)).basepoint = (X.obj (σ (j + 1))).basepoint)
    (D : letI : ∀ j, TopologicalSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).topology
         letI : ∀ j, ChartedSpace H (X.obj (σ j)).M := fun j => (X.obj (σ j)).charted
         letI : ∀ j, IsManifold I ∞ (X.obj (σ j)).M := fun j => (X.obj (σ j)).smooth
         letI : ∀ j, SigmaCompactSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).sigmaCompact
         letI : ∀ j, T2Space (X.obj (σ j)).M := fun j => (X.obj (σ j)).t2
         letI : ∀ j, MetricSpace (X.obj (σ j)).M := fun j => ProperMetricOn.alignedMetricSpace (X.obj (σ j)) (P (σ j))
         ConvergentMetricChain (I := I) (fun j => (X.obj (σ j)).basepoint) Ψ
           (fun j => (X.obj (σ j)).metric)) :
    ConnectedCanonicalMetricCompactness (I := I) X := by
  classical
  letI : ∀ j, TopologicalSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).topology
  letI : ∀ j, ChartedSpace H (X.obj (σ j)).M := fun j => (X.obj (σ j)).charted
  letI : ∀ j, IsManifold I ∞ (X.obj (σ j)).M := fun j => (X.obj (σ j)).smooth
  letI : ∀ j, T2Space (X.obj (σ j)).M := fun j => (X.obj (σ j)).t2
  letI : ∀ j, SigmaCompactSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).sigmaCompact
  letI : ∀ j, MetricSpace (X.obj (σ j)).M := fun j =>
    ProperMetricOn.alignedMetricSpace (X.obj (σ j)) (P (σ j))
  letI : ∀ j, IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.obj (σ j)).M := fun j => by
    change IsManifold I ∞ (X.obj (σ j)).M
    infer_instance
  letI : ∀ j, Bundle.RiemannianBundle
      (fun x : (X.obj (σ j)).M => TangentSpace I x) :=
    fun j => (X.obj (σ j)).riemBundle
  letI : ∀ j, IsRiemannianManifold I (X.obj (σ j)).M := fun j => by
    refine ⟨fun x y => ?_⟩
    have hreal := (P (σ j)).realizes x y
    rw [edist_dist, ← hreal]
    rfl
  letI : ∀ j, ProperSpace (X.obj (σ j)).M := fun j =>
    alignedProper (I := I) (σ j) (P (σ j))
  let b := fun j => (X.obj (σ j)).basepoint
  let g := fun j => (X.obj (σ j)).metric
  let j₀ := D.start
  have hj₀ : 1 ≤ j₀ := D.one_le_start
  let D₀ := D.zeroOrderApproximation
  let hU := D.sourceCoverage
  let hmap := D.successorCoverage
  let gInf := D.limitMetric
  have hclose := D.derivativesConverge
  have hstep := D.successorIsometry
  letI : ∀ n, Nonempty (tailBallOpen b j₀ n) := fun n => tail_ball_nonempty b j₀ n
  letI : ∀ n, SigmaCompactSpace (tailBallOpen b j₀ n) := fun n =>
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen I (tailBallOpen b j₀ n).isOpen)
  let S := tailBallSystem (I := I) b Ψ hbase g (by
    intro j x v
    with_unfolding_all exact
      (DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := I) (g j) x v)) j₀ D₀
  let gTail := tailMetric (I := I) b j₀ gInf
  let hgTail : S.MetricCocycle gTail :=
    tail_ball_system_metric_cocycle (I := I) b Ψ hbase g (by
      intro j x v
      with_unfolding_all exact
        (DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
          (I := I) (g j) x v)) j₀ D₀ hU hmap gInf hstep
  let L := pointedDirectLimitOfMetricCocycle S (tailCenter b j₀ 0) gTail hgTail
  let maps := tailMemberMaps (I := I) P σ Ψ hbase j₀ D₀ gTail hgTail
  have hcomplete : MetricComplete (I := I) L := by
    exact tail_limit_complete (I := I) b Ψ hbase g (by
      intro j x v
      with_unfolding_all exact
        (DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
          (I := I) (g j) x v)) j₀ hj₀ D₀
      hU hmap gInf hstep hclose
  let hchain := tailAmbientPointedRiemannianConvergence (I := I) b Ψ hbase g (by
    intro j x v
    with_unfolding_all exact
      (DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
      (I := I) (g j) x v)) j₀ D₀
    hU hmap gInf hstep hclose
  have hchain_ref : HasLimitReferenceMetric (I := I) hchain := by
    intro k
    simp only [hchain, tailAmbientPointedRiemannianConvergence,
      ambientPointedRiemannianConvergence,
      PointedRiemannianConverges.ofRestrictPullback,
      MetricConvergenceData.ofRestrictPullback,
      MetricConvergenceData.ofDerivNormSupOn,
      MetricSourceData.ofRestrictPullback, MetricSourceData.ofCanonical,
      pointedDirectLimitOfMetricCocycle, pointedDirectLimit]
    with_unfolding_all rfl
  have hchain_domain : forall k : Nat,
      hchain.metrics.domain k =
        CanonicalMetricCompactness.canonicalSourceData (I := I)
          (chainAmbientMaps (I := I) j₀ (tailBallOpen b j₀) S
            (tailCenter b j₀ 0) g gTail hgTail) k := by
    intro k
    simp only [hchain, tailAmbientPointedRiemannianConvergence,
      ambientPointedRiemannianConvergence,
      PointedRiemannianConverges.ofRestrictPullback,
      MetricConvergenceData.ofRestrictPullback,
      MetricConvergenceData.ofDerivNormSupOn,
      CanonicalMetricCompactness.canonicalSourceData, CanonicalMetricCompactness.canonicalReferenceMetric,
      pointedDirectLimitOfMetricCocycle, pointedDirectLimit]
    rfl
  have hstage : HasUniformMetricChainBounds (I := I) b Ψ g D :=
    D.uniform_metric_bounds (I := I) b Ψ g
  have hchain_bounds : HasUniformPullbackMetricBounds (I := I) hchain := by
    constructor
    · obtain ⟨Crel, hCrel, hrel⟩ := hstage.1
      refine ⟨Crel, hCrel, fun k => ?_⟩
      simp only [hchain, tailAmbientPointedRiemannianConvergence,
        ambientPointedRiemannianConvergence,
        PointedRiemannianConverges.ofRestrictPullback,
        MetricConvergenceData.ofRestrictPullback,
        MetricConvergenceData.ofDerivNormSupOn,
        pointedDirectLimitOfMetricCocycle, pointedDirectLimit]
      let Φc := chainAmbientMaps (I := I) j₀ (tailBallOpen b j₀) S
        (tailCenter b j₀ 0) g gTail hgTail
      let Dc := CanonicalMetricCompactness.canonicalSourceData (I := I) Φc k
      let : TopologicalSpace (MetricSourceDomain (I := I) Φc k) := Dc.topology
      let : ChartedSpace H (MetricSourceDomain (I := I) Φc k) := Dc.charted
      let : T2Space (MetricSourceDomain (I := I) Φc k) := Dc.t2
      let : IsManifold I ∞ (MetricSourceDomain (I := I) Φc k) := Dc.smooth
      let : SigmaCompactSpace (MetricSourceDomain (I := I) Φc k) := Dc.sigmaCompact
      let : TopologicalSpace (MetricTargetDomain (I := I) Φc k) :=
        metricTargetDomainTopology (I := I) Φc k
      let : ChartedSpace H (MetricTargetDomain (I := I) Φc k) :=
        metricTargetDomainChartedSpace (I := I) Φc k
      let : T2Space (MetricTargetDomain (I := I) Φc k) :=
        metric_target_domain_t2 (I := I) Φc k
      let : IsManifold I ∞ (MetricTargetDomain (I := I) Φc k) :=
        metric_target_domain_smooth (I := I) Φc k
      let : SigmaCompactSpace (MetricTargetDomain (I := I) Φc k) :=
        metric_target_domain_sigma_compact (I := I) Φc k
          (PointedRiemannianConvergenceMaps.isSigmaCompact_target (I := I) Φc k)
      let F := metricSourceTargetDiffeomorph (I := I) Φc k
      change MetricUniformEquivalentOn (I := I) Set.univ
        Dc.limitMetric Dc.pullbackMetric Crel
      rw [chain_limit_metric_eq_pullback (I := I) j₀ (tailBallOpen b j₀) S
        (tailCenter b j₀ 0) g gTail hgTail k]
      change MetricUniformEquivalentOn (I := I) Set.univ
        (Diffeomorph.pullbackMetric (I := I) (gTail k) F)
        (Diffeomorph.pullbackMetric (I := I)
          ((g (j₀ + k)).restrictOpen (I := I) (tailBallOpen b j₀ k)) F) Crel
      exact metricUniformEquivalentOn_pullback (I := I)
        (Set.univ : Set (tailBallOpen b j₀ k)) (gTail k)
        ((g (j₀ + k)).restrictOpen (I := I) (tailBallOpen b j₀ k))
        Crel (hrel k) F (by simp)
    · intro q
      obtain ⟨Cq, hCq, hcov⟩ := hstage.2 q
      refine ⟨Cq, hCq, fun k x => ?_⟩
      simp only [hchain, tailAmbientPointedRiemannianConvergence,
        ambientPointedRiemannianConvergence,
        PointedRiemannianConverges.ofRestrictPullback,
        MetricConvergenceData.ofRestrictPullback,
        MetricConvergenceData.ofDerivNormSupOn,
        pointedDirectLimitOfMetricCocycle, pointedDirectLimit]
      let Φc := chainAmbientMaps (I := I) j₀ (tailBallOpen b j₀) S
        (tailCenter b j₀ 0) g gTail hgTail
      let Dc := CanonicalMetricCompactness.canonicalSourceData (I := I) Φc k
      let : TopologicalSpace (MetricSourceDomain (I := I) Φc k) := Dc.topology
      let : ChartedSpace H (MetricSourceDomain (I := I) Φc k) := Dc.charted
      let : T2Space (MetricSourceDomain (I := I) Φc k) := Dc.t2
      let : IsManifold I ∞ (MetricSourceDomain (I := I) Φc k) := Dc.smooth
      let : SigmaCompactSpace (MetricSourceDomain (I := I) Φc k) := Dc.sigmaCompact
      let : TopologicalSpace (MetricTargetDomain (I := I) Φc k) :=
        metricTargetDomainTopology (I := I) Φc k
      let : ChartedSpace H (MetricTargetDomain (I := I) Φc k) :=
        metricTargetDomainChartedSpace (I := I) Φc k
      let : T2Space (MetricTargetDomain (I := I) Φc k) :=
        metric_target_domain_t2 (I := I) Φc k
      let : IsManifold I ∞ (MetricTargetDomain (I := I) Φc k) :=
        metric_target_domain_smooth (I := I) Φc k
      let : SigmaCompactSpace (MetricTargetDomain (I := I) Φc k) :=
        metric_target_domain_sigma_compact (I := I) Φc k
          (PointedRiemannianConvergenceMaps.isSigmaCompact_target (I := I) Φc k)
      let F := metricSourceTargetDiffeomorph (I := I) Φc k
      change metricCovDerivNorm (I := I) q
        Dc.pullbackMetric Dc.limitMetric x ≤ Cq
      rw [chain_limit_metric_eq_pullback (I := I) j₀ (tailBallOpen b j₀) S
        (tailCenter b j₀ 0) g gTail hgTail k]
      change metricCovDerivNorm (I := I) q
        (Diffeomorph.pullbackMetric (I := I)
          ((g (j₀ + k)).restrictOpen (I := I) (tailBallOpen b j₀ k)) F)
        (Diffeomorph.pullbackMetric (I := I) (gTail k) F) x ≤ Cq
      have hpull :
          metricCovDerivNorm (I := I) q
            (Diffeomorph.pullbackMetric (I := I)
              ((g (j₀ + k)).restrictOpen (I := I) (tailBallOpen b j₀ k)) F)
            (Diffeomorph.pullbackMetric (I := I) (gTail k) F) x =
          metricCovDerivNorm (I := I) q
            ((g (j₀ + k)).restrictOpen (I := I) (tailBallOpen b j₀ k))
            (gTail k) (F x) := by
        let : TopologicalSpace (MetricSourceDomain (I := I) Φc k) :=
          metricSourceDomainTopology (I := I) Φc k
        let : ChartedSpace H (MetricSourceDomain (I := I) Φc k) :=
          metricSourceDomainChartedSpace (I := I) Φc k
        let : T2Space (MetricSourceDomain (I := I) Φc k) :=
          metric_source_domain_t2 (I := I) Φc k
        let : IsManifold I ∞ (MetricSourceDomain (I := I) Φc k) :=
          metric_source_domain_smooth (I := I) Φc k
        let : SigmaCompactSpace (MetricSourceDomain (I := I) Φc k) :=
          metric_source_domain_sigma_compact (I := I) Φc k
            (PointedRiemannianConvergenceMaps.isSigmaCompact_source
              (I := I) Φc k)
        with_unfolding_all
          convert metricCovDerivNorm_pullback (I := I) q
            ((g (j₀ + k)).restrictOpen (I := I) (tailBallOpen b j₀ k))
            (gTail k) F x using 1 ; rfl
      rw [hpull]
      exact hcov k (F x)
  let XTail := X.subseq (fun n => σ (j₀ + n))
  let bTail : forall n, (XTail.obj n).M := fun n =>
    (S.toSeqSystem.map (Nat.zero_le n) (tailCenter b j₀ 0) :
      (X.obj (σ (j₀ + n))).M)
  let Φr : PointedRiemannianConvergenceMaps (I := I) (XTail.repoint bTail) L id := by
    change PointedRiemannianConvergenceMaps (I := I)
      (chainAmbientSeq (I := I) j₀ (tailBallOpen b j₀) S
        (tailCenter b j₀ 0) g) L id
    exact chainAmbientMaps (I := I) j₀ (tailBallOpen b j₀) S
      (tailCenter b j₀ 0) g gTail hgTail
  have hbase' : forall n,
      letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : TopologicalSpace (XTail.obj (id n)).M := (XTail.obj (id n)).topology
      letI : ChartedSpace H (XTail.obj (id n)).M := (XTail.obj (id n)).charted
      Φr.partialDiffeomorph n L.basepoint = (XTail.obj (id n)).basepoint := by
    intro n
    with_unfolding_all
      change ((Function.invFun (S.toSeqSystem.incl n)
          (S.toSeqSystem.incl 0 (tailCenter b j₀ 0)) :
            tailBallOpen b j₀ n) :
          (X.obj (σ (j₀ + n))).M) =
        (X.obj (σ (j₀ + n))).basepoint
    have hfirst :=
      congrArg Subtype.val
        (S.invIncl_incl_le (Nat.zero_le n) (tailCenter b j₀ 0))
    with_unfolding_all rw [hfirst]
    exact congrArg Subtype.val
      (tail_ball_system_map_center (I := I) b Ψ hbase g (by
        intro j x v
        with_unfolding_all exact
          (DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
            (I := I) (g j) x v)) j₀ D₀ n)
  let hconverges : PointedRiemannianConverges (I := I) X L
      (fun n => σ (j₀ + n)) maps :=
    tailMemberConvergence (I := I) P σ Ψ hbase j₀ D₀ gTail hgTail hchain
  have hconverges_ref : HasLimitReferenceMetric (I := I) hconverges := by
    intro k
    with_unfolding_all exact hchain_ref k
  have hconverges_domain : forall k : Nat,
      hconverges.metrics.domain k =
        CanonicalMetricCompactness.canonicalSourceData (I := I) maps k := by
    intro k
    change MetricSourceData.ofSubseq (I := I) (fun n => σ (j₀ + n)) k
        (MetricSourceData.unrepoint (I := I) bTail hbase' k
          (hchain.metrics.domain k)) =
      CanonicalMetricCompactness.canonicalSourceData (I := I) maps k
    rw [hchain_domain k]
    rfl
  let mc : MetricCompactLimit (I := I) X :=
    { subseq := fun n => σ (j₀ + n)
      strictMono := fun _ _ hnm => hσ (Nat.add_lt_add_left hnm j₀)
      limit := L
      limit_complete := hcomplete
      maps := maps
      convergence := hconverges }
  have hbounds : HasUniformPullbackMetricBounds (I := I) hconverges := by
    with_unfolding_all exact hchain_bounds
  let C : CanonicalMetricCompactness (I := I) X :=
    { compactness := mc
      domain_eq_canonical := by
        intro k
        exact hconverges_domain k
      reference_eq_limit := by
        intro k
        exact hconverges_ref k
      uniformly_equivalent := by
        simpa only [mc] using hbounds.1
      covariant_derivatives_bounded := by
        simpa only [mc] using hbounds.2 }
  have hsource : ∀ n, IsCompact (closure (Set.range (S.toSeqSystem.incl n))) ∧
      closure (Set.range (S.toSeqSystem.incl n)) ⊆
        Set.range (S.toSeqSystem.incl (n + 1)) := by
    intro n
    obtain ⟨K, hK, hmap⟩ := tail_ball_system_step_range_compact
      (I := I) b Ψ hbase g (by
        intro j x v
        with_unfolding_all exact
          (DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
            (I := I) (g j) x v)) j₀ hj₀ D₀ n
    have hcompactImage : IsCompact
        (S.toSeqSystem.incl (n + 1) '' K) :=
      hK.image (S.toSeqSystem.continuous_incl (n + 1))
    have hclosedImage : IsClosed (S.toSeqSystem.incl (n + 1) '' K) :=
      hcompactImage.isClosed
    have hsource : Set.range (S.toSeqSystem.incl n) ⊆
        S.toSeqSystem.incl (n + 1) '' K := by
      rintro z ⟨x, rfl⟩
      rw [← S.toSeqSystem.incl_comp (Nat.le_succ n) x]
      exact ⟨S.toSeqSystem.map (Nat.le_succ n) x,
        hmap ⟨x, rfl⟩, rfl⟩
    have hclosure : closure (Set.range (S.toSeqSystem.incl n)) ⊆
        S.toSeqSystem.incl (n + 1) '' K :=
      closure_minimal hsource hclosedImage
    have hcompact : IsCompact (closure (Set.range (S.toSeqSystem.incl n))) :=
      hcompactImage.of_isClosed_subset isClosed_closure hclosure
    have hnext : closure (Set.range (S.toSeqSystem.incl n)) ⊆
        Set.range (S.toSeqSystem.incl (n + 1)) := by
      intro z hz
      obtain ⟨y, _hyK, rfl⟩ := hclosure hz
      exact ⟨y, rfl⟩
    exact ⟨hcompact, hnext⟩
  let : ∀ n, PreconnectedSpace (tailBallOpen b j₀ n) := fun n =>
    tail_ball_preconnected (I := I) b j₀ n
  refine
    { canonical := C
      connected := ?_
      source_precompact := ?_
      source_connected := ?_
      source_closure_subset := ?_ }
  · change ConnectedSpace S.toSeqSystem.Lim
    infer_instance
  · intro n
    change IsCompact (closure (Set.range (S.toSeqSystem.incl n)))
    exact (hsource n).1
  · intro n
    change IsConnected (Set.range (S.toSeqSystem.incl n))
    exact ⟨Set.range_nonempty _, isPreconnected_range (S.toSeqSystem.continuous_incl n)⟩
  · intro n
    change closure (Set.range (S.toSeqSystem.incl n)) ⊆
      Set.range (S.toSeqSystem.incl (n + 1))
    exact (hsource n).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.connectedCanonicalMetricCompactnessOfConvergentChain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.connectedCanonicalMetricCompactnessOfConvergentChain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.connectedCanonicalMetricCompactnessOfConvergentChain ``Submission.DifferentialGeometry.CheegerGromovCompactness.connectedCanonicalMetricCompactnessOfConvergentChain

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private opaque connectedCanonicalMetricCompactness
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (P : ∀ k, ProperMetricOn (I := I) (X.obj k))
    (B : HasPairwiseApproximateIsometries (X := X) P) :
    ConnectedCanonicalMetricCompactness (I := I) X := by
  classical
  let hdirectedEx := exists_directed_approximate_isometry_subsequence (I := I) P B
  let σ := Classical.choose hdirectedEx
  have hσpack := Classical.choose_spec hdirectedEx
  have hσ : StrictMono σ := hσpack.1
  have hdirected := hσpack.2
  letI : ∀ j, TopologicalSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).topology
  letI : ∀ j, ChartedSpace H (X.obj (σ j)).M := fun j => (X.obj (σ j)).charted
  letI : ∀ j, IsManifold I ∞ (X.obj (σ j)).M := fun j => (X.obj (σ j)).smooth
  letI : ∀ j, T2Space (X.obj (σ j)).M := fun j => (X.obj (σ j)).t2
  letI : ∀ j, SigmaCompactSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).sigmaCompact
  letI : ∀ j, MetricSpace (X.obj (σ j)).M := fun j => (P (σ j)).ms
  let Ψ := Classical.choose hdirected
  have hΨpack := Classical.choose_spec hdirected
  have hbase := hΨpack.1
  have hdata := hΨpack.2
  letI : ∀ j, MetricSpace (X.obj (σ j)).M := fun j =>
    ProperMetricOn.alignedMetricSpace (X.obj (σ j)) (P (σ j))
  letI : ∀ j, IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.obj (σ j)).M := fun j => by
    change IsManifold I ∞ (X.obj (σ j)).M
    infer_instance
  letI : ∀ j, Bundle.RiemannianBundle
      (fun x : (X.obj (σ j)).M => TangentSpace I x) :=
    fun j => (X.obj (σ j)).riemBundle
  letI : ∀ j, IsRiemannianManifold I (X.obj (σ j)).M := fun j => by
    refine ⟨fun x y => ?_⟩
    have hreal := (P (σ j)).realizes x y
    rw [edist_dist, ← hreal]
    rfl
  letI : ∀ j, ProperSpace (X.obj (σ j)).M := fun j =>
    alignedProper (I := I) (σ j) (P (σ j))
  let b := fun j => (X.obj (σ j)).basepoint
  let g := fun j => (X.obj (σ j)).metric
  have hD : Nonempty (ConvergentMetricChain (I := I) b Ψ g) := by
    obtain ⟨j₀, hj₀, D₀, hU, hmap, _φ, _hφ, gInf, _hconv, hclose, hstep⟩ :=
      exists_compatible_chain_pullback_metric_limits (I := I) b Ψ hbase g (by
        intro j x v
        with_unfolding_all exact
          (DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
            (I := I) (g j) x v)) hdata
    exact ⟨
      { start := j₀
        one_le_start := hj₀
        zeroOrderApproximation := D₀
        sourceCoverage := hU
        successorCoverage := hmap
        limitMetric := gInf
        derivativesConverge := hclose
        successorIsometry := hstep }⟩
  let D := Classical.choice hD
  exact connectedCanonicalMetricCompactnessOfConvergentChain (I := I) P σ hσ Ψ hbase D

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.connectedCanonicalMetricCompactness
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.connectedCanonicalMetricCompactness target :: scope.openDecls } }

noncomputable def canonicalMetricCompactness
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (P : ∀ k, ProperMetricOn (I := I) (X.obj k))
    (B : HasPairwiseApproximateIsometries (X := X) P) :
    CanonicalMetricCompactness (I := I) X :=
  (connectedCanonicalMetricCompactness (I := I) P B).canonical

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.canonicalMetricCompactness then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.canonicalMetricCompactness"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.canonicalMetricCompactness ``Submission.DifferentialGeometry.CheegerGromovCompactness.canonicalMetricCompactness

omit [NeZero (Module.finrank ℝ E)] in
theorem canonical_metric_compactness_connected
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (P : ∀ k, ProperMetricOn (I := I) (X.obj k))
    (B : HasPairwiseApproximateIsometries (X := X) P) :
    let C := canonicalMetricCompactness (I := I) P B
    letI : TopologicalSpace C.compactness.limit.M := C.compactness.limit.topology
    ConnectedSpace C.compactness.limit.M := by
  with_unfolding_all exact
    (connectedCanonicalMetricCompactness (I := I) P B).connected

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.canonical_metric_compactness_connected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.canonical_metric_compactness_connected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.canonical_metric_compactness_connected ``Submission.DifferentialGeometry.CheegerGromovCompactness.canonical_metric_compactness_connected

omit [NeZero (Module.finrank ℝ E)] in
theorem canonical_metric_compactness_source_precompact
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (P : ∀ k, ProperMetricOn (I := I) (X.obj k))
    (B : HasPairwiseApproximateIsometries (X := X) P) :
    let C := canonicalMetricCompactness (I := I) P B
    letI : TopologicalSpace C.compactness.limit.M := C.compactness.limit.topology
    ∀ n, IsCompact (closure (C.compactness.maps.source n)) := by
  with_unfolding_all exact
    (connectedCanonicalMetricCompactness (I := I) P B).source_precompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.canonical_metric_compactness_source_precompact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.canonical_metric_compactness_source_precompact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.canonical_metric_compactness_source_precompact ``Submission.DifferentialGeometry.CheegerGromovCompactness.canonical_metric_compactness_source_precompact

omit [NeZero (Module.finrank ℝ E)] in
theorem canonical_metric_compactness_source_connected
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (P : ∀ k, ProperMetricOn (I := I) (X.obj k))
    (B : HasPairwiseApproximateIsometries (X := X) P) :
    let C := canonicalMetricCompactness (I := I) P B
    letI : TopologicalSpace C.compactness.limit.M := C.compactness.limit.topology
    ∀ n, IsConnected (C.compactness.maps.source n) := by
  with_unfolding_all exact
    (connectedCanonicalMetricCompactness (I := I) P B).source_connected

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.canonical_metric_compactness_source_connected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.canonical_metric_compactness_source_connected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.canonical_metric_compactness_source_connected ``Submission.DifferentialGeometry.CheegerGromovCompactness.canonical_metric_compactness_source_connected

omit [NeZero (Module.finrank ℝ E)] in
theorem canonical_metric_compactness_source_closure_subset
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (P : ∀ k, ProperMetricOn (I := I) (X.obj k))
    (B : HasPairwiseApproximateIsometries (X := X) P) :
    let C := canonicalMetricCompactness (I := I) P B
    letI : TopologicalSpace C.compactness.limit.M := C.compactness.limit.topology
    ∀ n, closure (C.compactness.maps.source n) ⊆
      C.compactness.maps.source (n + 1) := by
  with_unfolding_all exact
    (connectedCanonicalMetricCompactness (I := I) P B).source_closure_subset

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.canonical_metric_compactness_source_closure_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.canonical_metric_compactness_source_closure_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.canonical_metric_compactness_source_closure_subset ``Submission.DifferentialGeometry.CheegerGromovCompactness.canonical_metric_compactness_source_closure_subset

noncomputable def metricCompactnessOfPairwiseApproximateIsometries
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (P : ∀ k, ProperMetricOn (I := I) (X.obj k))
    (B : HasPairwiseApproximateIsometries (X := X) P) :
    MetricCompactLimit (I := I) X :=
  (canonicalMetricCompactness (I := I) P B).compactness

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.metricCompactnessOfPairwiseApproximateIsometries then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.metricCompactnessOfPairwiseApproximateIsometries"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.metricCompactnessOfPairwiseApproximateIsometries ``Submission.DifferentialGeometry.CheegerGromovCompactness.metricCompactnessOfPairwiseApproximateIsometries

def HasSubsequencePairwiseApproximateIsometries
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (P : ∀ k, ProperMetricOn (I := I) (X.obj k)) : Prop :=
  ∃ σ : Nat → Nat, StrictMono σ ∧
    HasPairwiseApproximateIsometries (I := I) (X := X.subseq σ) (fun k => P (σ k))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HasSubsequencePairwiseApproximateIsometries then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HasSubsequencePairwiseApproximateIsometries"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HasSubsequencePairwiseApproximateIsometries ``Submission.DifferentialGeometry.CheegerGromovCompactness.HasSubsequencePairwiseApproximateIsometries

theorem exists_connectedCanonicalMetricCompactness_of_hasSubsequencePairwiseApproximateIsometries
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconnected : ∀ i : Nat,
      let _ : TopologicalSpace (X.obj i).M := (X.obj i).topology
      ConnectedSpace (X.obj i).M)
    (hsub : HasSubsequencePairwiseApproximateIsometries (I := I) X
      (fun k => properMetricOn (I := I) (X.obj k)
        (hcomplete.complete k) (hconnected k))) :
    Nonempty (ConnectedCanonicalMetricCompactness (I := I) X) := by
  obtain ⟨σ, hσ, hpair⟩ := hsub
  let Pσ : ∀ k : Nat, ProperMetricOn (I := I) ((X.subseq σ).obj k) :=
    fun k => properMetricOn (I := I) ((X.subseq σ).obj k)
      ((hcomplete.subseq σ).complete k)
      (PointedRiemannianSeq.connected_subseq hconnected σ k)
  have hpair' : HasPairwiseApproximateIsometries (I := I) (X := X.subseq σ) Pσ := hpair
  let Cσ : CanonicalMetricCompactness (I := I) (X.subseq σ) :=
    canonicalMetricCompactness (I := I) Pσ hpair'
  have hconnσ := canonical_metric_compactness_connected (I := I) Pσ hpair'
  let C : CanonicalMetricCompactness (I := I) X := Cσ.ofSubsequence σ hσ
  refine ⟨
    { canonical := C
      connected := ?_
      source_precompact := ?_
      source_connected := ?_
      source_closure_subset := ?_ }⟩
  · have hlim : C.compactness.limit = Cσ.compactness.limit := rfl
    rw [hlim]
    exact hconnσ
  · with_unfolding_all exact
      canonical_metric_compactness_source_precompact (I := I) Pσ hpair'
  · with_unfolding_all exact
      canonical_metric_compactness_source_connected (I := I) Pσ hpair'
  · with_unfolding_all exact
      canonical_metric_compactness_source_closure_subset (I := I) Pσ hpair'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.exists_connectedCanonicalMetricCompactness_of_hasSubsequencePairwiseApproximateIsometries then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.exists_connectedCanonicalMetricCompactness_of_hasSubsequencePairwiseApproximateIsometries"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.exists_connectedCanonicalMetricCompactness_of_hasSubsequencePairwiseApproximateIsometries ``Submission.DifferentialGeometry.CheegerGromovCompactness.exists_connectedCanonicalMetricCompactness_of_hasSubsequencePairwiseApproximateIsometries

end CheegerGromovCompactness
end DifferentialGeometry
