import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedSectionalCurvature
import Submission.DifferentialGeometry.Geometry.Curvature.Algebraic.CurvatureOperatorConeMetric

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Filter
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology _root_.BigOperators

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
  {L : PointedRiemannianManifold.{u, uE, uH} (I := I)} {subseq : ℕ → ℕ}
  {Phi : PointedRiemannianConvergenceMaps (I := I) X L subseq}

local instance pointedOperatorLimitTopology : TopologicalSpace L.M := L.topology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedOperatorLimitTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedOperatorLimitTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedOperatorLimitTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedOperatorLimitTopology
local instance pointedOperatorLimitCharted : ChartedSpace H L.M := L.charted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedOperatorLimitCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedOperatorLimitCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedOperatorLimitCharted ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedOperatorLimitCharted
local instance pointedOperatorLimitSmooth : IsManifold I ∞ L.M := L.smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedOperatorLimitSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedOperatorLimitSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedOperatorLimitSmooth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedOperatorLimitSmooth
local instance pointedOperatorLimitT2 : T2Space L.M := L.t2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedOperatorLimitT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedOperatorLimitT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedOperatorLimitT2 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedOperatorLimitT2
local instance pointedOperatorLimitSigma : SigmaCompactSpace L.M := L.sigmaCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedOperatorLimitSigma then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedOperatorLimitSigma"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedOperatorLimitSigma ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedOperatorLimitSigma

local instance pointedOperatorApproxTopology (k : ℕ) :
    TopologicalSpace (X.obj k).M := (X.obj k).topology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedOperatorApproxTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedOperatorApproxTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedOperatorApproxTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedOperatorApproxTopology
local instance pointedOperatorApproxCharted (k : ℕ) :
    ChartedSpace H (X.obj k).M := (X.obj k).charted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedOperatorApproxCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedOperatorApproxCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedOperatorApproxCharted ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedOperatorApproxCharted
local instance pointedOperatorApproxSmooth (k : ℕ) :
    IsManifold I ∞ (X.obj k).M := (X.obj k).smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedOperatorApproxSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedOperatorApproxSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedOperatorApproxSmooth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedOperatorApproxSmooth
local instance pointedOperatorApproxT2 (k : ℕ) : T2Space (X.obj k).M := (X.obj k).t2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedOperatorApproxT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedOperatorApproxT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedOperatorApproxT2 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedOperatorApproxT2
local instance pointedOperatorApproxSigma (k : ℕ) :
    SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedOperatorApproxSigma then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedOperatorApproxSigma"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedOperatorApproxSigma ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedOperatorApproxSigma

theorem pointedCurvatureOperatorQuadraticEval_tendsto_of_canonical_metric_convergence
    (hconv : ∀ K : Set L.M, IsCompact K →
      metricSourceConvergesOn (I := I) Phi
        (CanonicalMetricCompactness.canonicalSourceData Phi) K 2)
    (x : L.M) (n : ℕ) (c : Fin n → ℝ) (v w : Fin n → TangentSpace I x) :
    Tendsto (fun k => algebraicCurvatureOperatorQuadraticEval (I := I)
        (metricAlgebraicCurvatureTensorAt (I := I)
          (X.obj (subseq k)).metric (Phi.map k x)) c
        (fun i => mfderiv I I (Phi.map k) x (v i))
        (fun i => mfderiv I I (Phi.map k) x (w i))) _root_.Filter.atTop
      (𝓝 (algebraicCurvatureOperatorQuadraticEval (I := I)
        (metricAlgebraicCurvatureTensorAt (I := I) L.metric x) c v w)) := by
  change _root_.Filter.Tendsto (fun k => ∑ i : Fin n, ∑ j : Fin n, c i * c j *
      metricRm04StandardAt (I := I) (X.obj (subseq k)).metric (Phi.map k x)
        (mfderiv I I (Phi.map k) x (v i)) (mfderiv I I (Phi.map k) x (w i))
        (mfderiv I I (Phi.map k) x (w j)) (mfderiv I I (Phi.map k) x (v j))) _root_.Filter.atTop
    (𝓝 (∑ i : Fin n, ∑ j : Fin n, c i * c j *
      metricRm04StandardAt (I := I) L.metric x (v i) (w i) (w j) (v j)))
  refine tendsto_finsetSum _ fun i _ => ?_
  refine tendsto_finsetSum _ fun j _ => ?_
  exact (pointedRm04_tendsto_of_canonical_metric_convergence
    hconv x (v i) (w i) (w j) (v j)).const_mul (c i * c j)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedCurvatureOperatorQuadraticEval_tendsto_of_canonical_metric_convergence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedCurvatureOperatorQuadraticEval_tendsto_of_canonical_metric_convergence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedCurvatureOperatorQuadraticEval_tendsto_of_canonical_metric_convergence ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedCurvatureOperatorQuadraticEval_tendsto_of_canonical_metric_convergence

theorem curvatureOperator_nonnegative_of_pointed_canonical_convergence
    (hconv : ∀ K : Set L.M, IsCompact K →
      metricSourceConvergesOn (I := I) Phi
        (CanonicalMetricCompactness.canonicalSourceData Phi) K 2)
    (hoperator : ∀ K : Set L.M, IsCompact K →
      ∀ᶠ k in _root_.Filter.atTop, ∀ y ∈ K, y ∈ Phi.source k →
        metricAlgebraicCurvatureTensorAt (I := I)
            (X.obj (subseq k)).metric (Phi.map k y) ∈
          algebraicCurvatureOperatorNonnegativeCone (I := I)) :
    ∀ x : L.M, metricAlgebraicCurvatureTensorAt (I := I) L.metric x ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) := by
  intro x
  apply mem_algebraicCurvatureOperatorNonnegativeCone.mpr
  intro n c v w
  have hc := pointedCurvatureOperatorQuadraticEval_tendsto_of_canonical_metric_convergence
    hconv x n c v w
  obtain ⟨k0, hk0⟩ := Phi.source_subset (K := {x}) isCompact_singleton
  have hs : ∀ᶠ k in _root_.Filter.atTop, x ∈ Phi.source k := by
    filter_upwards [_root_.Filter.eventually_ge_atTop k0] with k hk
    exact hk0 k hk (Set.mem_singleton x)
  apply ge_of_tendsto hc
  filter_upwards [hoperator {x} isCompact_singleton, hs] with k hk hx
  exact (mem_algebraicCurvatureOperatorNonnegativeCone.mp
    (hk x (Set.mem_singleton x) hx)) n c
      (fun i => mfderiv I I (Phi.map k) x (v i))
      (fun i => mfderiv I I (Phi.map k) x (w i))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.curvatureOperator_nonnegative_of_pointed_canonical_convergence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.curvatureOperator_nonnegative_of_pointed_canonical_convergence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.curvatureOperator_nonnegative_of_pointed_canonical_convergence ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.curvatureOperator_nonnegative_of_pointed_canonical_convergence

theorem curvatureOperator_nonnegative_of_canonical_metricCGConvergence
    (C : MetricConvergenceData (I := I) Phi)
    (hdomain : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Phi k)
    (hoperator : ∀ K : Set L.M, IsCompact K →
      ∀ᶠ k in _root_.Filter.atTop, ∀ y ∈ K, y ∈ Phi.source k →
        metricAlgebraicCurvatureTensorAt (I := I)
            (X.obj (subseq k)).metric (Phi.map k y) ∈
          algebraicCurvatureOperatorNonnegativeCone (I := I)) :
    ∀ x : L.M, metricAlgebraicCurvatureTensorAt (I := I) L.metric x ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) := by
  have hD : C.domain = CanonicalMetricCompactness.canonicalSourceData Phi := funext hdomain
  have hc : ∀ K : Set L.M, IsCompact K →
      metricSourceConvergesOn (I := I) Phi
        (CanonicalMetricCompactness.canonicalSourceData Phi) K 2 := by
    intro K hK
    have ht := C.converges K hK 2
    rw [hD] at ht
    exact ht
  exact curvatureOperator_nonnegative_of_pointed_canonical_convergence hc hoperator

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.curvatureOperator_nonnegative_of_canonical_metricCGConvergence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.curvatureOperator_nonnegative_of_canonical_metricCGConvergence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.curvatureOperator_nonnegative_of_canonical_metricCGConvergence ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.curvatureOperator_nonnegative_of_canonical_metricCGConvergence

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
