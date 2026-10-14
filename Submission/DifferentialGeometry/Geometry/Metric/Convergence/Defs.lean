import Submission.DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open scoped _root_.Manifold _root_.ContDiff _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M]

noncomputable def metricTensorErrorNorm
    (A :
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (g : SmoothRiemannianMetric I M) (x : M) : Real :=
  Real.sqrt
    (Tensor0SBundle.normSq0S (I := I) g x 2
      (A x - Tensor0SBundle.metricTensorField (I := I) g x))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.metricTensorErrorNorm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.metricTensorErrorNorm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.metricTensorErrorNorm ``Submission.DifferentialGeometry.CheegerGromovCompactness.metricTensorErrorNorm

noncomputable def metricDiffCovDerivAt
    (a : Nat) (gk gInf gRef : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SBundle.Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (a + 2) x :=
  metricCovDeriv (I := I) gk gRef a x -
    metricCovDeriv (I := I) gInf gRef a x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.metricDiffCovDerivAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.metricDiffCovDerivAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.metricDiffCovDerivAt ``Submission.DifferentialGeometry.CheegerGromovCompactness.metricDiffCovDerivAt

noncomputable def metricDerivNorm
    (a : Nat) (gk gInf gRef : SmoothRiemannianMetric I M) (x : M) : Real :=
  Real.sqrt
    (Tensor0SBundle.normSq0S (I := I) gRef x (a + 2)
      (metricDiffCovDerivAt (I := I) a gk gInf gRef x))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.metricDerivNorm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.metricDerivNorm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.metricDerivNorm ``Submission.DifferentialGeometry.CheegerGromovCompactness.metricDerivNorm

noncomputable def metricDerivNormSupOn
    (K : Set M) (p : Nat)
    (gk gInf gRef : SmoothRiemannianMetric I M) : Real :=
  _root_.SupSet.sSup {r : Real |
    exists a : Nat, a <= p ∧
      exists x : M, x ∈ K ∧
        metricDerivNorm (I := I) a gk gInf gRef x = r}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.metricDerivNormSupOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.metricDerivNormSupOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.metricDerivNormSupOn ``Submission.DifferentialGeometry.CheegerGromovCompactness.metricDerivNormSupOn

def MetricCPConvergenceOn
    (K : Set M) (p : Nat)
    (gSeq : Nat -> SmoothRiemannianMetric I M)
    (gInf gRef : SmoothRiemannianMetric I M) : Prop :=
  forall ε : Real, 0 < ε ->
    exists k0 : Nat, forall k : Nat, k0 <= k ->
      metricDerivNormSupOn (I := I) K p (gSeq k) gInf gRef < ε

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MetricCPConvergenceOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MetricCPConvergenceOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MetricCPConvergenceOn ``Submission.DifferentialGeometry.CheegerGromovCompactness.MetricCPConvergenceOn

def MetricCInfConvergenceOn
    (K : Set M)
    (gSeq : Nat -> SmoothRiemannianMetric I M)
    (gInf gRef : SmoothRiemannianMetric I M) : Prop :=
  forall p : Nat, MetricCPConvergenceOn (I := I) K p gSeq gInf gRef

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MetricCInfConvergenceOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MetricCInfConvergenceOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MetricCInfConvergenceOn ``Submission.DifferentialGeometry.CheegerGromovCompactness.MetricCInfConvergenceOn

def MetricCInfConvergenceOnCompacts
    (gSeq : Nat -> SmoothRiemannianMetric I M)
    (gInf gRef : SmoothRiemannianMetric I M) : Prop :=
  forall K : Set M, forall _hK : IsCompact K,
    MetricCInfConvergenceOn (I := I) K gSeq gInf gRef

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MetricCInfConvergenceOnCompacts then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MetricCInfConvergenceOnCompacts"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MetricCInfConvergenceOnCompacts ``Submission.DifferentialGeometry.CheegerGromovCompactness.MetricCInfConvergenceOnCompacts

structure MetricCInfConvergence
    (I : ModelWithCorners Real E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [IsManifold I ∞ M]
    [SigmaCompactSpace M] where
  gSeq : Nat -> SmoothRiemannianMetric I M
  gInf : SmoothRiemannianMetric I M
  gRef : SmoothRiemannianMetric I M
  converges : MetricCInfConvergenceOnCompacts (I := I) gSeq gInf gRef

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MetricCInfConvergence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MetricCInfConvergence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MetricCInfConvergence ``Submission.DifferentialGeometry.CheegerGromovCompactness.MetricCInfConvergence

end CheegerGromovCompactness
end DifferentialGeometry
