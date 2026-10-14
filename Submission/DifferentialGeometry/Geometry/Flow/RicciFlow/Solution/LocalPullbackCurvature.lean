import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.LocalPullback
import Submission.DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalNorm
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Ricci.Tower

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

open _root_.Set _root_.Function _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]
  {D : RealTimeInterval}

theorem SolutionOn.localPullback_curvature_derivative_normSq
    (S : SolutionOn (I := I) (M := N) D) (p : M → N)
    (hp : IsLocalDiffeomorph I I ∞ p) (t : ℝ) (k : ℕ) (x : M) :
    normSq0S ((S.localPullback p hp).base.metric t) x (4 + k)
      (iterCov ((S.localPullback p hp).base.metric t) 4
        (metricRm04 ((S.localPullback p hp).base.metric t)) k x) =
    normSq0S (S.base.metric t) (p x) (4 + k)
      (iterCov (S.base.metric t) 4 (metricRm04 (S.base.metric t)) k (p x)) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact Geometry.Tensor.normSq0S_iterCov_localPullMetric (S.base.metric t) p hp
    (metricRm04 (localPullMetric (S.base.metric t) p hp)) (metricRm04 (S.base.metric t))
    (fun y v => metricRm04StandardAt_localPullMetric (S.base.metric t) p hp
      y (v 0) (v 1) (v 2) (v 3)) k x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.SolutionOn.localPullback_curvature_derivative_normSq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.SolutionOn.localPullback_curvature_derivative_normSq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.SolutionOn.localPullback_curvature_derivative_normSq ``Submission.DifferentialGeometry.PDE.RicciFlow.SolutionOn.localPullback_curvature_derivative_normSq

variable [I.Boundaryless]

theorem SolutionOn.localPullback_ricci_derivative_normSq
    (S : SolutionOn (I := I) (M := N) D) (p : M → N)
    (hp : IsLocalDiffeomorph I I ∞ p) (t : ℝ) (k : ℕ) (x : M) :
    normSq0S ((S.localPullback p hp).base.metric t) x (2 + k)
      (ricCovTower ((S.localPullback p hp).base.metric t)
        ((S.localPullback p hp).base.metric t) k x) =
    normSq0S (S.base.metric t) (p x) (2 + k)
      (ricCovTower (S.base.metric t) (S.base.metric t) k (p x)) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact Geometry.Tensor.normSq0S_iterCov_localPullMetric (S.base.metric t) p hp
    (metricRicci (localPullMetric (S.base.metric t) p hp)) (metricRicci (S.base.metric t))
    (fun y v => Geometry.Tensor.metricRicciAt_localPullMetric (S.base.metric t) p hp y v) k x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.SolutionOn.localPullback_ricci_derivative_normSq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.SolutionOn.localPullback_ricci_derivative_normSq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.SolutionOn.localPullback_ricci_derivative_normSq ``Submission.DifferentialGeometry.PDE.RicciFlow.SolutionOn.localPullback_ricci_derivative_normSq

theorem SolutionOn.movingShiBoundOn_localPullback
    (S : SolutionOn (I := I) (M := N) D) (p : M → N)
    (hp : IsLocalDiffeomorph I I ∞ p) {U : Set N} {V : Set M}
    {a b K : ℝ} {k : ℕ} (hmap : _root_.Set.MapsTo p V U)
    (hbound : MovingShiBoundOn U a b (fun _ t => S.base.metric t) k K) :
    MovingShiBoundOn V a b (fun _ t => (S.localPullback p hp).base.metric t) k K := by
  intro j hj i t ht x hx
  rw [S.localPullback_ricci_derivative_normSq p hp t j x]
  exact hbound j hj i t ht (p x) (hmap hx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.SolutionOn.movingShiBoundOn_localPullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.SolutionOn.movingShiBoundOn_localPullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.SolutionOn.movingShiBoundOn_localPullback ``Submission.DifferentialGeometry.PDE.RicciFlow.SolutionOn.movingShiBoundOn_localPullback

end DifferentialGeometry.PDE.RicciFlow
