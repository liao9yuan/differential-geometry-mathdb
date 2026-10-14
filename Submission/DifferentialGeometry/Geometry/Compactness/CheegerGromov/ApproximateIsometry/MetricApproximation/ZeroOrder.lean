import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.MetricApproximation.Defs

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry.CheegerGromovCompactness

open scoped _root_.Manifold _root_.ContDiff

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]

variable {N : Type u} [TopologicalSpace N] [ChartedSpace H N]
  [T2Space N] [IsManifold I ∞ N] [SigmaCompactSpace N]

def MapMetricApproximationBoundsOn.toMetricApproximationZero
    {K : Set M} {c0 cov eps : ℝ} {p : ℕ} {Phi : M → N}
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (D : MapMetricApproximationBoundsOn (I := I) K c0 cov p Phi g h)
    (heps0 : 0 < eps) (heps1 : eps < 1) (hc0 : c0 ≤ eps) :
    MapMetricApproximationOn (I := I) K eps 0 Phi g h where
  eps_pos := heps0
  eps_lt_one := heps1
  smoothOn := D.smoothOn
  pullback := D.pullback
  pullback_apply := D.pullback_apply
  c0_small := fun x hx => le_trans (D.c0_small x hx) hc0
  cov_deriv_small := fun a h1 h2 => by omega

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MapMetricApproximationBoundsOn.toMetricApproximationZero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MapMetricApproximationBoundsOn.toMetricApproximationZero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MapMetricApproximationBoundsOn.toMetricApproximationZero ``Submission.DifferentialGeometry.CheegerGromovCompactness.MapMetricApproximationBoundsOn.toMetricApproximationZero

def PartialDiffeomorphMetricApproximationBounds.toMetricApproximationZero
    {K : Set M} {c0 cov eps : ℝ} {p : ℕ}
    {Phi : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞)}
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (D : PartialDiffeomorphMetricApproximationBounds (I := I) K c0 cov p Phi g h)
    (heps0 : 0 < eps) (heps1 : eps < 1) (hc0 : c0 ≤ eps) :
    PartialDiffeomorphMetricApproximation (I := I) K eps 0 Phi g h where
  source_sub := D.source_sub
  forward := D.forward.toMetricApproximationZero heps0 heps1 hc0
  reverse := D.reverse.toMetricApproximationZero heps0 heps1 hc0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PartialDiffeomorphMetricApproximationBounds.toMetricApproximationZero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PartialDiffeomorphMetricApproximationBounds.toMetricApproximationZero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PartialDiffeomorphMetricApproximationBounds.toMetricApproximationZero ``Submission.DifferentialGeometry.CheegerGromovCompactness.PartialDiffeomorphMetricApproximationBounds.toMetricApproximationZero

end DifferentialGeometry.CheegerGromovCompactness
