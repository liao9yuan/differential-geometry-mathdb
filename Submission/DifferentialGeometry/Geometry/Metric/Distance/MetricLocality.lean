import Submission.DifferentialGeometry.Geometry.Comparison.DistanceHessianLocal
import Submission.DifferentialGeometry.Geometry.Metric.Distance.Ball

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal

namespace DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem riemannianClosedBallOf_subset_of_add_radius_le
    (g : SmoothRiemannianMetric I M) {p x : M} {r ρ R : ℝ}
    (hr : 0 ≤ r) (hρ : 0 ≤ ρ) (hR : r + ρ ≤ R)
    (hx : x ∈ riemannianClosedBallOf g p r) :
    riemannianClosedBallOf g x ρ ⊆ riemannianClosedBallOf g p R := by
  intro y hy
  change riemannianEDistOf g p y ≤ ENNReal.ofReal R
  calc
    _ ≤ riemannianEDistOf g p x + riemannianEDistOf g x y :=
      riemannianEDistOf_triangle g p x y
    _ ≤ ENNReal.ofReal r + ENNReal.ofReal ρ := add_le_add hx hy
    _ = ENNReal.ofReal (r + ρ) := (ENNReal.ofReal_add hr hρ).symm
    _ ≤ ENNReal.ofReal R := ENNReal.ofReal_le_ofReal hR

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.riemannianClosedBallOf_subset_of_add_radius_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.riemannianClosedBallOf_subset_of_add_radius_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.riemannianClosedBallOf_subset_of_add_radius_le ``Submission.DifferentialGeometry.riemannianClosedBallOf_subset_of_add_radius_le

theorem riemannianBallOf_eq_of_eqOn_outer_closedBall
    (g g' : SmoothRiemannianMetric I M) {p x : M} {r ρ R : ℝ}
    (hr : 0 ≤ r) (hρ : 0 ≤ ρ) (hR : r + ρ ≤ R)
    (hx : x ∈ riemannianClosedBallOf g p r)
    (heq : ∀ z ∈ riemannianClosedBallOf g p R, g'.inner z = g.inner z)
    (hle : ∀ z (v : TangentSpace I z), g.inner z v v ≤ g'.inner z v v) :
    riemannianBallOf g' x ρ = riemannianBallOf g x ρ := by
  have hbuffer := riemannianClosedBallOf_subset_of_add_radius_le g hr hρ hR hx
  ext y
  constructor
  · intro hy
    exact (edistOf_mono g g' hle x y).trans_lt hy
  · intro hy
    have hd := riemannianEDistOf_eq_of_eqOn_ball g g' hbuffer heq hle hy
    change riemannianEDistOf g' x y < ENNReal.ofReal ρ
    rwa [hd]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.riemannianBallOf_eq_of_eqOn_outer_closedBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.riemannianBallOf_eq_of_eqOn_outer_closedBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.riemannianBallOf_eq_of_eqOn_outer_closedBall ``Submission.DifferentialGeometry.riemannianBallOf_eq_of_eqOn_outer_closedBall

end DifferentialGeometry
