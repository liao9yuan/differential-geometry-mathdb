import Submission.DifferentialGeometry.Geometry.Metric.Distance.Finiteness
import Mathlib.Tactic.Linarith

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
open _root_.Submission.DifferentialGeometry
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal

namespace DifferentialGeometry.Geometry.Metric

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]


theorem riemannianDistance_toReal_lipschitz
    [PreconnectedSpace M]
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∀ x y : M,
      _root_.EDist.edist ((riemannianEDistOf g p x).toReal)
        ((riemannianEDistOf g p y).toReal) ≤ riemannianEDistOf g x y := by
  intro x y
  have hpx := riemannianEDistOf_ne_top (I := I) g p x
  have hpy := riemannianEDistOf_ne_top (I := I) g p y
  have hxy := riemannianEDistOf_ne_top (I := I) g x y
  have hyx := riemannianEDistOf_ne_top (I := I) g y x
  have h1 := riemannianEDistOf_toReal_triangle (I := I) g p x y hpx hxy
  have h2 := riemannianEDistOf_toReal_triangle (I := I) g p y x hpy hyx
  have habs : |(riemannianEDistOf g p x).toReal -
      (riemannianEDistOf g p y).toReal| ≤
      (riemannianEDistOf g x y).toReal := by
    rw [abs_le]
    rw [riemannianEDistOf_comm (I := I) g y x] at h2
    constructor <;> linarith
  rw [edist_dist, Real.dist_eq]
  rw [← ENNReal.ofReal_toReal hxy]
  exact ENNReal.ofReal_le_ofReal habs

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.riemannianDistance_toReal_lipschitz then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.riemannianDistance_toReal_lipschitz"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.riemannianDistance_toReal_lipschitz ``Submission.DifferentialGeometry.Geometry.Metric.riemannianDistance_toReal_lipschitz

end DifferentialGeometry.Geometry.Metric
