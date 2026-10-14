import Submission.DifferentialGeometry.Geometry.Metric.Restriction
import Submission.DifferentialGeometry.Geometry.Metric.Distance.Ball
import Submission.DifferentialGeometry.Geometry.Metric.ConnectedComponentDistance

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem riemannianBallOf_eq_image_restrictOpen_of_isClosed
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M) [T2Space U]
    (hU : IsClosed (U : Set M)) (x : U) (r : ℝ) :
    riemannianBallOf g x.val r =
      Subtype.val '' riemannianBallOf (g.restrictOpen U) x r := by
  ext y
  constructor
  · intro hy
    have hycomp : y ∈ connectedComponent x.val :=
      Geometry.Metric.edistOf_ball_subset_connCompOpen g x.val r hy
    have hyU : y ∈ U :=
      (show IsClopen (U : Set M) from ⟨hU, U.isOpen⟩).connectedComponent_subset x.property hycomp
    refine ⟨⟨y, hyU⟩, ?_, rfl⟩
    change riemannianEDistOf (g.restrictOpen U) x ⟨y, hyU⟩ < ENNReal.ofReal r
    rw [riemannianEDistOf_restrictOpen_of_isClosed g U hU]
    exact hy
  · rintro ⟨z, hz, rfl⟩
    change riemannianEDistOf g x.val z.val < ENNReal.ofReal r
    rw [← riemannianEDistOf_restrictOpen_of_isClosed g U hU x z]
    exact hz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.riemannianBallOf_eq_image_restrictOpen_of_isClosed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.riemannianBallOf_eq_image_restrictOpen_of_isClosed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.riemannianBallOf_eq_image_restrictOpen_of_isClosed ``Submission.DifferentialGeometry.riemannianBallOf_eq_image_restrictOpen_of_isClosed

end DifferentialGeometry
