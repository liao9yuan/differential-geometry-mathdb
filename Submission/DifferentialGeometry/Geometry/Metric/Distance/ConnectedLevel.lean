import Submission.DifferentialGeometry.Geometry.Comparison.Distance.Continuity
import Submission.DifferentialGeometry.Geometry.Metric.Distance.Ball
import Mathlib.Topology.Order.IntermediateValue

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

open _root_.Set
open scoped _root_.Manifold _root_.ContDiff _root_.Topology _root_.ENNReal

namespace DifferentialGeometry.Geometry.Riemannian

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem exists_riemannianEDistOf_eq_of_isPreconnected_of_closure
    (g : SmoothRiemannianMetric I M) (p : M) {U : Set M} (hU : IsPreconnected U)
    {a b : M} (ha : a ∈ closure U) (hb : b ∈ U) {R : ℝ}
    (hnear : riemannianEDistOf g p a < ENNReal.ofReal R)
    (hfar : ENNReal.ofReal R ≤ riemannianEDistOf g p b) :
    ∃ z ∈ U, riemannianEDistOf g p z = ENNReal.ofReal R := by
  have hcont : Continuous (fun z => riemannianEDistOf g p z) := continuous_riemannianEDist g p
  have hnhds : {z | riemannianEDistOf g p z < ENNReal.ofReal R} ∈ 𝓝 a :=
    (isOpen_lt hcont continuous_const).mem_nhds hnear
  obtain ⟨a', ha'near, ha'U⟩ := mem_closure_iff_nhds.mp ha _ hnhds
  exact hU.intermediate_value ha'U hb hcont.continuousOn ⟨ha'near.le, hfar⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.exists_riemannianEDistOf_eq_of_isPreconnected_of_closure then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.exists_riemannianEDistOf_eq_of_isPreconnected_of_closure"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.exists_riemannianEDistOf_eq_of_isPreconnected_of_closure ``Submission.DifferentialGeometry.Geometry.Riemannian.exists_riemannianEDistOf_eq_of_isPreconnected_of_closure

end DifferentialGeometry.Geometry.Riemannian
