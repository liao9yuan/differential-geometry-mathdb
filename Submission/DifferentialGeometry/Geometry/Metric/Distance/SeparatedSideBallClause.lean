import Submission.DifferentialGeometry.Geometry.Metric.Distance.SeparatedSidePoint

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal

namespace DifferentialGeometry.Geometry.Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem separated_side_clause_of_le_radius (g : SmoothRiemannianMetric I M)
    {S V W : Set M} (hV : IsOpen V) (hW : IsOpen W) (hVW : Disjoint V W) {x : M} {A b r : ℝ}
    (hb : 0 ≤ b) (hbA : b < A) (hAr : A ≤ r)
    (hS : ∀ z ∈ S, riemannianEDistOf g x z ≤ ENNReal.ofReal b)
    (hcov : riemannianClosedBallOf g x (3 * r) \ S ⊆ V ∪ W) {p q : M} (hp : p ∈ V) (hq : q ∈ W)
    (hpa : ENNReal.ofReal r ≤ riemannianEDistOf g x p)
    (hpc : riemannianEDistOf g x p < ENNReal.ofReal (3 * r))
    (hqa : ENNReal.ofReal r ≤ riemannianEDistOf g x q)
    (hqc : riemannianEDistOf g x q < ENNReal.ofReal (3 * r)) :
    riemannianClosedBallOf g x (3 * A) \ S ⊆ V ∪ W ∧
    ∃ p' ∈ V, ∃ q' ∈ W,
      ENNReal.ofReal A ≤ riemannianEDistOf g x p' ∧
      riemannianEDistOf g x p' < ENNReal.ofReal (3 * A) ∧
      ENNReal.ofReal A ≤ riemannianEDistOf g x q' ∧
      riemannianEDistOf g x q' < ENNReal.ofReal (3 * A) := by
  have hA : 0 < A := hb.trans_lt hbA
  have hcov' : riemannianBallOf g x (3 * r) \ S ⊆ V ∪ W := fun z hz =>
    hcov ⟨(show riemannianEDistOf g x z < ENNReal.ofReal (3 * r) from hz.1).le, hz.2⟩
  have hlt : ENNReal.ofReal A < ENNReal.ofReal (3 * A) :=
    (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by linarith)
  refine ⟨fun z hz => hcov ⟨riemannianClosedBallOf_mono g x (by linarith) hz.1, hz.2⟩, ?_⟩
  obtain ⟨p', hp', hpd⟩ := exists_mem_riemannianEDistOf_eq_of_ball_diff_subset g hV hW hVW hb hbA
    hS hcov' hp ((ENNReal.ofReal_le_ofReal hAr).trans hpa) hpc
  obtain ⟨q', hq', hqd⟩ := exists_mem_riemannianEDistOf_eq_of_ball_diff_subset g hW hV hVW.symm
    hb hbA hS (by rw [_root_.Set.union_comm]; exact hcov') hq ((ENNReal.ofReal_le_ofReal hAr).trans hqa) hqc
  exact ⟨p', hp', q', hq', hpd.ge, hpd ▸ hlt, hqd.ge, hqd ▸ hlt⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.separated_side_clause_of_le_radius then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.separated_side_clause_of_le_radius"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.separated_side_clause_of_le_radius ``Submission.DifferentialGeometry.Geometry.Metric.separated_side_clause_of_le_radius

end DifferentialGeometry.Geometry.Metric
