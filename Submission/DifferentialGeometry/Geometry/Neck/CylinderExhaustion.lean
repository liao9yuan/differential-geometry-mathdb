import Submission.DifferentialGeometry.Geometry.Neck.PointwiseChart

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Filter
open scoped _root_.Topology
namespace DifferentialGeometry.Geometry.Neck
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.E3 target :: scope.openDecls } }
private abbrev S2 := Metric.sphere (0 : E3) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.S2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.S2 target :: scope.openDecls } }

theorem compact_subset_openCylinder {K : Set (S2 × ℝ)} (hK : IsCompact K) :
    ∃ L : ℝ, 0 < L ∧ K ⊆ (openCylinder L : Set (S2 × ℝ)) := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn continuous_snd.continuousOn
  refine ⟨max C 0 + 1, by positivity, ?_⟩
  intro q hq
  have hb : |q.2| ≤ C := by simpa only [Real.norm_eq_abs] using hC q hq
  change -(_root_.Max.max C 0 + 1) < q.2 ∧ q.2 < _root_.Max.max C 0 + 1
  exact ⟨by linarith [neg_abs_le q.2, le_max_left C 0],
    by linarith [le_abs_self q.2, le_max_left C 0]⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.compact_subset_openCylinder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.compact_subset_openCylinder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.compact_subset_openCylinder ``Submission.DifferentialGeometry.Geometry.Neck.compact_subset_openCylinder

theorem openCylinder_nat_exhaustion :
    Monotone (fun k : ℕ => (openCylinder ((k : ℝ) + 1) : Set (S2 × ℝ))) ∧
      (⋃ k : ℕ, (openCylinder ((k : ℝ) + 1) : Set (S2 × ℝ))) = univ := by
  constructor
  · intro i j hij q hq
    have hij' : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
    change -((j : ℝ) + 1) < q.2 ∧ q.2 < (j : ℝ) + 1
    exact ⟨by linarith [hq.1], by linarith [hq.2]⟩
  · apply _root_.Set.eq_univ_of_forall
    intro q
    obtain ⟨k, hk⟩ := exists_nat_gt |q.2|
    apply mem_iUnion.mpr
    refine ⟨k, ?_⟩
    change -((k : ℝ) + 1) < q.2 ∧ q.2 < (k : ℝ) + 1
    exact ⟨by linarith [neg_abs_le q.2], by linarith [le_abs_self q.2]⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.openCylinder_nat_exhaustion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.openCylinder_nat_exhaustion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.openCylinder_nat_exhaustion ``Submission.DifferentialGeometry.Geometry.Neck.openCylinder_nat_exhaustion

end DifferentialGeometry.Geometry.Neck
end
