import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorphGluing

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_isPLHomeomorphOn_iUnion_of_pairwise_disjoint {ι : Type*} [Finite ι]
    {P : ι → Set E} {Q : ι → Set F} {f : ι → E → F}
    (hP : ∀ i, IsPolyhedron (P i)) (hf : ∀ i, IsPLHomeomorphOn (f i) (P i) (Q i))
    (hPd : Pairwise fun i j => Disjoint (P i) (P j))
    (hQd : Pairwise fun i j => Disjoint (Q i) (Q j)) :
    ∃ g : E → F, IsPLHomeomorphOn g (⋃ i, P i) (⋃ i, Q i) ∧ ∀ i, _root_.Set.EqOn g (f i) (P i) := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  have hind : ∀ d : Finset ι,
      ∃ g : E → F, IsPLHomeomorphOn g (⋃ i ∈ d, P i) (⋃ i ∈ d, Q i) ∧
        ∀ i ∈ d, _root_.Set.EqOn g (f i) (P i) := by
    intro d
    induction d using Finset.induction_on with
    | empty =>
      refine ⟨fun _ => 0, ?_, by simp⟩
      simp only [Finset.notMem_empty, _root_.Set.iUnion_false, _root_.Set.iUnion_empty]
      exact ⟨by simp [_root_.Set.BijOn, _root_.Set.MapsTo, _root_.Set.InjOn, _root_.Set.SurjOn], fun _ hx => hx.elim, fun _ hx => hx.elim⟩
    | @insert i d hi ih =>
      obtain ⟨g, hg, hgi⟩ := ih
      have hPunion : IsPolyhedron (⋃ j ∈ d, P j) := by
        simpa only [_root_.Set.iUnion_subtype] using (IsPolyhedron.iUnion (fun j : d => hP j))
      have hPi : Disjoint (P i) (⋃ j ∈ d, P j) := by
        apply disjoint_iUnion_right.mpr
        intro j
        apply disjoint_iUnion_right.mpr
        intro hj
        exact hPd (ne_of_mem_of_not_mem hj hi).symm
      have hQi : Disjoint (Q i) (⋃ j ∈ d, Q j) := by
        apply disjoint_iUnion_right.mpr
        intro j
        apply disjoint_iUnion_right.mpr
        intro hj
        exact hQd (ne_of_mem_of_not_mem hj hi).symm
      obtain ⟨g', hg', hleft, hright⟩ := exists_isPLHomeomorphOn_union (hP i) hPunion (hf i) hg
        (by rw [hPi.inter_eq]; exact _root_.Set.eqOn_empty _ _)
        (by intro y hy; rw [hQi.inter_eq] at hy; exact hy.elim)
      refine ⟨g', ?_, ?_⟩
      · simpa only [Finset.set_biUnion_insert] using hg'
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact hleft
        · intro x hx
          exact (hright (mem_iUnion₂.mpr ⟨j, hj, hx⟩)).trans (hgi j hj hx)
  obtain ⟨g, hg, hgi⟩ := hind Finset.univ
  exact ⟨g, by simpa only [Finset.mem_univ, _root_.Set.iUnion_true] using hg,
    fun i => hgi i (Finset.mem_univ i)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_iUnion_of_pairwise_disjoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_iUnion_of_pairwise_disjoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_iUnion_of_pairwise_disjoint ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_iUnion_of_pairwise_disjoint

end DifferentialGeometry.Topology.PiecewiseLinear
