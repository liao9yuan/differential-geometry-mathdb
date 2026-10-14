import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Orientation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Finset

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem incidenceIndex_max (r : LinearOrder E) {t : Finset E} {m : E}
    (hm : ∀ x ∈ t, r.lt x m) :
    incidenceIndex r (_root_.Insert.insert m t) m = t.card := by
  let _ := r
  classical
  have h : (_root_.Insert.insert m t).filter (fun w => w < m) = t := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hw | hw, hlt⟩
      · exact absurd (hw ▸ hlt) (lt_irrefl m)
      · exact hw
    · exact fun hw => ⟨Or.inr hw, hm w hw⟩
  change ((_root_.Insert.insert m t).filter (fun w => w < m)).card = t.card
  rw [h]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.incidenceIndex_max then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.incidenceIndex_max"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.incidenceIndex_max ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.incidenceIndex_max

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem incidenceIndex_insert_of_lt (r : LinearOrder E) {t : Finset E} {m v : E}
    (hm : ∀ x ∈ t, r.lt x m) (hv : v ∈ t) :
    incidenceIndex r (_root_.Insert.insert m t) v = incidenceIndex r t v := by
  let _ := r
  classical
  have h : (_root_.Insert.insert m t).filter (fun w => w < v) = t.filter (fun w => w < v) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hw | hw, hlt⟩
      · exact absurd (lt_trans (hw ▸ hlt) (hm v hv)) (lt_irrefl m)
      · exact ⟨hw, hlt⟩
    · rintro ⟨hw, hlt⟩
      exact ⟨Or.inr hw, hlt⟩
  change ((_root_.Insert.insert m t).filter (fun w => w < v)).card = (t.filter (fun w => w < v)).card
  rw [h]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.incidenceIndex_insert_of_lt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.incidenceIndex_insert_of_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.incidenceIndex_insert_of_lt ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.incidenceIndex_insert_of_lt

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem prod_incidenceSign (r : LinearOrder E) (s : Finset E) :
    ∏ v ∈ s, incidenceSign r s v = (-1 : ℤ) ^ s.card.choose 2 := by
  let _ := r
  classical
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert m t hm ih =>
      have hmt : m ∉ t := fun h => lt_irrefl m (hm m h)
      rw [Finset.prod_insert hmt, incidenceSign, incidenceIndex_max r hm]
      have hrest : ∏ v ∈ t, incidenceSign r (_root_.Insert.insert m t) v = ∏ v ∈ t, incidenceSign r t v :=
        Finset.prod_congr rfl fun v hv => by
          rw [incidenceSign, incidenceSign, incidenceIndex_insert_of_lt r hm hv]
      rw [hrest, ih, Finset.card_insert_of_notMem hmt, ← pow_add, Nat.choose_succ_succ,
        Nat.choose_one_right]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.prod_incidenceSign then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.prod_incidenceSign"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.prod_incidenceSign ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.prod_incidenceSign

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem prod_incidenceSign_triple (r : LinearOrder E) {a b c : E} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) :
    incidenceSign r ({a, b, c} : Finset E) a * incidenceSign r ({a, b, c} : Finset E) b *
        incidenceSign r ({a, b, c} : Finset E) c = -1 := by
  let _ := r
  classical
  have hcard : ({a, b, c} : Finset E).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, hac]),
      Finset.card_insert_of_notMem (by simp [hbc]), Finset.card_singleton]
  have hprod := prod_incidenceSign r ({a, b, c} : Finset E)
  rw [hcard] at hprod
  rw [Finset.prod_insert (by simp [hab, hac]), Finset.prod_insert (by simp [hbc]),
    Finset.prod_singleton] at hprod
  rw [mul_assoc, hprod]
  norm_num

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.prod_incidenceSign_triple then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.prod_incidenceSign_triple"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.prod_incidenceSign_triple ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.prod_incidenceSign_triple

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem sum_incidenceIndex (r : LinearOrder E) (s : Finset E) :
    ∑ v ∈ s, incidenceIndex r s v = s.card.choose 2 := by
  let _ := r
  classical
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert m t hm ih =>
      have hmt : m ∉ t := fun h => lt_irrefl m (hm m h)
      rw [Finset.sum_insert hmt, incidenceIndex_max r hm]
      have hrest : ∑ v ∈ t, incidenceIndex r (_root_.Insert.insert m t) v = ∑ v ∈ t, incidenceIndex r t v :=
        Finset.sum_congr rfl fun v hv => incidenceIndex_insert_of_lt r hm hv
      rw [hrest, ih, Finset.card_insert_of_notMem hmt, Nat.choose_succ_succ, Nat.choose_one_right]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.sum_incidenceIndex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.sum_incidenceIndex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.sum_incidenceIndex ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.sum_incidenceIndex

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem incidenceIndex_union [DecidableEq E] (r : LinearOrder E) {s t : Finset E}
    (h : Disjoint s t) (v : E) :
    incidenceIndex r (s ∪ t) v = incidenceIndex r s v + incidenceIndex r t v := by
  simp only [incidenceIndex]
  rw [Finset.filter_union, Finset.card_union_of_disjoint]
  exact Finset.disjoint_filter_filter h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.incidenceIndex_union then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.incidenceIndex_union"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.incidenceIndex_union ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.incidenceIndex_union

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem incidenceIndex_singleton_self (r : LinearOrder E) (v : E) :
    incidenceIndex r {v} v = 0 := by
  have h := sum_incidenceIndex r ({v} : Finset E)
  rw [Finset.sum_singleton, Finset.card_singleton] at h
  simpa using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.incidenceIndex_singleton_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.incidenceIndex_singleton_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.incidenceIndex_singleton_self ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.incidenceIndex_singleton_self

end DifferentialGeometry.Topology.PiecewiseLinear
