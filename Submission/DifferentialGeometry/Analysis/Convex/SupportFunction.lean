import Mathlib.Analysis.InnerProductSpace.Projection.Minimal

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Analysis.Convex

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

def supportFunction (C : Set F) (v : F) : ℝ :=
  _root_.SupSet.sSup {x : ℝ | ∃ c : F, c ∈ C ∧ x = _root_.Inner.inner ℝ v c}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Convex.supportFunction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Convex.supportFunction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Convex.supportFunction ``Submission.DifferentialGeometry.Analysis.Convex.supportFunction

def finiteSupportDirections (C : Set F) : Set F :=
  {v : F | BddAbove {x : ℝ | ∃ c : F, c ∈ C ∧ x = _root_.Inner.inner ℝ v c}}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Convex.finiteSupportDirections then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Convex.finiteSupportDirections"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Convex.finiteSupportDirections ``Submission.DifferentialGeometry.Analysis.Convex.finiteSupportDirections

omit [CompleteSpace F] in
theorem supportFunction_le_of_mem {C : Set F} {v c : F}
    (hv : v ∈ finiteSupportDirections C) (hc : c ∈ C) :
    inner ℝ v c ≤ supportFunction C v := by
  unfold supportFunction
  exact le_csSup hv ⟨c, hc, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Convex.supportFunction_le_of_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Convex.supportFunction_le_of_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Convex.supportFunction_le_of_mem ``Submission.DifferentialGeometry.Analysis.Convex.supportFunction_le_of_mem

omit [CompleteSpace F] in
theorem mem_finiteSupportDirections_of_normal
    {C : Set F} {v p : F}
    (hnormal : ∀ q : F, q ∈ C → _root_.Inner.inner ℝ v (q - p) ≤ 0) :
    v ∈ finiteSupportDirections C := by
  unfold finiteSupportDirections
  refine ⟨inner ℝ v p, ?_⟩
  rintro x ⟨q, hq, rfl⟩
  have hqle : _root_.Inner.inner ℝ v q - _root_.Inner.inner ℝ v p ≤ 0 := by
    have h := hnormal q hq
    rw [show _root_.Inner.inner ℝ v (q - p) = _root_.Inner.inner ℝ v q - _root_.Inner.inner ℝ v p by
      rw [inner_sub_right]] at h
    exact h
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Convex.mem_finiteSupportDirections_of_normal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Convex.mem_finiteSupportDirections_of_normal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Convex.mem_finiteSupportDirections_of_normal ``Submission.DifferentialGeometry.Analysis.Convex.mem_finiteSupportDirections_of_normal

theorem mem_of_forall_support_le
    {C : Set F} {p : F}
    (hCclosed : IsClosed C) (hCne : C.Nonempty) (hCconvex : Convex ℝ C)
    (hp : ∀ v : F, v ∈ finiteSupportDirections C → _root_.Inner.inner ℝ v p ≤ supportFunction C v) :
    p ∈ C := by
  by_contra hnot
  obtain ⟨q, hqC, hqmin⟩ :=
    exists_norm_eq_iInf_of_complete_convex hCne hCclosed.isComplete hCconvex p
  let v : F := p - q
  have hnormal : ∀ c ∈ C, _root_.Inner.inner ℝ v (c - q) ≤ 0 := by
    exact (norm_eq_iInf_iff_real_inner_le_zero hCconvex hqC).mp hqmin
  have hbdd : BddAbove {x : ℝ | ∃ c : F, c ∈ C ∧ x = _root_.Inner.inner ℝ v c} := by
    refine ⟨inner ℝ v q, ?_⟩
    rintro x ⟨c, hc, rfl⟩
    have hqle : _root_.Inner.inner ℝ v c - _root_.Inner.inner ℝ v q ≤ 0 := by
      have h := hnormal c hc
      rw [show _root_.Inner.inner ℝ v (c - q) = _root_.Inner.inner ℝ v c - _root_.Inner.inner ℝ v q by
        rw [inner_sub_right]] at h
      exact h
    linarith
  have hv : v ∈ finiteSupportDirections C := hbdd
  have hle := hp v hv
  have hsup_le : supportFunction C v ≤ _root_.Inner.inner ℝ v q := by
    unfold supportFunction
    refine csSup_le ?_ ?_
    · rcases hCne with ⟨w, hw⟩
      refine ⟨inner ℝ v w, ?_⟩
      exact ⟨w, hw, rfl⟩
    · rintro x ⟨c, hc, rfl⟩
      have hqle : _root_.Inner.inner ℝ v c - _root_.Inner.inner ℝ v q ≤ 0 := by
        have h := hnormal c hc
        rw [show _root_.Inner.inner ℝ v (c - q) = _root_.Inner.inner ℝ v c - _root_.Inner.inner ℝ v q by
          rw [inner_sub_right]] at h
        exact h
      linarith
  have hmain : _root_.Inner.inner ℝ v p ≤ _root_.Inner.inner ℝ v q := le_trans hle hsup_le
  have hgt : _root_.Inner.inner ℝ v q < _root_.Inner.inner ℝ v p := by
    have hpos : 0 < ‖v‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (by
      intro hpq
      have : p ∈ C := by simpa [hpq] using hqC
      exact hnot this))
    have hval : _root_.Inner.inner ℝ v p - _root_.Inner.inner ℝ v q = ‖v‖ ^ 2 := by
      rw [← inner_sub_right]
      rw [show p - q = v from rfl, real_inner_self_eq_norm_sq]
    nlinarith [hpos]
  exact (not_lt_of_ge hmain) hgt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Convex.mem_of_forall_support_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Convex.mem_of_forall_support_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Convex.mem_of_forall_support_le ``Submission.DifferentialGeometry.Analysis.Convex.mem_of_forall_support_le

theorem mem_iff_support_le
    {C : Set F} {p : F}
    (hCclosed : IsClosed C) (hCne : C.Nonempty) (hCconvex : Convex ℝ C) :
    p ∈ C ↔ ∀ v : F, v ∈ finiteSupportDirections C → _root_.Inner.inner ℝ v p ≤ supportFunction C v := by
  constructor
  · intro hp v hv
    exact supportFunction_le_of_mem hv hp
  · exact mem_of_forall_support_le hCclosed hCne hCconvex

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Convex.mem_iff_support_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Convex.mem_iff_support_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Convex.mem_iff_support_le ``Submission.DifferentialGeometry.Analysis.Convex.mem_iff_support_le

end DifferentialGeometry.Analysis.Convex

end
