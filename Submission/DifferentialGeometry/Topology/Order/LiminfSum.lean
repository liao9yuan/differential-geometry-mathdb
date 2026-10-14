import Mathlib.Topology.Algebra.Order.LiminfLimsup

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace Filter
open _root_.Filter

open _root_.Filter in
theorem sum_liminf_le
    {ι α : Type*} {l : Filter α} [_root_.Filter.NeBot l] (s : Finset ι) (q : ι → α → ℝ)
    (hlo : ∀ i ∈ s, _root_.Filter.IsBoundedUnder (· ≥ ·) l (q i))
    (hhi : ∀ i ∈ s, _root_.Filter.IsBoundedUnder (· ≤ ·) l (q i)) :
    (∑ i ∈ s, _root_.Filter.liminf (q i) l) ≤
      liminf (∑ i ∈ s, q i) l := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      change 0 ≤ _root_.Filter.liminf (fun _ : α ↦ (0 : ℝ)) l
      rw [_root_.Filter.liminf_const]
  | @insert i s hi ih =>
      have hi_lo := hlo i (Finset.mem_insert_self i s)
      have hi_hi := hhi i (Finset.mem_insert_self i s)
      have hs_lo : ∀ j ∈ s, _root_.Filter.IsBoundedUnder (· ≥ ·) l (q j) :=
        fun j hj ↦ hlo j (Finset.mem_insert_of_mem hj)
      have hs_hi : ∀ j ∈ s, _root_.Filter.IsBoundedUnder (· ≤ ·) l (q j) :=
        fun j hj ↦ hhi j (Finset.mem_insert_of_mem hj)
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      exact (add_le_add_right (ih hs_lo hs_hi) _).trans
        (le_liminf_add hi_lo hi_hi
          (_root_.Filter.isBoundedUnder_ge_sum s hs_lo)
          (_root_.Filter.isBoundedUnder_le_sum s hs_hi).isCoboundedUnder_ge)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Filter.sum_liminf_le then
    throwError "Refusing to shadow existing declaration Filter.sum_liminf_le"
  Lean.modifyEnv fun env => Lean.addAlias env `Filter.sum_liminf_le ``Submission.Filter.sum_liminf_le

end Filter
