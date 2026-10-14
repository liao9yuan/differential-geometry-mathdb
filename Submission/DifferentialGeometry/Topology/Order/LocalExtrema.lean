import Mathlib.Topology.Order.LocalExtr
import Mathlib.Topology.Order.OrderClosed

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

theorem not_isLocalMax_iff_mem_closure_gt {X α : Type*} [TopologicalSpace X]
    [LinearOrder α] {f : X → α} {x : X} :
    ¬ IsLocalMax f x ↔ x ∈ closure {y | f x < f y} := by
  simp only [mem_closure_iff_frequently, Filter.Frequently, _root_.Set.mem_ofPred_eq, not_lt,
    IsLocalMax, IsMaxFilter]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `not_isLocalMax_iff_mem_closure_gt then
    throwError "Refusing to shadow existing declaration not_isLocalMax_iff_mem_closure_gt"
  Lean.modifyEnv fun env => Lean.addAlias env `not_isLocalMax_iff_mem_closure_gt ``Submission.not_isLocalMax_iff_mem_closure_gt

theorem not_isLocalMin_iff_mem_closure_lt {X α : Type*} [TopologicalSpace X]
    [LinearOrder α] {f : X → α} {x : X} :
    ¬ IsLocalMin f x ↔ x ∈ closure {y | f y < f x} :=
  not_isLocalMax_iff_mem_closure_gt (α := OrderDual α)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `not_isLocalMin_iff_mem_closure_lt then
    throwError "Refusing to shadow existing declaration not_isLocalMin_iff_mem_closure_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `not_isLocalMin_iff_mem_closure_lt ``Submission.not_isLocalMin_iff_mem_closure_lt

open _root_.Continuous in
theorem Continuous.closure_gt_eq_ge_of_not_isLocalMax {X α : Type*} [TopologicalSpace X]
    [LinearOrder α] [TopologicalSpace α] [OrderClosedTopology α]
    {f : X → α} (hf : Continuous f) {a : α}
    (ha : ∀ x, f x = a → ¬ IsLocalMax f x) :
    closure {x | a < f x} = {x | a ≤ f x} := by
  apply Subset.antisymm
  · exact closure_minimal (fun x hx => hx.le) (isClosed_le continuous_const hf)
  · intro x hx
    rcases eq_or_lt_of_le hx with h | h
    · have hc := not_isLocalMax_iff_mem_closure_gt.mp (ha x h.symm)
      simpa [h] using hc
    · exact subset_closure h

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.Continuous
  let env ← Lean.getEnv
  if env.contains `Continuous.closure_gt_eq_ge_of_not_isLocalMax then
    throwError "Refusing to shadow existing declaration Continuous.closure_gt_eq_ge_of_not_isLocalMax"
  Lean.modifyEnv fun env => Lean.addAlias env `Continuous.closure_gt_eq_ge_of_not_isLocalMax ``Submission.Continuous.closure_gt_eq_ge_of_not_isLocalMax

open _root_.Continuous in
theorem Continuous.closure_lt_eq_le_of_not_isLocalMin {X α : Type*} [TopologicalSpace X]
    [LinearOrder α] [TopologicalSpace α] [OrderClosedTopology α]
    {f : X → α} (hf : Continuous f) {a : α}
    (ha : ∀ x, f x = a → ¬ IsLocalMin f x) :
    closure {x | f x < a} = {x | f x ≤ a} :=
  hf.closure_gt_eq_ge_of_not_isLocalMax (α := OrderDual α) ha

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Continuous.closure_lt_eq_le_of_not_isLocalMin then
    throwError "Refusing to shadow existing declaration Continuous.closure_lt_eq_le_of_not_isLocalMin"
  Lean.modifyEnv fun env => Lean.addAlias env `Continuous.closure_lt_eq_le_of_not_isLocalMin ``Submission.Continuous.closure_lt_eq_le_of_not_isLocalMin
