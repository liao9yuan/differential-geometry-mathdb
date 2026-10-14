import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Instances.Real.Lemmas

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Function
set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.Topology


def intervalPush {ε : ℝ} (a : ℝ) (haε : 2 * a ≤ ε) : C(_root_.Set.Icc (0 : ℝ) ε, _root_.Set.Icc (0 : ℝ) ε) where
  toFun t := ⟨max t.val (a + t.val / 2), t.property.1.trans (le_max_left _ _),
    max_le t.property.2 (by linarith [t.property.2])⟩
  continuous_toFun := by fun_prop

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.intervalPush then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.intervalPush"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.intervalPush ``Submission.DifferentialGeometry.Topology.intervalPush

@[simp] theorem intervalPush_coe {ε : ℝ} (a : ℝ) (haε : 2 * a ≤ ε) (t : _root_.Set.Icc (0 : ℝ) ε) :
    (intervalPush a haε t : ℝ) = _root_.Max.max t.val (a + t.val / 2) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.intervalPush_coe then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.intervalPush_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.intervalPush_coe ``Submission.DifferentialGeometry.Topology.intervalPush_coe


theorem strictMono_intervalPush {ε : ℝ} (a : ℝ) (haε : 2 * a ≤ ε) :
    StrictMono (intervalPush a haε) := by
  intro s t hst
  change _root_.Max.max s.val (a + s.val / 2) < _root_.Max.max t.val (a + t.val / 2)
  exact max_lt_max hst (by change s.val < t.val at hst; linarith)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.strictMono_intervalPush then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.strictMono_intervalPush"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.strictMono_intervalPush ``Submission.DifferentialGeometry.Topology.strictMono_intervalPush


theorem intervalPush_fixed {ε : ℝ} (a : ℝ) (haε : 2 * a ≤ ε)
    (t : _root_.Set.Icc (0 : ℝ) ε) (ht : 2 * a ≤ t.val) : intervalPush a haε t = t := by
  apply Subtype.ext
  exact max_eq_left (by linarith)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.intervalPush_fixed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.intervalPush_fixed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.intervalPush_fixed ``Submission.DifferentialGeometry.Topology.intervalPush_fixed


theorem range_intervalPush {a ε : ℝ} (haε : 2 * a ≤ ε) :
    range (intervalPush a haε) = {t : _root_.Set.Icc (0 : ℝ) ε | a ≤ t.val} := by
  ext t
  constructor
  · rintro ⟨s, rfl⟩
    change a ≤ _root_.Max.max s.val (a + s.val / 2)
    exact (by linarith [s.property.1] : a ≤ a + s.val / 2).trans (le_max_right _ _)
  · intro ht
    change a ≤ t.val at ht
    by_cases hta : t.val ≤ 2 * a
    · let s : _root_.Set.Icc (0 : ℝ) ε := ⟨2 * (t.val - a), by constructor <;> linarith⟩
      refine ⟨s, Subtype.ext ?_⟩
      change _root_.Max.max (2 * (t.val - a)) (a + 2 * (t.val - a) / 2) = t.val
      have hh : a + 2 * (t.val - a) / 2 = t.val := by ring
      rw [hh, max_eq_right (by linarith)]
    · exact ⟨t, intervalPush_fixed a haε t (le_of_lt (lt_of_not_ge hta))⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.range_intervalPush then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.range_intervalPush"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.range_intervalPush ``Submission.DifferentialGeometry.Topology.range_intervalPush

end DifferentialGeometry.Topology
