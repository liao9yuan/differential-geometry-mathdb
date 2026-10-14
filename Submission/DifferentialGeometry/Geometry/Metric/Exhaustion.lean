import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.ProperSpace

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

namespace DifferentialGeometry

structure MetricExhaustion (X : Type*) [MetricSpace X] where
  carrier : ℕ → Set X
  compact : ∀ n, IsCompact (carrier n)
  mono : Monotone carrier
  union_eq_univ : ⋃ n, carrier n = Set.univ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.MetricExhaustion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.MetricExhaustion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.MetricExhaustion ``Submission.DifferentialGeometry.MetricExhaustion

namespace MetricExhaustion

variable {X : Type*} [MetricSpace X] [ProperSpace X]

noncomputable def closedBall (x : X) : MetricExhaustion X where
  carrier := fun n => Metric.closedBall x (n : ℝ)
  compact := fun n => _root_.ProperSpace.isCompact_closedBall x (n : ℝ)
  mono := by
    intro m n hmn
    exact Metric.closedBall_subset_closedBall (by exact_mod_cast hmn)
  union_eq_univ := by
    apply Set.eq_univ_of_forall
    intro y
    obtain ⟨n, hn⟩ := exists_nat_ge (_root_.Dist.dist y x)
    rw [Set.mem_iUnion]
    refine ⟨n, ?_⟩
    rw [Metric.mem_closedBall]
    exact (dist_comm y x).symm ▸ hn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.MetricExhaustion.closedBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.MetricExhaustion.closedBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.MetricExhaustion.closedBall ``Submission.DifferentialGeometry.MetricExhaustion.closedBall

@[simp] theorem closedBall_carrier (x : X) (n : ℕ) :
    (closedBall x).carrier n = Metric.closedBall x (n : ℝ) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.MetricExhaustion.closedBall_carrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.MetricExhaustion.closedBall_carrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.MetricExhaustion.closedBall_carrier ``Submission.DifferentialGeometry.MetricExhaustion.closedBall_carrier

theorem compact_subset_closedBall (x : X) {K : Set X} (hK : IsCompact K) :
    ∃ n, K ⊆ (closedBall x).carrier n := by
  obtain ⟨r, hr, hKr⟩ := hK.isBounded.subset_closedBall_lt 0 x
  obtain ⟨n, hn⟩ := exists_nat_ge r
  refine ⟨n, hKr.trans ?_⟩
  exact Metric.closedBall_subset_closedBall hn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.MetricExhaustion.compact_subset_closedBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.MetricExhaustion.compact_subset_closedBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.MetricExhaustion.compact_subset_closedBall ``Submission.DifferentialGeometry.MetricExhaustion.compact_subset_closedBall

end MetricExhaustion

end DifferentialGeometry
