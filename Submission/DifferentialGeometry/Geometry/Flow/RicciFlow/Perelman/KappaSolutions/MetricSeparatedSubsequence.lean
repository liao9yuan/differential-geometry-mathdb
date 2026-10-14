import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Logic.Function.Iterate

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.Filter _root_.Set
open scoped _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

theorem exists_metric_separated_subsequence
    {X : Type*} [MetricSpace X] {x : ℕ → X} (p : X)
    (hescape : _root_.Filter.Tendsto (fun i => _root_.Dist.dist p (x i)) _root_.Filter.atTop _root_.Filter.atTop)
    (R : ℝ) (hR : 0 < R) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      ∀ i j : ℕ, i < j → R < _root_.Dist.dist (x (phi i)) (x (phi j)) := by
  classical
  have hstep (i : ℕ) : ∃ j : ℕ, i < j ∧ _root_.Dist.dist p (x i) + R < _root_.Dist.dist p (x j) := by
    have hevent : ∀ᶠ j in _root_.Filter.atTop, i < j ∧ _root_.Dist.dist p (x i) + R < _root_.Dist.dist p (x j) :=
      (_root_.Filter.eventually_gt_atTop i).and (hescape.eventually_gt_atTop (_root_.Dist.dist p (x i) + R))
    exact hevent.exists
  choose next hindex hradial using hstep
  let phi : ℕ → ℕ := fun n => (next^[n]) 0
  have hsucc (n : ℕ) : phi (n + 1) = next (phi n) := Function.iterate_succ_apply' next n 0
  have hphi : StrictMono phi := by
    apply strictMono_nat_of_lt_succ
    intro n
    rw [hsucc]
    exact hindex (phi n)
  have hrad (n : ℕ) : _root_.Dist.dist p (x (phi n)) + R < _root_.Dist.dist p (x (phi (n + 1))) := by
    rw [hsucc]
    exact hradial (phi n)
  have hmono : StrictMono (fun n => _root_.Dist.dist p (x (phi n))) := by
    apply strictMono_nat_of_lt_succ
    intro n
    have hh := hrad n
    linarith
  refine ⟨phi, hphi, ?_⟩
  intro i j hij
  have hle := hmono.monotone (Nat.succ_le_iff.mpr hij)
  have hi := hrad i
  have htriangle := dist_triangle p (x (phi i)) (x (phi j))
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_metric_separated_subsequence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_metric_separated_subsequence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_metric_separated_subsequence ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_metric_separated_subsequence

theorem exists_disjoint_closedBall_subsequence
    {X : Type*} [MetricSpace X] {x : ℕ → X} (p : X)
    (hescape : _root_.Filter.Tendsto (fun i => _root_.Dist.dist p (x i)) _root_.Filter.atTop _root_.Filter.atTop)
    (r : ℝ) (hr : 0 < r) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      Pairwise (fun i j : ℕ => Disjoint (Metric.closedBall (x (phi i)) r)
        (Metric.closedBall (x (phi j)) r)) := by
  obtain ⟨phi, hphi, hsep⟩ := exists_metric_separated_subsequence p hescape (2 * r) (by positivity)
  refine ⟨phi, hphi, ?_⟩
  intro i j hij
  have hfar : 2 * r < _root_.Dist.dist (x (phi i)) (x (phi j)) := by
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact hsep i j hlt
    · simpa only [dist_comm] using hsep j i hgt
  apply Set.disjoint_left.mpr
  intro q hqi hqj
  have hqi' : _root_.Dist.dist (x (phi i)) q ≤ r := by
    simpa only [Metric.mem_closedBall, dist_comm] using hqi
  have hqj' : _root_.Dist.dist q (x (phi j)) ≤ r := hqj
  have htriangle := dist_triangle (x (phi i)) q (x (phi j))
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_disjoint_closedBall_subsequence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_disjoint_closedBall_subsequence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_disjoint_closedBall_subsequence ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_disjoint_closedBall_subsequence

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
