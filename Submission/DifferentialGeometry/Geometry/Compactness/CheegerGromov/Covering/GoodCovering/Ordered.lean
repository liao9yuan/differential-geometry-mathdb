import Mathlib.Topology.MetricSpace.HausdorffDistance


import Mathlib.Topology.MetricSpace.ProperSpace
import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Covering.GoodCovering.Basic
import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Metric.Proper

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry
namespace CheegerGromovCompactness
namespace OrderedNet

open _root_.Metric _root_.Set
open scoped _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

variable {M : Type*} [MetricSpace M] [ProperSpace M]

def availSet (O : M) (lam : ℝ → ℝ) (U : Set M) : Set M :=
  {x | Disjoint (Metric.ball x (lam (_root_.Dist.dist x O))) U}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.availSet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.OrderedNet.availSet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.availSet ``Submission.DifferentialGeometry.CheegerGromovCompactness.OrderedNet.availSet

omit [ProperSpace M] in
theorem isClosed_availSet (O : M) {lam : ℝ → ℝ} (hlam : Continuous lam) (U : Set M) :
    IsClosed (availSet O lam U) := by
  rcases U.eq_empty_or_nonempty with rfl | hUne
  · have : availSet O lam (∅ : Set M) = Set.univ := by ext x; simp [availSet]
    rw [this]; exact isClosed_univ
  have hset : availSet O lam U = {x | lam (_root_.Dist.dist x O) ≤ Metric.infDist x U} := by
    ext x
    simp only [availSet, Set.mem_ofPred_eq, Set.disjoint_left, Metric.mem_ball]
    constructor
    · intro h
      rw [Metric.le_infDist hUne]
      intro y hy
      rw [dist_comm x y]
      exact not_lt.mp (fun hlt => h hlt hy)
    · intro hle a ha haU
      have hax : Metric.infDist x U ≤ _root_.Dist.dist a x := by
        rw [dist_comm a x]; exact Metric.infDist_le_dist_of_mem haU
      linarith [le_trans hle hax]
  rw [hset]
  exact isClosed_le (hlam.comp (continuous_id.dist continuous_const))
    (Metric.continuous_infDist_pt U)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.isClosed_availSet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.OrderedNet.isClosed_availSet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.isClosed_availSet ``Submission.DifferentialGeometry.CheegerGromovCompactness.OrderedNet.isClosed_availSet

theorem exists_min_dist_base (O : M) {S : Set M} (hScl : IsClosed S) (hSne : S.Nonempty) :
    ∃ x ∈ S, ∀ y ∈ S, _root_.Dist.dist x O ≤ _root_.Dist.dist y O := by
  obtain ⟨s₀, hs₀⟩ := hSne
  have hcpt : IsCompact (S ∩ Metric.closedBall O (_root_.Dist.dist s₀ O)) :=
    (_root_.ProperSpace.isCompact_closedBall O (_root_.Dist.dist s₀ O)).inter_left hScl
  have hne : (S ∩ Metric.closedBall O (_root_.Dist.dist s₀ O)).Nonempty :=
    ⟨s₀, hs₀, Metric.mem_closedBall.mpr le_rfl⟩
  obtain ⟨x, ⟨hxS, hxball⟩, hxmin⟩ :=
    hcpt.exists_isMinOn hne ((continuous_id.dist continuous_const).continuousOn)
  refine ⟨x, hxS, fun y hyS => ?_⟩
  by_cases hy : y ∈ Metric.closedBall O (_root_.Dist.dist s₀ O)
  · exact hxmin ⟨hyS, hy⟩
  · rw [Metric.mem_closedBall, not_le] at hy
    have hx_le : _root_.Dist.dist x O ≤ _root_.Dist.dist s₀ O := Metric.mem_closedBall.mp hxball
    linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.exists_min_dist_base then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.OrderedNet.exists_min_dist_base"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.exists_min_dist_base ``Submission.DifferentialGeometry.CheegerGromovCompactness.OrderedNet.exists_min_dist_base

def forbidden (O : M) (lam : ℝ → ℝ) (prior : List M) : Set M :=
  ⋃ c ∈ prior, Metric.ball c (lam (_root_.Dist.dist c O))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.forbidden then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.OrderedNet.forbidden"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.forbidden ``Submission.DifferentialGeometry.CheegerGromovCompactness.OrderedNet.forbidden

open _root_.Classical in
def netList (O : M) (lam : ℝ → ℝ) (hlam : Continuous lam) : ℕ → List M
  | 0 => [O]
  | (α + 1) =>
      if h : (availSet O lam (forbidden O lam (netList O lam hlam α))).Nonempty then
        netList O lam hlam α ++
          [(exists_min_dist_base O
              (isClosed_availSet O hlam (forbidden O lam (netList O lam hlam α))) h).choose]
      else netList O lam hlam α

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList ``Submission.DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList

theorem O_mem_netList (O : M) (lam : ℝ → ℝ) (hlam : Continuous lam) (α : ℕ) :
    O ∈ netList O lam hlam α := by
  induction α with
  | zero => simp [netList]
  | succ α ih =>
      rw [netList]
      split_ifs with h
      · exact List.mem_append_left _ ih
      · exact ih

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.O_mem_netList then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.OrderedNet.O_mem_netList"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.O_mem_netList ``Submission.DifferentialGeometry.CheegerGromovCompactness.OrderedNet.O_mem_netList

theorem netList_succ_spec (O : M) (lam : ℝ → ℝ) (hlam : Continuous lam) (α : ℕ)
    (h : (availSet O lam (forbidden O lam (netList O lam hlam α))).Nonempty) :
    ∃ x, netList O lam hlam (α + 1) = netList O lam hlam α ++ [x] ∧
      x ∈ availSet O lam (forbidden O lam (netList O lam hlam α)) ∧
      (∀ y ∈ availSet O lam (forbidden O lam (netList O lam hlam α)), _root_.Dist.dist x O ≤ _root_.Dist.dist y O) := by
  classical
  refine ⟨(exists_min_dist_base O
      (isClosed_availSet O hlam (forbidden O lam (netList O lam hlam α))) h).choose, ?_,
      (exists_min_dist_base O
        (isClosed_availSet O hlam (forbidden O lam (netList O lam hlam α))) h).choose_spec.1,
      (exists_min_dist_base O
        (isClosed_availSet O hlam (forbidden O lam (netList O lam hlam α))) h).choose_spec.2⟩
  rw [netList, dif_pos h]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList_succ_spec then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList_succ_spec"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList_succ_spec ``Submission.DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList_succ_spec

def ballsDisjoint (O : M) (lam : ℝ → ℝ) (l : List M) : Prop :=
  l.Pairwise fun a b =>
    Disjoint (Metric.ball a (lam (_root_.Dist.dist a O))) (Metric.ball b (lam (_root_.Dist.dist b O)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.ballsDisjoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.OrderedNet.ballsDisjoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.ballsDisjoint ``Submission.DifferentialGeometry.CheegerGromovCompactness.OrderedNet.ballsDisjoint

theorem netList_ballsDisjoint (O : M) (lam : ℝ → ℝ) (hlam : Continuous lam) (α : ℕ) :
    ballsDisjoint O lam (netList O lam hlam α) := by
  classical
  induction α with
  | zero => exact List.pairwise_singleton _ _
  | succ α ih =>
      by_cases h : (availSet O lam (forbidden O lam (netList O lam hlam α))).Nonempty
      · obtain ⟨x, hxeq, hxavail, _⟩ := netList_succ_spec O lam hlam α h
        rw [ballsDisjoint, hxeq]
        refine List.pairwise_append.mpr ⟨ih, List.pairwise_singleton _ _, ?_⟩
        intro a ha b hb
        rw [List.mem_singleton] at hb
        subst hb
        simp only [availSet, Set.mem_ofPred_eq, forbidden,
          Set.disjoint_iUnion_right] at hxavail
        exact (hxavail a ha).symm
      · rw [ballsDisjoint, netList, dif_neg h]; exact ih

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList_ballsDisjoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList_ballsDisjoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList_ballsDisjoint ``Submission.DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList_ballsDisjoint

@[simp] theorem netList_zero (O : M) (lam : ℝ → ℝ) (hlam : Continuous lam) :
    netList O lam hlam 0 = [O] := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList_zero ``Submission.DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList_zero

theorem netList_succ_stop (O : M) (lam : ℝ → ℝ) (hlam : Continuous lam) (α : ℕ)
    (h : ¬ (availSet O lam (forbidden O lam (netList O lam hlam α))).Nonempty) :
    netList O lam hlam (α + 1) = netList O lam hlam α := by
  rw [netList, dif_neg h]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList_succ_stop then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList_succ_stop"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList_succ_stop ``Submission.DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList_succ_stop

theorem mem_netList_succ (O : M) (lam : ℝ → ℝ) (hlam : Continuous lam) (α : ℕ)
    {a : M} (ha : a ∈ netList O lam hlam α) : a ∈ netList O lam hlam (α + 1) := by
  classical
  by_cases h : (availSet O lam (forbidden O lam (netList O lam hlam α))).Nonempty
  · obtain ⟨x, hxeq, -, -⟩ := netList_succ_spec O lam hlam α h
    rw [hxeq]
    exact List.mem_append_left _ ha
  · rw [netList_succ_stop O lam hlam α h]
    exact ha

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.mem_netList_succ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.OrderedNet.mem_netList_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.mem_netList_succ ``Submission.DifferentialGeometry.CheegerGromovCompactness.OrderedNet.mem_netList_succ

omit [ProperSpace M] in
theorem meets_of_not_avail (O : M) (lam : ℝ → ℝ) {l : List M} {p : M}
    (hp : p ∉ availSet O lam (forbidden O lam l)) :
    ∃ c ∈ l,
      ¬ Disjoint (Metric.ball p (lam (_root_.Dist.dist p O))) (Metric.ball c (lam (_root_.Dist.dist c O))) := by
  simp only [availSet, Set.mem_ofPred_eq, forbidden, Set.disjoint_iUnion_right,
    _root_.Classical.not_forall] at hp
  obtain ⟨c, hc, hmeet⟩ := hp
  exact ⟨c, hc, hmeet⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.meets_of_not_avail then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.OrderedNet.meets_of_not_avail"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.meets_of_not_avail ``Submission.DifferentialGeometry.CheegerGromovCompactness.OrderedNet.meets_of_not_avail

omit [ProperSpace M] in
theorem dist_lt_two_lam {lam : ℝ → ℝ} (hanti : Antitone lam) {O p c : M}
    (hcd : _root_.Dist.dist c O ≤ _root_.Dist.dist p O)
    (hmeet : ¬ Disjoint (Metric.ball p (lam (_root_.Dist.dist p O))) (Metric.ball c (lam (_root_.Dist.dist c O)))) :
    dist p c < 2 * lam (_root_.Dist.dist c O) := by
  obtain ⟨q, hqp, hqc⟩ := Set.not_disjoint_iff.mp hmeet
  rw [Metric.mem_ball] at hqp hqc
  have hl : lam (_root_.Dist.dist p O) ≤ lam (_root_.Dist.dist c O) := hanti hcd
  have ht : _root_.Dist.dist p c ≤ _root_.Dist.dist p q + _root_.Dist.dist q c := dist_triangle p q c
  rw [dist_comm q p] at hqp
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.dist_lt_two_lam then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.OrderedNet.dist_lt_two_lam"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.dist_lt_two_lam ``Submission.DifferentialGeometry.CheegerGromovCompactness.OrderedNet.dist_lt_two_lam

theorem netList_cover (O : M) {lam : ℝ → ℝ} (hlam : Continuous lam) (hanti : Antitone lam)
    (p : M) :
    ∀ α : ℕ,
      (availSet O lam (forbidden O lam (netList O lam hlam α)) = ∅ ∨
        ∃ c ∈ netList O lam hlam α, _root_.Dist.dist p O < _root_.Dist.dist c O) →
      ∃ c ∈ netList O lam hlam α,
        dist c O ≤ _root_.Dist.dist p O ∧ _root_.Dist.dist p c < 2 * lam (_root_.Dist.dist c O) := by
  intro α
  induction α with
  | zero =>
      intro hpast
      rcases hpast with hemp | ⟨c, hc, hlt⟩
      · have hp : p ∉ availSet O lam (forbidden O lam (netList O lam hlam 0)) := by
          rw [hemp]
          simp
        obtain ⟨c, hc, hmeet⟩ := meets_of_not_avail O lam hp
        rw [netList_zero, List.mem_singleton] at hc
        have hcd : _root_.Dist.dist c O ≤ _root_.Dist.dist p O := by
          rw [hc, dist_self]
          exact dist_nonneg
        refine ⟨c, ?_, hcd, dist_lt_two_lam hanti hcd hmeet⟩
        simp [hc]
      · rw [netList_zero, List.mem_singleton] at hc
        rw [hc, dist_self] at hlt
        exact absurd hlt (not_lt.mpr dist_nonneg)
  | succ α ih =>
      intro hpast
      by_cases hpastα : ∃ c ∈ netList O lam hlam α, _root_.Dist.dist p O < _root_.Dist.dist c O
      · obtain ⟨c, hc, hcd, hcb⟩ := ih (Or.inr hpastα)
        exact ⟨c, mem_netList_succ O lam hlam α hc, hcd, hcb⟩
      · push Not at hpastα
        by_cases h : (availSet O lam (forbidden O lam (netList O lam hlam α))).Nonempty
        · obtain ⟨x, hxeq, hxavail, hxmin⟩ := netList_succ_spec O lam hlam α h
          by_cases hxs : _root_.Dist.dist p O < _root_.Dist.dist x O
          · have hp : p ∉ availSet O lam (forbidden O lam (netList O lam hlam α)) :=
              fun hp => absurd (hxmin p hp) (not_le.mpr hxs)
            obtain ⟨c, hc, hmeet⟩ := meets_of_not_avail O lam hp
            have hcd : _root_.Dist.dist c O ≤ _root_.Dist.dist p O := hpastα c hc
            refine ⟨c, ?_, hcd, dist_lt_two_lam hanti hcd hmeet⟩
            rw [hxeq]
            exact List.mem_append_left _ hc
          · push Not at hxs
            rcases hpast with hemp | ⟨c, hc, hlt⟩
            · have hp :
                  p ∉ availSet O lam (forbidden O lam (netList O lam hlam (α + 1))) := by
                rw [hemp]
                simp
              obtain ⟨c, hc, hmeet⟩ := meets_of_not_avail O lam hp
              have hcd : _root_.Dist.dist c O ≤ _root_.Dist.dist p O := by
                rw [hxeq, List.mem_append] at hc
                rcases hc with hc | hc
                · exact hpastα c hc
                · rw [List.mem_singleton] at hc
                  subst hc
                  exact hxs
              exact ⟨c, hc, hcd, dist_lt_two_lam hanti hcd hmeet⟩
            · rw [hxeq, List.mem_append] at hc
              rcases hc with hc | hc
              · exact absurd hlt (not_lt.mpr (hpastα c hc))
              · rw [List.mem_singleton] at hc
                subst hc
                exact absurd hlt (not_lt.mpr hxs)
        · have hemp := Set.not_nonempty_iff_eq_empty.mp h
          have hp : p ∉ availSet O lam (forbidden O lam (netList O lam hlam α)) := by
            rw [hemp]
            simp
          obtain ⟨c, hc, hmeet⟩ := meets_of_not_avail O lam hp
          have hcd : _root_.Dist.dist c O ≤ _root_.Dist.dist p O := hpastα c hc
          refine ⟨c, ?_, hcd, dist_lt_two_lam hanti hcd hmeet⟩
          rw [netList_succ_stop O lam hlam α h]
          exact hc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList_cover then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList_cover"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList_cover ``Submission.DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList_cover

omit [ProperSpace M] in
theorem availSet_antitone (O : M) (lam : ℝ → ℝ) {U V : Set M} (hUV : U ⊆ V) :
    availSet O lam V ⊆ availSet O lam U :=
  fun _ hx => hx.mono_right hUV

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.availSet_antitone then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.OrderedNet.availSet_antitone"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.availSet_antitone ``Submission.DifferentialGeometry.CheegerGromovCompactness.OrderedNet.availSet_antitone

omit [ProperSpace M] in
theorem forbidden_mono (O : M) (lam : ℝ → ℝ) {l l' : List M} (h : ∀ a ∈ l, a ∈ l') :
    forbidden O lam l ⊆ forbidden O lam l' := by
  intro z hz
  simp only [forbidden, Set.mem_iUnion] at hz ⊢
  obtain ⟨c, hc, hzc⟩ := hz
  exact ⟨c, h c hc, hzc⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.forbidden_mono then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.OrderedNet.forbidden_mono"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.forbidden_mono ``Submission.DifferentialGeometry.CheegerGromovCompactness.OrderedNet.forbidden_mono

theorem availSet_succ_subset (O : M) (lam : ℝ → ℝ) (hlam : Continuous lam) (α : ℕ) :
    availSet O lam (forbidden O lam (netList O lam hlam (α + 1))) ⊆
      availSet O lam (forbidden O lam (netList O lam hlam α)) :=
  availSet_antitone O lam
    (forbidden_mono O lam fun _ ha => mem_netList_succ O lam hlam α ha)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.availSet_succ_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.OrderedNet.availSet_succ_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.availSet_succ_subset ``Submission.DifferentialGeometry.CheegerGromovCompactness.OrderedNet.availSet_succ_subset

theorem netList_dist_le_avail (O : M) (lam : ℝ → ℝ) (hlam : Continuous lam) (α : ℕ) :
    ∀ c ∈ netList O lam hlam α,
      ∀ y ∈ availSet O lam (forbidden O lam (netList O lam hlam α)),
        dist c O ≤ _root_.Dist.dist y O := by
  induction α with
  | zero =>
      intro c hc y _hy
      rw [netList_zero, List.mem_singleton] at hc
      rw [hc, dist_self]
      exact dist_nonneg
  | succ α ih =>
      intro c hc y hy
      have hyα := availSet_succ_subset O lam hlam α hy
      by_cases h : (availSet O lam (forbidden O lam (netList O lam hlam α))).Nonempty
      · obtain ⟨x, hxeq, hxavail, hxmin⟩ := netList_succ_spec O lam hlam α h
        rw [hxeq, List.mem_append] at hc
        rcases hc with hc | hc
        · exact ih c hc y hyα
        · rw [List.mem_singleton] at hc
          rw [hc]
          exact hxmin y hyα
      · rw [netList_succ_stop O lam hlam α h] at hc
        exact ih c hc y hyα

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList_dist_le_avail then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList_dist_le_avail"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList_dist_le_avail ``Submission.DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList_dist_le_avail

theorem netList_sorted (O : M) (lam : ℝ → ℝ) (hlam : Continuous lam) (α : ℕ) :
    (netList O lam hlam α).Pairwise fun a b => _root_.Dist.dist a O ≤ _root_.Dist.dist b O := by
  induction α with
  | zero =>
      rw [netList_zero]
      exact List.pairwise_singleton _ _
  | succ α ih =>
      by_cases h : (availSet O lam (forbidden O lam (netList O lam hlam α))).Nonempty
      · obtain ⟨x, hxeq, hxavail, _⟩ := netList_succ_spec O lam hlam α h
        rw [hxeq, List.pairwise_append]
        refine ⟨ih, List.pairwise_singleton _ _, ?_⟩
        intro a ha b hb
        rw [List.mem_singleton] at hb
        rw [hb]
        exact netList_dist_le_avail O lam hlam α a ha x hxavail
      · rw [netList_succ_stop O lam hlam α h]
        exact ih

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList_sorted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList_sorted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList_sorted ``Submission.DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList_sorted

theorem netList_separated (O : M) {lam : ℝ → ℝ} (hlam : Continuous lam)
    (hanti : Antitone lam) (hpos : ∀ s : ℝ, 0 < lam s) (α : ℕ)
    {x y : M} (hx : x ∈ netList O lam hlam α) (hy : y ∈ netList O lam hlam α)
    (hxy : x ≠ y) {r : ℝ} (hxr : _root_.Dist.dist x O ≤ r) :
    lam r ≤ _root_.Dist.dist x y := by
  have hpd : (netList O lam hlam α).Pairwise fun a b =>
      Disjoint (Metric.ball a (lam (_root_.Dist.dist a O))) (Metric.ball b (lam (_root_.Dist.dist b O))) :=
    netList_ballsDisjoint O lam hlam α
  have hsymm : Std.Symm fun a b : M =>
      Disjoint (Metric.ball a (lam (_root_.Dist.dist a O))) (Metric.ball b (lam (_root_.Dist.dist b O))) :=
    ⟨fun _ _ h => h.symm⟩
  have hdisj := @List.Pairwise.forall M _ _ hsymm hpd x hx y hy hxy
  by_contra hlt
  push Not at hlt
  have hyx : y ∈ Metric.ball x (lam (_root_.Dist.dist x O)) := by
    rw [Metric.mem_ball, dist_comm]
    exact lt_of_lt_of_le hlt (hanti hxr)
  exact Set.disjoint_left.mp hdisj hyx (Metric.mem_ball_self (hpos _))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList_separated then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList_separated"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList_separated ``Submission.DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList_separated

theorem netList_count_le (O : M) {lam : ℝ → ℝ} (hlam : Continuous lam)
    (hanti : Antitone lam) (hpos : ∀ s : ℝ, 0 < lam s) {A : ℝ → ℕ}
    (pack : ∀ (r : ℝ) (J : Finset M), (∀ x ∈ J, _root_.Dist.dist x O ≤ r) →
      (∀ x ∈ J, ∀ y ∈ J, x ≠ y → lam r ≤ _root_.Dist.dist x y) → J.card ≤ A r)
    (α : ℕ) (r : ℝ) (J : Finset M)
    (hJl : ∀ x ∈ J, x ∈ netList O lam hlam α)
    (hJr : ∀ x ∈ J, _root_.Dist.dist x O ≤ r) :
    J.card ≤ A r :=
  pack r J hJr fun x hx y hy hxy =>
    netList_separated O hlam hanti hpos α (hJl x hx) (hJl y hy) hxy (hJr x hx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList_count_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList_count_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList_count_le ``Submission.DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList_count_le

theorem netList_dist_ge (O : M) {lam : ℝ → ℝ} (hlam : Continuous lam)
    (hanti : Antitone lam) (hpos : ∀ s : ℝ, 0 < lam s) (α : ℕ)
    {c : M} (hc : c ∈ netList O lam hlam α) (hcO : c ≠ O) :
    lam 0 ≤ _root_.Dist.dist c O := by
  have h := netList_separated O hlam hanti hpos α (O_mem_netList O lam hlam α) hc
    hcO.symm (le_of_eq (dist_self O))
  rwa [dist_comm] at h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList_dist_ge then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList_dist_ge"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList_dist_ge ``Submission.DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList_dist_ge

theorem netList_dist_le (O : M) {lam : ℝ → ℝ} (hlam : Continuous lam)
    (hanti : Antitone lam) (hpos : ∀ s : ℝ, 0 < lam s)
    (hint : ∀ p : M, ∀ t : ℝ, 0 ≤ t → t ≤ _root_.Dist.dist p O → ∃ q : M, _root_.Dist.dist q O = t)
    (α : ℕ) : ∀ c ∈ netList O lam hlam α, _root_.Dist.dist c O ≤ 2 * lam 0 * (α : ℝ) := by
  induction α with
  | zero =>
      intro c hc
      rw [netList_zero, List.mem_singleton] at hc
      rw [hc, dist_self]
      simp
  | succ α ih =>
      intro c hc
      have hl0 : (0:ℝ) ≤ lam 0 := (hpos 0).le
      by_cases h : (availSet O lam (forbidden O lam (netList O lam hlam α))).Nonempty
      · obtain ⟨x, hxeq, hxavail, hxmin⟩ := netList_succ_spec O lam hlam α h
        rw [hxeq, List.mem_append] at hc
        rcases hc with hc | hc
        · have h1 := ih c hc
          push_cast
          nlinarith
        · rw [List.mem_singleton] at hc
          rw [hc]
          by_contra hgt
          push Not at hgt
          push_cast at hgt
          have ht0 : (0:ℝ) ≤ 2 * lam 0 * ((α : ℝ) + 1) :=
            mul_nonneg (by linarith) (by positivity)
          obtain ⟨q, hqO⟩ := hint x (2 * lam 0 * ((α : ℝ) + 1)) ht0 hgt.le
          have hqlt : _root_.Dist.dist q O < _root_.Dist.dist x O := by rw [hqO]; exact hgt
          have hqna : q ∉ availSet O lam (forbidden O lam (netList O lam hlam α)) :=
            fun hq => absurd (hxmin q hq) (not_le.mpr hqlt)
          obtain ⟨c', hc', hmeet⟩ := meets_of_not_avail O lam hqna
          obtain ⟨w, hwq, hwc⟩ := Set.not_disjoint_iff.mp hmeet
          rw [Metric.mem_ball] at hwq hwc
          have h1 : lam (_root_.Dist.dist q O) ≤ lam 0 := hanti dist_nonneg
          have h2 : lam (_root_.Dist.dist c' O) ≤ lam 0 := hanti dist_nonneg
          have hqc' : _root_.Dist.dist q c' < 2 * lam 0 := by
            have htri := dist_triangle q w c'
            rw [dist_comm w q] at hwq
            linarith
          have hc'O : _root_.Dist.dist c' O ≤ 2 * lam 0 * (α : ℝ) := ih c' hc'
          have hcontra : _root_.Dist.dist q O < 2 * lam 0 * ((α : ℝ) + 1) := by
            have htri := dist_triangle q c' O
            nlinarith
          rw [hqO] at hcontra
          exact absurd hcontra (lt_irrefl _)
      · rw [netList_succ_stop O lam hlam α h] at hc
        have h1 := ih c hc
        push_cast
        nlinarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList_dist_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList_dist_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList_dist_le ``Submission.DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList_dist_le

theorem netList_disjoint_of_le (O : M) {lam lam' : ℝ → ℝ} (hlam : Continuous lam)
    (hle : ∀ s : ℝ, lam' s ≤ lam s) (α : ℕ) :
    (netList O lam hlam α).Pairwise fun a b =>
      Disjoint (Metric.ball a (lam' (_root_.Dist.dist a O))) (Metric.ball b (lam' (_root_.Dist.dist b O))) := by
  have h : (netList O lam hlam α).Pairwise fun a b =>
      Disjoint (Metric.ball a (lam (_root_.Dist.dist a O))) (Metric.ball b (lam (_root_.Dist.dist b O))) :=
    netList_ballsDisjoint O lam hlam α
  exact h.imp fun hd =>
    hd.mono (Metric.ball_subset_ball (hle _)) (Metric.ball_subset_ball (hle _))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList_disjoint_of_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList_disjoint_of_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList_disjoint_of_le ``Submission.DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList_disjoint_of_le

theorem netList_prefix (O : M) (lam : ℝ → ℝ) (hlam : Continuous lam) {α β : ℕ}
    (h : α ≤ β) : netList O lam hlam α <+: netList O lam hlam β := by
  induction β, h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ β hαβ ih =>
      refine ih.trans ?_
      by_cases hav : (availSet O lam (forbidden O lam (netList O lam hlam β))).Nonempty
      · obtain ⟨x, hxeq, -, -⟩ := netList_succ_spec O lam hlam β hav
        rw [hxeq]
        exact List.prefix_append _ _
      · rw [netList_succ_stop O lam hlam β hav]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList_prefix then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList_prefix"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList_prefix ``Submission.DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList_prefix

theorem netList_stall (O : M) (lam : ℝ → ℝ) (hlam : Continuous lam) {α β : ℕ} (h : α ≤ β)
    (hav : ¬ (availSet O lam (forbidden O lam (netList O lam hlam α))).Nonempty) :
    netList O lam hlam β = netList O lam hlam α := by
  induction β, h using Nat.le_induction with
  | base => rfl
  | succ β hαβ ih =>
      have hstop : netList O lam hlam (β + 1) = netList O lam hlam β := by
        apply netList_succ_stop
        rw [ih]
        exact hav
      rw [hstop, ih]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList_stall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList_stall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList_stall ``Submission.DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList_stall

theorem netList_length_le (O : M) (lam : ℝ → ℝ) (hlam : Continuous lam) (α : ℕ) :
    (netList O lam hlam α).length ≤ α + 1 := by
  induction α with
  | zero => simp
  | succ α ih =>
      by_cases h : (availSet O lam (forbidden O lam (netList O lam hlam α))).Nonempty
      · obtain ⟨x, hxeq, -, -⟩ := netList_succ_spec O lam hlam α h
        rw [hxeq, List.length_append, List.length_singleton]
        omega
      · rw [netList_succ_stop O lam hlam α h]
        omega

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList_length_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList_length_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList_length_le ``Submission.DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList_length_le

theorem netList_length_eq_of_available (O : M) (lam : ℝ → ℝ) (hlam : Continuous lam) (α : ℕ)
    (h : ∀ γ < α, (availSet O lam (forbidden O lam (netList O lam hlam γ))).Nonempty) :
    (netList O lam hlam α).length = α + 1 := by
  induction α with
  | zero => simp
  | succ α ih =>
      obtain ⟨x, hxeq, -, -⟩ := netList_succ_spec O lam hlam α (h α (Nat.lt_succ_self α))
      rw [hxeq, List.length_append, List.length_singleton,
        ih fun γ hγ => h γ (hγ.trans (Nat.lt_succ_self α))]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList_length_eq_of_available then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList_length_eq_of_available"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList_length_eq_of_available ``Submission.DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList_length_eq_of_available

theorem netList_alive_of_le (O : M) (lam : ℝ → ℝ) (hlam : Continuous lam) {γ β : ℕ}
    (h : γ ≤ β) (hβ : γ < (netList O lam hlam β).length) :
    γ < (netList O lam hlam γ).length := by
  by_contra hγ
  push Not at hγ
  have hex : ∃ s < γ, ¬ (availSet O lam (forbidden O lam (netList O lam hlam s))).Nonempty := by
    by_contra hall
    push Not at hall
    have := netList_length_eq_of_available O lam hlam γ hall
    omega
  obtain ⟨s, hsγ, hs⟩ := hex
  have hstall := netList_stall O lam hlam (le_of_lt (hsγ.trans_le h)) hs
  have hlens := netList_length_le O lam hlam s
  rw [hstall] at hβ
  omega

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList_alive_of_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList_alive_of_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList_alive_of_le ``Submission.DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList_alive_of_le

theorem netList_nodup (O : M) {lam : ℝ → ℝ} (hlam : Continuous lam)
    (hpos : ∀ s : ℝ, 0 < lam s) (α : ℕ) : (netList O lam hlam α).Nodup := by
  have h := netList_ballsDisjoint O lam hlam α
  exact h.imp fun hd hab => by
    subst hab
    exact Set.disjoint_left.mp hd (Metric.mem_ball_self (hpos _))
      (Metric.mem_ball_self (hpos _))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList_nodup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList_nodup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList_nodup ``Submission.DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList_nodup

noncomputable def netCenter (O : M) (lam : ℝ → ℝ) (hlam : Continuous lam) (α : ℕ) :
    Option M :=
  (netList O lam hlam α)[α]?

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netCenter then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netCenter"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netCenter ``Submission.DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netCenter

theorem netCenter_eq (O : M) (lam : ℝ → ℝ) (hlam : Continuous lam) (α : ℕ) :
    netCenter O lam hlam α = (netList O lam hlam α)[α]? := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netCenter_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netCenter_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netCenter_eq ``Submission.DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netCenter_eq

theorem netCenter_zero (O : M) (lam : ℝ → ℝ) (hlam : Continuous lam) :
    netCenter O lam hlam 0 = _root_.Option.some O := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netCenter_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netCenter_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netCenter_zero ``Submission.DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netCenter_zero

theorem netCenter_lt_length (O : M) (lam : ℝ → ℝ) (hlam : Continuous lam) {α : ℕ}
    {x : M} (hx : netCenter O lam hlam α = _root_.Option.some x) :
    α < (netList O lam hlam α).length := by
  by_contra h
  push Not at h
  rw [netCenter_eq, List.getElem?_eq_none h] at hx
  simp at hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netCenter_lt_length then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netCenter_lt_length"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netCenter_lt_length ``Submission.DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netCenter_lt_length

noncomputable def netRadius (O : M) (lam : ℝ → ℝ) (hlam : Continuous lam) (α : ℕ) : ℝ :=
  match netCenter O lam hlam α with
  | some x => _root_.Dist.dist x O
  | none => 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netRadius then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netRadius"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netRadius ``Submission.DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netRadius

theorem netRadius_of_center (O : M) (lam : ℝ → ℝ) (hlam : Continuous lam) (α : ℕ)
    {x : M} (hx : netCenter O lam hlam α = _root_.Option.some x) :
    netRadius O lam hlam α = _root_.Dist.dist x O := by
  unfold netRadius
  rw [hx]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netRadius_of_center then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netRadius_of_center"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netRadius_of_center ``Submission.DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netRadius_of_center

theorem netCenter_mem (O : M) (lam : ℝ → ℝ) (hlam : Continuous lam) (α : ℕ) {x : M}
    (hx : netCenter O lam hlam α = _root_.Option.some x) : x ∈ netList O lam hlam α := by
  rw [netCenter_eq] at hx
  exact List.mem_of_getElem? hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netCenter_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netCenter_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netCenter_mem ``Submission.DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netCenter_mem

theorem netRadius_mem (O : M) {lam : ℝ → ℝ} (hlam : Continuous lam)
    (hanti : Antitone lam) (hpos : ∀ s : ℝ, 0 < lam s)
    (hint : ∀ p : M, ∀ t : ℝ, 0 ≤ t → t ≤ _root_.Dist.dist p O → ∃ q : M, _root_.Dist.dist q O = t) (α : ℕ) :
    netRadius O lam hlam α ∈ Set.Icc (0 : ℝ) (2 * lam 0 * (α : ℝ)) := by
  have hub : (0 : ℝ) ≤ 2 * lam 0 * (α : ℝ) :=
    mul_nonneg (mul_nonneg (by norm_num) (hpos 0).le) (Nat.cast_nonneg α)
  unfold netRadius
  cases hc : netCenter O lam hlam α with
  | none => exact ⟨le_refl 0, hub⟩
  | some x =>
      exact ⟨dist_nonneg,
        netList_dist_le O hlam hanti hpos hint α x (netCenter_mem O lam hlam α hc)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netRadius_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netRadius_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netRadius_mem ``Submission.DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netRadius_mem

theorem netCenter_of_stage (O : M) (lam : ℝ → ℝ) (hlam : Continuous lam) {γ β : ℕ}
    (h : γ ≤ β) (hβ : γ < (netList O lam hlam β).length) :
    netCenter O lam hlam γ = (netList O lam hlam β)[γ]? := by
  have hγ : γ < (netList O lam hlam γ).length := netList_alive_of_le O lam hlam h hβ
  obtain ⟨t, ht⟩ := netList_prefix O lam hlam h
  rw [netCenter_eq, ← ht, List.getElem?_append_left hγ]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netCenter_of_stage then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netCenter_of_stage"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netCenter_of_stage ``Submission.DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netCenter_of_stage

theorem netCenter_stable (O : M) (lam : ℝ → ℝ) (hlam : Continuous lam) {α β : ℕ}
    (h : α ≤ β) {x : M} (hx : netCenter O lam hlam α = _root_.Option.some x) :
    (netList O lam hlam β)[α]? = _root_.Option.some x := by
  have hlen := netCenter_lt_length O lam hlam hx
  obtain ⟨t, ht⟩ := netList_prefix O lam hlam h
  rw [← ht, List.getElem?_append_left hlen, ← netCenter_eq]
  exact hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netCenter_stable then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netCenter_stable"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netCenter_stable ``Submission.DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netCenter_stable

theorem netCenter_ne (O : M) {lam : ℝ → ℝ} (hlam : Continuous lam)
    (hpos : ∀ s : ℝ, 0 < lam s) {α β : ℕ} (hαβ : α ≠ β) {x y : M}
    (hx : netCenter O lam hlam α = _root_.Option.some x) (hy : netCenter O lam hlam β = _root_.Option.some y) :
    x ≠ y := by
  intro hxy
  subst hxy
  have hx' := netCenter_stable O lam hlam (le_max_left α β) hx
  have hy' := netCenter_stable O lam hlam (le_max_right α β) hy
  have hαl : α < (netList O lam hlam (_root_.Max.max α β)).length :=
    lt_of_lt_of_le (netCenter_lt_length O lam hlam hx)
      (List.IsPrefix.length_le (netList_prefix O lam hlam (le_max_left α β)))
  have hβl : β < (netList O lam hlam (_root_.Max.max α β)).length :=
    lt_of_lt_of_le (netCenter_lt_length O lam hlam hy)
      (List.IsPrefix.length_le (netList_prefix O lam hlam (le_max_right α β)))
  have hgα : (netList O lam hlam (_root_.Max.max α β))[α] = x := by
    rw [List.getElem?_eq_getElem hαl] at hx'
    exact Option.some.inj hx'
  have hgβ : (netList O lam hlam (_root_.Max.max α β))[β] = x := by
    rw [List.getElem?_eq_getElem hβl] at hy'
    exact Option.some.inj hy'
  have hnd := netList_nodup O hlam hpos (_root_.Max.max α β)
  rcases Nat.lt_trichotomy α β with h | h | h
  · exact (List.pairwise_iff_getElem.mp hnd) α β hαl hβl h (hgα.trans hgβ.symm)
  · exact hαβ h
  · exact (List.pairwise_iff_getElem.mp hnd) β α hβl hαl h (hgβ.trans hgα.symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netCenter_ne then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netCenter_ne"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netCenter_ne ``Submission.DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netCenter_ne

theorem netCenter_disjoint (O : M) {lam : ℝ → ℝ} (hlam : Continuous lam)
    (hpos : ∀ s : ℝ, 0 < lam s) {α β : ℕ} (hαβ : α ≠ β) {x y : M}
    (hx : netCenter O lam hlam α = _root_.Option.some x) (hy : netCenter O lam hlam β = _root_.Option.some y) :
    Disjoint (Metric.ball x (lam (_root_.Dist.dist x O))) (Metric.ball y (lam (_root_.Dist.dist y O))) := by
  have hxy := netCenter_ne O hlam hpos hαβ hx hy
  have hxm : x ∈ netList O lam hlam (_root_.Max.max α β) :=
    (netList_prefix O lam hlam (le_max_left α β)).subset (netCenter_mem O lam hlam α hx)
  have hym : y ∈ netList O lam hlam (_root_.Max.max α β) :=
    (netList_prefix O lam hlam (le_max_right α β)).subset (netCenter_mem O lam hlam β hy)
  have hpd : (netList O lam hlam (_root_.Max.max α β)).Pairwise fun a b =>
      Disjoint (Metric.ball a (lam (_root_.Dist.dist a O))) (Metric.ball b (lam (_root_.Dist.dist b O))) :=
    netList_ballsDisjoint O lam hlam (_root_.Max.max α β)
  have hsymm : Std.Symm fun a b : M =>
      Disjoint (Metric.ball a (lam (_root_.Dist.dist a O))) (Metric.ball b (lam (_root_.Dist.dist b O))) :=
    ⟨fun _ _ h => h.symm⟩
  exact @List.Pairwise.forall M _ _ hsymm hpd x hxm y hym hxy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netCenter_disjoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netCenter_disjoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netCenter_disjoint ``Submission.DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netCenter_disjoint

theorem netCenter_index_lt (O : M) {lam : ℝ → ℝ} (hlam : Continuous lam)
    (hanti : Antitone lam) (hpos : ∀ s : ℝ, 0 < lam s) {A : ℝ → ℕ}
    (pack : ∀ (r : ℝ) (J : Finset M), (∀ x ∈ J, _root_.Dist.dist x O ≤ r) →
      (∀ x ∈ J, ∀ y ∈ J, x ≠ y → lam r ≤ _root_.Dist.dist x y) → J.card ≤ A r)
    (α : ℕ) {x : M} (hx : netCenter O lam hlam α = _root_.Option.some x) {r : ℝ}
    (hxr : _root_.Dist.dist x O ≤ r) :
    α < A r := by
  classical
  have hlen := netCenter_lt_length O lam hlam hx
  have hxget : (netList O lam hlam α)[α] = x := by
    have heq := List.getElem?_eq_getElem hlen
    rw [netCenter_eq, heq] at hx
    exact Option.some.inj hx
  have hnd := netList_nodup O hlam hpos α
  have hcard : (netList O lam hlam α).toFinset.card = (netList O lam hlam α).length :=
    List.toFinset_card_of_nodup hnd
  have hsorted := netList_sorted O lam hlam α
  have hmemr : ∀ y ∈ (netList O lam hlam α).toFinset, _root_.Dist.dist y O ≤ r := by
    intro y hy
    rw [List.mem_toFinset] at hy
    obtain ⟨i, hi, hiy⟩ := List.mem_iff_getElem.mp hy
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp
      (hi.trans_le (netList_length_le O lam hlam α))) with hiα | hiα
    · have hle := (List.pairwise_iff_getElem.mp hsorted) i α hi hlen hiα
      rw [hiy, hxget] at hle
      exact hle.trans hxr
    · subst hiα
      have hyx : y = x := hiy.symm.trans hxget
      rw [hyx]
      exact hxr
  have hcount := netList_count_le O hlam hanti hpos pack α r
    (netList O lam hlam α).toFinset
    (fun y hy => List.mem_toFinset.mp hy) hmemr
  omega

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netCenter_index_lt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netCenter_index_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netCenter_index_lt ``Submission.DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netCenter_index_lt

theorem netList_passes (O : M) {lam : ℝ → ℝ} (hlam : Continuous lam)
    (hanti : Antitone lam) (hpos : ∀ s : ℝ, 0 < lam s) {A : ℝ → ℕ}
    (pack : ∀ (r : ℝ) (J : Finset M), (∀ x ∈ J, _root_.Dist.dist x O ≤ r) →
      (∀ x ∈ J, ∀ y ∈ J, x ≠ y → lam r ≤ _root_.Dist.dist x y) → J.card ≤ A r)
    (r : ℝ) :
    ∃ α : ℕ, availSet O lam (forbidden O lam (netList O lam hlam α)) = ∅ ∨
      ∃ c ∈ netList O lam hlam α, r < _root_.Dist.dist c O := by
  classical
  by_contra hcon
  push Not at hcon
  have hav : ∀ α, (availSet O lam (forbidden O lam (netList O lam hlam α))).Nonempty :=
    fun α => (hcon α).1
  have hbd : ∀ α, ∀ c ∈ netList O lam hlam α, _root_.Dist.dist c O ≤ r := fun α => (hcon α).2
  have hlen := netList_length_eq_of_available O lam hlam (A r + 1) fun γ _ => hav γ
  have hnd := netList_nodup O hlam hpos (A r + 1)
  have hcard : (netList O lam hlam (A r + 1)).toFinset.card = A r + 2 := by
    rw [List.toFinset_card_of_nodup hnd, hlen]
  have hle := netList_count_le O hlam hanti hpos pack (A r + 1) r
    (netList O lam hlam (A r + 1)).toFinset
    (fun y hy => List.mem_toFinset.mp hy)
    (fun y hy => hbd _ y (List.mem_toFinset.mp hy))
  omega

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList_passes then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList_passes"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList_passes ``Submission.DifferentialGeometry.CheegerGromovCompactness.OrderedNet.netList_passes

end OrderedNet

section SeqInstantiation

universe u' uE' uH'

variable {E : Type uE'} [NormedAddCommGroup E]
variable [InnerProductSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH'} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]
variable {X : PointedRiemannianSeq.{u', uE', uH'} (I := I)}

noncomputable def orderedNet (hd : InjectivityRadiusDecay (I := I) X) (D : Real)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)) (k α : Nat) :
    List ((X.obj k).M) :=
  letI : MetricSpace (X.obj k).M := (P k).ms
  haveI : ProperSpace (X.obj k).M := (P k).proper
  OrderedNet.netList (X.obj k).basepoint (hd.lambda D) (hd.lambda_continuous D) α

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.orderedNet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.orderedNet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.orderedNet ``Submission.DifferentialGeometry.CheegerGromovCompactness.orderedNet

omit [CompleteSpace E] in
theorem ProperMetricOn.dist_eq (hd : InjectivityRadiusDecay (I := I) X)
    (hre : hd.RealizesDistance) (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (k : Nat) (x y : (X.obj k).M) :
    (letI : MetricSpace (X.obj k).M := (P k).ms
     dist x y) = hd.dist k x y := by
  have h1 := (P k).realizes x y
  have h2 := hre.edist_eq k x y
  rw [h1] at h2
  exact (ENNReal.ofReal_eq_ofReal_iff
    (letI : MetricSpace (X.obj k).M := (P k).ms
     dist_nonneg) (hre.dist_nonneg k x y)).mp h2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.ProperMetricOn.dist_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.ProperMetricOn.dist_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.ProperMetricOn.dist_eq ``Submission.DifferentialGeometry.CheegerGromovCompactness.ProperMetricOn.dist_eq

omit [CompleteSpace E] in
theorem packingBound_pack (hd : InjectivityRadiusDecay (I := I) X)
    (hre : hd.RealizesDistance) {D : Real} (pb : hd.PackingBound D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)) (k : Nat) :
    letI : MetricSpace (X.obj k).M := (P k).ms
    ∀ (r : Real) (J : Finset ((X.obj k).M)),
      (∀ x ∈ J, _root_.Dist.dist x (X.obj k).basepoint ≤ r) →
      (∀ x ∈ J, ∀ y ∈ J, x ≠ y → hd.lambda D r ≤ _root_.Dist.dist x y) → J.card ≤ pb.A r := by
  let : MetricSpace (X.obj k).M := (P k).ms
  intro r J hJr hJsep
  refine pb.card_le k r J (fun x hx => ?_) (fun x hx y hy hxy => ?_)
  · rw [← ProperMetricOn.dist_eq hd hre P k]
    exact hJr x hx
  · rw [← ProperMetricOn.dist_eq hd hre P k]
    exact hJsep x hx y hy hxy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.packingBound_pack then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.packingBound_pack"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.packingBound_pack ``Submission.DifferentialGeometry.CheegerGromovCompactness.packingBound_pack

end SeqInstantiation

end CheegerGromovCompactness
end DifferentialGeometry
