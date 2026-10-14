import Submission.DifferentialGeometry.Topology.LoopSpace.Lipschitz
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Calculus.Rademacher

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Filter _root_.MeasureTheory
open scoped _root_.NNReal _root_.Topology

namespace DifferentialGeometry.Topology

variable {F : Type*}

private def joinedArcProfile (a b : ℝ → F) (t : ℝ) : F :=
  if t ≤ 1 / 2 then a (2 * t) else b (2 * t - 1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.joinedArcProfile
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.joinedArcProfile target :: scope.openDecls } }

def joinedLoop (a b : ℝ → F) (t : ℝ) : F :=
  AddCircle.liftIco (1 : ℝ) 0 (joinedArcProfile a b) (t : loopCircle)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.joinedLoop then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.joinedLoop"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.joinedLoop ``Submission.DifferentialGeometry.Topology.joinedLoop

theorem joinedLoop_periodic (a b : ℝ → F) : Function.Periodic (joinedLoop a b) 1 := by
  intro t
  simp only [joinedLoop, AddCircle.coe_add, AddCircle.coe_period, add_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.joinedLoop_periodic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.joinedLoop_periodic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.joinedLoop_periodic ``Submission.DifferentialGeometry.Topology.joinedLoop_periodic

private theorem liftIco_one_coe_Icc {g : ℝ → F} (hg : g 0 = g 1) {t : ℝ}
    (ht : t ∈ _root_.Set.Icc (0 : ℝ) 1) : AddCircle.liftIco (1 : ℝ) 0 g (t : loopCircle) = g t := by
  rcases lt_or_eq_of_le ht.2 with hlt | rfl
  · exact AddCircle.liftIco_zero_coe_apply ⟨ht.1, hlt⟩
  · rw [AddCircle.coe_period]
    exact (AddCircle.liftIco_zero_coe_apply (f := g) (by norm_num : (0 : ℝ) ∈ Ico 0 1)).trans hg

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.liftIco_one_coe_Icc
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.liftIco_one_coe_Icc target :: scope.openDecls } }

private theorem joinedArcProfile_endpoints {a b : ℝ → F} (hba : b 1 = a 0) :
    joinedArcProfile a b 0 = joinedArcProfile a b 1 := by
  norm_num [joinedArcProfile, hba]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.joinedArcProfile_endpoints
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.joinedArcProfile_endpoints target :: scope.openDecls } }

theorem joinedLoop_first {a b : ℝ → F} (hba : b 1 = a 0) {t : ℝ}
    (ht : t ∈ _root_.Set.Icc (0 : ℝ) (1 / 2)) : joinedLoop a b t = a (2 * t) := by
  rw [joinedLoop, liftIco_one_coe_Icc (joinedArcProfile_endpoints hba) ⟨ht.1, by linarith [ht.2]⟩]
  exact if_pos ht.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.joinedLoop_first then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.joinedLoop_first"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.joinedLoop_first ``Submission.DifferentialGeometry.Topology.joinedLoop_first

theorem joinedLoop_second {a b : ℝ → F} (hab : a 1 = b 0) (hba : b 1 = a 0) {t : ℝ}
    (ht : t ∈ _root_.Set.Icc (1 / 2 : ℝ) 1) : joinedLoop a b t = b (2 * t - 1) := by
  rw [joinedLoop, liftIco_one_coe_Icc (joinedArcProfile_endpoints hba) ⟨by linarith [ht.1], ht.2⟩]
  rcases eq_or_lt_of_le ht.1 with he | hlt
  · subst t
    simpa [joinedArcProfile] using hab
  · exact if_neg (not_le.mpr hlt)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.joinedLoop_second then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.joinedLoop_second"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.joinedLoop_second ``Submission.DifferentialGeometry.Topology.joinedLoop_second

section Metric

variable [PseudoMetricSpace F]

private theorem lipschitz_liftIco_one {g : ℝ → F} {C : ℝ≥0}
    (hg : LipschitzOnWith C g (_root_.Set.Icc (0 : ℝ) 1)) (h01 : g 0 = g 1) :
    LipschitzWith C (AddCircle.liftIco (1 : ℝ) 0 g) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  obtain ⟨b, d, hb0, hb1, hd0, hd1, hby, hbdx, hdist⟩ := exists_short_circle_lifts x y
  have hb : b ∈ _root_.Set.Icc (0 : ℝ) 1 := ⟨hb0, hb1⟩
  rw [hdist, ← hby, liftIco_one_coe_Icc h01 hb]
  by_cases hlo : b + d < 0
  · have hq : b + d + 1 ∈ _root_.Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    have hqx : ((b + d + 1 : ℝ) : loopCircle) = x := by
      rw [AddCircle.coe_add, AddCircle.coe_period, add_zero, hbdx]
    rw [← hqx, liftIco_one_coe_Icc h01 hq, abs_of_neg (by linarith : d < 0)]
    have h₁ := hg.dist_le_mul (b + d + 1) hq 1 (by norm_num)
    have h₂ := hg.dist_le_mul 0 (by norm_num) b hb
    rw [Real.dist_eq, abs_of_nonpos (by linarith : b + d + 1 - 1 ≤ 0)] at h₁
    rw [Real.dist_eq, abs_of_nonpos (by linarith : 0 - b ≤ 0)] at h₂
    have htri := dist_triangle (g (b + d + 1)) (g 1) (g b)
    rw [← h01] at h₁ htri
    nlinarith
  · by_cases hhi : 1 < b + d
    · have hq : b + d - 1 ∈ _root_.Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
      have hqx : ((b + d - 1 : ℝ) : loopCircle) = x := by
        rw [AddCircle.coe_sub, AddCircle.coe_period, sub_zero, hbdx]
      rw [← hqx, liftIco_one_coe_Icc h01 hq, abs_of_pos (by linarith : 0 < d)]
      have h₁ := hg.dist_le_mul (b + d - 1) hq 0 (by norm_num)
      have h₂ := hg.dist_le_mul 1 (by norm_num) b hb
      rw [Real.dist_eq, abs_of_nonneg (by linarith : 0 ≤ b + d - 1 - 0)] at h₁
      rw [Real.dist_eq, abs_of_nonneg (by linarith : 0 ≤ 1 - b)] at h₂
      have htri := dist_triangle (g (b + d - 1)) (g 0) (g b)
      rw [h01] at h₁ htri
      nlinarith
    · have hq : b + d ∈ _root_.Set.Icc (0 : ℝ) 1 := ⟨not_lt.mp hlo, not_lt.mp hhi⟩
      rw [← hbdx, liftIco_one_coe_Icc h01 hq]
      simpa only [Real.dist_eq, add_sub_cancel_left] using hg.dist_le_mul (b + d) hq b hb

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.lipschitz_liftIco_one
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.lipschitz_liftIco_one target :: scope.openDecls } }

private theorem lipschitz_joinedArcProfile {a b : ℝ → F} {Ka Kb : ℝ≥0}
    (ha : LipschitzWith Ka a) (hb : LipschitzWith Kb b) (hab : a 1 = b 0) :
    LipschitzWith (_root_.Max.max (2 * Ka) (2 * Kb)) (joinedArcProfile a b) := by
  let C := _root_.Max.max (2 * Ka) (2 * Kb)
  have hs : LipschitzWith 2 (fun t : ℝ => 2 * t) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [Real.dist_eq, ← mul_sub, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 2), NNReal.coe_ofNat]
    exact le_rfl
  have ha' : LipschitzWith C (fun t => a (2 * t)) := by
    apply (ha.comp hs).weaken
    simpa only [C, mul_comm Ka 2] using le_max_left (2 * Ka) (2 * Kb)
  have hs' : LipschitzWith 2 (fun t : ℝ => 2 * t - 1) := by
    simpa only [Function.comp_def, sub_eq_add_neg, one_mul] using
      (isometry_add_right (-1 : ℝ)).lipschitz.comp hs
  have hb' : LipschitzWith C (fun t => b (2 * t - 1)) := by
    apply (hb.comp hs').weaken
    simpa only [C, mul_comm Kb 2] using le_max_right (2 * Ka) (2 * Kb)
  have hordered (x y : ℝ) (hxy : x ≤ y) :
      dist (joinedArcProfile a b x) (joinedArcProfile a b y) ≤ (C : ℝ) * _root_.Dist.dist x y := by
    by_cases hy : y ≤ 1 / 2
    · rw [joinedArcProfile, if_pos (hxy.trans hy), joinedArcProfile, if_pos hy]
      exact ha'.dist_le_mul x y
    · by_cases hx : x ≤ 1 / 2
      · rw [joinedArcProfile, if_pos hx, joinedArcProfile, if_neg hy]
        have h₁ := ha'.dist_le_mul x (1 / 2)
        have h₂ := hb'.dist_le_mul (1 / 2) y
        norm_num only [mul_one_div_cancel (by norm_num : (2 : ℝ) ≠ 0), sub_self] at h₁ h₂
        rw [hab] at h₁
        have htri := dist_triangle (a (2 * x)) (b 0) (b (2 * y - 1))
        rw [Real.dist_eq, abs_of_nonpos (by linarith)] at h₁
        rw [Real.dist_eq, abs_of_nonpos (by linarith)] at h₂
        rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxy)]
        nlinarith
      · rw [joinedArcProfile, if_neg hx, joinedArcProfile, if_neg hy]
        exact hb'.dist_le_mul x y
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rcases le_total x y with hxy | hyx
  · exact hordered x y hxy
  · simpa only [dist_comm] using hordered y x hyx

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.lipschitz_joinedArcProfile
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.lipschitz_joinedArcProfile target :: scope.openDecls } }

theorem joinedLoop_lipschitz {a b : ℝ → F} {Ka Kb : ℝ≥0}
    (ha : LipschitzWith Ka a) (hb : LipschitzWith Kb b)
    (hab : a 1 = b 0) (hba : b 1 = a 0) :
    LipschitzWith (_root_.Max.max (2 * Ka) (2 * Kb)) (joinedLoop a b) := by
  change LipschitzWith _ ((AddCircle.liftIco (1 : ℝ) 0 (joinedArcProfile a b)) ∘
    (fun t : ℝ => (t : loopCircle)))
  simpa only [mul_one] using
    (lipschitz_liftIco_one (lipschitz_joinedArcProfile ha hb hab).lipschitzOnWith
      (joinedArcProfile_endpoints hba)).comp loopCircle_projection_lipschitz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.joinedLoop_lipschitz then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.joinedLoop_lipschitz"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.joinedLoop_lipschitz ``Submission.DifferentialGeometry.Topology.joinedLoop_lipschitz

end Metric

theorem mapsTo_joinedLoop {a b : ℝ → F} {S : Set F}
    (ha : _root_.Set.MapsTo a (_root_.Set.Icc (0 : ℝ) 1) S) (hb : _root_.Set.MapsTo b (_root_.Set.Icc (0 : ℝ) 1) S) :
    MapsTo (joinedLoop a b) _root_.Set.univ S := by
  intro t ht
  let s := AddCircle.equivIco (1 : ℝ) 0 (t : loopCircle)
  have hs : 0 ≤ (s : ℝ) ∧ (s : ℝ) < 1 := by simpa using s.property
  change joinedArcProfile a b s ∈ S
  by_cases hhalf : (s : ℝ) ≤ 1 / 2
  · rw [joinedArcProfile, if_pos hhalf]
    exact ha ⟨by linarith [hs.1], by linarith⟩
  · rw [joinedArcProfile, if_neg hhalf]
    exact hb ⟨by linarith, by linarith [hs.2]⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.mapsTo_joinedLoop then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.mapsTo_joinedLoop"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.mapsTo_joinedLoop ``Submission.DifferentialGeometry.Topology.mapsTo_joinedLoop

end DifferentialGeometry.Topology

end
