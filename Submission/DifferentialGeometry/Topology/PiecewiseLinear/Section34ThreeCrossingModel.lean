import Submission.DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Prism

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

noncomputable def section34ZigzagHeight (x : ℝ) : ℝ := x - 3 / 2 * _root_.Max.max (-1) (_root_.Min.min 1 x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34ZigzagHeight then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34ZigzagHeight"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34ZigzagHeight ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34ZigzagHeight

noncomputable def section34ZigzagArc (t : ℝ) : ℝ × ℝ :=
  (4 * t - 2, section34ZigzagHeight (4 * t - 2))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34ZigzagArc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34ZigzagArc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34ZigzagArc ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34ZigzagArc

noncomputable def section34StraightArc (t : ℝ) : ℝ × ℝ := (4 * t - 2, t - 1 / 2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34StraightArc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34StraightArc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34StraightArc ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34StraightArc

def section34CrossingRectangle : Set (ℝ × ℝ) := _root_.Set.Icc (-2) 2 ×ˢ _root_.Set.Icc (-1) 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34CrossingRectangle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34CrossingRectangle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34CrossingRectangle ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34CrossingRectangle

theorem section34ZigzagHeight_eq_zero_iff (x : ℝ) :
    section34ZigzagHeight x = 0 ↔ x = -3 / 2 ∨ x = 0 ∨ x = 3 / 2 := by
  unfold section34ZigzagHeight
  by_cases hleft : x ≤ -1
  · rw [min_eq_right (by linarith : x ≤ 1), max_eq_left hleft]
    constructor
    · intro h
      exact Or.inl (by linarith)
    · rintro (rfl | rfl | rfl) <;> norm_num at *
  · by_cases hright : 1 ≤ x
    · rw [min_eq_left hright, max_eq_right (by norm_num : (-1 : ℝ) ≤ 1)]
      constructor
      · intro h
        exact Or.inr (Or.inr (by linarith))
      · rintro (rfl | rfl | rfl) <;> norm_num at *
    · rw [min_eq_right (le_of_not_ge hright), max_eq_right (le_of_not_ge hleft)]
      constructor
      · intro h
        exact Or.inr (Or.inl (by linarith))
      · rintro (rfl | rfl | rfl) <;> norm_num at *

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34ZigzagHeight_eq_zero_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34ZigzagHeight_eq_zero_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34ZigzagHeight_eq_zero_iff ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34ZigzagHeight_eq_zero_iff

theorem section34ZigzagHeight_bounds {x : ℝ} (hx : x ∈ _root_.Set.Icc (-2 : ℝ) 2) :
    section34ZigzagHeight x ∈ _root_.Set.Icc (-1 / 2 : ℝ) (1 / 2) := by
  unfold section34ZigzagHeight
  by_cases hleft : x ≤ -1
  · rw [min_eq_right (by linarith : x ≤ 1), max_eq_left hleft]
    exact ⟨by linarith [hx.1], by linarith⟩
  · by_cases hright : 1 ≤ x
    · rw [min_eq_left hright, max_eq_right (by norm_num : (-1 : ℝ) ≤ 1)]
      exact ⟨by linarith, by linarith [hx.2]⟩
    · rw [min_eq_right (le_of_not_ge hright), max_eq_right (le_of_not_ge hleft)]
      exact ⟨by linarith, by linarith⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34ZigzagHeight_bounds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34ZigzagHeight_bounds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34ZigzagHeight_bounds ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34ZigzagHeight_bounds

theorem isPiecewiseAffineOn_section34ZigzagHeight :
    IsPiecewiseAffineOn section34ZigzagHeight univ := by
  have hx := isPiecewiseAffineOn_id (E := ℝ) isOpen_univ
  have hm := (isPiecewiseAffineOn_of_affine (AffineMap.const ℝ ℝ (1 : ℝ)) isOpen_univ).min hx
  have hc := (isPiecewiseAffineOn_of_affine (AffineMap.const ℝ ℝ (-1 : ℝ)) isOpen_univ).max hm
  have h := hx.add (hc.affine_comp (LinearMap.lsmul ℝ ℝ (-3 / 2 : ℝ)).toAffineMap)
  convert h using 1
  ext x
  simp [section34ZigzagHeight, smul_eq_mul]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_section34ZigzagHeight then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_section34ZigzagHeight"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_section34ZigzagHeight ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_section34ZigzagHeight

theorem isPLHomeomorphOn_section34ZigzagArc :
    IsPLHomeomorphOn section34ZigzagArc (_root_.Set.Icc 0 1) (section34ZigzagArc '' _root_.Set.Icc 0 1) := by
  let a : ℝ →ᵃ[ℝ] ℝ := 4 • AffineMap.id ℝ ℝ - AffineMap.const ℝ ℝ 2
  have ha : IsPiecewiseAffineOn a univ := isPiecewiseAffineOn_of_affine a isOpen_univ
  have hg := isPiecewiseAffineOn_section34ZigzagHeight.comp ha
  rw [_root_.Set.preimage_univ, _root_.Set.inter_univ] at hg
  have hp : IsPiecewiseAffineOn section34ZigzagArc univ := by
    apply (ha.prod_mk hg).congr
    intro x _
    simp [a, section34ZigzagArc]
  have hi : _root_.Set.InjOn section34ZigzagArc (_root_.Set.Icc 0 1) := by
    intro s _ t _ hst
    have heq := congrArg Prod.fst hst
    change 4 * s - 2 = 4 * t - 2 at heq
    linarith
  exact isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn isHPolytope_Icc.isPolyhedron
    (hp.mono_of_isPolyhedron isHPolytope_Icc.isPolyhedron (_root_.Set.subset_univ _)) hi.bijOn_image

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_section34ZigzagArc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_section34ZigzagArc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_section34ZigzagArc ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_section34ZigzagArc

theorem isPLHomeomorphOn_section34StraightArc :
    IsPLHomeomorphOn section34StraightArc (_root_.Set.Icc 0 1) (section34StraightArc '' _root_.Set.Icc 0 1) := by
  let a : ℝ →ᵃ[ℝ] ℝ × ℝ :=
    (4 • AffineMap.id ℝ ℝ - AffineMap.const ℝ ℝ 2).prod
      (AffineMap.id ℝ ℝ - AffineMap.const ℝ ℝ (1 / 2))
  have hp : IsPiecewiseAffineOn section34StraightArc univ := by
    apply (isPiecewiseAffineOn_of_affine a isOpen_univ).congr
    intro x _
    simp [a, section34StraightArc]
  have hi : _root_.Set.InjOn section34StraightArc (_root_.Set.Icc 0 1) := by
    intro s _ t _ hst
    have heq := congrArg Prod.fst hst
    change 4 * s - 2 = 4 * t - 2 at heq
    linarith
  exact isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn isHPolytope_Icc.isPolyhedron
    (hp.mono_of_isPolyhedron isHPolytope_Icc.isPolyhedron (_root_.Set.subset_univ _)) hi.bijOn_image

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_section34StraightArc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_section34StraightArc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_section34StraightArc ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_section34StraightArc

theorem section34ZigzagArc_endpoints :
    section34ZigzagArc 0 = section34StraightArc 0 ∧
      section34ZigzagArc 1 = section34StraightArc 1 := by
  norm_num [section34ZigzagArc, section34ZigzagHeight, section34StraightArc]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34ZigzagArc_endpoints then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34ZigzagArc_endpoints"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34ZigzagArc_endpoints ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34ZigzagArc_endpoints

theorem section34ZigzagArc_three_crossings :
    (section34ZigzagArc '' _root_.Set.Icc 0 1) ∩ {p : ℝ × ℝ | p.2 = 0} =
      {(-3 / 2, 0), (0, 0), (3 / 2, 0)} := by
  apply Subset.antisymm
  · rintro _ ⟨⟨t, ht, rfl⟩, hz⟩
    have h := (section34ZigzagHeight_eq_zero_iff (4 * t - 2)).mp hz
    rcases h with h | h | h
    · left
      exact Prod.ext h hz
    · right
      left
      exact Prod.ext h hz
    · right
      right
      exact Prod.ext h hz
  · rintro p (rfl | rfl | rfl)
    · refine ⟨⟨1 / 8, by norm_num, ?_⟩, rfl⟩
      norm_num [section34ZigzagArc, section34ZigzagHeight]
    · refine ⟨⟨1 / 2, by norm_num, ?_⟩, rfl⟩
      norm_num [section34ZigzagArc, section34ZigzagHeight]
    · refine ⟨⟨7 / 8, by norm_num, ?_⟩, rfl⟩
      norm_num [section34ZigzagArc, section34ZigzagHeight]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34ZigzagArc_three_crossings then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34ZigzagArc_three_crossings"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34ZigzagArc_three_crossings ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34ZigzagArc_three_crossings

theorem section34StraightArc_one_crossing :
    (section34StraightArc '' _root_.Set.Icc 0 1) ∩ {p : ℝ × ℝ | p.2 = 0} = {(0, 0)} := by
  apply Subset.antisymm
  · rintro _ ⟨⟨t, ht, rfl⟩, hz⟩
    have ht' : t = 1 / 2 := by change t - 1 / 2 = 0 at hz; linarith
    subst t
    norm_num [section34StraightArc]
  · rintro p rfl
    exact ⟨⟨1 / 2, by norm_num, by norm_num [section34StraightArc]⟩, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34StraightArc_one_crossing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34StraightArc_one_crossing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34StraightArc_one_crossing ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34StraightArc_one_crossing

theorem isPLBall_section34CrossingRectangle : IsPLBall 2 section34CrossingRectangle :=
  isPLBall_two_prod (isPLBall_Icc (by norm_num)) (isPLBall_Icc (by norm_num))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_section34CrossingRectangle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_section34CrossingRectangle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_section34CrossingRectangle ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_section34CrossingRectangle

def section34HorizontalArc (t : ℝ) : ℝ × ℝ := (4 * t - 2, 0)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34HorizontalArc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34HorizontalArc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34HorizontalArc ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34HorizontalArc

theorem isPLHomeomorphOn_section34HorizontalArc :
    IsPLHomeomorphOn section34HorizontalArc (_root_.Set.Icc 0 1) (section34HorizontalArc '' _root_.Set.Icc 0 1) := by
  let a : ℝ →ᵃ[ℝ] ℝ × ℝ :=
    (4 • AffineMap.id ℝ ℝ - AffineMap.const ℝ ℝ 2).prod (AffineMap.const ℝ ℝ (0 : ℝ))
  have hp : IsPiecewiseAffineOn section34HorizontalArc univ := by
    apply (isPiecewiseAffineOn_of_affine a isOpen_univ).congr
    intro x _
    simp [a, section34HorizontalArc]
  have hi : _root_.Set.InjOn section34HorizontalArc (_root_.Set.Icc 0 1) := by
    intro s _ t _ hst
    have heq := congrArg Prod.fst hst
    change 4 * s - 2 = 4 * t - 2 at heq
    linarith
  exact isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn isHPolytope_Icc.isPolyhedron
    (hp.mono_of_isPolyhedron isHPolytope_Icc.isPolyhedron (_root_.Set.subset_univ _)) hi.bijOn_image

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_section34HorizontalArc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_section34HorizontalArc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_section34HorizontalArc ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_section34HorizontalArc

theorem section34HorizontalArc_image : section34HorizontalArc '' _root_.Set.Icc 0 1 =
    section34CrossingRectangle ∩ {p : ℝ × ℝ | p.2 = 0} := by
  apply Subset.antisymm
  · rintro _ ⟨t, ht, rfl⟩
    refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, rfl⟩
    · dsimp [section34HorizontalArc]
      linarith [ht.1]
    · dsimp [section34HorizontalArc]
      linarith [ht.2]
    · norm_num [section34HorizontalArc]
    · norm_num [section34HorizontalArc]
  · rintro p ⟨hp, hz⟩
    refine ⟨(p.1 + 2) / 4, ⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩, ?_⟩
    apply Prod.ext
    · dsimp [section34HorizontalArc]
      ring
    · exact hz.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34HorizontalArc_image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34HorizontalArc_image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34HorizontalArc_image ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34HorizontalArc_image

end DifferentialGeometry.Topology.PiecewiseLinear
