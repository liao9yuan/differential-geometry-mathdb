import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34CrossingNeighborhoodQuadrants

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

def section34CornerBase (a b : Bool) : Set (ℝ × ℝ) :=
  ((if a then _root_.Set.Icc (0 : ℝ) (1 / 2) else _root_.Set.Icc (-1 / 2 : ℝ) 0) ×ˢ {0}) ∪
    ({0} ×ˢ (if b then _root_.Set.Icc (0 : ℝ) (1 / 2) else _root_.Set.Icc (-1 / 2 : ℝ) 0))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34CornerBase then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34CornerBase"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34CornerBase ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34CornerBase

noncomputable def section34CornerPush (a b : Bool) (z : (ℝ × ℝ) × ℝ) : ℝ × ℝ :=
  (z.1.1 + (if a then z.2 / 2 else -z.2 / 2),
    z.1.2 + (if b then z.2 / 2 else -z.2 / 2))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34CornerPush then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34CornerPush"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34CornerPush ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34CornerPush

theorem section34_corner_base_isPolyhedron (a b : Bool) :
    IsPolyhedron (section34CornerBase a b) := by
  cases a <;> cases b <;>
    exact (isHPolytope_Icc.isPolyhedron.prod (isHPolytope_singleton _).isPolyhedron).union
      ((isHPolytope_singleton _).isPolyhedron.prod isHPolytope_Icc.isPolyhedron)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34_corner_base_isPolyhedron then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34_corner_base_isPolyhedron"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34_corner_base_isPolyhedron ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34_corner_base_isPolyhedron

theorem section34_corner_base_subset (a b : Bool) :
    section34CornerBase a b ⊆ section34CrossingQuadrant a b := by
  cases a <;> cases b <;> rintro ⟨x, y⟩ (⟨hx, hy⟩ | ⟨hx, hy⟩) <;>
    simp only [Bool.false_eq_true, ↓reduceIte, _root_.Set.mem_Icc, _root_.Set.mem_singleton_iff] at * <;>
    rcases (by assumption : _ ∧ _) with ⟨h₀, h₁⟩ <;>
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34_corner_base_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34_corner_base_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34_corner_base_subset ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34_corner_base_subset

theorem section34_corner_push_zero (a b : Bool) (p : ℝ × ℝ) :
    section34CornerPush a b (p, 0) = p := by simp [section34CornerPush]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34_corner_push_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34_corner_push_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34_corner_push_zero ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34_corner_push_zero

theorem section34_corner_push_injOn (a b : Bool) :
    InjOn (section34CornerPush a b) (section34CornerBase a b ×ˢ _root_.Set.Icc (0 : ℝ) 1) := by
  intro z hz w hw hzw
  have hx := congrArg Prod.fst hzw
  have hy := congrArg Prod.snd hzw
  cases a <;> cases b <;>
    rcases hz with ⟨⟨hzx, hzy⟩ | ⟨hzx, hzy⟩, hzt⟩ <;>
    rcases hw with ⟨⟨hwx, hwy⟩ | ⟨hwx, hwy⟩, hwt⟩ <;>
    simp only [section34CornerPush, Bool.false_eq_true, ↓reduceIte] at hx hy <;>
    simp only [Bool.false_eq_true, ↓reduceIte, _root_.Set.mem_Icc, _root_.Set.mem_singleton_iff] at * <;>
    apply Prod.ext <;> first
    | apply Prod.ext <;> linarith
    | linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34_corner_push_injOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34_corner_push_injOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34_corner_push_injOn ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34_corner_push_injOn

theorem section34_corner_push_mapsTo (a b : Bool) :
    _root_.Set.MapsTo (section34CornerPush a b) (section34CornerBase a b ×ˢ _root_.Set.Icc (0 : ℝ) 1)
      (section34CrossingQuadrant a b) := by
  cases a <;> cases b <;>
    rintro ⟨⟨x, y⟩, t⟩ ⟨⟨hx, hy⟩ | ⟨hx, hy⟩, ht⟩ <;>
    simp only [Bool.false_eq_true, ↓reduceIte, _root_.Set.mem_Icc, _root_.Set.mem_singleton_iff] at * <;>
    exact ⟨⟨by dsimp [section34CornerPush]; linarith,
      by dsimp [section34CornerPush]; linarith⟩,
      by dsimp [section34CornerPush]; linarith,
      by dsimp [section34CornerPush]; linarith⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34_corner_push_mapsTo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34_corner_push_mapsTo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34_corner_push_mapsTo ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34_corner_push_mapsTo

theorem section34_corner_push_sheet_contacts (a b : Bool) {p : ℝ × ℝ} {t : ℝ}
    (hp : p ∈ section34CornerBase a b) (ht : t ∈ _root_.Set.Icc (0 : ℝ) 1) :
    ((section34CornerPush a b (p, t)).1 = 0 ↔ p.1 = 0 ∧ t = 0) ∧
      ((section34CornerPush a b (p, t)).2 = 0 ↔ p.2 = 0 ∧ t = 0) := by
  cases a <;> cases b <;> rcases hp with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;>
    simp only [Bool.false_eq_true, ↓reduceIte, _root_.Set.mem_Icc, _root_.Set.mem_singleton_iff] at * <;>
    constructor <;> constructor
  all_goals first
    | intro h; constructor <;> dsimp [section34CornerPush] at h <;> linarith
    | rintro ⟨h, rfl⟩; simpa only [section34_corner_push_zero] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34_corner_push_sheet_contacts then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34_corner_push_sheet_contacts"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34_corner_push_sheet_contacts ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34_corner_push_sheet_contacts

theorem section34_corner_push_isPLHomeomorphOn (a b : Bool) :
    IsPLHomeomorphOn (section34CornerPush a b)
      (section34CornerBase a b ×ˢ _root_.Set.Icc (0 : ℝ) 1)
      (section34CornerPush a b '' (section34CornerBase a b ×ˢ _root_.Set.Icc (0 : ℝ) 1)) := by
  let L : ((ℝ × ℝ) × ℝ) →ₗ[ℝ] ℝ × ℝ :=
    { toFun := section34CornerPush a b
      map_add' := by
        intro z w
        cases a <;> cases b <;> ext <;> simp [section34CornerPush] <;> ring
      map_smul' := by
        intro c z
        cases a <;> cases b <;> ext <;> simp [section34CornerPush] <;> ring }
  have hP : IsPolyhedron (section34CornerBase a b ×ˢ _root_.Set.Icc (0 : ℝ) 1) :=
    (section34_corner_base_isPolyhedron a b).prod isHPolytope_Icc.isPolyhedron
  exact isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hP
    ((isPiecewiseAffineOn_of_affine L.toAffineMap isOpen_univ).mono_of_isPolyhedron hP
      (_root_.Set.subset_univ _)) (section34_corner_push_injOn a b).bijOn_image

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34_corner_push_isPLHomeomorphOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34_corner_push_isPLHomeomorphOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34_corner_push_isPLHomeomorphOn ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34_corner_push_isPLHomeomorphOn

end DifferentialGeometry.Topology.PiecewiseLinear
