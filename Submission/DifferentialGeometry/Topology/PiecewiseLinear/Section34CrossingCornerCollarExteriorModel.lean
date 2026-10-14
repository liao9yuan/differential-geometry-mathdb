import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34CrossingCornerCollarModel

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

noncomputable def section34CornerExteriorPush (a b : Bool) (z : (ℝ × ℝ) × ℝ) : ℝ × ℝ :=
  section34CornerPush a b (z.1, -z.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34CornerExteriorPush then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34CornerExteriorPush"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34CornerExteriorPush ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34CornerExteriorPush

theorem section34_corner_exterior_push_zero (a b : Bool) (p : ℝ × ℝ) :
    section34CornerExteriorPush a b (p, 0) = p := by
  simp [section34CornerExteriorPush, section34_corner_push_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34_corner_exterior_push_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34_corner_exterior_push_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34_corner_exterior_push_zero ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34_corner_exterior_push_zero

theorem section34_corner_exterior_push_injOn (a b : Bool) :
    InjOn (section34CornerExteriorPush a b) (section34CornerBase a b ×ˢ _root_.Set.Icc (0 : ℝ) 1) := by
  intro z hz w hw hzw
  have hx := congrArg Prod.fst hzw
  have hy := congrArg Prod.snd hzw
  cases a <;> cases b <;>
    rcases hz with ⟨⟨hzx, hzy⟩ | ⟨hzx, hzy⟩, hzt⟩ <;>
    rcases hw with ⟨⟨hwx, hwy⟩ | ⟨hwx, hwy⟩, hwt⟩ <;>
    simp only [section34CornerExteriorPush, section34CornerPush,
      Bool.false_eq_true, ↓reduceIte] at hx hy <;>
    simp only [Bool.false_eq_true, ↓reduceIte, _root_.Set.mem_Icc, _root_.Set.mem_singleton_iff] at * <;>
    apply Prod.ext <;> first
    | apply Prod.ext <;> linarith
    | linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34_corner_exterior_push_injOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34_corner_exterior_push_injOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34_corner_exterior_push_injOn ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34_corner_exterior_push_injOn

theorem section34_corner_exterior_push_mapsTo (a b : Bool) :
    _root_.Set.MapsTo (section34CornerExteriorPush a b) (section34CornerBase a b ×ˢ _root_.Set.Icc (0 : ℝ) 1)
      spliceSquare := by
  cases a <;> cases b <;>
    rintro ⟨⟨x, y⟩, t⟩ ⟨⟨hx, hy⟩ | ⟨hx, hy⟩, ht⟩ <;>
    simp only [Bool.false_eq_true, ↓reduceIte, _root_.Set.mem_Icc, _root_.Set.mem_singleton_iff] at * <;>
    exact ⟨⟨by dsimp [section34CornerExteriorPush, section34CornerPush]; linarith,
      by dsimp [section34CornerExteriorPush, section34CornerPush]; linarith⟩,
      by dsimp [section34CornerExteriorPush, section34CornerPush]; linarith,
      by dsimp [section34CornerExteriorPush, section34CornerPush]; linarith⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34_corner_exterior_push_mapsTo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34_corner_exterior_push_mapsTo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34_corner_exterior_push_mapsTo ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34_corner_exterior_push_mapsTo

theorem section34_corner_exterior_push_mem_quadrant (a b : Bool) {p : ℝ × ℝ} {t : ℝ}
    (hp : p ∈ section34CornerBase a b) (ht : t ∈ _root_.Set.Icc (0 : ℝ) 1) :
    section34CornerExteriorPush a b (p, t) ∈ section34CrossingQuadrant a b ↔ t = 0 := by
  constructor
  · intro h
    cases a <;> cases b <;> rcases hp with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;>
      simp only [Bool.false_eq_true, ↓reduceIte, _root_.Set.mem_Icc, _root_.Set.mem_singleton_iff] at * <;>
      dsimp [section34CornerExteriorPush, section34CornerPush, section34CrossingQuadrant] at h <;>
      rcases h with ⟨⟨hx₀, hx₁⟩, ⟨hy₀, hy₁⟩⟩ <;>
      linarith
  · rintro rfl
    rw [section34_corner_exterior_push_zero]
    exact section34_corner_base_subset a b hp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34_corner_exterior_push_mem_quadrant then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34_corner_exterior_push_mem_quadrant"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34_corner_exterior_push_mem_quadrant ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34_corner_exterior_push_mem_quadrant

theorem section34_corner_exterior_push_sheet_contacts (a b : Bool) (p : ℝ × ℝ) (t : ℝ) :
    ((section34CornerExteriorPush a b (p, t)).1 = 0 ↔
      p.1 = (if a then t / 2 else -t / 2)) ∧
      ((section34CornerExteriorPush a b (p, t)).2 = 0 ↔
        p.2 = (if b then t / 2 else -t / 2)) := by
  cases a <;> cases b <;>
    simp only [section34CornerExteriorPush, section34CornerPush,
      Bool.false_eq_true, ↓reduceIte] <;>
    constructor <;> constructor <;> intro h <;> linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34_corner_exterior_push_sheet_contacts then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34_corner_exterior_push_sheet_contacts"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34_corner_exterior_push_sheet_contacts ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34_corner_exterior_push_sheet_contacts

theorem section34_corner_exterior_push_isPLHomeomorphOn (a b : Bool) :
    IsPLHomeomorphOn (section34CornerExteriorPush a b)
      (section34CornerBase a b ×ˢ _root_.Set.Icc (0 : ℝ) 1)
      (section34CornerExteriorPush a b '' (section34CornerBase a b ×ˢ _root_.Set.Icc (0 : ℝ) 1)) := by
  let L : ((ℝ × ℝ) × ℝ) →ₗ[ℝ] ℝ × ℝ :=
    { toFun := section34CornerExteriorPush a b
      map_add' := by
        intro z w
        cases a <;> cases b <;> ext <;>
          simp [section34CornerExteriorPush, section34CornerPush] <;> ring
      map_smul' := by
        intro c z
        cases a <;> cases b <;> ext <;>
          simp [section34CornerExteriorPush, section34CornerPush] <;> ring }
  have hP : IsPolyhedron (section34CornerBase a b ×ˢ _root_.Set.Icc (0 : ℝ) 1) :=
    (section34_corner_base_isPolyhedron a b).prod isHPolytope_Icc.isPolyhedron
  exact isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hP
    ((isPiecewiseAffineOn_of_affine L.toAffineMap isOpen_univ).mono_of_isPolyhedron hP
      (_root_.Set.subset_univ _)) (section34_corner_exterior_push_injOn a b).bijOn_image

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34_corner_exterior_push_isPLHomeomorphOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34_corner_exterior_push_isPLHomeomorphOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34_corner_exterior_push_isPLHomeomorphOn ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34_corner_exterior_push_isPLHomeomorphOn

end DifferentialGeometry.Topology.PiecewiseLinear
