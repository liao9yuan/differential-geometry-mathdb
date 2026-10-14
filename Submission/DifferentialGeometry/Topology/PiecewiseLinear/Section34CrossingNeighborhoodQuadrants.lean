import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34CrossingNeighborhoodQuadrantsSigns

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

def section34CrossingQuadrant (a b : Bool) : Set (ℝ × ℝ) :=
  (if a then _root_.Set.Icc (0 : ℝ) 1 else _root_.Set.Icc (-1 : ℝ) 0) ×ˢ
    (if b then _root_.Set.Icc (0 : ℝ) 1 else _root_.Set.Icc (-1 : ℝ) 0)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34CrossingQuadrant then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34CrossingQuadrant"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34CrossingQuadrant ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34CrossingQuadrant

theorem section34_crossing_quadrant_subset_square (a b : Bool) :
    section34CrossingQuadrant a b ⊆ spliceSquare := by
  cases a <;> cases b <;>
    rintro ⟨x, y⟩ ⟨⟨hx₀, hx₁⟩, ⟨hy₀, hy₁⟩⟩ <;>
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34_crossing_quadrant_subset_square then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34_crossing_quadrant_subset_square"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34_crossing_quadrant_subset_square ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34_crossing_quadrant_subset_square

theorem IsCylindricalDiagram.crossing_neighborhood_quadrant_images
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : (ℝ × ℝ) × ℝ → E} {C X Y : Set E}
    (hf : IsCylindricalDiagram f spliceSquare C)
    (hends : ∀ x ∈ spliceSquare, f (x, 0) = f (x, 1))
    (hfirst : f '' (section34MarkedRibbon 0 ∪ section34MarkedRibbon 2) = C ∩ frontier X)
    (hsecond : f '' (section34MarkedRibbon 1 ∪ section34MarkedRibbon 3) = C ∩ frontier Y)
    (hpages : ∀ i : Fin 4, f '' section34MarkedRibbon i = C ∩
      ![frontier X ∩ Y, frontier Y ∩ X, frontier X \ interior Y, frontier Y \ interior X] i)
    (hX : IsClosed X) (hY : IsClosed Y) (a b : Bool) :
    f '' (section34CrossingQuadrant a b ×ˢ _root_.Set.Icc (0 : ℝ) 1) =
      C ∩ (if b then X else (interior X)ᶜ) ∩ (if a then Y else (interior Y)ᶜ) := by
  have hread := hf.crossing_neighborhood_sign_readings hends hfirst hsecond hpages hX hY
  have hmem (p : (ℝ × ℝ) × ℝ) (hp : p ∈ spliceCylinder) :
      p.1 ∈ section34CrossingQuadrant a b ↔
        f p ∈ (if b then X else (interior X)ᶜ) ∩
          (if a then Y else (interior Y)ᶜ) := by
    have h := hread p hp
    cases a <;> cases b <;>
      simp only [section34CrossingQuadrant, Bool.false_eq_true, ↓reduceIte,
        _root_.Set.mem_prod, _root_.Set.mem_Icc, _root_.Set.mem_inter_iff, _root_.Set.mem_compl_iff, h.1, h.2.1, h.2.2.1, h.2.2.2,
        not_lt] <;>
      constructor <;> intro hh
    all_goals first
      | exact ⟨hh.2.2, hh.1.2⟩
      | exact ⟨hh.2.1, hh.1.2⟩
      | exact ⟨hh.2.2, hh.1.1⟩
      | exact ⟨hh.2.1, hh.1.1⟩
      | exact ⟨⟨hp.1.1.1, hh.2⟩, hp.1.2.1, hh.1⟩
      | exact ⟨⟨hp.1.1.1, hh.2⟩, hh.1, hp.1.2.2⟩
      | exact ⟨⟨hh.2, hp.1.1.2⟩, hp.1.2.1, hh.1⟩
      | exact ⟨⟨hh.2, hp.1.1.2⟩, hh.1, hp.1.2.2⟩
  apply Subset.antisymm
  · rintro y ⟨p, hp, rfl⟩
    have hpC : p ∈ spliceCylinder :=
      ⟨section34_crossing_quadrant_subset_square a b hp.1, hp.2⟩
    exact ⟨⟨hf.image_eq ▸ _root_.Set.mem_image_of_mem f hpC, ((hmem p hpC).mp hp.1).1⟩,
      ((hmem p hpC).mp hp.1).2⟩
  · rintro y ⟨⟨hyC, hyX⟩, hyY⟩
    obtain ⟨p, hp, rfl⟩ := hf.image_eq.symm.subset hyC
    exact ⟨p, ⟨(hmem p hp).mpr ⟨hyX, hyY⟩, hp.2⟩, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.crossing_neighborhood_quadrant_images then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.crossing_neighborhood_quadrant_images"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.crossing_neighborhood_quadrant_images ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.crossing_neighborhood_quadrant_images

end DifferentialGeometry.Topology.PiecewiseLinear
