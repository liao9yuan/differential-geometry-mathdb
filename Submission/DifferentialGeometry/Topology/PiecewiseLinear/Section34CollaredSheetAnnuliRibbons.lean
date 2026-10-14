import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34CollaredSheetAnnuliModel
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34FillingRibbonContacts

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsCylindricalDiagram.inter_region_of_base_inter_eq_zero
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E × ℝ → F} {P B Q : Set E} {C R : Set F}
    (hf : IsCylindricalDiagram f P C) (hends : ∀ p ∈ P, f (p, 0) = f (p, 1))
    (hBP : B ⊆ P) (hQP : Q ⊆ P) (hBQ : B ∩ Q = {0})
    (hregion : f '' (Q ×ˢ _root_.Set.Icc (0 : ℝ) 1) = C ∩ R) :
    f '' (B ×ˢ _root_.Set.Icc (0 : ℝ) 1) ∩ R = f '' ({0} ×ˢ _root_.Set.Icc (0 : ℝ) 1) := by
  have hBC : f '' (B ×ˢ _root_.Set.Icc (0 : ℝ) 1) ⊆ C :=
    (_root_.Set.image_mono (_root_.Set.prod_mono_left hBP)).trans hf.image_eq.subset
  calc
    f '' (B ×ˢ _root_.Set.Icc (0 : ℝ) 1) ∩ R = f '' (B ×ˢ _root_.Set.Icc (0 : ℝ) 1) ∩ (C ∩ R) := by
      ext x
      exact ⟨fun h => ⟨h.1, hBC h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
    _ = f '' ({0} ×ˢ _root_.Set.Icc (0 : ℝ) 1) := by
      rw [← hregion, hf.inter_images_base_regions hends hBP hQP, hBQ]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.inter_region_of_base_inter_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.inter_region_of_base_inter_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.inter_region_of_base_inter_eq_zero ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.inter_region_of_base_inter_eq_zero

theorem section34_outgoing_radial_bases (a b : Bool) {d : ℝ} (hd : 0 ≤ d) (hd1 : d ≤ 1) :
    let B₀ := (fun r : ℝ => r • (if a then (-1 : ℝ) else 1, (0 : ℝ))) '' _root_.Set.Icc 0 d
    let B₁ := (fun r : ℝ => r • ((0 : ℝ), if b then (-1 : ℝ) else 1)) '' _root_.Set.Icc 0 d
    B₀ ⊆ spliceSquare ∧ B₁ ⊆ spliceSquare ∧
      B₀ ∩ section34CrossingQuadrant a b = {0} ∧
      B₁ ∩ section34CrossingQuadrant a b = {0} := by
  dsimp only
  have h₀ : (fun r : ℝ => r • (if a then (-1 : ℝ) else 1, (0 : ℝ))) '' _root_.Set.Icc 0 d ⊆
      spliceSquare := by
    rintro _ ⟨r, hr, rfl⟩
    cases a <;> simp only [Bool.false_eq_true, ↓reduceIte, Prod.smul_mk, smul_eq_mul,
      mul_neg_one, mul_one, _root_.MulZeroClass.mul_zero, spliceSquare, _root_.Set.mem_prod, _root_.Set.mem_Icc]
    all_goals constructor <;> constructor <;> linarith [hr.1, hr.2]
  have h₁ : (fun r : ℝ => r • ((0 : ℝ), if b then (-1 : ℝ) else 1)) '' _root_.Set.Icc 0 d ⊆
      spliceSquare := by
    rintro _ ⟨r, hr, rfl⟩
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, Prod.smul_mk, smul_eq_mul,
      mul_neg_one, mul_one, _root_.MulZeroClass.mul_zero, spliceSquare, _root_.Set.mem_prod, _root_.Set.mem_Icc]
    all_goals constructor <;> constructor <;> linarith [hr.1, hr.2]
  refine ⟨h₀, h₁, ?_, ?_⟩
  · apply Subset.antisymm
    · rintro _ ⟨⟨r, hr, rfl⟩, hq⟩
      have hr0 : r = 0 := by
        cases a <;> cases b <;>
          simp only [section34CrossingQuadrant, Bool.false_eq_true, ↓reduceIte,
            Prod.smul_mk, smul_eq_mul, mul_neg_one, mul_one, _root_.MulZeroClass.mul_zero,
            _root_.Set.mem_prod, _root_.Set.mem_Icc] at hq <;> linarith [hr.1]
      simp [hr0]
    · rintro p (rfl : p = 0)
      exact ⟨⟨0, ⟨le_rfl, hd⟩, zero_smul _ _⟩,
        by cases a <;> cases b <;> norm_num [section34CrossingQuadrant, Prod.le_def]⟩
  · apply Subset.antisymm
    · rintro _ ⟨⟨r, hr, rfl⟩, hq⟩
      have hr0 : r = 0 := by
        cases a <;> cases b <;>
          simp only [section34CrossingQuadrant, Bool.false_eq_true, ↓reduceIte,
            Prod.smul_mk, smul_eq_mul, mul_neg_one, mul_one, _root_.MulZeroClass.mul_zero,
            _root_.Set.mem_prod, _root_.Set.mem_Icc] at hq <;> linarith [hr.1]
      simp [hr0]
    · rintro p (rfl : p = 0)
      exact ⟨⟨0, ⟨le_rfl, hd⟩, zero_smul _ _⟩,
        by cases a <;> cases b <;> norm_num [section34CrossingQuadrant, Prod.le_def]⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34_outgoing_radial_bases then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34_outgoing_radial_bases"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34_outgoing_radial_bases ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34_outgoing_radial_bases

theorem IsCylindricalDiagram.outgoing_ribbon_annuli
    {f : (ℝ × ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)}
    {C R : Set (EuclideanSpace ℝ (Fin 3))} (hf : IsCylindricalDiagram f spliceSquare C)
    (hends : ∀ p ∈ spliceSquare, f (p, 0) = f (p, 1)) {a b : Bool} {d : ℝ}
    (hd : 0 < d) (hd1 : d ≤ 1)
    (hregion : f '' (section34CrossingQuadrant a b ×ˢ _root_.Set.Icc (0 : ℝ) 1) = C ∩ R) :
    let v₀ : ℝ × ℝ := (if a then -1 else 1, 0)
    let v₁ : ℝ × ℝ := (0, if b then -1 else 1)
    let Y₀ := f '' (((fun r : ℝ => r • v₀) '' _root_.Set.Icc 0 d) ×ˢ _root_.Set.Icc (0 : ℝ) 1)
    let Y₁ := f '' (((fun r : ℝ => r • v₁) '' _root_.Set.Icc 0 d) ×ˢ _root_.Set.Icc (0 : ℝ) 1)
    IsPLAnnulusWithEnds Y₀ (f '' section34MarkedAxis)
      (f '' ({d • v₀} ×ˢ _root_.Set.Icc (0 : ℝ) 1)) ∧
    IsPLAnnulusWithEnds Y₁ (f '' section34MarkedAxis)
      (f '' ({d • v₁} ×ˢ _root_.Set.Icc (0 : ℝ) 1)) ∧
    Y₀ ⊆ C ∧ Y₁ ⊆ C ∧ Y₀ ∩ R = f '' section34MarkedAxis ∧
      Y₁ ∩ R = f '' section34MarkedAxis := by
  obtain ⟨hB₀, hB₁, hB₀Q, hB₁Q⟩ := section34_outgoing_radial_bases a b hd.le hd1
  have hv₀ : (if a then (-1 : ℝ) else 1, (0 : ℝ)) ≠ 0 := by cases a <;> norm_num
  have hv₁ : ((0 : ℝ), if b then (-1 : ℝ) else 1) ≠ 0 := by cases b <;> norm_num
  exact ⟨hf.isPLAnnulusWithEnds_radial_band hends hv₀ hd hB₀,
    hf.isPLAnnulusWithEnds_radial_band hends hv₁ hd hB₁,
    (_root_.Set.image_mono (_root_.Set.prod_mono_left hB₀)).trans hf.image_eq.subset,
    (_root_.Set.image_mono (_root_.Set.prod_mono_left hB₁)).trans hf.image_eq.subset,
    hf.inter_region_of_base_inter_eq_zero hends hB₀
      (section34_crossing_quadrant_subset_square a b) hB₀Q hregion,
    hf.inter_region_of_base_inter_eq_zero hends hB₁
      (section34_crossing_quadrant_subset_square a b) hB₁Q hregion⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.outgoing_ribbon_annuli then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.outgoing_ribbon_annuli"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.outgoing_ribbon_annuli ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.outgoing_ribbon_annuli

end DifferentialGeometry.Topology.PiecewiseLinear
