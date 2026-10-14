import Submission.DifferentialGeometry.Topology.LoopSpace.AnnulusSectors
import Submission.DifferentialGeometry.Analysis.Integration.Measure.ComplexNullLines
import Mathlib.MeasureTheory.Constructions.Polish.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.MeasureTheory _root_.Metric
open _root_.Submission.DifferentialGeometry.Analysis
open scoped _root_.Topology

namespace DifferentialGeometry.Topology



theorem unitSquare_ae_eq_sectors :
    unitSquare =ᵐ[_root_.MeasureTheory.MeasureSpace.volume] (annulusSector 0 ∪ annulusSector (1 / 2) : Set ℂ) := by
  filter_upwards [ae_complex_re_ne 0, ae_complex_re_ne 1, ae_complex_im_ne 0,
    ae_complex_im_ne (1 / 2), ae_complex_im_ne 1] with z hr₀ hr₁ hi₀ hiₘ hi₁
  apply propext
  constructor
  · rintro ⟨hr, hi⟩
    have hro : z.re ∈ _root_.Set.Ioo (0 : ℝ) 1 :=
      ⟨lt_of_le_of_ne hr.1 hr₀.symm, lt_of_le_of_ne hr.2 hr₁⟩
    by_cases hθ : z.im < 1 / 2
    · exact Or.inl ⟨hro, lt_of_le_of_ne hi.1 hi₀.symm, by simpa using hθ⟩
    · exact Or.inr ⟨hro, lt_of_le_of_ne (le_of_not_gt hθ) hiₘ.symm,
        by have h := lt_of_le_of_ne hi.2 hi₁; linarith⟩
  · rintro (h | h)
    · exact annulusSector_subset_square le_rfl (by norm_num) h
    · exact annulusSector_subset_square (by norm_num) (by norm_num) h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.unitSquare_ae_eq_sectors then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.unitSquare_ae_eq_sectors"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.unitSquare_ae_eq_sectors ``Submission.DifferentialGeometry.Topology.unitSquare_ae_eq_sectors

theorem disjoint_annulusSectors : Disjoint (annulusSector 0) (annulusSector (1 / 2)) := by
  apply disjoint_left.mpr
  intro z hz hw
  linarith [hz.2.2, hw.2.1]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.disjoint_annulusSectors then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.disjoint_annulusSectors"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.disjoint_annulusSectors ``Submission.DifferentialGeometry.Topology.disjoint_annulusSectors


theorem annulusPolarMap_injOn_sector (a : ℝ) : _root_.Set.InjOn annulusPolarMap (annulusSector a) := by
  intro z hz w hw heq
  apply dist_eq_zero.mp
  have h := annulusPolarMap_inverse_dist_le (_root_.Set.Ioo_subset_Icc_self hz.1)
    (_root_.Set.Ioo_subset_Icc_self hw.1) (_root_.Set.Ioo_subset_Icc_self hz.2) (_root_.Set.Ioo_subset_Icc_self hw.2)
  rw [heq, dist_self, _root_.MulZeroClass.mul_zero] at h
  exact le_antisymm h dist_nonneg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.annulusPolarMap_injOn_sector then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.annulusPolarMap_injOn_sector"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.annulusPolarMap_injOn_sector ``Submission.DifferentialGeometry.Topology.annulusPolarMap_injOn_sector

theorem measurableSet_annulusSector_image (a : ℝ) :
    MeasurableSet (annulusPolarMap '' annulusSector a) :=
  (isOpen_annulusSector a).measurableSet.image_of_continuousOn_injOn
    contDiff_annulusPolarMap.continuous.continuousOn (annulusPolarMap_injOn_sector a)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.measurableSet_annulusSector_image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.measurableSet_annulusSector_image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.measurableSet_annulusSector_image ``Submission.DifferentialGeometry.Topology.measurableSet_annulusSector_image

theorem annulusSector_image_norm {a : ℝ} {z : ℂ}
    (hz : z ∈ annulusPolarMap '' annulusSector a) : 1 / 2 < ‖z‖ ∧ ‖z‖ < 1 := by
  obtain ⟨w, hw, rfl⟩ := hz
  rw [norm_annulusPolarMap (_root_.Set.Ioo_subset_Icc_self hw.1)]
  constructor <;> linarith [hw.1.1, hw.1.2]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.annulusSector_image_norm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.annulusSector_image_norm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.annulusSector_image_norm ``Submission.DifferentialGeometry.Topology.annulusSector_image_norm

theorem disjoint_annulusSector_images :
    Disjoint (annulusPolarMap '' annulusSector 0) (annulusPolarMap '' annulusSector (1 / 2)) := by
  apply disjoint_left.mpr
  rintro z ⟨x, hx, rfl⟩ ⟨y, hy, heq⟩
  have hx' : x ∈ {z : ℂ | z.re ∈ _root_.Set.Icc (0 : ℝ) 1 ∧ z.im ∈ _root_.Set.Ico (0 : ℝ) 1} :=
    ⟨Ioo_subset_Icc_self hx.1, hx.2.1.le, by linarith [hx.2.2]⟩
  have hy' : y ∈ {z : ℂ | z.re ∈ _root_.Set.Icc (0 : ℝ) 1 ∧ z.im ∈ _root_.Set.Ico (0 : ℝ) 1} :=
    ⟨Ioo_subset_Icc_self hy.1, by linarith [hy.2.1], by linarith [hy.2.2]⟩
  have hxy := annulusPolarMap_injective_on_period hx' hy' heq.symm
  exact disjoint_annulusSectors.le_bot ⟨hx, hxy ▸ hy⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.disjoint_annulusSector_images then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.disjoint_annulusSector_images"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.disjoint_annulusSector_images ``Submission.DifferentialGeometry.Topology.disjoint_annulusSector_images



theorem mem_annulusSector_images_of_im_ne_zero {z : ℂ}
    (hz : 1 / 2 < ‖z‖ ∧ ‖z‖ < 1) (hzi : z.im ≠ 0) :
    z ∈ annulusPolarMap '' annulusSector 0 ∪ annulusPolarMap '' annulusSector (1 / 2) := by
  let θ := (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm (radialDirection z)
  obtain ⟨t, ht, htθ⟩ := AddCircle.eq_coe_Ico θ
  have hcircle : AddCircle.toCircle (t : loopCircle) = radialDirection z := by
    rw [htθ, ← AddCircle.homeomorphCircle_apply one_ne_zero]
    exact (AddCircle.homeomorphCircle one_ne_zero).apply_symm_apply _
  let w : ℂ := ⟨2 * ‖z‖ - 1, t⟩
  have hφ : annulusPolarMap w = z := by
    change ((2 * ‖z‖ - 1 + 1) / 2 : ℝ) • (AddCircle.toCircle (t : loopCircle) : ℂ) = z
    rw [hcircle, show (2 * ‖z‖ - 1 + 1) / 2 = ‖z‖ by ring]
    exact radialDirection_reconstruct z
  have ht₀ : t ≠ 0 := by
    intro heq
    apply hzi
    rw [← hφ]
    simp [annulusPolarMap, w, heq]
  have htₘ : t ≠ 1 / 2 := by
    intro heq
    apply hzi
    have hc : (AddCircle.toCircle (t : loopCircle) : ℂ) = -1 := by
      rw [heq, AddCircle.toCircle_apply_mk, Circle.coe_exp, div_one,
        show 2 * Real.pi * (1 / 2) = Real.pi by ring, Complex.exp_pi_mul_I]
    rw [← hφ]
    change (((2 * ‖z‖ - 1 + 1) / 2 : ℝ) • (AddCircle.toCircle (t : loopCircle) : ℂ)).im = 0
    rw [hc]
    simp
  have hwr : w.re ∈ _root_.Set.Ioo (0 : ℝ) 1 := by
    change 0 < 2 * ‖z‖ - 1 ∧ 2 * ‖z‖ - 1 < 1
    constructor <;> linarith [hz.1, hz.2]
  by_cases htlt : t < 1 / 2
  · exact Or.inl ⟨w, ⟨hwr, lt_of_le_of_ne ht.1 ht₀.symm, by simpa [w] using htlt⟩, hφ⟩
  · exact Or.inr ⟨w, ⟨hwr, lt_of_le_of_ne (le_of_not_gt htlt) htₘ.symm,
      by dsimp [w]; linarith [ht.2]⟩, hφ⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.mem_annulusSector_images_of_im_ne_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.mem_annulusSector_images_of_im_ne_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.mem_annulusSector_images_of_im_ne_zero ``Submission.DifferentialGeometry.Topology.mem_annulusSector_images_of_im_ne_zero



theorem closedDisk_ae_eq_annulusPieces :
    _root_.Metric.closedBall (0 : ℂ) 1 =ᵐ[_root_.MeasureTheory.MeasureSpace.volume]
      (_root_.Metric.closedBall (0 : ℂ) (1 / 2) ∪
        (annulusPolarMap '' annulusSector 0 ∪ annulusPolarMap '' annulusSector (1 / 2)) : Set ℂ) := by
  have hcircle : ∀ᵐ z : ℂ ∂volume, ‖z‖ ≠ 1 := by
    rw [_root_.MeasureTheory.ae_iff]
    convert MeasureTheory.Measure.addHaar_sphere _root_.MeasureTheory.MeasureSpace.volume (0 : ℂ) 1 using 1
    congr 1
    ext z
    simp
  filter_upwards [hcircle, ae_complex_im_ne 0] with z hz₁ hzi
  apply propext
  constructor
  · intro hz
    change _root_.Dist.dist z 0 ≤ 1 at hz
    have hzn : ‖z‖ ≤ 1 := by simpa only [dist_zero_right] using hz
    by_cases hhalf : ‖z‖ ≤ 1 / 2
    · exact Or.inl (by simpa only [_root_.Metric.mem_closedBall, dist_zero_right] using hhalf)
    · exact Or.inr (mem_annulusSector_images_of_im_ne_zero
        ⟨lt_of_not_ge hhalf, lt_of_le_of_ne hzn hz₁⟩ hzi)
  · rintro (hz | hz | hz)
    · exact _root_.Metric.closedBall_subset_closedBall (by norm_num : (1 / 2 : ℝ) ≤ 1) hz
    · change _root_.Dist.dist z 0 ≤ 1
      rw [dist_zero_right]
      exact (annulusSector_image_norm hz).2.le
    · change _root_.Dist.dist z 0 ≤ 1
      rw [dist_zero_right]
      exact (annulusSector_image_norm hz).2.le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.closedDisk_ae_eq_annulusPieces then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.closedDisk_ae_eq_annulusPieces"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.closedDisk_ae_eq_annulusPieces ``Submission.DifferentialGeometry.Topology.closedDisk_ae_eq_annulusPieces

theorem disjoint_halfDisk_annulusSector (a : ℝ) :
    Disjoint (_root_.Metric.closedBall (0 : ℂ) (1 / 2)) (annulusPolarMap '' annulusSector a) := by
  apply disjoint_left.mpr
  intro z hz hzi
  have hzn : ‖z‖ ≤ 1 / 2 := by simpa only [_root_.Metric.mem_closedBall, dist_zero_right] using hz
  exact (not_lt_of_ge hzn) (annulusSector_image_norm hzi).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.disjoint_halfDisk_annulusSector then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.disjoint_halfDisk_annulusSector"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.disjoint_halfDisk_annulusSector ``Submission.DifferentialGeometry.Topology.disjoint_halfDisk_annulusSector

end DifferentialGeometry.Topology
