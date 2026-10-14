import Submission.DifferentialGeometry.Topology.LocallyLipschitzOperations
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Filter
open scoped _root_.Topology

section

variable {X Y Z : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y] [PseudoEMetricSpace Z]

open _root_.LocallyLipschitzOn in
theorem LocallyLipschitzOn.prodMk {f : X → Y} {g : X → Z} {s : Set X}
    (hf : LocallyLipschitzOn s f) (hg : LocallyLipschitzOn s g) :
    LocallyLipschitzOn s (fun x => (f x, g x)) :=
  locallyLipschitzOn_iff_restrict.mpr (hf.restrict.prodMk hg.restrict)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LocallyLipschitzOn.prodMk then
    throwError "Refusing to shadow existing declaration LocallyLipschitzOn.prodMk"
  Lean.modifyEnv fun env => Lean.addAlias env `LocallyLipschitzOn.prodMk ``Submission.LocallyLipschitzOn.prodMk

end

theorem locallyLipschitz_of_lipschitzOn_closedBall
    {X Y : Type*} [PseudoMetricSpace X] [PseudoEMetricSpace Y] {f : X → Y} (p : X)
    (hf : ∀ R : ℝ, 0 ≤ R → ∃ K, LipschitzOnWith K f (Metric.closedBall p R)) :
    LocallyLipschitz f := by
  intro x
  obtain ⟨K, hK⟩ := hf (_root_.Dist.dist x p + 1) (by positivity)
  exact ⟨K, Metric.closedBall p (_root_.Dist.dist x p + 1),
    Metric.closedBall_mem_nhds_of_mem (by linarith : dist x p < dist x p + 1), hK⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `locallyLipschitz_of_lipschitzOn_closedBall then
    throwError "Refusing to shadow existing declaration locallyLipschitz_of_lipschitzOn_closedBall"
  Lean.modifyEnv fun env => Lean.addAlias env `locallyLipschitz_of_lipschitzOn_closedBall ``Submission.locallyLipschitz_of_lipschitzOn_closedBall

variable {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] [Zero Y]

open scoped _root_.NNReal in
open _root_.Metric in
open _root_.LocallyLipschitzOn in
theorem LocallyLipschitzOn.exists_lipschitzWith_of_hasCompactSupport
    {f : X → Y} {Ω : Set X} (hf : LocallyLipschitzOn Ω f)
    (hΩ : IsOpen Ω) (hfc : HasCompactSupport f) (hfs : tsupport f ⊆ Ω) :
    ∃ C : ℝ≥0, LipschitzWith C f := by
  classical
  have hlocal (x : tsupport f) : ∃ C : ℝ≥0, ∃ U : Set X,
      IsOpen U ∧ x.1 ∈ U ∧ LipschitzOnWith C f U := by
    obtain ⟨C, U, hU, hC⟩ := hf (hfs x.2)
    rw [hΩ.nhdsWithin_eq (hfs x.2)] at hU
    obtain ⟨W, hWU, hW, hxW⟩ := _root_.mem_nhds_iff.mp hU
    exact ⟨C, W, hW, hxW, hC.mono hWU⟩
  choose C U hU hxU hC using hlocal
  obtain ⟨s, hs⟩ := hfc.isCompact.elim_finite_subcover U hU
    (fun x hx => _root_.Set.mem_iUnion_of_mem ⟨x, hx⟩ (hxU ⟨x, hx⟩))
  have hcover : tsupport f ⊆ ⋃ i : s, U i.1 := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hs hx)
    exact _root_.Set.mem_iUnion_of_mem ⟨i, hi⟩ hxi
  obtain ⟨δ, hδ, hδU⟩ := lebesgue_number_lemma_of_metric hfc.isCompact
    (fun i : s => hU i.1) hcover
  obtain ⟨B, hB⟩ := hfc.isCompact.bddAbove_image
    (continuous_dist.comp_continuousOn
      ((hf.continuousOn.mono hfs).prodMk continuousOn_const))
  let B' : ℝ≥0 := ⟨max B 0, le_max_right _ _⟩
  let D : ℝ≥0 := ⟨2 * (B' : ℝ) / δ, div_nonneg (by positivity) hδ.le⟩
  let K := s.sup C
  have hbound (x : X) : _root_.Dist.dist (f x) 0 ≤ (B' : ℝ) := by
    by_cases hx : x ∈ tsupport f
    · exact (hB (_root_.Set.mem_image_of_mem _ hx)).trans (le_max_left _ _)
    · rw [image_eq_zero_of_notMem_tsupport hx, dist_self]
      exact B'.coe_nonneg
  have hone (x y : X) (hx : x ∈ tsupport f) :
      dist (f x) (f y) ≤ ((K + D : ℝ≥0) : ℝ) * _root_.Dist.dist x y := by
    by_cases hdist : _root_.Dist.dist x y < δ
    · obtain ⟨i, hi⟩ := hδU x hx
      have hnear := (hC i.1).dist_le_mul x (hi (_root_.Metric.mem_ball_self hδ))
        y (hi (by simpa only [_root_.Metric.mem_ball, dist_comm] using hdist))
      have hle : C i.1 ≤ K + D := (Finset.le_sup i.2).trans (le_add_of_nonneg_right (show 0 ≤ D from zero_le))
      exact hnear.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hle) dist_nonneg)
    · have hdist' : δ ≤ _root_.Dist.dist x y := le_of_not_gt hdist
      calc
        dist (f x) (f y) ≤ _root_.Dist.dist (f x) 0 + _root_.Dist.dist (f y) 0 := dist_triangle_right _ _ _
        _ ≤ 2 * (B' : ℝ) := by linarith [hbound x, hbound y]
        _ = (D : ℝ) * δ := by dsimp [D]; exact (div_mul_cancel₀ _ hδ.ne').symm
        _ ≤ (D : ℝ) * _root_.Dist.dist x y := mul_le_mul_of_nonneg_left hdist' D.coe_nonneg
        _ ≤ ((K + D : ℝ≥0) : ℝ) * _root_.Dist.dist x y :=
          mul_le_mul_of_nonneg_right (by simp) dist_nonneg
  refine ⟨K + D, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  by_cases hx : x ∈ tsupport f
  · exact hone x y hx
  · by_cases hy : y ∈ tsupport f
    · simpa only [dist_comm] using hone y x hy
    · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hy, dist_self]
      positivity

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LocallyLipschitzOn.exists_lipschitzWith_of_hasCompactSupport then
    throwError "Refusing to shadow existing declaration LocallyLipschitzOn.exists_lipschitzWith_of_hasCompactSupport"
  Lean.modifyEnv fun env => Lean.addAlias env `LocallyLipschitzOn.exists_lipschitzWith_of_hasCompactSupport ``Submission.LocallyLipschitzOn.exists_lipschitzWith_of_hasCompactSupport

open scoped _root_.ENNReal _root_.NNReal in
theorem lipschitzWith_truncateToReal_edist {X : Type*} [PseudoEMetricSpace X]
    (K : ℝ≥0) (R : ℝ≥0∞) (hR : R ≠ ⊤) (o : X) :
    LipschitzWith K (fun x => ENNReal.truncateToReal R ((K : ℝ≥0∞) * _root_.EDist.edist o x)) := by
  by_cases hK : K = 0
  · subst K
    simpa only [ENNReal.coe_zero, _root_.MulZeroClass.zero_mul] using
      (LipschitzWith.const (ENNReal.truncateToReal R 0) :
        LipschitzWith 0 (fun _ : X => ENNReal.truncateToReal R 0))
  intro x y
  by_cases hxy : _root_.EDist.edist x y = ⊤
  · rw [hxy, ENNReal.mul_top (by exact_mod_cast hK)]
    exact le_top
  have hfin (z : X) : _root_.Min.min R ((K : ℝ≥0∞) * _root_.EDist.edist o z) ≠ ⊤ :=
    ne_top_of_le_ne_top hR (min_le_left _ _)
  have hstep (z w : X) (hzw : _root_.EDist.edist z w ≠ ⊤) :
      ENNReal.truncateToReal R ((K : ℝ≥0∞) * _root_.EDist.edist o z) ≤
        ENNReal.truncateToReal R ((K : ℝ≥0∞) * _root_.EDist.edist o w) + (K : ℝ) * (_root_.EDist.edist z w).toReal := by
    have hm : _root_.Min.min R ((K : ℝ≥0∞) * _root_.EDist.edist o z) ≤
        min R ((K : ℝ≥0∞) * _root_.EDist.edist o w) + (K : ℝ≥0∞) * _root_.EDist.edist z w := by
      rcases le_total R ((K : ℝ≥0∞) * _root_.EDist.edist o w) with hw | hw
      · rw [min_eq_left hw]
        exact (min_le_left _ _).trans le_self_add
      · rw [min_eq_right hw]
        calc
          _ ≤ (K : ℝ≥0∞) * _root_.EDist.edist o z := min_le_right _ _
          _ ≤ (K : ℝ≥0∞) * (_root_.EDist.edist o w + _root_.EDist.edist w z) :=
            mul_le_mul_right (_root_.PseudoEMetricSpace.edist_triangle o w z) _
          _ = _ := by rw [mul_add, _root_.PseudoEMetricSpace.edist_comm w z]
    have hf : (K : ℝ≥0∞) * _root_.EDist.edist z w ≠ ⊤ := ENNReal.mul_ne_top ENNReal.coe_ne_top hzw
    have ht := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfin w, hf⟩) hm
    rwa [ENNReal.toReal_add (hfin w) hf, ENNReal.toReal_mul, ENNReal.coe_toReal] at ht
  have hreal : _root_.Dist.dist (ENNReal.truncateToReal R ((K : ℝ≥0∞) * _root_.EDist.edist o x))
      (ENNReal.truncateToReal R ((K : ℝ≥0∞) * _root_.EDist.edist o y)) ≤ (K : ℝ) * (_root_.EDist.edist x y).toReal := by
    rw [Real.dist_eq, abs_sub_le_iff]
    have h₁ := hstep x y hxy
    have h₂ := hstep y x (by rwa [_root_.PseudoEMetricSpace.edist_comm])
    rw [_root_.PseudoEMetricSpace.edist_comm y x] at h₂
    constructor <;> linarith
  rw [edist_dist]
  have hr := ENNReal.ofReal_le_ofReal hreal
  rwa [ENNReal.ofReal_mul K.coe_nonneg, ENNReal.ofReal_coe_nnreal,
    ENNReal.ofReal_toReal hxy] at hr

run_cmd do
  let env ← Lean.getEnv
  if env.contains `lipschitzWith_truncateToReal_edist then
    throwError "Refusing to shadow existing declaration lipschitzWith_truncateToReal_edist"
  Lean.modifyEnv fun env => Lean.addAlias env `lipschitzWith_truncateToReal_edist ``Submission.lipschitzWith_truncateToReal_edist
