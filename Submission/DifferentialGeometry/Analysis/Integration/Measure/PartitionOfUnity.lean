import Submission.DifferentialGeometry.Topology.PartitionOfUnity.CompactSupport
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Bochner.Set

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.MeasureTheory _root_.Set

namespace PartitionOfUnity
open _root_.PartitionOfUnity

variable {ι X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] {s : Set X}

open _root_.PartitionOfUnity in
theorem lintegral_eq_sum_fintsupportOn (ρ : PartitionOfUnity ι X s)
    (μ : _root_.MeasureTheory.Measure X) {K : Set X} (hK : IsCompact K) {f : X → ENNReal}
    (hf : AEMeasurable f μ) (hfK : Function.support f ⊆ K)
    (hfs : Function.support f ⊆ s) :
    ∫⁻ x, f x ∂μ = ∑ i ∈ ρ.fintsupportOn K hK,
      ∫⁻ x in tsupport (ρ i) ∩ K, ENNReal.ofReal (ρ i x) * f x ∂μ := by
  have hsum (x : X) : f x =
      ∑ i ∈ ρ.fintsupportOn K hK, ENNReal.ofReal (ρ i x) * f x := by
    by_cases hx : f x = 0
    · simp only [hx, _root_.MulZeroClass.mul_zero, Finset.sum_const_zero]
    · rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg
        (fun i _ => ρ.nonneg i x),
        ρ.sum_fintsupportOn hK (hfK hx) (hfs hx), ENNReal.ofReal_one, one_mul]
  calc
    ∫⁻ x, f x ∂μ = ∫⁻ x, ∑ i ∈ ρ.fintsupportOn K hK,
        ENNReal.ofReal (ρ i x) * f x ∂μ := _root_.MeasureTheory.lintegral_congr hsum
    _ = ∑ i ∈ ρ.fintsupportOn K hK, ∫⁻ x, ENNReal.ofReal (ρ i x) * f x ∂μ :=
      _root_.MeasureTheory.lintegral_finsetSum' _ (fun i _ =>
        ((ENNReal.measurable_ofReal.comp (ρ i).continuous.measurable).aemeasurable).mul hf)
    _ = ∑ i ∈ ρ.fintsupportOn K hK,
        ∫⁻ x in tsupport (ρ i) ∩ K, ENNReal.ofReal (ρ i x) * f x ∂μ := by
      apply Finset.sum_congr rfl
      intro i _
      symm
      apply _root_.MeasureTheory.setLIntegral_eq_of_support_subset
      intro x hx
      refine ⟨subset_tsupport _ ?_, hfK (right_ne_zero_of_mul hx)⟩
      intro hzero
      exact (left_ne_zero_of_mul hx) (by rw [hzero, ENNReal.ofReal_zero])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartitionOfUnity.lintegral_eq_sum_fintsupportOn then
    throwError "Refusing to shadow existing declaration PartitionOfUnity.lintegral_eq_sum_fintsupportOn"
  Lean.modifyEnv fun env => Lean.addAlias env `PartitionOfUnity.lintegral_eq_sum_fintsupportOn ``Submission.PartitionOfUnity.lintegral_eq_sum_fintsupportOn

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]

open _root_.PartitionOfUnity in
theorem integrable_iff_fintsupportOn (ρ : PartitionOfUnity ι X s)
    (μ : _root_.MeasureTheory.Measure X) {K : Set X} (hK : IsCompact K) {f : X → A}
    (hfK : Function.support f ⊆ K) (hfs : Function.support f ⊆ s) :
    _root_.MeasureTheory.Integrable f μ ↔ ∀ i ∈ ρ.fintsupportOn K hK,
      IntegrableOn (fun x => ρ i x • f x) (tsupport (ρ i) ∩ K) μ := by
  constructor
  · intro hf i _
    exact (hf.bdd_smul 1 (ρ i).continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (ρ.nonneg i x)]
        exact ρ.le_one i x)).integrableOn
  · intro h
    have hi (i : ι) (hi : i ∈ ρ.fintsupportOn K hK) :
        Integrable (fun x => ρ i x • f x) μ := by
      exact (_root_.MeasureTheory.integrableOn_iff_integrable_of_support_subset
        (_root_.Set.subset_inter ((Function.support_smul_subset_left (ρ i) f).trans (subset_tsupport _))
          ((Function.support_smul_subset_right (ρ i) f).trans hfK))).mp (h i hi)
    have hsum := _root_.MeasureTheory.integrable_finsetSum (ρ.fintsupportOn K hK) hi
    simpa only [ρ.sum_fintsupportOn_smul hK hfK hfs] using hsum

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartitionOfUnity.integrable_iff_fintsupportOn then
    throwError "Refusing to shadow existing declaration PartitionOfUnity.integrable_iff_fintsupportOn"
  Lean.modifyEnv fun env => Lean.addAlias env `PartitionOfUnity.integrable_iff_fintsupportOn ``Submission.PartitionOfUnity.integrable_iff_fintsupportOn

open _root_.PartitionOfUnity in
theorem integral_eq_sum_fintsupportOn (ρ : PartitionOfUnity ι X s)
    (μ : _root_.MeasureTheory.Measure X) {K : Set X} (hK : IsCompact K) {f : X → A}
    (hf : _root_.MeasureTheory.Integrable f μ) (hfK : Function.support f ⊆ K)
    (hfs : Function.support f ⊆ s) :
    ∫ x, f x ∂μ = ∑ i ∈ ρ.fintsupportOn K hK,
      ∫ x in tsupport (ρ i) ∩ K, ρ i x • f x ∂μ := by
  calc
    ∫ x, f x ∂μ = ∫ x, ∑ i ∈ ρ.fintsupportOn K hK, ρ i x • f x ∂μ := by
      simp only [ρ.sum_fintsupportOn_smul hK hfK hfs]
    _ = ∑ i ∈ ρ.fintsupportOn K hK, ∫ x, ρ i x • f x ∂μ := by
      apply _root_.MeasureTheory.integral_finsetSum
      intro i _
      exact hf.bdd_smul 1 (ρ i).continuous.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => by
          rw [Real.norm_of_nonneg (ρ.nonneg i x)]
          exact ρ.le_one i x)
    _ = ∑ i ∈ ρ.fintsupportOn K hK,
        ∫ x in tsupport (ρ i) ∩ K, ρ i x • f x ∂μ := by
      apply Finset.sum_congr rfl
      intro i _
      symm
      apply _root_.MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      exact Function.support_subset_iff'.mp
        (_root_.Set.subset_inter ((Function.support_smul_subset_left (ρ i) f).trans (subset_tsupport _))
          ((Function.support_smul_subset_right (ρ i) f).trans hfK))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartitionOfUnity.integral_eq_sum_fintsupportOn then
    throwError "Refusing to shadow existing declaration PartitionOfUnity.integral_eq_sum_fintsupportOn"
  Lean.modifyEnv fun env => Lean.addAlias env `PartitionOfUnity.integral_eq_sum_fintsupportOn ``Submission.PartitionOfUnity.integral_eq_sum_fintsupportOn

end PartitionOfUnity
