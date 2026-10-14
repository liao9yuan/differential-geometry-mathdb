import Submission.DifferentialGeometry.Topology.Order.LiminfSum
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Topology.PartitionOfUnity
import Submission.DifferentialGeometry.Topology.PartitionOfUnity.FiniteSum

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

set_option autoImplicit false
noncomputable section

open _root_.MeasureTheory _root_.Filter _root_.Submission.Filter
open scoped _root_.Topology

namespace MeasureTheory
open _root_.MeasureTheory

open _root_.MeasureTheory in
theorem sum_le_liminf_integral_of_subordinate_weighted_liminf
    {α ι : Type*} [MeasurableSpace α] {μ : _root_.MeasureTheory.Measure α}
    (s : Finset ι) (f : ℕ → α → ℝ) (w : ι → ℕ → α → ℝ)
    (hf : ∀ n, _root_.MeasureTheory.Integrable (f n) μ) (hf0 : ∀ n, ∀ᵐ x ∂μ, 0 ≤ f n x)
    (hw : ∀ i ∈ s, ∀ n, _root_.MeasureTheory.AEStronglyMeasurable (w i n) μ)
    (hw0 : ∀ i ∈ s, ∀ n, ∀ᵐ x ∂μ, 0 ≤ w i n x)
    (hwsum : ∀ n, ∀ᵐ x ∂μ, ∑ i ∈ s, w i n x ≤ 1)
    {C : ℝ} (hbound : ∀ n, (∫ x, f n x ∂μ) ≤ C)
    (a : ι → ℝ)
    (ha : ∀ i ∈ s, a i ≤ _root_.Filter.liminf (fun n => ∫ x, w i n x * f n x ∂μ) _root_.Filter.atTop) :
    (∑ i ∈ s, a i) ≤ _root_.Filter.liminf (fun n => ∫ x, f n x ∂μ) atTop := by
  classical
  have hw1 (i : ι) (hi : i ∈ s) (n : ℕ) : ∀ᵐ x ∂μ, w i n x ≤ 1 := by
    have hpos : ∀ᵐ x ∂μ, ∀ j ∈ s, 0 ≤ w j n x := by
      exact (s.eventually_all).mpr fun j hj => hw0 j hj n
    filter_upwards [hpos, hwsum n] with x hx hsx
    exact (Finset.single_le_sum (fun j hj => hx j hj) hi).trans hsx
  have hint (i : ι) (hi : i ∈ s) (n : ℕ) : _root_.MeasureTheory.Integrable (fun x => w i n x * f n x) μ := by
    apply (hf n).bdd_mul (c := (1 : ℝ)) (hw i hi n)
    filter_upwards [hw0 i hi n, hw1 i hi n] with x hx hx1
    rwa [Real.norm_eq_abs, abs_of_nonneg hx]
  let q : ι → ℕ → ℝ := fun i n => ∫ x, w i n x * f n x ∂μ
  have hq0 (i : ι) (hi : i ∈ s) (n : ℕ) : 0 ≤ q i n :=
    _root_.MeasureTheory.integral_nonneg_of_ae ((hw0 i hi n).and (hf0 n) |>.mono
      fun _ h => mul_nonneg h.1 h.2)
  have hqE (i : ι) (hi : i ∈ s) (n : ℕ) : q i n ≤ ∫ x, f n x ∂μ := by
    apply _root_.MeasureTheory.integral_mono_ae (hint i hi n) (hf n)
    filter_upwards [hw1 i hi n, hf0 n] with x hx hf0x
    exact mul_le_of_le_one_left hf0x hx
  have hlo (i : ι) (hi : i ∈ s) : _root_.Filter.IsBoundedUnder (· ≥ ·) _root_.Filter.atTop (q i) := by
    refine ⟨0, ?_⟩
    change ∀ᶠ n in _root_.Filter.atTop, 0 ≤ q i n
    exact Eventually.of_forall (hq0 i hi)
  have hhi (i : ι) (hi : i ∈ s) : _root_.Filter.IsBoundedUnder (· ≤ ·) _root_.Filter.atTop (q i) := by
    refine ⟨C, ?_⟩
    change ∀ᶠ n in _root_.Filter.atTop, q i n ≤ C
    exact Eventually.of_forall fun n => (hqE i hi n).trans (hbound n)
  have hsumE (n : ℕ) : (∑ i ∈ s, q i n) ≤ ∫ x, f n x ∂μ := by
    rw [show (∑ i ∈ s, q i n) = ∫ x, (∑ i ∈ s, w i n x) * f n x ∂μ by
      simp only [Finset.sum_mul]
      exact (_root_.MeasureTheory.integral_finsetSum s (fun i hi => hint i hi n)).symm]
    have hsumint : _root_.MeasureTheory.Integrable (fun x => (∑ i ∈ s, w i n x) * f n x) μ := by
      simpa only [Finset.sum_mul] using _root_.MeasureTheory.integrable_finsetSum s (fun i hi => hint i hi n)
    apply _root_.MeasureTheory.integral_mono_ae hsumint (hf n)
    filter_upwards [hwsum n, hf0 n] with x hx hfx
    exact mul_le_of_le_one_left hfx hx
  have hsum := sum_liminf_le s q hlo hhi
  have hsumlo : _root_.Filter.IsBoundedUnder (· ≥ ·) _root_.Filter.atTop (fun n => ∑ i ∈ s, q i n) := by
    refine ⟨0, ?_⟩
    change ∀ᶠ n in _root_.Filter.atTop, 0 ≤ ∑ i ∈ s, q i n
    exact Eventually.of_forall fun n => Finset.sum_nonneg (fun i hi => hq0 i hi n)
  have hEhi : _root_.Filter.IsCoboundedUnder (· ≥ ·) _root_.Filter.atTop (fun n => ∫ x, f n x ∂μ) :=
    _root_.Filter.isCoboundedUnder_ge_of_eventually_le _root_.Filter.atTop (Eventually.of_forall hbound)
  have hsumle := _root_.Filter.liminf_le_liminf (Eventually.of_forall hsumE) hsumlo hEhi
  have heq : (∑ i ∈ s, q i) = (fun n => ∑ i ∈ s, q i n) := by
    funext n
    exact Finset.sum_apply n s q
  rw [heq] at hsum
  exact (Finset.sum_le_sum ha).trans (hsum.trans hsumle)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.sum_le_liminf_integral_of_subordinate_weighted_liminf then
    throwError "Refusing to shadow existing declaration MeasureTheory.sum_le_liminf_integral_of_subordinate_weighted_liminf"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.sum_le_liminf_integral_of_subordinate_weighted_liminf ``Submission.MeasureTheory.sum_le_liminf_integral_of_subordinate_weighted_liminf

end MeasureTheory

end

end

section

set_option autoImplicit false
noncomputable section

open _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Filter _root_.Submission.Filter _root_.Set
open scoped _root_.Topology

namespace PartitionOfUnity
open _root_.PartitionOfUnity

variable {ι M : Type*} [TopologicalSpace M]

open _root_.PartitionOfUnity in
theorem sum_le_liminf_integral_of_weighted_liminf
    {α : Type*} [MeasurableSpace α] {μ : _root_.MeasureTheory.Measure α}
    [MeasurableSpace M] [BorelSpace M]
    {s₀ : Set M} (ρ : PartitionOfUnity ι M s₀) (s : Finset ι)
    (U : ℕ → α → M) (hU : ∀ n, AEMeasurable (U n) μ)
    (f : ℕ → α → ℝ) (hf : ∀ n, _root_.MeasureTheory.Integrable (f n) μ)
    (hf0 : ∀ n, ∀ᵐ x ∂μ, 0 ≤ f n x)
    {C : ℝ} (hbound : ∀ n, (∫ x, f n x ∂μ) ≤ C)
    (a : ι → ℝ)
    (ha : ∀ i ∈ s, a i ≤ _root_.Filter.liminf (fun n => ∫ x, ρ i (U n x) * f n x ∂μ) _root_.Filter.atTop) :
    (∑ i ∈ s, a i) ≤ _root_.Filter.liminf (fun n => ∫ x, f n x ∂μ) atTop := by
  apply MeasureTheory.sum_le_liminf_integral_of_subordinate_weighted_liminf
    s f (fun i n x => ρ i (U n x)) hf hf0
  · intro i _ n
    exact ((ρ i).continuous.measurable.comp_aemeasurable (hU n)).aestronglyMeasurable
  · exact fun i _ n => Eventually.of_forall fun x => ρ.nonneg i (U n x)
  · exact fun n => Eventually.of_forall fun x => ρ.sum_finset_le_one s (U n x)
  · exact hbound
  · exact ha

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartitionOfUnity.sum_le_liminf_integral_of_weighted_liminf then
    throwError "Refusing to shadow existing declaration PartitionOfUnity.sum_le_liminf_integral_of_weighted_liminf"
  Lean.modifyEnv fun env => Lean.addAlias env `PartitionOfUnity.sum_le_liminf_integral_of_weighted_liminf ``Submission.PartitionOfUnity.sum_le_liminf_integral_of_weighted_liminf

end PartitionOfUnity

end

end
