import Mathlib.Topology.PartitionOfUnity
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.MeasureTheory.Integral.DominatedConvergence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

set_option autoImplicit false
noncomputable section

open _root_.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.Topology _root_.ENNReal

namespace PartitionOfUnity
open _root_.PartitionOfUnity

variable {ι M : Type*} [TopologicalSpace M]

open _root_.PartitionOfUnity in
theorem tsum_mul_eq_of_eq_on_support (ρ : PartitionOfUnity ι M _root_.Set.univ)
    (x : M) (d : ι → ℝ) (a : ℝ) (hd : ∀ i, ρ i x ≠ 0 → d i = a) :
    (∑' i, ρ i x * d i) = a := by
  have hfin : (Function.support fun i => ρ i x * d i).Finite :=
    (ρ.locallyFinite.point_finite x).subset (Function.support_mul_subset_left _ _)
  rw [tsum_eq_finsum hfin]
  calc
    (∑ᶠ i, ρ i x * d i) = ∑ᶠ i, ρ i x * a := by
      apply finsum_congr
      intro i
      by_cases hi : ρ i x = 0
      · simp only [hi, _root_.MulZeroClass.zero_mul]
      · rw [hd i hi]
    _ = (∑ᶠ i, ρ i x) * a := (finsum_mul _ _).symm
    _ = a := by rw [ρ.sum_eq_one (_root_.Set.mem_univ x), one_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartitionOfUnity.tsum_mul_eq_of_eq_on_support then
    throwError "Refusing to shadow existing declaration PartitionOfUnity.tsum_mul_eq_of_eq_on_support"
  Lean.modifyEnv fun env => Lean.addAlias env `PartitionOfUnity.tsum_mul_eq_of_eq_on_support ``Submission.PartitionOfUnity.tsum_mul_eq_of_eq_on_support

open _root_.PartitionOfUnity in
theorem tsum_mul_ae_eq_of_compatible
    {α : Type*} [MeasurableSpace α] {μ : _root_.MeasureTheory.Measure α} [Countable ι]
    (ρ : PartitionOfUnity ι M _root_.Set.univ) (v : α → M) (d : ι → α → ℝ)
    (hd : ∀ i j, ∀ᵐ x ∂μ, ρ i (v x) ≠ 0 → ρ j (v x) ≠ 0 → d i x = d j x) :
    ∀ᵐ x ∂μ, ∀ i, ρ i (v x) ≠ 0 → (∑' j, ρ j (v x) * d j x) = d i x := by
  have hall : ∀ᵐ x ∂μ, ∀ i j, ρ i (v x) ≠ 0 → ρ j (v x) ≠ 0 → d i x = d j x :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr (hd i)
  filter_upwards [hall] with x hx i hi
  exact ρ.tsum_mul_eq_of_eq_on_support (v x) (fun j => d j x) (d i x)
    (fun j hj => hx j i hj hi)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartitionOfUnity.tsum_mul_ae_eq_of_compatible then
    throwError "Refusing to shadow existing declaration PartitionOfUnity.tsum_mul_ae_eq_of_compatible"
  Lean.modifyEnv fun env => Lean.addAlias env `PartitionOfUnity.tsum_mul_ae_eq_of_compatible ``Submission.PartitionOfUnity.tsum_mul_ae_eq_of_compatible

open _root_.PartitionOfUnity in
theorem tsum_mul_ae_eq_of_cross_compatible
    {α κ : Type*} [MeasurableSpace α] {μ : _root_.MeasureTheory.Measure α} [Countable ι] [Countable κ]
    (ρ : PartitionOfUnity ι M _root_.Set.univ) (σ : PartitionOfUnity κ M _root_.Set.univ)
    (v : α → M) (d : ι → α → ℝ) (e : κ → α → ℝ)
    (hde : ∀ i j, ∀ᵐ x ∂μ, ρ i (v x) ≠ 0 → σ j (v x) ≠ 0 → d i x = e j x) :
    (fun x => ∑' i, ρ i (v x) * d i x) =ᵐ[μ] (fun x => ∑' j, σ j (v x) * e j x) := by
  have hall : ∀ᵐ x ∂μ, ∀ i j, ρ i (v x) ≠ 0 → σ j (v x) ≠ 0 → d i x = e j x :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr (hde i)
  filter_upwards [hall] with x hx
  obtain ⟨i, hi⟩ := ρ.exists_pos (_root_.Set.mem_univ (v x))
  obtain ⟨j, hj⟩ := σ.exists_pos (_root_.Set.mem_univ (v x))
  have hleft := ρ.tsum_mul_eq_of_eq_on_support (v x) (fun k => d k x) (e j x)
    (fun k hk => hx k j hk hj.ne')
  have hright := σ.tsum_mul_eq_of_eq_on_support (v x) (fun k => e k x) (d i x)
    (fun k hk => (hx i k hi.ne' hk).symm)
  exact hleft.trans ((hx i j hi.ne' hj.ne').symm.trans hright.symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartitionOfUnity.tsum_mul_ae_eq_of_cross_compatible then
    throwError "Refusing to shadow existing declaration PartitionOfUnity.tsum_mul_ae_eq_of_cross_compatible"
  Lean.modifyEnv fun env => Lean.addAlias env `PartitionOfUnity.tsum_mul_ae_eq_of_cross_compatible ``Submission.PartitionOfUnity.tsum_mul_ae_eq_of_cross_compatible

end PartitionOfUnity

namespace MeasureTheory
open _root_.MeasureTheory

open _root_.MeasureTheory in
theorem integrable_tsum_of_summable_integral_norm
    {α ι : Type*} [MeasurableSpace α] [Countable ι] {μ : _root_.MeasureTheory.Measure α}
    (f : ι → α → ℝ) (hf : ∀ i, _root_.MeasureTheory.Integrable (f i) μ)
    (hs : Summable (fun i => ∫ x, ‖f i x‖ ∂μ)) :
    Integrable (fun x => ∑' i, f i x) μ := by
  let F : ι → _root_.MeasureTheory.Lp ℝ 1 μ := fun i => (hf i).toL1 (f i)
  have hnorm (i : ι) : ‖F i‖ = ∫ x, ‖f i x‖ ∂μ := by
    rw [show F i = (hf i).toL1 (f i) from rfl,
      Integrable.norm_toL1_eq_lintegral_enorm,
      _root_.MeasureTheory.integral_norm_eq_lintegral_enorm (hf i).aestronglyMeasurable]
  have hsum : ∑' i, ‖F i‖ₑ ≠ ⊤ :=
    tsum_enorm_ne_top_iff_summable_norm.mpr (by simpa only [hnorm] using hs)
  have heq : (fun x => (∑' i, F i) x) =ᵐ[μ] (fun x => ∑' i, f i x) := by
    filter_upwards [Lp.coeFn_tsum hsum, _root_.MeasureTheory.ae_all_iff.mpr (fun i => (hf i).coeFn_toL1)] with x hx hi
    rw [hx]
    exact tsum_congr fun i => hi i
  exact (_root_.MeasureTheory.memLp_one_iff_integrable.mp (Lp.memLp (∑' i, F i))).congr heq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.integrable_tsum_of_summable_integral_norm then
    throwError "Refusing to shadow existing declaration MeasureTheory.integrable_tsum_of_summable_integral_norm"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.integrable_tsum_of_summable_integral_norm ``Submission.MeasureTheory.integrable_tsum_of_summable_integral_norm

end MeasureTheory

end

end
