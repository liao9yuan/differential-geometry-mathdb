import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.SplitIfs

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

open _root_.Function _root_.Set
open scoped _root_.Manifold _root_.ContDiff _root_.Topology _root_.BigOperators

noncomputable section

namespace SmoothPartitionOfUnity
open _root_.SmoothPartitionOfUnity

universe uI uE uH uM

variable {ι : Type uI} [Finite ι] {E : Type uE} [NormedAddCommGroup E]
  [NormedSpace ℝ E] {H : Type uH} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type uM} [TopologicalSpace M]
  [ChartedSpace H M] {s : Set M}

open _root_.SmoothPartitionOfUnity in
def concentrate (f : SmoothPartitionOfUnity ι I M s) (i₀ : ι)
    (β : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯) (hβ : ∀ x, β x ∈ _root_.Set.Icc (0 : ℝ) 1) :
    SmoothPartitionOfUnity ι I M s := by
  classical
  letI := Fintype.ofFinite ι
  refine {
    toFun := fun i => ⟨fun x => (1 - β x) * f i x + if i = i₀ then β x else 0, ?_⟩
    locallyFinite' := locallyFinite_of_finite _
    nonneg' := ?_
    sum_eq_one' := ?_
    sum_le_one' := ?_ }
  · apply ContMDiff.add
    · exact (contMDiff_const.sub β.contMDiff).mul (f i).contMDiff
    · split_ifs
      · exact β.contMDiff
      · exact contMDiff_const
  · intro i x
    apply add_nonneg (mul_nonneg (sub_nonneg.mpr (hβ x).2) (f.nonneg i x))
    split_ifs
    · exact (hβ x).1
    · exact le_rfl
  · intro x hx
    rw [finsum_eq_sum_of_fintype]
    change ∑ i, ((1 - β x) * f i x + if i = i₀ then β x else 0) = 1
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_ite_eq', Finset.mem_univ, if_true,
      show ∑ i, f i x = 1 by simpa only [finsum_eq_sum_of_fintype] using f.sum_eq_one hx,
      mul_one, sub_add_cancel]
  · intro x
    rw [finsum_eq_sum_of_fintype]
    change ∑ i, ((1 - β x) * f i x + if i = i₀ then β x else 0) ≤ 1
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have hf : ∑ i, f i x ≤ 1 := by simpa only [finsum_eq_sum_of_fintype] using f.sum_le_one x
    nlinarith [mul_le_mul_of_nonneg_left hf (sub_nonneg.mpr (hβ x).2)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SmoothPartitionOfUnity.concentrate then
    throwError "Refusing to shadow existing declaration SmoothPartitionOfUnity.concentrate"
  Lean.modifyEnv fun env => Lean.addAlias env `SmoothPartitionOfUnity.concentrate ``Submission.SmoothPartitionOfUnity.concentrate

open _root_.SmoothPartitionOfUnity in
theorem concentrate_apply (f : SmoothPartitionOfUnity ι I M s) (i₀ : ι)
    (β : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯) (hβ : ∀ x, β x ∈ _root_.Set.Icc (0 : ℝ) 1) (i : ι) (x : M) :
    letI := Classical.decEq ι
    f.concentrate i₀ β hβ i x = (1 - β x) * f i x + if i = i₀ then β x else 0 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SmoothPartitionOfUnity.concentrate_apply then
    throwError "Refusing to shadow existing declaration SmoothPartitionOfUnity.concentrate_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `SmoothPartitionOfUnity.concentrate_apply ``Submission.SmoothPartitionOfUnity.concentrate_apply

open _root_.SmoothPartitionOfUnity in
theorem concentrate_apply_of_eq_one (f : SmoothPartitionOfUnity ι I M s) (i₀ : ι)
    (β : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯) (hβ : ∀ x, β x ∈ _root_.Set.Icc (0 : ℝ) 1)
    {x : M} (hx : β x = 1) (i : ι) :
    letI := Classical.decEq ι
    f.concentrate i₀ β hβ i x = if i = i₀ then 1 else 0 := by
  classical
  simp only [concentrate_apply, hx, sub_self, _root_.MulZeroClass.zero_mul, zero_add]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SmoothPartitionOfUnity.concentrate_apply_of_eq_one then
    throwError "Refusing to shadow existing declaration SmoothPartitionOfUnity.concentrate_apply_of_eq_one"
  Lean.modifyEnv fun env => Lean.addAlias env `SmoothPartitionOfUnity.concentrate_apply_of_eq_one ``Submission.SmoothPartitionOfUnity.concentrate_apply_of_eq_one

open _root_.SmoothPartitionOfUnity in
theorem isSubordinate_concentrate (f : SmoothPartitionOfUnity ι I M s) (i₀ : ι)
    (β : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯) (hβ : ∀ x, β x ∈ _root_.Set.Icc (0 : ℝ) 1)
    {U : ι → Set M} (hf : f.IsSubordinate U) (hs : tsupport β ⊆ U i₀) :
    (f.concentrate i₀ β hβ).IsSubordinate U := by
  classical
  intro i
  change tsupport (fun x => (1 - β x) * f i x + if i = i₀ then β x else 0) ⊆ U i
  apply Set.Subset.trans (tsupport_add _ _)
  apply Set.union_subset
  · exact (tsupport_mul_subset_right).trans (hf i)
  · by_cases hi : i = i₀
    · simpa only [hi, if_true] using hs
    · simp only [hi, ↓reduceIte]
      change tsupport (0 : M → ℝ) ⊆ U i
      rw [tsupport_zero]
      exact _root_.Set.empty_subset _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SmoothPartitionOfUnity.isSubordinate_concentrate then
    throwError "Refusing to shadow existing declaration SmoothPartitionOfUnity.isSubordinate_concentrate"
  Lean.modifyEnv fun env => Lean.addAlias env `SmoothPartitionOfUnity.isSubordinate_concentrate ``Submission.SmoothPartitionOfUnity.isSubordinate_concentrate

end SmoothPartitionOfUnity

end

end

section

set_option autoImplicit false

open _root_.Set _root_.Filter _root_.Topology
open scoped _root_.ContDiff _root_.Manifold

namespace SmoothPartitionOfUnity
open _root_.SmoothPartitionOfUnity

variable {ι E H M : Type*} [Finite ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

open _root_.SmoothPartitionOfUnity in
theorem exists_isSubordinate_eq_single_near
    {K : Set M} (hK : IsClosed K) (U : ι → Set M) (hU : ∀ i, IsOpen (U i))
    (hcover : K ⊆ ⋃ i, U i) (i₀ : ι) {x₀ : M} (hx₀ : x₀ ∈ U i₀) :
    letI := Classical.decEq ι
    ∃ ρ : SmoothPartitionOfUnity ι I M K, ρ.IsSubordinate U ∧
      ∃ W : Set M, IsOpen W ∧ x₀ ∈ W ∧
        ∀ x ∈ W, ∀ i, ρ i x = if i = i₀ then 1 else 0 := by
  classical
  obtain ⟨ρ, hρ⟩ := _root_.SmoothPartitionOfUnity.exists_isSubordinate I hK U hU hcover
  obtain ⟨f, _, hf⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I) x₀).mem_iff.mp
    ((hU i₀).mem_nhds hx₀)
  let β : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯ := ⟨f, f.contMDiff⟩
  have hβ : ∀ x, β x ∈ _root_.Set.Icc (0 : ℝ) 1 := fun _ => f.mem_Icc
  have hβsupp : tsupport β ⊆ U i₀ := hf
  have hβone : ∀ᶠ x in 𝓝 x₀, β x = 1 := f.eventuallyEq_one
  obtain ⟨W, hWsub, hWopen, hxW⟩ := mem_nhds_iff.mp hβone
  refine ⟨ρ.concentrate i₀ β hβ, ρ.isSubordinate_concentrate i₀ β hβ hρ hβsupp,
    W, hWopen, hxW, ?_⟩
  intro x hx i
  exact ρ.concentrate_apply_of_eq_one i₀ β hβ (hWsub hx) i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SmoothPartitionOfUnity.exists_isSubordinate_eq_single_near then
    throwError "Refusing to shadow existing declaration SmoothPartitionOfUnity.exists_isSubordinate_eq_single_near"
  Lean.modifyEnv fun env => Lean.addAlias env `SmoothPartitionOfUnity.exists_isSubordinate_eq_single_near ``Submission.SmoothPartitionOfUnity.exists_isSubordinate_eq_single_near

end SmoothPartitionOfUnity

end
