import Submission.DifferentialGeometry.Topology.Manifold.RegularLevel.Collar.ManifoldField

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Bundle
open scoped _root_.Manifold _root_.ContDiff _root_.Topology
open _root_.Submission.DifferentialGeometry.Topology.Morse

namespace DifferentialGeometry.Manifold.RegularLevel

variable {m : ℕ} {H M : Type*} [TopologicalSpace H] [TopologicalSpace M]
  [ChartedSpace H M] (I : ModelWithCorners ℝ (MorseModel (m + 1)) H)
  [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

theorem exists_descendingField_on_compact {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {K : Set M} (hK : IsCompact K)
    (hr : ∀ x ∈ K, mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0) :
    ∃ V : (x : M) → TangentSpace I x,
      ContMDiff I I.tangent ∞ (fun x ↦ (⟨x, V x⟩ : TangentBundle I M)) ∧
      IsCompact (tsupport V) ∧
      (∀ x ∈ K, mvfderiv I f x (V x) = (-1 : ℝ)) ∧
      ∀ x, (-1 : ℝ) ≤ mvfderiv I f x (V x) ∧
        mvfderiv I f x (V x) ≤ (0 : ℝ) := by
  classical
  obtain ⟨O, hO, hKO, W, hW, hsuppW, hdfW⟩ :=
    exists_unitSpeed_near_compact_regularSet_manifold I hf hK hr
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (I := I)
    hK.isClosed (fun _ : Unit ↦ O) (fun _ ↦ hO) (by
      intro x hx
      exact mem_iUnion.mpr ⟨(), hKO hx⟩)
  have hρone (x : M) (hx : x ∈ K) : ρ () x = 1 := by
    simpa only [finsum_eq_sum_of_fintype, Fintype.sum_unique] using ρ.sum_eq_one hx
  have hρzero (x : M) (hx : x ∉ O) : ρ () x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hy ↦ hx (hρ () hy))
  let V : (x : M) → TangentSpace I x := fun x ↦ ρ () x • W x
  have hV : ContMDiff I I.tangent ∞
      (fun x ↦ (⟨x, V x⟩ : TangentBundle I M)) :=
    (ρ ()).contMDiff.smul_section hW
  have hsupp : Function.support V ⊆ Function.support W := by
    intro x hx hzero
    apply hx
    change ρ () x • (W x : MorseModel (m + 1)) = 0
    rw [show (W x : MorseModel (m + 1)) = 0 from hzero, smul_zero]
  refine ⟨V, hV, hsuppW.of_isClosed_subset (isClosed_tsupport V) (closure_mono hsupp), ?_, ?_⟩
  · intro x hx
    change mvfderiv I f x (ρ () x • W x) = (-1 : ℝ)
    rw [hρone x hx, one_smul]
    exact hdfW x (hKO hx)
  · intro x
    change (-1 : ℝ) ≤ mvfderiv I f x (ρ () x • W x) ∧
      mvfderiv I f x (ρ () x • W x) ≤ (0 : ℝ)
    by_cases hx : x ∈ O
    · have hd : mvfderiv I f x (W x) = -1 := hdfW x hx
      rw [map_smul, hd]
      change -1 ≤ ρ () x * -1 ∧ ρ () x * -1 ≤ 0
      constructor <;> linarith [ρ.nonneg () x, ρ.le_one () x]
    · rw [hρzero x hx, zero_smul, map_zero]
      norm_num

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.RegularLevel.exists_descendingField_on_compact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.RegularLevel.exists_descendingField_on_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.RegularLevel.exists_descendingField_on_compact ``Submission.DifferentialGeometry.Manifold.RegularLevel.exists_descendingField_on_compact

end DifferentialGeometry.Manifold.RegularLevel
