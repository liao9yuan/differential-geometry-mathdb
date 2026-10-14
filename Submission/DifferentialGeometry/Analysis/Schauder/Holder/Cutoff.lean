import Submission.DifferentialGeometry.Analysis.Schauder.Holder.CompactRegularity
import Submission.DifferentialGeometry.Analysis.Schauder.Holder.Bilinear

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set
open scoped _root_.NNReal _root_.ENNReal

namespace DifferentialGeometry.Analysis.Schauder

variable {V F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_holderWith_smul_cutoff_of_holderOnWith
    {s : Set V} (hs : IsCompact s) {u : V → F} {η : V → ℝ}
    {α K : ℝ≥0} (hα : 0 < α) (hα1 : α ≤ 1) (hu : HolderOnWith K α u s)
    (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η) (hηs : tsupport η ⊆ s) :
    ∃ B C : ℝ≥0, (∀ x, ‖η x • u x‖ ≤ B) ∧ HolderWith C α (fun x => η x • u x) := by
  obtain ⟨Mu, hMu⟩ := exists_norm_bound_of_continuousOn_isCompact hs (hu.continuousOn hα)
  obtain ⟨Mη, Kη, hMη, hHη⟩ :=
    exists_norm_bound_and_holderWith_of_contDiff_hasCompactSupport hη hηc hα1
  have hzero (x : V) (hx : x ∉ s) : η x = 0 :=
    image_eq_zero_of_notMem_tsupport fun ht => hx (hηs ht)
  have hH : HolderWith (Mu * Kη + Mη * K) α (fun x => η x • u x) := by
    exact holderWith_bilinear_of_restrict_of_support
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F).flip
      (fun a b => by simp only [ContinuousLinearMap.flip_apply,
        ContinuousLinearMap.lsmul_apply, norm_smul]; rw [mul_comm])
      hu.holderWith hHη hMu hMη hzero
  refine ⟨Mη * Mu, Mu * Kη + Mη * K, ?_, hH⟩
  intro x
  by_cases hx : x ∈ s
  · rw [norm_smul, NNReal.coe_mul]
    exact mul_le_mul (hMη x) (hMu x hx) (norm_nonneg _) Mη.coe_nonneg
  · simp only [hzero x hx, zero_smul, norm_zero]
    positivity

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.exists_holderWith_smul_cutoff_of_holderOnWith then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.exists_holderWith_smul_cutoff_of_holderOnWith"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.exists_holderWith_smul_cutoff_of_holderOnWith ``Submission.DifferentialGeometry.Analysis.Schauder.exists_holderWith_smul_cutoff_of_holderOnWith

end DifferentialGeometry.Analysis.Schauder

end
