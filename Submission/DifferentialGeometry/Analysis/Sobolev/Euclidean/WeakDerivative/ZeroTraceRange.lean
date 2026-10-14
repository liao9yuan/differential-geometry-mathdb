import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.ZeroTraceExtension
import Submission.DifferentialGeometry.External.DeGiorgi.SobolevSpace.Approximation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

noncomputable section

open _root_.Set _root_.Filter _root_.MeasureTheory
open scoped _root_.Topology _root_.ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ} [NeZero d] {ι : Type*}

local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "F" => EuclideanSpace ℝ ι

theorem exists_weak_extension_mem_set_of_memW01p_sub
    {Ω U : Set E} (hΩ : IsOpen Ω) (hU : IsOpen U) (hUΩ : U ⊆ Ω)
    {z q : E → F}
    (hz : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => z x i) Ω)
    (hq : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => q x i) U)
    (hqz : ∀ i, DeGiorgi.MemW01p 2 (fun x => q x i - z x i) U)
    {K : Set F} (hzK : ∀ᵐ x ∂volume.restrict Ω, z x ∈ K)
    (hqK : ∀ᵐ x ∂volume.restrict U, q x ∈ K) :
    ∃ f : E → F,
      ∃ hf : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => f x i) Ω,
        _root_.Set.EqOn f q U ∧ _root_.Set.EqOn f z Uᶜ ∧
        (∀ᵐ x ∂volume.restrict Ω, f x ∈ K) ∧
        ∀ i, (hf i).weakGrad =ᵐ[volume.restrict U] (hq i).weakGrad := by
  obtain ⟨f, ⟨hf⟩, hfq, hfz⟩ := exists_weak_extension_of_memW01p_sub hΩ hU hz hqz
  have hfK : ∀ᵐ x ∂volume.restrict Ω, f x ∈ K := by
    filter_upwards [hzK, _root_.MeasureTheory.ae_restrict_of_ae ((_root_.MeasureTheory.ae_restrict_iff' hU.measurableSet).mp hqK)]
      with x hxz hxq
    by_cases hxU : x ∈ U
    · rw [hfq hxU]
      exact hxq hxU
    · rw [hfz hxU]
      exact hxz
  refine ⟨f, hf, hfq, hfz, hfK, ?_⟩
  intro i
  have heq : (fun x => f x i) =ᵐ[volume.restrict U] (fun x => q x i) := by
    filter_upwards [_root_.MeasureTheory.ae_restrict_mem hU.measurableSet] with x hx
    exact congrArg (fun y : F => y i) (hfq hx)
  exact (((hf i).restrict hU hUΩ).congr heq).ae_eq hU (hq i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_weak_extension_mem_set_of_memW01p_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_weak_extension_mem_set_of_memW01p_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_weak_extension_mem_set_of_memW01p_sub ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_weak_extension_mem_set_of_memW01p_sub

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end

end
