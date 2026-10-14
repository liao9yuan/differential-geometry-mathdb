import Submission.DifferentialGeometry.Topology.Manifold.AddCircle.ParameterDerivative
import Submission.DifferentialGeometry.Topology.Manifold.AddCircle.Descent

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Filter _root_.Bundle
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace AddCircle
open _root_.AddCircle

open _root_.AddCircle in
theorem contMDiff_periodic_lift_family {β : ℝ × ℝ → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hper : ∀ t, Function.Periodic (fun x => β (t, x)) 1) :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × AddCircle (1 : ℝ) => (hper p.1).lift p.2) := by
  rw [← contMDiffOn_univ, ← Set.univ_prod_univ]
  apply contMDiffOn_of_comp_coe
  change ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ β (_root_.Set.univ ×ˢ _root_.Set.univ)
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
  exact hβ.contMDiff.contMDiffOn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.contMDiff_periodic_lift_family then
    throwError "Refusing to shadow existing declaration AddCircle.contMDiff_periodic_lift_family"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.contMDiff_periodic_lift_family ``Submission.AddCircle.contMDiff_periodic_lift_family

open _root_.AddCircle in
theorem contMDiff_parameterTangent_smul {β : ℝ × AddCircle (1 : ℝ) → ℝ}
    (hβ : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ β) :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ).tangent ∞
      (fun p : ℝ × AddCircle (1 : ℝ) =>
        (⟨p.2, β p • parameterTangent p.2⟩ : TangentBundle 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))) := by
  have hV : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ).tangent ∞
      (fun p : ℝ × AddCircle (1 : ℝ) =>
        (⟨p.2, parameterTangent p.2⟩ : TangentBundle 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))) :=
    contMDiff_parameterTangent.comp contMDiff_snd
  intro p₀
  have hVat := hV p₀
  rw [Bundle.contMDiffAt_totalSpace] at hVat ⊢
  refine ⟨hVat.1, ?_⟩
  let e := _root_.FiberBundle.trivializationAt ℝ (TangentSpace 𝓘(ℝ, ℝ) : AddCircle (1 : ℝ) → Type) p₀.2
  have hfib := (hβ p₀).smul hVat.2
  have hmem : e.baseSet ∈ 𝓝 p₀.2 :=
    e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' p₀.2)
  refine hfib.congr_of_eventuallyEq ?_
  filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds hmem] with p hp
  exact (e.linear ℝ hp).2 (β p) (parameterTangent p.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.contMDiff_parameterTangent_smul then
    throwError "Refusing to shadow existing declaration AddCircle.contMDiff_parameterTangent_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.contMDiff_parameterTangent_smul ``Submission.AddCircle.contMDiff_parameterTangent_smul

end AddCircle
