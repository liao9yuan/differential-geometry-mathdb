import Submission.DifferentialGeometry.Topology.Manifold.ImmersionCriterion
import Submission.DifferentialGeometry.Topology.Manifold.ImmersionDifferential
import Submission.DifferentialGeometry.Topology.Manifold.AddCircle.Descent
import Mathlib.Geometry.Manifold.SmoothEmbedding

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace AddCircle
open _root_.AddCircle

open _root_.AddCircle in
theorem isSmoothEmbedding_periodic_lift
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {γ : ℝ → E} (hγ : ContDiff ℝ ∞ γ) (hp : Function.Periodic γ 1)
    (hinj : _root_.Set.InjOn γ (_root_.Set.Ico (0 : ℝ) 1))
    (hne : ∀ t ∈ _root_.Set.Icc (0 : ℝ) 1, deriv γ t ≠ 0) :
    Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ hp.lift := by
  have hs : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ hp.lift :=
    isLocalDiffeomorph_coe.contMDiff_of_comp_of_surjective
      QuotientAddGroup.mk_surjective hγ.contMDiff
  have hi : Function.Injective hp.lift := by
    intro a b hab
    apply (_root_.AddCircle.equivIco 1 0).injective
    apply Subtype.ext
    apply hinj
    · simpa using (_root_.AddCircle.equivIco 1 0 a).property
    · simpa using (_root_.AddCircle.equivIco 1 0 b).property
    · change hp.lift ((_root_.AddCircle.equivIco 1 0 a : ℝ) : AddCircle (1 : ℝ)) =
        hp.lift ((_root_.AddCircle.equivIco 1 0 b : ℝ) : AddCircle (1 : ℝ))
      simpa only [_root_.AddCircle.coe_equivIco] using hab
  have himm : Manifold.IsImmersion 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ hp.lift := by
    apply DifferentialGeometry.Topology.Manifold.isImmersion_of_injective_mfderiv (by simp) hs
    intro z
    have hv : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) hp.lift z (parameterTangent z) ≠ 0 := by
      let t : ℝ := _root_.AddCircle.equivIco 1 0 z
      have ht : t ∈ _root_.Set.Icc (0 : ℝ) 1 := by
        have hi := (_root_.AddCircle.equivIco 1 0 z).property
        exact ⟨hi.1, by simpa using hi.2.le⟩
      have hzt : (t : AddCircle (1 : ℝ)) = z := _root_.AddCircle.coe_equivIco
      rw [← hzt, ← deriv_comp_coe (hs.mdifferentiable (by simp) (t : AddCircle (1 : ℝ)))]
      exact hne t ht
    intro a b hab
    obtain ⟨α, rfl⟩ := exists_smul_parameterTangent z a
    obtain ⟨β, rfl⟩ := exists_smul_parameterTangent z b
    rw [map_smul, map_smul] at hab
    rw [(smul_left_injective ℝ hv) hab]
  exact ⟨himm, (hs.continuous.isClosedEmbedding hi).isEmbedding⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.isSmoothEmbedding_periodic_lift then
    throwError "Refusing to shadow existing declaration AddCircle.isSmoothEmbedding_periodic_lift"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.isSmoothEmbedding_periodic_lift ``Submission.AddCircle.isSmoothEmbedding_periodic_lift

open _root_.AddCircle in
theorem deriv_comp_coe_ne_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : AddCircle (1 : ℝ) → E}
    (hf : Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ f) (t : ℝ) :
    deriv (fun x : ℝ => f (x : AddCircle (1 : ℝ))) t ≠ 0 := by
  rw [deriv_comp_coe (hf.contMDiff.mdifferentiable (by simp) (t : AddCircle (1 : ℝ)))]
  intro heq
  apply parameterTangent_ne_zero (t : AddCircle (1 : ℝ))
  exact (hf.isImmersion.isImmersionAt (t : AddCircle (1 : ℝ))).injective_mfderiv
    (by simp) (heq.trans (map_zero _).symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.deriv_comp_coe_ne_zero then
    throwError "Refusing to shadow existing declaration AddCircle.deriv_comp_coe_ne_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.deriv_comp_coe_ne_zero ``Submission.AddCircle.deriv_comp_coe_ne_zero

end AddCircle
