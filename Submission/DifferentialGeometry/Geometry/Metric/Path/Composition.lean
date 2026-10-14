import Mathlib.Geometry.Manifold.Riemannian.PathELength

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.MeasureTheory _root_.Set
open scoped _root_.Manifold _root_.Topology

namespace Manifold
open _root_.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [∀ x : M, ENorm (TangentSpace I x)] [∀ y : N, ENorm (TangentSpace J y)]

open _root_.Manifold in
theorem pathELength_comp_le_of_enorm_mfderiv_le
    (f : M → N) {γ : ℝ → M} {a b : ℝ} (C : NNReal)
    (hγ : ∀ᵐ t ∂volume.restrict (_root_.Set.Ioo a b), MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    (hf : ∀ᵐ t ∂volume.restrict (_root_.Set.Ioo a b), MDifferentiableAt I J f (γ t))
    (hnorm : ∀ᵐ t ∂volume.restrict (_root_.Set.Ioo a b),
      ‖mfderiv I J f (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1)‖ₑ ≤
        (C : ENNReal) * ‖mfderiv 𝓘(ℝ, ℝ) I γ t 1‖ₑ) :
    pathELength J (f ∘ γ) a b ≤ (C : ENNReal) * _root_.Manifold.pathELength I γ a b := by
  rw [_root_.Manifold.pathELength_eq_lintegral_mfderiv_Ioo, _root_.Manifold.pathELength_eq_lintegral_mfderiv_Ioo,
    ← _root_.MeasureTheory.lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  apply _root_.MeasureTheory.lintegral_mono_ae
  filter_upwards [hγ, hf, hnorm] with t hγt hft hnormt
  have hcomp := mfderiv_comp t hft hγt
  change ‖mfderiv 𝓘(ℝ, ℝ) J (f ∘ γ) t 1‖ₑ ≤
    (C : ENNReal) * ‖mfderiv 𝓘(ℝ, ℝ) I γ t 1‖ₑ
  rw [hcomp]
  exact hnormt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.pathELength_comp_le_of_enorm_mfderiv_le then
    throwError "Refusing to shadow existing declaration Manifold.pathELength_comp_le_of_enorm_mfderiv_le"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.pathELength_comp_le_of_enorm_mfderiv_le ``Submission.Manifold.pathELength_comp_le_of_enorm_mfderiv_le

open _root_.Manifold in
theorem pathELength_comp_eq_of_enorm_mfderiv_eq
    (f : M → N) {γ : ℝ → M} {a b : ℝ}
    (hγ : ∀ᵐ t ∂volume.restrict (_root_.Set.Ioo a b), MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    (hf : ∀ᵐ t ∂volume.restrict (_root_.Set.Ioo a b), MDifferentiableAt I J f (γ t))
    (hnorm : ∀ᵐ t ∂volume.restrict (_root_.Set.Ioo a b),
      ‖mfderiv I J f (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1)‖ₑ =
        ‖mfderiv 𝓘(ℝ, ℝ) I γ t 1‖ₑ) :
    pathELength J (f ∘ γ) a b = _root_.Manifold.pathELength I γ a b := by
  rw [_root_.Manifold.pathELength_eq_lintegral_mfderiv_Ioo, _root_.Manifold.pathELength_eq_lintegral_mfderiv_Ioo]
  apply _root_.MeasureTheory.lintegral_congr_ae
  filter_upwards [hγ, hf, hnorm] with t hγt hft hnormt
  have hcomp := mfderiv_comp t hft hγt
  change ‖mfderiv 𝓘(ℝ, ℝ) J (f ∘ γ) t 1‖ₑ =
    ‖mfderiv 𝓘(ℝ, ℝ) I γ t 1‖ₑ
  rw [hcomp]
  exact hnormt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.pathELength_comp_eq_of_enorm_mfderiv_eq then
    throwError "Refusing to shadow existing declaration Manifold.pathELength_comp_eq_of_enorm_mfderiv_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.pathELength_comp_eq_of_enorm_mfderiv_eq ``Submission.Manifold.pathELength_comp_eq_of_enorm_mfderiv_eq

end Manifold
