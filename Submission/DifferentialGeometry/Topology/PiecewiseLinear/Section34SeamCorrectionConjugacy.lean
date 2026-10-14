import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34SeamCorrectionFacePreservation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem image_eq_of_injective_conjugacy
    {A B : Type*} {S T : Set A} {φ : A → B} {ψ : A → A} {H : B → B}
    (hTS : T ⊆ S) (hφ : _root_.Set.InjOn φ S) (hψ : _root_.Set.MapsTo ψ S S)
    (hconj : ∀ x ∈ S, H (φ x) = φ (ψ x))
    (hH : H '' (φ '' T) = φ '' T) : ψ '' T = T := by
  apply (hφ.image_eq_image_iff (fun _ hx => by
    obtain ⟨x, hx, rfl⟩ := hx
    exact hψ (hTS hx)) hTS).mp
  rw [← _root_.Set.image_comp, ← EqOn.image_eq (show _root_.Set.EqOn (H ∘ φ) (φ ∘ ψ) T from
    fun x hx => hconj x (hTS hx)), _root_.Set.image_comp, hH]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.image_eq_of_injective_conjugacy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.image_eq_of_injective_conjugacy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.image_eq_of_injective_conjugacy ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.image_eq_of_injective_conjugacy

theorem IsPLHomeomorphOn.image_circle_region_of_preserved_bottom_annulus
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : (ℝ × ℝ) × ℝ → E} {R : Set E} {σ : ((Fin 3 → ℝ) × ℝ) × ℝ → E}
    (hσ : IsPLHomeomorphOn σ
      ((stdSimplexBoundary 2 ×ˢ _root_.Set.Icc (0 : ℝ) 1) ×ˢ _root_.Set.Icc (0 : ℝ) 1) R)
    (hσf : ∀ u ∈ _root_.Set.Icc (0 : ℝ) 1, ∀ v ∈ _root_.Set.Icc (0 : ℝ) 1, ∀ t ∈ _root_.Set.Icc (0 : ℝ) 1,
      σ ((stdTriangleLoop t, u), v) = f ((u, v), t))
    {H : E → E} {ψ : (Fin 3 → ℝ) × ℝ → (Fin 3 → ℝ) × ℝ}
    (hψ : IsPLHomeomorphOn ψ (stdSimplexBoundary 2 ×ˢ _root_.Set.Icc (0 : ℝ) 1)
      (stdSimplexBoundary 2 ×ˢ _root_.Set.Icc (0 : ℝ) 1))
    (hconj : ∀ z ∈ stdSimplexBoundary 2 ×ˢ _root_.Set.Icc (0 : ℝ) 1, ∀ v ∈ _root_.Set.Icc (0 : ℝ) 1,
      H (σ (z, v)) = σ (ψ z, v))
    {K : Set ℝ} (hK : K ⊆ _root_.Set.Icc (0 : ℝ) 1)
    (hH : H '' (f '' ((K ×ˢ {(0 : ℝ)}) ×ˢ _root_.Set.Icc (0 : ℝ) 1)) =
      f '' ((K ×ˢ {(0 : ℝ)}) ×ˢ _root_.Set.Icc (0 : ℝ) 1)) :
    ψ '' (stdSimplexBoundary 2 ×ˢ K) = stdSimplexBoundary 2 ×ˢ K := by
  let κ : (Fin 3 → ℝ) × ℝ → E := fun z => σ (z, 0)
  have hκ : _root_.Set.InjOn κ (stdSimplexBoundary 2 ×ˢ _root_.Set.Icc (0 : ℝ) 1) := by
    intro x hx y hy hxy
    exact congrArg Prod.fst (hσ.bijOn.injOn ⟨hx, by norm_num⟩ ⟨hy, by norm_num⟩ hxy)
  have heq : κ '' (stdSimplexBoundary 2 ×ˢ K) =
      f '' ((K ×ˢ {(0 : ℝ)}) ×ˢ _root_.Set.Icc (0 : ℝ) 1) := by
    apply Subset.antisymm
    · rintro y ⟨⟨z, u⟩, ⟨hz, hu⟩, rfl⟩
      obtain ⟨t, ht, rfl⟩ := stdTriangleLoop_image.symm.subset hz
      exact ⟨((u, 0), t), ⟨⟨hu, rfl⟩, ht⟩,
        (hσf u (hK hu) 0 (by norm_num) t ht).symm⟩
    · rintro y ⟨⟨⟨u, v⟩, t⟩, ⟨⟨hu, hv⟩, ht⟩, rfl⟩
      change v = 0 at hv
      subst v
      exact ⟨(stdTriangleLoop t, u),
        ⟨stdTriangleLoop_image.subset (_root_.Set.mem_image_of_mem stdTriangleLoop ht), hu⟩,
        hσf u (hK hu) 0 (by norm_num) t ht⟩
  apply image_eq_of_injective_conjugacy (_root_.Set.prod_mono_right hK) hκ hψ.bijOn.mapsTo
    (fun x hx => hconj x hx 0 (by norm_num))
  rwa [heq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.image_circle_region_of_preserved_bottom_annulus then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.image_circle_region_of_preserved_bottom_annulus"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.image_circle_region_of_preserved_bottom_annulus ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.image_circle_region_of_preserved_bottom_annulus

end DifferentialGeometry.Topology.PiecewiseLinear
