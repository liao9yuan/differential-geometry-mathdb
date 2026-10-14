import Submission.DifferentialGeometry.Topology.Homeomorph.CylinderCap

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Submission.Set _root_.Metric

namespace Homeomorph
open _root_.Homeomorph

open _root_.Homeomorph in
theorem exists_cylinderCap_replacement_flattening
    {X Y E : Type*} [TopologicalSpace Y] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [ProperSpace E] {e f g : X → Y} (Ψ : (E × ℝ) ≃ₜ Y)
    {a b R : ℝ} (ha : a ≠ 0) (hab : |a| < b) (hR : 1 < R)
    {D : Set X} (χ : E → X) (hχD : χ '' _root_.Metric.closedBall (0 : E) 1 = D)
    (hcap : ∀ x ∈ _root_.Metric.closedBall (0 : E) 1, f (χ x) = Ψ (EuclideanGeometry.cylinderCap a x))
    (hflat : ∀ x ∈ _root_.Metric.closedBall (0 : E) 1, g (χ x) = Ψ (x, 0))
    (hfix : _root_.Set.EqOn f e Dᶜ) (hgfix : _root_.Set.EqOn g e Dᶜ)
    (hside : ∀ p ∈ _root_.Metric.ball (0 : E) R ×ˢ _root_.Set.Ioo (-b) b,
      Ψ p ∈ e '' Dᶜ → ‖p.1‖ = 1 ∧ 0 ≤ a * p.2) :
    ∃ Φ : Y ≃ₜ Y, Φ ∘ f = g ∧ _root_.Set.EqOn Φ id (e '' Dᶜ) ∧
      ∃ C : Set Y, IsCompact C ∧ C ⊆ Ψ '' (_root_.Metric.ball (0 : E) R ×ˢ _root_.Set.Ioo (-b) b) ∧
        EqOn Φ id Cᶜ ∧ _root_.Set.EqOn Φ.symm id Cᶜ := by
  classical
  obtain ⟨H, hHcap, hHwall, C, hC, hCU, hHfix, hHifix⟩ :=
    exists_cylinderCap_flattening (E := E) ha hab hR
  let Φ := Ψ.symm.trans (H.trans Ψ)
  have hretained : _root_.Set.EqOn Φ id (e '' Dᶜ) := by
    rintro z ⟨x, hx, rfl⟩
    let p := Ψ.symm (e x)
    have hHp : H p = p := by
      by_cases hp : p ∈ C
      · have hs := hside p (hCU hp) ⟨x, hx, (Ψ.apply_symm_apply (e x)).symm⟩
        exact hHwall p hs.1 hs.2
      · exact hHfix hp
    change Ψ (H p) = e x
    rw [hHp]
    exact Ψ.apply_symm_apply (e x)
  refine ⟨Φ, ?_, hretained, Ψ '' C, hC.image Ψ.continuous, _root_.Set.image_mono hCU, ?_, ?_⟩
  · funext x
    by_cases hx : x ∈ D
    · obtain ⟨y, hy, rfl⟩ := hχD.symm.subset hx
      change Ψ (H (Ψ.symm (f (χ y)))) = g (χ y)
      rw [hcap y hy, Ψ.symm_apply_apply, hHcap y hy, hflat y hy]
    · change Φ (f x) = g x
      rw [hfix hx, hgfix hx]
      exact hretained (_root_.Set.mem_image_of_mem e hx)
  · intro y hy
    have hp : Ψ.symm y ∉ C := fun hp => hy ⟨Ψ.symm y, hp, Ψ.apply_symm_apply y⟩
    change Ψ (H (Ψ.symm y)) = y
    rw [hHfix hp, id_eq, Ψ.apply_symm_apply]
  · intro y hy
    have hp : Ψ.symm y ∉ C := fun hp => hy ⟨Ψ.symm y, hp, Ψ.apply_symm_apply y⟩
    change Ψ (H.symm (Ψ.symm y)) = y
    rw [hHifix hp, id_eq, Ψ.apply_symm_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Homeomorph.exists_cylinderCap_replacement_flattening then
    throwError "Refusing to shadow existing declaration Homeomorph.exists_cylinderCap_replacement_flattening"
  Lean.modifyEnv fun env => Lean.addAlias env `Homeomorph.exists_cylinderCap_replacement_flattening ``Submission.Homeomorph.exists_cylinderCap_replacement_flattening

end Homeomorph
