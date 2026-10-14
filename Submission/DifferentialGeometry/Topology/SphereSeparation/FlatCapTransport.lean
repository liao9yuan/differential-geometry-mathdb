import Submission.DifferentialGeometry.Topology.Embedding.FlatCapTransport
import Submission.DifferentialGeometry.Topology.SphereSeparation.SourceTheorems
import Submission.DifferentialGeometry.Topology.SphereSeparation.Transport

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Submission.Set _root_.Metric _root_.Manifold _root_.Submission.Manifold
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold

namespace DifferentialGeometry.Topology.SphereSeparation

theorem exists_sphere_sides_flat_cap
    {e f g : SphereTwo → EuclideanThree} (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    (Ψ : (EuclideanSpace ℝ (Fin 2) × ℝ) ≃ₜ EuclideanThree)
    {a b R : ℝ} (ha : a ≠ 0) (hab : |a| < b) (hR : 1 < R)
    {D : Set SphereTwo} (χ : EuclideanSpace ℝ (Fin 2) → SphereTwo)
    (hχD : χ '' _root_.Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 = D)
    (hcap : ∀ x ∈ _root_.Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,
      f (χ x) = Ψ (EuclideanGeometry.cylinderCap a x))
    (hflat : ∀ x ∈ _root_.Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, g (χ x) = Ψ (x, 0))
    (hfix : _root_.Set.EqOn f e Dᶜ) (hgfix : _root_.Set.EqOn g e Dᶜ)
    (hside : ∀ p ∈ _root_.Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R ×ˢ _root_.Set.Ioo (-b) b,
      Ψ p ∈ e '' Dᶜ → ‖p.1‖ = 1 ∧ 0 ≤ a * p.2) :
    let d_f := (jordanBrouwer_openThreeSpace f hf
      (Diffeomorph.refl (𝓡 3) EuclideanThree ∞)).toSphereSides
    ∃ Φ : EuclideanThree ≃ₜ EuclideanThree,
      Φ ∘ f = g ∧ _root_.Set.EqOn Φ id (e '' Dᶜ) ∧ _root_.Topology.IsEmbedding g ∧
      ∃ C : Set EuclideanThree, IsCompact C ∧
        C ⊆ Ψ '' (_root_.Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R ×ˢ _root_.Set.Ioo (-b) b) ∧
        _root_.Set.EqOn Φ id Cᶜ ∧ _root_.Set.EqOn Φ.symm id Cᶜ ∧
        ∃ d : SphereSides (_root_.Set.range g),
          d.compactSide = Φ '' d_f.compactSide ∧ d.endSide = Φ '' d_f.endSide := by
  dsimp only
  obtain ⟨Φ, hΦ, hretained, C, hC, hCU, hfixΦ, hfixΦi⟩ :=
    Homeomorph.exists_cylinderCap_replacement_flattening Ψ ha hab hR χ hχD
      hcap hflat hfix hgfix hside
  have hg : _root_.Topology.IsEmbedding g := hΦ ▸ Φ.isEmbedding.comp hf.isEmbedding
  refine ⟨Φ, hΦ, hretained, hg, C, hC, hCU, hfixΦ, hfixΦi, ?_⟩
  have himage : Φ '' _root_.Set.range f = _root_.Set.range g := by rw [← _root_.Set.range_comp, hΦ]
  rw [← himage]
  exact ⟨((jordanBrouwer_openThreeSpace f hf
    (Diffeomorph.refl (𝓡 3) EuclideanThree ∞)).toSphereSides).image Φ, rfl, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.exists_sphere_sides_flat_cap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.exists_sphere_sides_flat_cap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.exists_sphere_sides_flat_cap ``Submission.DifferentialGeometry.Topology.SphereSeparation.exists_sphere_sides_flat_cap

end DifferentialGeometry.Topology.SphereSeparation
