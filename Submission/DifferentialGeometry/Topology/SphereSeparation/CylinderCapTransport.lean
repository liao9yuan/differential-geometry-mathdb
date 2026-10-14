import Submission.DifferentialGeometry.Topology.SphereSeparation.CylinderCap
import Submission.DifferentialGeometry.Topology.Diffeomorph.CylinderCapTranslation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Submission.Set _root_.Metric _root_.Submission.Metric _root_.Manifold _root_.Submission.Manifold
open scoped _root_.ContDiff _root_.Submission.ContDiff _root_.Manifold _root_.Submission.Manifold

namespace DifferentialGeometry.Topology.SphereSeparation

theorem exists_isotopy_displacing_cylinderCap
    {e f : SphereTwo → EuclideanThree} (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    (Ψ : (Schoenflies.Plane × ℝ) ≃ₘ[ℝ] EuclideanThree) {R ε a d σ c : ℝ}
    (hR : 1 < R) (ha : 0 ≤ a) (had : a < d) (hdε : d < ε)
    (hσ : σ = 1 ∨ σ = -1) (hheight : ∀ p, Ψ p 2 = c + p.2)
    (hS : Ψ ⁻¹' _root_.Set.range e ∩ (_root_.Metric.closedBall (0 : Schoenflies.Plane) R ×ˢ _root_.Set.Icc (-ε) ε) =
      _root_.Metric.sphere (0 : Schoenflies.Plane) 1 ×ˢ _root_.Set.Icc (-ε) ε)
    {D : Set SphereTwo} (χ : Schoenflies.Plane → SphereTwo)
    (hχD : χ '' _root_.Metric.closedBall (0 : Schoenflies.Plane) 1 = D)
    (hcap : ∀ x ∈ _root_.Metric.closedBall (0 : Schoenflies.Plane) 1,
      f (χ x) = Ψ (EuclideanGeometry.cylinderCap (σ * a) x))
    (hfix : _root_.Set.EqOn f e Dᶜ)
    (hside : ∀ p ∈ _root_.Metric.ball (0 : Schoenflies.Plane) R ×ˢ _root_.Set.Ioo (-ε) ε,
      Ψ p ∈ e '' Dᶜ → 0 < σ * p.2) :
    ∃ H : ℝ → (EuclideanThree ≃ₘ[ℝ] EuclideanThree),
      ContDiff ℝ ∞ (fun z : ℝ × EuclideanThree => H z.1 z.2) ∧
      ContDiff ℝ ∞ (fun z : ℝ × EuclideanThree => (H z.1).symm z.2) ∧
      H 0 = Diffeomorph.refl (𝓡 3) EuclideanThree ∞ ∧
      (∀ t, H t '' _root_.Set.range e = _root_.Set.range e) ∧
      (∀ t, _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (H t ∘ f)) ∧
      _root_.Set.range (H 1 ∘ f) ∩ {z | z 2 = c} = e '' Dᶜ ∩ {z | z 2 = c} ∧
      (∀ x ∈ _root_.Metric.closedBall (0 : Schoenflies.Plane) 1, 0 < σ * (H 1 (f (χ x)) 2 - c)) ∧
      ∃ U : Set (Schoenflies.Plane × ℝ), IsOpen U ∧
        EuclideanGeometry.cylinderCap (σ * a) '' _root_.Metric.closedBall (0 : Schoenflies.Plane) 1 ⊆ U ∧
        (∀ t ∈ _root_.Set.Icc (0 : ℝ) 1, ∀ p ∈ U, H t (Ψ p) = Ψ (p.1, p.2 + t * (σ * d))) ∧
      ∃ J : Set EuclideanThree, IsCompact J ∧
        J ⊆ Ψ '' (_root_.Metric.ball (0 : Schoenflies.Plane) R ×ˢ _root_.Set.Ioo (-ε) ε) ∧
        ∀ t : ℝ, _root_.Set.EqOn (H t) id Jᶜ ∧ _root_.Set.EqOn (H t).symm id Jᶜ := by
  have hSopen : Ψ ⁻¹' _root_.Set.range e ∩ (_root_.Metric.ball (0 : Schoenflies.Plane) R ×ˢ _root_.Set.Ioo (-ε) ε) =
      sphere (0 : Schoenflies.Plane) 1 ×ˢ _root_.Set.Ioo (-ε) ε := by
    ext p
    constructor
    · rintro ⟨hpS, hp⟩
      have hh := hS.subset ⟨hpS, _root_.Metric.ball_subset_closedBall hp.1, _root_.Set.Ioo_subset_Icc_self hp.2⟩
      exact ⟨hh.1, hp.2⟩
    · rintro ⟨hp, ht⟩
      exact ⟨(hS.symm.subset ⟨hp, _root_.Set.Ioo_subset_Icc_self ht⟩).1,
        _root_.Metric.sphere_subset_ball hR hp, ht⟩
  have hrange : _root_.Set.range f = e '' Dᶜ ∪
      Ψ '' (EuclideanGeometry.cylinderCap (σ * a) '' _root_.Metric.closedBall (0 : Schoenflies.Plane) 1) := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      by_cases hx : x ∈ D
      · obtain ⟨y, hy, rfl⟩ := hχD.symm.subset hx
        exact Or.inr ⟨EuclideanGeometry.cylinderCap (σ * a) y, ⟨y, hy, rfl⟩, (hcap y hy).symm⟩
      · exact Or.inl ⟨x, hx, (hfix hx).symm⟩
    · rintro (⟨x, hx, rfl⟩ | ⟨p, ⟨x, hx, rfl⟩, rfl⟩)
      · exact ⟨x, hfix hx⟩
      · exact ⟨χ x, hcap x hx⟩
  obtain ⟨H, hH, hHi, hH0, hHS, hpositive, hlevel, U, hU, hcapU, hmove,
    J, hJ, hJU, hsupport⟩ := Diffeomorph.exists_isotopy_cylinderCap_translation_in_chart
      Ψ hR ha had hdε hσ (fun z : EuclideanThree => z 2) hheight hSopen
  refine ⟨H, hH, hHi, hH0, hHS, fun t => hf.diffeomorph_comp (H t), ?_,
    fun x hx => ?_, U, hU, hcapU, hmove, J, hJ, hJU, hsupport⟩
  · rw [_root_.Set.range_comp, hrange]
    exact hlevel (e '' Dᶜ) (_root_.Set.image_subset_range _ _) hside
  · rw [hcap x hx]
    exact hpositive x hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.exists_isotopy_displacing_cylinderCap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.exists_isotopy_displacing_cylinderCap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.exists_isotopy_displacing_cylinderCap ``Submission.DifferentialGeometry.Topology.SphereSeparation.exists_isotopy_displacing_cylinderCap

end DifferentialGeometry.Topology.SphereSeparation
