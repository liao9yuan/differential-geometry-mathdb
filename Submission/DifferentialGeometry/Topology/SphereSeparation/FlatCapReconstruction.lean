import Submission.DifferentialGeometry.Topology.SphereSeparation.FlatCapRegions
import Submission.DifferentialGeometry.Topology.SphereSeparation.FlatCapTransport

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Submission.Set _root_.Metric _root_.Manifold _root_.Submission.Manifold
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold

namespace DifferentialGeometry.Topology.SphereSeparation

attribute [local instance] Handle.closedCellChartedSpaceSucc Handle.closedCellIsManifold

theorem exists_flat_cap_reconstruction_regions
    {e : SphereTwo → EuclideanThree} (he : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    {b : Fin 2 → ClosedCell 2 → SphereTwo}
    (hb : ∀ i, _root_.Manifold.IsSmoothEmbedding (𝓡∂ 2) (𝓡 2) ∞ (b i))
    {η : AddCircle (1 : ℝ) → SphereTwo}
    (hbboundary : ∀ i, _root_.Set.range (b i ∘ cellBoundaryInclusion 2) = _root_.Set.range η)
    (hcover : _root_.Set.range (b 0) ∪ _root_.Set.range (b 1) = _root_.Set.univ)
    (hinter : _root_.Set.range (b 0) ∩ _root_.Set.range (b 1) = _root_.Set.range η)
    (Ψ : (EuclideanSpace ℝ (Fin 2) × ℝ) ≃ₘ[ℝ] EuclideanThree)
    {R ε : ℝ} (hR : 1 < R)
    (hS : Ψ ⁻¹' _root_.Set.range e ∩ (_root_.Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) R ×ˢ _root_.Set.Icc (-ε) ε) =
      _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ×ˢ _root_.Set.Icc (-ε) ε)
    (hboundary : e '' _root_.Set.range η = Ψ '' (_root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ×ˢ {0}))
    (χ : Fin 2 → PartialDiffeomorph (𝓡 2) (𝓡 2) (EuclideanSpace ℝ (Fin 2)) SphereTwo ∞)
    (hχ : ∀ i, _root_.Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ⊆ (χ i).source)
    (hχD : ∀ i, χ i '' _root_.Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 = _root_.Set.range (b i))
    {a : Fin 2 → ℝ} (ha : ∀ i, a i ≠ 0) (haε : ∀ i, |a i| < ε)
    {f g : Fin 2 → SphereTwo → EuclideanThree}
    (hf : ∀ i, _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (f i))
    (hcap : ∀ i, ∀ x ∈ _root_.Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,
      f i (χ i x) = Ψ (EuclideanGeometry.cylinderCap (a i) x))
    (hffix : ∀ i, _root_.Set.EqOn (f i) e (_root_.Set.range (b i))ᶜ)
    (hside : ∀ i, ∀ p ∈ _root_.Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R ×ˢ _root_.Set.Ioo (-ε) ε,
      Ψ p ∈ e '' (_root_.Set.range (b i))ᶜ → ‖p.1‖ = 1 ∧ 0 ≤ a i * p.2)
    (hflat : ∀ i, ∀ x ∈ _root_.Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, g i (χ i x) = Ψ (x, 0))
    (hgfix : ∀ i, _root_.Set.EqOn (g i) e (_root_.Set.range (b i))ᶜ)
    (hrange : ∀ i, _root_.Set.range (g i) = Ψ '' (_root_.Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ×ˢ {0}) ∪
      e '' (_root_.Set.range (b i))ᶜ)
    (hgin : _root_.Set.range (g 0) ∩ _root_.Set.range (g 1) =
      Ψ '' (_root_.Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ×ˢ {0}))
    (hgun : _root_.Set.range (g 0) ∪ _root_.Set.range (g 1) = _root_.Set.range e ∪
      Ψ '' (_root_.Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ×ˢ {0})) :
    let d := (jordanBrouwer_openThreeSpace e he
      (Diffeomorph.refl (𝓡 3) EuclideanThree ∞)).toSphereSides
    let d_f := fun i => (jordanBrouwer_openThreeSpace (f i) (hf i)
      (Diffeomorph.refl (𝓡 3) EuclideanThree ∞)).toSphereSides
    ∃ (Φ : Fin 2 → EuclideanThree ≃ₜ EuclideanThree)
      (C : Fin 2 → Set EuclideanThree) (d' : ∀ i, SphereSides (_root_.Set.range (g i))),
      (∀ i, Φ i ∘ f i = g i ∧ _root_.Set.EqOn (Φ i) id (e '' (_root_.Set.range (b i))ᶜ) ∧
        _root_.Topology.IsEmbedding (g i) ∧ IsCompact (C i) ∧
        C i ⊆ Ψ '' (_root_.Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R ×ˢ _root_.Set.Ioo (-ε) ε) ∧
        _root_.Set.EqOn (Φ i) id (C i)ᶜ ∧ _root_.Set.EqOn (Φ i).symm id (C i)ᶜ ∧
        (d' i).compactSide = Φ i '' (d_f i).compactSide ∧
        (d' i).endSide = Φ i '' (d_f i).endSide) ∧
      ((Disjoint (d' 0).compactSide (d' 1).compactSide ∧
        closure d.compactSide = closure (d' 0).compactSide ∪ closure (d' 1).compactSide ∧
        closure (d' 0).compactSide ∩ closure (d' 1).compactSide =
          Ψ '' (_root_.Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ×ˢ {0})) ∨
      ((d' 0).compactSide ⊂ (d' 1).compactSide ∧
        d.compactSide = (d' 1).compactSide \ closure (d' 0).compactSide ∧
        closure d.compactSide =
          closure (interior (closure (d' 1).compactSide) \ closure (d' 0).compactSide) ∧
        closure (d' 1).compactSide = closure d.compactSide ∪ closure (d' 0).compactSide ∧
        closure d.compactSide ∩ closure (d' 0).compactSide = _root_.Set.range e ∩ _root_.Set.range (g 0)) ∨
      ((d' 1).compactSide ⊂ (d' 0).compactSide ∧
        d.compactSide = (d' 0).compactSide \ closure (d' 1).compactSide ∧
        closure d.compactSide =
          closure (interior (closure (d' 0).compactSide) \ closure (d' 1).compactSide) ∧
        closure (d' 0).compactSide = closure d.compactSide ∪ closure (d' 1).compactSide ∧
        closure d.compactSide ∩ closure (d' 1).compactSide = _root_.Set.range e ∩ _root_.Set.range (g 1))) := by
  classical
  dsimp only
  have htransport (i : Fin 2) := exists_sphere_sides_flat_cap (hf i) Ψ.toHomeomorph
    (ha i) (haε i) hR (χ i) (hχD i) (hcap i) (hflat i) (hffix i) (hgfix i) (hside i)
  choose Φ hΦ hretained hg C hC hCU hΦfix hΦifix d' hcompact hend using htransport
  refine ⟨Φ, C, d', fun i => ⟨hΦ i, hretained i, hg i, hC i, hCU i, hΦfix i,
    hΦifix i, hcompact i, hend i⟩, ?_⟩
  exact SphereSides.flat_cap_reconstruction_regions he.isEmbedding hb hbboundary hcover
    hinter Ψ (le_of_lt hR) (le_trans (abs_nonneg (a 0)) (le_of_lt (haε 0))) hS hboundary
    χ hχ hχD hg hflat hgfix hrange hgin hgun
    (jordanBrouwer_openThreeSpace e he (Diffeomorph.refl (𝓡 3) EuclideanThree ∞)).toSphereSides d'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.exists_flat_cap_reconstruction_regions then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.exists_flat_cap_reconstruction_regions"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.exists_flat_cap_reconstruction_regions ``Submission.DifferentialGeometry.Topology.SphereSeparation.exists_flat_cap_reconstruction_regions

end DifferentialGeometry.Topology.SphereSeparation
