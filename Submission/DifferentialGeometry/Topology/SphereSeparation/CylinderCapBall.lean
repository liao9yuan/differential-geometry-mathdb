import Submission.DifferentialGeometry.Topology.SphereSeparation.FlatCapBallReconstruction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Submission.Set _root_.Metric _root_.Submission.Metric _root_.Manifold _root_.Submission.Manifold
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold

namespace DifferentialGeometry.Topology.SphereSeparation

attribute [local instance] Handle.closedCellChartedSpaceSucc Handle.closedCellIsManifold

theorem exists_diffeomorph_ball_of_cylinderCap_replacements
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
    {a : Fin 2 → ℝ} {σ : ℝ} (ha : ∀ i, 0 < a i) (haε : ∀ i, a i < ε)
    (hσ : σ = 1 ∨ σ = -1)
    {f : Fin 2 → SphereTwo → EuclideanThree}
    (hf : ∀ i, _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (f i))
    (hcap : ∀ i, ∀ x ∈ _root_.Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,
      f i (χ i x) = Ψ (EuclideanGeometry.cylinderCap ((if i = 0 then σ else -σ) * a i) x))
    (hffix : ∀ i, _root_.Set.EqOn (f i) e (_root_.Set.range (b i))ᶜ)
    (hret : ∀ i, ∀ p ∈ _root_.Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R ×ˢ _root_.Set.Ioo (-ε) ε,
      Ψ p ∈ e '' (_root_.Set.range (b i))ᶜ ↔ ‖p.1‖ = 1 ∧ 0 < (if i = 0 then σ else -σ) * p.2)
    (D : Fin 2 → EuclideanThree ≃ₘ[ℝ] EuclideanThree)
    (hD : ∀ i, D i '' _root_.Metric.closedBall 0 1 = closure
      (jordanBrouwer_openThreeSpace (f i) (hf i)
        (Diffeomorph.refl (𝓡 3) EuclideanThree ∞)).toSphereSides.compactSide) :
    let d := (jordanBrouwer_openThreeSpace e he
      (Diffeomorph.refl (𝓡 3) EuclideanThree ∞)).toSphereSides
    ∃ H : EuclideanThree ≃ₘ[ℝ] EuclideanThree,
      H '' _root_.Metric.closedBall 0 1 = closure d.compactSide ∧ H '' _root_.Metric.sphere 0 1 = _root_.Set.range e := by
  have hε : 0 < ε := (ha 0).trans (haε 0)
  have hinter' : e '' (_root_.Set.range (b 0) ∩ _root_.Set.range (b 1)) ⊆
      Ψ '' (_root_.Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ×ˢ {0}) := by
    rw [hinter, hboundary]
    exact _root_.Set.image_mono (_root_.Set.prod_mono _root_.Metric.sphere_subset_closedBall (Subset.refl _))
  obtain ⟨g, hg, hgin, hgun⟩ := he.isEmbedding.exists_two_flat_cap_replacements
    Ψ.toHomeomorph.isEmbedding (fun i => (χ i).toOpenPartialHomeomorph) hR hε
    hcover hinter' hχ hχD (fun i => (hf i).contMDiff.continuous) hcap hffix hret
  exact exists_diffeomorph_ball_of_flat_cap_reconstruction he hb hbboundary hcover hinter Ψ hR hS
    hboundary χ hχ hχD ha haε hσ hf hcap hffix hret (fun i => (hg i).2.1)
    (fun i => (hg i).2.2.1) (fun i => (hg i).2.2.2.1) hgin hgun D hD

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.exists_diffeomorph_ball_of_cylinderCap_replacements then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.exists_diffeomorph_ball_of_cylinderCap_replacements"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.exists_diffeomorph_ball_of_cylinderCap_replacements ``Submission.DifferentialGeometry.Topology.SphereSeparation.exists_diffeomorph_ball_of_cylinderCap_replacements

theorem exists_diffeomorph_ball_of_cylinderCap_images
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
    {a : Fin 2 → ℝ} {σ : ℝ} (ha : ∀ i, 0 < a i) (haε : ∀ i, a i < ε)
    (hσ : σ = 1 ∨ σ = -1)
    {f : Fin 2 → SphereTwo → EuclideanThree}
    (hf : ∀ i, _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (f i))
    (hcap : ∀ i, ∀ x ∈ _root_.Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,
      f i (χ i x) = Ψ (EuclideanGeometry.cylinderCap ((if i = 0 then σ else -σ) * a i) x))
    (hffix : ∀ i, _root_.Set.EqOn (f i) e (_root_.Set.range (b i))ᶜ)
    (hret : ∀ i, ∀ p ∈ _root_.Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R ×ˢ _root_.Set.Ioo (-ε) ε,
      Ψ p ∈ e '' (_root_.Set.range (b i))ᶜ ↔ ‖p.1‖ = 1 ∧ 0 < (if i = 0 then σ else -σ) * p.2)
    (T D : Fin 2 → EuclideanThree ≃ₘ[ℝ] EuclideanThree)
    (hD : ∀ i, D i '' _root_.Metric.sphere 0 1 = _root_.Set.range (T i ∘ f i)) :
    let d := (jordanBrouwer_openThreeSpace e he
      (Diffeomorph.refl (𝓡 3) EuclideanThree ∞)).toSphereSides
    ∃ H : EuclideanThree ≃ₘ[ℝ] EuclideanThree,
      H '' _root_.Metric.closedBall 0 1 = closure d.compactSide ∧ H '' _root_.Metric.sphere 0 1 = _root_.Set.range e := by
  let A : Fin 2 → EuclideanThree ≃ₘ[ℝ] EuclideanThree := fun i => (D i).trans (T i).symm
  have hAsphere (i : Fin 2) : A i '' _root_.Metric.sphere 0 1 = _root_.Set.range (f i) := by
    change ((T i).symm ∘ D i) '' _ = _
    rw [_root_.Set.image_comp, hD i, _root_.Set.range_comp]
    exact (T i).symm_image_image _
  have hAball (i : Fin 2) : A i '' _root_.Metric.closedBall 0 1 = closure
      (jordanBrouwer_openThreeSpace (f i) (hf i)
        (Diffeomorph.refl (𝓡 3) EuclideanThree ∞)).toSphereSides.compactSide := by
    let d := (jordanBrouwer_openThreeSpace (f i) (hf i)
      (Diffeomorph.refl (𝓡 3) EuclideanThree ∞)).toSphereSides
    let d' := standardUnitSphereSides.image (A i).toHomeomorph
    have hunion : d'.compactSide ∪ d'.endSide = (_root_.Set.range (f i))ᶜ := by
      rw [d'.union_eq_compl]
      change (A i '' _root_.Metric.sphere 0 1)ᶜ = _
      rw [hAsphere i]
    have hside := (d.side_sets_unique_of_core_properties d'.compactSide d'.endSide
      d'.isOpen_compactSide d'.isOpen_endSide d'.isConnected_compactSide d'.isConnected_endSide
      d'.disjoint hunion d'.isCompact_closure_compactSide d'.not_isCompact_closure_endSide).1
    change A i '' _root_.Metric.ball 0 1 = d.compactSide at hside
    have hclosure : A i '' closure (_root_.Metric.ball 0 1) = closure (A i '' _root_.Metric.ball 0 1) :=
      (A i).toHomeomorph.image_closure _
    rw [closure_ball _ one_ne_zero, hside] at hclosure
    exact hclosure
  exact exists_diffeomorph_ball_of_cylinderCap_replacements he hb hbboundary hcover hinter Ψ hR hS hboundary
    χ hχ hχD ha haε hσ hf hcap hffix hret A hAball

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.exists_diffeomorph_ball_of_cylinderCap_images then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.exists_diffeomorph_ball_of_cylinderCap_images"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.exists_diffeomorph_ball_of_cylinderCap_images ``Submission.DifferentialGeometry.Topology.SphereSeparation.exists_diffeomorph_ball_of_cylinderCap_images

end DifferentialGeometry.Topology.SphereSeparation
