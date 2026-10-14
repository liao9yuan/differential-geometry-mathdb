import Submission.DifferentialGeometry.Topology.SphereSeparation.FlatCapAbsorption
import Submission.DifferentialGeometry.Topology.SphereSeparation.FlatCapReconstruction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Submission.Set _root_.Metric _root_.Submission.Metric _root_.Manifold _root_.Submission.Manifold
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold

namespace DifferentialGeometry.Topology.SphereSeparation

theorem exists_diffeomorph_ball_of_flat_caps (m : ℕ)
    (hm : 0 < m) {X : Type*}
    {e : X → EuclideanSpace ℝ (Fin ((m + 1) + 1))}
    {f g : Fin 2 → X → EuclideanSpace ℝ (Fin ((m + 1) + 1))}
    (d : SphereSides (_root_.Set.range e)) (df : ∀ i, SphereSides (_root_.Set.range (f i)))
    (dg : ∀ i, SphereSides (_root_.Set.range (g i)))
    (Ψ : (EuclideanSpace ℝ (Fin (m + 1)) × ℝ) ≃ₘ[ℝ]
      EuclideanSpace ℝ (Fin ((m + 1) + 1)))
    (χ : Fin 2 → EuclideanSpace ℝ (Fin (m + 1)) → X)
    (D : Fin 2 → EuclideanSpace ℝ (Fin ((m + 1) + 1)) ≃ₘ[ℝ]
      EuclideanSpace ℝ (Fin ((m + 1) + 1)))
    {S : Fin 2 → Set X} {R b σ : ℝ} {a : Fin 2 → ℝ}
    (hR : 1 < R) (ha : ∀ i, 0 < a i) (hab : ∀ i, a i < b) (hσ : σ = 1 ∨ σ = -1)
    (hχS : ∀ i, χ i '' _root_.Metric.closedBall 0 1 = S i)
    (hcap : ∀ i, ∀ x ∈ _root_.Metric.closedBall 0 1,
      f i (χ i x) = Ψ (EuclideanGeometry.cylinderCap ((if i = 0 then σ else -σ) * a i) x))
    (hflat : ∀ i, ∀ x ∈ _root_.Metric.closedBall 0 1, g i (χ i x) = Ψ (x, 0))
    (hfix : ∀ i, _root_.Set.EqOn (f i) e (S i)ᶜ) (hgfix : ∀ i, _root_.Set.EqOn (g i) e (S i)ᶜ)
    (hret : ∀ i, ∀ p ∈ _root_.Metric.ball 0 R ×ˢ _root_.Set.Ioo (-b) b,
      Ψ p ∈ e '' (S i)ᶜ ↔ ‖p.1‖ = 1 ∧ 0 < (if i = 0 then σ else -σ) * p.2)
    (hS : ∀ p ∈ _root_.Metric.ball 0 R ×ˢ _root_.Set.Ioo (-b) b, Ψ p ∈ _root_.Set.range e ↔ ‖p.1‖ = 1)
    (hshared : _root_.Set.range (g 0) ∩ _root_.Set.range (g 1) = Ψ '' (_root_.Metric.closedBall 0 1 ×ˢ {(0 : ℝ)}))
    (hrel : (Disjoint (dg 0).compactSide (dg 1).compactSide ∧
        closure d.compactSide = closure (dg 0).compactSide ∪ closure (dg 1).compactSide ∧
        closure (dg 0).compactSide ∩ closure (dg 1).compactSide =
          Ψ '' (_root_.Metric.closedBall 0 1 ×ˢ {(0 : ℝ)})) ∨
      ((dg 0).compactSide ⊆ (dg 1).compactSide ∧
        closure d.compactSide = closure (interior (closure (dg 1).compactSide) \ closure (dg 0).compactSide) ∧
        closure (dg 1).compactSide = closure d.compactSide ∪ closure (dg 0).compactSide) ∨
      ((dg 1).compactSide ⊆ (dg 0).compactSide ∧
        closure d.compactSide = closure (interior (closure (dg 0).compactSide) \ closure (dg 1).compactSide) ∧
        closure (dg 0).compactSide = closure d.compactSide ∪ closure (dg 1).compactSide))
    (hD : ∀ i, D i '' _root_.Metric.closedBall 0 1 = closure (df i).compactSide) :
    ∃ H : EuclideanSpace ℝ (Fin ((m + 1) + 1)) ≃ₘ[ℝ]
        EuclideanSpace ℝ (Fin ((m + 1) + 1)),
      H '' _root_.Metric.closedBall 0 1 = closure d.compactSide ∧ H '' _root_.Metric.sphere 0 1 = _root_.Set.range e := by
  let M := EuclideanSpace ℝ (Fin ((m + 1) + 1))
  have hfinish (H : M ≃ₘ[ℝ] M) (hH : H '' _root_.Metric.closedBall 0 1 = closure d.compactSide) :
      H '' _root_.Metric.sphere 0 1 = _root_.Set.range e := by
    have hh : H '' frontier (_root_.Metric.closedBall 0 1) = frontier (H '' _root_.Metric.closedBall 0 1) :=
      H.toHomeomorph.image_frontier _
    rw [frontier_closedBall _ one_ne_zero, hH, frontier, closure_closure, d.interior_closure_compactSide,
      ← d.isOpen_compactSide.frontier_eq, d.frontier_compactSide] at hh
    exact hh
  have hforward (hcase :
      (Disjoint (dg 0).compactSide (dg 1).compactSide ∧
        closure d.compactSide = closure (dg 0).compactSide ∪ closure (dg 1).compactSide ∧
        closure (dg 0).compactSide ∩ closure (dg 1).compactSide = Ψ '' (_root_.Metric.closedBall 0 1 ×ˢ {(0 : ℝ)})) ∨
      ((dg 0).compactSide ⊆ (dg 1).compactSide ∧
        closure d.compactSide = closure (interior (closure (dg 1).compactSide) \ closure (dg 0).compactSide) ∧
        closure (dg 1).compactSide = closure d.compactSide ∪ closure (dg 0).compactSide)) :
      ∃ H : M ≃ₘ[ℝ] M, H '' _root_.Metric.closedBall 0 1 = closure d.compactSide := by
    obtain ⟨H, hH, _⟩ := exists_diffeomorph_flat_cap_absorption m hm d df dg Ψ χ (D 0)
      hR ha hab hσ hχS hcap hflat hfix hgfix hret hS hshared hcase (hD 0)
    refine ⟨(D 1).trans H, ?_⟩
    change (H ∘ D 1) '' _ = _
    rw [_root_.Set.image_comp, hD 1, hH]
  rcases hrel with hdisj | hnest | hnest
  · obtain ⟨H, hH⟩ := hforward (Or.inl hdisj)
    exact ⟨H, hH, hfinish H hH⟩
  · obtain ⟨H, hH⟩ := hforward (Or.inr hnest)
    exact ⟨H, hH, hfinish H hH⟩
  · let τ : Fin 2 → Fin 2 := fun i => if i = 0 then 1 else 0
    have hsign (i : Fin 2) : (if τ i = 0 then σ else -σ) = (if i = 0 then -σ else - -σ) := by
      fin_cases i <;> simp [τ]
    have hnegσ : -σ = 1 ∨ -σ = -1 := by rcases hσ with rfl | rfl <;> norm_num
    obtain ⟨H, hH, _⟩ := exists_diffeomorph_flat_cap_absorption m hm d
      (fun i => df (τ i)) (fun i => dg (τ i)) Ψ (fun i => χ (τ i)) (D 1)
      hR (fun i => ha (τ i)) (fun i => hab (τ i)) hnegσ (fun i => hχS (τ i))
      (by intro i x hx; simpa only [hsign] using hcap (τ i) x hx)
      (fun i => hflat (τ i)) (fun i => hfix (τ i)) (fun i => hgfix (τ i))
      (by intro i p hp; simpa only [hsign] using hret (τ i) p hp) hS
      (by simpa [τ, _root_.Set.inter_comm] using hshared)
      (Or.inr (by simpa [τ] using hnest))
      (by simpa [τ] using hD 1)
    have hball : ((D 0).trans H) '' _root_.Metric.closedBall 0 1 = closure d.compactSide := by
      change (H ∘ D 0) '' _ = _
      rw [_root_.Set.image_comp, hD 0]
      simpa [τ] using hH
    exact ⟨(D 0).trans H, hball, hfinish _ hball⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.exists_diffeomorph_ball_of_flat_caps then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.exists_diffeomorph_ball_of_flat_caps"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.exists_diffeomorph_ball_of_flat_caps ``Submission.DifferentialGeometry.Topology.SphereSeparation.exists_diffeomorph_ball_of_flat_caps

attribute [local instance] Handle.closedCellChartedSpaceSucc Handle.closedCellIsManifold

theorem exists_diffeomorph_ball_of_flat_cap_reconstruction
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
    {f g : Fin 2 → SphereTwo → EuclideanThree}
    (hf : ∀ i, _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (f i))
    (hcap : ∀ i, ∀ x ∈ _root_.Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,
      f i (χ i x) = Ψ (EuclideanGeometry.cylinderCap ((if i = 0 then σ else -σ) * a i) x))
    (hffix : ∀ i, _root_.Set.EqOn (f i) e (_root_.Set.range (b i))ᶜ)
    (hret : ∀ i, ∀ p ∈ _root_.Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R ×ˢ _root_.Set.Ioo (-ε) ε,
      Ψ p ∈ e '' (_root_.Set.range (b i))ᶜ ↔ ‖p.1‖ = 1 ∧ 0 < (if i = 0 then σ else -σ) * p.2)
    (hflat : ∀ i, ∀ x ∈ _root_.Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, g i (χ i x) = Ψ (x, 0))
    (hgfix : ∀ i, _root_.Set.EqOn (g i) e (_root_.Set.range (b i))ᶜ)
    (hrange : ∀ i, _root_.Set.range (g i) = Ψ '' (_root_.Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ×ˢ {0}) ∪
      e '' (_root_.Set.range (b i))ᶜ)
    (hgin : _root_.Set.range (g 0) ∩ _root_.Set.range (g 1) =
      Ψ '' (_root_.Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ×ˢ {0}))
    (hgun : _root_.Set.range (g 0) ∪ _root_.Set.range (g 1) = _root_.Set.range e ∪
      Ψ '' (_root_.Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ×ˢ {0}))
    (D : Fin 2 → EuclideanThree ≃ₘ[ℝ] EuclideanThree)
    (hD : ∀ i, D i '' _root_.Metric.closedBall 0 1 = closure
      (jordanBrouwer_openThreeSpace (f i) (hf i)
        (Diffeomorph.refl (𝓡 3) EuclideanThree ∞)).toSphereSides.compactSide) :
    let d := (jordanBrouwer_openThreeSpace e he
      (Diffeomorph.refl (𝓡 3) EuclideanThree ∞)).toSphereSides
    ∃ H : EuclideanThree ≃ₘ[ℝ] EuclideanThree,
      H '' _root_.Metric.closedBall 0 1 = closure d.compactSide ∧ H '' _root_.Metric.sphere 0 1 = _root_.Set.range e := by
  let s : Fin 2 → ℝ := fun i => if i = 0 then σ else -σ
  have hs (i : Fin 2) : s i = 1 ∨ s i = -1 := by
    dsimp [s]
    split_ifs
    · exact hσ
    · rcases hσ with rfl | rfl <;> norm_num
  have hsa (i : Fin 2) : s i * a i ≠ 0 :=
    mul_ne_zero (by rcases hs i with hh | hh <;> rw [hh] <;> norm_num) (ha i).ne'
  have hab (i : Fin 2) : |s i * a i| < ε := by
    have habs : |s i| = 1 := by rcases hs i with hh | hh <;> rw [hh] <;> norm_num
    rw [abs_mul, habs, one_mul, abs_of_pos (ha i)]
    exact haε i
  have hside (i : Fin 2) (p : EuclideanSpace ℝ (Fin 2) × ℝ)
      (hp : p ∈ _root_.Metric.ball 0 R ×ˢ _root_.Set.Ioo (-ε) ε) (hh : Ψ p ∈ e '' (_root_.Set.range (b i))ᶜ) :
      ‖p.1‖ = 1 ∧ 0 ≤ (s i * a i) * p.2 := by
    have ht := (hret i p hp).mp hh
    refine ⟨ht.1, ?_⟩
    have hn : 0 ≤ a i * (s i * p.2) := mul_nonneg (ha i).le ht.2.le
    nlinarith
  obtain ⟨Φ, C, dg, _, hrel⟩ := exists_flat_cap_reconstruction_regions he hb hbboundary hcover
    hinter Ψ hR hS hboundary χ hχ hχD hsa hab hf hcap hffix hside hflat hgfix hrange hgin hgun
  let d := (jordanBrouwer_openThreeSpace e he
    (Diffeomorph.refl (𝓡 3) EuclideanThree ∞)).toSphereSides
  let df := fun i => (jordanBrouwer_openThreeSpace (f i) (hf i)
    (Diffeomorph.refl (𝓡 3) EuclideanThree ∞)).toSphereSides
  have hcyl : ∀ p ∈ _root_.Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R ×ˢ _root_.Set.Ioo (-ε) ε,
      Ψ p ∈ _root_.Set.range e ↔ ‖p.1‖ = 1 := by
    intro p hp
    have hclosed : p ∈ _root_.Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) R ×ˢ _root_.Set.Icc (-ε) ε :=
      ⟨ball_subset_closedBall hp.1, _root_.Set.Ioo_subset_Icc_self hp.2⟩
    constructor
    · intro hh
      have hh' := hS.subset ⟨hh, hclosed⟩
      exact mem_sphere_zero_iff_norm.mp hh'.1
    · intro hh
      exact (hS.symm.subset ⟨mem_sphere_zero_iff_norm.mpr hh, hclosed.2⟩).1
  apply exists_diffeomorph_ball_of_flat_caps 1 (by norm_num) d df dg Ψ (fun i => χ i) D hR ha haε hσ hχD
    hcap hflat hffix hgfix hret hcyl hgin _ hD
  rcases hrel with hh | hh | hh
  · exact Or.inl hh
  · exact Or.inr (Or.inl ⟨hh.1.subset, hh.2.2.1, hh.2.2.2.1⟩)
  · exact Or.inr (Or.inr ⟨hh.1.subset, hh.2.2.1, hh.2.2.2.1⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.exists_diffeomorph_ball_of_flat_cap_reconstruction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.exists_diffeomorph_ball_of_flat_cap_reconstruction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.exists_diffeomorph_ball_of_flat_cap_reconstruction ``Submission.DifferentialGeometry.Topology.SphereSeparation.exists_diffeomorph_ball_of_flat_cap_reconstruction

end DifferentialGeometry.Topology.SphereSeparation
