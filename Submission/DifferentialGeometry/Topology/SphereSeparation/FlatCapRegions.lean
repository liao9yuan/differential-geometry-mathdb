import Submission.DifferentialGeometry.Topology.SphereSeparation.FlatCapNormalCharts
import Submission.DifferentialGeometry.Topology.SphereSeparation.SmoothReconstructionRegions
import Submission.DifferentialGeometry.Topology.Handle.SphereEmbedding

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Submission.Set _root_.Metric _root_.Manifold _root_.Submission.Manifold
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold

namespace DifferentialGeometry.Topology.SphereSeparation.SphereSides

attribute [local instance] Handle.closedCellChartedSpaceSucc Handle.closedCellIsManifold

theorem flat_cap_reconstruction_regions
    {e : SphereTwo → EuclideanThree} (he : _root_.Topology.IsEmbedding e)
    {b : Fin 2 → ClosedCell 2 → SphereTwo}
    (hb : ∀ i, _root_.Manifold.IsSmoothEmbedding (𝓡∂ 2) (𝓡 2) ∞ (b i))
    {η : AddCircle (1 : ℝ) → SphereTwo}
    (hbboundary : ∀ i, _root_.Set.range (b i ∘ cellBoundaryInclusion 2) = _root_.Set.range η)
    (hcover : _root_.Set.range (b 0) ∪ _root_.Set.range (b 1) = _root_.Set.univ)
    (hinter : _root_.Set.range (b 0) ∩ _root_.Set.range (b 1) = _root_.Set.range η)
    (Ψ : (EuclideanSpace ℝ (Fin 2) × ℝ) ≃ₘ[ℝ] EuclideanThree)
    {R ε : ℝ} (hR : 1 ≤ R) (hε : 0 ≤ ε)
    (hS : Ψ ⁻¹' _root_.Set.range e ∩ (_root_.Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) R ×ˢ _root_.Set.Icc (-ε) ε) =
      _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ×ˢ _root_.Set.Icc (-ε) ε)
    (hboundary : e '' _root_.Set.range η = Ψ '' (_root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ×ˢ {0}))
    (χ : Fin 2 → PartialDiffeomorph (𝓡 2) (𝓡 2) (EuclideanSpace ℝ (Fin 2)) SphereTwo ∞)
    (hχ : ∀ i, _root_.Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ⊆ (χ i).source)
    (hχD : ∀ i, χ i '' _root_.Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 = _root_.Set.range (b i))
    {g : Fin 2 → SphereTwo → EuclideanThree} (hg : ∀ i, _root_.Topology.IsEmbedding (g i))
    (hflat : ∀ i, ∀ x ∈ _root_.Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, g i (χ i x) = Ψ (x, 0))
    (hfix : ∀ i, _root_.Set.EqOn (g i) e (_root_.Set.range (b i))ᶜ)
    (hrange : ∀ i, _root_.Set.range (g i) = Ψ '' (_root_.Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ×ˢ {0}) ∪
      e '' (_root_.Set.range (b i))ᶜ)
    (hgin : _root_.Set.range (g 0) ∩ _root_.Set.range (g 1) =
      Ψ '' (_root_.Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ×ˢ {0}))
    (hgun : _root_.Set.range (g 0) ∪ _root_.Set.range (g 1) = _root_.Set.range e ∪
      Ψ '' (_root_.Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ×ˢ {0}))
    (d : SphereSides (_root_.Set.range e)) (d' : ∀ i, SphereSides (_root_.Set.range (g i))) :
    (Disjoint (d' 0).compactSide (d' 1).compactSide ∧
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
      closure d.compactSide ∩ closure (d' 1).compactSide = _root_.Set.range e ∩ _root_.Set.range (g 1)) := by
  classical
  let K := Ψ '' (_root_.Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ×ˢ {0})
  have hwall (x : EuclideanSpace ℝ (Fin 2)) (hx : x ∈ _root_.Metric.closedBall 0 1) :
      Ψ (x, 0) ∈ _root_.Set.range e ↔ ‖x‖ = 1 := by
    have ht : (0 : ℝ) ∈ _root_.Set.Icc (-ε) ε := ⟨neg_nonpos.mpr hε, hε⟩
    constructor
    · intro hh
      have hp : (x, (0 : ℝ)) ∈ _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ×ˢ _root_.Set.Icc (-ε) ε :=
        hS.subset ⟨hh, _root_.Metric.closedBall_subset_closedBall hR hx, ht⟩
      exact mem_sphere_zero_iff_norm.mp hp.1
    · intro hn
      have hp : (x, (0 : ℝ)) ∈ Ψ ⁻¹' _root_.Set.range e ∩
          (_root_.Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) R ×ˢ _root_.Set.Icc (-ε) ε) :=
        hS.symm.subset ⟨mem_sphere_zero_iff_norm.mpr hn, ht⟩
      exact hp.1
  have hKold : K ∩ _root_.Set.range e = e '' _root_.Set.range η := by
    rw [hboundary]
    apply Subset.antisymm
    · rintro z ⟨⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩, hz⟩
      have ht0 : t = 0 := ht
      subst t
      exact ⟨(x, 0), ⟨mem_sphere_zero_iff_norm.mpr ((hwall x hx).mp hz), rfl⟩, rfl⟩
    · rintro z ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
      have ht0 : t = 0 := ht
      subst t
      exact ⟨⟨(x, 0), ⟨sphere_subset_closedBall hx, rfl⟩, rfl⟩,
        (hwall x (_root_.Metric.sphere_subset_closedBall hx)).mpr (mem_sphere_zero_iff_norm.mp hx)⟩
  have hηD (i : Fin 2) : _root_.Set.range η ⊆ _root_.Set.range (b i) := by
    rw [← hbboundary i]
    exact _root_.Set.range_comp_subset_range _ _
  have hdisj (i : Fin 2) : Disjoint K (e '' (_root_.Set.range (b i))ᶜ) := by
    rw [_root_.Set.disjoint_left]
    rintro z hz ⟨y, hy, rfl⟩
    obtain ⟨x, hx, hxy⟩ := hKold.subset ⟨hz, _root_.Set.mem_range_self y⟩
    exact hy ((he.injective hxy) ▸ hηD i hx)
  have hret : Disjoint (e '' (_root_.Set.range (b 0))ᶜ) (e '' (_root_.Set.range (b 1))ᶜ) := by
    rw [_root_.Set.disjoint_left]
    rintro z ⟨x, hx, rfl⟩ ⟨y, hy, hyx⟩
    have hyx' := he.injective hyx
    subst y
    exact (hcover.symm.subset (_root_.Set.mem_univ x)).elim hx hy
  have hdiff (i j : Fin 2)
      (hd : Disjoint (e '' (_root_.Set.range (b i))ᶜ) (e '' (_root_.Set.range (b j))ᶜ)) :
      range (g i) \ _root_.Set.range (g j) = e '' (_root_.Set.range (b i))ᶜ := by
    rw [hrange i, hrange j]
    ext x
    constructor
    · rintro ⟨hx | hx, hn⟩
      · exact False.elim (hn (Or.inl hx))
      · exact hx
    · intro hx
      refine ⟨Or.inr hx, ?_⟩
      rintro (hy | hy)
      · exact (hdisj i).le_bot ⟨hy, hx⟩
      · exact hd.le_bot ⟨hx, hy⟩
  have hdiff₀ := hdiff 0 1 hret
  have hdiff₁ := hdiff 1 0 hret.symm
  have hfront (i : Fin 2) : frontier (_root_.Set.range (b i)) = _root_.Set.range η :=
    (Handle.frontier_range_closedCell_sphere 1 (hb i)).trans (hbboundary i)
  have hcompl (i j : Fin 2) (hcoverij : _root_.Set.range (b i) ∪ _root_.Set.range (b j) = _root_.Set.univ)
      (hinterij : _root_.Set.range (b i) ∩ _root_.Set.range (b j) = _root_.Set.range η) :
      (_root_.Set.range (b i))ᶜ = interior (_root_.Set.range (b j)) := by
    rw [← self_sdiff_frontier (_root_.Set.range (b j)), hfront j, ← hinterij]
    ext x
    constructor
    · intro hx
      exact ⟨(hcoverij.symm.subset (_root_.Set.mem_univ x)).resolve_left hx, fun hh => hx hh.1⟩
    · rintro ⟨hx, hn⟩ hi
      exact hn ⟨hi, hx⟩
  have hcompl₀ := hcompl 0 1 hcover hinter
  have hcompl₁ := hcompl 1 0 (_root_.Set.union_comm _ _ ▸ hcover) (_root_.Set.inter_comm _ _ ▸ hinter)
  have hconn₀ : IsConnected (_root_.Set.range (g 0) \ _root_.Set.range (g 1)) := by
    rw [hdiff₀, hcompl₀]
    exact (Handle.isConnected_interior_range_closedCell_sphere 1 (hb 1)).image e
      he.continuous.continuousOn
  have hconn₁ : IsConnected (_root_.Set.range (g 1) \ _root_.Set.range (g 0)) := by
    rw [hdiff₁, hcompl₁]
    exact (Handle.isConnected_interior_range_closedCell_sphere 1 (hb 0)).image e
      he.continuous.continuousOn
  have hdensity : _root_.Set.range e = closure ((_root_.Set.range (g 0) \ _root_.Set.range (g 1)) ∪
      (_root_.Set.range (g 1) \ _root_.Set.range (g 0))) := by
    rw [hdiff₀, hdiff₁, ← _root_.Set.image_union, hcompl₀, hcompl₁,
      (he.continuous.isClosedEmbedding he.injective).closure_image_eq, closure_union,
      Handle.closure_interior_range_closedCell_sphere 1 (hb 1),
      Handle.closure_interior_range_closedCell_sphere 1 (hb 0), _root_.Set.union_comm, hcover, _root_.Set.image_univ]
  have hlocal (i : Fin 2) (z : SphereTwo) (hz : g i z ∉ _root_.Set.range e) :
      Nonempty (EmbeddedSphereNormalChart (g i) z) := by
    apply embeddedSphereNormalChart_nonempty_of_flat_cap (hg i) Ψ (χ i) (hχ i) (hflat i)
      _ (hboundary.symm.subset.trans (_root_.Set.image_subset_range _ _)) hz
    simpa only [hχD i] using hfix i
  have hclosed : IsClosed (_root_.Set.range e) := (isCompact_range he.continuous).isClosed
  have hpatch : ∀ x ∈ (_root_.Set.range (g 0) ∪ _root_.Set.range (g 1)) \ _root_.Set.range e,
      ∃ O : Set EuclideanThree, IsOpen O ∧ x ∈ O ∧ _root_.Set.range (g 0) ∩ O = _root_.Set.range (g 1) ∩ O := by
    intro x hx
    refine ⟨(_root_.Set.range e)ᶜ, hclosed.isOpen_compl, hx.2, ?_⟩
    have heq (i : Fin 2) : _root_.Set.range (g i) ∩ (_root_.Set.range e)ᶜ = K ∩ (_root_.Set.range e)ᶜ := by
      rw [hrange i]
      apply Subset.antisymm
      · rintro y ⟨hy | hy, hn⟩
        · exact ⟨hy, hn⟩
        · exact False.elim (hn (_root_.Set.image_subset_range _ _ hy))
      · exact fun y hy => ⟨Or.inl hy.1, hy.2⟩
    exact (heq 0).trans (heq 1).symm
  have hpatch' : ∀ x ∈ (_root_.Set.range (g 1) ∪ _root_.Set.range (g 0)) \ _root_.Set.range e,
      ∃ O : Set EuclideanThree, IsOpen O ∧ x ∈ O ∧ _root_.Set.range (g 1) ∩ O = _root_.Set.range (g 0) ∩ O := by
    intro x hx
    obtain ⟨O, hO, hxO, heq⟩ := hpatch x ⟨hx.1.elim Or.inr Or.inl, hx.2⟩
    exact ⟨O, hO, hxO, heq.symm⟩
  have hScover : _root_.Set.range e ⊆ _root_.Set.range (g 0) ∪ _root_.Set.range (g 1) := by
    rw [hgun]
    exact _root_.Set.subset_union_left
  have hne : (d' 0).compactSide ≠ (d' 1).compactSide := by
    intro heq
    have heqS : _root_.Set.range (g 0) = _root_.Set.range (g 1) :=
      (d' 0).frontier_compactSide.symm.trans
        ((congrArg frontier heq).trans (d' 1).frontier_compactSide)
    obtain ⟨x, hx, hn⟩ := hconn₀.nonempty
    exact hn (heqS ▸ hx)
  rcases (d' 0).compactSide_disjoint_or_subset_of_isPreconnected_sdiff (d' 1)
      hconn₁.isPreconnected with hd | hsub | hsub
  · have hh := disjoint_reconstruction_regions_of_local_normal_charts (hlocal 0) d (d' 0) (d' 1)
      hd hdensity hpatch
    exact Or.inl ⟨hd, hh.1, hh.2.trans hgin⟩
  · have hproper := ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩
    have hh := nested_reconstruction_regions_of_local_normal_charts (hlocal 0) d (d' 0) (d' 1)
      hproper hScover hpatch
    refine Or.inr (Or.inl ⟨hproper, hh.1, ?_, hh.2⟩)
    rw [(d' 1).interior_closure_compactSide, hh.1]
  · have hproper := ssubset_iff_subset_ne.mpr ⟨hsub, Ne.symm hne⟩
    have hh := nested_reconstruction_regions_of_local_normal_charts (hlocal 1) d (d' 1) (d' 0)
      hproper (by simpa only [_root_.Set.union_comm] using hScover) hpatch'
    refine Or.inr (Or.inr ⟨hproper, hh.1, ?_, hh.2⟩)
    rw [(d' 0).interior_closure_compactSide, hh.1]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.SphereSides.flat_cap_reconstruction_regions then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.SphereSides.flat_cap_reconstruction_regions"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.SphereSides.flat_cap_reconstruction_regions ``Submission.DifferentialGeometry.Topology.SphereSeparation.SphereSides.flat_cap_reconstruction_regions

end DifferentialGeometry.Topology.SphereSeparation.SphereSides
