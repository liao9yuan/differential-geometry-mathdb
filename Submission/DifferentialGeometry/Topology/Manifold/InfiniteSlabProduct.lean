import Submission.DifferentialGeometry.Topology.Manifold.CylinderCollar.InfiniteSlabs
import Submission.DifferentialGeometry.Topology.Manifold.ProductChartProper

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Filter _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.NNReal

namespace DifferentialGeometry.Topology.Manifold

private abbrev S2 := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.S2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.S2 target :: scope.openDecls } }
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.IC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.IC target :: scope.openDecls } }

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [CompactlyCoherentSpace M]

theorem exists_proper_smooth_product_of_slabs_eq_on_first_slab
    (P : ℕ → PartialDiffeomorph IC I (S2 × ℝ) M ∞)
    (η : ℕ → S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2)
    (hsource : ∀ n, _root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1 ⊆ (P n).source)
    (hseam : ∀ n z, P (n + 1) (z, 0) = P n (η n z, 1))
    (hadjacent : ∀ n, P n '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) ∩
      P (n + 1) '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) = P n '' (_root_.Set.univ ×ˢ ({1} : Set ℝ)))
    (hseparated : ∀ m n : ℕ, m + 1 < n →
      Disjoint (P m '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1)) (P n '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1)))
    (hescape : ∀ K : Set M, IsCompact K → ∀ᶠ n in _root_.Filter.atTop,
      Disjoint (P n '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1)) K) :
    ∃ Θ : S2 × ℝ → M,
      ContMDiffOn IC I ∞ Θ (_root_.Set.univ ×ˢ _root_.Set.Ici (0 : ℝ)) ∧
      _root_.Set.InjOn Θ (_root_.Set.univ ×ˢ _root_.Set.Ici (0 : ℝ)) ∧
      IsProperMap (fun z : S2 × ℝ≥0 => Θ (z.1, z.2.val)) ∧
      (let U : TopologicalSpace.Opens (S2 × ℝ) :=
        ⟨univ ×ˢ _root_.Set.Ioi (0 : ℝ), isOpen_univ.prod isOpen_Ioi⟩
       _root_.Manifold.IsSmoothEmbedding IC I ∞ (fun z : U => Θ z)) ∧
      Θ '' (_root_.Set.univ ×ˢ _root_.Set.Ici (0 : ℝ)) = ⋃ n, P n '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) ∧
      (∀ z t, t ∈ _root_.Set.Icc (0 : ℝ) 1 → Θ (z, t) = P 0 (z, t)) ∧
      ∀ n : ℕ, Θ '' (_root_.Set.univ ×ˢ _root_.Set.Icc (n : ℝ) ((n : ℝ) + 1)) =
        P n '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) := by
  obtain ⟨Q, hQ0, hQs, hQi, hQu, hQseam⟩ :=
    exists_compatible_slab_parametrizations P η hsource hseam hadjacent
  have hQface (n) : Q n '' (_root_.Set.univ ×ˢ ({1} : Set ℝ)) =
      P n '' (_root_.Set.univ ×ˢ ({1} : Set ℝ)) := by
    obtain ⟨μ, hμ⟩ := hQu n
    ext x
    constructor
    · rintro ⟨⟨z, t⟩, ⟨_, ht⟩, hzx⟩
      have : t = 1 := ht
      subst t
      exact ⟨(μ z, 1), ⟨mem_univ _, rfl⟩, (hμ z).symm.trans hzx⟩
    · rintro ⟨⟨z, t⟩, ⟨_, ht⟩, hzx⟩
      have : t = 1 := ht
      subst t
      refine ⟨(μ.symm z, 1), ⟨mem_univ _, rfl⟩, (hμ _).trans ?_⟩
      exact (congrArg (fun q => P n (q, 1))
        (show μ (μ.symm z) = z from μ.apply_symm_apply z)).trans hzx
  have hQa (n) : Q n '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) ∩
      Q (n + 1) '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) = Q n '' (_root_.Set.univ ×ˢ ({1} : Set ℝ)) := by
    rw [hQi, hQi, hQface]
    exact hadjacent n
  have hQsep (m n : ℕ) (hmn : m + 1 < n) :
      Disjoint (Q m '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1)) (Q n '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1)) := by
    rw [hQi, hQi]
    exact hseparated m n hmn
  have hQesc (K : Set M) (hK : IsCompact K) : ∀ᶠ n in _root_.Filter.atTop,
      Disjoint (Q n '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1)) K := by
    simpa only [hQi] using hescape K hK
  obtain ⟨hproper, _, hrange, hbase, hstrip⟩ :=
    isProperMap_product_of_compatible_slabs Q hQs hQseam hQa hQsep hQesc
  let Θ := productChartMap (fun n => Q n)
  refine ⟨Θ, contMDiffOn_productChartMap_nonnegative Q hQs hQseam,
    productChartMap_injOn Q hQs hQa hQsep, hproper,
    isSmoothEmbedding_productChartMap_interior Q hQs hQseam hQa hQsep, ?_, ?_, ?_⟩
  · have heq : Θ '' (_root_.Set.univ ×ˢ _root_.Set.Ici (0 : ℝ)) = _root_.Set.range (halfCylinderProductMap (fun n => Q n)) := by
      ext x
      constructor
      · rintro ⟨⟨z, t⟩, ht, htx⟩
        exact ⟨(z, ⟨t, ht.2⟩), htx⟩
      · rintro ⟨⟨z, t⟩, htx⟩
        exact ⟨(z, t.val), ⟨mem_univ _, t.property⟩, htx⟩
    rw [heq, hrange]
    simp only [hQi]
  · intro z t ht
    have h := hstrip 0 z t ht
    simpa only [halfCylinderProductMap, Nat.cast_zero, zero_add, hQ0, Θ] using h
  · intro n
    rw [← hQi n]
    ext x
    constructor
    · rintro ⟨⟨z, t⟩, ht, htx⟩
      have htt : t - (n : ℝ) ∈ _root_.Set.Icc (0 : ℝ) 1 :=
        ⟨by linarith [ht.2.1], by linarith [ht.2.2]⟩
      have he := hstrip n z (t - n) htt
      have ht0 : 0 ≤ t := (Nat.cast_nonneg n).trans ht.2.1
      change Θ (z, (n : ℝ) + (t - n)) = Q n (z, t - n) at he
      rw [add_sub_cancel] at he
      exact ⟨(z, t - n), ⟨mem_univ _, htt⟩, he.symm.trans htx⟩
    · rintro ⟨⟨z, t⟩, ht, htx⟩
      exact ⟨(z, (n : ℝ) + t), ⟨mem_univ _, by linarith [ht.2.1], by linarith [ht.2.2]⟩,
        (hstrip n z t ht.2).trans htx⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.exists_proper_smooth_product_of_slabs_eq_on_first_slab then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.exists_proper_smooth_product_of_slabs_eq_on_first_slab"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.exists_proper_smooth_product_of_slabs_eq_on_first_slab ``Submission.DifferentialGeometry.Topology.Manifold.exists_proper_smooth_product_of_slabs_eq_on_first_slab


theorem exists_proper_smooth_product_of_slabs
    (P : ℕ → PartialDiffeomorph IC I (S2 × ℝ) M ∞)
    (η : ℕ → S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2)
    (hsource : ∀ n, _root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1 ⊆ (P n).source)
    (hseam : ∀ n z, P (n + 1) (z, 0) = P n (η n z, 1))
    (hadjacent : ∀ n, P n '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) ∩
      P (n + 1) '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) = P n '' (_root_.Set.univ ×ˢ ({1} : Set ℝ)))
    (hseparated : ∀ m n : ℕ, m + 1 < n →
      Disjoint (P m '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1)) (P n '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1)))
    (hescape : ∀ K : Set M, IsCompact K → ∀ᶠ n in _root_.Filter.atTop,
      Disjoint (P n '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1)) K) :
    ∃ Θ : S2 × ℝ → M,
      ContMDiffOn IC I ∞ Θ (_root_.Set.univ ×ˢ _root_.Set.Ici (0 : ℝ)) ∧
      _root_.Set.InjOn Θ (_root_.Set.univ ×ˢ _root_.Set.Ici (0 : ℝ)) ∧
      IsProperMap (fun z : S2 × ℝ≥0 => Θ (z.1, z.2.val)) ∧
      (let U : TopologicalSpace.Opens (S2 × ℝ) :=
        ⟨univ ×ˢ _root_.Set.Ioi (0 : ℝ), isOpen_univ.prod isOpen_Ioi⟩
       _root_.Manifold.IsSmoothEmbedding IC I ∞ (fun z : U => Θ z)) ∧
      Θ '' (_root_.Set.univ ×ˢ _root_.Set.Ici (0 : ℝ)) = ⋃ n, P n '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) ∧
      (∀ z, Θ (z, 0) = P 0 (z, 0)) ∧
      ∀ n : ℕ, Θ '' (_root_.Set.univ ×ˢ _root_.Set.Icc (n : ℝ) ((n : ℝ) + 1)) =
        P n '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) := by
  obtain ⟨Theta, hsmooth, hinj, hproper, hembed, hrange, hfirst, hstrip⟩ :=
    exists_proper_smooth_product_of_slabs_eq_on_first_slab P η
      hsource hseam hadjacent hseparated hescape
  exact ⟨Theta, hsmooth, hinj, hproper, hembed, hrange,
    fun z => hfirst z 0 ⟨le_rfl, zero_le_one⟩, hstrip⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.exists_proper_smooth_product_of_slabs then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.exists_proper_smooth_product_of_slabs"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.exists_proper_smooth_product_of_slabs ``Submission.DifferentialGeometry.Topology.Manifold.exists_proper_smooth_product_of_slabs

end DifferentialGeometry.Topology.Manifold
