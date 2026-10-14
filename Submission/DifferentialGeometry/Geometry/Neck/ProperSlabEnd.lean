import Submission.DifferentialGeometry.Topology.Manifold.InfiniteSlabProduct
import Submission.DifferentialGeometry.Topology.ProperMap.HalfCylinder
import Submission.DifferentialGeometry.Geometry.Neck.SpatialScalarEscape

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Filter _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology _root_.NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

theorem exists_proper_neck_product_of_fresh_slabs_eq_on_first_slab
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    [T2Space M] [CompactlyCoherentSpace M]
    (g : SmoothRiemannianMetric I3 M) {eps : ℝ} (heps : eps ≤ 1 / 156000)
    (p : ℕ → M) (neck : ∀ n, SpatialNeck g eps (p n))
    (hcompact : ∀ B : ℝ, IsCompact {x : M | metricScalarAt g x ≤ B})
    (P : ℕ → PartialDiffeomorph IC I3 Cylinder M ∞)
    (η : ℕ → Sphere 2 ≃ₘ⟮I2, I2⟯ Sphere 2)
    (hsource : ∀ n, _root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1 ⊆ (P n).source)
    (hseam : ∀ n z, P (n + 1) (z, 0) = P n (η n z, 1))
    (hadjacent : ∀ n, P n '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) ∩
      P (n + 1) '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) = P n '' (_root_.Set.univ ×ˢ ({1} : Set ℝ)))
    (hseparated : ∀ m n : ℕ, m + 1 < n →
      Disjoint (P m '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1)) (P n '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1)))
    (hcontrolled : ∀ n, P n '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) ⊆
      (neck n).map '' (_root_.Set.univ ×ˢ _root_.Set.Ioo (-eps⁻¹) eps⁻¹))
    (hband : ∀ n, (neck n).map '' (_root_.Set.univ ×ˢ _root_.Set.Icc (1 : ℝ) 2) ⊆
      P n '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1))
 :
    ∃ Θ : Cylinder → M,
      ContMDiffOn IC I3 ∞ Θ (_root_.Set.univ ×ˢ _root_.Set.Ici (0 : ℝ)) ∧
      _root_.Set.InjOn Θ (_root_.Set.univ ×ˢ _root_.Set.Ici (0 : ℝ)) ∧
      IsProperMap (fun z : Sphere 2 × ℝ≥0 => Θ (z.1, z.2.val)) ∧
      (let U : TopologicalSpace.Opens Cylinder :=
        ⟨univ ×ˢ _root_.Set.Ioi (0 : ℝ), isOpen_univ.prod isOpen_Ioi⟩
       _root_.Manifold.IsSmoothEmbedding IC I3 ∞ (fun z : U => Θ z)) ∧
      Θ '' (_root_.Set.univ ×ˢ _root_.Set.Ici (0 : ℝ)) = ⋃ n, P n '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) ∧
      (∀ z t, t ∈ _root_.Set.Icc (0 : ℝ) 1 → Θ (z, t) = P 0 (z, t)) ∧
      (∀ n : ℕ, Θ '' (_root_.Set.univ ×ˢ _root_.Set.Icc (n : ℝ) ((n : ℝ) + 1)) =
        P n '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1)) ∧
      ∀ B : ℝ, ∃ T : ℝ≥0, ∀ (z : Sphere 2) (t : ℝ≥0),
        T ≤ t → B < metricScalarAt g (Θ (z, t.val)) := by
  have havoid (i j : ℕ) (hij : i < j) :
      (neck j).map ((neck j).center, 3 / 2) ∉ P i '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) := by
    let x := (neck j).map ((neck j).center, 3 / 2)
    have hlen : (2 : ℝ) < eps⁻¹ :=
      (lt_inv_comm₀ (by norm_num) (neck j).eps_pos).mpr (by linarith)
    have hwindow : _root_.Set.univ ×ˢ _root_.Set.Ioo (1 : ℝ) 2 ⊆ (neck j).map.source := by
      intro z hz
      exact (neck j).domain ⟨mem_univ _, by constructor <;> linarith [hz.2.1, hz.2.2]⟩
    have hxo : IsOpen ((neck j).map '' (_root_.Set.univ ×ˢ _root_.Set.Ioo (1 : ℝ) 2)) :=
      (neck j).map.toOpenPartialHomeomorph.isOpen_image_of_subset_source
        (isOpen_univ.prod isOpen_Ioo) hwindow
    have hxint : x ∈ interior (P j '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1)) := by
      apply mem_interior.mpr
      refine ⟨(neck j).map '' (_root_.Set.univ ×ˢ _root_.Set.Ioo (1 : ℝ) 2), ?_, hxo, ?_⟩
      · exact (_root_.Set.image_mono (_root_.Set.prod_mono_right _root_.Set.Ioo_subset_Icc_self)).trans (hband j)
      · exact ⟨((neck j).center, 3 / 2), ⟨mem_univ _, by norm_num⟩, rfl⟩
    intro hxi
    by_cases hsucc : j = i + 1
    · subst j
      have hm := hadjacent i ▸ (show x ∈ P i '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) ∩
          P (i + 1) '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) from ⟨hxi, interior_subset hxint⟩)
      obtain ⟨⟨z, t⟩, ⟨_, ht⟩, hz⟩ := hm
      have ht1 : t = 1 := ht
      subst t
      have hxface : x ∈ P (i + 1) '' (_root_.Set.univ ×ˢ ({0} : Set ℝ)) := by
        refine ⟨((η i).symm z, 0), ⟨mem_univ _, rfl⟩, ?_⟩
        have he := hseam i ((η i).symm z)
        exact he.trans ((congrArg (fun q => P i (q, 1))
          (show η i ((η i).symm z) = z from (η i).apply_symm_apply z)).trans hz)
      have hclosed : IsClosed (P (i + 1) '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1)) :=
        ((isCompact_univ.prod _root_.CompactIccSpace.isCompact_Icc).image_of_continuousOn
          ((P (i + 1)).contMDiffOn_toFun.continuousOn.mono (hsource (i + 1)))).isClosed
      have hf := (P (i + 1)).toOpenPartialHomeomorph.image_frontier_of_subset_source
        (hsource (i + 1)) (isClosed_univ.prod isClosed_Icc) hclosed
      change P (i + 1) '' frontier (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) =
        frontier (P (i + 1) '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1)) at hf
      rw [frontier_univ_prod_eq, frontier_Icc zero_le_one] at hf
      have hxfront : x ∈ frontier (P (i + 1) '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1)) := by
        rw [← hf]
        exact _root_.Set.image_mono (_root_.Set.prod_mono_right (by intro a ha; exact Or.inl ha)) hxface
      exact hxfront.2 hxint
    · have hfar : i + 1 < j := by omega
      exact disjoint_left.mp (hseparated i j hfar) hxi (interior_subset hxint)
  have havoidband (i j : ℕ) (hij : i < j) :
      (neck j).map ((neck j).center, 3 / 2) ∉
        (neck i).map '' (_root_.Set.univ ×ˢ _root_.Set.Icc (1 : ℝ) 2) := fun h => havoid i j hij (hband i h)
  have hescape (K : Set M) (hK : IsCompact K) : ∀ᶠ n in _root_.Filter.atTop,
      Disjoint (P n '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1)) K := by
    filter_upwards [eventually_disjoint_spatial_neck_window_of_midpoint_avoids_earlier_band
      heps p neck hcompact havoidband hK] with n hn
    exact (hn.mono_right (hcontrolled n)).symm
  obtain ⟨Θ, hsmooth, hinj, hproper, hembed, hrange, hbase, hstrip⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_proper_smooth_product_of_slabs_eq_on_first_slab
      P η hsource hseam hadjacent hseparated hescape
  exact ⟨Θ, hsmooth, hinj, hproper, hembed, hrange, hbase, hstrip,
    fun B => DifferentialGeometry.Topology.uniform_scalar_divergence_of_isProperMap
      (metricScalarAt g) hcompact _ hproper B⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_proper_neck_product_of_fresh_slabs_eq_on_first_slab then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_proper_neck_product_of_fresh_slabs_eq_on_first_slab"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_proper_neck_product_of_fresh_slabs_eq_on_first_slab ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_proper_neck_product_of_fresh_slabs_eq_on_first_slab


theorem exists_proper_neck_product_of_fresh_slabs
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    [T2Space M] [CompactlyCoherentSpace M]
    (g : SmoothRiemannianMetric I3 M) {eps : ℝ} (heps : eps ≤ 1 / 156000)
    (p : ℕ → M) (neck : ∀ n, SpatialNeck g eps (p n))
    (hcompact : ∀ B : ℝ, IsCompact {x : M | metricScalarAt g x ≤ B})
    (P : ℕ → PartialDiffeomorph IC I3 Cylinder M ∞)
    (η : ℕ → Sphere 2 ≃ₘ⟮I2, I2⟯ Sphere 2)
    (hsource : ∀ n, _root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1 ⊆ (P n).source)
    (hseam : ∀ n z, P (n + 1) (z, 0) = P n (η n z, 1))
    (hadjacent : ∀ n, P n '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) ∩
      P (n + 1) '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) = P n '' (_root_.Set.univ ×ˢ ({1} : Set ℝ)))
    (hseparated : ∀ m n : ℕ, m + 1 < n →
      Disjoint (P m '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1)) (P n '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1)))
    (hcontrolled : ∀ n, P n '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) ⊆
      (neck n).map '' (_root_.Set.univ ×ˢ _root_.Set.Ioo (-eps⁻¹) eps⁻¹))
    (hband : ∀ n, (neck n).map '' (_root_.Set.univ ×ˢ _root_.Set.Icc (1 : ℝ) 2) ⊆
      P n '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1))
 :
    ∃ Θ : Cylinder → M,
      ContMDiffOn IC I3 ∞ Θ (_root_.Set.univ ×ˢ _root_.Set.Ici (0 : ℝ)) ∧
      _root_.Set.InjOn Θ (_root_.Set.univ ×ˢ _root_.Set.Ici (0 : ℝ)) ∧
      IsProperMap (fun z : Sphere 2 × ℝ≥0 => Θ (z.1, z.2.val)) ∧
      (let U : TopologicalSpace.Opens Cylinder :=
        ⟨univ ×ˢ _root_.Set.Ioi (0 : ℝ), isOpen_univ.prod isOpen_Ioi⟩
       _root_.Manifold.IsSmoothEmbedding IC I3 ∞ (fun z : U => Θ z)) ∧
      Θ '' (_root_.Set.univ ×ˢ _root_.Set.Ici (0 : ℝ)) = ⋃ n, P n '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) ∧
      (∀ z, Θ (z, 0) = P 0 (z, 0)) ∧
      (∀ n : ℕ, Θ '' (_root_.Set.univ ×ˢ _root_.Set.Icc (n : ℝ) ((n : ℝ) + 1)) =
        P n '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1)) ∧
      ∀ B : ℝ, ∃ T : ℝ≥0, ∀ (z : Sphere 2) (t : ℝ≥0),
        T ≤ t → B < metricScalarAt g (Θ (z, t.val)) := by
  obtain ⟨Theta, hsmooth, hinj, hproper, hembed, hrange, hfirst, hstrip, hscalar⟩ :=
    exists_proper_neck_product_of_fresh_slabs_eq_on_first_slab g heps p neck hcompact
      P η hsource hseam hadjacent hseparated hcontrolled hband
  exact ⟨Theta, hsmooth, hinj, hproper, hembed, hrange,
    fun z => hfirst z 0 ⟨le_rfl, zero_le_one⟩, hstrip, hscalar⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_proper_neck_product_of_fresh_slabs then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_proper_neck_product_of_fresh_slabs"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_proper_neck_product_of_fresh_slabs ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_proper_neck_product_of_fresh_slabs


theorem scalar_le_on_first_slab_of_neck_product
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    [T2Space M] {g : SmoothRiemannianMetric I3 M} {eps : ℝ} {p : M}
    (nk : SpatialNeck g eps p)
    (P : PartialDiffeomorph IC I3 Cylinder M ∞) (Theta : Cylinder → M)
    (hfirst : ∀ z t, t ∈ _root_.Set.Icc (0 : ℝ) 1 → Theta (z, t) = P (z, t))
    (hcontrolled : P '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) ⊆ nk.map '' (_root_.Set.univ ×ˢ _root_.Set.Ioo (-eps⁻¹) eps⁻¹)) :
    ∀ z t, t ∈ _root_.Set.Icc (0 : ℝ) 1 →
      metricScalarAt g (Theta (z, t)) ≤ (1 + 4323 * eps) * metricScalarAt g p := by
  intro z t ht
  rw [hfirst z t ht]
  exact (nk.scalar_bounds_on_image_window (hcontrolled ⟨(z, t), ⟨mem_univ _, ht⟩, rfl⟩)).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.scalar_le_on_first_slab_of_neck_product then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.scalar_le_on_first_slab_of_neck_product"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.scalar_le_on_first_slab_of_neck_product ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.scalar_le_on_first_slab_of_neck_product


theorem scalar_le_on_first_slab_of_original_base_bound
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    [T2Space M] {g : SmoothRiemannianMetric I3 M} {eps : ℝ} {p : M}
    (nk : SpatialNeck g eps p) (P : PartialDiffeomorph IC I3 Cylinder M ∞)
    (Theta : Cylinder → M) (S : Set M) (hp : p ∈ S) (B : ℝ)
    (hB : ∀ x ∈ S, metricScalarAt g x ≤ B)
    (hfirst : ∀ z t, t ∈ _root_.Set.Icc (0 : ℝ) 1 → Theta (z, t) = P (z, t))
    (hcontrolled : P '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) ⊆
      nk.map '' (_root_.Set.univ ×ˢ _root_.Set.Ioo (-eps⁻¹) eps⁻¹)) :
    ∀ z t, t ∈ _root_.Set.Icc (0 : ℝ) 1 →
      metricScalarAt g (Theta (z, t)) ≤ (1 + 4323 * eps) * B := by
  intro z t ht
  exact (scalar_le_on_first_slab_of_neck_product nk P Theta hfirst hcontrolled z t ht).trans
    (mul_le_mul_of_nonneg_left (hB p hp) (by have := nk.eps_pos; positivity))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.scalar_le_on_first_slab_of_original_base_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.scalar_le_on_first_slab_of_original_base_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.scalar_le_on_first_slab_of_original_base_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.scalar_le_on_first_slab_of_original_base_bound

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
