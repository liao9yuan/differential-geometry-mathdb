import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialCapContact

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Submission.Set _root_.Metric _root_.Submission.Metric _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
  {eps epsc t : ℝ} {y : M} {U : Set M}

theorem exists_cap_move_on_finite_spatial_neck_frontier_of_sphere_subset
    {g : SmoothRiemannianMetric I3 M} {ι : Type*} (alive : Finset ι) (point : ι → M)
    (neck : ∀ i, SpatialNeck g eps (point i)) (level : ι → ℝ)
    (hlevel : ∀ i ∈ alive, |level i| ≤ 4)
    (hdisjoint : (alive : Set ι).Pairwise (fun i j =>
      Disjoint (_root_.Set.range (fun q : Sphere 2 => (neck i).map (q, level i)))
        (_root_.Set.range (fun q : Sphere 2 => (neck j).map (q, level j)))))
    (i : ι) (hi : i ∈ alive) (cap : CapCore U)
    (hinside : _root_.Set.range (fun z : Sphere 2 => (neck i).map (z, level i)) ⊆ interior U)
    {W : Set M} (hcompact : IsCompact W) (hW : closure (interior W) = W)
    (hconn : IsPreconnected (interior W))
    (hfront : frontier W = ⋃ j ∈ alive, _root_.Set.range (fun z : Sphere 2 => (neck j).map (z, level j))) :
    ∃ (V K : Set M) (next : Finset ι),
      IsCompact V ∧ closure (interior V) = V ∧ W ⊆ V ∧
      IsCompact K ∧ closure (interior K) = K ∧ K ⊆ interior U ∧
      frontier K = _root_.Set.range (fun z : Sphere 2 => (neck i).map (z, level i)) ∧
      frontier V = ⋃ j ∈ next, _root_.Set.range (fun z : Sphere 2 => (neck j).map (z, level j)) ∧
      next ⊆ alive ∧ next.card ≤ alive.card ∧
      (1 < alive.card → next.card < alive.card) ∧
      ((V = K ∧ next = {i}) ∨
        (V = W ∪ K ∧ (next : Set ι) = (alive : Set ι) \ {i} ∧
          K ∩ W = _root_.Set.range (fun z : Sphere 2 => (neck i).map (z, level i)) ∧
          _root_.Set.range (fun z : Sphere 2 => (neck i).map (z, level i)) ⊆ interior V ∧
          next.card < alive.card)) := by
  classical
  let F (j : ι) := _root_.Set.range (fun z : Sphere 2 => (neck j).map (z, level j))
  let R := ⋃ j ∈ alive.erase i, F j
  have hFclosed (j : ι) (hj : j ∈ alive) : IsClosed (F j) := by
    have hlen : (4 : ℝ) < eps⁻¹ :=
      (lt_inv_comm₀ (by norm_num) (neck j).eps_pos).mpr (by linarith [(neck j).eps_small])
    apply IsCompact.isClosed
    apply isCompact_range
    exact (neck j).map.contMDiffOn_toFun.continuousOn.comp_continuous
      (continuous_id.prodMk continuous_const)
      (fun q => (neck j).domain ⟨mem_univ _, by constructor <;>
        linarith [(abs_le.mp (hlevel j hj)).1, (abs_le.mp (hlevel j hj)).2]⟩)
  have hR : IsClosed R := by
    apply Set.Finite.isClosed_biUnion (alive.erase i).finite_toSet
    intro j hj
    exact hFclosed j (Finset.mem_of_mem_erase hj)
  have hfront' : frontier W = F i ∪ R := by
    rw [hfront]
    ext x
    simp only [F, R, _root_.Set.mem_union, _root_.Set.mem_iUnion, Finset.mem_erase]
    constructor
    · rintro ⟨j, hj, hx⟩
      by_cases hji : j = i
      · subst j; exact Or.inl hx
      · exact Or.inr ⟨j, ⟨hji, hj⟩, hx⟩
    · rintro (hx | ⟨j, hj, hx⟩)
      · exact ⟨i, hi, hx⟩
      · exact ⟨j, hj.2, hx⟩
  have hdis : Disjoint (F i) R := by
    apply disjoint_iUnion_right.mpr
    intro j
    apply disjoint_iUnion_right.mpr
    intro hj
    exact hdisjoint hi (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj).symm
  obtain ⟨K, hK, hKr, hKf, hKin, hcases⟩ :=
    (neck i).exists_cap_filling_or_containment_of_sphere_subset (hlevel i hi) cap hinside
      hW hconn hR hfront' hdis
  rcases hcases with hsub | ⟨hinter, hreg, hfrontV, hfill⟩
  · refine ⟨K, K, {i}, hK, hKr, hsub, hK, hKr, hKin, hKf, ?_, ?_, ?_, ?_,
      Or.inl ⟨rfl, rfl⟩⟩
    · simpa using hKf
    · exact Finset.singleton_subset_iff.mpr hi
    · simpa only [Finset.card_singleton] using Finset.one_le_card.mpr ⟨i, hi⟩
    · simpa only [Finset.card_singleton] using fun h : 1 < alive.card => h
  · have hlt : (alive.erase i).card < alive.card := Finset.card_erase_lt_of_mem hi
    refine ⟨W ∪ K, K, alive.erase i, hcompact.union hK, hreg, _root_.Set.subset_union_left,
      hK, hKr, hKin, hKf, hfrontV, Finset.erase_subset _ _, hlt.le, fun _ => hlt,
      Or.inr ⟨rfl, by ext j; simp [and_comm], hinter, hfill, hlt⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_cap_move_on_finite_spatial_neck_frontier_of_sphere_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_cap_move_on_finite_spatial_neck_frontier_of_sphere_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_cap_move_on_finite_spatial_neck_frontier_of_sphere_subset ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_cap_move_on_finite_spatial_neck_frontier_of_sphere_subset

theorem exists_cap_move_on_finite_spatial_neck_frontier
    {ι : Type*} (alive : Finset ι) (point : ι → M)
    (neck : ∀ i, SpatialNeck (S.base.metric t) eps (point i)) (level : ι → ℝ)
    (hlevel : ∀ i ∈ alive, |level i| ≤ 4)
    (hdisjoint : (alive : Set ι).Pairwise (fun i j =>
      Disjoint (_root_.Set.range (fun q : Sphere 2 => (neck i).map (q, level i)))
        (_root_.Set.range (fun q : Sphere 2 => (neck j).map (q, level j)))))
    (heps : eps ≤ 1 / 8646) (i : ι) (hi : i ∈ alive) (q : Sphere 2)
    (hy : (neck i).map (q, level i) = y)
    (cap : LocalCap S epsc y t U)
    (hdepth : ∀ z ∈ cap.tube,
      10000 / Real.sqrt (S.scalar t y) ≤ metricDistance (S.base.metric t) y z)
    {W : Set M} (hcompact : IsCompact W) (hW : closure (interior W) = W)
    (hconn : IsPreconnected (interior W))
    (hfront : frontier W = ⋃ j ∈ alive, _root_.Set.range (fun z : Sphere 2 => (neck j).map (z, level j))) :
    ∃ (V K : Set M) (next : Finset ι),
      IsCompact V ∧ closure (interior V) = V ∧ W ⊆ V ∧
      IsCompact K ∧ closure (interior K) = K ∧ K ⊆ interior cap.core.carrier ∧
      frontier K = _root_.Set.range (fun z : Sphere 2 => (neck i).map (z, level i)) ∧
      frontier V = ⋃ j ∈ next, _root_.Set.range (fun z : Sphere 2 => (neck j).map (z, level j)) ∧
      next ⊆ alive ∧ next.card ≤ alive.card ∧
      (1 < alive.card → next.card < alive.card) ∧
      ((V = K ∧ next = {i}) ∨
        (V = W ∪ K ∧ (next : Set ι) = (alive : Set ι) \ {i} ∧
          K ∩ W = _root_.Set.range (fun z : Sphere 2 => (neck i).map (z, level i)) ∧
          _root_.Set.range (fun z : Sphere 2 => (neck i).map (z, level i)) ⊆ interior V ∧
          next.card < alive.card)) := by
  exact exists_cap_move_on_finite_spatial_neck_frontier_of_sphere_subset alive point neck level
    hlevel hdisjoint i hi cap.core_model
    (by
      rintro z ⟨v, rfl⟩
      exact (neck i).image_slab_subset_cap_core_of_center_in_slab heps q (hlevel i hi) hy cap hdepth
        ⟨(v, level i), ⟨mem_univ _, abs_le.mp (hlevel i hi)⟩, rfl⟩)
    hcompact hW hconn hfront

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_cap_move_on_finite_spatial_neck_frontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_cap_move_on_finite_spatial_neck_frontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_cap_move_on_finite_spatial_neck_frontier ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_cap_move_on_finite_spatial_neck_frontier

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
