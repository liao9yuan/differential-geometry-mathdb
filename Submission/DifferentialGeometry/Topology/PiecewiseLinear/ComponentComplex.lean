/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Subcomplex
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.ManifoldWithBoundary
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PolyhedronLocalConnectedness

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem restrict_connectedComponentIn_space (K : Geometry.SimplicialComplex ℝ E) (p : E) :
    (restrict K (connectedComponentIn K.space p)).space = connectedComponentIn K.space p := by
  apply Subset.antisymm (restrict_space_subset K _)
  intro z hz
  obtain ⟨s, hs, hzs⟩ := K.mem_space_iff.mp (connectedComponentIn_subset K.space p hz)
  have hsub := (convex_convexHull ℝ (s : Set E)).isPreconnected.subset_connectedComponentIn
    hzs (K.convexHull_subset_space hs)
  rw [← connectedComponentIn_eq hz] at hsub
  exact (restrict K (connectedComponentIn K.space p)).convexHull_subset_space ⟨hs, hsub⟩ hzs

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.restrict_connectedComponentIn_space then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.restrict_connectedComponentIn_space"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.restrict_connectedComponentIn_space ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.restrict_connectedComponentIn_space

theorem geometricLink_restrict_connectedComponentIn_of_mem [DecidableEq E]
    (K : Geometry.SimplicialComplex ℝ E) {p v : E} {s : Finset E}
    (hvs : v ∈ s) (hv : v ∈ connectedComponentIn K.space p) :
    SimplicialComplex.geometricLink (restrict K (connectedComponentIn K.space p)) s =
      SimplicialComplex.geometricLink K s := by
  ext t
  simp only [mem_geometricLink_faces_iff, mem_restrict_faces_iff]
  constructor
  · rintro ⟨hne, hdis, ht, -⟩
    exact ⟨hne, hdis, ht⟩
  · rintro ⟨hne, hdis, ht⟩
    refine ⟨hne, hdis, ht, ?_⟩
    have hsub := (convex_convexHull ℝ ((s ∪ t : Finset E) : Set E)).isPreconnected
      |>.subset_connectedComponentIn (subset_convexHull ℝ _ (Finset.mem_union_left t hvs))
        (K.convexHull_subset_space ht)
    rwa [← connectedComponentIn_eq hv] at hsub

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.geometricLink_restrict_connectedComponentIn_of_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.geometricLink_restrict_connectedComponentIn_of_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.geometricLink_restrict_connectedComponentIn_of_mem ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.geometricLink_restrict_connectedComponentIn_of_mem

open _root_.Classical in
theorem geometricLink_restrict_connectedComponentIn (K : Geometry.SimplicialComplex ℝ E)
    {p v : E} (hv : v ∈ connectedComponentIn K.space p) :
    SimplicialComplex.geometricLink (restrict K (connectedComponentIn K.space p)) {v} =
      SimplicialComplex.geometricLink K {v} :=
  geometricLink_restrict_connectedComponentIn_of_mem K (Finset.mem_singleton_self v) hv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.geometricLink_restrict_connectedComponentIn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.geometricLink_restrict_connectedComponentIn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.geometricLink_restrict_connectedComponentIn ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.geometricLink_restrict_connectedComponentIn

theorem boundaryComplex_restrict_connectedComponentIn [DecidableEq E]
    (n : ℕ) (K : Geometry.SimplicialComplex ℝ E) (p : E) :
    boundaryComplex n (restrict K (connectedComponentIn K.space p)) =
      restrict (boundaryComplex n K) (connectedComponentIn K.space p) := by
  ext s
  constructor
  · rintro ⟨⟨hs, hsc⟩, t, ⟨ht, htc⟩, hst, hcard, hball⟩
    obtain ⟨v, hv⟩ := K.nonempty_of_mem_faces ht
    rw [geometricLink_restrict_connectedComponentIn_of_mem K hv
      (htc (subset_convexHull ℝ _ hv))] at hball
    exact ⟨⟨hs, t, ht, hst, hcard, hball⟩, hsc⟩
  · rintro ⟨⟨hs, t, ht, hst, hcard, hball⟩, hsc⟩
    obtain ⟨v, hv⟩ := K.nonempty_of_mem_faces hs
    have hvc := hsc (subset_convexHull ℝ _ hv)
    have htc := (convex_convexHull ℝ (t : Set E)).isPreconnected
      |>.subset_connectedComponentIn (subset_convexHull ℝ _ (hst hv)) (K.convexHull_subset_space ht)
    rw [← connectedComponentIn_eq hvc] at htc
    refine ⟨⟨hs, hsc⟩, t, ⟨ht, htc⟩, hst, hcard, ?_⟩
    rwa [geometricLink_restrict_connectedComponentIn_of_mem K (hst hv) hvc]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.boundaryComplex_restrict_connectedComponentIn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.boundaryComplex_restrict_connectedComponentIn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.boundaryComplex_restrict_connectedComponentIn ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.boundaryComplex_restrict_connectedComponentIn

theorem boundaryComplex_space_restrict_connectedComponentIn [DecidableEq E]
    (n : ℕ) (K : Geometry.SimplicialComplex ℝ E) (p : E) :
    (boundaryComplex n (restrict K (connectedComponentIn K.space p))).space =
      (boundaryComplex n K).space ∩ connectedComponentIn K.space p := by
  rw [boundaryComplex_restrict_connectedComponentIn]
  apply Subset.antisymm
  · exact fun _ hx => ⟨space_mono_of_faces_subset (restrict_faces_subset _ _) hx,
      restrict_space_subset _ _ hx⟩
  · rintro x ⟨hxB, hxC⟩
    obtain ⟨s, hs, hxs⟩ := (boundaryComplex n K).mem_space_iff.mp hxB
    have hsub := (convex_convexHull ℝ (s : Set E)).isPreconnected
      |>.subset_connectedComponentIn hxs (K.convexHull_subset_space hs.1)
    rw [← connectedComponentIn_eq hxC] at hsub
    exact (restrict (boundaryComplex n K) (connectedComponentIn K.space p)).convexHull_subset_space
      ⟨hs, hsub⟩ hxs

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.boundaryComplex_space_restrict_connectedComponentIn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.boundaryComplex_space_restrict_connectedComponentIn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.boundaryComplex_space_restrict_connectedComponentIn ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.boundaryComplex_space_restrict_connectedComponentIn

theorem IsCombinatorialManifoldWithBoundary.restrict_connectedComponentIn
    {K : Geometry.SimplicialComplex ℝ E} {n : ℕ}
    (hK : IsCombinatorialManifoldWithBoundary n K) (p : E) :
    IsCombinatorialManifoldWithBoundary n (restrict K (connectedComponentIn K.space p)) := by
  classical
  cases n with
  | zero =>
    intro v hv
    have hvc : v ∈ connectedComponentIn K.space p := hv.2 (by simp)
    rw [geometricLink_restrict_connectedComponentIn K hvc]
    exact hK v hv.1
  | succ n =>
    intro v hv
    have hvc : v ∈ connectedComponentIn K.space p := hv.2 (by simp)
    rw [geometricLink_restrict_connectedComponentIn K hvc]
    exact hK v hv.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.restrict_connectedComponentIn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.restrict_connectedComponentIn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.restrict_connectedComponentIn ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.restrict_connectedComponentIn

theorem IsCombinatorialManifold.restrict_connectedComponentIn
    {K : Geometry.SimplicialComplex ℝ E} {n : ℕ}
    (hK : IsCombinatorialManifold n K) (p : E) :
    IsCombinatorialManifold n (restrict K (connectedComponentIn K.space p)) := by
  classical
  cases n with
  | zero =>
    intro v hv
    have hvc : v ∈ connectedComponentIn K.space p := hv.2 (by simp)
    rw [geometricLink_restrict_connectedComponentIn K hvc]
    exact hK v hv.1
  | succ n =>
    intro v hv
    have hvc : v ∈ connectedComponentIn K.space p := hv.2 (by simp)
    rw [geometricLink_restrict_connectedComponentIn K hvc]
    exact hK v hv.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.restrict_connectedComponentIn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.restrict_connectedComponentIn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.restrict_connectedComponentIn ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.restrict_connectedComponentIn

def connectedComponentComplex (K : Geometry.SimplicialComplex ℝ E)
    (c : ConnectedComponents K.space) : Geometry.SimplicialComplex ℝ E :=
  restrict K (((↑) : K.space → E) '' (ConnectedComponents.mk ⁻¹' {c}))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.connectedComponentComplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.connectedComponentComplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.connectedComponentComplex ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.connectedComponentComplex

theorem connectedComponentComplex_mk (K : Geometry.SimplicialComplex ℝ E) (p : K.space) :
    connectedComponentComplex K (ConnectedComponents.mk p) =
      restrict K (connectedComponentIn K.space (p : E)) := by
  simp only [connectedComponentComplex, connectedComponents_preimage_singleton,
    ← connectedComponentIn_eq_image p.property]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.connectedComponentComplex_mk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.connectedComponentComplex_mk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.connectedComponentComplex_mk ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.connectedComponentComplex_mk

theorem connectedComponentComplex_space (K : Geometry.SimplicialComplex ℝ E)
    (c : ConnectedComponents K.space) :
    (connectedComponentComplex K c).space =
      ((↑) : K.space → E) '' (ConnectedComponents.mk ⁻¹' {c}) := by
  obtain ⟨p, rfl⟩ := ConnectedComponents.surjective_coe c
  rw [connectedComponentComplex_mk, restrict_connectedComponentIn_space,
    connectedComponents_preimage_singleton, connectedComponentIn_eq_image p.property]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.connectedComponentComplex_space then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.connectedComponentComplex_space"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.connectedComponentComplex_space ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.connectedComponentComplex_space

theorem connectedComponentComplex_faces_finite (K : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] (c : ConnectedComponents K.space) :
    (connectedComponentComplex K c).faces.Finite := restrict_faces_finite K _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.connectedComponentComplex_faces_finite then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.connectedComponentComplex_faces_finite"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.connectedComponentComplex_faces_finite ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.connectedComponentComplex_faces_finite

theorem isConnected_connectedComponentComplex_space (K : Geometry.SimplicialComplex ℝ E)
    (c : ConnectedComponents K.space) : IsConnected (connectedComponentComplex K c).space := by
  obtain ⟨p, rfl⟩ := ConnectedComponents.surjective_coe c
  rw [connectedComponentComplex_mk, restrict_connectedComponentIn_space]
  exact isConnected_connectedComponentIn_iff.mpr p.property

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isConnected_connectedComponentComplex_space then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isConnected_connectedComponentComplex_space"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isConnected_connectedComponentComplex_space ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isConnected_connectedComponentComplex_space

theorem iUnion_connectedComponentComplex_space (K : Geometry.SimplicialComplex ℝ E) :
    ⋃ c, (connectedComponentComplex K c).space = K.space := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨c, hc⟩ := mem_iUnion.mp hx
    rw [connectedComponentComplex_space] at hc
    obtain ⟨p, -, rfl⟩ := hc
    exact p.property
  · intro x hx
    apply mem_iUnion.mpr
    refine ⟨ConnectedComponents.mk (⟨x, hx⟩ : K.space), ?_⟩
    rw [connectedComponentComplex_space]
    exact ⟨⟨x, hx⟩, rfl, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.iUnion_connectedComponentComplex_space then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.iUnion_connectedComponentComplex_space"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.iUnion_connectedComponentComplex_space ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.iUnion_connectedComponentComplex_space

theorem pairwise_disjoint_connectedComponentComplex_space (K : Geometry.SimplicialComplex ℝ E) :
    Pairwise fun c d => Disjoint (connectedComponentComplex K c).space
      (connectedComponentComplex K d).space := by
  intro c d hcd
  apply disjoint_left.mpr
  intro x hxC hxD
  rw [connectedComponentComplex_space] at hxC hxD
  obtain ⟨p, hp, hpx⟩ := hxC
  obtain ⟨q, hq, hqx⟩ := hxD
  have hpq : p = q := Subtype.val_injective (hpx.trans hqx.symm)
  subst q
  exact hcd (hp.symm.trans hq)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.pairwise_disjoint_connectedComponentComplex_space then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.pairwise_disjoint_connectedComponentComplex_space"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.pairwise_disjoint_connectedComponentComplex_space ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.pairwise_disjoint_connectedComponentComplex_space

theorem IsCombinatorialManifold.connectedComponentComplex {n : ℕ}
    {K : Geometry.SimplicialComplex ℝ E} (hK : IsCombinatorialManifold n K)
    (c : ConnectedComponents K.space) :
    IsCombinatorialManifold n (connectedComponentComplex K c) := by
  obtain ⟨p, rfl⟩ := ConnectedComponents.surjective_coe c
  rw [PiecewiseLinear.connectedComponentComplex_mk]
  exact hK.restrict_connectedComponentIn p

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.connectedComponentComplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.connectedComponentComplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.connectedComponentComplex ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.connectedComponentComplex

theorem IsCombinatorialManifoldWithBoundary.connectedComponentComplex {n : ℕ}
    {K : Geometry.SimplicialComplex ℝ E} (hK : IsCombinatorialManifoldWithBoundary n K)
    (c : ConnectedComponents K.space) :
    IsCombinatorialManifoldWithBoundary n (connectedComponentComplex K c) := by
  obtain ⟨p, rfl⟩ := ConnectedComponents.surjective_coe c
  rw [PiecewiseLinear.connectedComponentComplex_mk]
  exact hK.restrict_connectedComponentIn p

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.connectedComponentComplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.connectedComponentComplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.connectedComponentComplex ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.connectedComponentComplex

theorem finite_connectedComponents_space [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] :
    Finite (ConnectedComponents K.space) := by
  let _ : LocallyConnectedSpace K.space := locallyConnectedSpace_space K
  let _ : CompactSpace K.space := isCompact_iff_compactSpace.mp (isPolyhedron_space K).isCompact
  infer_instance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.finite_connectedComponents_space then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.finite_connectedComponents_space"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.finite_connectedComponents_space ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.finite_connectedComponents_space
end DifferentialGeometry.Topology.PiecewiseLinear
