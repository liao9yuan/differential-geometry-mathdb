/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SphereTopHomology
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.BallHomotopy
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.ExistsGeneralPositionSolidTorusRelative
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.TorusSubsurfaceCarrier

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology
open scoped _root_.ContinuousMap

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsTopologicalSolidTorus.nontrivial_integralSingularHomology_one
    {Y : Type} [TopologicalSpace Y] {S : Set Y} (hS : IsTopologicalSolidTorus S) :
    Nontrivial (integralSingularHomology 1 S) := by
  obtain ⟨φ⟩ := hS
  let D := Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1
  let T := Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1
  let p : D := ⟨0, by simp [D]⟩
  let e : S ≃ₕ T := φ.toHomotopyEquiv.trans
    ((Homeomorph.prodComm D T).toHomotopyEquiv.trans
      (DifferentialGeometry.HomotopyEquiv.productConvex T (convex_closedBall _ _) p))
  let eH : integralSingularHomology 1 S ≃ₗ[ℤ] ℤ :=
    (integralSingularHomologyHomotopyEquiv 1 e).trans
      (integralSphereTopHomologyEquiv 0 (EuclideanSpace ℝ (Fin 2)) (by simp))
  exact ⟨⟨eH.symm 0, eH.symm 1, fun heq => zero_ne_one (eH.symm.injective heq)⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsTopologicalSolidTorus.nontrivial_integralSingularHomology_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsTopologicalSolidTorus.nontrivial_integralSingularHomology_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsTopologicalSolidTorus.nontrivial_integralSingularHomology_one ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsTopologicalSolidTorus.nontrivial_integralSingularHomology_one

theorem exists_surjective_trace_circle {ι : Type*} [Finite ι] {T : Set E3}
    {J : ι → Set E3} (hT : IsCombinatorialSolidTorus T) (hJ : ∀ i, IsPLSphere 1 (J i))
    (hJT : ∀ i, J i ⊆ frontier T) (hdisj : Pairwise fun i j => Disjoint (J i) (J j))
    (hcarry : CarriesFirstHomologyOnto (⋃ i, J i) T) :
    ∃ i, IsPreconnected (frontier T \ J i) ∧ CarriesFirstHomologyOnto (J i) T := by
  have hΘ : IsPLTorus (frontier T) := hT.isPLTorus_frontier
  have hΘT : id '' frontier T ⊆ T := by
    simpa only [_root_.Set.image_id] using hT.isPolyhedron.isClosed.frontier_subset
  have hc : CarriesFirstHomologyOnto (id '' ⋃ i, J i) T := by
    simpa only [_root_.Set.image_id] using hcarry
  rcases hΘ.carriesFirstHomologyOnto_or_subsingleton_of_iUnion hJ hJT hdisj
      continuous_id.continuousOn (fun _ _ _ _ heq => heq) hΘT hc with hsome | htriv
  · simpa only [_root_.Set.image_id] using hsome
  · obtain ⟨a, b, hab⟩ := hT.1.nontrivial_integralSingularHomology_one.exists_pair_ne
    let _ := htriv
    exact (hab (Subsingleton.elim a b)).elim

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_surjective_trace_circle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_surjective_trace_circle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_surjective_trace_circle ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_surjective_trace_circle

theorem trace_circle_separates_of_zero_homology_image {ι : Type*} [Finite ι] {T : Set E3}
    {J : ι → Set E3} (hT : IsCombinatorialSolidTorus T) (hJ : ∀ i, IsPLSphere 1 (J i))
    (hJT : ∀ i, J i ⊆ frontier T) (hdisj : Pairwise fun i j => Disjoint (J i) (J j))
    (hcarry : CarriesFirstHomologyOnto (⋃ i, J i) T) (i : ι) (hsub : J i ⊆ T)
    (hzero : integralSingularHomologyMap 1
      (⟨inclusion hsub, continuous_inclusion hsub⟩ : C(J i, T)) = 0) :
    ¬ IsPreconnected (frontier T \ J i) := by
  intro hsep
  obtain ⟨k, hksep, hkcarry⟩ := exists_surjective_trace_circle hT hJ hJT hdisj hcarry
  have hicarry : CarriesFirstHomologyOnto (J i) T := by
    by_cases hik : i = k
    · simpa only [hik] using hkcarry
    · have hΘT : id '' frontier T ⊆ T := by
        simpa only [_root_.Set.image_id] using hT.isPolyhedron.isClosed.frontier_subset
      have hkc : CarriesFirstHomologyOnto (id '' J k) T := by
        simpa only [_root_.Set.image_id] using hkcarry
      have hc := hT.isPLTorus_frontier.carriesFirstHomologyOnto_image_of_disjoint
        (hJ k) (hJT k) (hJ i) (hJT i) (hdisj hik) hksep hsep
        continuous_id.continuousOn (fun _ _ _ _ heq => heq) hΘT hkc
      simpa only [_root_.Set.image_id] using hc
  let _ := hT.1.nontrivial_integralSingularHomology_one
  obtain ⟨z, hz⟩ := exists_ne (0 : integralSingularHomology 1 T)
  obtain ⟨x, hx⟩ := hicarry.2 hsub z
  rw [hzero, LinearMap.zero_apply] at hx
  exact hz hx.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.trace_circle_separates_of_zero_homology_image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.trace_circle_separates_of_zero_homology_image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.trace_circle_separates_of_zero_homology_image ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.trace_circle_separates_of_zero_homology_image

theorem exists_disk_of_zero_trace_homology_image {ι : Type*} [Finite ι] {T : Set E3}
    {J : ι → Set E3} (hT : IsCombinatorialSolidTorus T) (hJ : ∀ i, IsPLSphere 1 (J i))
    (hJT : ∀ i, J i ⊆ frontier T) (hdisj : Pairwise fun i j => Disjoint (J i) (J j))
    (hcarry : CarriesFirstHomologyOnto (⋃ i, J i) T) (i : ι) (hsub : J i ⊆ T)
    (hzero : integralSingularHomologyMap 1
      (⟨inclusion hsub, continuous_inclusion hsub⟩ : C(J i, T)) = 0) :
    ∃ (D : Set E3) (r : (Fin 3 → ℝ) → E3),
      IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) D ∧ D ⊆ frontier T ∧
        J i = r '' stdSimplexBoundary 2 :=
  hT.isPLTorus_frontier.exists_isPLHomeomorphOn_disk_of_not_isPreconnected_sdiff
    (hJ i) (hJT i)
    (trace_circle_separates_of_zero_homology_image hT hJ hJT hdisj hcarry i hsub hzero)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_disk_of_zero_trace_homology_image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_disk_of_zero_trace_homology_image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_disk_of_zero_trace_homology_image ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_disk_of_zero_trace_homology_image

end DifferentialGeometry.Topology.PiecewiseLinear
