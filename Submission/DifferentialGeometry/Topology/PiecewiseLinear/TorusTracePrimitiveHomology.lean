/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.Homology.InfiniteCyclicDegree
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.TorusTraceCircles
import Submission.DifferentialGeometry.Topology.Simplex.NormedBall

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology
open scoped _root_.ContinuousMap

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem carriesFirstHomologyOnto_trace_circle_of_isPreconnected
    {ι : Type*} [Finite ι] {T : Set E3} {J : ι → Set E3}
    (hT : IsCombinatorialSolidTorus T) (hJ : ∀ i, IsPLSphere 1 (J i))
    (hJT : ∀ i, J i ⊆ frontier T) (hdisj : Pairwise fun i j => Disjoint (J i) (J j))
    (hcarry : CarriesFirstHomologyOnto (⋃ i, J i) T)
    (i : ι) (hi : IsPreconnected (frontier T \ J i)) :
    CarriesFirstHomologyOnto (J i) T := by
  obtain ⟨k, hksep, hkcarry⟩ := exists_surjective_trace_circle hT hJ hJT hdisj hcarry
  by_cases hik : i = k
  · simpa only [hik] using hkcarry
  · have hΘT : id '' frontier T ⊆ T := by
      simpa only [_root_.Set.image_id] using hT.isPolyhedron.isClosed.frontier_subset
    have hkc : CarriesFirstHomologyOnto (id '' J k) T := by
      simpa only [_root_.Set.image_id] using hkcarry
    have hc := hT.isPLTorus_frontier.carriesFirstHomologyOnto_image_of_disjoint
      (hJ k) (hJT k) (hJ i) (hJT i) (hdisj hik) hksep hi
      continuous_id.continuousOn (fun _ _ _ _ heq => heq) hΘT hkc
    simpa only [_root_.Set.image_id] using hc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.carriesFirstHomologyOnto_trace_circle_of_isPreconnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.carriesFirstHomologyOnto_trace_circle_of_isPreconnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.carriesFirstHomologyOnto_trace_circle_of_isPreconnected ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.carriesFirstHomologyOnto_trace_circle_of_isPreconnected

theorem CarriesFirstHomologyOnto.inclusion_generator_eq_one_or_neg_one
    {Y : Type*} [TopologicalSpace Y] {J T : Set Y}
    (h : CarriesFirstHomologyOnto J T)
    (eJ : integralSingularHomology 1 J ≃ₗ[ℤ] ℤ)
    (eT : integralSingularHomology 1 T ≃ₗ[ℤ] ℤ) (hJT : J ⊆ T) :
    eT (integralSingularHomologyMap 1
        (⟨inclusion hJT, continuous_inclusion hJT⟩ : C(J, T)) (eJ.symm 1)) = 1 ∨
      eT (integralSingularHomologyMap 1
        (⟨inclusion hJT, continuous_inclusion hJT⟩ : C(J, T)) (eJ.symm 1)) = -1 :=
  integralSingularHomologyMap_generator_eq_one_or_neg_one_of_surjective 1 _ (h.2 hJT) eJ eT

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.CarriesFirstHomologyOnto.inclusion_generator_eq_one_or_neg_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.CarriesFirstHomologyOnto.inclusion_generator_eq_one_or_neg_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.CarriesFirstHomologyOnto.inclusion_generator_eq_one_or_neg_one ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.CarriesFirstHomologyOnto.inclusion_generator_eq_one_or_neg_one

theorem IsPLSphere.nonempty_integralSingularHomology_one_equiv_int
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {J : Set E} (hJ : IsPLSphere 1 J) :
    Nonempty (integralSingularHomology 1 J ≃ₗ[ℤ] ℤ) := by
  obtain ⟨f, hf⟩ := hJ
  let β : stdSimplexBoundary 2 ≃ₜ DifferentialGeometry.Simplex.boundary (Fin 3) :=
    { toFun := fun z => ⟨⟨z.1, z.2.1⟩, z.2.2⟩
      invFun := fun z => ⟨z.1.1, z.1.2, z.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
      continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _ }
  let e : J ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
    (hf.homeomorph.symm.trans β).trans
      (DifferentialGeometry.Simplex.stdSimplexNormedBoundarySphereHomeomorph
        (EuclideanSpace.equiv (Fin 2) ℝ).symm)
  exact ⟨(integralSingularHomologyHomotopyEquiv 1 e.toHomotopyEquiv).trans
    (integralSphereTopHomologyEquiv 0 (EuclideanSpace ℝ (Fin 2)) (by simp))⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere.nonempty_integralSingularHomology_one_equiv_int then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere.nonempty_integralSingularHomology_one_equiv_int"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere.nonempty_integralSingularHomology_one_equiv_int ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere.nonempty_integralSingularHomology_one_equiv_int

theorem IsTopologicalSolidTorus.nonempty_integralSingularHomology_one_equiv_int
    {Y : Type} [TopologicalSpace Y] {T : Set Y} (hT : IsTopologicalSolidTorus T) :
    Nonempty (integralSingularHomology 1 T ≃ₗ[ℤ] ℤ) := by
  obtain ⟨φ⟩ := hT
  let D := Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1
  let S := Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1
  let p : D := ⟨0, by simp [D]⟩
  let e : T ≃ₕ S := φ.toHomotopyEquiv.trans
    ((Homeomorph.prodComm D S).toHomotopyEquiv.trans
      (DifferentialGeometry.HomotopyEquiv.productConvex S (convex_closedBall _ _) p))
  exact ⟨(integralSingularHomologyHomotopyEquiv 1 e).trans
    (integralSphereTopHomologyEquiv 0 (EuclideanSpace ℝ (Fin 2)) (by simp))⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsTopologicalSolidTorus.nonempty_integralSingularHomology_one_equiv_int then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsTopologicalSolidTorus.nonempty_integralSingularHomology_one_equiv_int"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsTopologicalSolidTorus.nonempty_integralSingularHomology_one_equiv_int ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsTopologicalSolidTorus.nonempty_integralSingularHomology_one_equiv_int

theorem IsPLSphere.exists_primitive_homology_coordinates
    {J T : Set E3} (hJ : IsPLSphere 1 J) (hT : IsTopologicalSolidTorus T)
    (hcarry : CarriesFirstHomologyOnto J T) :
    ∃ (eJ : integralSingularHomology 1 J ≃ₗ[ℤ] ℤ)
      (eT : integralSingularHomology 1 T ≃ₗ[ℤ] ℤ),
      eT (integralSingularHomologyMap 1
          (⟨inclusion hcarry.1, continuous_inclusion hcarry.1⟩ : C(J, T)) (eJ.symm 1)) = 1 ∨
        eT (integralSingularHomologyMap 1
          (⟨inclusion hcarry.1, continuous_inclusion hcarry.1⟩ : C(J, T)) (eJ.symm 1)) = -1 := by
  obtain ⟨eJ⟩ := hJ.nonempty_integralSingularHomology_one_equiv_int
  obtain ⟨eT⟩ := hT.nonempty_integralSingularHomology_one_equiv_int
  exact ⟨eJ, eT, hcarry.inclusion_generator_eq_one_or_neg_one eJ eT hcarry.1⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere.exists_primitive_homology_coordinates then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere.exists_primitive_homology_coordinates"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere.exists_primitive_homology_coordinates ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere.exists_primitive_homology_coordinates

end DifferentialGeometry.Topology.PiecewiseLinear
