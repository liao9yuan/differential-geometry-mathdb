/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.TorusDisjointCircleFilling
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLModelTopology

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology
open scoped _root_.ContinuousMap

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {Y : Type*} [TopologicalSpace Y] [T2Space Y]
  {u : E3 → Y} {T : Set Y} [Nontrivial (integralSingularHomology 1 T)]
  {ι : Type*} [Finite ι] {Θ : Set E3} {J : ι → Set E3}

theorem IsPLTorus.exists_surjective_circle_image (hΘ : IsPLTorus Θ)
    (hJ : ∀ i, IsPLSphere 1 (J i)) (hJΘ : ∀ i, J i ⊆ Θ)
    (hdis : Pairwise fun i j => Disjoint (J i) (J j))
    (hu : ContinuousOn u Θ) (hui : _root_.Set.InjOn u Θ) (hΘT : u '' Θ ⊆ T)
    (hcarry : CarriesFirstHomologyOnto (u '' ⋃ i, J i) T) :
    ∃ i, IsPreconnected (Θ \ J i) ∧ CarriesFirstHomologyOnto (u '' J i) T := by
  rcases hΘ.carriesFirstHomologyOnto_or_subsingleton_of_iUnion hJ hJΘ hdis hu hui hΘT
      hcarry with hsome | htriv
  · exact hsome
  · obtain ⟨a, b, hab⟩ := exists_pair_ne (integralSingularHomology 1 T)
    exact (hab (@Subsingleton.elim _ htriv a b)).elim

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLTorus.exists_surjective_circle_image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLTorus.exists_surjective_circle_image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLTorus.exists_surjective_circle_image ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLTorus.exists_surjective_circle_image

theorem IsPLTorus.circle_separates_of_zero_image (hΘ : IsPLTorus Θ)
    (hJ : ∀ i, IsPLSphere 1 (J i)) (hJΘ : ∀ i, J i ⊆ Θ)
    (hdis : Pairwise fun i j => Disjoint (J i) (J j))
    (hu : ContinuousOn u Θ) (hui : _root_.Set.InjOn u Θ) (hΘT : u '' Θ ⊆ T)
    (hcarry : CarriesFirstHomologyOnto (u '' ⋃ i, J i) T) (i : ι)
    (hiT : u '' J i ⊆ T)
    (hzero : integralSingularHomologyMap 1
      (⟨inclusion hiT, continuous_inclusion hiT⟩ : C(u '' J i, T)) = 0) :
    ¬ IsPreconnected (Θ \ J i) := by
  intro hsep
  obtain ⟨k, hksep, hkcarry⟩ :=
    hΘ.exists_surjective_circle_image hJ hJΘ hdis hu hui hΘT hcarry
  have hicarry : CarriesFirstHomologyOnto (u '' J i) T := by
    by_cases hik : i = k
    · simpa only [hik] using hkcarry
    · exact hΘ.carriesFirstHomologyOnto_image_of_disjoint
        (hJ k) (hJΘ k) (hJ i) (hJΘ i) (hdis hik) hksep hsep hu hui hΘT hkcarry
  obtain ⟨z, hz⟩ := exists_ne (0 : integralSingularHomology 1 T)
  obtain ⟨a, ha⟩ := hicarry.2 hiT z
  rw [hzero, LinearMap.zero_apply] at ha
  exact hz ha.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLTorus.circle_separates_of_zero_image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLTorus.circle_separates_of_zero_image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLTorus.circle_separates_of_zero_image ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLTorus.circle_separates_of_zero_image

theorem IsPLTorus.exists_disk_of_nullhomotopic_image_circle_disjoint_carrier
    (hΘ : IsPLTorus Θ) (hJ : ∀ i, IsPLSphere 1 (J i)) (hJΘ : ∀ i, J i ⊆ Θ)
    (hdis : Pairwise fun i j => Disjoint (J i) (J j))
    (hu : ContinuousOn u Θ) (hui : _root_.Set.InjOn u Θ) (hΘT : u '' Θ ⊆ T)
    (hcarry : CarriesFirstHomologyOnto (u '' ⋃ i, J i) T)
    {C : Set E3} (hC : IsPLSphere 1 C) (hCΘ : C ⊆ Θ)
    (hCJ : ∀ i, Disjoint C (J i))
    (hnull : (⟨inclusion ((_root_.Set.image_mono hCΘ).trans hΘT), continuous_inclusion _⟩ :
      C(u '' C, T)).Nullhomotopic) :
    ∃ (D : Set E3) (q : (Fin 3 → ℝ) → E3),
      IsPLHomeomorphOn q (stdSimplex ℝ (Fin 3)) D ∧ D ⊆ Θ ∧
        C = q '' stdSimplexBoundary 2 := by
  let F : Option ι → Set E3 := fun i => i.elim C J
  have hF : ∀ i, IsPLSphere 1 (F i) := by
    intro i
    cases i with
    | none => exact hC
    | some i => exact hJ i
  have hFΘ : ∀ i, F i ⊆ Θ := by
    intro i
    cases i with
    | none => exact hCΘ
    | some i => exact hJΘ i
  have hFd : Pairwise fun i j => Disjoint (F i) (F j) := by
    intro i j hij
    cases i with
    | none =>
      cases j with
      | none => exact (hij rfl).elim
      | some j => exact hCJ j
    | some i =>
      cases j with
      | none => exact (hCJ i).symm
      | some j => exact hdis (fun h => hij (congrArg Option.some h))
  have hJF : (⋃ i, J i) ⊆ ⋃ i, F i := by
    intro x hx
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨some i, hxi⟩
  have hFT : u '' (⋃ i, F i) ⊆ T :=
    (_root_.Set.image_mono (_root_.Set.iUnion_subset hFΘ)).trans hΘT
  have hzero := integralSingularHomologyMap_nullhomotopic 1 one_ne_zero hnull
  apply hΘ.exists_isPLHomeomorphOn_disk_of_not_isPreconnected_sdiff hC hCΘ
  exact hΘ.circle_separates_of_zero_image hF hFΘ hFd hu hui hΘT
    (hcarry.mono (_root_.Set.image_mono hJF) hFT) _root_.Option.none ((_root_.Set.image_mono hCΘ).trans hΘT) hzero

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLTorus.exists_disk_of_nullhomotopic_image_circle_disjoint_carrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLTorus.exists_disk_of_nullhomotopic_image_circle_disjoint_carrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLTorus.exists_disk_of_nullhomotopic_image_circle_disjoint_carrier ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLTorus.exists_disk_of_nullhomotopic_image_circle_disjoint_carrier

end DifferentialGeometry.Topology.PiecewiseLinear
