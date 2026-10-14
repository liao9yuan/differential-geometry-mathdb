/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.BallHomotopy
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.ExistsGeneralPositionSolidTorusRelative
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLModelCellRestriction
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.TopologicalSolidTorusHomology

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

noncomputable def IsPLHomeomorphInto.compactModelHomeomorph
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E3 M]
    {u : E3 → M} {P : Set E3} (hu : IsPLHomeomorphInto 3 u P) (hP : IsCompact P) :
    P ≃ₜ u '' P := by
  let _ : CompactSpace P := isCompact_iff_compactSpace.mp hP
  have he : _root_.Topology.IsClosedEmbedding (fun x : P => u x) :=
    hu.continuousOn.domRestrict.isClosedEmbedding
      (fun x y hxy => Subtype.ext (hu.injOn x.2 y.2 hxy))
  exact he.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr (by
    change _root_.Set.range (u ∘ ((↑) : P → E3)) = u '' P
    rw [_root_.Set.range_comp, Subtype.range_coe]))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphInto.compactModelHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphInto.compactModelHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphInto.compactModelHomeomorph ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphInto.compactModelHomeomorph

theorem IsPLCellOn.contractibleSpace
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E3 M]
    {d : ℕ} {A B : Set M} (hA : IsPLCellOn d A B) : ContractibleSpace A := by
  obtain ⟨P, r, u, hr, hu, rfl, -⟩ := hA
  have hP : IsPLBall d P := ⟨r, hr⟩
  let _ := hP.contractibleSpace
  exact (hu.compactModelHomeomorph hP.isPolyhedron.isCompact).symm.contractibleSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.contractibleSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.contractibleSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.contractibleSpace ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.contractibleSpace

theorem IsPLCellOn.nullhomotopic_inclusion
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E3 M]
    {d : ℕ} {D B A T : Set M} (hD : IsPLCellOn d D B)
    (hAD : A ⊆ D) (hDT : D ⊆ T) :
    (⟨Set.inclusion (hAD.trans hDT), continuous_inclusion _⟩ : C(A, T)).Nullhomotopic := by
  let _ := hD.contractibleSpace
  let i : C(A, D) := ⟨Set.inclusion hAD, continuous_inclusion hAD⟩
  let j : C(D, T) := ⟨Set.inclusion hDT, continuous_inclusion hDT⟩
  exact ((id_nullhomotopic D).comp_left i).comp_right j

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.nullhomotopic_inclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.nullhomotopic_inclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.nullhomotopic_inclusion ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.nullhomotopic_inclusion

theorem IsCombinatorialSolidTorus.isTopologicalSolidTorus_image
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E3 M]
    {u : E3 → M} {P : Set E3} (hP : IsCombinatorialSolidTorus P)
    (hu : IsPLHomeomorphInto 3 u P) : IsTopologicalSolidTorus (u '' P) :=
  ⟨(hu.compactModelHomeomorph hP.isPolyhedron.isCompact).symm.trans (Classical.choice hP.1)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialSolidTorus.isTopologicalSolidTorus_image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialSolidTorus.isTopologicalSolidTorus_image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialSolidTorus.isTopologicalSolidTorus_image ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialSolidTorus.isTopologicalSolidTorus_image

theorem IsPLCellOn.image_of_subset
    {M N : Type*} [TopologicalSpace M] [ChartedSpace E3 M]
    [TopologicalSpace N] [T2Space N] [ChartedSpace E3 N]
    {d : ℕ} {S B A : Set M} {f : M → N} (hS : IsPLCellOn d S B)
    (hf : IsPLHomeomorphInto 3 f A) (hSA : S ⊆ A) :
    IsPLCellOn d (f '' S) (f '' B) := by
  obtain ⟨P, r, u, hr, hu, rfl, rfl⟩ := hS
  have hmap : _root_.Set.MapsTo u P A := fun x hx => hSA ⟨x, hx, rfl⟩
  have hfu : IsPLOn 3 3 (f ∘ u) P := IsPLOn.comp_of_mapsTo hf.isPLOn hu.isPLOn hmap
  have hinj : _root_.Set.InjOn (f ∘ u) P := hf.injOn.comp hu.injOn hmap
  have hP : IsPLBall d P := ⟨r, hr⟩
  exact ⟨P, r, f ∘ u, hr,
    hfu.isPLHomeomorphInto_of_isCompact hP.isPolyhedron.isCompact hinj,
    (_root_.Set.image_comp f u P).symm, (_root_.Set.image_comp f u (r '' stdSimplexBoundary d)).symm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.image_of_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.image_of_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.image_of_subset ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.image_of_subset

end DifferentialGeometry.Topology.PiecewiseLinear
