/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnBoundary
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.BallRegularClosed
import Submission.DifferentialGeometry.Topology.Manifold.EmbeddingLocalHomeomorph
import Submission.DifferentialGeometry.Topology.LocalDegree.ChartParityTransport

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set
open scoped _root_.Manifold

namespace DifferentialGeometry.Topology.PiecewiseLinear

open _root_.Submission.DifferentialGeometry.LocalDegree

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {M N : Type*} [TopologicalSpace M] [ChartedSpace E3 M]
  [TopologicalSpace N] [ChartedSpace E3 N]

theorem IsPLCellOn.isConnected_interior {C B : Set M} (hC : IsPLCellOn 3 C B) :
    IsConnected (interior C) := by
  obtain ⟨P, r, u, hr, hu, rfl, -⟩ := hC
  rw [← hu.image_interior]
  exact ((show IsPLBall 3 P from ⟨r, hr⟩).isConnected_interior_of_finrank
    (by simp)).image u (hu.continuousOn.mono interior_subset)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.isConnected_interior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.isConnected_interior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.isConnected_interior ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.isConnected_interior

theorem exists_relative_orientation_sign_of_cell
    {C B : Set M} (hC : IsPLCellOn 3 C B)
    {h f : M → N} (hh : ContinuousOn h C) (hhi : _root_.Set.InjOn h C)
    (hf : ContinuousOn f C) (hfi : _root_.Set.InjOn f C)
    {A : Set N} (hA : IsPreconnected A)
    (hHA : _root_.Set.MapsTo h (interior C) A) (hFA : _root_.Set.MapsTo f (interior C) A)
    (b : OpenPartialHomeomorph N E3) (hAb : A ⊆ b.source) :
    ∃ (H F : OpenPartialHomeomorph M N) (σ : ZMod 2),
      H.source = interior C ∧ F.source = interior C ∧
      H.target = h '' interior C ∧ F.target = f '' interior C ∧
      (∀ x, H x = h x) ∧ (∀ x, F x = f x) ∧
      ∀ (c : OpenPartialHomeomorph N E3), A ⊆ c.source →
        ∀ x (hxH : x ∈ H.source) (hxF : x ∈ F.source)
          (hxc : H x ∈ c.source) (hxfc : F x ∈ c.source),
          chartOrientationParity (H ≫ₕ c) (F ≫ₕ c) x ⟨hxH, hxc⟩ ⟨hxF, hxfc⟩ = σ := by
  have hconn := hC.isConnected_interior
  have : Nonempty M := ⟨hconn.nonempty.choose⟩
  obtain ⟨H, hHs, hHt, hH⟩ := exists_openPartialHomeomorph_of_continuousOn_injOn
    (E := E3) isOpen_interior (hh.mono interior_subset) (hhi.mono interior_subset)
  obtain ⟨F, hFs, hFt, hF⟩ := exists_openPartialHomeomorph_of_continuousOn_injOn
    (E := E3) isOpen_interior (hf.mono interior_subset) (hfi.mono interior_subset)
  have hHS : interior C ⊆ H.source := hHs ▸ Subset.rfl
  have hFS : interior C ⊆ F.source := hFs ▸ Subset.rfl
  have hHA' : _root_.Set.MapsTo H (interior C) A := by
    intro x hx
    rw [hH]
    exact hHA hx
  have hFA' : _root_.Set.MapsTo F (interior C) A := by
    intro x hx
    rw [hF]
    exact hFA hx
  obtain ⟨σ, hσ⟩ := exists_relative_chart_sign_of_connected_carrier
    H F hconn hHS hFS hA hHA' hFA' b hAb
  refine ⟨H, F, σ, hHs, hFs, hHt, hFt, hH, hF, ?_⟩
  intro c hAc x hxH hxF hxc hxfc
  have hx : x ∈ interior C := hHs ▸ hxH
  exact hσ c hAc x hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_relative_orientation_sign_of_cell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_relative_orientation_sign_of_cell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_relative_orientation_sign_of_cell ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_relative_orientation_sign_of_cell

end DifferentialGeometry.Topology.PiecewiseLinear
