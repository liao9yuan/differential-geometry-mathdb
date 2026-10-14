/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.Collar.Thickening
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.BicollarEmbedding
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.ExistsGeneralPositionSolidTorusRelative

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

private theorem isConnected_of_isPLTorus {S : Set E3} (hS : IsPLTorus S) : IsConnected S := by
  obtain ⟨-, ⟨e⟩⟩ := hS
  have hcircle : IsConnected (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) := by
    apply isConnected_sphere _ _ zero_le_one
    rw [← Module.finrank_eq_rank]
    norm_num
  let _ : ConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
    isConnected_iff_connectedSpace.mp hcircle
  let _ : ConnectedSpace S := e.symm.surjective.connectedSpace e.symm.continuous
  exact isConnected_iff_connectedSpace.mpr inferInstance

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isConnected_of_isPLTorus
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.isConnected_of_isPLTorus target :: scope.openDecls } }

private theorem isPolyhedralManifold_of_isPLTorus {S : Set E3} (hS : IsPLTorus S) :
    IsPolyhedralManifold (n := 3) 2 S := by
  classical
  obtain ⟨hpoly, ⟨e⟩⟩ := hS
  obtain ⟨K, hKfin, hKS⟩ := hpoly.exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  have hK := isCombinatorialManifold_two_of_homeomorph_sphere_prod K
    ((Homeomorph.setCongr hKS).trans e)
  let ec := chartAt E3 (0 : E3)
  have htarget : K.space ⊆ ec.target := by
    simp only [ec, chartAt_self_eq, OpenPartialHomeomorph.refl_target]
    exact _root_.Set.subset_univ _
  have h := isPolyhedralManifold_of_pieceIn
    (chartPieceOfComplex ec (chart_mem_atlas E3 (0 : E3)) K htarget) hK
  simpa only [ec, chartAt_self_eq, OpenPartialHomeomorph.refl_symm,
    OpenPartialHomeomorph.refl_apply, _root_.Set.image_id, hKS] using h

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPolyhedralManifold_of_isPLTorus
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.isPolyhedralManifold_of_isPLTorus target :: scope.openDecls } }

theorem IsCombinatorialSolidTorus.exists_thickening_fixed_on_compact {N A U : Set E3}
    (hN : IsCombinatorialSolidTorus N) (hA : IsCompact A) (hAN : A ⊆ interior N)
    (hU : IsOpen U) (hNU : N ⊆ U) :
    ∃ P : Set E3, P ⊆ U ∧ N ⊆ interior P ∧
      ∃ e : N ≃ₜ P, ∀ x : N, (x : E3) ∈ A → (e x : E3) = (x : E3) := by
  have hregular : closure (interior N) = N := by
    apply Subset.antisymm (closure_minimal interior_subset hN.isPolyhedron.isClosed)
    obtain ⟨-, n, -, C, -, hcover, hball, -⟩ := hN
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover.symm ▸ hx)
    have hsub : (C i).space ⊆ N := (_root_.Set.subset_iUnion (fun j => (C j).space) i).trans
      hcover.subset
    exact closure_mono (interior_mono hsub) ((hball i).closure_interior.symm ▸ hi)
  have hfront := hN.isPLTorus_frontier
  have hpoly := isPolyhedralManifold_of_isPLTorus hfront
  have hconn := isConnected_of_isPLTorus hfront
  exact (hpoly.isBicollared (hpoly.isTwoSided hconn)).exists_thickening_fixed_on_closed
    hregular hconn hfront.1.isCompact hA.isClosed hAN hU hNU

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialSolidTorus.exists_thickening_fixed_on_compact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialSolidTorus.exists_thickening_fixed_on_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialSolidTorus.exists_thickening_fixed_on_compact ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialSolidTorus.exists_thickening_fixed_on_compact

end DifferentialGeometry.Topology.PiecewiseLinear
