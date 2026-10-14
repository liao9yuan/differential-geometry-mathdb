/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.SurfaceComplement
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.EuclideanPolyhedralManifold

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPolyhedralManifold.not_isPreconnected_compl
    {S : Set (EuclideanSpace ℝ (Fin 3))} (hS : IsPolyhedralManifold (n := 3) 2 S)
    (hne : S.Nonempty) : ¬IsPreconnected Sᶜ := by
  obtain ⟨K, hfinite, hspace, hK⟩ := hS.exists_simplicialComplex
  let _ : Finite K.faces := hfinite.to_subtype
  rw [← hspace] at hne ⊢
  exact hK.not_isPreconnected_compl K (by simp) hne

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifold.not_isPreconnected_compl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifold.not_isPreconnected_compl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifold.not_isPreconnected_compl ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifold.not_isPreconnected_compl

theorem IsPolyhedralManifold.exists_connectedComponentIn_pair_compl
    {S : Set (EuclideanSpace ℝ (Fin 3))} (hS : IsPolyhedralManifold (n := 3) 2 S)
    (hconn : IsConnected S) :
    ∃ a ∈ Sᶜ, ∃ b ∈ Sᶜ,
      let A := connectedComponentIn Sᶜ a
      let B := connectedComponentIn Sᶜ b
      Disjoint A B ∧ A ∪ B = Sᶜ ∧ closure A ∪ closure B = _root_.Set.univ ∧
        closure A ∩ closure B = S ∧ frontier A = S ∧ frontier B = S := by
  obtain ⟨K, hfinite, hspace, hK⟩ := hS.exists_simplicialComplex
  let _ : Finite K.faces := hfinite.to_subtype
  rw [← hspace] at hconn ⊢
  exact hK.exists_connectedComponentIn_pair_compl K (by simp) hconn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifold.exists_connectedComponentIn_pair_compl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifold.exists_connectedComponentIn_pair_compl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifold.exists_connectedComponentIn_pair_compl ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifold.exists_connectedComponentIn_pair_compl

theorem IsPolyhedralManifold.isTwoSided
    {S : Set (EuclideanSpace ℝ (Fin 3))} (hS : IsPolyhedralManifold (n := 3) 2 S)
    (hconn : IsConnected S) : Topology.IsTwoSided S := by
  obtain ⟨K, hfinite, hspace, hK⟩ := hS.exists_simplicialComplex
  let _ : Finite K.faces := hfinite.to_subtype
  rw [← hspace] at hconn ⊢
  exact hK.isTwoSided K (by simp) hconn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifold.isTwoSided then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifold.isTwoSided"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifold.isTwoSided ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifold.isTwoSided

end DifferentialGeometry.Topology.PiecewiseLinear
