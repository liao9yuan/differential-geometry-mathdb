/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.LocallyFiniteCollar
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.StageTransport

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

section LocalModel

variable {n m : ℕ} {M N : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]

theorem isPLWithinAt_congr_of_isOpen_inter_eq {f : M → N} {K P O : Set M} {x : M}
    (hO : IsOpen O) (hx : x ∈ O) (hKP : O ∩ K = O ∩ P) :
    IsPLWithinAt n m f K x ↔ IsPLWithinAt n m f P x := by
  refine piecewiseAffineProperty_localInvariantProp.liftPropWithinAt_congr_set ?_
  filter_upwards [hO.mem_nhds hx] with z hz
  apply propext
  exact ⟨fun hzK => (hKP.subset ⟨hz, hzK⟩).2, fun hzP => (hKP.symm.subset ⟨hz, hzP⟩).2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPLWithinAt_congr_of_isOpen_inter_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPLWithinAt_congr_of_isOpen_inter_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPLWithinAt_congr_of_isOpen_inter_eq ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPLWithinAt_congr_of_isOpen_inter_eq

theorem isPLOn_of_forall_exists_isOpen_inter_eq {f : M → N} {K : Set M}
    (hloc : ∀ x ∈ K, ∃ O : Set M, IsOpen O ∧ x ∈ O ∧ ∃ P : Set M, O ∩ K = O ∩ P ∧
      IsPLWithinAt n m f P x) : IsPLOn n m f K := by
  intro x hx
  obtain ⟨O, hO, hxO, P, hOP, hf⟩ := hloc x hx
  exact (isPLWithinAt_congr_of_isOpen_inter_eq hO hxO hOP).mpr hf

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPLOn_of_forall_exists_isOpen_inter_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPLOn_of_forall_exists_isOpen_inter_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPLOn_of_forall_exists_isOpen_inter_eq ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPLOn_of_forall_exists_isOpen_inter_eq

end LocalModel

section Identity

variable {n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]

theorem PLPiece.isPLOn_id {Y : Set X} (T : PLPiece n X Y) : IsPLOn n n (id : X → X) Y := by
  classical
  have _ : Finite T.piece.complex.faces := T.piece.finite_faces.to_subtype
  have hid : IsPiecewiseAffineOn (id : EuclideanSpace ℝ (Fin T.ambientDim) →
      EuclideanSpace ℝ (Fin T.ambientDim)) T.piece.complex.space :=
    (isPolyhedron_space T.piece.complex).isPLHomeomorphOn_id.isPiecewiseAffineOn
  have hw : IsPLOn T.ambientDim n (T.piece.map ∘ id) T.piece.complex.space :=
    T.piece.isPLOn_comp hid (_root_.Set.mapsTo_id _)
  refine T.piece.isPLOn_of_eqOn_comp_invFunOn hw fun y hy => ?_
  exact (T.piece.bijOn.invOn_invFunOn.2 hy).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.PLPiece.isPLOn_id then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.PLPiece.isPLOn_id"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.PLPiece.isPLOn_id ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLPiece.isPLOn_id

theorem IsPolyhedralManifoldWithBoundary.isPLOn_id {m : ℕ} {P : Set X}
    (hP : IsPolyhedralManifoldWithBoundary (n := n) m P) : IsPLOn n n (id : X → X) P := by
  obtain ⟨T, -⟩ := hP
  exact T.isPLOn_id

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifoldWithBoundary.isPLOn_id then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifoldWithBoundary.isPLOn_id"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifoldWithBoundary.isPLOn_id ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifoldWithBoundary.isPLOn_id

end Identity

section LocallyFinite

variable {m : ℕ} {X : Type*} [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) X]

theorem IsLocallyFinitePolyhedralManifoldWithBoundary.isPLOn_id {K : Set X}
    (hK : IsLocallyFinitePolyhedralManifoldWithBoundary (n := m + 1) (m + 1) K) :
    IsPLOn (m + 1) (m + 1) (id : X → X) K := by
  refine isPLOn_of_forall_exists_isOpen_inter_eq fun x hx => ?_
  obtain ⟨O, hO, hxO, P, hP, -, hOP⟩ := hK.exists_isOpen_inter_eq hx
  exact ⟨O, hO, hxO, P, hOP, hP.isPLOn_id x (hOP.subset ⟨hxO, hx⟩).2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyFinitePolyhedralManifoldWithBoundary.isPLOn_id then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyFinitePolyhedralManifoldWithBoundary.isPLOn_id"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyFinitePolyhedralManifoldWithBoundary.isPLOn_id ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyFinitePolyhedralManifoldWithBoundary.isPLOn_id

end LocallyFinite

end DifferentialGeometry.Topology.PiecewiseLinear
