/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.NormalCell
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.OneManifoldClassification
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PieceTransition
import Submission.DifferentialGeometry.Topology.SimplicialComplex.ConnectedSpace
import Submission.DifferentialGeometry.Topology.SimplicialComplex.GeometricBoundaryPair

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

namespace NormalSingularSetTriangulation

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D : SingularTwoCell M} {BdM : Set M}

open _root_.Classical in
private noncomputable def boundaryComplexModel
    (T : NormalSingularSetTriangulation D BdM) :=
  DifferentialGeometry.Topology.PiecewiseLinear.boundaryComplex 1 T.complex

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.boundaryComplexModel
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.boundaryComplexModel target :: scope.openDecls } }

private noncomputable def classicalBoundaryComplexModel
    (T : NormalSingularSetTriangulation D BdM) :=
  @DifferentialGeometry.Topology.PiecewiseLinear.boundaryComplex
    (EuclideanSpace ℝ (Fin T.piece.ambientDim)) _ _ (Classical.decEq _) 1 T.complex

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.classicalBoundaryComplexModel
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.classicalBoundaryComplexModel target :: scope.openDecls } }

private theorem boundaryComplexModel_eq_classicalBoundaryComplexModel
    (T : NormalSingularSetTriangulation D BdM) :
    T.boundaryComplexModel = T.classicalBoundaryComplexModel := by
  unfold boundaryComplexModel classicalBoundaryComplexModel
  exact congrArg
    (fun d : DecidableEq (EuclideanSpace ℝ (Fin T.piece.ambientDim)) =>
      @DifferentialGeometry.Topology.PiecewiseLinear.boundaryComplex
        (EuclideanSpace ℝ (Fin T.piece.ambientDim)) _ _ d 1 T.complex)
    (Subsingleton.elim _ _)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.boundaryComplexModel_eq_classicalBoundaryComplexModel
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.boundaryComplexModel_eq_classicalBoundaryComplexModel target :: scope.openDecls } }

open _root_.Classical in
private theorem map_boundaryComplexModel (T : NormalSingularSetTriangulation D BdM) :
    T.piece.piece.map '' T.boundaryComplexModel.space =
      doublePointSet D D.domain ∩ BdM :=
  T.map_boundary

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.map_boundaryComplexModel
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.map_boundaryComplexModel target :: scope.openDecls } }

def branchVertices (T : NormalSingularSetTriangulation D BdM) (c : T.Branch) :
    Set (EuclideanSpace ℝ (Fin T.piece.ambientDim)) :=
  ((↑) : T.complex.vertices → EuclideanSpace ℝ (Fin T.piece.ambientDim)) '' c.supp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchVertices then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchVertices"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchVertices ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchVertices

def branchComplex (T : NormalSingularSetTriangulation D BdM) (c : T.Branch) :
    Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin T.piece.ambientDim)) where
  faces := {s ∈ T.complex.faces | (s : Set _) ⊆ T.branchVertices c}
  isRelLowerSet_faces := by
    rintro s ⟨hs, hsc⟩
    refine ⟨T.complex.nonempty_of_mem_faces hs,
      fun t hts ht => ⟨T.complex.down_closed hs hts ht, ?_⟩⟩
    exact (Finset.coe_subset.mpr hts).trans hsc
  indep hs := T.complex.indep hs.1
  inter_subset_convexHull hs ht := T.complex.inter_subset_convexHull hs.1 ht.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchComplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchComplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchComplex ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchComplex

theorem mem_branchComplex_faces_iff
    (T : NormalSingularSetTriangulation D BdM) (c : T.Branch) {s : Finset _} :
    s ∈ (T.branchComplex c).faces ↔
      s ∈ T.complex.faces ∧ (s : Set _) ⊆ T.branchVertices c :=
  Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.mem_branchComplex_faces_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.mem_branchComplex_faces_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.mem_branchComplex_faces_iff ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.mem_branchComplex_faces_iff

theorem branchComplex_faces_subset
    (T : NormalSingularSetTriangulation D BdM) (c : T.Branch) :
    (T.branchComplex c).faces ⊆ T.complex.faces :=
  fun _ hs => hs.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchComplex_faces_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchComplex_faces_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchComplex_faces_subset ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchComplex_faces_subset

theorem branchComplex_faces_finite
    (T : NormalSingularSetTriangulation D BdM) (c : T.Branch) :
    (T.branchComplex c).faces.Finite :=
  T.finite_faces.subset (T.branchComplex_faces_subset c)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchComplex_faces_finite then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchComplex_faces_finite"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchComplex_faces_finite ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchComplex_faces_finite

def branchVertex (T : NormalSingularSetTriangulation D BdM) (c : T.Branch)
    (v : c.supp) : (T.branchComplex c).vertices := by
  refine ⟨v.1, v.1.2, ?_⟩
  intro x hx
  have hxv : x = (v.1 : EuclideanSpace ℝ (Fin T.piece.ambientDim)) := by simpa using hx
  subst x
  exact ⟨v.1, v.2, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchVertex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchVertex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchVertex ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchVertex

theorem branchVertex_injective
    (T : NormalSingularSetTriangulation D BdM) (c : T.Branch) :
    Function.Injective (T.branchVertex c) := by
  intro u v huv
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg
    (fun z : (T.branchComplex c).vertices =>
      (z : EuclideanSpace ℝ (Fin T.piece.ambientDim))) huv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchVertex_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchVertex_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchVertex_injective ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchVertex_injective

theorem branchVertex_surjective
    (T : NormalSingularSetTriangulation D BdM) (c : T.Branch) :
    Function.Surjective (T.branchVertex c) := by
  intro v
  have hv : (v : EuclideanSpace ℝ (Fin T.piece.ambientDim)) ∈ T.branchVertices c :=
    v.2.2 (by simp)
  obtain ⟨w, hwc, hwv⟩ := hv
  refine ⟨⟨w, hwc⟩, ?_⟩
  apply Subtype.ext
  exact hwv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchVertex_surjective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchVertex_surjective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchVertex_surjective ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchVertex_surjective

noncomputable def branchVertexEquiv
    (T : NormalSingularSetTriangulation D BdM) (c : T.Branch) :
    c.supp ≃ (T.branchComplex c).vertices :=
  Equiv.ofBijective (T.branchVertex c) ⟨T.branchVertex_injective c, T.branchVertex_surjective c⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchVertexEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchVertexEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchVertexEquiv ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchVertexEquiv

@[simp]
theorem branchVertexEquiv_apply
    (T : NormalSingularSetTriangulation D BdM) (c : T.Branch) (v : c.supp) :
    T.branchVertexEquiv c v = T.branchVertex c v :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchVertexEquiv_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchVertexEquiv_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchVertexEquiv_apply ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchVertexEquiv_apply

noncomputable def connectedComponentNeighborEquiv
    (T : NormalSingularSetTriangulation D BdM) (c : T.Branch) (v : c.supp) :
    c.toSimpleGraph.neighborSet v ≃
      (SimplicialComplex.edgeGraph T.complex).neighborSet v.1 where
  toFun w := ⟨w.1.1, w.2⟩
  invFun w :=
    ⟨⟨w.1, c.mem_supp_of_adj_mem_supp v.2 w.2⟩, w.2⟩
  left_inv w := Subtype.ext (Subtype.ext (rfl : w.1.1 = w.1.1))
  right_inv w := Subtype.ext (rfl : w.1 = w.1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.connectedComponentNeighborEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.connectedComponentNeighborEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.connectedComponentNeighborEquiv ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.connectedComponentNeighborEquiv

open _root_.Classical in
noncomputable def branchEdgeGraphIso
    (T : NormalSingularSetTriangulation D BdM) (c : T.Branch) :
    c.toSimpleGraph ≃g SimplicialComplex.edgeGraph (T.branchComplex c) where
  toEquiv := T.branchVertexEquiv c
  map_rel_iff' := by
    intro u v
    change (SimplicialComplex.edgeGraph (T.branchComplex c)).Adj
        (T.branchVertex c u) (T.branchVertex c v) ↔ c.toSimpleGraph.Adj u v
    rw [c.toSimpleGraph_adj u.2 v.2]
    constructor
    · intro huv
      refine ⟨?_, huv.2.1⟩
      intro h
      apply huv.1
      apply Subtype.ext
      exact congrArg
        (fun z : T.complex.vertices =>
          (z : EuclideanSpace ℝ (Fin T.piece.ambientDim))) h
    · intro huv
      refine ⟨?_, ⟨huv.2, ?_⟩⟩
      · intro h
        apply huv.1
        apply Subtype.ext
        exact congrArg
          (fun z : (T.branchComplex c).vertices =>
            (z : EuclideanSpace ℝ (Fin T.piece.ambientDim))) h
      · intro x hx
        simp only [Finset.coe_pair, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff] at hx
        rcases hx with hx | hx
        · exact ⟨u.1, u.2, hx.symm⟩
        · exact ⟨v.1, v.2, hx.symm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchEdgeGraphIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchEdgeGraphIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchEdgeGraphIso ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchEdgeGraphIso

theorem edgeGraph_branchComplex_connected
    (T : NormalSingularSetTriangulation D BdM) (c : T.Branch) :
    (SimplicialComplex.edgeGraph (T.branchComplex c)).Connected :=
  (T.branchEdgeGraphIso c).connected_iff.mp c.connected_toSimpleGraph

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.edgeGraph_branchComplex_connected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.edgeGraph_branchComplex_connected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.edgeGraph_branchComplex_connected ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.edgeGraph_branchComplex_connected

open _root_.Classical in
theorem branchEdgeGraph_neighborSet_ncard
    (T : NormalSingularSetTriangulation D BdM) (c : T.Branch) (v : c.supp) :
    ((SimplicialComplex.edgeGraph (T.branchComplex c)).neighborSet (T.branchVertex c v)).ncard =
      ((SimplicialComplex.edgeGraph T.complex).neighborSet v.1).ncard := by
  calc
    ((SimplicialComplex.edgeGraph (T.branchComplex c)).neighborSet
        (T.branchVertex c v)).ncard =
        (c.toSimpleGraph.neighborSet v).ncard :=
      (Set.ncard_congr' ((T.branchEdgeGraphIso c).mapNeighborSet v)).symm
    _ = ((SimplicialComplex.edgeGraph T.complex).neighborSet v.1).ncard :=
      Set.ncard_congr' (T.connectedComponentNeighborEquiv c v)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchEdgeGraph_neighborSet_ncard then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchEdgeGraph_neighborSet_ncard"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchEdgeGraph_neighborSet_ncard ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchEdgeGraph_neighborSet_ncard

open _root_.Classical in
theorem branchComplex_isManifoldWithBoundary
    (T : NormalSingularSetTriangulation D BdM) (c : T.Branch) :
    IsCombinatorialManifoldWithBoundary 1 (T.branchComplex c) := by
  let _ : Finite T.complex.faces := T.finite_faces.to_subtype
  let _ : Finite (T.branchComplex c).faces := (T.branchComplex_faces_finite c).to_subtype
  apply (isCombinatorialManifoldWithBoundary_one_iff (T.branchComplex c)).mpr
  refine ⟨fun s hs => T.isManifoldWithBoundary.card_le T.complex hs.1, ?_⟩
  intro x hx
  let v : (T.branchComplex c).vertices := ⟨x, hx⟩
  let w : c.supp := (T.branchVertexEquiv c).symm v
  have hvw : T.branchVertex c w = v := (T.branchVertexEquiv c).apply_symm_apply v
  have hdegree := T.neighborSet_ncard_eq_one_or_two w.1
  have htransfer :
      ((SimplicialComplex.edgeGraph (T.branchComplex c)).neighborSet v).ncard =
        ((SimplicialComplex.edgeGraph T.complex).neighborSet w.1).ncard := by
    rw [← hvw]
    exact T.branchEdgeGraph_neighborSet_ncard c w
  rw [← htransfer] at hdegree
  rw [SimplicialComplex.ncard_neighborSet_edgeGraph] at hdegree
  exact hdegree.imp Set.ncard_eq_one.mp Set.ncard_eq_two.mp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchComplex_isManifoldWithBoundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchComplex_isManifoldWithBoundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchComplex_isManifoldWithBoundary ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchComplex_isManifoldWithBoundary

open _root_.Classical in
theorem branchComplex_isManifold
    (T : NormalSingularSetTriangulation D BdM) {c : T.Branch}
    (hc : ¬T.IsBoundaryBranch c) :
    IsCombinatorialManifold 1 (T.branchComplex c) := by
  let _ : Finite T.complex.faces := T.finite_faces.to_subtype
  let _ : Finite (T.branchComplex c).faces := (T.branchComplex_faces_finite c).to_subtype
  apply (isCombinatorialManifold_one_iff (T.branchComplex c)).mpr
  refine ⟨fun s hs => T.isManifoldWithBoundary.card_le T.complex hs.1, ?_⟩
  intro x hx
  let v : (T.branchComplex c).vertices := ⟨x, hx⟩
  let w : c.supp := (T.branchVertexEquiv c).symm v
  have hvw : T.branchVertex c w = v := (T.branchVertexEquiv c).apply_symm_apply v
  have hdegree := T.neighborSet_ncard_eq_two_of_not_isBoundaryBranch hc w.2
  have htransfer :
      ((SimplicialComplex.edgeGraph (T.branchComplex c)).neighborSet v).ncard =
        ((SimplicialComplex.edgeGraph T.complex).neighborSet w.1).ncard := by
    rw [← hvw]
    exact T.branchEdgeGraph_neighborSet_ncard c w
  rw [← htransfer, SimplicialComplex.ncard_neighborSet_edgeGraph] at hdegree
  exact Set.ncard_eq_two.mp hdegree

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchComplex_isManifold then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchComplex_isManifold"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchComplex_isManifold ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchComplex_isManifold

theorem branchComplex_space_isConnected
    (T : NormalSingularSetTriangulation D BdM) (c : T.Branch) :
    IsConnected (T.branchComplex c).space :=
  isConnected_space_of_edgeGraph_connected (T.branchComplex c)
    (T.edgeGraph_branchComplex_connected c)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchComplex_space_isConnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchComplex_space_isConnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchComplex_space_isConnected ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchComplex_space_isConnected

open _root_.Classical in
theorem branchComplex_isPLSphere
    (T : NormalSingularSetTriangulation D BdM) {c : T.Branch}
    (hc : ¬T.IsBoundaryBranch c) :
    IsPLSphere 1 (T.branchComplex c).space := by
  let _ : Finite (T.branchComplex c).faces := (T.branchComplex_faces_finite c).to_subtype
  exact isPLSphere_one_of_edgeGraph_connected (T.branchComplex c)
    (T.branchComplex_isManifold hc) (T.edgeGraph_branchComplex_connected c)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchComplex_isPLSphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchComplex_isPLSphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchComplex_isPLSphere ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchComplex_isPLSphere

open _root_.Classical in
theorem branchComplex_isPLBall
    (T : NormalSingularSetTriangulation D BdM) {c : T.Branch}
    (hc : T.IsBoundaryBranch c) :
    IsPLBall 1 (T.branchComplex c).space := by
  let _ : Finite (T.branchComplex c).faces := (T.branchComplex_faces_finite c).to_subtype
  apply isPLBall_one_of_edgeGraph_connected_of_exists_degree_one (T.branchComplex c)
    (T.branchComplex_isManifoldWithBoundary c) (T.edgeGraph_branchComplex_connected c)
  obtain ⟨v, hvc, hdegree⟩ := T.exists_degree_one_vertex_of_isBoundaryBranch hc
  let w : c.supp := ⟨v, hvc⟩
  refine ⟨T.branchVertex c w, ?_⟩
  rw [T.branchEdgeGraph_neighborSet_ncard c w]
  exact hdegree

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchComplex_isPLBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchComplex_isPLBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchComplex_isPLBall ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchComplex_isPLBall

open _root_.Classical in
theorem branchComplex_space_isPolyhedron
    (T : NormalSingularSetTriangulation D BdM) (c : T.Branch) :
    IsPolyhedron (T.branchComplex c).space := by
  let _ : Finite (T.branchComplex c).faces := (T.branchComplex_faces_finite c).to_subtype
  exact isPolyhedron_space (T.branchComplex c)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchComplex_space_isPolyhedron then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchComplex_space_isPolyhedron"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchComplex_space_isPolyhedron ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchComplex_space_isPolyhedron

def branchCarrier (T : NormalSingularSetTriangulation D BdM) (c : T.Branch) : Set M :=
  T.piece.piece.map '' (T.branchComplex c).space

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchCarrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchCarrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchCarrier ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchCarrier

open _root_.Classical in
noncomputable def branchPieceIn
    (T : NormalSingularSetTriangulation D BdM) (c : T.Branch) :
    PLPieceIn (EuclideanSpace ℝ (Fin T.piece.ambientDim)) 3 M (T.branchCarrier c) :=
  T.piece.piece.restrict (T.branchComplex c)
    ((T.branchComplex_faces_subset c).trans T.faces_subset)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchPieceIn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchPieceIn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchPieceIn ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchPieceIn

@[simp]
theorem branchPieceIn_complex
    (T : NormalSingularSetTriangulation D BdM) (c : T.Branch) :
    (T.branchPieceIn c).complex = T.branchComplex c :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchPieceIn_complex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchPieceIn_complex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchPieceIn_complex ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchPieceIn_complex

@[simp]
theorem branchPieceIn_map
    (T : NormalSingularSetTriangulation D BdM) (c : T.Branch) :
    (T.branchPieceIn c).map = T.piece.piece.map :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchPieceIn_map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchPieceIn_map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchPieceIn_map ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchPieceIn_map

open _root_.Classical in
theorem branchCarrier_isPolyhedralSphere
    (T : NormalSingularSetTriangulation D BdM) {c : T.Branch}
    (hc : ¬T.IsBoundaryBranch c) :
    IsPolyhedralSphere (n := 3) 1 (T.branchCarrier c) := by
  apply isPolyhedralSphere_of_pieceIn (T.branchPieceIn c)
  simpa only [branchPieceIn_complex] using T.branchComplex_isPLSphere hc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchCarrier_isPolyhedralSphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchCarrier_isPolyhedralSphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchCarrier_isPolyhedralSphere ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchCarrier_isPolyhedralSphere

open _root_.Classical in
theorem branchCarrier_isPolyhedralBall
    (T : NormalSingularSetTriangulation D BdM) {c : T.Branch}
    (hc : T.IsBoundaryBranch c) :
    IsPolyhedralBall (n := 3) 1 (T.branchCarrier c) := by
  apply isPolyhedralBall_of_pieceIn (T.branchPieceIn c)
  simpa only [branchPieceIn_complex] using T.branchComplex_isPLBall hc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchCarrier_isPolyhedralBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchCarrier_isPolyhedralBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchCarrier_isPolyhedralBall ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchCarrier_isPolyhedralBall

theorem branchComplex_space_subset
    (T : NormalSingularSetTriangulation D BdM) (c : T.Branch) :
    (T.branchComplex c).space ⊆ T.complex.space :=
  space_mono_of_faces_subset (T.branchComplex_faces_subset c)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchComplex_space_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchComplex_space_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchComplex_space_subset ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchComplex_space_subset

theorem branchComplex_space_subset_piece
    (T : NormalSingularSetTriangulation D BdM) (c : T.Branch) :
    (T.branchComplex c).space ⊆ T.piece.piece.complex.space :=
  space_mono_of_faces_subset ((T.branchComplex_faces_subset c).trans T.faces_subset)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchComplex_space_subset_piece then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchComplex_space_subset_piece"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchComplex_space_subset_piece ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchComplex_space_subset_piece

open _root_.Classical in
theorem space_eq_iUnion_branchComplex
    (T : NormalSingularSetTriangulation D BdM) :
    T.complex.space = ⋃ c : T.Branch, (T.branchComplex c).space := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨s, hs, hxs⟩ := T.complex.mem_space_iff.mp hx
    obtain ⟨u, hus⟩ := T.complex.nonempty_of_mem_faces hs
    have hu : u ∈ T.complex.vertices :=
      T.complex.down_closed hs (Finset.singleton_subset_iff.mpr hus)
        (Finset.singleton_nonempty u)
    let c : T.Branch :=
      (SimplicialComplex.edgeGraph T.complex).connectedComponentMk ⟨u, hu⟩
    apply mem_iUnion.mpr
    refine ⟨c, (T.branchComplex c).convexHull_subset_space ⟨hs, ?_⟩ hxs⟩
    intro w hws
    have hw : w ∈ T.complex.vertices :=
      T.complex.down_closed hs (Finset.singleton_subset_iff.mpr hws)
        (Finset.singleton_nonempty w)
    have hwc : (⟨w, hw⟩ : T.complex.vertices) ∈ c.supp := by
      by_cases hwu : w = u
      · subst w
        exact SimpleGraph.ConnectedComponent.connectedComponentMk_mem
      · apply c.mem_supp_of_adj_mem_supp
          SimpleGraph.ConnectedComponent.connectedComponentMk_mem
        refine ⟨fun h => hwu (congrArg Subtype.val h).symm, ?_⟩
        apply T.complex.down_closed hs
        · intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          exact hz.elim (fun h => h ▸ hus) (fun h => h ▸ hws)
        · simp
    exact ⟨⟨w, hw⟩, hwc, rfl⟩
  · apply _root_.Set.iUnion_subset
    intro c
    exact T.branchComplex_space_subset c

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.space_eq_iUnion_branchComplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.space_eq_iUnion_branchComplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.space_eq_iUnion_branchComplex ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.space_eq_iUnion_branchComplex

open _root_.Classical in
theorem pairwise_disjoint_branchComplex_space
    (T : NormalSingularSetTriangulation D BdM) :
    Pairwise fun c d : T.Branch =>
      Disjoint (T.branchComplex c).space (T.branchComplex d).space := by
  intro c d hcd
  apply Set.disjoint_left.mpr
  intro x hxc hxd
  obtain ⟨s, hs, hxs⟩ := (T.branchComplex c).mem_space_iff.mp hxc
  obtain ⟨t, ht, hxt⟩ := (T.branchComplex d).mem_space_iff.mp hxd
  have hxst : x ∈ convexHull ℝ (s : Set _) ∩ convexHull ℝ (t : Set _) := ⟨hxs, hxt⟩
  have hxinter := T.complex.inter_subset_convexHull hs.1 ht.1 hxst
  obtain ⟨w, hws, hwt⟩ := convexHull_nonempty_iff.mp ⟨x, hxinter⟩
  obtain ⟨v, hvc, hvw⟩ := hs.2 hws
  obtain ⟨z, hzd, hzw⟩ := ht.2 hwt
  have hvz : v = z := Subtype.ext (hvw.trans hzw.symm)
  subst z
  exact hcd (SimpleGraph.ConnectedComponent.eq_of_common_vertex hvc hzd)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.pairwise_disjoint_branchComplex_space then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.pairwise_disjoint_branchComplex_space"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.pairwise_disjoint_branchComplex_space ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.pairwise_disjoint_branchComplex_space

theorem branchCarrier_subset_doublePointSet
    (T : NormalSingularSetTriangulation D BdM) (c : T.Branch) :
    T.branchCarrier c ⊆ doublePointSet D D.domain := by
  rw [← T.map_space]
  exact _root_.Set.image_mono (T.branchComplex_space_subset c)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchCarrier_subset_doublePointSet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchCarrier_subset_doublePointSet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchCarrier_subset_doublePointSet ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchCarrier_subset_doublePointSet

open _root_.Classical in
private theorem mem_branch_supp_of_vertex
    (T : NormalSingularSetTriangulation D BdM) (c : T.Branch)
    {x : EuclideanSpace ℝ (Fin T.piece.ambientDim)}
    (hxvertex : x ∈ T.complex.vertices)
    (hxbranch : x ∈ (T.branchComplex c).space) :
    (⟨x, hxvertex⟩ : T.complex.vertices) ∈ c.supp := by
  have hxbranchface : {x} ∈ (T.branchComplex c).faces :=
    (SimplicialComplex.singleton_mem_subcomplex_iff_mem_space
      (K := T.complex) (L := T.branchComplex c)
      (T.branchComplex_faces_subset c) hxvertex).mpr hxbranch
  have hxvertices : x ∈ T.branchVertices c := hxbranchface.2 (by simp)
  obtain ⟨v, hvc, hvx⟩ := hxvertices
  have hv : v = (⟨x, hxvertex⟩ : T.complex.vertices) := Subtype.ext hvx
  exact hv ▸ hvc

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.mem_branch_supp_of_vertex
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.mem_branch_supp_of_vertex target :: scope.openDecls } }

open _root_.Classical in
private theorem exists_mem_boundaryComplexModel_of_mem_doublePointSet_inter_boundary
    (T : NormalSingularSetTriangulation D BdM) {y : M}
    (hy : y ∈ doublePointSet D D.domain ∩ BdM) :
    ∃ x ∈ T.boundaryComplexModel.space, T.piece.piece.map x = y := by
  change y ∈ T.piece.piece.map '' T.boundaryComplexModel.space
  rw [T.map_boundaryComplexModel]
  exact hy

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.exists_mem_boundaryComplexModel_of_mem_doublePointSet_inter_boundary
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.exists_mem_boundaryComplexModel_of_mem_doublePointSet_inter_boundary target :: scope.openDecls } }

open _root_.Classical in
private theorem exists_degree_one_vertex_of_mem_boundaryComplexModel
    (T : NormalSingularSetTriangulation D BdM)
    {x : EuclideanSpace ℝ (Fin T.piece.ambientDim)}
    (hxboundary : x ∈ T.boundaryComplexModel.space) :
    ∃ hxvertex : x ∈ T.complex.vertices,
      ((SimplicialComplex.edgeGraph T.complex).neighborSet
        (⟨x, hxvertex⟩ : T.complex.vertices)).ncard = 1 := by
  have hxclassical : x ∈ T.classicalBoundaryComplexModel.space := by
    rw [← T.boundaryComplexModel_eq_classicalBoundaryComplexModel]
    exact hxboundary
  obtain ⟨s, hs, hxs⟩ := T.classicalBoundaryComplexModel.mem_space_iff.mp hxclassical
  have hsB := hs
  obtain ⟨hsG, t, _, hst, _, _⟩ := hs
  have hsc : s.card = 1 := by
    have hpos := Finset.card_pos.mpr (T.complex.nonempty_of_mem_faces hsG)
    have hle := Finset.card_le_card hst
    omega
  obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hsc
  have hxv : x = v := by
    simpa only [Finset.coe_singleton, convexHull_singleton, Set.mem_singleton_iff] using hxs
  subst x
  let _ : Finite T.complex.faces := T.finite_faces.to_subtype
  refine ⟨hsG, ?_⟩
  apply (mem_boundaryComplex_vertices_iff_edgeGraph_neighborSet_ncard_eq_one
    T.complex T.isManifoldWithBoundary ⟨v, hsG⟩).mp
  change ({v} : Finset (EuclideanSpace ℝ (Fin T.piece.ambientDim))) ∈
    (@boundaryComplex (EuclideanSpace ℝ (Fin T.piece.ambientDim)) _ _
      (Classical.decEq _) 1 T.complex).faces
  simpa only [classicalBoundaryComplexModel] using hsB

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.exists_degree_one_vertex_of_mem_boundaryComplexModel
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.exists_degree_one_vertex_of_mem_boundaryComplexModel target :: scope.openDecls } }

open _root_.Classical in
private theorem exists_degree_one_preimage_of_mem_doublePointSet_inter_boundary
    (T : NormalSingularSetTriangulation D BdM) {y : M}
    (hy : y ∈ doublePointSet D D.domain ∩ BdM) :
    ∃ v : T.complex.vertices,
      ((SimplicialComplex.edgeGraph T.complex).neighborSet v).ncard = 1 ∧
        T.piece.piece.map v = y := by
  obtain ⟨x, hxboundary, hxy⟩ :=
    T.exists_mem_boundaryComplexModel_of_mem_doublePointSet_inter_boundary hy
  obtain ⟨hxvertex, hdegree⟩ :=
    T.exists_degree_one_vertex_of_mem_boundaryComplexModel hxboundary
  exact ⟨⟨x, hxvertex⟩, hdegree, hxy⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.exists_degree_one_preimage_of_mem_doublePointSet_inter_boundary
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.exists_degree_one_preimage_of_mem_doublePointSet_inter_boundary target :: scope.openDecls } }

open _root_.Classical in
theorem isBoundaryBranch_of_mem_branchComplex_space_of_map_mem_boundary
    (T : NormalSingularSetTriangulation D BdM) (c : T.Branch)
    {x : EuclideanSpace ℝ (Fin T.piece.ambientDim)}
    (hxbranch : x ∈ (T.branchComplex c).space)
    (hxboundary : T.piece.piece.map x ∈ BdM) :
    T.IsBoundaryBranch c := by
  have hdouble : T.piece.piece.map x ∈ doublePointSet D D.domain :=
    T.branchCarrier_subset_doublePointSet c ⟨x, hxbranch, rfl⟩
  obtain ⟨v, hdegree, hvx⟩ :=
    T.exists_degree_one_preimage_of_mem_doublePointSet_inter_boundary
      ⟨hdouble, hxboundary⟩
  have hvspace : (v : EuclideanSpace ℝ (Fin T.piece.ambientDim)) ∈
      T.piece.piece.complex.space :=
    space_mono_of_faces_subset T.faces_subset (T.complex.vertices_subset_space v.2)
  have hxspace : x ∈ T.piece.piece.complex.space :=
    T.branchComplex_space_subset_piece c hxbranch
  have hvx' : (v : EuclideanSpace ℝ (Fin T.piece.ambientDim)) = x :=
    T.piece.piece.bijOn.injOn hvspace hxspace hvx
  have hxvertex : x ∈ T.complex.vertices := hvx' ▸ v.2
  let w : T.complex.vertices := ⟨x, hxvertex⟩
  have hvw : v = w := Subtype.ext hvx'
  refine ⟨w, T.mem_branch_supp_of_vertex c hxvertex hxbranch, ?_⟩
  rw [← hvw]
  exact hdegree

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.isBoundaryBranch_of_mem_branchComplex_space_of_map_mem_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.isBoundaryBranch_of_mem_branchComplex_space_of_map_mem_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.isBoundaryBranch_of_mem_branchComplex_space_of_map_mem_boundary ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.isBoundaryBranch_of_mem_branchComplex_space_of_map_mem_boundary

open _root_.Classical in
theorem branchCarrier_disjoint_boundary_of_not_isBoundaryBranch
    (T : NormalSingularSetTriangulation D BdM) {c : T.Branch}
    (hc : ¬T.IsBoundaryBranch c) :
    Disjoint (T.branchCarrier c) BdM := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨x, hxbranch, rfl⟩ hxboundary
  apply hc
  exact T.isBoundaryBranch_of_mem_branchComplex_space_of_map_mem_boundary
    c hxbranch hxboundary

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchCarrier_disjoint_boundary_of_not_isBoundaryBranch then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchCarrier_disjoint_boundary_of_not_isBoundaryBranch"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchCarrier_disjoint_boundary_of_not_isBoundaryBranch ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchCarrier_disjoint_boundary_of_not_isBoundaryBranch

open _root_.Classical in
private theorem mem_boundaryComplexModel_of_degree_one
    (T : NormalSingularSetTriangulation D BdM) (v : T.complex.vertices)
    (hdegree : ((SimplicialComplex.edgeGraph T.complex).neighborSet v).ncard = 1) :
    (v : EuclideanSpace ℝ (Fin T.piece.ambientDim)) ∈ T.boundaryComplexModel.space := by
  let _ : Finite T.complex.faces := T.finite_faces.to_subtype
  have hvclassical : (v : EuclideanSpace ℝ (Fin T.piece.ambientDim)) ∈
      T.classicalBoundaryComplexModel.vertices := by
    have hv :=
      (mem_boundaryComplex_vertices_iff_edgeGraph_neighborSet_ncard_eq_one
        T.complex T.isManifoldWithBoundary v).mpr hdegree
    change ({(v : EuclideanSpace ℝ (Fin T.piece.ambientDim))} :
      Finset (EuclideanSpace ℝ (Fin T.piece.ambientDim))) ∈
        (@boundaryComplex (EuclideanSpace ℝ (Fin T.piece.ambientDim)) _ _
          (Classical.decEq _) 1 T.complex).faces at hv
    change ({(v : EuclideanSpace ℝ (Fin T.piece.ambientDim))} :
      Finset (EuclideanSpace ℝ (Fin T.piece.ambientDim))) ∈
        (@boundaryComplex (EuclideanSpace ℝ (Fin T.piece.ambientDim)) _ _
          (Classical.decEq _) 1 T.complex).faces
    exact hv
  rw [T.boundaryComplexModel_eq_classicalBoundaryComplexModel]
  exact T.classicalBoundaryComplexModel.vertices_subset_space hvclassical

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.mem_boundaryComplexModel_of_degree_one
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.mem_boundaryComplexModel_of_degree_one target :: scope.openDecls } }

open _root_.Classical in
private theorem map_mem_doublePointSet_inter_boundary_of_degree_one
    (T : NormalSingularSetTriangulation D BdM) (v : T.complex.vertices)
    (hdegree : ((SimplicialComplex.edgeGraph T.complex).neighborSet v).ncard = 1) :
    T.piece.piece.map v ∈ doublePointSet D D.domain ∩ BdM := by
  rw [← T.map_boundaryComplexModel]
  exact ⟨v, T.mem_boundaryComplexModel_of_degree_one v hdegree, rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.map_mem_doublePointSet_inter_boundary_of_degree_one
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.map_mem_doublePointSet_inter_boundary_of_degree_one target :: scope.openDecls } }

open _root_.Classical in
theorem branchCarrier_inter_boundary_nonempty_of_isBoundaryBranch
    (T : NormalSingularSetTriangulation D BdM) {c : T.Branch}
    (hc : T.IsBoundaryBranch c) :
    (T.branchCarrier c ∩ BdM).Nonempty := by
  obtain ⟨v, hvc, hdegree⟩ := T.exists_degree_one_vertex_of_isBoundaryBranch hc
  let w : c.supp := ⟨v, hvc⟩
  have hvbranch : (v : EuclideanSpace ℝ (Fin T.piece.ambientDim)) ∈
      (T.branchComplex c).space :=
    (T.branchComplex c).vertices_subset_space (T.branchVertex c w).2
  have hyboundary := T.map_mem_doublePointSet_inter_boundary_of_degree_one v hdegree
  exact ⟨T.piece.piece.map v, ⟨v, hvbranch, rfl⟩, hyboundary.2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchCarrier_inter_boundary_nonempty_of_isBoundaryBranch then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchCarrier_inter_boundary_nonempty_of_isBoundaryBranch"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchCarrier_inter_boundary_nonempty_of_isBoundaryBranch ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchCarrier_inter_boundary_nonempty_of_isBoundaryBranch

theorem branchCarrier_isConnected
    (T : NormalSingularSetTriangulation D BdM) (c : T.Branch) :
    IsConnected (T.branchCarrier c) :=
  (T.branchComplex_space_isConnected c).image T.piece.piece.map
    (T.piece.piece.continuousOn.mono (T.branchComplex_space_subset_piece c))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchCarrier_isConnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchCarrier_isConnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchCarrier_isConnected ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchCarrier_isConnected

theorem iUnion_branchCarrier
    (T : NormalSingularSetTriangulation D BdM) :
    ⋃ c : T.Branch, T.branchCarrier c = doublePointSet D D.domain := by
  apply Subset.antisymm
  · apply _root_.Set.iUnion_subset
    intro c
    exact T.branchCarrier_subset_doublePointSet c
  · intro y hy
    have hyimage : y ∈ T.piece.piece.map '' T.complex.space := by
      rw [T.map_space]
      exact hy
    obtain ⟨x, hx, rfl⟩ := hyimage
    rw [T.space_eq_iUnion_branchComplex] at hx
    obtain ⟨c, hxc⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨c, ⟨x, hxc, rfl⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.iUnion_branchCarrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.iUnion_branchCarrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.iUnion_branchCarrier ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.iUnion_branchCarrier

theorem pairwise_disjoint_branchCarrier
    (T : NormalSingularSetTriangulation D BdM) :
    Pairwise fun c d : T.Branch => Disjoint (T.branchCarrier c) (T.branchCarrier d) := by
  intro c d hcd
  apply Set.disjoint_left.mpr
  rintro y ⟨x, hxc, rfl⟩ ⟨z, hzd, hzx⟩
  have hxz : x = z := T.piece.piece.bijOn.injOn
    (T.branchComplex_space_subset_piece c hxc)
    (T.branchComplex_space_subset_piece d hzd) hzx.symm
  subst z
  exact Set.disjoint_left.mp (T.pairwise_disjoint_branchComplex_space hcd) hxc hzd

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.pairwise_disjoint_branchCarrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.pairwise_disjoint_branchCarrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.pairwise_disjoint_branchCarrier ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.pairwise_disjoint_branchCarrier

def branchSet (T : NormalSingularSetTriangulation D BdM) (c : T.Branch) :
    Set (doublePointSet D D.domain) :=
  ((↑) : doublePointSet D D.domain → M) ⁻¹' T.branchCarrier c

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchSet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchSet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchSet ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchSet

theorem iUnion_branchSet
    (T : NormalSingularSetTriangulation D BdM) :
    ⋃ c : T.Branch, T.branchSet c = univ := by
  apply eq_univ_iff_forall.mpr
  intro y
  have hy : (y : M) ∈ ⋃ c : T.Branch, T.branchCarrier c := by
    rw [T.iUnion_branchCarrier]
    exact y.2
  obtain ⟨c, hyc⟩ := mem_iUnion.mp hy
  exact mem_iUnion.mpr ⟨c, hyc⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.iUnion_branchSet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.iUnion_branchSet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.iUnion_branchSet ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.iUnion_branchSet

theorem pairwise_disjoint_branchSet
    (T : NormalSingularSetTriangulation D BdM) :
    Pairwise fun c d : T.Branch => Disjoint (T.branchSet c) (T.branchSet d) := by
  intro c d hcd
  apply Set.disjoint_left.mpr
  intro y hyc hyd
  exact Set.disjoint_left.mp (T.pairwise_disjoint_branchCarrier hcd) hyc hyd

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.pairwise_disjoint_branchSet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.pairwise_disjoint_branchSet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.pairwise_disjoint_branchSet ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.pairwise_disjoint_branchSet

theorem image_branchSet
    (T : NormalSingularSetTriangulation D BdM) (c : T.Branch) :
    ((↑) : doublePointSet D D.domain → M) '' T.branchSet c = T.branchCarrier c := by
  apply Subset.antisymm
  · rintro _ ⟨y, hy, rfl⟩
    exact hy
  · intro y hy
    exact ⟨⟨y, T.branchCarrier_subset_doublePointSet c hy⟩, hy, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.image_branchSet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.image_branchSet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.image_branchSet ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.image_branchSet

theorem branchSet_isConnected
    (T : NormalSingularSetTriangulation D BdM) (c : T.Branch) :
    IsConnected (T.branchSet c) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨y, hy⟩ := (T.branchCarrier_isConnected c).nonempty
    exact ⟨⟨y, T.branchCarrier_subset_doublePointSet c hy⟩, hy⟩
  · apply IsInducing.subtypeVal.isPreconnected_image.mp
    rw [T.image_branchSet c]
    exact (T.branchCarrier_isConnected c).isPreconnected

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchSet_isConnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchSet_isConnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchSet_isConnected ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchSet_isConnected

end NormalSingularSetTriangulation

namespace NormalSingularCellData

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D : SingularTwoCell M} {BdM B : Set M}

theorem branchCarrier_inter_boundary_subset
    (hD : NormalSingularCellData D BdM B) (c : hD.singularSet.Branch) :
    hD.singularSet.branchCarrier c ∩ BdM ⊆ B := by
  rintro y ⟨hycarrier, hyboundary⟩
  have hydouble := hD.singularSet.branchCarrier_subset_doublePointSet c hycarrier
  obtain ⟨x, hx, _, _, _, hxy, _⟩ := hydouble
  apply hD.boundary_image_subset
  rw [← hD.image_inter_boundary]
  exact ⟨⟨x, hx, hxy⟩, hyboundary⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.branchCarrier_inter_boundary_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.branchCarrier_inter_boundary_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.branchCarrier_inter_boundary_subset ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.branchCarrier_inter_boundary_subset

end NormalSingularCellData

end DifferentialGeometry.Topology.PiecewiseLinear
