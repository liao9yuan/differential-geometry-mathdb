/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnBoundary
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactDualCells
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactResidualCells
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.SubcomplexComplement

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

private theorem restrict_subcomplex_eq_self {M K : Geometry.SimplicialComplex ℝ E3}
    (hKM : K.faces ⊆ M.faces) : restrict M K.space = K := by
  ext s
  rw [mem_restrict_faces_iff_of_faces_subset M M K subset_rfl hKM]
  exact ⟨fun hs => hs.2, fun hs => ⟨hKM hs, hs⟩⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.restrict_subcomplex_eq_self
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.restrict_subcomplex_eq_self target :: scope.openDecls } }

theorem isPLCellOn_of_isPLBall_restrict_space
    (R : Geometry.SimplicialComplex ℝ E3) [Finite R.faces] {n : ℕ} {P : Set E3}
    (hP : IsPLBall n P) (hRP : (restrict R P).space = P) :
    IsPLCellOn n P (boundaryComplex n (restrict R P)).space := by
  classical
  let _ : Finite (restrict R P).faces := (restrict_faces_finite R P).to_subtype
  cases n with
  | zero =>
    obtain ⟨r, hr⟩ := hP
    have hcell := isPLCellOn_id_of_isPLBall hr
    have hb : (boundaryComplex 0 (restrict R P)).space = ∅ := by
      rw [_root_.Set.eq_empty_iff_forall_notMem]
      intro x hx
      obtain ⟨s, ⟨-, t, ht, -, hcard, -⟩, -⟩ :=
        (boundaryComplex 0 (restrict R P)).mem_space_iff.mp hx
      have hpos := Finset.card_pos.mpr ((restrict R P).nonempty_of_mem_faces ht)
      omega
    simpa only [stdSimplexBoundary_zero, _root_.Set.image_empty, hb] using hcell
  | succ n =>
    obtain ⟨r, hr⟩ := hP
    have hcell := isPLCellOn_id_of_isPLBall hr
    rw [hr.image_stdSimplexBoundary_eq_boundaryComplex (restrict R P) hRP] at hcell
    exact hcell

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPLCellOn_of_isPLBall_restrict_space then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPLCellOn_of_isPLBall_restrict_space"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPLCellOn_of_isPLBall_restrict_space ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPLCellOn_of_isPLBall_restrict_space

theorem compactDualResidualCell_eq_derived_triangle
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hKM : K.faces ⊆ M.faces) (s : Section34CompactSimplexIndex K 3) :
    compactDualResidualCell M K s.1 =
      (derivedNeighborhoodCell (restrict M (convexHull ℝ (s.1 : Set E3))) s.1).space := by
  have hMK := restrict_subcomplex_eq_self hKM
  let s' : Section34CompactSimplexIndex (restrict M K.space) 3 :=
    ⟨s.1, by simpa only [hMK] using s.2⟩
  have h := closure_convexHull_sdiff_iUnion_graphDualCell_of_card_eq_three (M := M)
    (C := K.space) s'
  simpa only [compactDualResidualCell, compactDualNeighborhood, hMK, s'] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.compactDualResidualCell_eq_derived_triangle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.compactDualResidualCell_eq_derived_triangle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.compactDualResidualCell_eq_derived_triangle ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.compactDualResidualCell_eq_derived_triangle

theorem compactDualResidualCell_eq_derived_tetrahedron
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hKM : K.faces ⊆ M.faces) (t : Section34CompactSimplexIndex K 4) :
    compactDualResidualCell M K t.1 =
      (derivedNeighborhoodCell (restrict M (convexHull ℝ (t.1 : Set E3))) t.1).space ∪
        ⋃ s ∈ t.1.powersetCard 3,
          (derivedNeighborhoodCell (restrict M (convexHull ℝ (t.1 : Set E3))) s).space := by
  have hMK := restrict_subcomplex_eq_self hKM
  let t' : Section34CompactSimplexIndex (restrict M K.space) 4 :=
    ⟨t.1, by simpa only [hMK] using t.2⟩
  have h := closure_convexHull_sdiff_iUnion_graphDualCell_of_card_eq_four (M := M)
    (C := K.space) t'
  simpa only [compactDualResidualCell, compactDualNeighborhood, hMK, t'] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.compactDualResidualCell_eq_derived_tetrahedron then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.compactDualResidualCell_eq_derived_tetrahedron"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.compactDualResidualCell_eq_derived_tetrahedron ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.compactDualResidualCell_eq_derived_tetrahedron

theorem isPLBall_compactDualResidualCell_triangle
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hKM : K.faces ⊆ M.faces) (s : Section34CompactSimplexIndex K 3) :
    IsPLBall 2 (compactDualResidualCell M K s.1) := by
  rw [compactDualResidualCell_eq_derived_triangle M K hKM s]
  exact isPLBall_derivedNeighborhoodCell_restrict_of_card_eq_three (hKM s.2.1) s.2.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_compactDualResidualCell_triangle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_compactDualResidualCell_triangle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_compactDualResidualCell_triangle ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_compactDualResidualCell_triangle

theorem isPLBall_compactDualResidualCell_tetrahedron
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hKM : K.faces ⊆ M.faces) (t : Section34CompactSimplexIndex K 4) :
    IsPLBall 3 (compactDualResidualCell M K t.1) := by
  rw [compactDualResidualCell_eq_derived_tetrahedron M K hKM t]
  exact isPLBall_residualCell_of_card_eq_four (hKM t.2.1) t.2.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_compactDualResidualCell_tetrahedron then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_compactDualResidualCell_tetrahedron"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_compactDualResidualCell_tetrahedron ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_compactDualResidualCell_tetrahedron

theorem restrict_compactDualResidualCell_space
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hKM : K.faces ⊆ M.faces) {s : Finset E3} (hs : s ∈ K.faces) :
    (restrict (secondDerived M) (compactDualResidualCell M K s)).space =
      compactDualResidualCell M K s := by
  classical
  let L := restrict K (section34CompactGraphSkeleton K)
  let A := secondDerived (restrict M (convexHull ℝ (s : Set E3)))
  let B := derivedNeighborhood M L
  let G := subcomplexGeneratedBy A B.facesᶜ
  have hAR : A.faces ⊆ (secondDerived M).faces :=
    secondDerived_faces_subset (restrict_faces_subset M _)
  have hBR : B.faces ⊆ (secondDerived M).faces := derivedNeighborhood_faces_subset M L
  have hGR : G.faces ⊆ (secondDerived M).faces :=
    (subcomplexGeneratedBy_faces_subset A _).trans hAR
  let _ : Finite A.faces := ((Set.toFinite (secondDerived M).faces).subset hAR).to_subtype
  have hAspace : A.space = convexHull ℝ (s : Set E3) :=
    (secondDerived_isSubdivision _).space_eq.trans (restrict_convexHull_space (hKM hs))
  have hLM : L.faces ⊆ M.faces := (restrict_faces_subset K _).trans hKM
  have hN : compactDualNeighborhood M K = B.space := by
    change (⋃ v ∈ K.vertices, (graphDualCell M L v).space) = B.space
    rw [vertices_eq_setOf_restrict_section34CompactGraphSkeleton]
    exact (iUnion_graphDualCell_space M L hLM).trans
      (congrArg (fun d : DecidableEq E3 => (@derivedNeighborhood E3 _ _ d M L).space)
        (Subsingleton.elim _ _))
  have hres : compactDualResidualCell M K s = G.space := by
    change closure (convexHull ℝ (s : Set E3) \ compactDualNeighborhood M K) = G.space
    rw [hN, ← hAspace]
    exact closure_space_sdiff_space_eq_subcomplexGeneratedBy (secondDerived M) A B hAR hBR
  rw [hres, restrict_space_eq_inter_of_faces_subset (secondDerived M)
    (secondDerived M) G subset_rfl hGR]
  exact inter_eq_right.mpr (space_mono_of_faces_subset hGR)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.restrict_compactDualResidualCell_space then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.restrict_compactDualResidualCell_space"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.restrict_compactDualResidualCell_space ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.restrict_compactDualResidualCell_space

theorem isPLCellOn_compactDualFaceDisk
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hKM : K.faces ⊆ M.faces) (s : Section34CompactSimplexIndex K 3) :
    IsPLCellOn 2 (compactDualCutCell M K hKM (.faceDisk s))
      (compactDualCutBoundary M K hKM (.faceDisk s)) := by
  exact isPLCellOn_of_isPLBall_restrict_space (secondDerived M)
    (isPLBall_compactDualResidualCell_triangle M K hKM s)
    (restrict_compactDualResidualCell_space M K hKM s.2.1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPLCellOn_compactDualFaceDisk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPLCellOn_compactDualFaceDisk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPLCellOn_compactDualFaceDisk ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPLCellOn_compactDualFaceDisk

theorem isPLCellOn_compactDualTetraBall
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hKM : K.faces ⊆ M.faces) (t : Section34CompactSimplexIndex K 4) :
    IsPLCellOn 3 (compactDualCutCell M K hKM (.tetraBall t))
      (compactDualCutBoundary M K hKM (.tetraBall t)) := by
  exact isPLCellOn_of_isPLBall_restrict_space (secondDerived M)
    (isPLBall_compactDualResidualCell_tetrahedron M K hKM t)
    (restrict_compactDualResidualCell_space M K hKM t.2.1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPLCellOn_compactDualTetraBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPLCellOn_compactDualTetraBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPLCellOn_compactDualTetraBall ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPLCellOn_compactDualTetraBall

end DifferentialGeometry.Topology.PiecewiseLinear
