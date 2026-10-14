/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossSeamTube
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Pasting
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PieceMap

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

theorem crossSeamResolve_eq_pos {q : Bool × ((ℝ × ℝ) × ℝ)} (hq : q.1 = _root_.Bool.true) :
    crossSeamResolve q = crossSeamResolvePos q.2 := by
  have h : q = (_root_.Bool.true, q.2) := Prod.ext hq rfl
  rw [h, crossSeamResolve_true]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.crossSeamResolve_eq_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.crossSeamResolve_eq_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.crossSeamResolve_eq_pos ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.crossSeamResolve_eq_pos

theorem crossSeamResolve_eq_neg {q : Bool × ((ℝ × ℝ) × ℝ)} (hq : q.1 = _root_.Bool.false) :
    crossSeamResolve q = crossSeamResolveNeg q.2 := by
  have h : q = (_root_.Bool.false, q.2) := Prod.ext hq rfl
  rw [h, crossSeamResolve_false]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.crossSeamResolve_eq_neg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.crossSeamResolve_eq_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.crossSeamResolve_eq_neg ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.crossSeamResolve_eq_neg

theorem bentSheetPos_nonempty : bentSheetPos.Nonempty :=
  ⟨(((1 : ℝ), (0 : ℝ)), (0 : ℝ)), mem_bentArcPos.mpr (Or.inl ⟨⟨by norm_num, le_rfl⟩, rfl⟩),
    ⟨le_rfl, zero_le_one⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.bentSheetPos_nonempty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.bentSheetPos_nonempty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.bentSheetPos_nonempty ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.bentSheetPos_nonempty

theorem bentSheetNeg_nonempty : bentSheetNeg.Nonempty :=
  ⟨((((-1) : ℝ), (0 : ℝ)), (0 : ℝ)), mem_bentArcNeg.mpr (Or.inl ⟨⟨le_rfl, by norm_num⟩, rfl⟩),
    ⟨le_rfl, zero_le_one⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.bentSheetNeg_nonempty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.bentSheetNeg_nonempty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.bentSheetNeg_nonempty ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.bentSheetNeg_nonempty

structure PLSeamTubeChart (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] (chart : (ℝ × ℝ) × ℝ → M) where
  piece : PLPieceIn ((ℝ × ℝ) × ℝ) 3 M (chart '' spliceCylinder)
  space_eq : piece.complex.space = spliceCylinder
  map_eq : piece.map = chart

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.PLSeamTubeChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.PLSeamTubeChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.PLSeamTubeChart ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLSeamTubeChart

namespace PLSeamTubeChart

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {chart : (ℝ × ℝ) × ℝ → M}

theorem isPLOn_comp (C : PLSeamTubeChart M chart)
    {f : EuclideanSpace ℝ (Fin 2) → (ℝ × ℝ) × ℝ} {P : Set (EuclideanSpace ℝ (Fin 2))}
    (hf : IsPiecewiseAffineOn f P) (hmap : _root_.Set.MapsTo f P spliceCylinder) :
    IsPLOn 2 3 (chart ∘ f) P := by
  have hmap' : _root_.Set.MapsTo f P C.piece.complex.space := by
    rw [C.space_eq]
    exact hmap
  have h := C.piece.isPLOn_comp hf hmap'
  rwa [C.map_eq] at h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.PLSeamTubeChart.isPLOn_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.PLSeamTubeChart.isPLOn_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.PLSeamTubeChart.isPLOn_comp ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLSeamTubeChart.isPLOn_comp

end PLSeamTubeChart

structure PLCrossSeamReading {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] (chart : (ℝ × ℝ) × ℝ → M)
    (G : SingularTwoCell M) where
  coord : EuclideanSpace ℝ (Fin 2) → Bool × ((ℝ × ℝ) × ℝ)
  sourcePos : Set (EuclideanSpace ℝ (Fin 2))
  sourceNeg : Set (EuclideanSpace ℝ (Fin 2))
  face : Set (EuclideanSpace ℝ (Fin 2))
  isPLHomeomorphOn_pos : IsPLHomeomorphOn (fun x => (coord x).2) sourcePos bentSheetPos
  isPLHomeomorphOn_neg : IsPLHomeomorphOn (fun x => (coord x).2) sourceNeg bentSheetNeg
  coord_fst_pos : ∀ x ∈ sourcePos, (coord x).1 = _root_.Bool.true
  coord_fst_neg : ∀ x ∈ sourceNeg, (coord x).1 = _root_.Bool.false
  source_eq : sourcePos ∪ sourceNeg = G.domain ∩ ⇑G ⁻¹' (chart '' spliceCylinder)
  isPolyhedron_face : IsPolyhedron face
  union_eq : sourcePos ∪ sourceNeg ∪ face = G.domain
  reglued_eq : _root_.Set.EqOn (⇑G) (chart ∘ crossSeamInclude ∘ coord) (sourcePos ∪ sourceNeg)
  overlap_lateral : ∀ x ∈ (sourcePos ∪ sourceNeg) ∩ face,
    (coord x).2 ∈ spliceSquareBoundary ×ˢ _root_.Set.Icc (0 : ℝ) 1
  boundary_iff_end : ∀ x ∈ sourcePos ∪ sourceNeg,
    (x ∈ frontier G.domain ↔ (coord x).2.2 = 0 ∨ (coord x).2.2 = 1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading

namespace PLCrossSeamReading

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {chart : (ℝ × ℝ) × ℝ → M} {G : SingularTwoCell M}

def tubeSource (R : PLCrossSeamReading chart G) : Set (EuclideanSpace ℝ (Fin 2)) :=
  R.sourcePos ∪ R.sourceNeg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.tubeSource then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.tubeSource"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.tubeSource ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.tubeSource

theorem mem_tubeSource (R : PLCrossSeamReading chart G) {x : EuclideanSpace ℝ (Fin 2)} :
    x ∈ R.tubeSource ↔ x ∈ R.sourcePos ∨ x ∈ R.sourceNeg := Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.mem_tubeSource then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.mem_tubeSource"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.mem_tubeSource ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.mem_tubeSource

theorem tubeSource_eq (R : PLCrossSeamReading chart G) :
    R.tubeSource = G.domain ∩ ⇑G ⁻¹' (chart '' spliceCylinder) := R.source_eq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.tubeSource_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.tubeSource_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.tubeSource_eq ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.tubeSource_eq

theorem tubeSource_union_face (R : PLCrossSeamReading chart G) :
    R.tubeSource ∪ R.face = G.domain := R.union_eq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.tubeSource_union_face then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.tubeSource_union_face"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.tubeSource_union_face ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.tubeSource_union_face

theorem disjoint_source (R : PLCrossSeamReading chart G) :
    Disjoint R.sourcePos R.sourceNeg := by
  rw [Set.disjoint_left]
  intro x hx hx'
  exact Bool.noConfusion ((R.coord_fst_pos x hx).symm.trans (R.coord_fst_neg x hx'))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.disjoint_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.disjoint_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.disjoint_source ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.disjoint_source

theorem bijOn_coord (R : PLCrossSeamReading chart G) :
    BijOn R.coord R.tubeSource bentSource := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rcases R.mem_tubeSource.mp hx with hx | hx
    · exact mem_bentSource.mpr
        (Or.inl ⟨R.coord_fst_pos x hx, R.isPLHomeomorphOn_pos.bijOn.mapsTo hx⟩)
    · exact mem_bentSource.mpr
        (Or.inr ⟨R.coord_fst_neg x hx, R.isPLHomeomorphOn_neg.bijOn.mapsTo hx⟩)
  · intro x hx z hz hxz
    rcases R.mem_tubeSource.mp hx with hx | hx <;>
      rcases R.mem_tubeSource.mp hz with hz | hz
    · exact R.isPLHomeomorphOn_pos.bijOn.injOn hx hz (congrArg Prod.snd hxz)
    · exact absurd (congrArg Prod.fst hxz) (by
        rw [R.coord_fst_pos x hx, R.coord_fst_neg z hz]; simp)
    · exact absurd (congrArg Prod.fst hxz) (by
        rw [R.coord_fst_neg x hx, R.coord_fst_pos z hz]; simp)
    · exact R.isPLHomeomorphOn_neg.bijOn.injOn hx hz (congrArg Prod.snd hxz)
  · intro q hq
    rcases mem_bentSource.mp hq with ⟨hb, hs⟩ | ⟨hb, hs⟩
    · obtain ⟨x, hx, hcx⟩ := R.isPLHomeomorphOn_pos.bijOn.surjOn hs
      exact ⟨x, R.mem_tubeSource.mpr (Or.inl hx),
        Prod.ext ((R.coord_fst_pos x hx).trans hb.symm) hcx⟩
    · obtain ⟨x, hx, hcx⟩ := R.isPLHomeomorphOn_neg.bijOn.surjOn hs
      exact ⟨x, R.mem_tubeSource.mpr (Or.inr hx),
        Prod.ext ((R.coord_fst_neg x hx).trans hb.symm) hcx⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.bijOn_coord then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.bijOn_coord"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.bijOn_coord ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.bijOn_coord

theorem isPolyhedron_sourcePos (R : PLCrossSeamReading chart G) :
    IsPolyhedron R.sourcePos := by
  have h := R.isPLHomeomorphOn_pos.symm
  rw [← h.image_eq]
  exact isPLBall_bentSheetPos.isPolyhedron.image_of_isPiecewiseAffineOn h.isPiecewiseAffineOn
    h.bijOn.injOn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.isPolyhedron_sourcePos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.isPolyhedron_sourcePos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.isPolyhedron_sourcePos ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.isPolyhedron_sourcePos

theorem isPolyhedron_sourceNeg (R : PLCrossSeamReading chart G) :
    IsPolyhedron R.sourceNeg := by
  have h := R.isPLHomeomorphOn_neg.symm
  rw [← h.image_eq]
  exact isPLBall_bentSheetNeg.isPolyhedron.image_of_isPiecewiseAffineOn h.isPiecewiseAffineOn
    h.bijOn.injOn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.isPolyhedron_sourceNeg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.isPolyhedron_sourceNeg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.isPolyhedron_sourceNeg ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.isPolyhedron_sourceNeg

theorem isPolyhedron_source (R : PLCrossSeamReading chart G) :
    IsPolyhedron R.tubeSource :=
  R.isPolyhedron_sourcePos.union R.isPolyhedron_sourceNeg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.isPolyhedron_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.isPolyhedron_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.isPolyhedron_source ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.isPolyhedron_source

theorem face_subset_domain (R : PLCrossSeamReading chart G) : R.face ⊆ G.domain := by
  rw [← R.tubeSource_union_face]
  exact _root_.Set.subset_union_right

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.face_subset_domain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.face_subset_domain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.face_subset_domain ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.face_subset_domain

theorem source_subset_domain (R : PLCrossSeamReading chart G) :
    R.tubeSource ⊆ G.domain := by
  rw [← R.tubeSource_union_face]
  exact _root_.Set.subset_union_left

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.source_subset_domain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.source_subset_domain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.source_subset_domain ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.source_subset_domain

theorem eqOn_resolve_pos (R : PLCrossSeamReading chart G) :
    _root_.Set.EqOn (crossSeamResolve ∘ R.coord) (crossSeamResolvePos ∘ fun x => (R.coord x).2)
      R.sourcePos := fun x hx => crossSeamResolve_eq_pos (R.coord_fst_pos x hx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.eqOn_resolve_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.eqOn_resolve_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.eqOn_resolve_pos ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.eqOn_resolve_pos

theorem eqOn_resolve_neg (R : PLCrossSeamReading chart G) :
    _root_.Set.EqOn (crossSeamResolve ∘ R.coord) (crossSeamResolveNeg ∘ fun x => (R.coord x).2)
      R.sourceNeg := fun x hx => crossSeamResolve_eq_neg (R.coord_fst_neg x hx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.eqOn_resolve_neg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.eqOn_resolve_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.eqOn_resolve_neg ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.eqOn_resolve_neg

theorem isPiecewiseAffineOn_resolve_pos (R : PLCrossSeamReading chart G) :
    IsPiecewiseAffineOn (crossSeamResolve ∘ R.coord) R.sourcePos := by
  have h := (isPLHomeomorphOn_crossSeamResolvePos.isPiecewiseAffineOn.comp
    R.isPLHomeomorphOn_pos.isPiecewiseAffineOn).mono_of_isPolyhedron R.isPolyhedron_sourcePos
    fun x hx => ⟨hx, R.isPLHomeomorphOn_pos.bijOn.mapsTo hx⟩
  exact h.congr R.eqOn_resolve_pos

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.isPiecewiseAffineOn_resolve_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.isPiecewiseAffineOn_resolve_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.isPiecewiseAffineOn_resolve_pos ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.isPiecewiseAffineOn_resolve_pos

theorem isPiecewiseAffineOn_resolve_neg (R : PLCrossSeamReading chart G) :
    IsPiecewiseAffineOn (crossSeamResolve ∘ R.coord) R.sourceNeg := by
  have h := (isPLHomeomorphOn_crossSeamResolveNeg.isPiecewiseAffineOn.comp
    R.isPLHomeomorphOn_neg.isPiecewiseAffineOn).mono_of_isPolyhedron R.isPolyhedron_sourceNeg
    fun x hx => ⟨hx, R.isPLHomeomorphOn_neg.bijOn.mapsTo hx⟩
  exact h.congr R.eqOn_resolve_neg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.isPiecewiseAffineOn_resolve_neg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.isPiecewiseAffineOn_resolve_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.isPiecewiseAffineOn_resolve_neg ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.isPiecewiseAffineOn_resolve_neg

theorem mapsTo_resolve (R : PLCrossSeamReading chart G) :
    MapsTo (crossSeamResolve ∘ R.coord) R.tubeSource spliceCylinder := by
  intro x hx
  refine spliceFigure_subset_spliceCylinder ?_
  rw [← image_crossSeamResolve]
  exact ⟨R.coord x, R.bijOn_coord.mapsTo hx, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.mapsTo_resolve then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.mapsTo_resolve"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.mapsTo_resolve ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.mapsTo_resolve

theorem isPLOn_resolve (R : PLCrossSeamReading chart G) (C : PLSeamTubeChart M chart) :
    IsPLOn 2 3 (chart ∘ crossSeamResolve ∘ R.coord) R.tubeSource := by
  classical
  have hpos : IsPLOn 2 3 (chart ∘ crossSeamResolve ∘ R.coord) R.sourcePos :=
    C.isPLOn_comp R.isPiecewiseAffineOn_resolve_pos fun x hx =>
      R.mapsTo_resolve (R.mem_tubeSource.mpr (Or.inl hx))
  have hneg : IsPLOn 2 3 (chart ∘ crossSeamResolve ∘ R.coord) R.sourceNeg :=
    C.isPLOn_comp R.isPiecewiseAffineOn_resolve_neg fun x hx =>
      R.mapsTo_resolve (R.mem_tubeSource.mpr (Or.inr hx))
  have h := hpos.piecewise_of_isClosed hneg R.isPolyhedron_sourcePos.isClosed
    R.isPolyhedron_sourceNeg.isClosed fun _ _ => rfl
  rwa [Set.piecewise_same] at h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.isPLOn_resolve then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.isPLOn_resolve"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.isPLOn_resolve ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.isPLOn_resolve

theorem eqOn_overlap (R : PLCrossSeamReading chart G) :
    _root_.Set.EqOn (chart ∘ crossSeamResolve ∘ R.coord) (⇑G)
      (R.tubeSource ∩ R.face) := by
  intro x hx
  have hlat := R.overlap_lateral x hx
  have hq : R.coord x ∈ bentSource := R.bijOn_coord.mapsTo hx.1
  have hfix : crossSeamResolve (R.coord x) = (R.coord x).2 := by
    rcases mem_bentSource.mp hq with ⟨hb, hs⟩ | ⟨hb, hs⟩
    · rw [crossSeamResolve_eq_pos hb]
      exact crossSeamResolvePos_eqOn_lateral ⟨hs, hlat⟩
    · rw [crossSeamResolve_eq_neg hb]
      exact crossSeamResolveNeg_eqOn_lateral ⟨hs, hlat⟩
  change chart (crossSeamResolve (R.coord x)) = G x
  rw [hfix, R.reglued_eq hx.1]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.eqOn_overlap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.eqOn_overlap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.eqOn_overlap ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.eqOn_overlap

open _root_.Classical in
noncomputable def resolvedCell (R : PLCrossSeamReading chart G) (C : PLSeamTubeChart M chart) :
    SingularTwoCell M where
  domain := G.domain
  isPLBall_domain := G.isPLBall_domain
  toFun := R.tubeSource.piecewise (chart ∘ crossSeamResolve ∘ R.coord) ⇑G
  isPLOn := by
    have h := (R.isPLOn_resolve C).piecewise_of_isClosed
      (G.isPLOn.mono_of_isPolyhedron R.isPolyhedron_face R.face_subset_domain)
      R.isPolyhedron_source.isClosed R.isPolyhedron_face.isClosed R.eqOn_overlap
    rw [R.tubeSource_union_face] at h
    exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.resolvedCell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.resolvedCell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.resolvedCell ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.resolvedCell

@[simp]
theorem resolvedCell_domain (R : PLCrossSeamReading chart G) (C : PLSeamTubeChart M chart) :
    (R.resolvedCell C).domain = G.domain := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.resolvedCell_domain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.resolvedCell_domain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.resolvedCell_domain ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.resolvedCell_domain

open _root_.Classical in
theorem resolvedCell_apply_of_mem (R : PLCrossSeamReading chart G)
    (C : PLSeamTubeChart M chart) {x : EuclideanSpace ℝ (Fin 2)}
    (hx : x ∈ R.tubeSource) :
    R.resolvedCell C x = chart (crossSeamResolve (R.coord x)) :=
  Set.piecewise_eq_of_mem _ _ _ hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.resolvedCell_apply_of_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.resolvedCell_apply_of_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.resolvedCell_apply_of_mem ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.resolvedCell_apply_of_mem

open _root_.Classical in
theorem resolvedCell_apply_of_notMem (R : PLCrossSeamReading chart G)
    (C : PLSeamTubeChart M chart) {x : EuclideanSpace ℝ (Fin 2)}
    (hx : x ∉ R.tubeSource) : R.resolvedCell C x = G x :=
  Set.piecewise_eq_of_notMem _ _ _ hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.resolvedCell_apply_of_notMem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.resolvedCell_apply_of_notMem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.resolvedCell_apply_of_notMem ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.resolvedCell_apply_of_notMem

theorem image_resolvedCell_subset (R : PLCrossSeamReading chart G)
    (C : PLSeamTubeChart M chart) :
    R.resolvedCell C '' (R.resolvedCell C).domain ⊆
      ⇑G '' G.domain ∪ chart '' spliceCylinder := by
  rintro _ ⟨x, hx, rfl⟩
  by_cases hxs : x ∈ R.tubeSource
  · refine Or.inr ⟨crossSeamResolve (R.coord x), R.mapsTo_resolve hxs, ?_⟩
    exact (R.resolvedCell_apply_of_mem C hxs).symm
  · exact Or.inl ⟨x, hx, (R.resolvedCell_apply_of_notMem C hxs).symm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.image_resolvedCell_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.image_resolvedCell_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.image_resolvedCell_subset ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.image_resolvedCell_subset

theorem mapsTo_resolvedCell_frontier (R : PLCrossSeamReading chart G)
    (C : PLSeamTubeChart M chart) :
    _root_.Set.MapsTo (R.resolvedCell C) (R.tubeSource ∩ frontier G.domain)
      (chart '' spliceEndDisks) := by
  rintro x ⟨hxs, hxf⟩
  refine ⟨crossSeamResolve (R.coord x), ?_, (R.resolvedCell_apply_of_mem C hxs).symm⟩
  exact crossSeamResolve_mem_spliceEndDisks (R.bijOn_coord.mapsTo hxs)
    ((R.boundary_iff_end x hxs).mp hxf)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.mapsTo_resolvedCell_frontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.mapsTo_resolvedCell_frontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.mapsTo_resolvedCell_frontier ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.mapsTo_resolvedCell_frontier

variable {D : SingularTwoCell M} {BdM B U : Set M} {hD : NormalSingularCellData D BdM B}
  {c : hD.singularSet.Branch}

open _root_.Classical in
noncomputable def toCrossSeamRegluedData (T : CrossSeamTubeData hD c U)
    (R : PLCrossSeamReading T.chart G) (C : PLSeamTubeChart M T.chart) :
    CrossSeamRegluedData T G where
  cell := R.resolvedCell C
  domain_eq := rfl
  coord := R.coord
  bijOn_coord := R.tubeSource_eq ▸ R.bijOn_coord
  reglued_eq := R.tubeSource_eq ▸ R.reglued_eq
  resolved_eq := by
    rw [← R.tubeSource_eq]
    intro x hx
    exact R.resolvedCell_apply_of_mem C hx
  eqOn_compl := by
    intro x hx
    refine R.resolvedCell_apply_of_notMem C fun hxs => ?_
    rw [R.tubeSource_eq] at hxs
    exact hx.2 hxs.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.toCrossSeamRegluedData then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.toCrossSeamRegluedData"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.toCrossSeamRegluedData ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.toCrossSeamRegluedData

theorem sourcePos_nonempty (R : PLCrossSeamReading chart G) : R.sourcePos.Nonempty := by
  obtain ⟨y, hy⟩ := bentSheetPos_nonempty
  obtain ⟨x, hx, -⟩ := R.isPLHomeomorphOn_pos.bijOn.surjOn hy
  exact ⟨x, hx⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.sourcePos_nonempty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.sourcePos_nonempty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.sourcePos_nonempty ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.sourcePos_nonempty

theorem sourceNeg_nonempty (R : PLCrossSeamReading chart G) : R.sourceNeg.Nonempty := by
  obtain ⟨y, hy⟩ := bentSheetNeg_nonempty
  obtain ⟨x, hx, -⟩ := R.isPLHomeomorphOn_neg.bijOn.surjOn hy
  exact ⟨x, hx⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.sourceNeg_nonempty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.sourceNeg_nonempty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.sourceNeg_nonempty ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.sourceNeg_nonempty

theorem source_ssubset_domain (R : PLCrossSeamReading chart G) :
    R.tubeSource ⊂ G.domain := by
  refine ⟨R.source_subset_domain, fun hsub => ?_⟩
  have hdom : G.domain = R.tubeSource :=
    Subset.antisymm hsub R.source_subset_domain
  obtain ⟨x, hx⟩ := R.sourcePos_nonempty
  obtain ⟨z, hz⟩ := R.sourceNeg_nonempty
  have hconn := G.isPLBall_domain.isConnected.isPreconnected
  obtain ⟨y, hy, hy1, hy2⟩ := hconn R.sourceNegᶜ R.sourcePosᶜ
    R.isPolyhedron_sourceNeg.isClosed.isOpen_compl
    R.isPolyhedron_sourcePos.isClosed.isOpen_compl
    (fun w hw => by
      rcases R.mem_tubeSource.mp (hdom ▸ hw) with hw' | hw'
      · exact Or.inl (Set.disjoint_left.mp R.disjoint_source hw')
      · exact Or.inr fun hw'' => Set.disjoint_left.mp R.disjoint_source hw'' hw')
    ⟨x, R.source_subset_domain (R.mem_tubeSource.mpr (Or.inl hx)),
      Set.disjoint_left.mp R.disjoint_source hx⟩
    ⟨z, R.source_subset_domain (R.mem_tubeSource.mpr (Or.inr hz)), fun hz' =>
      Set.disjoint_left.mp R.disjoint_source hz' hz⟩
  rcases R.mem_tubeSource.mp (hdom ▸ hy) with hy' | hy'
  · exact hy2 hy'
  · exact hy1 hy'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.source_ssubset_domain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.source_ssubset_domain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.source_ssubset_domain ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.source_ssubset_domain

theorem face_nonempty (R : PLCrossSeamReading chart G) : R.face.Nonempty := by
  obtain ⟨y, hy, hys⟩ := (_root_.Set.ssubset_iff_of_subset R.source_subset_domain).mp
    R.source_ssubset_domain
  refine ⟨y, ?_⟩
  rw [← R.tubeSource_union_face] at hy
  rcases hy with hy' | hy'
  · exact absurd hy' hys
  · exact hy'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.face_nonempty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.face_nonempty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.face_nonempty ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.face_nonempty

theorem corner_of_mem_face (R : PLCrossSeamReading chart G) {x : EuclideanSpace ℝ (Fin 2)}
    (hx : x ∈ R.tubeSource ∩ R.face) (hend : (R.coord x).2.2 = 0 ∨ (R.coord x).2.2 = 1) :
    x ∈ frontier G.domain ∧ (R.coord x).2 ∈ spliceEndDisks ∧
      (R.coord x).2.1 ∈ spliceSquareBoundary := by
  have hlat := R.overlap_lateral x hx
  refine ⟨(R.boundary_iff_end x hx.1).mpr hend, ⟨hlat.1.1, ?_⟩, hlat.1⟩
  rcases hend with h | h
  · exact Or.inl h
  · exact Or.inr (Set.mem_singleton_iff.mpr h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.corner_of_mem_face then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.corner_of_mem_face"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.corner_of_mem_face ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLCrossSeamReading.corner_of_mem_face

end PLCrossSeamReading

theorem isPiecewiseAffineOn_spliceEmbedding :
    IsPiecewiseAffineOn (⇑spliceEmbedding) spliceCylinder :=
  (isPiecewiseAffineOn_of_affine_of_isHPolytope spliceEmbedding.toLinearMap.toAffineMap
    isHPolytope_spliceCylinder).congr fun _ _ => rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_spliceEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_spliceEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_spliceEmbedding ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_spliceEmbedding

theorem isPolyhedron_image_spliceEmbedding :
    IsPolyhedron (⇑spliceEmbedding '' spliceCylinder) :=
  isHPolytope_spliceCylinder.isPolyhedron.image_of_isPiecewiseAffineOn
    isPiecewiseAffineOn_spliceEmbedding spliceEmbedding.injective.injOn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPolyhedron_image_spliceEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPolyhedron_image_spliceEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPolyhedron_image_spliceEmbedding ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPolyhedron_image_spliceEmbedding

theorem isPiecewiseAffineOn_spliceEmbedding_symm :
    IsPiecewiseAffineOn (⇑spliceEmbedding.symm) (⇑spliceEmbedding '' spliceCylinder) :=
  ((isPiecewiseAffineOn_of_affine spliceEmbedding.symm.toLinearMap.toAffineMap
    isOpen_univ).mono_of_isPolyhedron isPolyhedron_image_spliceEmbedding
      (_root_.Set.subset_univ _)).congr fun _ _ => rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_spliceEmbedding_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_spliceEmbedding_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_spliceEmbedding_symm ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_spliceEmbedding_symm

theorem nonempty_plSeamTubeChart_spliceEmbedding :
    Nonempty (PLSeamTubeChart (EuclideanSpace ℝ (Fin 3)) ⇑spliceEmbedding) := by
  obtain ⟨K, hfin, hspace⟩ := isHPolytope_spliceCylinder.isPolyhedron.exists_simplicialComplex
  have hbij : _root_.Set.BijOn (⇑spliceEmbedding) K.space (⇑spliceEmbedding '' spliceCylinder) := by
    rw [hspace]
    exact spliceEmbedding.injective.injOn.bijOn_image
  refine ⟨⟨⟨K, hfin, ⇑spliceEmbedding, hbij,
    spliceEmbedding.continuous.continuousOn, ?_, ?_⟩, hspace, rfl⟩⟩
  · intro e he
    have hrefl : e = OpenPartialHomeomorph.refl (EuclideanSpace ℝ (Fin 3)) :=
      chartedSpaceSelf_atlas.mp he
    subst hrefl
    have hset : K.space ∩ ⇑spliceEmbedding ⁻¹'
        (OpenPartialHomeomorph.refl (EuclideanSpace ℝ (Fin 3))).source = spliceCylinder := by
      rw [OpenPartialHomeomorph.refl_source, _root_.Set.preimage_univ, _root_.Set.inter_univ, hspace]
    rw [hset]
    exact isPiecewiseAffineOn_spliceEmbedding.congr fun _ _ => rfl
  · intro e he
    have hrefl : e = OpenPartialHomeomorph.refl (EuclideanSpace ℝ (Fin 3)) :=
      chartedSpaceSelf_atlas.mp he
    subst hrefl
    have hset : (OpenPartialHomeomorph.refl (EuclideanSpace ℝ (Fin 3))).target ∩
        (OpenPartialHomeomorph.refl (EuclideanSpace ℝ (Fin 3))).symm ⁻¹'
          (⇑spliceEmbedding '' spliceCylinder) = ⇑spliceEmbedding '' spliceCylinder := by
      rw [OpenPartialHomeomorph.refl_target, OpenPartialHomeomorph.refl_symm]
      exact _root_.Set.univ_inter _
    rw [hset]
    refine isPiecewiseAffineOn_spliceEmbedding_symm.congr fun y hy => ?_
    obtain ⟨x, hx, rfl⟩ := hy
    have hmem : spliceEmbedding x ∈ ⇑spliceEmbedding '' spliceCylinder := ⟨x, hx, rfl⟩
    have h1 : Function.invFunOn (⇑spliceEmbedding) K.space (spliceEmbedding x) = x :=
      spliceEmbedding.injective (hbij.invOn_invFunOn.2 hmem)
    change Function.invFunOn (⇑spliceEmbedding) K.space (spliceEmbedding x) =
      spliceEmbedding.symm (spliceEmbedding x)
    rw [h1, spliceEmbedding.symm_apply_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.nonempty_plSeamTubeChart_spliceEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.nonempty_plSeamTubeChart_spliceEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.nonempty_plSeamTubeChart_spliceEmbedding ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.nonempty_plSeamTubeChart_spliceEmbedding

end DifferentialGeometry.Topology.PiecewiseLinear
