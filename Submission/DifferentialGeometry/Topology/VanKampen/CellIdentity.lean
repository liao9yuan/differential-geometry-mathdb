/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import Mathlib.Topology.Homotopy.Product
import Submission.DifferentialGeometry.Topology.VanKampen.Evaluation
import Submission.DifferentialGeometry.Topology.VanKampen.HomotopyGrid

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.CategoryTheory _root_.Set _root_.unitInterval
open scoped _root_.unitInterval

universe u v

namespace DifferentialGeometry.Topology.VanKampen

noncomputable def convexSubtypeSegment {E : Type u} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {S : Set E} (hS : Convex ℝ S) (a b : S) : _root_.Path a b where
  toFun t := ⟨AffineMap.lineMap a.1 b.1 (t : ℝ), hS.lineMap_mem a.2 b.2 t.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    simp only [AffineMap.lineMap_apply_module]
    fun_prop
  source' := by
    apply Subtype.ext
    simp
  target' := by
    apply Subtype.ext
    simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.convexSubtypeSegment then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.convexSubtypeSegment"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.convexSubtypeSegment ``Submission.DifferentialGeometry.Topology.VanKampen.convexSubtypeSegment

noncomputable def convexSubtypePathHomotopy {E : Type u} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {S : Set E} (hS : Convex ℝ S) {a b : S} (p q : _root_.Path a b) :
    p.Homotopy q where
  toFun z := ⟨AffineMap.lineMap (p z.2).1 (q z.2).1 (z.1 : ℝ),
    hS.lineMap_mem (p z.2).2 (q z.2).2 z.1.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    simp only [AffineMap.lineMap_apply_module]
    fun_prop
  map_zero_left t := by
    apply Subtype.ext
    simp
  map_one_left t := by
    apply Subtype.ext
    simp
  prop' t s hs := by
    rcases hs with hs | hs
    · subst s
      apply Subtype.ext
      simp
    · rw [Set.mem_singleton_iff] at hs
      subst s
      apply Subtype.ext
      simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.convexSubtypePathHomotopy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.convexSubtypePathHomotopy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.convexSubtypePathHomotopy ``Submission.DifferentialGeometry.Topology.VanKampen.convexSubtypePathHomotopy

def gridCellSet {n : ℕ} (i j : Fin n) : Set (ℝ × ℝ) :=
  _root_.Set.Icc (standardTime n i.castSucc : ℝ) (standardTime n i.succ : ℝ) ×ˢ
    _root_.Set.Icc (standardTime n j.castSucc : ℝ) (standardTime n j.succ : ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.gridCellSet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.gridCellSet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.gridCellSet ``Submission.DifferentialGeometry.Topology.VanKampen.gridCellSet

abbrev GridCell {n : ℕ} (i j : Fin n) := ↥(gridCellSet i j)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.GridCell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.GridCell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.GridCell ``Submission.DifferentialGeometry.Topology.VanKampen.GridCell

theorem convex_gridCellSet {n : ℕ} (i j : Fin n) : Convex ℝ (gridCellSet i j) :=
  (convex_Icc _ _).prod (convex_Icc _ _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.convex_gridCellSet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.convex_gridCellSet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.convex_gridCellSet ``Submission.DifferentialGeometry.Topology.VanKampen.convex_gridCellSet

noncomputable def gridCell00 {n : ℕ} (hn : 0 < n) (i j : Fin n) : GridCell i j :=
  ⟨((standardTime n i.castSucc : ℝ), (standardTime n j.castSucc : ℝ)),
    ⟨⟨le_rfl, by exact_mod_cast standardTime_castSucc_le_succ hn i⟩,
      ⟨le_rfl, by exact_mod_cast standardTime_castSucc_le_succ hn j⟩⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.gridCell00 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.gridCell00"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.gridCell00 ``Submission.DifferentialGeometry.Topology.VanKampen.gridCell00

noncomputable def gridCell10 {n : ℕ} (hn : 0 < n) (i j : Fin n) : GridCell i j :=
  ⟨((standardTime n i.succ : ℝ), (standardTime n j.castSucc : ℝ)),
    ⟨⟨by exact_mod_cast standardTime_castSucc_le_succ hn i, le_rfl⟩,
      ⟨le_rfl, by exact_mod_cast standardTime_castSucc_le_succ hn j⟩⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.gridCell10 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.gridCell10"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.gridCell10 ``Submission.DifferentialGeometry.Topology.VanKampen.gridCell10

noncomputable def gridCell01 {n : ℕ} (hn : 0 < n) (i j : Fin n) : GridCell i j :=
  ⟨((standardTime n i.castSucc : ℝ), (standardTime n j.succ : ℝ)),
    ⟨⟨le_rfl, by exact_mod_cast standardTime_castSucc_le_succ hn i⟩,
      ⟨by exact_mod_cast standardTime_castSucc_le_succ hn j, le_rfl⟩⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.gridCell01 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.gridCell01"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.gridCell01 ``Submission.DifferentialGeometry.Topology.VanKampen.gridCell01

noncomputable def gridCell11 {n : ℕ} (hn : 0 < n) (i j : Fin n) : GridCell i j :=
  ⟨((standardTime n i.succ : ℝ), (standardTime n j.succ : ℝ)),
    ⟨⟨by exact_mod_cast standardTime_castSucc_le_succ hn i, le_rfl⟩,
      ⟨by exact_mod_cast standardTime_castSucc_le_succ hn j, le_rfl⟩⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.gridCell11 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.gridCell11"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.gridCell11 ``Submission.DifferentialGeometry.Topology.VanKampen.gridCell11

def gridCellInclusion {n : ℕ} (i j : Fin n) : C(GridCell i j, I × I) where
  toFun z :=
    (⟨z.1.1, (standardTime n i.castSucc).2.1.trans z.2.1.1,
        z.2.1.2.trans (standardTime n i.succ).2.2⟩,
      ⟨z.1.2, (standardTime n j.castSucc).2.1.trans z.2.2.1,
        z.2.2.2.trans (standardTime n j.succ).2.2⟩)
  continuous_toFun := by fun_prop

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.gridCellInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.gridCellInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.gridCellInclusion ``Submission.DifferentialGeometry.Topology.VanKampen.gridCellInclusion

def gridCellMap {X : Type u} [TopologicalSpace X] (H : C(I × I, X))
    {n : ℕ} (i j : Fin n) : C(GridCell i j, X) :=
  H.comp (gridCellInclusion i j)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.gridCellMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.gridCellMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.gridCellMap ``Submission.DifferentialGeometry.Topology.VanKampen.gridCellMap

noncomputable def cellBottom {n : ℕ} (hn : 0 < n) (i j : Fin n) :
    _root_.Path (gridCell00 hn i j) (gridCell10 hn i j) :=
  convexSubtypeSegment (convex_gridCellSet i j) _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.cellBottom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.cellBottom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.cellBottom ``Submission.DifferentialGeometry.Topology.VanKampen.cellBottom

noncomputable def cellRight {n : ℕ} (hn : 0 < n) (i j : Fin n) :
    _root_.Path (gridCell10 hn i j) (gridCell11 hn i j) :=
  convexSubtypeSegment (convex_gridCellSet i j) _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.cellRight then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.cellRight"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.cellRight ``Submission.DifferentialGeometry.Topology.VanKampen.cellRight

noncomputable def cellLeft {n : ℕ} (hn : 0 < n) (i j : Fin n) :
    _root_.Path (gridCell00 hn i j) (gridCell01 hn i j) :=
  convexSubtypeSegment (convex_gridCellSet i j) _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.cellLeft then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.cellLeft"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.cellLeft ``Submission.DifferentialGeometry.Topology.VanKampen.cellLeft

noncomputable def cellTop {n : ℕ} (hn : 0 < n) (i j : Fin n) :
    _root_.Path (gridCell01 hn i j) (gridCell11 hn i j) :=
  convexSubtypeSegment (convex_gridCellSet i j) _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.cellTop then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.cellTop"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.cellTop ``Submission.DifferentialGeometry.Topology.VanKampen.cellTop

noncomputable def gridBottom {X : Type u} [TopologicalSpace X] (H : C(I × I, X))
    {n : ℕ} (hn : 0 < n) (i j : Fin n) :=
  (cellBottom hn i j).map (gridCellMap H i j).continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.gridBottom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.gridBottom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.gridBottom ``Submission.DifferentialGeometry.Topology.VanKampen.gridBottom

noncomputable def gridRight {X : Type u} [TopologicalSpace X] (H : C(I × I, X))
    {n : ℕ} (hn : 0 < n) (i j : Fin n) :=
  (cellRight hn i j).map (gridCellMap H i j).continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.gridRight then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.gridRight"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.gridRight ``Submission.DifferentialGeometry.Topology.VanKampen.gridRight

noncomputable def gridLeft {X : Type u} [TopologicalSpace X] (H : C(I × I, X))
    {n : ℕ} (hn : 0 < n) (i j : Fin n) :=
  (cellLeft hn i j).map (gridCellMap H i j).continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.gridLeft then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.gridLeft"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.gridLeft ``Submission.DifferentialGeometry.Topology.VanKampen.gridLeft

noncomputable def gridTop {X : Type u} [TopologicalSpace X] (H : C(I × I, X))
    {n : ℕ} (hn : 0 < n) (i j : Fin n) :=
  (cellTop hn i j).map (gridCellMap H i j).continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.gridTop then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.gridTop"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.gridTop ``Submission.DifferentialGeometry.Topology.VanKampen.gridTop

noncomputable def gridCellParameterHomotopy {n : ℕ} (hn : 0 < n) (i j : Fin n) :
    ((cellBottom hn i j).trans (cellRight hn i j)).Homotopy
      ((cellLeft hn i j).trans (cellTop hn i j)) :=
  convexSubtypePathHomotopy (convex_gridCellSet i j)
    ((cellBottom hn i j).trans (cellRight hn i j))
    ((cellLeft hn i j).trans (cellTop hn i j))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.gridCellParameterHomotopy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.gridCellParameterHomotopy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.gridCellParameterHomotopy ``Submission.DifferentialGeometry.Topology.VanKampen.gridCellParameterHomotopy

noncomputable def gridCellBoundaryHomotopy {X : Type u} [TopologicalSpace X]
    (H : C(I × I, X)) {n : ℕ} (hn : 0 < n) (i j : Fin n) :
    (gridBottom H hn i j).trans (gridRight H hn i j) |>.Homotopy
      ((gridLeft H hn i j).trans (gridTop H hn i j)) where
  toFun z := gridCellMap H i j (gridCellParameterHomotopy hn i j z)
  continuous_toFun := (gridCellMap H i j).continuous.comp
    (gridCellParameterHomotopy hn i j).continuous
  map_zero_left t := by
    change gridCellMap H i j (gridCellParameterHomotopy hn i j (0, t)) =
      ((cellBottom hn i j).map (gridCellMap H i j).continuous).trans
        ((cellRight hn i j).map (gridCellMap H i j).continuous) t
    rw [← Path.map_trans]
    exact congrArg (gridCellMap H i j)
      ((gridCellParameterHomotopy hn i j).map_zero_left t)
  map_one_left t := by
    change gridCellMap H i j (gridCellParameterHomotopy hn i j (1, t)) =
      ((cellLeft hn i j).map (gridCellMap H i j).continuous).trans
        ((cellTop hn i j).map (gridCellMap H i j).continuous) t
    rw [← Path.map_trans]
    exact congrArg (gridCellMap H i j)
      ((gridCellParameterHomotopy hn i j).map_one_left t)
  prop' t s hs := by
    change gridCellMap H i j (gridCellParameterHomotopy hn i j (t, s)) =
      ((cellBottom hn i j).map (gridCellMap H i j).continuous).trans
        ((cellRight hn i j).map (gridCellMap H i j).continuous) s
    rw [← Path.map_trans]
    exact congrArg (gridCellMap H i j)
      ((gridCellParameterHomotopy hn i j).prop' t s hs)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.gridCellBoundaryHomotopy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.gridCellBoundaryHomotopy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.gridCellBoundaryHomotopy ``Submission.DifferentialGeometry.Topology.VanKampen.gridCellBoundaryHomotopy

theorem gridCellMap_mem_of_image_subset {X : Type u} [TopologicalSpace X]
    (H : C(I × I, X)) {A : Set X} {n : ℕ} (i j : Fin n)
    (hcell : H '' (_root_.Set.Icc (standardTime n i.castSucc) (standardTime n i.succ) ×ˢ
      _root_.Set.Icc (standardTime n j.castSucc) (standardTime n j.succ)) ⊆ A)
    (z : GridCell i j) : gridCellMap H i j z ∈ A := by
  apply hcell
  refine ⟨gridCellInclusion i j z, ?_, rfl⟩
  constructor
  · constructor
    · exact_mod_cast z.2.1.1
    · exact_mod_cast z.2.1.2
  · constructor
    · exact_mod_cast z.2.2.1
    · exact_mod_cast z.2.2.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.gridCellMap_mem_of_image_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.gridCellMap_mem_of_image_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.gridCellMap_mem_of_image_subset ``Submission.DifferentialGeometry.Topology.VanKampen.gridCellMap_mem_of_image_subset

def pathHomotopyIn {X : Type u} [TopologicalSpace X] {A : Set X} {x y : X}
    {p q : _root_.Path x y} (hp : _root_.Set.range p ⊆ A) (hq : _root_.Set.range q ⊆ A)
    (K : p.Homotopy q) (hK : ∀ z, K z ∈ A) :
    (pathIn A p hp).Homotopy (pathIn A q hq) where
  toFun z := ⟨K z, hK z⟩
  continuous_toFun := K.continuous.subtype_mk _
  map_zero_left t := by
    apply Subtype.ext
    exact K.map_zero_left t
  map_one_left t := by
    apply Subtype.ext
    exact K.map_one_left t
  prop' t s hs := by
    apply Subtype.ext
    exact K.prop' t s hs

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.pathHomotopyIn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.pathHomotopyIn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.pathHomotopyIn ``Submission.DifferentialGeometry.Topology.VanKampen.pathHomotopyIn

theorem LocalFunctorData.leftPathMap_eq_of_homotopyIn
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    {G : Type v} [_root_.CategoryTheory.Groupoid G] (F : LocalFunctorData U V G)
    (hcover : U ∪ V = _root_.Set.univ) {x y : X} {p q : _root_.Path x y}
    (hp : _root_.Set.range p ⊆ U) (hq : _root_.Set.range q ⊆ U) (K : p.Homotopy q)
    (hK : ∀ z, K z ∈ U) :
    F.leftPathMap hcover p hp = F.leftPathMap hcover q hq := by
  unfold LocalFunctorData.leftPathMap
  apply LocalFunctorData.normalizeHom_eq_of_heq
  exact heq_of_eq (congrArg F.left.map
    (Path.Homotopic.Quotient.eq.mpr ⟨pathHomotopyIn hp hq K hK⟩))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.leftPathMap_eq_of_homotopyIn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.leftPathMap_eq_of_homotopyIn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.leftPathMap_eq_of_homotopyIn ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.leftPathMap_eq_of_homotopyIn

theorem LocalFunctorData.rightPathMap_eq_of_homotopyIn
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    {G : Type v} [_root_.CategoryTheory.Groupoid G] (F : LocalFunctorData U V G)
    (hcover : U ∪ V = _root_.Set.univ) {x y : X} {p q : _root_.Path x y}
    (hp : _root_.Set.range p ⊆ V) (hq : _root_.Set.range q ⊆ V) (K : p.Homotopy q)
    (hK : ∀ z, K z ∈ V) :
    F.rightPathMap hcover p hp = F.rightPathMap hcover q hq := by
  unfold LocalFunctorData.rightPathMap
  apply LocalFunctorData.normalizeHom_eq_of_heq
  exact heq_of_eq (congrArg F.right.map
    (Path.Homotopic.Quotient.eq.mpr ⟨pathHomotopyIn hp hq K hK⟩))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rightPathMap_eq_of_homotopyIn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rightPathMap_eq_of_homotopyIn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rightPathMap_eq_of_homotopyIn ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rightPathMap_eq_of_homotopyIn

theorem range_gridBottom_subset {X : Type u} [TopologicalSpace X]
    (H : C(I × I, X)) {A : Set X} {n : ℕ} (hn : 0 < n) (i j : Fin n)
    (hcell : H '' (_root_.Set.Icc (standardTime n i.castSucc) (standardTime n i.succ) ×ˢ
      _root_.Set.Icc (standardTime n j.castSucc) (standardTime n j.succ)) ⊆ A) :
    range (gridBottom H hn i j) ⊆ A := by
  rintro _ ⟨t, rfl⟩
  exact gridCellMap_mem_of_image_subset H i j hcell ((cellBottom hn i j) t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.range_gridBottom_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.range_gridBottom_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.range_gridBottom_subset ``Submission.DifferentialGeometry.Topology.VanKampen.range_gridBottom_subset

theorem range_gridRight_subset {X : Type u} [TopologicalSpace X]
    (H : C(I × I, X)) {A : Set X} {n : ℕ} (hn : 0 < n) (i j : Fin n)
    (hcell : H '' (_root_.Set.Icc (standardTime n i.castSucc) (standardTime n i.succ) ×ˢ
      _root_.Set.Icc (standardTime n j.castSucc) (standardTime n j.succ)) ⊆ A) :
    range (gridRight H hn i j) ⊆ A := by
  rintro _ ⟨t, rfl⟩
  exact gridCellMap_mem_of_image_subset H i j hcell ((cellRight hn i j) t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.range_gridRight_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.range_gridRight_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.range_gridRight_subset ``Submission.DifferentialGeometry.Topology.VanKampen.range_gridRight_subset

theorem range_gridLeft_subset {X : Type u} [TopologicalSpace X]
    (H : C(I × I, X)) {A : Set X} {n : ℕ} (hn : 0 < n) (i j : Fin n)
    (hcell : H '' (_root_.Set.Icc (standardTime n i.castSucc) (standardTime n i.succ) ×ˢ
      _root_.Set.Icc (standardTime n j.castSucc) (standardTime n j.succ)) ⊆ A) :
    range (gridLeft H hn i j) ⊆ A := by
  rintro _ ⟨t, rfl⟩
  exact gridCellMap_mem_of_image_subset H i j hcell ((cellLeft hn i j) t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.range_gridLeft_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.range_gridLeft_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.range_gridLeft_subset ``Submission.DifferentialGeometry.Topology.VanKampen.range_gridLeft_subset

theorem range_gridTop_subset {X : Type u} [TopologicalSpace X]
    (H : C(I × I, X)) {A : Set X} {n : ℕ} (hn : 0 < n) (i j : Fin n)
    (hcell : H '' (_root_.Set.Icc (standardTime n i.castSucc) (standardTime n i.succ) ×ˢ
      _root_.Set.Icc (standardTime n j.castSucc) (standardTime n j.succ)) ⊆ A) :
    range (gridTop H hn i j) ⊆ A := by
  rintro _ ⟨t, rfl⟩
  exact gridCellMap_mem_of_image_subset H i j hcell ((cellTop hn i j) t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.range_gridTop_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.range_gridTop_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.range_gridTop_subset ``Submission.DifferentialGeometry.Topology.VanKampen.range_gridTop_subset

theorem gridCellBoundaryHomotopy_mem {X : Type u} [TopologicalSpace X]
    (H : C(I × I, X)) {A : Set X} {n : ℕ} (hn : 0 < n) (i j : Fin n)
    (hcell : H '' (_root_.Set.Icc (standardTime n i.castSucc) (standardTime n i.succ) ×ˢ
      _root_.Set.Icc (standardTime n j.castSucc) (standardTime n j.succ)) ⊆ A)
    (z : I × I) : gridCellBoundaryHomotopy H hn i j z ∈ A := by
  exact gridCellMap_mem_of_image_subset H i j hcell
    (gridCellParameterHomotopy hn i j z)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.gridCellBoundaryHomotopy_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.gridCellBoundaryHomotopy_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.gridCellBoundaryHomotopy_mem ``Submission.DifferentialGeometry.Topology.VanKampen.gridCellBoundaryHomotopy_mem

theorem LocalFunctorData.cell_boundary_of_side
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    {G : Type v} [_root_.CategoryTheory.Groupoid G] (F : LocalFunctorData U V G)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = _root_.Set.univ)
    (H : C(I × I, X)) {n : ℕ} (hn : 0 < n) (i j : Fin n) (side : CoverSide)
    (hcell : H '' (_root_.Set.Icc (standardTime n i.castSucc) (standardTime n i.succ) ×ˢ
      _root_.Set.Icc (standardTime n j.castSucc) (standardTime n j.succ)) ⊆ side.set U V) :
    F.rawEvaluation hU hV hcover (gridBottom H hn i j) ≫
        F.rawEvaluation hU hV hcover (gridRight H hn i j) =
      F.rawEvaluation hU hV hcover (gridLeft H hn i j) ≫
        F.rawEvaluation hU hV hcover (gridTop H hn i j) := by
  rw [← F.rawEvaluation_trans hU hV hcover (gridBottom H hn i j) (gridRight H hn i j),
    ← F.rawEvaluation_trans hU hV hcover (gridLeft H hn i j) (gridTop H hn i j)]
  have hbr : _root_.Set.range ((gridBottom H hn i j).trans (gridRight H hn i j)) ⊆
      side.set U V := by
    rw [_root_.Path.trans_range]
    exact _root_.Set.union_subset (range_gridBottom_subset H hn i j hcell)
      (range_gridRight_subset H hn i j hcell)
  have hlt : _root_.Set.range ((gridLeft H hn i j).trans (gridTop H hn i j)) ⊆
      side.set U V := by
    rw [_root_.Path.trans_range]
    exact _root_.Set.union_subset (range_gridLeft_subset H hn i j hcell)
      (range_gridTop_subset H hn i j hcell)
  have hK : ∀ z, gridCellBoundaryHomotopy H hn i j z ∈ side.set U V :=
    gridCellBoundaryHomotopy_mem H hn i j hcell
  cases side
  · rw [F.rawEvaluation_eq_leftPathMap hU hV hcover _ hbr,
      F.rawEvaluation_eq_leftPathMap hU hV hcover _ hlt]
    exact F.leftPathMap_eq_of_homotopyIn hcover hbr hlt
      (gridCellBoundaryHomotopy H hn i j) hK
  · rw [F.rawEvaluation_eq_rightPathMap hU hV hcover _ hbr,
      F.rawEvaluation_eq_rightPathMap hU hV hcover _ hlt]
    exact F.rightPathMap_eq_of_homotopyIn hcover hbr hlt
      (gridCellBoundaryHomotopy H hn i j) hK

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.cell_boundary_of_side then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.cell_boundary_of_side"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.cell_boundary_of_side ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.cell_boundary_of_side

theorem LocalFunctorData.cell_boundary
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    {G : Type v} [_root_.CategoryTheory.Groupoid G] (F : LocalFunctorData U V G)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = _root_.Set.univ)
    (H : C(I × I, X)) {n : ℕ} (hn : 0 < n) (hgrid : IsCoveredGrid H U V n)
    (i j : Fin n) :
    F.rawEvaluation hU hV hcover (gridBottom H hn i j) ≫
        F.rawEvaluation hU hV hcover (gridRight H hn i j) =
      F.rawEvaluation hU hV hcover (gridLeft H hn i j) ≫
        F.rawEvaluation hU hV hcover (gridTop H hn i j) := by
  rcases hgrid i j with hcell | hcell
  · exact F.cell_boundary_of_side hU hV hcover H hn i j .left hcell
  · exact F.cell_boundary_of_side hU hV hcover H hn i j .right hcell

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.cell_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.cell_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.cell_boundary ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.cell_boundary

end DifferentialGeometry.Topology.VanKampen
