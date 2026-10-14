/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import Submission.DifferentialGeometry.Topology.VanKampen.CellIdentity
import Submission.DifferentialGeometry.Topology.VanKampen.GroupoidTelescope

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

def homotopySquare {X : Type u} [TopologicalSpace X] {x y : X}
    {p q : _root_.Path x y} (K : p.Homotopy q) : C(I × I, X) where
  toFun z := K (z.2, z.1)
  continuous_toFun := K.continuous.comp (by fun_prop)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.homotopySquare then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.homotopySquare"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.homotopySquare ``Submission.DifferentialGeometry.Topology.VanKampen.homotopySquare

noncomputable def homotopyVerticalEdge {X : Type u} [TopologicalSpace X] {x y : X}
    {p q : _root_.Path x y} (K : p.Homotopy q) {n : ℕ} (k : Fin (n + 1)) (j : Fin n) :
    _root_.Path (K.eval (standardTime n j.castSucc) (standardTime n k))
      (K.eval (standardTime n j.succ) (standardTime n k)) where
  toFun t := K (Set.Icc.convexComb (standardTime n j.castSucc)
    (standardTime n j.succ) t, standardTime n k)
  continuous_toFun := K.continuous.comp (by fun_prop)
  source' := by simp
  target' := by simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.homotopyVerticalEdge then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.homotopyVerticalEdge"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.homotopyVerticalEdge ``Submission.DifferentialGeometry.Topology.VanKampen.homotopyVerticalEdge

theorem gridBottom_homotopySquare {X : Type u} [TopologicalSpace X] {x y : X}
    {p q : _root_.Path x y} (K : p.Homotopy q) {n : ℕ} (hn : 0 < n)
    (i j : Fin n) :
    gridBottom (homotopySquare K) hn i j =
      standardSubpath (K.eval (standardTime n j.castSucc)) i := by
  apply _root_.Path.ext
  funext t
  apply congrArg K
  apply Prod.ext
  · apply Subtype.ext
    change (((cellBottom hn i j) t).1.2 : ℝ) = standardTime n j.castSucc
    change (AffineMap.lineMap (gridCell00 hn i j).1 (gridCell10 hn i j).1 (t : ℝ)).2 = _
    rw [AffineMap.lineMap_apply_module]
    dsimp [gridCell00, gridCell10]
    ring
  · apply Subtype.ext
    change (((cellBottom hn i j) t).1.1 : ℝ) =
      (Set.Icc.convexComb (standardTime n i.castSucc) (standardTime n i.succ) t : ℝ)
    change (AffineMap.lineMap (gridCell00 hn i j).1 (gridCell10 hn i j).1 (t : ℝ)).1 = _
    rw [AffineMap.lineMap_apply_module]
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.gridBottom_homotopySquare then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.gridBottom_homotopySquare"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.gridBottom_homotopySquare ``Submission.DifferentialGeometry.Topology.VanKampen.gridBottom_homotopySquare

theorem gridTop_homotopySquare {X : Type u} [TopologicalSpace X] {x y : X}
    {p q : _root_.Path x y} (K : p.Homotopy q) {n : ℕ} (hn : 0 < n)
    (i j : Fin n) :
    gridTop (homotopySquare K) hn i j =
      standardSubpath (K.eval (standardTime n j.succ)) i := by
  apply _root_.Path.ext
  funext t
  apply congrArg K
  apply Prod.ext
  · apply Subtype.ext
    change (((cellTop hn i j) t).1.2 : ℝ) = standardTime n j.succ
    change (AffineMap.lineMap (gridCell01 hn i j).1 (gridCell11 hn i j).1 (t : ℝ)).2 = _
    rw [AffineMap.lineMap_apply_module]
    dsimp [gridCell01, gridCell11]
    ring
  · apply Subtype.ext
    change (((cellTop hn i j) t).1.1 : ℝ) =
      (Set.Icc.convexComb (standardTime n i.castSucc) (standardTime n i.succ) t : ℝ)
    change (AffineMap.lineMap (gridCell01 hn i j).1 (gridCell11 hn i j).1 (t : ℝ)).1 = _
    rw [AffineMap.lineMap_apply_module]
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.gridTop_homotopySquare then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.gridTop_homotopySquare"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.gridTop_homotopySquare ``Submission.DifferentialGeometry.Topology.VanKampen.gridTop_homotopySquare

theorem gridLeft_homotopySquare {X : Type u} [TopologicalSpace X] {x y : X}
    {p q : _root_.Path x y} (K : p.Homotopy q) {n : ℕ} (hn : 0 < n)
    (i j : Fin n) :
    gridLeft (homotopySquare K) hn i j = homotopyVerticalEdge K i.castSucc j := by
  apply _root_.Path.ext
  funext t
  apply congrArg K
  apply Prod.ext
  · apply Subtype.ext
    change (((cellLeft hn i j) t).1.2 : ℝ) =
      (Set.Icc.convexComb (standardTime n j.castSucc) (standardTime n j.succ) t : ℝ)
    change (AffineMap.lineMap (gridCell00 hn i j).1 (gridCell01 hn i j).1 (t : ℝ)).2 = _
    rw [AffineMap.lineMap_apply_module]
    rfl
  · apply Subtype.ext
    change (((cellLeft hn i j) t).1.1 : ℝ) = standardTime n i.castSucc
    change (AffineMap.lineMap (gridCell00 hn i j).1 (gridCell01 hn i j).1 (t : ℝ)).1 = _
    rw [AffineMap.lineMap_apply_module]
    dsimp [gridCell00, gridCell01]
    ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.gridLeft_homotopySquare then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.gridLeft_homotopySquare"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.gridLeft_homotopySquare ``Submission.DifferentialGeometry.Topology.VanKampen.gridLeft_homotopySquare

theorem gridRight_homotopySquare {X : Type u} [TopologicalSpace X] {x y : X}
    {p q : _root_.Path x y} (K : p.Homotopy q) {n : ℕ} (hn : 0 < n)
    (i j : Fin n) :
    gridRight (homotopySquare K) hn i j = homotopyVerticalEdge K i.succ j := by
  apply _root_.Path.ext
  funext t
  apply congrArg K
  apply Prod.ext
  · apply Subtype.ext
    change (((cellRight hn i j) t).1.2 : ℝ) =
      (Set.Icc.convexComb (standardTime n j.castSucc) (standardTime n j.succ) t : ℝ)
    change (AffineMap.lineMap (gridCell10 hn i j).1 (gridCell11 hn i j).1 (t : ℝ)).2 = _
    rw [AffineMap.lineMap_apply_module]
    rfl
  · apply Subtype.ext
    change (((cellRight hn i j) t).1.1 : ℝ) = standardTime n i.succ
    change (AffineMap.lineMap (gridCell10 hn i j).1 (gridCell11 hn i j).1 (t : ℝ)).1 = _
    rw [AffineMap.lineMap_apply_module]
    dsimp [gridCell10, gridCell11]
    ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.gridRight_homotopySquare then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.gridRight_homotopySquare"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.gridRight_homotopySquare ``Submission.DifferentialGeometry.Topology.VanKampen.gridRight_homotopySquare

theorem LocalFunctorData.rawEvaluation_heq_of_pointwise
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    {G : Type v} [_root_.CategoryTheory.Groupoid G] (F : LocalFunctorData U V G)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = _root_.Set.univ)
    {x y x' y' : X} (p : _root_.Path x y) (q : _root_.Path x' y')
    (h : ∀ t, p t = q t) :
    F.rawEvaluation hU hV hcover p ≍ F.rawEvaluation hU hV hcover q := by
  have hx : x = x' := p.source.symm.trans ((h 0).trans q.source)
  have hy : y = y' := p.target.symm.trans ((h 1).trans q.target)
  subst x'
  subst y'
  have hpq : p = q := by
    apply _root_.Path.ext
    funext t
    exact h t
  subst q
  exact HEq.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawEvaluation_heq_of_pointwise then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawEvaluation_heq_of_pointwise"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawEvaluation_heq_of_pointwise ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawEvaluation_heq_of_pointwise

theorem LocalFunctorData.rawEvaluation_eq_sidePathMap
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    {G : Type v} [_root_.CategoryTheory.Groupoid G] (F : LocalFunctorData U V G)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = _root_.Set.univ)
    {x y : X} (p : _root_.Path x y) (side : CoverSide)
    (hp : _root_.Set.range p ⊆ side.set U V) :
    F.rawEvaluation hU hV hcover p = F.sidePathMap hcover p side hp := by
  cases side
  · exact F.rawEvaluation_eq_leftPathMap hU hV hcover p hp
  · exact F.rawEvaluation_eq_rightPathMap hU hV hcover p hp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawEvaluation_eq_sidePathMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawEvaluation_eq_sidePathMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawEvaluation_eq_sidePathMap ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawEvaluation_eq_sidePathMap

noncomputable def LocalFunctorData.rawRowChain
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    {G : Type v} [_root_.CategoryTheory.Groupoid G] (F : LocalFunctorData U V G)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = _root_.Set.univ)
    {x y : X} {p q : _root_.Path x y} (K : p.Homotopy q)
    (n : ℕ) (r : Fin (n + 1)) : _root_.CategoryTheory.ComposableArrows G n :=
  ComposableArrows.mkOfObjOfMapSucc
    (fun k ↦ F.gluedObj hcover (K.eval (standardTime n r) (standardTime n k)))
    (fun i ↦ F.rawEvaluation hU hV hcover
      (standardSubpath (K.eval (standardTime n r)) i))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawRowChain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawRowChain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawRowChain ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawRowChain

theorem LocalFunctorData.rawRowChain_map_succ
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    {G : Type v} [_root_.CategoryTheory.Groupoid G] (F : LocalFunctorData U V G)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = _root_.Set.univ)
    {x y : X} {p q : _root_.Path x y} (K : p.Homotopy q)
    (n : ℕ) (r : Fin (n + 1)) (i : ℕ) (hi : i < n) :
    (F.rawRowChain hU hV hcover K n r).map' i (i + 1) =
      F.rawEvaluation hU hV hcover
        (standardSubpath (K.eval (standardTime n r)) ⟨i, hi⟩) := by
  apply ComposableArrows.mkOfObjOfMapSucc_map_succ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawRowChain_map_succ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawRowChain_map_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawRowChain_map_succ ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawRowChain_map_succ

theorem homotopyRow_isCovered_bottom {X : Type u} [TopologicalSpace X]
    {U V : Set X} {x y : X} {p q : _root_.Path x y} (K : p.Homotopy q)
    {n : ℕ} (hn : 0 < n) (hgrid : IsCoveredGrid (homotopySquare K) U V n)
    (j : Fin n) : Path.IsCovered (K.eval (standardTime n j.castSucc)) U V n := by
  intro i
  rcases hgrid i j with hcell | hcell
  · left
    rw [← gridBottom_homotopySquare K hn i j]
    exact range_gridBottom_subset (homotopySquare K) hn i j hcell
  · right
    rw [← gridBottom_homotopySquare K hn i j]
    exact range_gridBottom_subset (homotopySquare K) hn i j hcell

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.homotopyRow_isCovered_bottom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.homotopyRow_isCovered_bottom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.homotopyRow_isCovered_bottom ``Submission.DifferentialGeometry.Topology.VanKampen.homotopyRow_isCovered_bottom

theorem homotopyRow_isCovered_top {X : Type u} [TopologicalSpace X]
    {U V : Set X} {x y : X} {p q : _root_.Path x y} (K : p.Homotopy q)
    {n : ℕ} (hn : 0 < n) (hgrid : IsCoveredGrid (homotopySquare K) U V n)
    (j : Fin n) : Path.IsCovered (K.eval (standardTime n j.succ)) U V n := by
  intro i
  rcases hgrid i j with hcell | hcell
  · left
    rw [← gridTop_homotopySquare K hn i j]
    exact range_gridTop_subset (homotopySquare K) hn i j hcell
  · right
    rw [← gridTop_homotopySquare K hn i j]
    exact range_gridTop_subset (homotopySquare K) hn i j hcell

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.homotopyRow_isCovered_top then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.homotopyRow_isCovered_top"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.homotopyRow_isCovered_top ``Submission.DifferentialGeometry.Topology.VanKampen.homotopyRow_isCovered_top

set_option backward.isDefEq.respectTransparency false in
theorem LocalFunctorData.rawRowChain_eq_assignedChain
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    {G : Type v} [_root_.CategoryTheory.Groupoid G] (F : LocalFunctorData U V G)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = _root_.Set.univ)
    {x y : X} {p q : _root_.Path x y} (K : p.Homotopy q)
    {n : ℕ} (r : Fin (n + 1))
    (hp : Path.IsCovered (K.eval (standardTime n r)) U V n) :
    F.rawRowChain hU hV hcover K n r =
      F.assignedChain hcover (K.eval (standardTime n r))
        (CoverAssignment.ofIsCovered hp) := by
  unfold LocalFunctorData.rawRowChain LocalFunctorData.assignedChain
  congr 1
  funext i
  exact F.rawEvaluation_eq_sidePathMap hU hV hcover _ _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawRowChain_eq_assignedChain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawRowChain_eq_assignedChain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawRowChain_eq_assignedChain ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawRowChain_eq_assignedChain

theorem LocalFunctorData.rawRowChain_hom_heq
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    {G : Type v} [_root_.CategoryTheory.Groupoid G] (F : LocalFunctorData U V G)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = _root_.Set.univ)
    {x y : X} {p q : _root_.Path x y} (K : p.Homotopy q)
    {n : ℕ} (hn : 0 < n) (r : Fin (n + 1))
    (hp : Path.IsCovered (K.eval (standardTime n r)) U V n) :
    (F.rawRowChain hU hV hcover K n r).hom ≍
      F.rawEvaluation hU hV hcover (K.eval (standardTime n r)) := by
  rw [F.rawRowChain_eq_assignedChain hU hV hcover K r hp]
  rw [F.rawEvaluation_eq_covered hU hV hcover _ hn hp]
  unfold LocalFunctorData.coveredEvaluation LocalFunctorData.assignedEvaluation
  exact (LocalFunctorData.normalizeHom_heq _ _ _).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawRowChain_hom_heq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawRowChain_hom_heq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawRowChain_hom_heq ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawRowChain_hom_heq

noncomputable def LocalFunctorData.rawRowTransformation
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    {G : Type v} [_root_.CategoryTheory.Groupoid G] (F : LocalFunctorData U V G)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = _root_.Set.univ)
    {x y : X} {p q : _root_.Path x y} (K : p.Homotopy q)
    {n : ℕ} (hn : 0 < n) (hgrid : IsCoveredGrid (homotopySquare K) U V n)
    (j : Fin n) :
    F.rawRowChain hU hV hcover K n j.castSucc ⟶
      F.rawRowChain hU hV hcover K n j.succ :=
  ComposableArrows.homMk
    (fun k ↦ F.rawEvaluation hU hV hcover (homotopyVerticalEdge K k j))
    (by
      intro i hi
      rw [F.rawRowChain_map_succ hU hV hcover K n j.castSucc i hi,
        F.rawRowChain_map_succ hU hV hcover K n j.succ i hi]
      let k : Fin n := ⟨i, hi⟩
      change F.rawEvaluation hU hV hcover
          (standardSubpath (K.eval (standardTime n j.castSucc)) k) ≫
            F.rawEvaluation hU hV hcover (homotopyVerticalEdge K k.succ j) =
        F.rawEvaluation hU hV hcover (homotopyVerticalEdge K k.castSucc j) ≫
          F.rawEvaluation hU hV hcover
            (standardSubpath (K.eval (standardTime n j.succ)) k)
      rw [← gridBottom_homotopySquare K hn k j,
        ← gridRight_homotopySquare K hn k j,
        ← gridLeft_homotopySquare K hn k j,
        ← gridTop_homotopySquare K hn k j]
      exact F.cell_boundary hU hV hcover (homotopySquare K) hn hgrid k j)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawRowTransformation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawRowTransformation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawRowTransformation ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawRowTransformation

theorem LocalFunctorData.rawRowTransformation_app
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    {G : Type v} [_root_.CategoryTheory.Groupoid G] (F : LocalFunctorData U V G)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = _root_.Set.univ)
    {x y : X} {p q : _root_.Path x y} (K : p.Homotopy q)
    {n : ℕ} (hn : 0 < n) (hgrid : IsCoveredGrid (homotopySquare K) U V n)
    (j : Fin n) (k : Fin (n + 1)) :
    (F.rawRowTransformation hU hV hcover K hn hgrid j).app k =
      F.rawEvaluation hU hV hcover (homotopyVerticalEdge K k j) :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawRowTransformation_app then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawRowTransformation_app"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawRowTransformation_app ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawRowTransformation_app

theorem homotopyVerticalEdge_zero_apply {X : Type u} [TopologicalSpace X] {x y : X}
    {p q : _root_.Path x y} (K : p.Homotopy q) {n : ℕ}
    (j : Fin n) (t : I) : homotopyVerticalEdge K (0 : Fin (n + 1)) j t = x := by
  simp [homotopyVerticalEdge]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.homotopyVerticalEdge_zero_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.homotopyVerticalEdge_zero_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.homotopyVerticalEdge_zero_apply ``Submission.DifferentialGeometry.Topology.VanKampen.homotopyVerticalEdge_zero_apply

theorem homotopyVerticalEdge_last_apply {X : Type u} [TopologicalSpace X] {x y : X}
    {p q : _root_.Path x y} (K : p.Homotopy q) {n : ℕ} (hn : 0 < n)
    (j : Fin n) (t : I) : homotopyVerticalEdge K (Fin.last n) j t = y := by
  simp [homotopyVerticalEdge, standardTime_last hn]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.homotopyVerticalEdge_last_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.homotopyVerticalEdge_last_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.homotopyVerticalEdge_last_apply ``Submission.DifferentialGeometry.Topology.VanKampen.homotopyVerticalEdge_last_apply

theorem LocalFunctorData.rawRowTransformation_app_zero_heq
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    {G : Type v} [_root_.CategoryTheory.Groupoid G] (F : LocalFunctorData U V G)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = _root_.Set.univ)
    {x y : X} {p q : _root_.Path x y} (K : p.Homotopy q)
    {n : ℕ} (hn : 0 < n) (hgrid : IsCoveredGrid (homotopySquare K) U V n)
    (j : Fin n) :
    ComposableArrows.app' (F.rawRowTransformation hU hV hcover K hn hgrid j) 0 ≍
      𝟙 (F.gluedObj hcover x) := by
  change F.rawEvaluation hU hV hcover
      (homotopyVerticalEdge K (0 : Fin (n + 1)) j) ≍ 𝟙 (F.gluedObj hcover x)
  exact (F.rawEvaluation_heq_of_pointwise hU hV hcover
    (homotopyVerticalEdge K (0 : Fin (n + 1)) j) (_root_.Path.refl x)
      (homotopyVerticalEdge_zero_apply K j)).trans
        (heq_of_eq (F.rawEvaluation_refl hU hV hcover x))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawRowTransformation_app_zero_heq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawRowTransformation_app_zero_heq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawRowTransformation_app_zero_heq ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawRowTransformation_app_zero_heq

theorem LocalFunctorData.rawRowTransformation_app_last_heq
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    {G : Type v} [_root_.CategoryTheory.Groupoid G] (F : LocalFunctorData U V G)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = _root_.Set.univ)
    {x y : X} {p q : _root_.Path x y} (K : p.Homotopy q)
    {n : ℕ} (hn : 0 < n) (hgrid : IsCoveredGrid (homotopySquare K) U V n)
    (j : Fin n) :
    ComposableArrows.app' (F.rawRowTransformation hU hV hcover K hn hgrid j) n ≍
      𝟙 (F.gluedObj hcover y) := by
  change F.rawEvaluation hU hV hcover
      (homotopyVerticalEdge K (Fin.last n) j) ≍ 𝟙 (F.gluedObj hcover y)
  exact (F.rawEvaluation_heq_of_pointwise hU hV hcover
    (homotopyVerticalEdge K (Fin.last n) j) (_root_.Path.refl y)
      (homotopyVerticalEdge_last_apply K hn j)).trans
        (heq_of_eq (F.rawEvaluation_refl hU hV hcover y))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawRowTransformation_app_last_heq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawRowTransformation_app_last_heq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawRowTransformation_app_last_heq ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawRowTransformation_app_last_heq

theorem LocalFunctorData.normalizeHom_inv
    {G : Type v} [_root_.CategoryTheory.Groupoid G] {a a' b b' : G}
    (ha : a = a') (hb : b = b') (f : a' ⟶ b') :
    LocalFunctorData.normalizeHom hb ha (_root_.CategoryTheory.inv f) =
      inv (LocalFunctorData.normalizeHom ha hb f) := by
  subst a'
  subst b'
  simp [LocalFunctorData.normalizeHom]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.normalizeHom_inv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.normalizeHom_inv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.normalizeHom_inv ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.normalizeHom_inv

theorem LocalFunctorData.gluedObj_eq_rawRowChain_left
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    {G : Type v} [_root_.CategoryTheory.Groupoid G] (F : LocalFunctorData U V G)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = _root_.Set.univ)
    {x y : X} {p q : _root_.Path x y} (K : p.Homotopy q)
    (n : ℕ) (r : Fin (n + 1)) :
    F.gluedObj hcover x = (F.rawRowChain hU hV hcover K n r).left := by
  change F.gluedObj hcover x =
    F.gluedObj hcover (K.eval (standardTime n r) (standardTime n 0))
  apply congrArg (F.gluedObj hcover)
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.gluedObj_eq_rawRowChain_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.gluedObj_eq_rawRowChain_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.gluedObj_eq_rawRowChain_left ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.gluedObj_eq_rawRowChain_left

theorem LocalFunctorData.gluedObj_eq_rawRowChain_right
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    {G : Type v} [_root_.CategoryTheory.Groupoid G] (F : LocalFunctorData U V G)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = _root_.Set.univ)
    {x y : X} {p q : _root_.Path x y} (K : p.Homotopy q)
    {n : ℕ} (hn : 0 < n) (r : Fin (n + 1)) :
    F.gluedObj hcover y = (F.rawRowChain hU hV hcover K n r).right := by
  change F.gluedObj hcover y =
    F.gluedObj hcover (K.eval (standardTime n r) (standardTime n (Fin.last n)))
  apply congrArg (F.gluedObj hcover)
  simp [standardTime_last hn]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.gluedObj_eq_rawRowChain_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.gluedObj_eq_rawRowChain_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.gluedObj_eq_rawRowChain_right ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.gluedObj_eq_rawRowChain_right

theorem LocalFunctorData.rawEvaluation_eq_normalize_rawRowChain
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    {G : Type v} [_root_.CategoryTheory.Groupoid G] (F : LocalFunctorData U V G)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = _root_.Set.univ)
    {x y : X} {p q : _root_.Path x y} (K : p.Homotopy q)
    {n : ℕ} (hn : 0 < n) (r : Fin (n + 1))
    (hp : Path.IsCovered (K.eval (standardTime n r)) U V n) :
    F.rawEvaluation hU hV hcover (K.eval (standardTime n r)) =
      LocalFunctorData.normalizeHom
        (F.gluedObj_eq_rawRowChain_left hU hV hcover K n r)
        (F.gluedObj_eq_rawRowChain_right hU hV hcover K hn r)
        (F.rawRowChain hU hV hcover K n r).hom := by
  rw [F.rawEvaluation_eq_covered hU hV hcover _ hn hp]
  unfold LocalFunctorData.coveredEvaluation LocalFunctorData.assignedEvaluation
  apply LocalFunctorData.normalizeHom_eq_of_heq
  have hhom :
      (F.assignedChain hcover (K.eval (standardTime n r))
        (CoverAssignment.ofIsCovered hp)).hom ≍
        (F.rawRowChain hU hV hcover K n r).hom := by
    apply Functor.hcongr_hom
    exact (F.rawRowChain_eq_assignedChain hU hV hcover K r hp).symm
  exact hhom

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawEvaluation_eq_normalize_rawRowChain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawEvaluation_eq_normalize_rawRowChain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawEvaluation_eq_normalize_rawRowChain ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawEvaluation_eq_normalize_rawRowChain

theorem LocalFunctorData.rawEvaluation_eval_succ_eq
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    {G : Type v} [_root_.CategoryTheory.Groupoid G] (F : LocalFunctorData U V G)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = _root_.Set.univ)
    {x y : X} {p q : _root_.Path x y} (K : p.Homotopy q)
    {n : ℕ} (hn : 0 < n) (hgrid : IsCoveredGrid (homotopySquare K) U V n)
    (j : Fin n) :
    F.rawEvaluation hU hV hcover (K.eval (standardTime n j.succ)) =
      F.rawEvaluation hU hV hcover (K.eval (standardTime n j.castSucc)) := by
  let R := F.rawRowChain hU hV hcover K n j.castSucc
  let S := F.rawRowChain hU hV hcover K n j.succ
  let α : R ⟶ S := F.rawRowTransformation hU hV hcover K hn hgrid j
  have htel : S.hom =
      inv (ComposableArrows.app' α 0 (hi := Nat.zero_le n)) ≫ R.hom ≫
        ComposableArrows.app' α n (hi := le_rfl) :=
    groupoid_telescope α
  have hα0 : ComposableArrows.app' α 0 (hi := Nat.zero_le n) ≍
      𝟙 (F.gluedObj hcover x) := by
    exact F.rawRowTransformation_app_zero_heq hU hV hcover K hn hgrid j
  have hαn : ComposableArrows.app' α n (hi := le_rfl) ≍
      𝟙 (F.gluedObj hcover y) := by
    exact F.rawRowTransformation_app_last_heq hU hV hcover K hn hgrid j
  let rx : F.gluedObj hcover x = R.left :=
    F.gluedObj_eq_rawRowChain_left hU hV hcover K n j.castSucc
  let sx : F.gluedObj hcover x = S.left :=
    F.gluedObj_eq_rawRowChain_left hU hV hcover K n j.succ
  let ry : F.gluedObj hcover y = R.right :=
    F.gluedObj_eq_rawRowChain_right hU hV hcover K hn j.castSucc
  let sy : F.gluedObj hcover y = S.right :=
    F.gluedObj_eq_rawRowChain_right hU hV hcover K hn j.succ
  have hα0Norm : LocalFunctorData.normalizeHom rx sx
      (ComposableArrows.app' α 0 (hi := Nat.zero_le n)) = 𝟙 (F.gluedObj hcover x) := by
    calc
      LocalFunctorData.normalizeHom rx sx
          (ComposableArrows.app' α 0 (hi := Nat.zero_le n)) =
          LocalFunctorData.normalizeHom rfl rfl (𝟙 (F.gluedObj hcover x)) :=
        LocalFunctorData.normalizeHom_eq_of_heq rx rfl sx rfl _ _ hα0
      _ = 𝟙 (F.gluedObj hcover x) := LocalFunctorData.normalizeHom_id rfl
  have hαnNorm : LocalFunctorData.normalizeHom ry sy
      (ComposableArrows.app' α n (hi := le_rfl)) = 𝟙 (F.gluedObj hcover y) := by
    calc
      LocalFunctorData.normalizeHom ry sy
          (ComposableArrows.app' α n (hi := le_rfl)) =
          LocalFunctorData.normalizeHom rfl rfl (𝟙 (F.gluedObj hcover y)) :=
        LocalFunctorData.normalizeHom_eq_of_heq ry rfl sy rfl _ _ hαn
      _ = 𝟙 (F.gluedObj hcover y) := LocalFunctorData.normalizeHom_id rfl
  have hnorm : LocalFunctorData.normalizeHom sx sy S.hom =
      LocalFunctorData.normalizeHom rx ry R.hom := by
    rw [htel]
    rw [LocalFunctorData.normalizeHom_comp sx rx sy
      (_root_.CategoryTheory.inv (ComposableArrows.app' α 0 (hi := Nat.zero_le n)))
      (R.hom ≫ ComposableArrows.app' α n (hi := le_rfl))]
    rw [LocalFunctorData.normalizeHom_comp rx ry sy R.hom
      (ComposableArrows.app' α n (hi := le_rfl))]
    rw [LocalFunctorData.normalizeHom_inv rx sx,
      hα0Norm, hαnNorm]
    simp
  rw [F.rawEvaluation_eq_normalize_rawRowChain hU hV hcover K hn j.succ
      (homotopyRow_isCovered_top K hn hgrid j),
    F.rawEvaluation_eq_normalize_rawRowChain hU hV hcover K hn j.castSucc
      (homotopyRow_isCovered_bottom K hn hgrid j)]
  exact hnorm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawEvaluation_eval_succ_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawEvaluation_eval_succ_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawEvaluation_eval_succ_eq ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawEvaluation_eval_succ_eq

theorem LocalFunctorData.rawEvaluation_eq_of_homotopyGrid
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    {G : Type v} [_root_.CategoryTheory.Groupoid G] (F : LocalFunctorData U V G)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = _root_.Set.univ)
    {x y : X} {p q : _root_.Path x y} (K : p.Homotopy q)
    {n : ℕ} (hn : 0 < n) (hgrid : IsCoveredGrid (homotopySquare K) U V n) :
    F.rawEvaluation hU hV hcover p = F.rawEvaluation hU hV hcover q := by
  have hrows : ∀ (k : ℕ) (hk : k ≤ n),
      F.rawEvaluation hU hV hcover
          (K.eval (standardTime n ⟨k, Nat.lt_succ_of_le hk⟩)) =
        F.rawEvaluation hU hV hcover (K.eval (standardTime n 0)) := by
    intro k hk
    induction k with
    | zero => rfl
    | succ k ih =>
        have hklt : k < n := Nat.lt_of_succ_le hk
        let j : Fin n := ⟨k, hklt⟩
        calc
          F.rawEvaluation hU hV hcover
              (K.eval (standardTime n ⟨k + 1, Nat.lt_succ_of_le hk⟩)) =
              F.rawEvaluation hU hV hcover (K.eval (standardTime n j.succ)) := by
                rfl
          _ = F.rawEvaluation hU hV hcover
              (K.eval (standardTime n j.castSucc)) :=
                F.rawEvaluation_eval_succ_eq hU hV hcover K hn hgrid j
          _ = F.rawEvaluation hU hV hcover (K.eval (standardTime n 0)) :=
                ih (Nat.le_of_succ_le hk)
  have hlast := hrows n le_rfl
  have hfin : (⟨n, Nat.lt_succ_of_le (le_refl n)⟩ : Fin (n + 1)) = Fin.last n := by
    apply Fin.ext
    rfl
  rw [hfin, standardTime_last hn] at hlast
  simpa using hlast.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawEvaluation_eq_of_homotopyGrid then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawEvaluation_eq_of_homotopyGrid"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawEvaluation_eq_of_homotopyGrid ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawEvaluation_eq_of_homotopyGrid

theorem LocalFunctorData.rawEvaluation_eq_of_homotopy
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    {G : Type v} [_root_.CategoryTheory.Groupoid G] (F : LocalFunctorData U V G)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = _root_.Set.univ)
    {x y : X} {p q : _root_.Path x y} (K : p.Homotopy q) :
    F.rawEvaluation hU hV hcover p = F.rawEvaluation hU hV hcover q := by
  obtain ⟨n, hn, hgrid⟩ := exists_coveredGrid (homotopySquare K) hU hV hcover
  exact F.rawEvaluation_eq_of_homotopyGrid hU hV hcover K hn hgrid

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawEvaluation_eq_of_homotopy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawEvaluation_eq_of_homotopy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawEvaluation_eq_of_homotopy ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawEvaluation_eq_of_homotopy

theorem LocalFunctorData.rawEvaluation_eq_of_homotopic
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    {G : Type v} [_root_.CategoryTheory.Groupoid G] (F : LocalFunctorData U V G)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = _root_.Set.univ)
    {x y : X} {p q : _root_.Path x y} (hpq : p.Homotopic q) :
    F.rawEvaluation hU hV hcover p = F.rawEvaluation hU hV hcover q := by
  rcases hpq with ⟨K⟩
  exact F.rawEvaluation_eq_of_homotopy hU hV hcover K

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawEvaluation_eq_of_homotopic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawEvaluation_eq_of_homotopic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawEvaluation_eq_of_homotopic ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawEvaluation_eq_of_homotopic

end DifferentialGeometry.Topology.VanKampen
