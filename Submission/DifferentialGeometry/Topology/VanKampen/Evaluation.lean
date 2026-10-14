/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
import Mathlib.CategoryTheory.ComposableArrows.Basic
import Submission.DifferentialGeometry.Topology.VanKampen.CoveredPath

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.CategoryTheory _root_.Set

universe u v

namespace DifferentialGeometry.Topology.VanKampen

def interToLeft {X : Type u} [TopologicalSpace X] (U V : Set X) : C(↥(U ∩ V), ↥U) where
  toFun x := ⟨x.1, x.2.1⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.interToLeft then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.interToLeft"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.interToLeft ``Submission.DifferentialGeometry.Topology.VanKampen.interToLeft

def interToRight {X : Type u} [TopologicalSpace X] (U V : Set X) : C(↥(U ∩ V), ↥V) where
  toFun x := ⟨x.1, x.2.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.interToRight then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.interToRight"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.interToRight ``Submission.DifferentialGeometry.Topology.VanKampen.interToRight

structure LocalFunctorData {X : Type u} [TopologicalSpace X] (U V : Set X)
    (G : Type v) [_root_.CategoryTheory.Groupoid G] where
  left : FundamentalGroupoid U ⥤ G
  right : FundamentalGroupoid V ⥤ G
  compatibility :
    FundamentalGroupoid.map (interToLeft U V) ⋙ left =
      FundamentalGroupoid.map (interToRight U V) ⋙ right

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData

namespace LocalFunctorData

variable {X : Type u} [TopologicalSpace X] {U V : Set X}
  {G : Type v} [Groupoid G] (F : LocalFunctorData U V G)

noncomputable def gluedObj (hcover : U ∪ V = _root_.Set.univ) (x : X) : G := by
  classical
  by_cases hx : x ∈ U
  · exact F.left.obj ⟨⟨x, hx⟩⟩
  · have hxV : x ∈ V := by
      have : x ∈ U ∪ V := by rw [hcover]; trivial
      exact this.resolve_left hx
    exact F.right.obj ⟨⟨x, hxV⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.gluedObj then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.gluedObj"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.gluedObj ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.gluedObj

theorem gluedObj_eq_left (hcover : U ∪ V = _root_.Set.univ) {x : X} (hx : x ∈ U) :
    F.gluedObj hcover x = F.left.obj ⟨⟨x, hx⟩⟩ := by
  classical
  simp [gluedObj, hx]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.gluedObj_eq_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.gluedObj_eq_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.gluedObj_eq_left ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.gluedObj_eq_left

theorem gluedObj_eq_right (hcover : U ∪ V = _root_.Set.univ) {x : X} (hx : x ∈ V) :
    F.gluedObj hcover x = F.right.obj ⟨⟨x, hx⟩⟩ := by
  classical
  by_cases hxU : x ∈ U
  · let z : FundamentalGroupoid (↥(U ∩ V)) := ⟨⟨x, hxU, hx⟩⟩
    have h := Functor.congr_obj F.compatibility z
    simp only [gluedObj, hxU, ↓reduceDIte]
    convert h using 1
    · apply congrArg F.left.obj
      ext
      rfl
    · apply congrArg F.right.obj
      ext
      rfl
  · simp [gluedObj, hxU]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.gluedObj_eq_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.gluedObj_eq_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.gluedObj_eq_right ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.gluedObj_eq_right

def normalizeHom {a a' b b' : G} (ha : a = a') (hb : b = b') (f : a' ⟶ b') : a ⟶ b :=
  _root_.CategoryTheory.eqToHom ha ≫ f ≫ _root_.CategoryTheory.eqToHom hb.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.normalizeHom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.normalizeHom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.normalizeHom ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.normalizeHom

@[simp]
theorem normalizeHom_id {a a' : G} (ha : a = a') :
    normalizeHom ha ha (𝟙 a') = 𝟙 a := by
  subst ha
  simp [normalizeHom]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.normalizeHom_id then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.normalizeHom_id"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.normalizeHom_id ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.normalizeHom_id

theorem normalizeHom_comp {a a' b b' c c' : G}
    (ha : a = a') (hb : b = b') (hc : c = c')
    (f : a' ⟶ b') (g : b' ⟶ c') :
    normalizeHom ha hc (f ≫ g) = normalizeHom ha hb f ≫ normalizeHom hb hc g := by
  subst ha
  subst hb
  subst hc
  simp [normalizeHom]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.normalizeHom_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.normalizeHom_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.normalizeHom_comp ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.normalizeHom_comp

theorem normalizeHom_heq {a a' b b' : G} (ha : a = a') (hb : b = b')
    (f : a' ⟶ b') : normalizeHom ha hb f ≍ f :=
  (CategoryTheory.conj_eqToHom_iff_heq _ _ ha hb).1 rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.normalizeHom_heq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.normalizeHom_heq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.normalizeHom_heq ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.normalizeHom_heq

theorem normalizeHom_normalizeHom {a a' a'' b b' b'' : G}
    (ha : a = a') (ha' : a' = a'') (hb : b = b') (hb' : b' = b'')
    (f : a'' ⟶ b'') :
    normalizeHom ha hb (normalizeHom ha' hb' f) =
      normalizeHom (ha.trans ha') (hb.trans hb') f := by
  subst a'
  subst a''
  subst b'
  subst b''
  simp [normalizeHom]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.normalizeHom_normalizeHom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.normalizeHom_normalizeHom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.normalizeHom_normalizeHom ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.normalizeHom_normalizeHom

theorem normalizeHom_eq_of_heq {a a' a'' b b' b'' : G}
    (ha' : a = a') (ha'' : a = a'') (hb' : b = b') (hb'' : b = b'')
    (f : a' ⟶ b') (g : a'' ⟶ b'') (hfg : f ≍ g) :
    normalizeHom ha' hb' f = normalizeHom ha'' hb'' g := by
  subst a'
  subst a''
  subst b'
  subst b''
  cases hfg
  simp [normalizeHom]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.normalizeHom_eq_of_heq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.normalizeHom_eq_of_heq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.normalizeHom_eq_of_heq ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.normalizeHom_eq_of_heq

noncomputable def normalizedChain {n : ℕ} (obj localObj : Fin (n + 1) → G)
    (hObj : ∀ i, obj i = localObj i)
    (mapSucc : ∀ i : Fin n, localObj i.castSucc ⟶ localObj i.succ) :
    ComposableArrows G n :=
  ComposableArrows.mkOfObjOfMapSucc obj
    (fun i => normalizeHom (hObj i.castSucc) (hObj i.succ) (mapSucc i))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.normalizedChain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.normalizedChain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.normalizedChain ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.normalizedChain

noncomputable def normalizedChainOf {n : ℕ} (obj : Fin (n + 1) → G)
    (L : _root_.CategoryTheory.ComposableArrows G n) (hObj : ∀ i, obj i = L.obj i) : _root_.CategoryTheory.ComposableArrows G n :=
  ComposableArrows.mkOfObjOfMapSucc obj
    (fun i => normalizeHom (hObj i.castSucc) (hObj i.succ) (L.map' i (i + 1)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.normalizedChainOf then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.normalizedChainOf"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.normalizedChainOf ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.normalizedChainOf

set_option backward.isDefEq.respectTransparency false in
theorem normalizedChainOf_hom {n : ℕ} (obj : Fin (n + 1) → G)
    (L : _root_.CategoryTheory.ComposableArrows G n) (hObj : ∀ i, obj i = L.obj i) :
    (normalizedChainOf obj L hObj).hom =
      normalizeHom (hObj 0) (hObj (Fin.last n)) L.hom := by
  let N := normalizedChainOf obj L hObj
  let α : N ⟶ L := ComposableArrows.homMk
    (fun i => _root_.CategoryTheory.eqToHom (hObj i)) (by
      intro i hi
      dsimp only [N, normalizedChainOf]
      rw [ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ i hi]
      simp [normalizeHom])
  have hnat := ComposableArrows.naturality' α 0 n (Nat.zero_le n) le_rfl
  change N.hom ≫ _root_.CategoryTheory.eqToHom (hObj (Fin.last n)) = _root_.CategoryTheory.eqToHom (hObj 0) ≫ L.hom at hnat
  change N.hom = normalizeHom (hObj 0) (hObj (Fin.last n)) L.hom
  apply (_root_.CategoryTheory.cancel_mono (_root_.CategoryTheory.eqToHom (hObj (Fin.last n)))).1
  rw [hnat]
  simp [normalizeHom]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.normalizedChainOf_hom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.normalizedChainOf_hom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.normalizedChainOf_hom ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.normalizedChainOf_hom

set_option backward.isDefEq.respectTransparency false in
theorem normalizedChain_hom {n : ℕ} (obj localObj : Fin (n + 1) → G)
    (hObj : ∀ i, obj i = localObj i)
    (mapSucc : ∀ i : Fin n, localObj i.castSucc ⟶ localObj i.succ) :
    (normalizedChain obj localObj hObj mapSucc).hom =
      normalizeHom (hObj 0) (hObj (Fin.last n))
        (ComposableArrows.mkOfObjOfMapSucc localObj mapSucc).hom := by
  let N := normalizedChain obj localObj hObj mapSucc
  let L := ComposableArrows.mkOfObjOfMapSucc localObj mapSucc
  let α : N ⟶ L := ComposableArrows.homMk
    (fun i => _root_.CategoryTheory.eqToHom (hObj i)) (by
      intro i hi
      dsimp only [N, L, normalizedChain]
      rw [ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ i hi,
        ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ i hi]
      simp [normalizeHom])
  have hnat := ComposableArrows.naturality' α 0 n (Nat.zero_le n) le_rfl
  change N.hom ≫ _root_.CategoryTheory.eqToHom (hObj (Fin.last n)) = _root_.CategoryTheory.eqToHom (hObj 0) ≫ L.hom at hnat
  change N.hom = normalizeHom (hObj 0) (hObj (Fin.last n)) L.hom
  apply (_root_.CategoryTheory.cancel_mono (_root_.CategoryTheory.eqToHom (hObj (Fin.last n)))).1
  rw [hnat]
  simp [normalizeHom]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.normalizedChain_hom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.normalizedChain_hom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.normalizedChain_hom ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.normalizedChain_hom

end LocalFunctorData

def pathIn {X : Type u} [TopologicalSpace X] {x y : X} (A : Set X)
    (p : _root_.Path x y) (hp : _root_.Set.range p ⊆ A) :
    _root_.Path (⟨x, hp ⟨0, p.source⟩⟩ : A) (⟨y, hp ⟨1, p.target⟩⟩ : A) where
  toFun t := ⟨p t, hp ⟨t, rfl⟩⟩
  continuous_toFun := p.continuous.subtype_mk _
  source' := Subtype.ext p.source
  target' := Subtype.ext p.target

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.pathIn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.pathIn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.pathIn ``Submission.DifferentialGeometry.Topology.VanKampen.pathIn

theorem range_standardSubpath_subset {X : Type u} [TopologicalSpace X] {x y : X}
    {A : Set X} (p : _root_.Path x y) (hp : _root_.Set.range p ⊆ A) {n : ℕ} (i : Fin n) :
    range (standardSubpath p i) ⊆ A := by
  rintro z ⟨t, rfl⟩
  exact hp ⟨Set.Icc.convexComb (standardTime n i.castSucc)
    (standardTime n i.succ) t, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.range_standardSubpath_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.range_standardSubpath_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.range_standardSubpath_subset ``Submission.DifferentialGeometry.Topology.VanKampen.range_standardSubpath_subset

theorem pathIn_standardSubpath {X : Type u} [TopologicalSpace X] {x y : X}
    {A : Set X} (p : _root_.Path x y) (hp : _root_.Set.range p ⊆ A) {n : ℕ} (i : Fin n) :
    pathIn A (standardSubpath p i) (range_standardSubpath_subset p hp i) =
      standardSubpath (pathIn A p hp) i := by
  apply _root_.Path.ext
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.pathIn_standardSubpath then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.pathIn_standardSubpath"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.pathIn_standardSubpath ``Submission.DifferentialGeometry.Topology.VanKampen.pathIn_standardSubpath

theorem pathIn_map_interToLeft {X : Type u} [TopologicalSpace X] {x y : X}
    {U V : Set X} (p : _root_.Path x y) (hUV : _root_.Set.range p ⊆ U ∩ V)
    (hU : _root_.Set.range p ⊆ U) :
    (Path.Homotopic.Quotient.mk (pathIn (U ∩ V) p hUV)).map (interToLeft U V) =
      Path.Homotopic.Quotient.mk (pathIn U p hU) := by
  apply congrArg Path.Homotopic.Quotient.mk
  apply _root_.Path.ext
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.pathIn_map_interToLeft then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.pathIn_map_interToLeft"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.pathIn_map_interToLeft ``Submission.DifferentialGeometry.Topology.VanKampen.pathIn_map_interToLeft

theorem pathIn_map_interToRight {X : Type u} [TopologicalSpace X] {x y : X}
    {U V : Set X} (p : _root_.Path x y) (hUV : _root_.Set.range p ⊆ U ∩ V)
    (hV : _root_.Set.range p ⊆ V) :
    (Path.Homotopic.Quotient.mk (pathIn (U ∩ V) p hUV)).map (interToRight U V) =
      Path.Homotopic.Quotient.mk (pathIn V p hV) := by
  apply congrArg Path.Homotopic.Quotient.mk
  apply _root_.Path.ext
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.pathIn_map_interToRight then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.pathIn_map_interToRight"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.pathIn_map_interToRight ``Submission.DifferentialGeometry.Topology.VanKampen.pathIn_map_interToRight

noncomputable def standardPathChain {X : Type u} [TopologicalSpace X] {x y : X}
    (p : _root_.Path x y) (n : ℕ) : _root_.CategoryTheory.ComposableArrows (FundamentalGroupoid X) n where
  obj i := ⟨p (standardTime n i)⟩
  map {i j} _ := Path.Homotopic.Quotient.mk
    (p.subpath (standardTime n i) (standardTime n j))
  map_id i := by
    change Path.Homotopic.Quotient.mk
      (p.subpath (standardTime n i) (standardTime n i)) =
        Path.Homotopic.Quotient.mk (_root_.Path.refl (p (standardTime n i)))
    rw [_root_.Path.subpath_self]
  map_comp f g := by
    change Path.Homotopic.Quotient.mk
      (p.subpath (standardTime n _) (standardTime n _)) =
        Path.Homotopic.Quotient.trans
          (Path.Homotopic.Quotient.mk
            (p.subpath (standardTime n _) (standardTime n _)))
          (Path.Homotopic.Quotient.mk
            (p.subpath (standardTime n _) (standardTime n _)))
    rw [← Path.Homotopic.Quotient.mk_trans]
    exact Path.Homotopic.Quotient.eq.mpr
      ⟨(_root_.Path.Homotopy.subpathTransSubpath p _ _ _).symm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.standardPathChain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.standardPathChain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.standardPathChain ``Submission.DifferentialGeometry.Topology.VanKampen.standardPathChain

theorem standardPathChain_hom_heq {X : Type u} [TopologicalSpace X] {x y : X}
    (p : _root_.Path x y) {n : ℕ} (hn : 0 < n) :
    (standardPathChain p n).hom ≍ Path.Homotopic.Quotient.mk p := by
  change Path.Homotopic.Quotient.mk
    (p.subpath (standardTime n 0) (standardTime n (Fin.last n))) ≍
      Path.Homotopic.Quotient.mk p
  apply _root_.Path.Homotopic.hpath_hext
  intro t
  simp [_root_.Path.subpath, standardTime_last hn]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.standardPathChain_hom_heq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.standardPathChain_hom_heq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.standardPathChain_hom_heq ``Submission.DifferentialGeometry.Topology.VanKampen.standardPathChain_hom_heq

inductive CoverSide
  | left
  | right
  deriving DecidableEq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.CoverSide then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.CoverSide"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.CoverSide ``Submission.DifferentialGeometry.Topology.VanKampen.CoverSide

def CoverSide.set {X : Type u} (U V : Set X) : CoverSide → Set X
  | .left => U
  | .right => V

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Topology.VanKampen.CoverSide
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.CoverSide.set then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.CoverSide.set"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.CoverSide.set ``Submission.DifferentialGeometry.Topology.VanKampen.CoverSide.set

def blockEndpointFunctor (n k : ℕ) : Fin (n + 1) ⥤ Fin (n * k + 1) where
  obj i := ⟨i * k, Nat.lt_succ_of_le
    (Nat.mul_le_mul_right k (Nat.le_of_lt_succ i.isLt))⟩
  map {i j} hij := _root_.CategoryTheory.homOfLE (by
    apply Fin.mk_le_mk.mpr
    exact Nat.mul_le_mul_right k (Fin.mk_le_mk.mp (_root_.CategoryTheory.leOfHom hij)))
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.blockEndpointFunctor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.blockEndpointFunctor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.blockEndpointFunctor ``Submission.DifferentialGeometry.Topology.VanKampen.blockEndpointFunctor

def refinedBlockFunctor {n k : ℕ} (i : Fin n) : Fin (k + 1) ⥤ Fin (n * k + 1) where
  obj r := refinedVertex i r
  map {r s} hrs := _root_.CategoryTheory.homOfLE (by
    apply Fin.mk_le_mk.mpr
    exact Nat.add_le_add_left (Fin.mk_le_mk.mp (_root_.CategoryTheory.leOfHom hrs)) (i * k))
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.refinedBlockFunctor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.refinedBlockFunctor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.refinedBlockFunctor ``Submission.DifferentialGeometry.Topology.VanKampen.refinedBlockFunctor

def firstHalfVertexFunctor {n : ℕ} (hn : 0 < n) : Fin (n + 1) ⥤ Fin (2 * n + 1) where
  obj i := firstHalfVertex hn i
  map {i j} hij := _root_.CategoryTheory.homOfLE (by
    apply Fin.mk_le_mk.mpr
    exact Fin.mk_le_mk.mp (_root_.CategoryTheory.leOfHom hij))
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.firstHalfVertexFunctor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.firstHalfVertexFunctor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.firstHalfVertexFunctor ``Submission.DifferentialGeometry.Topology.VanKampen.firstHalfVertexFunctor

def secondHalfVertexFunctor (n : ℕ) : Fin (n + 1) ⥤ Fin (2 * n + 1) where
  obj i := secondHalfVertex i
  map {i j} hij := _root_.CategoryTheory.homOfLE (by
    apply Fin.mk_le_mk.mpr
    exact Nat.add_le_add_left (Fin.mk_le_mk.mp (_root_.CategoryTheory.leOfHom hij)) n)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.secondHalfVertexFunctor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.secondHalfVertexFunctor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.secondHalfVertexFunctor ``Submission.DifferentialGeometry.Topology.VanKampen.secondHalfVertexFunctor

theorem standardTime_blockEndpoint {n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    (i : Fin (n + 1)) :
    standardTime (n * k) ((blockEndpointFunctor n k).obj i) = standardTime n i := by
  apply Subtype.ext
  simp only [standardTime, blockEndpointFunctor, Nat.cast_mul]
  field_simp [Nat.ne_of_gt hn, Nat.ne_of_gt hk]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.standardTime_blockEndpoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.standardTime_blockEndpoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.standardTime_blockEndpoint ``Submission.DifferentialGeometry.Topology.VanKampen.standardTime_blockEndpoint

theorem refinedBlock_hom_heq_blockEndpoint_map {C : Type u} [Category.{v} C]
    {n k : ℕ} (R : _root_.CategoryTheory.ComposableArrows C (n * k)) (i : Fin n) :
    (R.whiskerLeft (refinedBlockFunctor i)).hom ≍
      (R.whiskerLeft (blockEndpointFunctor n k)).map'
        i (i + 1) (hjn := Nat.succ_le_iff.mpr i.isLt) := by
  let A := refinedBlockFunctor (k := k) i
  let B := blockEndpointFunctor n k
  let f : A.obj 0 ⟶ A.obj (Fin.last k) := A.map (_root_.CategoryTheory.homOfLE (Fin.zero_le _))
  let g : B.obj i.castSucc ⟶ B.obj i.succ :=
    B.map (_root_.CategoryTheory.homOfLE (Fin.mk_le_mk.mpr (Nat.le_succ i)))
  have h0 : A.obj 0 = B.obj i.castSucc := by
    apply Fin.ext
    simp [A, B, refinedBlockFunctor, refinedVertex, blockEndpointFunctor]
  have h1 : A.obj (Fin.last k) = B.obj i.succ := by
    apply Fin.ext
    simp [A, B, refinedBlockFunctor, refinedVertex, blockEndpointFunctor, Nat.add_mul]
  have hfg : f = _root_.CategoryTheory.eqToHom h0 ≫ g ≫ _root_.CategoryTheory.eqToHom h1.symm := Subsingleton.elim _ _
  change R.map f ≍ R.map g
  apply (CategoryTheory.conj_eqToHom_iff_heq _ _
    (congrArg R.obj h0) (congrArg R.obj h1)).mp
  rw [hfg, R.map_comp, R.map_comp]
  simp only [CategoryTheory.eqToHom_map]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.refinedBlock_hom_heq_blockEndpoint_map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.refinedBlock_hom_heq_blockEndpoint_map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.refinedBlock_hom_heq_blockEndpoint_map ``Submission.DifferentialGeometry.Topology.VanKampen.refinedBlock_hom_heq_blockEndpoint_map

theorem blockEndpoint_hom_heq {C : Type u} [Category.{v} C]
    {n k : ℕ} (R : _root_.CategoryTheory.ComposableArrows C (n * k)) :
    (R.whiskerLeft (blockEndpointFunctor n k)).hom ≍ R.hom := by
  let A := blockEndpointFunctor n k
  let f : A.obj 0 ⟶ A.obj (Fin.last n) := A.map (_root_.CategoryTheory.homOfLE (Fin.zero_le _))
  let g : (0 : Fin (n * k + 1)) ⟶ Fin.last (n * k) := _root_.CategoryTheory.homOfLE (Fin.zero_le _)
  have h0 : A.obj 0 = (0 : Fin (n * k + 1)) := by
    apply Fin.ext
    simp [A, blockEndpointFunctor]
  have h1 : A.obj (Fin.last n) = Fin.last (n * k) := by
    apply Fin.ext
    simp [A, blockEndpointFunctor]
  have hfg : f = _root_.CategoryTheory.eqToHom h0 ≫ g ≫ _root_.CategoryTheory.eqToHom h1.symm := Subsingleton.elim _ _
  change R.map f ≍ R.map g
  apply (CategoryTheory.conj_eqToHom_iff_heq _ _
    (congrArg R.obj h0) (congrArg R.obj h1)).mp
  rw [hfg, R.map_comp, R.map_comp]
  simp only [CategoryTheory.eqToHom_map]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.blockEndpoint_hom_heq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.blockEndpoint_hom_heq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.blockEndpoint_hom_heq ``Submission.DifferentialGeometry.Topology.VanKampen.blockEndpoint_hom_heq

theorem firstHalf_hom_heq_map_middle {C : Type u} [Category.{v} C]
    {n : ℕ} (hn : 0 < n) (R : _root_.CategoryTheory.ComposableArrows C (2 * n)) :
    (R.whiskerLeft (firstHalfVertexFunctor hn)).hom ≍
      R.map' 0 n (hjn := by omega) := by
  let A := firstHalfVertexFunctor hn
  let m : Fin (2 * n + 1) := ⟨n, by omega⟩
  let f : A.obj 0 ⟶ A.obj (Fin.last n) := A.map (_root_.CategoryTheory.homOfLE (Fin.zero_le _))
  let g : (0 : Fin (2 * n + 1)) ⟶ m := _root_.CategoryTheory.homOfLE (Fin.zero_le _)
  have h0 : A.obj 0 = (0 : Fin (2 * n + 1)) := by
    apply Fin.ext
    rfl
  have h1 : A.obj (Fin.last n) = m := by
    apply Fin.ext
    rfl
  have hfg : f = _root_.CategoryTheory.eqToHom h0 ≫ g ≫ _root_.CategoryTheory.eqToHom h1.symm := Subsingleton.elim _ _
  change R.map f ≍ R.map g
  apply (CategoryTheory.conj_eqToHom_iff_heq _ _
    (congrArg R.obj h0) (congrArg R.obj h1)).mp
  rw [hfg, R.map_comp, R.map_comp]
  simp only [CategoryTheory.eqToHom_map]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.firstHalf_hom_heq_map_middle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.firstHalf_hom_heq_map_middle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.firstHalf_hom_heq_map_middle ``Submission.DifferentialGeometry.Topology.VanKampen.firstHalf_hom_heq_map_middle

theorem secondHalf_hom_heq_map_middle {C : Type u} [Category.{v} C]
    {n : ℕ} (hn : 0 < n) (R : _root_.CategoryTheory.ComposableArrows C (2 * n)) :
    (R.whiskerLeft (secondHalfVertexFunctor n)).hom ≍
      R.map' n (2 * n) := by
  let A := secondHalfVertexFunctor n
  let m : Fin (2 * n + 1) := ⟨n, by omega⟩
  let f : A.obj 0 ⟶ A.obj (Fin.last n) := A.map (_root_.CategoryTheory.homOfLE (Fin.zero_le _))
  let g : m ⟶ Fin.last (2 * n) := _root_.CategoryTheory.homOfLE (by
    apply Fin.mk_le_mk.mpr
    omega)
  have h0 : A.obj 0 = m := by
    apply Fin.ext
    rfl
  have h1 : A.obj (Fin.last n) = Fin.last (2 * n) := by
    apply Fin.ext
    simp [A, secondHalfVertexFunctor, secondHalfVertex]
    omega
  have hfg : f = _root_.CategoryTheory.eqToHom h0 ≫ g ≫ _root_.CategoryTheory.eqToHom h1.symm := Subsingleton.elim _ _
  change R.map f ≍ R.map g
  apply (CategoryTheory.conj_eqToHom_iff_heq _ _
    (congrArg R.obj h0) (congrArg R.obj h1)).mp
  rw [hfg, R.map_comp, R.map_comp]
  simp only [CategoryTheory.eqToHom_map]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.secondHalf_hom_heq_map_middle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.secondHalf_hom_heq_map_middle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.secondHalf_hom_heq_map_middle ``Submission.DifferentialGeometry.Topology.VanKampen.secondHalf_hom_heq_map_middle

structure CoverAssignment {X : Type u} [TopologicalSpace X] {x y : X}
    (p : _root_.Path x y) (U V : Set X) (n : ℕ) where
  side : Fin n → CoverSide
  range_subset : ∀ i, _root_.Set.range (standardSubpath p i) ⊆ (side i).set U V

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.CoverAssignment then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.CoverAssignment"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.CoverAssignment ``Submission.DifferentialGeometry.Topology.VanKampen.CoverAssignment

theorem CoverAssignment.isCovered {X : Type u} [TopologicalSpace X] {x y : X}
    {p : _root_.Path x y} {U V : Set X} {n : ℕ} (σ : CoverAssignment p U V n) :
    Path.IsCovered p U V n := by
  intro i
  cases h : σ.side i
  · exact Or.inl (by simpa [CoverSide.set, h] using σ.range_subset i)
  · exact Or.inr (by simpa [CoverSide.set, h] using σ.range_subset i)

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Topology.VanKampen.CoverAssignment
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.CoverAssignment.isCovered then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.CoverAssignment.isCovered"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.CoverAssignment.isCovered ``Submission.DifferentialGeometry.Topology.VanKampen.CoverAssignment.isCovered

noncomputable def CoverAssignment.ofIsCovered {X : Type u} [TopologicalSpace X] {x y : X}
    {p : _root_.Path x y} {U V : Set X} {n : ℕ} (h : Path.IsCovered p U V n) :
    CoverAssignment p U V n := by
  classical
  refine ⟨fun i => if _root_.Set.range (standardSubpath p i) ⊆ U then .left else .right, ?_⟩
  intro i
  by_cases hU : _root_.Set.range (standardSubpath p i) ⊆ U
  · simp only [if_pos hU, CoverSide.set]
    exact hU
  · simp only [if_neg hU, CoverSide.set]
    exact (h i).resolve_left hU

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.CoverAssignment.ofIsCovered then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.CoverAssignment.ofIsCovered"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.CoverAssignment.ofIsCovered ``Submission.DifferentialGeometry.Topology.VanKampen.CoverAssignment.ofIsCovered

def CoverAssignment.constant {X : Type u} [TopologicalSpace X] {x y : X}
    {p : _root_.Path x y} {U V : Set X} (n : ℕ) (side : CoverSide)
    (hp : _root_.Set.range p ⊆ side.set U V) : CoverAssignment p U V n where
  side _ := side
  range_subset i := range_standardSubpath_subset p hp i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.CoverAssignment.constant then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.CoverAssignment.constant"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.CoverAssignment.constant ``Submission.DifferentialGeometry.Topology.VanKampen.CoverAssignment.constant

def CoverAssignment.refine {X : Type u} [TopologicalSpace X] {x y : X}
    {p : _root_.Path x y} {U V : Set X} {n : ℕ} (σ : CoverAssignment p U V n)
    {k : ℕ} (hn : 0 < n) (hk : 0 < k) : CoverAssignment p U V (n * k) where
  side j := σ.side ⟨j / k, (Nat.div_lt_iff_lt_mul hk).mpr j.isLt⟩
  range_subset j := by
    let i : Fin n := ⟨j / k, (Nat.div_lt_iff_lt_mul hk).mpr j.isLt⟩
    let r : Fin k := ⟨j % k, Nat.mod_lt j hk⟩
    have hj : refinedIndex i r = j := by
      apply Fin.ext
      simpa [refinedIndex, i, r, Nat.mul_comm] using Nat.div_add_mod j k
    rw [← hj]
    have hidx :
        (⟨(refinedIndex i r : ℕ) / k,
          (Nat.div_lt_iff_lt_mul hk).mpr (refinedIndex i r).isLt⟩ : Fin n) = i := by
      apply Fin.ext
      change (i * k + r) / k = i
      rw [Nat.mul_comm]
      simpa [Nat.div_eq_of_lt r.isLt] using Nat.mul_add_div hk i r
    rw [hidx]
    exact (range_standardSubpath_refined_subset p hn hk i r).trans (σ.range_subset i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.CoverAssignment.refine then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.CoverAssignment.refine"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.CoverAssignment.refine ``Submission.DifferentialGeometry.Topology.VanKampen.CoverAssignment.refine

def CoverAssignment.trans {X : Type u} [TopologicalSpace X] {x y z : X}
    {p : _root_.Path x y} {q : _root_.Path y z} {U V : Set X} {n : ℕ}
    (hn : 0 < n) (σ : CoverAssignment p U V n) (τ : CoverAssignment q U V n) :
    CoverAssignment (p.trans q) U V (2 * n) where
  side j := if hj : (j : ℕ) < n then σ.side ⟨j, hj⟩ else
    τ.side ⟨j - n, by omega⟩
  range_subset j := by
    split_ifs with hj
    · let i : Fin n := ⟨j, hj⟩
      have hji : firstHalfIndex hn i = j := by
        apply Fin.ext
        rfl
      rintro w ⟨s, rfl⟩
      have hpath : standardSubpath (p.trans q) j s = standardSubpath p i s := by
        rw [← hji]
        exact standardSubpath_trans_first_apply p q hn i s
      rw [hpath]
      exact σ.range_subset ⟨j, hj⟩ ⟨s, rfl⟩
    · let i : Fin n := ⟨j - n, by omega⟩
      rintro w ⟨s, rfl⟩
      have hji : secondHalfIndex hn i = j := by
        apply Fin.ext
        simp [secondHalfIndex, i]
        omega
      have hpath : standardSubpath (p.trans q) j s = standardSubpath q i s := by
        rw [← hji]
        exact standardSubpath_trans_second_apply p q hn i s
      rw [hpath]
      exact τ.range_subset i ⟨s, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.CoverAssignment.trans then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.CoverAssignment.trans"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.CoverAssignment.trans ``Submission.DifferentialGeometry.Topology.VanKampen.CoverAssignment.trans

namespace LocalFunctorData

variable {X : Type u} [TopologicalSpace X] {U V : Set X}
  {G : Type v} [Groupoid G] (F : LocalFunctorData U V G)

noncomputable def leftPathMap (hcover : U ∪ V = _root_.Set.univ) {x y : X}
    (p : _root_.Path x y) (hp : _root_.Set.range p ⊆ U) :
    F.gluedObj hcover x ⟶ F.gluedObj hcover y :=
  let px : x ∈ U := hp ⟨0, p.source⟩
  let py : y ∈ U := hp ⟨1, p.target⟩
  normalizeHom (F.gluedObj_eq_left hcover px) (F.gluedObj_eq_left hcover py)
    (F.left.map (Path.Homotopic.Quotient.mk (pathIn U p hp)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.leftPathMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.leftPathMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.leftPathMap ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.leftPathMap

noncomputable def rightPathMap (hcover : U ∪ V = _root_.Set.univ) {x y : X}
    (p : _root_.Path x y) (hp : _root_.Set.range p ⊆ V) :
    F.gluedObj hcover x ⟶ F.gluedObj hcover y :=
  let px : x ∈ V := hp ⟨0, p.source⟩
  let py : y ∈ V := hp ⟨1, p.target⟩
  normalizeHom (F.gluedObj_eq_right hcover px) (F.gluedObj_eq_right hcover py)
    (F.right.map (Path.Homotopic.Quotient.mk (pathIn V p hp)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rightPathMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rightPathMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rightPathMap ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rightPathMap

theorem leftPathMap_refl (hcover : U ∪ V = _root_.Set.univ) {x : X}
    (hp : _root_.Set.range (_root_.Path.refl x) ⊆ U) :
    F.leftPathMap hcover (_root_.Path.refl x) hp = 𝟙 (F.gluedObj hcover x) := by
  let qx : U := ⟨x, hp ⟨0, rfl⟩⟩
  have hq : pathIn U (_root_.Path.refl x) hp = _root_.Path.refl qx := by
    apply _root_.Path.ext
    rfl
  unfold leftPathMap
  rw [hq]
  change normalizeHom _ _ (F.left.map (𝟙 _)) = _
  rw [F.left.map_id]
  apply normalizeHom_id

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.leftPathMap_refl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.leftPathMap_refl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.leftPathMap_refl ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.leftPathMap_refl

theorem rightPathMap_refl (hcover : U ∪ V = _root_.Set.univ) {x : X}
    (hp : _root_.Set.range (_root_.Path.refl x) ⊆ V) :
    F.rightPathMap hcover (_root_.Path.refl x) hp = 𝟙 (F.gluedObj hcover x) := by
  let qx : V := ⟨x, hp ⟨0, rfl⟩⟩
  have hq : pathIn V (_root_.Path.refl x) hp = _root_.Path.refl qx := by
    apply _root_.Path.ext
    rfl
  unfold rightPathMap
  rw [hq]
  change normalizeHom _ _ (F.right.map (𝟙 _)) = _
  rw [F.right.map_id]
  apply normalizeHom_id

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rightPathMap_refl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rightPathMap_refl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rightPathMap_refl ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rightPathMap_refl

noncomputable def leftPathChain {x y : X} (p : _root_.Path x y)
    (hp : _root_.Set.range p ⊆ U) (n : ℕ) : _root_.CategoryTheory.ComposableArrows G n :=
  (F.left.mapComposableArrows n).obj (standardPathChain (pathIn U p hp) n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.leftPathChain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.leftPathChain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.leftPathChain ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.leftPathChain

noncomputable def rightPathChain {x y : X} (p : _root_.Path x y)
    (hp : _root_.Set.range p ⊆ V) (n : ℕ) : _root_.CategoryTheory.ComposableArrows G n :=
  (F.right.mapComposableArrows n).obj (standardPathChain (pathIn V p hp) n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rightPathChain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rightPathChain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rightPathChain ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rightPathChain

theorem leftPathChain_hom_heq {x y : X} (p : _root_.Path x y)
    (hp : _root_.Set.range p ⊆ U) {n : ℕ} (hn : 0 < n) :
    (F.leftPathChain p hp n).hom ≍
      F.left.map (Path.Homotopic.Quotient.mk (pathIn U p hp)) := by
  let qx : U := ⟨x, hp ⟨0, p.source⟩⟩
  let qy : U := ⟨y, hp ⟨1, p.target⟩⟩
  let q : _root_.Path qx qy := pathIn U p hp
  have h0 : (standardPathChain q n).left = FundamentalGroupoid.mk qx := by
    apply FundamentalGroupoid.ext
    change q (standardTime n 0) = qx
    rw [standardTime_zero, q.source]
  have h1 : (standardPathChain q n).right = FundamentalGroupoid.mk qy := by
    apply FundamentalGroupoid.ext
    change q (standardTime n (Fin.last n)) = qy
    rw [standardTime_last hn, q.target]
  have hraw : (standardPathChain q n).hom =
      eqToHom h0 ≫ Path.Homotopic.Quotient.mk q ≫ _root_.CategoryTheory.eqToHom h1.symm :=
    (CategoryTheory.conj_eqToHom_iff_heq _ _ h0 h1).2
      (standardPathChain_hom_heq q hn)
  change F.left.map (standardPathChain q n).hom ≍
    F.left.map (Path.Homotopic.Quotient.mk q)
  apply (CategoryTheory.conj_eqToHom_iff_heq _ _
    (congrArg F.left.obj h0) (congrArg F.left.obj h1)).mp
  rw [hraw, F.left.map_comp, F.left.map_comp]
  simp only [CategoryTheory.eqToHom_map]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.leftPathChain_hom_heq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.leftPathChain_hom_heq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.leftPathChain_hom_heq ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.leftPathChain_hom_heq

theorem rightPathChain_hom_heq {x y : X} (p : _root_.Path x y)
    (hp : _root_.Set.range p ⊆ V) {n : ℕ} (hn : 0 < n) :
    (F.rightPathChain p hp n).hom ≍
      F.right.map (Path.Homotopic.Quotient.mk (pathIn V p hp)) := by
  let qx : V := ⟨x, hp ⟨0, p.source⟩⟩
  let qy : V := ⟨y, hp ⟨1, p.target⟩⟩
  let q : _root_.Path qx qy := pathIn V p hp
  have h0 : (standardPathChain q n).left = FundamentalGroupoid.mk qx := by
    apply FundamentalGroupoid.ext
    change q (standardTime n 0) = qx
    rw [standardTime_zero, q.source]
  have h1 : (standardPathChain q n).right = FundamentalGroupoid.mk qy := by
    apply FundamentalGroupoid.ext
    change q (standardTime n (Fin.last n)) = qy
    rw [standardTime_last hn, q.target]
  have hraw : (standardPathChain q n).hom =
      eqToHom h0 ≫ Path.Homotopic.Quotient.mk q ≫ _root_.CategoryTheory.eqToHom h1.symm :=
    (CategoryTheory.conj_eqToHom_iff_heq _ _ h0 h1).2
      (standardPathChain_hom_heq q hn)
  change F.right.map (standardPathChain q n).hom ≍
    F.right.map (Path.Homotopic.Quotient.mk q)
  apply (CategoryTheory.conj_eqToHom_iff_heq _ _
    (congrArg F.right.obj h0) (congrArg F.right.obj h1)).mp
  rw [hraw, F.right.map_comp, F.right.map_comp]
  simp only [CategoryTheory.eqToHom_map]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rightPathChain_hom_heq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rightPathChain_hom_heq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rightPathChain_hom_heq ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rightPathChain_hom_heq

theorem gluedObj_eq_leftPathChain_obj (hcover : U ∪ V = _root_.Set.univ) {x y : X}
    (p : _root_.Path x y) (hp : _root_.Set.range p ⊆ U) (n : ℕ) (i : Fin (n + 1)) :
    F.gluedObj hcover (p (standardTime n i)) = (F.leftPathChain p hp n).obj i := by
  change F.gluedObj hcover (p (standardTime n i)) =
    F.left.obj ⟨(pathIn U p hp) (standardTime n i)⟩
  convert F.gluedObj_eq_left hcover (hp ⟨standardTime n i, rfl⟩) using 1
  apply congrArg F.left.obj
  ext
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.gluedObj_eq_leftPathChain_obj then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.gluedObj_eq_leftPathChain_obj"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.gluedObj_eq_leftPathChain_obj ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.gluedObj_eq_leftPathChain_obj

theorem gluedObj_eq_rightPathChain_obj (hcover : U ∪ V = _root_.Set.univ) {x y : X}
    (p : _root_.Path x y) (hp : _root_.Set.range p ⊆ V) (n : ℕ) (i : Fin (n + 1)) :
    F.gluedObj hcover (p (standardTime n i)) = (F.rightPathChain p hp n).obj i := by
  change F.gluedObj hcover (p (standardTime n i)) =
    F.right.obj ⟨(pathIn V p hp) (standardTime n i)⟩
  convert F.gluedObj_eq_right hcover (hp ⟨standardTime n i, rfl⟩) using 1
  apply congrArg F.right.obj
  ext
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.gluedObj_eq_rightPathChain_obj then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.gluedObj_eq_rightPathChain_obj"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.gluedObj_eq_rightPathChain_obj ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.gluedObj_eq_rightPathChain_obj

noncomputable def leftNormalizedPathChain (hcover : U ∪ V = _root_.Set.univ) {x y : X}
    (p : _root_.Path x y) (hp : _root_.Set.range p ⊆ U) (n : ℕ) : _root_.CategoryTheory.ComposableArrows G n :=
  normalizedChainOf (fun i => F.gluedObj hcover (p (standardTime n i)))
    (F.leftPathChain p hp n) (F.gluedObj_eq_leftPathChain_obj hcover p hp n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.leftNormalizedPathChain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.leftNormalizedPathChain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.leftNormalizedPathChain ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.leftNormalizedPathChain

noncomputable def rightNormalizedPathChain (hcover : U ∪ V = _root_.Set.univ) {x y : X}
    (p : _root_.Path x y) (hp : _root_.Set.range p ⊆ V) (n : ℕ) : _root_.CategoryTheory.ComposableArrows G n :=
  normalizedChainOf (fun i => F.gluedObj hcover (p (standardTime n i)))
    (F.rightPathChain p hp n) (F.gluedObj_eq_rightPathChain_obj hcover p hp n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rightNormalizedPathChain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rightNormalizedPathChain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rightNormalizedPathChain ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rightNormalizedPathChain

theorem leftPathMap_eq_rightPathMap (hcover : U ∪ V = _root_.Set.univ) {x y : X}
    (p : _root_.Path x y) (hpU : _root_.Set.range p ⊆ U) (hpV : _root_.Set.range p ⊆ V) :
    F.leftPathMap hcover p hpU = F.rightPathMap hcover p hpV := by
  let hpUV : _root_.Set.range p ⊆ U ∩ V := fun z hz => ⟨hpU hz, hpV hz⟩
  let q := Path.Homotopic.Quotient.mk (pathIn (U ∩ V) p hpUV)
  have hcompat := Functor.hcongr_hom F.compatibility q
  dsimp only [Functor.comp_map] at hcompat
  change F.left.map (q.map (interToLeft U V)) ≍
    F.right.map (q.map (interToRight U V)) at hcompat
  dsimp only [q] at hcompat
  have hleft :
      F.left.map ((Path.Homotopic.Quotient.mk (pathIn (U ∩ V) p hpUV)).map
          (interToLeft U V)) ≍
        F.left.map (Path.Homotopic.Quotient.mk (pathIn U p hpU)) := by
    rw [pathIn_map_interToLeft p hpUV hpU]
    apply HEq.rfl
  have hright :
      F.right.map ((Path.Homotopic.Quotient.mk (pathIn (U ∩ V) p hpUV)).map
          (interToRight U V)) ≍
        F.right.map (Path.Homotopic.Quotient.mk (pathIn V p hpV)) := by
    rw [pathIn_map_interToRight p hpUV hpV]
    apply HEq.rfl
  have hcompat' := hleft.symm.trans (hcompat.trans hright)
  apply normalizeHom_eq_of_heq _ _ _ _ _ _ hcompat'
  · apply F.gluedObj_eq_left
  · apply F.gluedObj_eq_right

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.leftPathMap_eq_rightPathMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.leftPathMap_eq_rightPathMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.leftPathMap_eq_rightPathMap ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.leftPathMap_eq_rightPathMap

noncomputable def sidePathMap (hcover : U ∪ V = _root_.Set.univ) {x y : X}
    (p : _root_.Path x y) (side : CoverSide)
    (hp : _root_.Set.range p ⊆ side.set U V) : F.gluedObj hcover x ⟶ F.gluedObj hcover y :=
  match side with
  | .left => F.leftPathMap hcover p (by simpa [CoverSide.set] using hp)
  | .right => F.rightPathMap hcover p (by simpa [CoverSide.set] using hp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.sidePathMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.sidePathMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.sidePathMap ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.sidePathMap

theorem sidePathMap_eq (hcover : U ∪ V = _root_.Set.univ) {x y : X}
    (p : _root_.Path x y) (s t : CoverSide)
    (hs : _root_.Set.range p ⊆ s.set U V) (ht : _root_.Set.range p ⊆ t.set U V) :
    F.sidePathMap hcover p s hs = F.sidePathMap hcover p t ht := by
  cases s <;> cases t
  · rfl
  · apply F.leftPathMap_eq_rightPathMap
  · symm
    apply F.leftPathMap_eq_rightPathMap
  · rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.sidePathMap_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.sidePathMap_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.sidePathMap_eq ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.sidePathMap_eq

theorem sidePathMap_heq_of_pointwise (hcover : U ∪ V = _root_.Set.univ)
    {x y x' y' : X} (p : _root_.Path x y) (q : _root_.Path x' y')
    (s t : CoverSide) (hp : _root_.Set.range p ⊆ s.set U V)
    (hq : _root_.Set.range q ⊆ t.set U V) (h : ∀ z, p z = q z) :
    F.sidePathMap hcover p s hp ≍ F.sidePathMap hcover q t hq := by
  have hx : x = x' := p.source.symm.trans ((h 0).trans q.source)
  have hy : y = y' := p.target.symm.trans ((h 1).trans q.target)
  subst x'
  subst y'
  have hpq : p = q := by
    apply _root_.Path.ext
    funext z
    exact h z
  subst q
  exact heq_of_eq (F.sidePathMap_eq hcover p s t hp hq)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.sidePathMap_heq_of_pointwise then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.sidePathMap_heq_of_pointwise"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.sidePathMap_heq_of_pointwise ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.sidePathMap_heq_of_pointwise

noncomputable def assignedSegment (hcover : U ∪ V = _root_.Set.univ) {x y : X}
    (p : _root_.Path x y) {n : ℕ} (σ : CoverAssignment p U V n) (i : Fin n) :
    F.gluedObj hcover (p (standardTime n i.castSucc)) ⟶
      F.gluedObj hcover (p (standardTime n i.succ)) :=
  F.sidePathMap hcover (standardSubpath p i) (σ.side i) (σ.range_subset i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedSegment then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedSegment"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedSegment ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedSegment

theorem assignedSegment_eq (hcover : U ∪ V = _root_.Set.univ) {x y : X}
    (p : _root_.Path x y) {n : ℕ} (σ τ : CoverAssignment p U V n) (i : Fin n) :
    F.assignedSegment hcover p σ i = F.assignedSegment hcover p τ i :=
  F.sidePathMap_eq hcover (standardSubpath p i) (σ.side i) (τ.side i)
    (σ.range_subset i) (τ.range_subset i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedSegment_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedSegment_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedSegment_eq ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedSegment_eq

noncomputable def assignedChain (hcover : U ∪ V = _root_.Set.univ) {x y : X}
    (p : _root_.Path x y) {n : ℕ} (σ : CoverAssignment p U V n) :
    ComposableArrows G n :=
  ComposableArrows.mkOfObjOfMapSucc
    (fun i => F.gluedObj hcover (p (standardTime n i)))
    (fun i => F.assignedSegment hcover p σ i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedChain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedChain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedChain ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedChain

theorem assignedChain_map_succ (hcover : U ∪ V = _root_.Set.univ) {x y : X}
    (p : _root_.Path x y) {n : ℕ} (σ : CoverAssignment p U V n)
    (i : ℕ) (hi : i < n) :
    (F.assignedChain hcover p σ).map' i (i + 1) =
      F.assignedSegment hcover p σ ⟨i, hi⟩ := by
  apply ComposableArrows.mkOfObjOfMapSucc_map_succ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedChain_map_succ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedChain_map_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedChain_map_succ ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedChain_map_succ

set_option backward.isDefEq.respectTransparency false in
theorem assignedChain_firstHalf_map_succ (hcover : U ∪ V = _root_.Set.univ)
    {x y z : X} (p : _root_.Path x y) (q : _root_.Path y z) {n : ℕ}
    (hn : 0 < n) (τ : CoverAssignment (p.trans q) U V (2 * n))
    (r : ℕ) (hr : r < n) :
    ((F.assignedChain hcover (p.trans q) τ).whiskerLeft
      (firstHalfVertexFunctor hn)).map' r (r + 1) =
      F.assignedSegment hcover (p.trans q) τ (firstHalfIndex hn ⟨r, hr⟩) := by
  unfold assignedChain
  change (ComposableArrows.mkOfObjOfMapSucc
      (fun j => F.gluedObj hcover ((p.trans q) (standardTime (2 * n) j)))
      (fun j => F.assignedSegment hcover (p.trans q) τ j)).map' r (r + 1) = _
  exact ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ r (by omega)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedChain_firstHalf_map_succ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedChain_firstHalf_map_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedChain_firstHalf_map_succ ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedChain_firstHalf_map_succ

set_option backward.isDefEq.respectTransparency false in
theorem assignedChain_secondHalf_map_succ (hcover : U ∪ V = _root_.Set.univ)
    {x y z : X} (p : _root_.Path x y) (q : _root_.Path y z) {n : ℕ}
    (hn : 0 < n) (τ : CoverAssignment (p.trans q) U V (2 * n))
    (r : ℕ) (hr : r < n) :
    ((F.assignedChain hcover (p.trans q) τ).whiskerLeft
      (secondHalfVertexFunctor n)).map' r (r + 1) =
      F.assignedSegment hcover (p.trans q) τ (secondHalfIndex hn ⟨r, hr⟩) := by
  have hbound : n + r + 1 ≤ 2 * n := by omega
  unfold assignedChain
  change (ComposableArrows.mkOfObjOfMapSucc
      (fun j => F.gluedObj hcover ((p.trans q) (standardTime (2 * n) j)))
      (fun j => F.assignedSegment hcover (p.trans q) τ j)).map'
        (n + r) (n + r + 1) (hjn := hbound) = _
  exact ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ (n + r)
    (secondHalfIndex hn ⟨r, hr⟩).isLt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedChain_secondHalf_map_succ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedChain_secondHalf_map_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedChain_secondHalf_map_succ ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedChain_secondHalf_map_succ

set_option backward.isDefEq.respectTransparency false in
theorem assignedChain_eq_trans_first (hcover : U ∪ V = _root_.Set.univ)
    {x y z : X} (p : _root_.Path x y) (q : _root_.Path y z) {n : ℕ}
    (hn : 0 < n) (σ : CoverAssignment p U V n) (τ : CoverAssignment q U V n) :
    F.assignedChain hcover p σ =
      (F.assignedChain hcover (p.trans q) (CoverAssignment.trans hn σ τ)).whiskerLeft
        (firstHalfVertexFunctor hn) := by
  let ξ := CoverAssignment.trans hn σ τ
  let hObj : ∀ i : Fin (n + 1),
      (F.assignedChain hcover p σ).obj i =
        ((F.assignedChain hcover (p.trans q) ξ).whiskerLeft
          (firstHalfVertexFunctor hn)).obj i := by
    intro i
    change F.gluedObj hcover (p (standardTime n i)) =
      F.gluedObj hcover ((p.trans q) (standardTime (2 * n) (firstHalfVertex hn i)))
    exact congrArg (F.gluedObj hcover) (trans_standardTime_first p q hn i).symm
  apply ComposableArrows.ext hObj
  intro r hr
  apply (CategoryTheory.conj_eqToHom_iff_heq _ _ (hObj _) (hObj _)).2
  rw [F.assignedChain_map_succ hcover p σ r hr,
    F.assignedChain_firstHalf_map_succ hcover p q hn ξ r hr]
  unfold assignedSegment
  apply F.sidePathMap_heq_of_pointwise
  intro s
  exact (standardSubpath_trans_first_apply p q hn ⟨r, hr⟩ s).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedChain_eq_trans_first then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedChain_eq_trans_first"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedChain_eq_trans_first ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedChain_eq_trans_first

set_option backward.isDefEq.respectTransparency false in
theorem assignedChain_eq_trans_second (hcover : U ∪ V = _root_.Set.univ)
    {x y z : X} (p : _root_.Path x y) (q : _root_.Path y z) {n : ℕ}
    (hn : 0 < n) (σ : CoverAssignment p U V n) (τ : CoverAssignment q U V n) :
    F.assignedChain hcover q τ =
      (F.assignedChain hcover (p.trans q) (CoverAssignment.trans hn σ τ)).whiskerLeft
        (secondHalfVertexFunctor n) := by
  let ξ := CoverAssignment.trans hn σ τ
  let hObj : ∀ i : Fin (n + 1),
      (F.assignedChain hcover q τ).obj i =
        ((F.assignedChain hcover (p.trans q) ξ).whiskerLeft
          (secondHalfVertexFunctor n)).obj i := by
    intro i
    change F.gluedObj hcover (q (standardTime n i)) =
      F.gluedObj hcover ((p.trans q) (standardTime (2 * n) (secondHalfVertex i)))
    exact congrArg (F.gluedObj hcover) (trans_standardTime_second p q hn i).symm
  apply ComposableArrows.ext hObj
  intro r hr
  apply (CategoryTheory.conj_eqToHom_iff_heq _ _ (hObj _) (hObj _)).2
  rw [F.assignedChain_map_succ hcover q τ r hr,
    F.assignedChain_secondHalf_map_succ hcover p q hn ξ r hr]
  unfold assignedSegment
  apply F.sidePathMap_heq_of_pointwise
  intro s
  exact (standardSubpath_trans_second_apply p q hn ⟨r, hr⟩ s).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedChain_eq_trans_second then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedChain_eq_trans_second"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedChain_eq_trans_second ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedChain_eq_trans_second

set_option backward.isDefEq.respectTransparency false in
theorem assignedChain_refinedBlock_map_succ (hcover : U ∪ V = _root_.Set.univ)
    {x y : X} (p : _root_.Path x y) {n k : ℕ}
    (τ : CoverAssignment p U V (n * k)) (i : Fin n)
    (r : ℕ) (hr : r < k) :
    ((F.assignedChain hcover p τ).whiskerLeft (refinedBlockFunctor i)).map'
        r (r + 1) =
      F.assignedSegment hcover p τ (refinedIndex i ⟨r, hr⟩) := by
  have hblock : i * k + r + 1 ≤ n * k := by
    calc
      i * k + r + 1 ≤ i * k + k := by omega
      _ = (i + 1) * k := by rw [Nat.add_mul, one_mul]
      _ ≤ n * k := Nat.mul_le_mul_right k (Nat.succ_le_iff.mpr i.isLt)
  unfold assignedChain
  change (ComposableArrows.mkOfObjOfMapSucc
      (fun j => F.gluedObj hcover (p (standardTime (n * k) j)))
      (fun j => F.assignedSegment hcover p τ j)).map'
        (i * k + r) (i * k + r + 1) (hjn := hblock) = _
  exact ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ (i * k + r)
    (refinedIndex i ⟨r, hr⟩).isLt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedChain_refinedBlock_map_succ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedChain_refinedBlock_map_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedChain_refinedBlock_map_succ ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedChain_refinedBlock_map_succ

set_option backward.isDefEq.respectTransparency false in
theorem assignedChain_standardSubpath_eq_refinedBlock (hcover : U ∪ V = _root_.Set.univ)
    {x y : X} (p : _root_.Path x y) {n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    (σ : CoverAssignment p U V n) (i : Fin n) :
    F.assignedChain hcover (standardSubpath p i)
        (CoverAssignment.constant k (σ.side i) (σ.range_subset i)) =
      (F.assignedChain hcover p (σ.refine hn hk)).whiskerLeft (refinedBlockFunctor i) := by
  let hObj : ∀ r : Fin (k + 1),
      (F.assignedChain hcover (standardSubpath p i)
        (CoverAssignment.constant k (σ.side i) (σ.range_subset i))).obj r =
      ((F.assignedChain hcover p (σ.refine hn hk)).whiskerLeft
        (refinedBlockFunctor i)).obj r := by
    intro r
    change F.gluedObj hcover (standardSubpath p i (standardTime k r)) =
      F.gluedObj hcover (p (standardTime (n * k) (refinedVertex i r)))
    exact congrArg (F.gluedObj hcover) (standardSubpath_refinedVertex p hn hk i r)
  apply ComposableArrows.ext hObj
  intro r hr
  apply (CategoryTheory.conj_eqToHom_iff_heq _ _ (hObj _) (hObj _)).2
  rw [F.assignedChain_map_succ hcover _ _ r hr]
  rw [F.assignedChain_refinedBlock_map_succ hcover p (σ.refine hn hk) i r hr]
  change F.assignedSegment hcover (standardSubpath p i)
      (CoverAssignment.constant k (σ.side i) (σ.range_subset i)) ⟨r, hr⟩ ≍
    F.assignedSegment hcover p (σ.refine hn hk) (refinedIndex i ⟨r, hr⟩)
  unfold assignedSegment
  apply F.sidePathMap_heq_of_pointwise
  intro s
  exact (standardSubpath_refined_apply p hn hk i ⟨r, hr⟩ s).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedChain_standardSubpath_eq_refinedBlock then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedChain_standardSubpath_eq_refinedBlock"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedChain_standardSubpath_eq_refinedBlock ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedChain_standardSubpath_eq_refinedBlock

set_option backward.isDefEq.respectTransparency false in
theorem assignedChain_constant_left (hcover : U ∪ V = _root_.Set.univ) {x y : X}
    (p : _root_.Path x y) (hp : _root_.Set.range p ⊆ U) (n : ℕ) :
    F.assignedChain hcover p (CoverAssignment.constant n .left hp) =
      F.leftNormalizedPathChain hcover p hp n := by
  unfold assignedChain leftNormalizedPathChain normalizedChainOf
  congr 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedChain_constant_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedChain_constant_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedChain_constant_left ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedChain_constant_left

set_option backward.isDefEq.respectTransparency false in
theorem assignedChain_constant_right (hcover : U ∪ V = _root_.Set.univ) {x y : X}
    (p : _root_.Path x y) (hp : _root_.Set.range p ⊆ V) (n : ℕ) :
    F.assignedChain hcover p (CoverAssignment.constant n .right hp) =
      F.rightNormalizedPathChain hcover p hp n := by
  unfold assignedChain rightNormalizedPathChain normalizedChainOf
  congr 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedChain_constant_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedChain_constant_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedChain_constant_right ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedChain_constant_right

theorem assignedChain_eq (hcover : U ∪ V = _root_.Set.univ) {x y : X}
    (p : _root_.Path x y) {n : ℕ} (σ τ : CoverAssignment p U V n) :
    F.assignedChain hcover p σ = F.assignedChain hcover p τ := by
  unfold assignedChain
  congr 1
  funext i
  exact F.assignedSegment_eq hcover p σ τ i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedChain_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedChain_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedChain_eq ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedChain_eq

noncomputable def assignedEvaluation (hcover : U ∪ V = _root_.Set.univ) {x y : X}
    (p : _root_.Path x y) {n : ℕ} (hn : 0 < n) (σ : CoverAssignment p U V n) :
    F.gluedObj hcover x ⟶ F.gluedObj hcover y :=
  normalizeHom
    (by simp [assignedChain, standardTime_zero])
    (by
      change F.gluedObj hcover y = F.gluedObj hcover (p (standardTime n (Fin.last n)))
      rw [standardTime_last hn, p.target])
    (F.assignedChain hcover p σ).hom

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedEvaluation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedEvaluation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedEvaluation ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedEvaluation

theorem assignedEvaluation_eq (hcover : U ∪ V = _root_.Set.univ) {x y : X}
    (p : _root_.Path x y) {n : ℕ} (hn : 0 < n) (σ τ : CoverAssignment p U V n) :
    F.assignedEvaluation hcover p hn σ = F.assignedEvaluation hcover p hn τ := by
  have hchain := F.assignedChain_eq hcover p σ τ
  have hhom : (F.assignedChain hcover p σ).hom ≍
      (F.assignedChain hcover p τ).hom := by
    apply Functor.hcongr_hom hchain
  apply normalizeHom_eq_of_heq _ _ _ _ _ _ hhom

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedEvaluation_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedEvaluation_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedEvaluation_eq ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedEvaluation_eq

theorem assignedEvaluation_constant_left (hcover : U ∪ V = _root_.Set.univ) {x y : X}
    (p : _root_.Path x y) (hp : _root_.Set.range p ⊆ U) {n : ℕ} (hn : 0 < n) :
    F.assignedEvaluation hcover p hn (CoverAssignment.constant n .left hp) =
      F.leftPathMap hcover p hp := by
  have hchain := F.assignedChain_constant_left hcover p hp n
  have hhom : (F.assignedChain hcover p (CoverAssignment.constant n .left hp)).hom ≍
      (F.leftNormalizedPathChain hcover p hp n).hom := by
    apply Functor.hcongr_hom hchain
  have hnormalized : (F.leftNormalizedPathChain hcover p hp n).hom ≍
      (F.leftPathChain p hp n).hom := by
    unfold leftNormalizedPathChain
    rw [normalizedChainOf_hom]
    apply normalizeHom_heq
  have htotal : (F.assignedChain hcover p (CoverAssignment.constant n .left hp)).hom ≍
      F.left.map (Path.Homotopic.Quotient.mk (pathIn U p hp)) :=
    hhom.trans (hnormalized.trans (F.leftPathChain_hom_heq p hp hn))
  unfold assignedEvaluation leftPathMap
  apply normalizeHom_eq_of_heq _ _ _ _ _ _ htotal

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedEvaluation_constant_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedEvaluation_constant_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedEvaluation_constant_left ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedEvaluation_constant_left

theorem assignedEvaluation_constant_right (hcover : U ∪ V = _root_.Set.univ) {x y : X}
    (p : _root_.Path x y) (hp : _root_.Set.range p ⊆ V) {n : ℕ} (hn : 0 < n) :
    F.assignedEvaluation hcover p hn (CoverAssignment.constant n .right hp) =
      F.rightPathMap hcover p hp := by
  have hchain := F.assignedChain_constant_right hcover p hp n
  have hhom : (F.assignedChain hcover p (CoverAssignment.constant n .right hp)).hom ≍
      (F.rightNormalizedPathChain hcover p hp n).hom := by
    apply Functor.hcongr_hom hchain
  have hnormalized : (F.rightNormalizedPathChain hcover p hp n).hom ≍
      (F.rightPathChain p hp n).hom := by
    unfold rightNormalizedPathChain
    rw [normalizedChainOf_hom]
    apply normalizeHom_heq
  have htotal : (F.assignedChain hcover p (CoverAssignment.constant n .right hp)).hom ≍
      F.right.map (Path.Homotopic.Quotient.mk (pathIn V p hp)) :=
    hhom.trans (hnormalized.trans (F.rightPathChain_hom_heq p hp hn))
  unfold assignedEvaluation rightPathMap
  apply normalizeHom_eq_of_heq _ _ _ _ _ _ htotal

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedEvaluation_constant_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedEvaluation_constant_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedEvaluation_constant_right ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedEvaluation_constant_right

theorem assignedEvaluation_constant_side (hcover : U ∪ V = _root_.Set.univ) {x y : X}
    (p : _root_.Path x y) (side : CoverSide)
    (hp : _root_.Set.range p ⊆ side.set U V) {n : ℕ} (hn : 0 < n) :
    F.assignedEvaluation hcover p hn (CoverAssignment.constant n side hp) =
      F.sidePathMap hcover p side hp := by
  cases side
  · exact F.assignedEvaluation_constant_left hcover p hp hn
  · exact F.assignedEvaluation_constant_right hcover p hp hn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedEvaluation_constant_side then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedEvaluation_constant_side"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedEvaluation_constant_side ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedEvaluation_constant_side

theorem assignedSegment_heq_refinedBlock_hom (hcover : U ∪ V = _root_.Set.univ)
    {x y : X} (p : _root_.Path x y) {n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    (σ : CoverAssignment p U V n) (i : Fin n) :
    F.assignedSegment hcover p σ i ≍
      ((F.assignedChain hcover p (σ.refine hn hk)).whiskerLeft
        (refinedBlockFunctor i)).hom := by
  let q := standardSubpath p i
  let τ := CoverAssignment.constant k (σ.side i) (σ.range_subset i)
  have hchain := F.assignedChain_standardSubpath_eq_refinedBlock hcover p hn hk σ i
  have hhom : (F.assignedChain hcover q τ).hom ≍
      ((F.assignedChain hcover p (σ.refine hn hk)).whiskerLeft
        (refinedBlockFunctor i)).hom := by
    apply Functor.hcongr_hom hchain
  have heval : F.assignedEvaluation hcover q hk τ ≍
      (F.assignedChain hcover q τ).hom := by
    unfold assignedEvaluation
    apply normalizeHom_heq
  change F.sidePathMap hcover q (σ.side i) (σ.range_subset i) ≍ _
  exact (heq_of_eq (F.assignedEvaluation_constant_side hcover q (σ.side i)
    (σ.range_subset i) hk).symm).trans (heval.trans hhom)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedSegment_heq_refinedBlock_hom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedSegment_heq_refinedBlock_hom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedSegment_heq_refinedBlock_hom ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedSegment_heq_refinedBlock_hom

set_option backward.isDefEq.respectTransparency false in
theorem assignedChain_eq_refinement (hcover : U ∪ V = _root_.Set.univ)
    {x y : X} (p : _root_.Path x y) {n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    (σ : CoverAssignment p U V n) :
    F.assignedChain hcover p σ =
      (F.assignedChain hcover p (σ.refine hn hk)).whiskerLeft
        (blockEndpointFunctor n k) := by
  let hObj : ∀ i : Fin (n + 1),
      (F.assignedChain hcover p σ).obj i =
        ((F.assignedChain hcover p (σ.refine hn hk)).whiskerLeft
          (blockEndpointFunctor n k)).obj i := by
    intro i
    change F.gluedObj hcover (p (standardTime n i)) =
      F.gluedObj hcover (p (standardTime (n * k) ((blockEndpointFunctor n k).obj i)))
    exact congrArg (fun t => F.gluedObj hcover (p t))
      (standardTime_blockEndpoint hn hk i).symm
  apply ComposableArrows.ext hObj
  intro r hr
  apply (CategoryTheory.conj_eqToHom_iff_heq _ _ (hObj _) (hObj _)).2
  rw [F.assignedChain_map_succ hcover p σ r hr]
  exact (F.assignedSegment_heq_refinedBlock_hom hcover p hn hk σ ⟨r, hr⟩).trans
    (refinedBlock_hom_heq_blockEndpoint_map
      (F.assignedChain hcover p (σ.refine hn hk)) ⟨r, hr⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedChain_eq_refinement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedChain_eq_refinement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedChain_eq_refinement ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedChain_eq_refinement

theorem assignedEvaluation_mul (hcover : U ∪ V = _root_.Set.univ)
    {x y : X} (p : _root_.Path x y) {n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    (σ : CoverAssignment p U V n) :
    F.assignedEvaluation hcover p hn σ =
      F.assignedEvaluation hcover p (Nat.mul_pos hn hk) (σ.refine hn hk) := by
  have hchain := F.assignedChain_eq_refinement hcover p hn hk σ
  have hhom : (F.assignedChain hcover p σ).hom ≍
      ((F.assignedChain hcover p (σ.refine hn hk)).whiskerLeft
        (blockEndpointFunctor n k)).hom := by
    apply Functor.hcongr_hom hchain
  have htotal : (F.assignedChain hcover p σ).hom ≍
      (F.assignedChain hcover p (σ.refine hn hk)).hom :=
    hhom.trans (blockEndpoint_hom_heq
      (F.assignedChain hcover p (σ.refine hn hk)))
  unfold assignedEvaluation
  apply normalizeHom_eq_of_heq _ _ _ _ _ _ htotal

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedEvaluation_mul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedEvaluation_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedEvaluation_mul ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedEvaluation_mul

theorem assignedEvaluation_trans (hcover : U ∪ V = _root_.Set.univ)
    {x y z : X} (p : _root_.Path x y) (q : _root_.Path y z) {n : ℕ}
    (hn : 0 < n) (σ : CoverAssignment p U V n) (τ : CoverAssignment q U V n) :
    F.assignedEvaluation hcover (p.trans q) (Nat.mul_pos (by omega) hn)
        (CoverAssignment.trans hn σ τ) =
      F.assignedEvaluation hcover p hn σ ≫ F.assignedEvaluation hcover q hn τ := by
  let ξ := CoverAssignment.trans hn σ τ
  let R := F.assignedChain hcover (p.trans q) ξ
  have hpChain := F.assignedChain_eq_trans_first hcover p q hn σ τ
  have hqChain := F.assignedChain_eq_trans_second hcover p q hn σ τ
  have hpHom : (F.assignedChain hcover p σ).hom ≍ R.map' 0 n (hjn := by omega) := by
    have h₁ : (F.assignedChain hcover p σ).hom ≍
        (R.whiskerLeft (firstHalfVertexFunctor hn)).hom := by
      apply Functor.hcongr_hom hpChain
    exact h₁.trans (firstHalf_hom_heq_map_middle hn R)
  have hqHom : (F.assignedChain hcover q τ).hom ≍ R.map' n (2 * n) := by
    have h₁ : (F.assignedChain hcover q τ).hom ≍
        (R.whiskerLeft (secondHalfVertexFunctor n)).hom := by
      apply Functor.hcongr_hom hqChain
    exact h₁.trans (secondHalf_hom_heq_map_middle hn R)
  have h0 : F.gluedObj hcover x = R.obj' 0 := by
    change F.gluedObj hcover x =
      F.gluedObj hcover ((p.trans q) (standardTime (2 * n) 0))
    rw [standardTime_zero, (p.trans q).source]
  have hmid : F.gluedObj hcover y = R.obj' n (hi := by omega) := by
    change F.gluedObj hcover y =
      F.gluedObj hcover ((p.trans q) (standardTime (2 * n) ⟨n, by omega⟩))
    apply congrArg (F.gluedObj hcover)
    calc
      y = p (standardTime n (Fin.last n)) := by rw [standardTime_last hn, p.target]
      _ = (p.trans q) (standardTime (2 * n) (firstHalfVertex hn (Fin.last n))) :=
        (trans_standardTime_first p q hn (Fin.last n)).symm
      _ = (p.trans q) (standardTime (2 * n) ⟨n, by omega⟩) := by rfl
  have h2 : F.gluedObj hcover z = R.obj' (2 * n) := by
    change F.gluedObj hcover z =
      F.gluedObj hcover ((p.trans q) (standardTime (2 * n) (Fin.last (2 * n))))
    rw [standardTime_last (Nat.mul_pos (by omega) hn), (p.trans q).target]
  have hpEval : F.assignedEvaluation hcover p hn σ =
      normalizeHom h0 hmid (R.map' 0 n (hjn := by omega)) := by
    unfold assignedEvaluation
    apply normalizeHom_eq_of_heq _ _ _ _ _ _ hpHom
  have hqEval : F.assignedEvaluation hcover q hn τ =
      normalizeHom hmid h2 (R.map' n (2 * n)) := by
    unfold assignedEvaluation
    apply normalizeHom_eq_of_heq _ _ _ _ _ _ hqHom
  rw [hpEval, hqEval, ← normalizeHom_comp]
  unfold assignedEvaluation
  apply normalizeHom_eq_of_heq _ _ _ _ _ _
  exact heq_of_eq (R.map'_comp 0 n (2 * n))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedEvaluation_trans then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedEvaluation_trans"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedEvaluation_trans ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.assignedEvaluation_trans

noncomputable def coveredEvaluation (hcover : U ∪ V = _root_.Set.univ) {x y : X}
    (p : _root_.Path x y) {n : ℕ} (hn : 0 < n) (hp : Path.IsCovered p U V n) :
    F.gluedObj hcover x ⟶ F.gluedObj hcover y :=
  F.assignedEvaluation hcover p hn (CoverAssignment.ofIsCovered hp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.coveredEvaluation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.coveredEvaluation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.coveredEvaluation ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.coveredEvaluation

theorem coveredEvaluation_eq_assigned (hcover : U ∪ V = _root_.Set.univ) {x y : X}
    (p : _root_.Path x y) {n : ℕ} (hn : 0 < n) (hp : Path.IsCovered p U V n)
    (σ : CoverAssignment p U V n) :
    F.coveredEvaluation hcover p hn hp = F.assignedEvaluation hcover p hn σ :=
  F.assignedEvaluation_eq hcover p hn _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.coveredEvaluation_eq_assigned then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.coveredEvaluation_eq_assigned"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.coveredEvaluation_eq_assigned ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.coveredEvaluation_eq_assigned

theorem coveredEvaluation_mul (hcover : U ∪ V = _root_.Set.univ) {x y : X}
    (p : _root_.Path x y) {n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    (hp : Path.IsCovered p U V n) :
    F.coveredEvaluation hcover p hn hp =
      F.coveredEvaluation hcover p (Nat.mul_pos hn hk) (hp.mul hn hk) := by
  let σ := CoverAssignment.ofIsCovered hp
  calc
    F.coveredEvaluation hcover p hn hp = F.assignedEvaluation hcover p hn σ :=
      F.coveredEvaluation_eq_assigned hcover p hn hp σ
    _ = F.assignedEvaluation hcover p (Nat.mul_pos hn hk) (σ.refine hn hk) :=
      F.assignedEvaluation_mul hcover p hn hk σ
    _ = F.coveredEvaluation hcover p (Nat.mul_pos hn hk) (hp.mul hn hk) :=
      (F.coveredEvaluation_eq_assigned hcover p (Nat.mul_pos hn hk) (hp.mul hn hk)
        (σ.refine hn hk)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.coveredEvaluation_mul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.coveredEvaluation_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.coveredEvaluation_mul ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.coveredEvaluation_mul

theorem coveredEvaluation_eq_of_isCovered (hcover : U ∪ V = _root_.Set.univ) {x y : X}
    (p : _root_.Path x y) {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (hnCovered : Path.IsCovered p U V n) (hmCovered : Path.IsCovered p U V m) :
    F.coveredEvaluation hcover p hn hnCovered =
      F.coveredEvaluation hcover p hm hmCovered := by
  calc
    F.coveredEvaluation hcover p hn hnCovered =
        F.coveredEvaluation hcover p (Nat.mul_pos hn hm) (hnCovered.mul hn hm) :=
      F.coveredEvaluation_mul hcover p hn hm hnCovered
    _ = F.coveredEvaluation hcover p hm hmCovered := by
      symm
      simpa [Nat.mul_comm] using F.coveredEvaluation_mul hcover p hm hn hmCovered

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.coveredEvaluation_eq_of_isCovered then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.coveredEvaluation_eq_of_isCovered"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.coveredEvaluation_eq_of_isCovered ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.coveredEvaluation_eq_of_isCovered

noncomputable def Path.coveredSubdivision {x y : X} (p : _root_.Path x y)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = _root_.Set.univ) :
    {n : ℕ // 0 < n ∧ Path.IsCovered p U V n} :=
  ⟨(Path.exists_isCovered p hU hV hcover).choose,
    (Path.exists_isCovered p hU hV hcover).choose_spec⟩

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.Path
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.Path.coveredSubdivision then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.Path.coveredSubdivision"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.Path.coveredSubdivision ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.Path.coveredSubdivision

noncomputable def rawEvaluation (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = _root_.Set.univ) {x y : X} (p : _root_.Path x y) :
    F.gluedObj hcover x ⟶ F.gluedObj hcover y :=
  let c := Path.coveredSubdivision p hU hV hcover
  F.coveredEvaluation hcover p c.property.1 c.property.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawEvaluation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawEvaluation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawEvaluation ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawEvaluation

theorem rawEvaluation_eq_covered (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = _root_.Set.univ) {x y : X} (p : _root_.Path x y)
    {n : ℕ} (hn : 0 < n) (hp : Path.IsCovered p U V n) :
    F.rawEvaluation hU hV hcover p = F.coveredEvaluation hcover p hn hp := by
  unfold rawEvaluation
  apply F.coveredEvaluation_eq_of_isCovered

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawEvaluation_eq_covered then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawEvaluation_eq_covered"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawEvaluation_eq_covered ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawEvaluation_eq_covered

theorem rawEvaluation_eq_leftPathMap (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = _root_.Set.univ) {x y : X} (p : _root_.Path x y)
    (hp : _root_.Set.range p ⊆ U) :
    F.rawEvaluation hU hV hcover p = F.leftPathMap hcover p hp := by
  let hcovered : Path.IsCovered p U V 1 := fun i =>
    Or.inl (range_standardSubpath_subset p hp i)
  calc
    F.rawEvaluation hU hV hcover p =
        F.coveredEvaluation hcover p Nat.zero_lt_one hcovered :=
      F.rawEvaluation_eq_covered hU hV hcover p Nat.zero_lt_one hcovered
    _ = F.assignedEvaluation hcover p Nat.zero_lt_one
        (CoverAssignment.constant 1 .left hp) :=
      F.coveredEvaluation_eq_assigned hcover p Nat.zero_lt_one hcovered _
    _ = F.leftPathMap hcover p hp :=
      F.assignedEvaluation_constant_left hcover p hp Nat.zero_lt_one

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawEvaluation_eq_leftPathMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawEvaluation_eq_leftPathMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawEvaluation_eq_leftPathMap ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawEvaluation_eq_leftPathMap

theorem rawEvaluation_eq_rightPathMap (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = _root_.Set.univ) {x y : X} (p : _root_.Path x y)
    (hp : _root_.Set.range p ⊆ V) :
    F.rawEvaluation hU hV hcover p = F.rightPathMap hcover p hp := by
  let hcovered : Path.IsCovered p U V 1 := fun i =>
    Or.inr (range_standardSubpath_subset p hp i)
  calc
    F.rawEvaluation hU hV hcover p =
        F.coveredEvaluation hcover p Nat.zero_lt_one hcovered :=
      F.rawEvaluation_eq_covered hU hV hcover p Nat.zero_lt_one hcovered
    _ = F.assignedEvaluation hcover p Nat.zero_lt_one
        (CoverAssignment.constant 1 .right hp) :=
      F.coveredEvaluation_eq_assigned hcover p Nat.zero_lt_one hcovered _
    _ = F.rightPathMap hcover p hp :=
      F.assignedEvaluation_constant_right hcover p hp Nat.zero_lt_one

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawEvaluation_eq_rightPathMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawEvaluation_eq_rightPathMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawEvaluation_eq_rightPathMap ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawEvaluation_eq_rightPathMap

theorem rawEvaluation_refl (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = _root_.Set.univ) (x : X) :
    F.rawEvaluation hU hV hcover (_root_.Path.refl x) = 𝟙 (F.gluedObj hcover x) := by
  have hx : x ∈ U ∨ x ∈ V := by
    have : x ∈ U ∪ V := by rw [hcover]; trivial
    exact this
  rcases hx with hxU | hxV
  · let hp : _root_.Set.range (_root_.Path.refl x) ⊆ U := by
      rintro _ ⟨t, rfl⟩
      exact hxU
    rw [F.rawEvaluation_eq_leftPathMap hU hV hcover (_root_.Path.refl x) hp]
    exact F.leftPathMap_refl hcover hp
  · let hp : _root_.Set.range (_root_.Path.refl x) ⊆ V := by
      rintro _ ⟨t, rfl⟩
      exact hxV
    rw [F.rawEvaluation_eq_rightPathMap hU hV hcover (_root_.Path.refl x) hp]
    exact F.rightPathMap_refl hcover hp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawEvaluation_refl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawEvaluation_refl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawEvaluation_refl ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawEvaluation_refl

theorem rawEvaluation_trans (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = _root_.Set.univ) {x y z : X}
    (p : _root_.Path x y) (q : _root_.Path y z) :
    F.rawEvaluation hU hV hcover (p.trans q) =
      F.rawEvaluation hU hV hcover p ≫ F.rawEvaluation hU hV hcover q := by
  obtain ⟨np, hnp, hp⟩ := Path.exists_isCovered p hU hV hcover
  obtain ⟨nq, hnq, hq⟩ := Path.exists_isCovered q hU hV hcover
  let n := np * nq
  have hn : 0 < n := Nat.mul_pos hnp hnq
  let hpN : Path.IsCovered p U V n := hp.mul hnp hnq
  let hqN : Path.IsCovered q U V n := by
    simpa [n, Nat.mul_comm] using hq.mul hnq hnp
  let σ := CoverAssignment.ofIsCovered hpN
  let τ := CoverAssignment.ofIsCovered hqN
  let ξ := CoverAssignment.trans hn σ τ
  have hξ : Path.IsCovered (p.trans q) U V (2 * n) := ξ.isCovered
  calc
    F.rawEvaluation hU hV hcover (p.trans q) =
        F.coveredEvaluation hcover (p.trans q) (Nat.mul_pos (by omega) hn) hξ :=
      F.rawEvaluation_eq_covered hU hV hcover (p.trans q)
        (Nat.mul_pos (by omega) hn) hξ
    _ = F.assignedEvaluation hcover (p.trans q) (Nat.mul_pos (by omega) hn) ξ :=
      F.coveredEvaluation_eq_assigned hcover (p.trans q)
        (Nat.mul_pos (by omega) hn) hξ ξ
    _ = F.assignedEvaluation hcover p hn σ ≫ F.assignedEvaluation hcover q hn τ :=
      F.assignedEvaluation_trans hcover p q hn σ τ
    _ = F.coveredEvaluation hcover p hn hpN ≫
        F.coveredEvaluation hcover q hn hqN := by
      rw [F.coveredEvaluation_eq_assigned hcover p hn hpN σ,
        F.coveredEvaluation_eq_assigned hcover q hn hqN τ]
    _ = F.rawEvaluation hU hV hcover p ≫ F.rawEvaluation hU hV hcover q := by
      rw [F.rawEvaluation_eq_covered hU hV hcover p hn hpN,
        F.rawEvaluation_eq_covered hU hV hcover q hn hqN]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawEvaluation_trans then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawEvaluation_trans"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawEvaluation_trans ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.rawEvaluation_trans

theorem coveredEvaluation_eq_leftPathMap (hcover : U ∪ V = _root_.Set.univ) {x y : X}
    (p : _root_.Path x y) {n : ℕ} (hn : 0 < n) (hcovered : Path.IsCovered p U V n)
    (hp : _root_.Set.range p ⊆ U) :
    F.coveredEvaluation hcover p hn hcovered = F.leftPathMap hcover p hp := by
  rw [F.coveredEvaluation_eq_assigned hcover p hn hcovered
    (CoverAssignment.constant n .left hp)]
  exact F.assignedEvaluation_constant_left hcover p hp hn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.coveredEvaluation_eq_leftPathMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.coveredEvaluation_eq_leftPathMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.coveredEvaluation_eq_leftPathMap ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.coveredEvaluation_eq_leftPathMap

theorem coveredEvaluation_eq_rightPathMap (hcover : U ∪ V = _root_.Set.univ) {x y : X}
    (p : _root_.Path x y) {n : ℕ} (hn : 0 < n) (hcovered : Path.IsCovered p U V n)
    (hp : _root_.Set.range p ⊆ V) :
    F.coveredEvaluation hcover p hn hcovered = F.rightPathMap hcover p hp := by
  rw [F.coveredEvaluation_eq_assigned hcover p hn hcovered
    (CoverAssignment.constant n .right hp)]
  exact F.assignedEvaluation_constant_right hcover p hp hn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.coveredEvaluation_eq_rightPathMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.LocalFunctorData.coveredEvaluation_eq_rightPathMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.LocalFunctorData.coveredEvaluation_eq_rightPathMap ``Submission.DifferentialGeometry.Topology.VanKampen.LocalFunctorData.coveredEvaluation_eq_rightPathMap

end LocalFunctorData

end DifferentialGeometry.Topology.VanKampen
