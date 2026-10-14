import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.Homotopy.Equiv

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.Topology.Homotopy

universe u v w

open _root_.ContinuousMap

structure HomotopyEquivUnder {X : Type u} [TopologicalSpace X] {Y : Type v} [TopologicalSpace Y]
    {Z : Type w} [TopologicalSpace Z] (toBase : C(X, Y)) (fromBase : C(X, Z)) where
  toFun : C(Y, Z)
  invFun : C(Z, Y)
  map_toBase : toFun.comp toBase = fromBase
  map_fromBase : invFun.comp fromBase = toBase
  leftInv : ContinuousMap.HomotopyRel (invFun.comp toFun) (ContinuousMap.id Y) (Set.range toBase)
  rightInv : ContinuousMap.HomotopyRel (toFun.comp invFun) (ContinuousMap.id Z) (Set.range fromBase)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder ``Submission.DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder

namespace HomotopyEquivUnder

variable {X : Type u} [TopologicalSpace X] {Y : Type v} [TopologicalSpace Y]
variable {Z : Type w} [TopologicalSpace Z] {toBase : C(X, Y)} {fromBase : C(X, Z)}

def precompHomotopyRel {X Y W : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace W] {f₀ f₁ : C(X, Y)} {S : Set X} (F : ContinuousMap.HomotopyRel f₀ f₁ S)
    {T : Set W} (h : C(W, X)) (hmaps : Set.MapsTo h T S) :
    ContinuousMap.HomotopyRel (f₀.comp h) (f₁.comp h) T where
  toHomotopy := F.toHomotopy.comp (ContinuousMap.Homotopy.refl h)
  prop' := by
    intro t x hx
    change F (t, h x) = f₀ (h x)
    exact F.prop t (h x) (hmaps hx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.precompHomotopyRel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.precompHomotopyRel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.precompHomotopyRel ``Submission.DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.precompHomotopyRel

noncomputable def toHomotopyEquiv (e : HomotopyEquivUnder toBase fromBase) :
    ContinuousMap.HomotopyEquiv Y Z where
  toFun := e.toFun
  invFun := e.invFun
  left_inv := ⟨e.leftInv.toHomotopy⟩
  right_inv := ⟨e.rightInv.toHomotopy⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.toHomotopyEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.toHomotopyEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.toHomotopyEquiv ``Submission.DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.toHomotopyEquiv

@[simp]
theorem toHomotopyEquiv_toFun (e : HomotopyEquivUnder toBase fromBase) :
    e.toHomotopyEquiv.toFun = e.toFun := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.toHomotopyEquiv_toFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.toHomotopyEquiv_toFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.toHomotopyEquiv_toFun ``Submission.DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.toHomotopyEquiv_toFun

@[simp]
theorem toHomotopyEquiv_invFun (e : HomotopyEquivUnder toBase fromBase) :
    e.toHomotopyEquiv.invFun = e.invFun := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.toHomotopyEquiv_invFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.toHomotopyEquiv_invFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.toHomotopyEquiv_invFun ``Submission.DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.toHomotopyEquiv_invFun

theorem map_toBase_apply (e : HomotopyEquivUnder toBase fromBase) (x : X) :
    e.toFun (toBase x) = fromBase x :=
  congrArg (fun f : C(X, Z) => f x) e.map_toBase

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.map_toBase_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.map_toBase_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.map_toBase_apply ``Submission.DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.map_toBase_apply

theorem map_fromBase_apply (e : HomotopyEquivUnder toBase fromBase) (x : X) :
    e.invFun (fromBase x) = toBase x :=
  congrArg (fun f : C(X, Y) => f x) e.map_fromBase

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.map_fromBase_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.map_fromBase_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.map_fromBase_apply ``Submission.DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.map_fromBase_apply

noncomputable def refl {toBase fromBase : C(X, Y)} (h : toBase = fromBase) :
    HomotopyEquivUnder toBase fromBase where
  toFun := ContinuousMap.id Y
  invFun := ContinuousMap.id Y
  map_toBase := by
    simp [h]
  map_fromBase := by
    simp [h]
  leftInv := by
    simpa using (ContinuousMap.HomotopyRel.refl (ContinuousMap.id Y) (Set.range toBase))
  rightInv := by
    simpa using (ContinuousMap.HomotopyRel.refl (ContinuousMap.id Y) (Set.range fromBase))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.refl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.refl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.refl ``Submission.DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.refl

noncomputable def symm (e : HomotopyEquivUnder toBase fromBase) :
    HomotopyEquivUnder fromBase toBase where
  toFun := e.invFun
  invFun := e.toFun
  map_toBase := e.map_fromBase
  map_fromBase := e.map_toBase
  leftInv := e.rightInv
  rightInv := e.leftInv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.symm ``Submission.DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.symm

@[simp]
theorem symm_toFun (e : HomotopyEquivUnder toBase fromBase) :
    e.symm.toFun = e.invFun := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.symm_toFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.symm_toFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.symm_toFun ``Submission.DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.symm_toFun

@[simp]
theorem symm_invFun (e : HomotopyEquivUnder toBase fromBase) :
    e.symm.invFun = e.toFun := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.symm_invFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.symm_invFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.symm_invFun ``Submission.DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.symm_invFun

@[simp]
theorem symm_symm (e : HomotopyEquivUnder toBase fromBase) : e.symm.symm = e := by
  cases e
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.symm_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.symm_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.symm_symm ``Submission.DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.symm_symm

noncomputable def trans {X₁ Y₁ Z₁ W : Type*} [TopologicalSpace X₁] [TopologicalSpace Y₁]
    [TopologicalSpace Z₁] [TopologicalSpace W]
    {toBase₁ : C(X₁, Y₁)} {fromBase₁ : C(X₁, Z₁)}
    {toBase₂ : C(X₁, Z₁)} {fromBase₂ : C(X₁, W)}
    (e₁ : HomotopyEquivUnder toBase₁ fromBase₁) (e₂ : HomotopyEquivUnder toBase₂ fromBase₂)
    (h : fromBase₁ = toBase₂) : HomotopyEquivUnder toBase₁ fromBase₂ where
  toFun := e₂.toFun.comp e₁.toFun
  invFun := e₁.invFun.comp e₂.invFun
  map_toBase := by
    apply ContinuousMap.ext
    intro x
    calc
      e₂.toFun (e₁.toFun (toBase₁ x)) = e₂.toFun (fromBase₁ x) :=
        congrArg e₂.toFun (e₁.map_toBase_apply x)
      _ = e₂.toFun (toBase₂ x) := by rw [h]
      _ = fromBase₂ x := e₂.map_toBase_apply x
  map_fromBase := by
    apply ContinuousMap.ext
    intro x
    calc
      e₁.invFun (e₂.invFun (fromBase₂ x)) = e₁.invFun (toBase₂ x) :=
        congrArg e₁.invFun (e₂.map_fromBase_apply x)
      _ = e₁.invFun (fromBase₁ x) := by rw [← h]
      _ = toBase₁ x := e₁.map_fromBase_apply x
  leftInv := by
    have hmap₂ : Set.MapsTo e₁.toFun (Set.range toBase₁) (Set.range toBase₂) := by
      intro y hy
      rcases hy with ⟨x, rfl⟩
      refine Set.mem_range.mpr ⟨x, ?_⟩
      rw [e₁.map_toBase_apply, h]
    have R₂pre : ContinuousMap.HomotopyRel
        ((e₂.invFun.comp e₂.toFun).comp e₁.toFun) ((ContinuousMap.id Z₁).comp e₁.toFun)
        (Set.range toBase₁) :=
      precompHomotopyRel (S := Set.range toBase₂) (T := Set.range toBase₁) e₂.leftInv e₁.toFun hmap₂
    have R₂post : ContinuousMap.HomotopyRel
        (e₁.invFun.comp ((e₂.invFun.comp e₂.toFun).comp e₁.toFun))
        (e₁.invFun.comp ((ContinuousMap.id Z₁).comp e₁.toFun)) (Set.range toBase₁) :=
      R₂pre.compContinuousMap e₁.invFun
    have R₂post' : ContinuousMap.HomotopyRel
        ((e₁.invFun.comp (e₂.invFun.comp e₂.toFun)).comp e₁.toFun)
        (e₁.invFun.comp e₁.toFun) (Set.range toBase₁) := by
      exact R₂post.cast (by ext x; rfl) (by ext x; rfl)
    have R₂post'' : ContinuousMap.HomotopyRel
        ((e₁.invFun.comp e₂.invFun).comp (e₂.toFun.comp e₁.toFun))
        (e₁.invFun.comp e₁.toFun) (Set.range toBase₁) := by
      exact R₂post'.cast (by ext x; rfl) (by ext x; rfl)
    exact R₂post''.trans e₁.leftInv
  rightInv := by
    have hmap₁ : Set.MapsTo e₂.invFun (Set.range fromBase₂) (Set.range fromBase₁) := by
      intro y hy
      rcases hy with ⟨x, rfl⟩
      refine Set.mem_range.mpr ⟨x, ?_⟩
      rw [e₂.map_fromBase_apply, ← h]
    have R₁pre : ContinuousMap.HomotopyRel
        ((e₁.toFun.comp e₁.invFun).comp e₂.invFun) ((ContinuousMap.id Z₁).comp e₂.invFun)
        (Set.range fromBase₂) :=
      precompHomotopyRel (S := Set.range fromBase₁) (T := Set.range fromBase₂) e₁.rightInv e₂.invFun
        hmap₁
    have R₁post : ContinuousMap.HomotopyRel
        (e₂.toFun.comp ((e₁.toFun.comp e₁.invFun).comp e₂.invFun))
        (e₂.toFun.comp ((ContinuousMap.id Z₁).comp e₂.invFun)) (Set.range fromBase₂) :=
      R₁pre.compContinuousMap e₂.toFun
    have R₁post' : ContinuousMap.HomotopyRel
        ((e₂.toFun.comp (e₁.toFun.comp e₁.invFun)).comp e₂.invFun)
        (e₂.toFun.comp e₂.invFun) (Set.range fromBase₂) := by
      exact R₁post.cast (by ext x; rfl) (by ext x; rfl)
    have R₁post'' : ContinuousMap.HomotopyRel
        ((e₂.toFun.comp e₁.toFun).comp (e₁.invFun.comp e₂.invFun))
        (e₂.toFun.comp e₂.invFun) (Set.range fromBase₂) := by
      exact R₁post'.cast (by ext x; rfl) (by ext x; rfl)
    exact R₁post''.trans e₂.rightInv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.trans then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.trans"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.trans ``Submission.DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.trans

@[simp]
theorem trans_toFun (e₁ : HomotopyEquivUnder toBase fromBase) {W : Type*} [TopologicalSpace W]
    {toBase₂ : C(X, Z)} {fromBase₂ : C(X, W)} (e₂ : HomotopyEquivUnder toBase₂ fromBase₂)
    (h : fromBase = toBase₂) :
    (e₁.trans e₂ h).toFun = e₂.toFun.comp e₁.toFun := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.trans_toFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.trans_toFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.trans_toFun ``Submission.DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.trans_toFun

@[simp]
theorem trans_invFun (e₁ : HomotopyEquivUnder toBase fromBase) {W : Type*} [TopologicalSpace W]
    {toBase₂ : C(X, Z)} {fromBase₂ : C(X, W)} (e₂ : HomotopyEquivUnder toBase₂ fromBase₂)
    (h : fromBase = toBase₂) :
    (e₁.trans e₂ h).invFun = e₁.invFun.comp e₂.invFun := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.trans_invFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.trans_invFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.trans_invFun ``Submission.DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.trans_invFun

@[simp]
theorem toHomotopyEquiv_symm (e : HomotopyEquivUnder toBase fromBase) :
    e.symm.toHomotopyEquiv = e.toHomotopyEquiv.symm := by
  cases e with
  | mk toFun invFun map_toBase map_fromBase leftInv rightInv =>
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.toHomotopyEquiv_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.toHomotopyEquiv_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.toHomotopyEquiv_symm ``Submission.DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.toHomotopyEquiv_symm

@[simp]
theorem toHomotopyEquiv_refl {toBase fromBase : C(X, Y)} (h : toBase = fromBase) :
    (refl h).toHomotopyEquiv = ContinuousMap.HomotopyEquiv.refl Y := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.toHomotopyEquiv_refl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.toHomotopyEquiv_refl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.toHomotopyEquiv_refl ``Submission.DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.toHomotopyEquiv_refl

@[simp]
theorem toHomotopyEquiv_trans {X₁ Y₁ Z₁ W : Type*} [TopologicalSpace X₁] [TopologicalSpace Y₁]
    [TopologicalSpace Z₁] [TopologicalSpace W]
    {toBase₁ : C(X₁, Y₁)} {fromBase₁ : C(X₁, Z₁)}
    {toBase₂ : C(X₁, Z₁)} {fromBase₂ : C(X₁, W)}
    (e₁ : HomotopyEquivUnder toBase₁ fromBase₁) (e₂ : HomotopyEquivUnder toBase₂ fromBase₂)
    (h : fromBase₁ = toBase₂) :
    (e₁.trans e₂ h).toHomotopyEquiv = e₁.toHomotopyEquiv.trans e₂.toHomotopyEquiv := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.toHomotopyEquiv_trans then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.toHomotopyEquiv_trans"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.toHomotopyEquiv_trans ``Submission.DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.toHomotopyEquiv_trans

noncomputable def precomp {A B X Y : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace X] [TopologicalSpace Y]
    {j : C(A, X)} {k : C(A, Y)} (e : HomotopyEquivUnder j k) (h : C(B, A)) :
    HomotopyEquivUnder (j.comp h) (k.comp h) where
  toFun := e.toFun
  invFun := e.invFun
  map_toBase := by rw [← ContinuousMap.comp_assoc, e.map_toBase]
  map_fromBase := by rw [← ContinuousMap.comp_assoc, e.map_fromBase]
  leftInv := { e.leftInv with
    prop' := by
      rintro t _ ⟨x, rfl⟩
      exact e.leftInv.prop t (j (h x)) ⟨h x, rfl⟩ }
  rightInv := { e.rightInv with
    prop' := by
      rintro t _ ⟨x, rfl⟩
      exact e.rightInv.prop t (k (h x)) ⟨h x, rfl⟩ }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.precomp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.precomp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.precomp ``Submission.DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.precomp

@[simp]
theorem precomp_toFun {A B X Y : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace X] [TopologicalSpace Y]
    {j : C(A, X)} {k : C(A, Y)} (e : HomotopyEquivUnder j k) (h : C(B, A)) :
    (precomp e h).toFun = e.toFun := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.precomp_toFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.precomp_toFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.precomp_toFun ``Submission.DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.precomp_toFun

@[simp]
theorem precomp_invFun {A B X Y : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace X] [TopologicalSpace Y]
    {j : C(A, X)} {k : C(A, Y)} (e : HomotopyEquivUnder j k) (h : C(B, A)) :
    (precomp e h).invFun = e.invFun := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.precomp_invFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.precomp_invFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.precomp_invFun ``Submission.DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.precomp_invFun

noncomputable def ofHomeomorph {A X Y : Type*} [TopologicalSpace A]
    [TopologicalSpace X] [TopologicalSpace Y]
    (j : C(A, X)) (k : C(A, Y)) (e : X ≃ₜ Y)
    (he : (⟨e, e.continuous_toFun⟩ : C(X, Y)).comp j = k) :
    HomotopyEquivUnder j k where
  toFun := ⟨e, e.continuous_toFun⟩
  invFun := ⟨e.symm, e.symm.continuous_toFun⟩
  map_toBase := he
  map_fromBase := by
    rw [← he]
    ext x
    exact e.left_inv (j x)
  leftInv := (ContinuousMap.HomotopyRel.refl (ContinuousMap.id X) (Set.range j)).cast
    (by ext x; exact (e.left_inv x).symm) rfl
  rightInv := (ContinuousMap.HomotopyRel.refl (ContinuousMap.id Y) (Set.range k)).cast
    (by ext y; exact (e.right_inv y).symm) rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.ofHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.ofHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.ofHomeomorph ``Submission.DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.ofHomeomorph

@[simp]
theorem ofHomeomorph_toFun {A X Y : Type*} [TopologicalSpace A]
    [TopologicalSpace X] [TopologicalSpace Y]
    (j : C(A, X)) (k : C(A, Y)) (e : X ≃ₜ Y)
    (he : (⟨e, e.continuous_toFun⟩ : C(X, Y)).comp j = k) :
    (ofHomeomorph j k e he).toFun = (⟨e, e.continuous_toFun⟩ : C(X, Y)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.ofHomeomorph_toFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.ofHomeomorph_toFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.ofHomeomorph_toFun ``Submission.DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.ofHomeomorph_toFun

@[simp]
theorem ofHomeomorph_invFun {A X Y : Type*} [TopologicalSpace A]
    [TopologicalSpace X] [TopologicalSpace Y]
    (j : C(A, X)) (k : C(A, Y)) (e : X ≃ₜ Y)
    (he : (⟨e, e.continuous_toFun⟩ : C(X, Y)).comp j = k) :
    (ofHomeomorph j k e he).invFun = (⟨e.symm, e.symm.continuous_toFun⟩ : C(Y, X)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.ofHomeomorph_invFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.ofHomeomorph_invFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.ofHomeomorph_invFun ``Submission.DifferentialGeometry.Topology.Homotopy.HomotopyEquivUnder.ofHomeomorph_invFun

end HomotopyEquivUnder

end DifferentialGeometry.Topology.Homotopy
