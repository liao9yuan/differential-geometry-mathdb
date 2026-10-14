import Submission.DifferentialGeometry.Topology.ThreeManifold.PairedBallGluing
import Submission.DifferentialGeometry.Topology.Homeomorph.QuotientDescent
import Submission.DifferentialGeometry.Topology.Homeomorph.Sigma

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

open _root_.Set _root_.Metric _root_.Submission.Metric

namespace DifferentialGeometry.Topology.PairedBallGluing

universe u v w
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PairedBallGluing.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PairedBallGluing.E3 target :: scope.openDecls } }

variable {V : Type v} {E : Type w}
  (N : V → ConnectedClosedOrientedManifold.{u} 3)
  (endpoint : E → Bool → V)
  (chart : (e : E) → (b : Bool) →
    OrientedBallChart (N (endpoint e b)).toClosedOrientedManifold)
  (s : E) (a : BoundaryAttachment)

private abbrev RemainingVertex := {v // v ≠ endpoint s _root_.Bool.false ∧ v ≠ endpoint s _root_.Bool.true}

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PairedBallGluing.RemainingVertex
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PairedBallGluing.RemainingVertex target :: scope.openDecls } }

def mergeFactor : Option (RemainingVertex endpoint s) → ConnectedClosedOrientedManifold.{u} 3
  | none => (smoothConnectedSum (N (endpoint s _root_.Bool.false)) (N (endpoint s _root_.Bool.true))
      (chart s _root_.Bool.false) (chart s _root_.Bool.true) a).toConnectedClosedOrientedManifold
  | some v => N v.val

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.mergeFactor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.mergeFactor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.mergeFactor ``Submission.DifferentialGeometry.Topology.PairedBallGluing.mergeFactor

def mergeVertex (v : V) : Option (RemainingVertex endpoint s) := by
  classical
  exact if hi : v = endpoint s _root_.Bool.false then _root_.Option.none
  else if hj : v = endpoint s _root_.Bool.true then _root_.Option.none
  else _root_.Option.some ⟨v, hi, hj⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.mergeVertex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.mergeVertex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.mergeVertex ``Submission.DifferentialGeometry.Topology.PairedBallGluing.mergeVertex

@[simp] theorem mergeVertex_left : mergeVertex endpoint s (endpoint s _root_.Bool.false) = none := by
  simp [mergeVertex]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.mergeVertex_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.mergeVertex_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.mergeVertex_left ``Submission.DifferentialGeometry.Topology.PairedBallGluing.mergeVertex_left

@[simp] theorem mergeVertex_right : mergeVertex endpoint s (endpoint s _root_.Bool.true) = none := by
  simp [mergeVertex]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.mergeVertex_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.mergeVertex_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.mergeVertex_right ``Submission.DifferentialGeometry.Topology.PairedBallGluing.mergeVertex_right

@[simp] theorem mergeVertex_remaining (v : RemainingVertex endpoint s) :
    mergeVertex endpoint s v.val = _root_.Option.some v := by
  simp [mergeVertex, v.property.1, v.property.2]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.mergeVertex_remaining then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.mergeVertex_remaining"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.mergeVertex_remaining ``Submission.DifferentialGeometry.Topology.PairedBallGluing.mergeVertex_remaining

def mergeFlag
    (b : ({p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s _root_.Bool.false} ⊕
      {p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s _root_.Bool.true}) →
      OrientedBallChart (mergeFactor N endpoint chart s a _root_.Option.none).toClosedOrientedManifold)
    (e : {e // e ≠ s}) (t : Bool) :
    Σ v, OrientedBallChart (mergeFactor N endpoint chart s a v).toClosedOrientedManifold := by
  classical
  exact if hi : endpoint e.val t = endpoint s _root_.Bool.false then
    ⟨none, b (Sum.inl ⟨(e.val, t), e.property, hi⟩)⟩
  else if hj : endpoint e.val t = endpoint s _root_.Bool.true then
    ⟨none, b (Sum.inr ⟨(e.val, t), e.property, hj⟩)⟩
  else ⟨some ⟨endpoint e.val t, hi, hj⟩, chart e.val t⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.mergeFlag then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.mergeFlag"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.mergeFlag ``Submission.DifferentialGeometry.Topology.PairedBallGluing.mergeFlag

theorem mergeFlag_flagMap_left
    (b : ({p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s _root_.Bool.false} ⊕
      {p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s _root_.Bool.true}) →
      OrientedBallChart (mergeFactor N endpoint chart s a _root_.Option.none).toClosedOrientedManifold)
    (e : {e // e ≠ s}) (t : Bool) (hi : endpoint e.val t = endpoint s _root_.Bool.false) (x : E3) :
    flagMap (mergeFactor N endpoint chart s a)
        (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
        (fun e t => (mergeFlag N endpoint chart s a b e t).snd) (e, t) x =
      ⟨none, (b (Sum.inl ⟨(e.val, t), e.property, hi⟩)).chart x⟩ := by
  classical
  have h : mergeFlag N endpoint chart s a b e t =
      ⟨none, b (Sum.inl ⟨(e.val, t), e.property, hi⟩)⟩ := by
    unfold mergeFlag
    rw [dif_pos hi]
  exact congrArg (fun p : Σ v, OrientedBallChart
    (mergeFactor N endpoint chart s a v).toClosedOrientedManifold =>
      (⟨p.fst, p.snd.chart x⟩ : Σ v, (mergeFactor N endpoint chart s a v).Carrier)) h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.mergeFlag_flagMap_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.mergeFlag_flagMap_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.mergeFlag_flagMap_left ``Submission.DifferentialGeometry.Topology.PairedBallGluing.mergeFlag_flagMap_left

theorem mergeFlag_flagMap_right
    (b : ({p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s _root_.Bool.false} ⊕
      {p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s _root_.Bool.true}) →
      OrientedBallChart (mergeFactor N endpoint chart s a _root_.Option.none).toClosedOrientedManifold)
    (e : {e // e ≠ s}) (t : Bool) (hi : endpoint e.val t ≠ endpoint s _root_.Bool.false)
    (hj : endpoint e.val t = endpoint s _root_.Bool.true) (x : E3) :
    flagMap (mergeFactor N endpoint chart s a)
        (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
        (fun e t => (mergeFlag N endpoint chart s a b e t).snd) (e, t) x =
      ⟨none, (b (Sum.inr ⟨(e.val, t), e.property, hj⟩)).chart x⟩ := by
  classical
  have h : mergeFlag N endpoint chart s a b e t =
      ⟨none, b (Sum.inr ⟨(e.val, t), e.property, hj⟩)⟩ := by
    unfold mergeFlag
    rw [dif_neg hi, dif_pos hj]
  exact congrArg (fun p : Σ v, OrientedBallChart
    (mergeFactor N endpoint chart s a v).toClosedOrientedManifold =>
      (⟨p.fst, p.snd.chart x⟩ : Σ v, (mergeFactor N endpoint chart s a v).Carrier)) h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.mergeFlag_flagMap_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.mergeFlag_flagMap_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.mergeFlag_flagMap_right ``Submission.DifferentialGeometry.Topology.PairedBallGluing.mergeFlag_flagMap_right

theorem mergeFlag_flagMap_remaining
    (b : ({p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s _root_.Bool.false} ⊕
      {p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s _root_.Bool.true}) →
      OrientedBallChart (mergeFactor N endpoint chart s a _root_.Option.none).toClosedOrientedManifold)
    (e : {e // e ≠ s}) (t : Bool)
    (hi : endpoint e.val t ≠ endpoint s _root_.Bool.false) (hj : endpoint e.val t ≠ endpoint s _root_.Bool.true)
    (x : E3) :
    flagMap (mergeFactor N endpoint chart s a)
        (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
        (fun e t => (mergeFlag N endpoint chart s a b e t).snd) (e, t) x =
      ⟨some ⟨endpoint e.val t, hi, hj⟩, (chart e.val t).chart x⟩ := by
  classical
  have h : mergeFlag N endpoint chart s a b e t =
      ⟨some ⟨endpoint e.val t, hi, hj⟩, chart e.val t⟩ := by
    unfold mergeFlag
    rw [dif_neg hi, dif_neg hj]
  exact congrArg (fun p : Σ v, OrientedBallChart
    (mergeFactor N endpoint chart s a v).toClosedOrientedManifold =>
      (⟨p.fst, p.snd.chart x⟩ : Σ v, (mergeFactor N endpoint chart s a v).Carrier)) h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.mergeFlag_flagMap_remaining then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.mergeFlag_flagMap_remaining"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.mergeFlag_flagMap_remaining ``Submission.DifferentialGeometry.Topology.PairedBallGluing.mergeFlag_flagMap_remaining

theorem mergeFlag_fst
    (b : ({p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s _root_.Bool.false} ⊕
      {p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s _root_.Bool.true}) →
      OrientedBallChart (mergeFactor N endpoint chart s a _root_.Option.none).toClosedOrientedManifold)
    (e : {e // e ≠ s}) (t : Bool) :
    (mergeFlag N endpoint chart s a b e t).fst =
      mergeVertex endpoint s (endpoint e.val t) := by
  classical
  unfold mergeFlag mergeVertex
  split_ifs <;> rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.mergeFlag_fst then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.mergeFlag_fst"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.mergeFlag_fst ``Submission.DifferentialGeometry.Topology.PairedBallGluing.mergeFlag_fst

theorem pairwise_disjoint_mergeFlag_image
    (b : ({p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s _root_.Bool.false} ⊕
      {p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s _root_.Bool.true}) →
      OrientedBallChart (mergeFactor N endpoint chart s a _root_.Option.none).toClosedOrientedManifold)
    (hdisj : Pairwise fun p q =>
      Disjoint (flagMap N endpoint chart p '' _root_.Metric.closedBall (0 : E3) 2)
        (flagMap N endpoint chart q '' _root_.Metric.closedBall (0 : E3) 2))
    (hb : Pairwise fun p q => Disjoint ((b p).chart '' _root_.Metric.closedBall (0 : E3) 2)
      ((b q).chart '' _root_.Metric.closedBall (0 : E3) 2)) :
    Pairwise fun p q : {e // e ≠ s} × Bool =>
      Disjoint (flagMap (mergeFactor N endpoint chart s a)
        (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
        (fun e t => (mergeFlag N endpoint chart s a b e t).snd) p '' _root_.Metric.closedBall (0 : E3) 2)
      (flagMap (mergeFactor N endpoint chart s a)
        (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
        (fun e t => (mergeFlag N endpoint chart s a b e t).snd) q '' _root_.Metric.closedBall (0 : E3) 2) := by
  classical
  let O := {e // e ≠ s} × Bool
  let J := {p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s _root_.Bool.false} ⊕
    {p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s _root_.Bool.true}
  let original : O → E × Bool := fun p => (p.1.val, p.2)
  have horiginal : Function.Injective original := by
    intro p q h
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (congrArg (fun p : E × Bool => p.2) h)
  let oldIndex : J → E × Bool := Sum.elim Subtype.val Subtype.val
  let F := flagMap (mergeFactor N endpoint chart s a)
    (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
    (fun e t => (mergeFlag N endpoint chart s a b e t).snd)
  let P : (Σ v, (mergeFactor N endpoint chart s a v).Carrier) →
      (mergeFactor N endpoint chart s a _root_.Option.none).Carrier ⊕ (Σ v, (N v).Carrier) :=
    fun q => match q with
      | ⟨none, x⟩ => Sum.inl x
      | ⟨some v, x⟩ => Sum.inr ⟨v.val, x⟩
  have hclass (p : O) (x : E3) :
      (∃ j : J, oldIndex j = original p ∧ P (F p x) = Sum.inl ((b j).chart x)) ∨
      P (F p x) = Sum.inr (flagMap N endpoint chart (original p) x) := by
    by_cases hi : endpoint p.1.val p.2 = endpoint s _root_.Bool.false
    · refine Or.inl ⟨Sum.inl ⟨original p, p.1.property, hi⟩, rfl, ?_⟩
      rw [show F p x = _ from mergeFlag_flagMap_left N endpoint chart s a b p.1 p.2 hi x]
    · by_cases hj : endpoint p.1.val p.2 = endpoint s _root_.Bool.true
      · refine Or.inl ⟨Sum.inr ⟨original p, p.1.property, hj⟩, rfl, ?_⟩
        rw [show F p x = _ from
          mergeFlag_flagMap_right N endpoint chart s a b p.1 p.2 hi hj x]
      · refine Or.inr ?_
        rw [show F p x = _ from
          mergeFlag_flagMap_remaining N endpoint chart s a b p.1 p.2 hi hj x]
        rfl
  intro p q hpq
  rw [_root_.Set.disjoint_left]
  rintro z ⟨x, hx, hxz⟩ ⟨y, hy, hyz⟩
  have hxy : P (F p x) = P (F q y) := congrArg P (hxz.trans hyz.symm)
  rcases hclass p x with ⟨i, hi, hix⟩ | hix <;>
    rcases hclass q y with ⟨j, hj, hjy⟩ | hjy
  · have hv : (b i).chart x = (b j).chart y := Sum.inl.inj (hix.symm.trans (hxy.trans hjy))
    have hij : i ≠ j := fun h => hpq (horiginal (hi.symm.trans ((congrArg oldIndex h).trans hj)))
    exact disjoint_left.mp (hb hij) ⟨x, hx, hv⟩ ⟨y, hy, rfl⟩
  · exact Sum.inl_ne_inr (hix.symm.trans (hxy.trans hjy))
  · exact Sum.inr_ne_inl (hix.symm.trans (hxy.trans hjy))
  · have hv := Sum.inr.inj (hix.symm.trans (hxy.trans hjy))
    exact disjoint_left.mp (hdisj (fun h => hpq (horiginal h))) ⟨x, hx, hv⟩ ⟨y, hy, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.pairwise_disjoint_mergeFlag_image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.pairwise_disjoint_mergeFlag_image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.pairwise_disjoint_mergeFlag_image ``Submission.DifferentialGeometry.Topology.PairedBallGluing.pairwise_disjoint_mergeFlag_image

theorem mergeFlag_holes_none
    (b : ({p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s _root_.Bool.false} ⊕
      {p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s _root_.Bool.true}) →
      OrientedBallChart (mergeFactor N endpoint chart s a _root_.Option.none).toClosedOrientedManifold)
    (hends : endpoint s _root_.Bool.false ≠ endpoint s _root_.Bool.true) (S : Set E3) :
    (fun x : (mergeFactor N endpoint chart s a _root_.Option.none).Carrier =>
      (⟨none, x⟩ : Σ v, (mergeFactor N endpoint chart s a v).Carrier)) ⁻¹'
      (⋃ p, flagMap (mergeFactor N endpoint chart s a)
        (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
        (fun e t => (mergeFlag N endpoint chart s a b e t).snd) p '' S) =
      ⋃ p, (b p).chart '' S := by
  classical
  let F := flagMap (mergeFactor N endpoint chart s a)
    (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
    (fun e t => (mergeFlag N endpoint chart s a b e t).snd)
  have hinj : Function.Injective (fun x : (mergeFactor N endpoint chart s a _root_.Option.none).Carrier =>
      (⟨none, x⟩ : Σ v, (mergeFactor N endpoint chart s a v).Carrier)) := by
    intro x y h
    cases h
    rfl
  ext x
  constructor
  · intro hx
    obtain ⟨⟨e, t⟩, y, hy, hyx⟩ := mem_iUnion.mp hx
    change F (e, t) y = _ at hyx
    by_cases hi : endpoint e.val t = endpoint s _root_.Bool.false
    · have hf := mergeFlag_flagMap_left N endpoint chart s a b e t hi y
      exact mem_iUnion.mpr ⟨Sum.inl ⟨(e.val, t), e.property, hi⟩, y, hy,
        hinj (hf.symm.trans hyx)⟩
    · by_cases hj : endpoint e.val t = endpoint s _root_.Bool.true
      · have hf := mergeFlag_flagMap_right N endpoint chart s a b e t hi hj y
        exact mem_iUnion.mpr ⟨Sum.inr ⟨(e.val, t), e.property, hj⟩, y, hy,
          hinj (hf.symm.trans hyx)⟩
      · have hf := mergeFlag_flagMap_remaining N endpoint chart s a b e t hi hj y
        have hh := congrArg Sigma.fst (hf.symm.trans hyx)
        exact (Option.some_ne_none _ hh).elim
  · intro hx
    obtain ⟨p, y, hy, hyx⟩ := mem_iUnion.mp hx
    rcases p with p | p
    · refine mem_iUnion.mpr ⟨(⟨p.val.1, p.property.1⟩, p.val.2), y, hy, ?_⟩
      exact (mergeFlag_flagMap_left N endpoint chart s a b
        ⟨p.val.1, p.property.1⟩ p.val.2 p.property.2 y).trans
        (congrArg (fun x : (mergeFactor N endpoint chart s a _root_.Option.none).Carrier =>
          (⟨none, x⟩ : Σ v, (mergeFactor N endpoint chart s a v).Carrier)) hyx)
    · refine mem_iUnion.mpr ⟨(⟨p.val.1, p.property.1⟩, p.val.2), y, hy, ?_⟩
      exact (mergeFlag_flagMap_right N endpoint chart s a b
        ⟨p.val.1, p.property.1⟩ p.val.2
        (fun h => hends (h.symm.trans p.property.2)) p.property.2 y).trans
        (congrArg (fun x : (mergeFactor N endpoint chart s a _root_.Option.none).Carrier =>
          (⟨none, x⟩ : Σ v, (mergeFactor N endpoint chart s a v).Carrier)) hyx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.mergeFlag_holes_none then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.mergeFlag_holes_none"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.mergeFlag_holes_none ``Submission.DifferentialGeometry.Topology.PairedBallGluing.mergeFlag_holes_none

private theorem sigma_some_eq_of_eq (v v' : RemainingVertex endpoint s)
    (x : (N v.val).Carrier) (y : (N v'.val).Carrier)
    (h : (⟨v.val, x⟩ : Σ v, (N v).Carrier) = ⟨v'.val, y⟩) :
    (⟨some v, x⟩ : Σ v, (mergeFactor N endpoint chart s a v).Carrier) = ⟨some v', y⟩ := by
  have hv : v = v' := Subtype.ext (congrArg Sigma.fst h)
  subst v'
  have hinj : Function.Injective (fun x : (N v.val).Carrier =>
      (⟨v.val, x⟩ : Σ v, (N v).Carrier)) := by
    intro x y h
    cases h
    rfl
  rw [hinj h]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PairedBallGluing.sigma_some_eq_of_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PairedBallGluing.sigma_some_eq_of_eq target :: scope.openDecls } }

theorem mergeFlag_holes_some
    (b : ({p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s _root_.Bool.false} ⊕
      {p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s _root_.Bool.true}) →
      OrientedBallChart (mergeFactor N endpoint chart s a _root_.Option.none).toClosedOrientedManifold)
    (v : RemainingVertex endpoint s) (S : Set E3) :
    (fun x : (N v.val).Carrier =>
      (⟨some v, x⟩ : Σ v, (mergeFactor N endpoint chart s a v).Carrier)) ⁻¹'
      (⋃ p, flagMap (mergeFactor N endpoint chart s a)
        (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
        (fun e t => (mergeFlag N endpoint chart s a b e t).snd) p '' S) =
      (fun x : (N v.val).Carrier => (⟨v.val, x⟩ : Σ v, (N v).Carrier)) ⁻¹'
        (⋃ p, flagMap N endpoint chart p '' S) := by
  classical
  let F := flagMap (mergeFactor N endpoint chart s a)
    (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
    (fun e t => (mergeFlag N endpoint chart s a b e t).snd)
  let P : (Σ v, (mergeFactor N endpoint chart s a v).Carrier) →
      (mergeFactor N endpoint chart s a _root_.Option.none).Carrier ⊕ (Σ v, (N v).Carrier) :=
    fun q => match q with
      | ⟨none, x⟩ => Sum.inl x
      | ⟨some v, x⟩ => Sum.inr ⟨v.val, x⟩
  ext x
  constructor
  · intro hx
    obtain ⟨⟨e, t⟩, y, hy, hyx⟩ := mem_iUnion.mp hx
    change F (e, t) y = _ at hyx
    by_cases hi : endpoint e.val t = endpoint s _root_.Bool.false
    · have hf := mergeFlag_flagMap_left N endpoint chart s a b e t hi y
      have hh := congrArg Sigma.fst (hf.symm.trans hyx)
      exact (Option.some_ne_none _ hh.symm).elim
    · by_cases hj : endpoint e.val t = endpoint s _root_.Bool.true
      · have hf := mergeFlag_flagMap_right N endpoint chart s a b e t hi hj y
        have hh := congrArg Sigma.fst (hf.symm.trans hyx)
        exact (Option.some_ne_none _ hh.symm).elim
      · have hf := mergeFlag_flagMap_remaining N endpoint chart s a b e t hi hj y
        have hh := congrArg P (hf.symm.trans hyx)
        exact mem_iUnion.mpr ⟨(e.val, t), y, hy, Sum.inr.inj hh⟩
  · intro hx
    obtain ⟨p, y, hy, hyx⟩ := mem_iUnion.mp hx
    have hpv : endpoint p.1 p.2 = v.val := congrArg Sigma.fst hyx
    have hi : endpoint p.1 p.2 ≠ endpoint s false := fun h => v.property.1 (hpv.symm.trans h)
    have hj : endpoint p.1 p.2 ≠ endpoint s true := fun h => v.property.2 (hpv.symm.trans h)
    have hps : p.1 ≠ s := by
      intro h
      obtain ⟨e, t⟩ := p
      dsimp at h hi hj
      subst e
      cases t
      · exact hi rfl
      · exact hj rfl
    refine mem_iUnion.mpr ⟨(⟨p.1, hps⟩, p.2), y, hy, ?_⟩
    exact (mergeFlag_flagMap_remaining N endpoint chart s a b ⟨p.1, hps⟩ p.2 hi hj y).trans
      (sigma_some_eq_of_eq N endpoint chart s a ⟨endpoint p.1 p.2, hi, hj⟩ v
        ((chart p.1 p.2).chart y) x hyx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.mergeFlag_holes_some then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.mergeFlag_holes_some"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.mergeFlag_holes_some ``Submission.DifferentialGeometry.Topology.PairedBallGluing.mergeFlag_holes_some

def mergePuncturedFactorHomeomorph
    (b : ({p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s _root_.Bool.false} ⊕
      {p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s _root_.Bool.true}) →
      OrientedBallChart (mergeFactor N endpoint chart s a _root_.Option.none).toClosedOrientedManifold)
    (hends : endpoint s _root_.Bool.false ≠ endpoint s _root_.Bool.true) :
    (Σ v, PuncturedFactor (mergeFactor N endpoint chart s a)
      (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
      (fun e t => (mergeFlag N endpoint chart s a b e t).snd) v) ≃ₜ
      {q : (mergeFactor N endpoint chart s a _root_.Option.none).Carrier //
        q ∉ ⋃ p, (b p).chart '' _root_.Metric.ball (0 : E3) 1} ⊕
      (Σ v : RemainingVertex endpoint s, PuncturedFactor N endpoint chart v.val) := by
  let N' := mergeFactor N endpoint chart s a
  let ep' := fun e t => (mergeFlag N endpoint chart s a b e t).fst
  let ch' := fun e t => (mergeFlag N endpoint chart s a b e t).snd
  let X := PuncturedFactor N' ep' ch'
  let Y : Option (RemainingVertex endpoint s) → Type u := fun v =>
    match v with
    | none => {q : (N' _root_.Option.none).Carrier // q ∉ ⋃ p, (b p).chart '' _root_.Metric.ball (0 : E3) 1}
    | some v => PuncturedFactor N endpoint chart v.val
  letI : ∀ v, TopologicalSpace (Y v) := fun v => by
    cases v <;> dsimp [Y] <;> infer_instance
  let h : ∀ v, X v ≃ₜ Y v := fun v => by
    cases v with
    | none =>
      apply Homeomorph.setCongr
      ext x
      exact not_congr (Set.ext_iff.mp
        (mergeFlag_holes_none N endpoint chart s a b hends (_root_.Metric.ball (0 : E3) 1)) x)
    | some v =>
      apply Homeomorph.setCongr
      ext x
      exact not_congr (Set.ext_iff.mp
        (mergeFlag_holes_some N endpoint chart s a b v (_root_.Metric.ball (0 : E3) 1)) x)
  exact (Homeomorph.sigmaCongrRight h).trans (Homeomorph.sigmaOption Y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.mergePuncturedFactorHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.mergePuncturedFactorHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.mergePuncturedFactorHomeomorph ``Submission.DifferentialGeometry.Topology.PairedBallGluing.mergePuncturedFactorHomeomorph

theorem mergePuncturedFactorHomeomorph_none
    (b : ({p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s _root_.Bool.false} ⊕
      {p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s _root_.Bool.true}) →
      OrientedBallChart (mergeFactor N endpoint chart s a _root_.Option.none).toClosedOrientedManifold)
    (hends : endpoint s _root_.Bool.false ≠ endpoint s _root_.Bool.true)
    (x : PuncturedFactor (mergeFactor N endpoint chart s a)
      (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
      (fun e t => (mergeFlag N endpoint chart s a b e t).snd) _root_.Option.none)
    (hx : x.val ∉ ⋃ p, (b p).chart '' _root_.Metric.ball (0 : E3) 1) :
    mergePuncturedFactorHomeomorph N endpoint chart s a b hends ⟨none, x⟩ =
      Sum.inl ⟨x.val, hx⟩ := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.mergePuncturedFactorHomeomorph_none then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.mergePuncturedFactorHomeomorph_none"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.mergePuncturedFactorHomeomorph_none ``Submission.DifferentialGeometry.Topology.PairedBallGluing.mergePuncturedFactorHomeomorph_none

theorem mergePuncturedFactorHomeomorph_some
    (b : ({p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s _root_.Bool.false} ⊕
      {p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s _root_.Bool.true}) →
      OrientedBallChart (mergeFactor N endpoint chart s a _root_.Option.none).toClosedOrientedManifold)
    (hends : endpoint s _root_.Bool.false ≠ endpoint s _root_.Bool.true) (v : RemainingVertex endpoint s)
    (x : PuncturedFactor (mergeFactor N endpoint chart s a)
      (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
      (fun e t => (mergeFlag N endpoint chart s a b e t).snd) (_root_.Option.some v))
    (hx : (⟨v.val, x.val⟩ : Σ v, (N v).Carrier) ∉
      ⋃ p, flagMap N endpoint chart p '' _root_.Metric.ball (0 : E3) 1) :
    mergePuncturedFactorHomeomorph N endpoint chart s a b hends ⟨some v, x⟩ =
      Sum.inr ⟨v, ⟨x.val, hx⟩⟩ := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.mergePuncturedFactorHomeomorph_some then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.mergePuncturedFactorHomeomorph_some"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.mergePuncturedFactorHomeomorph_some ``Submission.DifferentialGeometry.Topology.PairedBallGluing.mergePuncturedFactorHomeomorph_some


private abbrev RVertex := {v // v ≠ endpoint s _root_.Bool.false ∧ v ≠ endpoint s _root_.Bool.true}

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PairedBallGluing.RVertex
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PairedBallGluing.RVertex target :: scope.openDecls } }
private abbrev LFlag := {p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s _root_.Bool.false}

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PairedBallGluing.LFlag
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PairedBallGluing.LFlag target :: scope.openDecls } }
private abbrev RFlag := {p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s _root_.Bool.true}

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PairedBallGluing.RFlag
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PairedBallGluing.RFlag target :: scope.openDecls } }

private def mergeSplitVal
    (b : LFlag endpoint s ⊕ RFlag endpoint s →
      OrientedBallChart (mergeFactor N endpoint chart s a _root_.Option.none).toClosedOrientedManifold) :
    ({x : (mergeFactor N endpoint chart s a _root_.Option.none).Carrier //
        x ∉ ⋃ p, (b p).chart '' _root_.Metric.ball (0 : E3) 1} ⊕
      (Σ v : RVertex endpoint s, PuncturedFactor N endpoint chart v.val)) →
        (mergeFactor N endpoint chart s a _root_.Option.none).Carrier ⊕ (Σ v, (N v).Carrier) :=
  Sum.elim (fun x => Sum.inl x.val) (fun p => Sum.inr ⟨p.fst.val, p.snd.val⟩)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PairedBallGluing.mergeSplitVal
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PairedBallGluing.mergeSplitVal target :: scope.openDecls } }

private theorem mergeSplitVal_injective
    (b : LFlag endpoint s ⊕ RFlag endpoint s →
      OrientedBallChart (mergeFactor N endpoint chart s a _root_.Option.none).toClosedOrientedManifold) :
    Function.Injective (mergeSplitVal N endpoint chart s a b) := by
  rintro (x | ⟨v, x⟩) (y | ⟨w, y⟩) h
  · exact congrArg Sum.inl (Subtype.ext (Sum.inl.inj h))
  · exact (Sum.inl_ne_inr h).elim
  · exact (Sum.inr_ne_inl h).elim
  · have hval := Sum.inr.inj h
    have hv : v = w := Subtype.ext (congrArg Sigma.fst hval)
    subst w
    have hinj : Function.Injective (fun x : (N v.val).Carrier =>
        (⟨v.val, x⟩ : Σ v, (N v).Carrier)) := by
      intro x y h
      cases h
      rfl
    have hxy : x = y := Subtype.ext (hinj hval)
    subst y
    rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PairedBallGluing.mergeSplitVal_injective
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PairedBallGluing.mergeSplitVal_injective target :: scope.openDecls } }

private def mergeAmbientSplit :
    (Σ v, (mergeFactor N endpoint chart s a v).Carrier) →
      (mergeFactor N endpoint chart s a _root_.Option.none).Carrier ⊕ (Σ v, (N v).Carrier)
  | ⟨none, x⟩ => Sum.inl x
  | ⟨some v, x⟩ => Sum.inr ⟨v.val, x⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PairedBallGluing.mergeAmbientSplit
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PairedBallGluing.mergeAmbientSplit target :: scope.openDecls } }

private theorem mergePuncturedFactorHomeomorph_val
    (b : LFlag endpoint s ⊕ RFlag endpoint s →
      OrientedBallChart (mergeFactor N endpoint chart s a _root_.Option.none).toClosedOrientedManifold)
    (hends : endpoint s _root_.Bool.false ≠ endpoint s _root_.Bool.true)
    (x : Σ v, PuncturedFactor (mergeFactor N endpoint chart s a)
      (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
      (fun e t => (mergeFlag N endpoint chart s a b e t).snd) v) :
    mergeSplitVal N endpoint chart s a b
      (mergePuncturedFactorHomeomorph N endpoint chart s a b hends x) =
        mergeAmbientSplit N endpoint chart s a ⟨x.fst, x.snd.val⟩ := by
  obtain ⟨v, x⟩ := x
  cases v <;> rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PairedBallGluing.mergePuncturedFactorHomeomorph_val
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PairedBallGluing.mergePuncturedFactorHomeomorph_val target :: scope.openDecls } }

theorem exists_merge_homeomorph
    (hdisj : Pairwise fun p q =>
      Disjoint (flagMap N endpoint chart p '' _root_.Metric.closedBall (0 : E3) 2)
        (flagMap N endpoint chart q '' _root_.Metric.closedBall (0 : E3) 2))
    (hends : endpoint s _root_.Bool.false ≠ endpoint s _root_.Bool.true) :
    ∃ b : LFlag endpoint s ⊕ RFlag endpoint s →
      OrientedBallChart (mergeFactor N endpoint chart s a _root_.Option.none).toClosedOrientedManifold,
      (∀ p x, x ∈ _root_.Metric.closedBall (0 : E3) 2 →
        ∃ hx : (remainingIncidenceChart N endpoint chart s (endpoint s _root_.Bool.false) p).chart x ∉
            (chart s _root_.Bool.false).chart '' _root_.Metric.ball (0 : E3) 1,
          (b (Sum.inl p)).chart x = ConnectedSumQuotient.inl
            (chart s _root_.Bool.false).toBallChart (chart s _root_.Bool.true).toBallChart a.1.toHomeomorph
            ⟨(remainingIncidenceChart N endpoint chart s (endpoint s _root_.Bool.false) p).chart x, hx⟩) ∧
      (∀ p x, x ∈ _root_.Metric.closedBall (0 : E3) 2 →
        ∃ hx : (remainingIncidenceChart N endpoint chart s (endpoint s _root_.Bool.true) p).chart x ∉
            (chart s _root_.Bool.true).chart '' _root_.Metric.ball (0 : E3) 1,
          (b (Sum.inr p)).chart x = ConnectedSumQuotient.inr
            (chart s _root_.Bool.false).toBallChart (chart s _root_.Bool.true).toBallChart a.1.toHomeomorph
            ⟨(remainingIncidenceChart N endpoint chart s (endpoint s _root_.Bool.true) p).chart x, hx⟩) ∧
      ∃ hb : Pairwise fun p q =>
        Disjoint (flagMap (mergeFactor N endpoint chart s a)
          (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
          (fun e t => (mergeFlag N endpoint chart s a b e t).snd) p '' _root_.Metric.closedBall (0 : E3) 2)
        (flagMap (mergeFactor N endpoint chart s a)
          (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
          (fun e t => (mergeFlag N endpoint chart s a b e t).snd) q '' _root_.Metric.closedBall (0 : E3) 2),
        ∃ H : Quot (seamRel N endpoint chart hdisj s a) ≃ₜ
          (Σ v, PuncturedFactor (mergeFactor N endpoint chart s a)
            (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
            (fun e t => (mergeFlag N endpoint chart s a b e t).snd) v),
          (∀ x : PuncturedFactor N endpoint chart (endpoint s _root_.Bool.false),
            ∃ y, mergePuncturedFactorHomeomorph N endpoint chart s a b hends
                (H (Quot.mk _ ⟨endpoint s _root_.Bool.false, x⟩)) = Sum.inl y ∧
              y.val = ConnectedSumQuotient.inl (chart s _root_.Bool.false).toBallChart
                (chart s _root_.Bool.true).toBallChart a.1.toHomeomorph
                (selectedPuncturedFactorHomeomorph N endpoint chart s _root_.Bool.false hends x).val) ∧
          (∀ x : PuncturedFactor N endpoint chart (endpoint s _root_.Bool.true),
            ∃ y, mergePuncturedFactorHomeomorph N endpoint chart s a b hends
                (H (Quot.mk _ ⟨endpoint s _root_.Bool.true, x⟩)) = Sum.inl y ∧
              y.val = ConnectedSumQuotient.inr (chart s _root_.Bool.false).toBallChart
                (chart s _root_.Bool.true).toBallChart a.1.toHomeomorph
                (selectedPuncturedFactorHomeomorph N endpoint chart s _root_.Bool.true hends x).val) ∧
          (∀ (v : {v // v ≠ endpoint s _root_.Bool.false ∧ v ≠ endpoint s _root_.Bool.true})
            (x : PuncturedFactor N endpoint chart v.val),
            mergePuncturedFactorHomeomorph N endpoint chart s a b hends
              (H (Quot.mk _ ⟨v.val, x⟩)) = Sum.inr ⟨v, x⟩) ∧
          ∀ (e : {e // e ≠ s}) (t : Bool) (z : _root_.Metric.sphere (0 : E3) 1),
            H (Quot.mk _ ⟨endpoint e.val t, boundaryPoint N endpoint chart hdisj e.val t z⟩) =
              ⟨(mergeFlag N endpoint chart s a b e t).fst,
                boundaryPoint (mergeFactor N endpoint chart s a)
                  (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
                  (fun e t => (mergeFlag N endpoint chart s a b e t).snd) hb e t z⟩ := by
  classical
  obtain ⟨b, hbL, hbR, hbd, H, hfirst, hsecond, hu, hL, hR⟩ :=
    exists_seam_quotient_homeomorph N endpoint chart hdisj s a hends
  have hb := pairwise_disjoint_mergeFlag_image N endpoint chart s a b hdisj hbd
  let J := mergePuncturedFactorHomeomorph N endpoint chart s a b hends
  let H' := H.trans J.symm
  refine ⟨b, hbL, hbR, hb, H', ?_, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨y, hy, hyval⟩ := hfirst x
    exact ⟨y, (J.apply_symm_apply _).trans hy, hyval⟩
  · intro x
    obtain ⟨y, hy, hyval⟩ := hsecond x
    exact ⟨y, (J.apply_symm_apply _).trans hy, hyval⟩
  · intro v x
    exact (J.apply_symm_apply _).trans (hu v x)
  intro e t z
  apply J.injective
  change J (J.symm (H (Quot.mk _
    ⟨endpoint e.val t, boundaryPoint N endpoint chart hdisj e.val t z⟩))) = _
  refine (J.apply_symm_apply _).trans ?_
  apply mergeSplitVal_injective N endpoint chart s a b
  refine Eq.trans ?_ (mergePuncturedFactorHomeomorph_val N endpoint chart s a b hends _).symm
  change mergeSplitVal N endpoint chart s a b
    (H (Quot.mk _ ⟨endpoint e.val t, boundaryPoint N endpoint chart hdisj e.val t z⟩)) =
      mergeAmbientSplit N endpoint chart s a
        (flagMap (mergeFactor N endpoint chart s a)
          (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
          (fun e t => (mergeFlag N endpoint chart s a b e t).snd) (e, t) z)
  by_cases hi : endpoint e.val t = endpoint s _root_.Bool.false
  · obtain ⟨y, hy, hyval⟩ := hL ⟨(e.val, t), e.property, hi⟩ z
    rw [hy, mergeFlag_flagMap_left N endpoint chart s a b e t hi z]
    exact congrArg Sum.inl hyval
  · by_cases hj : endpoint e.val t = endpoint s _root_.Bool.true
    · obtain ⟨y, hy, hyval⟩ := hR ⟨(e.val, t), e.property, hj⟩ z
      rw [hy, mergeFlag_flagMap_right N endpoint chart s a b e t hi hj z]
      exact congrArg Sum.inl hyval
    · rw [hu ⟨endpoint e.val t, hi, hj⟩,
        mergeFlag_flagMap_remaining N endpoint chart s a b e t hi hj z]
      rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.exists_merge_homeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.exists_merge_homeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.exists_merge_homeomorph ``Submission.DifferentialGeometry.Topology.PairedBallGluing.exists_merge_homeomorph


variable
  (hdisj : Pairwise fun p q =>
    Disjoint (flagMap N endpoint chart p '' closedBall (0 : E3) 2)
      (flagMap N endpoint chart q '' closedBall (0 : E3) 2))
  (attachment : E → BoundaryAttachment)

private theorem map_seamRel_iff
    {V' : Type*} (N' : V' → ConnectedClosedOrientedManifold.{u} 3)
    (endpoint' : {e // e ≠ s} → Bool → V')
    (chart' : (e : {e // e ≠ s}) → (t : Bool) →
      OrientedBallChart (N' (endpoint' e t)).toClosedOrientedManifold)
    (hdisj' : Pairwise fun p q =>
      Disjoint (flagMap N' endpoint' chart' p '' _root_.Metric.closedBall (0 : E3) 2)
        (flagMap N' endpoint' chart' q '' _root_.Metric.closedBall (0 : E3) 2))
    (F : (Σ v, PuncturedFactor N endpoint chart v) →
      (Σ v, PuncturedFactor N' endpoint' chart' v))
    (hF : ∀ (e : {e // e ≠ s}) (t : Bool) (z : _root_.Metric.sphere (0 : E3) 1),
      F ⟨endpoint e.val t, boundaryPoint N endpoint chart hdisj e.val t z⟩ =
        ⟨endpoint' e t, boundaryPoint N' endpoint' chart' hdisj' e t z⟩)
    (e : {e // e ≠ s}) (x y : Σ v, PuncturedFactor N' endpoint' chart' v) :
    Relation.Map (seamRel N endpoint chart hdisj e.val (attachment e.val)) F F x y ↔
      seamRel N' endpoint' chart' hdisj' e (attachment e.val) x y := by
  constructor
  · rintro ⟨p, q, ⟨z, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩, hpx, hqy⟩
    · exact ⟨z, Or.inl ⟨hpx.symm.trans (hF e _root_.Bool.false z),
        hqy.symm.trans (hF e _root_.Bool.true ((attachment e.val).1 z))⟩⟩
    · exact ⟨z, Or.inr ⟨hqy.symm.trans (hF e _root_.Bool.false z),
        hpx.symm.trans (hF e _root_.Bool.true ((attachment e.val).1 z))⟩⟩
  · rintro ⟨z, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact ⟨_, _, ⟨z, Or.inl ⟨rfl, rfl⟩⟩,
        hF e _root_.Bool.false z, hF e _root_.Bool.true ((attachment e.val).1 z)⟩
    · exact ⟨_, _, ⟨z, Or.inr ⟨rfl, rfl⟩⟩,
        hF e _root_.Bool.true ((attachment e.val).1 z), hF e _root_.Bool.false z⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PairedBallGluing.map_seamRel_iff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PairedBallGluing.map_seamRel_iff target :: scope.openDecls } }

theorem exists_quotient_homeomorph_merge
    (hends : endpoint s _root_.Bool.false ≠ endpoint s _root_.Bool.true) :
    let N' := mergeFactor N endpoint chart s (attachment s)
    ∃ b : ({p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s _root_.Bool.false} ⊕
        {p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s _root_.Bool.true}) →
      OrientedBallChart (N' _root_.Option.none).toClosedOrientedManifold,
      let endpoint' := fun e t => (mergeFlag N endpoint chart s (attachment s) b e t).fst
      let chart' := fun e t => (mergeFlag N endpoint chart s (attachment s) b e t).snd
      (∀ p x, x ∈ _root_.Metric.closedBall (0 : E3) 2 →
        ∃ hx : (remainingIncidenceChart N endpoint chart s (endpoint s _root_.Bool.false) p).chart x ∉
            (chart s _root_.Bool.false).chart '' _root_.Metric.ball (0 : E3) 1,
          (b (Sum.inl p)).chart x = ConnectedSumQuotient.inl
            (chart s _root_.Bool.false).toBallChart (chart s _root_.Bool.true).toBallChart (attachment s).1.toHomeomorph
            ⟨(remainingIncidenceChart N endpoint chart s (endpoint s _root_.Bool.false) p).chart x, hx⟩) ∧
      (∀ p x, x ∈ _root_.Metric.closedBall (0 : E3) 2 →
        ∃ hx : (remainingIncidenceChart N endpoint chart s (endpoint s _root_.Bool.true) p).chart x ∉
            (chart s _root_.Bool.true).chart '' _root_.Metric.ball (0 : E3) 1,
          (b (Sum.inr p)).chart x = ConnectedSumQuotient.inr
            (chart s _root_.Bool.false).toBallChart (chart s _root_.Bool.true).toBallChart (attachment s).1.toHomeomorph
            ⟨(remainingIncidenceChart N endpoint chart s (endpoint s _root_.Bool.true) p).chart x, hx⟩) ∧
      ∃ hb : Pairwise fun p q =>
        Disjoint (flagMap N' endpoint' chart' p '' _root_.Metric.closedBall (0 : E3) 2)
          (flagMap N' endpoint' chart' q '' _root_.Metric.closedBall (0 : E3) 2),
        ∃ H : Quot (seamRel N endpoint chart hdisj s (attachment s)) ≃ₜ
          (Σ v, PuncturedFactor N' endpoint' chart' v),
          (∀ x : PuncturedFactor N endpoint chart (endpoint s _root_.Bool.false),
            ∃ y, mergePuncturedFactorHomeomorph N endpoint chart s (attachment s) b hends
                (H (Quot.mk _ ⟨endpoint s _root_.Bool.false, x⟩)) = Sum.inl y ∧
              y.val = ConnectedSumQuotient.inl (chart s _root_.Bool.false).toBallChart
                (chart s _root_.Bool.true).toBallChart (attachment s).1.toHomeomorph
                (selectedPuncturedFactorHomeomorph N endpoint chart s _root_.Bool.false hends x).val) ∧
          (∀ x : PuncturedFactor N endpoint chart (endpoint s _root_.Bool.true),
            ∃ y, mergePuncturedFactorHomeomorph N endpoint chart s (attachment s) b hends
                (H (Quot.mk _ ⟨endpoint s _root_.Bool.true, x⟩)) = Sum.inl y ∧
              y.val = ConnectedSumQuotient.inr (chart s _root_.Bool.false).toBallChart
                (chart s _root_.Bool.true).toBallChart (attachment s).1.toHomeomorph
                (selectedPuncturedFactorHomeomorph N endpoint chart s _root_.Bool.true hends x).val) ∧
          (∀ (v : {v // v ≠ endpoint s _root_.Bool.false ∧ v ≠ endpoint s _root_.Bool.true})
            (x : PuncturedFactor N endpoint chart v.val),
            mergePuncturedFactorHomeomorph N endpoint chart s (attachment s) b hends
              (H (Quot.mk _ ⟨v.val, x⟩)) = Sum.inr ⟨v, x⟩) ∧
          (∀ (e : {e // e ≠ s}) (t : Bool) (z : _root_.Metric.sphere (0 : E3) 1),
            H (Quot.mk _ ⟨endpoint e.val t, boundaryPoint N endpoint chart hdisj e.val t z⟩) =
              ⟨endpoint' e t, boundaryPoint N' endpoint' chart' hb e t z⟩) ∧
          ∃ J : Quot (fun x y => ∃ e, seamRel N endpoint chart hdisj e (attachment e) x y) ≃ₜ
              Quot (fun x y => ∃ e : {e // e ≠ s},
                seamRel N' endpoint' chart' hb e (attachment e.val) x y),
            ∀ x, J (Quot.mk _ x) = Quot.mk _ (H (Quot.mk _ x)) := by
  dsimp only
  obtain ⟨b, hbL, hbR, hb, H, hfirst, hsecond, hu, hH⟩ :=
    exists_merge_homeomorph N endpoint chart s (attachment s) hdisj hends
  let N' := mergeFactor N endpoint chart s (attachment s)
  let endpoint' := fun e t => (mergeFlag N endpoint chart s (attachment s) b e t).fst
  let chart' := fun e t => (mergeFlag N endpoint chart s (attachment s) b e t).snd
  let r := fun e => seamRel N endpoint chart hdisj e (attachment e)
  let K := Homeomorph.Quot.indexedRelationStep r s H
  have hrel (x y : Σ v, PuncturedFactor N' endpoint' chart' v) :
      (∃ e : {e // e ≠ s}, Relation.Map (r e.val)
        (H ∘ Quot.mk (r s)) (H ∘ Quot.mk (r s)) x y) ↔
      ∃ e : {e // e ≠ s}, seamRel N' endpoint' chart' hb e (attachment e.val) x y := by
    apply exists_congr
    intro e
    exact map_seamRel_iff N endpoint chart s hdisj attachment N' endpoint' chart' hb
      (H ∘ Quot.mk (r s)) hH e x y
  let J := K.trans (Homeomorph.Quot.congrRight hrel)
  exact ⟨b, hbL, hbR, hb, H, hfirst, hsecond, hu, hH, J, fun _ => rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.exists_quotient_homeomorph_merge then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.exists_quotient_homeomorph_merge"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.exists_quotient_homeomorph_merge ``Submission.DifferentialGeometry.Topology.PairedBallGluing.exists_quotient_homeomorph_merge

end DifferentialGeometry.Topology.PairedBallGluing
