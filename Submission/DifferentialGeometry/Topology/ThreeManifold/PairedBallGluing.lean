import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.PuncturedQuotient
import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.QuotientTransport
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

def flagMap (p : E × Bool) (x : E3) : Σ v, (N v).Carrier :=
  ⟨endpoint p.1 p.2, (chart p.1 p.2).chart x⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.flagMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.flagMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.flagMap ``Submission.DifferentialGeometry.Topology.PairedBallGluing.flagMap

abbrev PuncturedFactor (v : V) :=
  {x : (N v).Carrier // Sigma.mk v x ∉ ⋃ p, flagMap N endpoint chart p '' _root_.Metric.ball (0 : E3) 1}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.PuncturedFactor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.PuncturedFactor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.PuncturedFactor ``Submission.DifferentialGeometry.Topology.PairedBallGluing.PuncturedFactor

def incidenceChart (v : V) (p : {p : E × Bool // endpoint p.1 p.2 = v}) :
    OrientedBallChart (N v).toClosedOrientedManifold :=
  p.property ▸ chart p.val.1 p.val.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.incidenceChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.incidenceChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.incidenceChart ``Submission.DifferentialGeometry.Topology.PairedBallGluing.incidenceChart

@[simp] theorem incidenceChart_sigma_apply (v : V)
    (p : {p : E × Bool // endpoint p.1 p.2 = v}) (x : E3) :
    Sigma.mk v ((incidenceChart N endpoint chart v p).chart x) =
      flagMap N endpoint chart p.val x := by
  obtain ⟨p, hp⟩ := p
  subst v
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.incidenceChart_sigma_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.incidenceChart_sigma_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.incidenceChart_sigma_apply ``Submission.DifferentialGeometry.Topology.PairedBallGluing.incidenceChart_sigma_apply

theorem pairwise_disjoint_incidenceChart_image (v : V)
    (hdisj : Pairwise fun p q =>
      Disjoint (flagMap N endpoint chart p '' _root_.Metric.closedBall (0 : E3) 2)
        (flagMap N endpoint chart q '' _root_.Metric.closedBall (0 : E3) 2)) :
    Pairwise fun p q : {p : E × Bool // endpoint p.1 p.2 = v} =>
      Disjoint ((incidenceChart N endpoint chart v p).chart '' _root_.Metric.closedBall (0 : E3) 2)
        ((incidenceChart N endpoint chart v q).chart '' _root_.Metric.closedBall (0 : E3) 2) := by
  intro p q hpq
  rw [_root_.Set.disjoint_left]
  rintro x ⟨y, hy, hyx⟩ ⟨z, hz, hzx⟩
  apply disjoint_left.mp (hdisj (fun h => hpq (Subtype.ext h)))
    (⟨y, hy, rfl⟩ : flagMap N endpoint chart p.val y ∈
      flagMap N endpoint chart p.val '' _root_.Metric.closedBall (0 : E3) 2)
  refine ⟨z, hz, ?_⟩
  rw [← incidenceChart_sigma_apply N endpoint chart v p,
    ← incidenceChart_sigma_apply N endpoint chart v q, hyx, hzx]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.pairwise_disjoint_incidenceChart_image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.pairwise_disjoint_incidenceChart_image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.pairwise_disjoint_incidenceChart_image ``Submission.DifferentialGeometry.Topology.PairedBallGluing.pairwise_disjoint_incidenceChart_image

def remainingIncidenceChart (s : E) (v : V)
    (p : {p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = v}) :
    OrientedBallChart (N v).toClosedOrientedManifold :=
  incidenceChart N endpoint chart v ⟨p.val, p.property.2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.remainingIncidenceChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.remainingIncidenceChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.remainingIncidenceChart ``Submission.DifferentialGeometry.Topology.PairedBallGluing.remainingIncidenceChart

@[simp] theorem remainingIncidenceChart_sigma_apply (s : E) (v : V)
    (p : {p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = v}) (x : E3) :
    Sigma.mk v ((remainingIncidenceChart N endpoint chart s v p).chart x) =
      flagMap N endpoint chart p.val x :=
  incidenceChart_sigma_apply N endpoint chart v ⟨p.val, p.property.2⟩ x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.remainingIncidenceChart_sigma_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.remainingIncidenceChart_sigma_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.remainingIncidenceChart_sigma_apply ``Submission.DifferentialGeometry.Topology.PairedBallGluing.remainingIncidenceChart_sigma_apply

theorem pairwise_disjoint_remainingIncidenceChart_image (s : E) (v : V)
    (hdisj : Pairwise fun p q =>
      Disjoint (flagMap N endpoint chart p '' _root_.Metric.closedBall (0 : E3) 2)
        (flagMap N endpoint chart q '' _root_.Metric.closedBall (0 : E3) 2)) :
    Pairwise fun p q : {p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = v} =>
      Disjoint ((remainingIncidenceChart N endpoint chart s v p).chart '' _root_.Metric.closedBall (0 : E3) 2)
        ((remainingIncidenceChart N endpoint chart s v q).chart '' _root_.Metric.closedBall (0 : E3) 2) := by
  intro p q hpq
  exact pairwise_disjoint_incidenceChart_image N endpoint chart v hdisj
    (fun h => hpq (Subtype.ext (congrArg
      (fun z : {p : E × Bool // endpoint p.1 p.2 = v} => z.val) h)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.pairwise_disjoint_remainingIncidenceChart_image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.pairwise_disjoint_remainingIncidenceChart_image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.pairwise_disjoint_remainingIncidenceChart_image ``Submission.DifferentialGeometry.Topology.PairedBallGluing.pairwise_disjoint_remainingIncidenceChart_image

theorem remainingIncidenceChart_avoids_selected (s : E) (b : Bool)
    (hdisj : Pairwise fun p q =>
      Disjoint (flagMap N endpoint chart p '' _root_.Metric.closedBall (0 : E3) 2)
        (flagMap N endpoint chart q '' _root_.Metric.closedBall (0 : E3) 2))
    (p : {p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s b})
    (x : E3) (hx : x ∈ _root_.Metric.closedBall (0 : E3) 2) :
    (remainingIncidenceChart N endpoint chart s (endpoint s b) p).chart x ∉
      (chart s b).chart '' _root_.Metric.closedBall (0 : E3) 1 := by
  rintro ⟨y, hy, hyx⟩
  have hpne : p.val ≠ (s, b) := fun h => p.property.1 (congrArg Prod.fst h)
  apply disjoint_left.mp (hdisj hpne)
    (⟨x, hx, rfl⟩ : flagMap N endpoint chart p.val x ∈
      flagMap N endpoint chart p.val '' _root_.Metric.closedBall (0 : E3) 2)
  refine ⟨y, _root_.Metric.closedBall_subset_closedBall (by norm_num) hy, ?_⟩
  rw [← remainingIncidenceChart_sigma_apply N endpoint chart s (endpoint s b) p]
  exact congrArg (Sigma.mk (endpoint s b)) hyx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.remainingIncidenceChart_avoids_selected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.remainingIncidenceChart_avoids_selected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.remainingIncidenceChart_avoids_selected ``Submission.DifferentialGeometry.Topology.PairedBallGluing.remainingIncidenceChart_avoids_selected

theorem selected_holes_iff (s : E) (b : Bool)
    (hends : endpoint s _root_.Bool.false ≠ endpoint s _root_.Bool.true) (x : (N (endpoint s b)).Carrier) :
    Sigma.mk (endpoint s b) x ∈ ⋃ p, flagMap N endpoint chart p '' _root_.Metric.ball (0 : E3) 1 ↔
      x ∈ (chart s b).chart '' _root_.Metric.ball (0 : E3) 1 ∨
        x ∈ ⋃ p, (remainingIncidenceChart N endpoint chart s (endpoint s b) p).chart ''
          ball (0 : E3) 1 := by
  have hinj : Function.Injective (fun x : (N (endpoint s b)).Carrier =>
      (⟨endpoint s b, x⟩ : Σ v, (N v).Carrier)) := by
    intro x y h
    cases h
    rfl
  constructor
  · intro hx
    obtain ⟨p, y, hy, hyx⟩ := mem_iUnion.mp hx
    have hpv : endpoint p.1 p.2 = endpoint s b := congrArg Sigma.fst hyx
    by_cases hps : p.1 = s
    · have hpb : p.2 = b := by
        obtain ⟨t, t'⟩ := p
        dsimp at hps hpv ⊢
        subst t
        cases t' <;> cases b <;> simp_all
      have hp : p = (s, b) := Prod.ext hps hpb
      subst p
      exact Or.inl ⟨y, hy, hinj hyx⟩
    · refine Or.inr (mem_iUnion.mpr ⟨⟨p, hps, hpv⟩, y, hy, ?_⟩)
      apply hinj
      exact (remainingIncidenceChart_sigma_apply N endpoint chart s (endpoint s b)
        ⟨p, hps, hpv⟩ y).trans hyx
  · rintro (⟨y, hy, rfl⟩ | hx)
    · exact mem_iUnion.mpr ⟨(s, b), y, hy, rfl⟩
    · obtain ⟨p, y, hy, hyx⟩ := mem_iUnion.mp hx
      refine mem_iUnion.mpr ⟨p.val, y, hy, ?_⟩
      exact (remainingIncidenceChart_sigma_apply N endpoint chart s (endpoint s b) p y).symm.trans
        (congrArg (Sigma.mk (endpoint s b)) hyx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.selected_holes_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.selected_holes_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.selected_holes_iff ``Submission.DifferentialGeometry.Topology.PairedBallGluing.selected_holes_iff

def selectedPuncturedFactorHomeomorph (s : E) (b : Bool)
    (hends : endpoint s _root_.Bool.false ≠ endpoint s _root_.Bool.true) :
    PuncturedFactor N endpoint chart (endpoint s b) ≃ₜ
      {x : (chart s b).Punctured // x.val ∉
        ⋃ p, (remainingIncidenceChart N endpoint chart s (endpoint s b) p).chart ''
          _root_.Metric.ball (0 : E3) 1} where
  toFun x := ⟨⟨x.val, fun h => x.property
      ((selected_holes_iff N endpoint chart s b hends x.val).mpr (Or.inl h))⟩,
    fun h => x.property
      ((selected_holes_iff N endpoint chart s b hends x.val).mpr (Or.inr h))⟩
  invFun x := ⟨x.val.val, fun h =>
    ((selected_holes_iff N endpoint chart s b hends x.val.val).mp h).elim
      x.val.property x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.selectedPuncturedFactorHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.selectedPuncturedFactorHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.selectedPuncturedFactorHomeomorph ``Submission.DifferentialGeometry.Topology.PairedBallGluing.selectedPuncturedFactorHomeomorph

@[simp] theorem selectedPuncturedFactorHomeomorph_apply_val (s : E) (b : Bool)
    (hends : endpoint s _root_.Bool.false ≠ endpoint s _root_.Bool.true)
    (x : PuncturedFactor N endpoint chart (endpoint s b)) :
    (selectedPuncturedFactorHomeomorph N endpoint chart s b hends x).val.val = x.val := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.selectedPuncturedFactorHomeomorph_apply_val then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.selectedPuncturedFactorHomeomorph_apply_val"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.selectedPuncturedFactorHomeomorph_apply_val ``Submission.DifferentialGeometry.Topology.PairedBallGluing.selectedPuncturedFactorHomeomorph_apply_val

@[simp] theorem selectedPuncturedFactorHomeomorph_symm_apply_val (s : E) (b : Bool)
    (hends : endpoint s _root_.Bool.false ≠ endpoint s _root_.Bool.true)
    (x : {x : (chart s b).Punctured // x.val ∉
      ⋃ p, (remainingIncidenceChart N endpoint chart s (endpoint s b) p).chart ''
        _root_.Metric.ball (0 : E3) 1}) :
    ((selectedPuncturedFactorHomeomorph N endpoint chart s b hends).symm x).val = x.val.val := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.selectedPuncturedFactorHomeomorph_symm_apply_val then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.selectedPuncturedFactorHomeomorph_symm_apply_val"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.selectedPuncturedFactorHomeomorph_symm_apply_val ``Submission.DifferentialGeometry.Topology.PairedBallGluing.selectedPuncturedFactorHomeomorph_symm_apply_val

theorem boundary_not_mem_holes
    (hdisj : Pairwise fun p q =>
      Disjoint (flagMap N endpoint chart p '' _root_.Metric.closedBall (0 : E3) 2)
        (flagMap N endpoint chart q '' _root_.Metric.closedBall (0 : E3) 2))
    (e : E) (b : Bool) (z : _root_.Metric.sphere (0 : E3) 1) :
    flagMap N endpoint chart (e, b) z ∉
      ⋃ p, flagMap N endpoint chart p '' _root_.Metric.ball (0 : E3) 1 := by
  intro hz
  obtain ⟨p, y, hy, hyz⟩ := mem_iUnion.mp hz
  by_cases hp : p = (e, b)
  · subst p
    have hinj : Function.Injective (fun x : (N (endpoint e b)).Carrier =>
        (⟨endpoint e b, x⟩ : Σ v, (N v).Carrier)) := by
      intro x y h
      cases h
      rfl
    exact (chart e b).boundaryMap z |>.property ⟨y, hy, hinj hyz⟩
  · exact disjoint_left.mp (hdisj hp)
      ⟨y, ball_subset_closedBall.trans (_root_.Metric.closedBall_subset_closedBall (by norm_num)) hy, hyz⟩
      ⟨z, sphere_subset_closedBall.trans (_root_.Metric.closedBall_subset_closedBall (by norm_num)) z.property,
        rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.boundary_not_mem_holes then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.boundary_not_mem_holes"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.boundary_not_mem_holes ``Submission.DifferentialGeometry.Topology.PairedBallGluing.boundary_not_mem_holes

def boundaryPoint
    (hdisj : Pairwise fun p q =>
      Disjoint (flagMap N endpoint chart p '' _root_.Metric.closedBall (0 : E3) 2)
        (flagMap N endpoint chart q '' _root_.Metric.closedBall (0 : E3) 2))
    (e : E) (b : Bool) (z : _root_.Metric.sphere (0 : E3) 1) :
    PuncturedFactor N endpoint chart (endpoint e b) :=
  ⟨(chart e b).chart z, boundary_not_mem_holes N endpoint chart hdisj e b z⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.boundaryPoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.boundaryPoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.boundaryPoint ``Submission.DifferentialGeometry.Topology.PairedBallGluing.boundaryPoint

@[simp] theorem boundaryPoint_val
    (hdisj : Pairwise fun p q =>
      Disjoint (flagMap N endpoint chart p '' _root_.Metric.closedBall (0 : E3) 2)
        (flagMap N endpoint chart q '' _root_.Metric.closedBall (0 : E3) 2))
    (e : E) (b : Bool) (z : _root_.Metric.sphere (0 : E3) 1) :
    (boundaryPoint N endpoint chart hdisj e b z).val = (chart e b).chart z := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.boundaryPoint_val then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.boundaryPoint_val"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.boundaryPoint_val ``Submission.DifferentialGeometry.Topology.PairedBallGluing.boundaryPoint_val

theorem continuous_boundaryPoint
    (hdisj : Pairwise fun p q =>
      Disjoint (flagMap N endpoint chart p '' _root_.Metric.closedBall (0 : E3) 2)
        (flagMap N endpoint chart q '' _root_.Metric.closedBall (0 : E3) 2))
    (e : E) (b : Bool) : Continuous (boundaryPoint N endpoint chart hdisj e b) :=
  ((chart e b).continuous_boundaryMap.subtype_val).subtype_mk _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.continuous_boundaryPoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.continuous_boundaryPoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.continuous_boundaryPoint ``Submission.DifferentialGeometry.Topology.PairedBallGluing.continuous_boundaryPoint

def seamRel
    (hdisj : Pairwise fun p q =>
      Disjoint (flagMap N endpoint chart p '' _root_.Metric.closedBall (0 : E3) 2)
        (flagMap N endpoint chart q '' _root_.Metric.closedBall (0 : E3) 2))
    (s : E) (a : BoundaryAttachment)
    (x y : Σ v, PuncturedFactor N endpoint chart v) : Prop :=
  ∃ z : _root_.Metric.sphere (0 : E3) 1,
    (x = ⟨endpoint s _root_.Bool.false, boundaryPoint N endpoint chart hdisj s _root_.Bool.false z⟩ ∧
      y = ⟨endpoint s _root_.Bool.true, boundaryPoint N endpoint chart hdisj s _root_.Bool.true (a.1 z)⟩) ∨
    (y = ⟨endpoint s _root_.Bool.false, boundaryPoint N endpoint chart hdisj s _root_.Bool.false z⟩ ∧
      x = ⟨endpoint s _root_.Bool.true, boundaryPoint N endpoint chart hdisj s _root_.Bool.true (a.1 z)⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.seamRel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.seamRel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.seamRel ``Submission.DifferentialGeometry.Topology.PairedBallGluing.seamRel

private theorem boundaryPoint_cast_sigma
    (hdisj : Pairwise fun p q =>
      Disjoint (flagMap N endpoint chart p '' _root_.Metric.closedBall (0 : E3) 2)
        (flagMap N endpoint chart q '' _root_.Metric.closedBall (0 : E3) 2))
    (v : V) (p : E × Bool) (hp : endpoint p.1 p.2 = v) (z : _root_.Metric.sphere (0 : E3) 1) :
    (⟨v, hp ▸ boundaryPoint N endpoint chart hdisj p.1 p.2 z⟩ :
      Σ v, PuncturedFactor N endpoint chart v) =
        ⟨endpoint p.1 p.2, boundaryPoint N endpoint chart hdisj p.1 p.2 z⟩ := by
  subst v
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PairedBallGluing.boundaryPoint_cast_sigma
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PairedBallGluing.boundaryPoint_cast_sigma target :: scope.openDecls } }

private theorem boundaryPoint_cast_val
    (hdisj : Pairwise fun p q =>
      Disjoint (flagMap N endpoint chart p '' _root_.Metric.closedBall (0 : E3) 2)
        (flagMap N endpoint chart q '' _root_.Metric.closedBall (0 : E3) 2))
    (v : V) (p : E × Bool) (hp : endpoint p.1 p.2 = v) (z : _root_.Metric.sphere (0 : E3) 1) :
    (hp ▸ boundaryPoint N endpoint chart hdisj p.1 p.2 z).val =
      (incidenceChart N endpoint chart v ⟨p, hp⟩).chart z := by
  subst v
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PairedBallGluing.boundaryPoint_cast_val
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PairedBallGluing.boundaryPoint_cast_val target :: scope.openDecls } }

theorem exists_seam_quotient_homeomorph
    (hdisj : Pairwise fun p q =>
      Disjoint (flagMap N endpoint chart p '' _root_.Metric.closedBall (0 : E3) 2)
        (flagMap N endpoint chart q '' _root_.Metric.closedBall (0 : E3) 2))
    (s : E) (a : BoundaryAttachment) (hends : endpoint s _root_.Bool.false ≠ endpoint s _root_.Bool.true) :
    let L := {p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s _root_.Bool.false}
    let R := {p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s _root_.Bool.true}
    let CS := smoothConnectedSum (N (endpoint s _root_.Bool.false)) (N (endpoint s _root_.Bool.true))
      (chart s _root_.Bool.false) (chart s _root_.Bool.true) a
    ∃ b : L ⊕ R → OrientedBallChart CS.toConnectedClosedOrientedManifold.toClosedOrientedManifold,
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
      (Pairwise fun p q => Disjoint ((b p).chart '' _root_.Metric.closedBall (0 : E3) 2)
        ((b q).chart '' _root_.Metric.closedBall (0 : E3) 2)) ∧
      ∃ H : Quot (seamRel N endpoint chart hdisj s a) ≃ₜ
          {q : CS.toConnectedClosedOrientedManifold.Carrier //
            q ∉ ⋃ p, (b p).chart '' _root_.Metric.ball (0 : E3) 1} ⊕
          (Σ v : {v // v ≠ endpoint s _root_.Bool.false ∧ v ≠ endpoint s _root_.Bool.true},
            PuncturedFactor N endpoint chart v.val),
        (∀ x : PuncturedFactor N endpoint chart (endpoint s _root_.Bool.false),
          ∃ y, H (Quot.mk _ ⟨endpoint s _root_.Bool.false, x⟩) = Sum.inl y ∧
            y.val = ConnectedSumQuotient.inl (chart s _root_.Bool.false).toBallChart
              (chart s _root_.Bool.true).toBallChart a.1.toHomeomorph
              (selectedPuncturedFactorHomeomorph N endpoint chart s _root_.Bool.false hends x).val) ∧
        (∀ x : PuncturedFactor N endpoint chart (endpoint s _root_.Bool.true),
          ∃ y, H (Quot.mk _ ⟨endpoint s _root_.Bool.true, x⟩) = Sum.inl y ∧
            y.val = ConnectedSumQuotient.inr (chart s _root_.Bool.false).toBallChart
              (chart s _root_.Bool.true).toBallChart a.1.toHomeomorph
              (selectedPuncturedFactorHomeomorph N endpoint chart s _root_.Bool.true hends x).val) ∧
        (∀ (v : {v // v ≠ endpoint s _root_.Bool.false ∧ v ≠ endpoint s _root_.Bool.true})
          (x : PuncturedFactor N endpoint chart v.val),
          H (Quot.mk _ ⟨v.val, x⟩) = Sum.inr ⟨v, x⟩) ∧
        (∀ (p : L) (z : _root_.Metric.sphere (0 : E3) 1),
          ∃ y, H (Quot.mk _ ⟨endpoint p.val.1 p.val.2,
            boundaryPoint N endpoint chart hdisj p.val.1 p.val.2 z⟩) = Sum.inl y ∧
              y.val = (b (Sum.inl p)).chart z) ∧
        (∀ (p : R) (z : _root_.Metric.sphere (0 : E3) 1),
          ∃ y, H (Quot.mk _ ⟨endpoint p.val.1 p.val.2,
            boundaryPoint N endpoint chart hdisj p.val.1 p.val.2 z⟩) = Sum.inl y ∧
              y.val = (b (Sum.inr p)).chart z) := by
  dsimp only
  let c := chart s _root_.Bool.false
  let d := chart s _root_.Bool.true
  let eL := remainingIncidenceChart N endpoint chart s (endpoint s _root_.Bool.false)
  let eR := remainingIncidenceChart N endpoint chart s (endpoint s _root_.Bool.true)
  obtain ⟨b, hbL, hbR, hbdisj, _, _, l, r, hl, hr, H, hHL, hHR⟩ :=
    ConnectedSumQuotient.exists_orientedBallChart_sum_family_complement_homeomorph c d a eL eR
      (remainingIncidenceChart_avoids_selected N endpoint chart s _root_.Bool.false hdisj)
      (remainingIncidenceChart_avoids_selected N endpoint chart s _root_.Bool.true hdisj)
      (pairwise_disjoint_remainingIncidenceChart_image N endpoint chart s (endpoint s _root_.Bool.false) hdisj)
      (pairwise_disjoint_remainingIncidenceChart_image N endpoint chart s (endpoint s _root_.Bool.true) hdisj)
  let B := boundaryPoint N endpoint chart hdisj s _root_.Bool.false
  let D := boundaryPoint N endpoint chart hdisj s _root_.Bool.true ∘ a.1
  let EL := selectedPuncturedFactorHomeomorph N endpoint chart s _root_.Bool.false hends
  let ER := selectedPuncturedFactorHomeomorph N endpoint chart s _root_.Bool.true hends
  have hEL (z : _root_.Metric.sphere (0 : E3) 1) : EL (B z) = l z := by
    apply Subtype.ext
    exact (hl z).symm
  have hER (z : _root_.Metric.sphere (0 : E3) 1) : ER (D z) = (r ∘ a.1) z := by
    apply Subtype.ext
    exact (hr (a.1 z)).symm
  let J := adjunctionSpaceHomeomorphOfHomeomorph B D l (r ∘ a.1)
    (Homeomorph.refl _) EL ER hEL hER
  let K := (Homeomorph.sigmaAdjunction (PuncturedFactor N endpoint chart)
      (endpoint s _root_.Bool.false) (endpoint s _root_.Bool.true) hends B D).trans
    (Homeomorph.sumCongr (J.trans H) (Homeomorph.refl _))
  have hKL (x : PuncturedFactor N endpoint chart (endpoint s _root_.Bool.false)) :
      ∃ y, K (Quot.mk _ ⟨endpoint s _root_.Bool.false, x⟩) = Sum.inl y ∧
        y.val = ConnectedSumQuotient.inl c.toBallChart d.toBallChart a.1.toHomeomorph
          (EL x).val := by
    refine ⟨H (adjunctionCell l (r ∘ a.1) (EL x)), ?_, hHL (EL x)⟩
    change (Homeomorph.sumCongr (J.trans H) (Homeomorph.refl _))
      (Homeomorph.sigmaAdjunction (PuncturedFactor N endpoint chart)
        (endpoint s _root_.Bool.false) (endpoint s _root_.Bool.true) hends B D (Quot.mk _ ⟨endpoint s _root_.Bool.false, x⟩)) = _
    rw [Homeomorph.sigmaAdjunction_mk_left]
    rfl
  have hKR (x : PuncturedFactor N endpoint chart (endpoint s _root_.Bool.true)) :
      ∃ y, K (Quot.mk _ ⟨endpoint s _root_.Bool.true, x⟩) = Sum.inl y ∧
        y.val = ConnectedSumQuotient.inr c.toBallChart d.toBallChart a.1.toHomeomorph
          (ER x).val := by
    refine ⟨H (adjunctionLower (i := l) (r ∘ a.1) (ER x)), ?_, hHR (ER x)⟩
    change (Homeomorph.sumCongr (J.trans H) (Homeomorph.refl _))
      (Homeomorph.sigmaAdjunction (PuncturedFactor N endpoint chart)
        (endpoint s _root_.Bool.false) (endpoint s _root_.Bool.true) hends B D (Quot.mk _ ⟨endpoint s _root_.Bool.true, x⟩)) = _
    rw [Homeomorph.sigmaAdjunction_mk_right]
    rfl
  have hKU (v : {v // v ≠ endpoint s _root_.Bool.false ∧ v ≠ endpoint s _root_.Bool.true})
      (x : PuncturedFactor N endpoint chart v.val) :
      K (Quot.mk _ ⟨v.val, x⟩) = Sum.inr ⟨v, x⟩ := by
    change (Homeomorph.sumCongr (J.trans H) (Homeomorph.refl _))
      (Homeomorph.sigmaAdjunction (PuncturedFactor N endpoint chart)
        (endpoint s _root_.Bool.false) (endpoint s _root_.Bool.true) hends B D (Quot.mk _ ⟨v.val, x⟩)) = _
    rw [Homeomorph.sigmaAdjunction_mk_remaining]
    rfl
  refine ⟨b, hbL, hbR, hbdisj, K, hKL, hKR, hKU, ?_, ?_⟩
  · intro p z
    let x : PuncturedFactor N endpoint chart (endpoint s _root_.Bool.false) :=
      p.property.2 ▸ boundaryPoint N endpoint chart hdisj p.val.1 p.val.2 z
    have hxSigma : (⟨endpoint s _root_.Bool.false, x⟩ : Σ v, PuncturedFactor N endpoint chart v) =
        ⟨endpoint p.val.1 p.val.2, boundaryPoint N endpoint chart hdisj p.val.1 p.val.2 z⟩ := by
      exact boundaryPoint_cast_sigma N endpoint chart hdisj (endpoint s _root_.Bool.false)
        p.val p.property.2 z
    have hxVal : x.val = (eL p).chart z := by
      exact boundaryPoint_cast_val N endpoint chart hdisj (endpoint s _root_.Bool.false)
        p.val p.property.2 z
    obtain ⟨y, hy, hyVal⟩ := hKL x
    refine ⟨y, ?_, ?_⟩
    · exact (congrArg (fun q => K (Quot.mk _ q)) hxSigma).symm.trans hy
    · obtain ⟨hx, hb⟩ := hbL p z
        (sphere_subset_closedBall.trans (_root_.Metric.closedBall_subset_closedBall (by norm_num)) z.property)
      refine hyVal.trans ((congrArg (ConnectedSumQuotient.inl c.toBallChart d.toBallChart
        a.1.toHomeomorph) (Subtype.ext hxVal)).trans hb.symm)
  · intro p z
    let x : PuncturedFactor N endpoint chart (endpoint s _root_.Bool.true) :=
      p.property.2 ▸ boundaryPoint N endpoint chart hdisj p.val.1 p.val.2 z
    have hxSigma : (⟨endpoint s _root_.Bool.true, x⟩ : Σ v, PuncturedFactor N endpoint chart v) =
        ⟨endpoint p.val.1 p.val.2, boundaryPoint N endpoint chart hdisj p.val.1 p.val.2 z⟩ := by
      exact boundaryPoint_cast_sigma N endpoint chart hdisj (endpoint s _root_.Bool.true)
        p.val p.property.2 z
    have hxVal : x.val = (eR p).chart z := by
      exact boundaryPoint_cast_val N endpoint chart hdisj (endpoint s _root_.Bool.true)
        p.val p.property.2 z
    obtain ⟨y, hy, hyVal⟩ := hKR x
    refine ⟨y, ?_, ?_⟩
    · exact (congrArg (fun q => K (Quot.mk _ q)) hxSigma).symm.trans hy
    · obtain ⟨hx, hb⟩ := hbR p z
        (sphere_subset_closedBall.trans (_root_.Metric.closedBall_subset_closedBall (by norm_num)) z.property)
      refine hyVal.trans ((congrArg (ConnectedSumQuotient.inr c.toBallChart d.toBallChart
        a.1.toHomeomorph) (Subtype.ext hxVal)).trans hb.symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.exists_seam_quotient_homeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.exists_seam_quotient_homeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.exists_seam_quotient_homeomorph ``Submission.DifferentialGeometry.Topology.PairedBallGluing.exists_seam_quotient_homeomorph

end DifferentialGeometry.Topology.PairedBallGluing
