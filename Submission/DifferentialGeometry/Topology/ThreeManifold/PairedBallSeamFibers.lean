import Submission.DifferentialGeometry.Topology.ThreeManifold.PairedBallSeam

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Function _root_.Metric _root_.Submission.Metric
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.Topology.PairedBallGluing

private theorem eq_of_eqvGen_of_no_relation {X : Type*} {r : X → X → Prop} {x y : X}
    (hl : ∀ z, ¬ r x z) (hr : ∀ z, ¬ r z x) (h : Relation.EqvGen r x y) : x = y := by
  have hm : ∀ {a b : X}, Relation.EqvGen r a b → (a = x ↔ b = x) := by
    intro a b hab
    induction hab with
    | rel a b hab =>
      constructor
      · intro ha
        subst a
        exact (hl b hab).elim
      · intro hb
        subst b
        exact (hr a hab).elim
    | refl => exact Iff.rfl
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ihab ihbc => exact ihab.trans ihbc
  exact ((hm h).mp rfl).symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PairedBallGluing.eq_of_eqvGen_of_no_relation
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PairedBallGluing.eq_of_eqvGen_of_no_relation target :: scope.openDecls } }

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
  (hdisj : Pairwise fun p q =>
    Disjoint (flagMap N endpoint chart p '' closedBall (0 : E3) 2)
      (flagMap N endpoint chart q '' closedBall (0 : E3) 2))

theorem radialPoint_sigma_ne_boundaryPoint
    {s e : E} (b c : Bool) (hflags : (s, b) ≠ (e, c))
    (z y : _root_.Metric.sphere (0 : E3) 1) (r : ℝ) (hr : r ∈ _root_.Set.Icc 1 2) :
    (⟨endpoint s b, radialPoint N endpoint chart hdisj s b z r hr⟩ :
      Σ v, PuncturedFactor N endpoint chart v) ≠
      ⟨endpoint e c, boundaryPoint N endpoint chart hdisj e c y⟩ := by
  intro heq
  have hflag : flagMap N endpoint chart (s, b) (r • z.val) =
      flagMap N endpoint chart (e, c) y.val :=
    congrArg (fun x : Σ v, PuncturedFactor N endpoint chart v =>
      (⟨x.fst, x.snd.val⟩ : Σ v, (N v).Carrier)) heq
  have hrad : r • z.val ∈ _root_.Metric.closedBall (0 : E3) 2 := by
    rw [_root_.Metric.mem_closedBall, dist_zero_right, BallChart.norm_radial z (by linarith [hr.1])]
    exact hr.2
  have hy : y.val ∈ _root_.Metric.closedBall (0 : E3) 2 :=
    (_root_.Metric.closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2))
      (_root_.Metric.sphere_subset_closedBall y.property)
  exact disjoint_left.mp (hdisj hflags)
    ⟨r • z.val, hrad, hflag⟩ ⟨y.val, hy, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.radialPoint_sigma_ne_boundaryPoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.radialPoint_sigma_ne_boundaryPoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.radialPoint_sigma_ne_boundaryPoint ``Submission.DifferentialGeometry.Topology.PairedBallGluing.radialPoint_sigma_ne_boundaryPoint

theorem boundaryPoint_mem_seamCore_of_ne
    {s e : E} (hse : s ≠ e) (b : Bool) (z : _root_.Metric.sphere (0 : E3) 1) :
    (⟨endpoint e b, boundaryPoint N endpoint chart hdisj e b z⟩ :
      Σ v, PuncturedFactor N endpoint chart v) ∈ seamCore N endpoint chart hdisj s := by
  rintro (⟨y, hy⟩ | ⟨y, hy⟩)
  · have hne := radialPoint_sigma_ne_boundaryPoint N endpoint chart hdisj
      _root_.Bool.false b (fun h => hse (congrArg Prod.fst h)) y z 1 (by norm_num)
    rw [radialPoint_one] at hne
    exact hne hy
  · have hne := radialPoint_sigma_ne_boundaryPoint N endpoint chart hdisj
      _root_.Bool.true b (fun h => hse (congrArg Prod.fst h)) y z 1 (by norm_num)
    rw [radialPoint_one] at hne
    exact hne hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.boundaryPoint_mem_seamCore_of_ne then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.boundaryPoint_mem_seamCore_of_ne"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.boundaryPoint_mem_seamCore_of_ne ``Submission.DifferentialGeometry.Topology.PairedBallGluing.boundaryPoint_mem_seamCore_of_ne

theorem quot_mk_eq_iff_of_mem_seamCore
    (s : E) (a : BoundaryAttachment)
    (x y : Σ v, PuncturedFactor N endpoint chart v)
    (hy : y ∈ seamCore N endpoint chart hdisj s) :
    Quot.mk (seamRel N endpoint chart hdisj s a) x = Quot.mk _ y ↔ x = y := by
  have hyb (b : Bool) (z : _root_.Metric.sphere (0 : E3) 1) :
      y ≠ ⟨endpoint s b, boundaryPoint N endpoint chart hdisj s b z⟩ := by
    intro heq
    cases b with
    | false => exact hy (Or.inl ⟨z, heq.symm⟩)
    | true => exact hy (Or.inr ⟨z, heq.symm⟩)
  have hl (z : Σ v, PuncturedFactor N endpoint chart v) :
      ¬ seamRel N endpoint chart hdisj s a y z := by
    rintro ⟨p, h | h⟩
    · exact hyb _root_.Bool.false p h.1
    · exact hyb _root_.Bool.true (a.val p) h.2
  have hr (z : Σ v, PuncturedFactor N endpoint chart v) :
      ¬ seamRel N endpoint chart hdisj s a z y := by
    rintro ⟨p, h | h⟩
    · exact hyb _root_.Bool.true (a.val p) h.2
    · exact hyb _root_.Bool.false p h.1
  constructor
  · intro h
    exact (eq_of_eqvGen_of_no_relation hl hr (Quot.eqvGen_exact h.symm)).symm
  · rintro rfl
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.quot_mk_eq_iff_of_mem_seamCore then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.quot_mk_eq_iff_of_mem_seamCore"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.quot_mk_eq_iff_of_mem_seamCore ``Submission.DifferentialGeometry.Topology.PairedBallGluing.quot_mk_eq_iff_of_mem_seamCore

theorem quot_mk_eq_boundaryPoint_iff_of_ne
    (s : E) (a : BoundaryAttachment) {e : E} (hse : s ≠ e)
    (b : Bool) (z : _root_.Metric.sphere (0 : E3) 1)
    (x : Σ v, PuncturedFactor N endpoint chart v) :
    Quot.mk (seamRel N endpoint chart hdisj s a) x =
        Quot.mk _ ⟨endpoint e b, boundaryPoint N endpoint chart hdisj e b z⟩ ↔
      x = ⟨endpoint e b, boundaryPoint N endpoint chart hdisj e b z⟩ :=
  quot_mk_eq_iff_of_mem_seamCore N endpoint chart hdisj s a x _
    (boundaryPoint_mem_seamCore_of_ne N endpoint chart hdisj hse b z)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.quot_mk_eq_boundaryPoint_iff_of_ne then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.quot_mk_eq_boundaryPoint_iff_of_ne"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.quot_mk_eq_boundaryPoint_iff_of_ne ``Submission.DifferentialGeometry.Topology.PairedBallGluing.quot_mk_eq_boundaryPoint_iff_of_ne

theorem quot_mk_radialPoint_ne_boundaryPoint
    (s : E) (a : BoundaryAttachment) {e : E} (hse : s ≠ e)
    (b c : Bool) (z y : _root_.Metric.sphere (0 : E3) 1) (r : ℝ) (hr : r ∈ _root_.Set.Icc 1 2) :
    Quot.mk (seamRel N endpoint chart hdisj s a)
        ⟨endpoint s b, radialPoint N endpoint chart hdisj s b z r hr⟩ ≠
      Quot.mk _ ⟨endpoint e c, boundaryPoint N endpoint chart hdisj e c y⟩ := by
  intro h
  exact radialPoint_sigma_ne_boundaryPoint N endpoint chart hdisj b c
    (fun h => hse (congrArg Prod.fst h)) z y r hr
    ((quot_mk_eq_boundaryPoint_iff_of_ne N endpoint chart hdisj s a hse c y _).mp h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.quot_mk_radialPoint_ne_boundaryPoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.quot_mk_radialPoint_ne_boundaryPoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.quot_mk_radialPoint_ne_boundaryPoint ``Submission.DifferentialGeometry.Topology.PairedBallGluing.quot_mk_radialPoint_ne_boundaryPoint

theorem seamChart_ne_quot_mk_boundaryPoint
    (s : E) (a : BoundaryAttachment) {e : E} (hse : s ≠ e)
    (p : SelfAttachment.directSeamDomain) (b : Bool) (z : _root_.Metric.sphere (0 : E3) 1) :
    seamChart N endpoint chart hdisj s a p ≠
      Quot.mk _ ⟨endpoint e b, boundaryPoint N endpoint chart hdisj e b z⟩ := by
  unfold seamChart
  split_ifs with hp
  · exact quot_mk_radialPoint_ne_boundaryPoint N endpoint chart hdisj s a hse
      _root_.Bool.false b p.val.1 z (1 + p.val.2) _
  · exact quot_mk_radialPoint_ne_boundaryPoint N endpoint chart hdisj s a hse
      _root_.Bool.true b (a.val p.val.1) z (1 - p.val.2) _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.seamChart_ne_quot_mk_boundaryPoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.seamChart_ne_quot_mk_boundaryPoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.seamChart_ne_quot_mk_boundaryPoint ``Submission.DifferentialGeometry.Topology.PairedBallGluing.seamChart_ne_quot_mk_boundaryPoint

end DifferentialGeometry.Topology.PairedBallGluing
