import Submission.DifferentialGeometry.Topology.ThreeManifold.PartialGraphRealization

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.Topology

universe u v w

local notation "S²" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
local notation "Tube" => S² × Set.Icc (-2 : ℝ) 2

namespace MarkedBall

variable {N : ClosedOrientedManifold.{u} 3}

theorem disjoint_range_ball {B B' : MarkedBall N} (h : Disjoint B.collar B'.collar) :
    Disjoint (_root_.Set.range B.ball) (_root_.Set.range B'.ball) :=
  h.mono B.ball_subset_collar B'.ball_subset_collar

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedBall.disjoint_range_ball then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedBall.disjoint_range_ball"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedBall.disjoint_range_ball ``Submission.DifferentialGeometry.Topology.MarkedBall.disjoint_range_ball

theorem boundary_not_mem_own_interior (B : MarkedBall N) (z : S²) :
    B.boundary z ∉ (_root_.Set.range B.ball \ _root_.Set.range (B.ball ∘ sphereToClosedCell)) :=
  fun hx => hx.2 (_root_.Set.mem_range_self (f := B.ball ∘ sphereToClosedCell) z)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedBall.boundary_not_mem_own_interior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedBall.boundary_not_mem_own_interior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedBall.boundary_not_mem_own_interior ``Submission.DifferentialGeometry.Topology.MarkedBall.boundary_not_mem_own_interior

end MarkedBall

namespace MarkedManifoldGraph

variable (G : MarkedManifoldGraph.{u})

theorem mem_flagBall_cast_iff (e : G.Edge) (b : Bool) (v : G.Vertex)
    (hv : G.endpoint e b = v) (x : (G.vertexManifold v).Carrier) :
    (x ∈ hv ▸ _root_.Set.range (G.flag e b).ball) ↔ (hv.symm ▸ x ∈ _root_.Set.range (G.flag e b).ball) := by
  cases hv
  exact Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.mem_flagBall_cast_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.mem_flagBall_cast_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.mem_flagBall_cast_iff ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.mem_flagBall_cast_iff

theorem mem_flagInterior_cast_iff (e : G.Edge) (b : Bool) (v : G.Vertex)
    (hv : G.endpoint e b = v) (x : (G.vertexManifold v).Carrier) :
    (x ∈ hv ▸ (_root_.Set.range (G.flag e b).ball \
        _root_.Set.range ((G.flag e b).ball ∘ sphereToClosedCell))) ↔
      (hv.symm ▸ x ∈ _root_.Set.range (G.flag e b).ball \
        range ((G.flag e b).ball ∘ sphereToClosedCell)) := by
  cases hv
  exact Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.mem_flagInterior_cast_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.mem_flagInterior_cast_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.mem_flagInterior_cast_iff ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.mem_flagInterior_cast_iff

theorem flagBall_cast_subset_collar (e : G.Edge) (b : Bool) (v : G.Vertex)
    (hv : G.endpoint e b = v) :
    hv ▸ _root_.Set.range (G.flag e b).ball ⊆ hv ▸ (G.flag e b).collar := by
  cases hv
  exact (G.flag e b).ball_subset_collar

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.flagBall_cast_subset_collar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.flagBall_cast_subset_collar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.flagBall_cast_subset_collar ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.flagBall_cast_subset_collar

theorem flagBoundary_not_mem_own_flagInterior_cast (e : G.Edge) (b : Bool)
    (hv : G.endpoint e b = G.endpoint e b) (z : S²) :
    ¬ ((G.flag e b).ball (sphereToClosedCell z) ∈ hv ▸
      (_root_.Set.range (G.flag e b).ball \ _root_.Set.range ((G.flag e b).ball ∘ sphereToClosedCell))) := by
  intro hx
  rw [Subsingleton.elim hv rfl] at hx
  exact hx.2 (_root_.Set.mem_range_self (f := (G.flag e b).ball ∘ sphereToClosedCell) z)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.flagBoundary_not_mem_own_flagInterior_cast then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.flagBoundary_not_mem_own_flagInterior_cast"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.flagBoundary_not_mem_own_flagInterior_cast ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.flagBoundary_not_mem_own_flagInterior_cast

theorem flagBoundary_not_mem_removedBallSet (S : Finset G.Edge) (e : G.Edge) (b : Bool)
    (z : S²) :
    (G.flag e b).boundary z ∉ G.removedBallSet S (G.endpoint e b) := by
  rintro ⟨e', he', b', hv', hmem⟩
  by_cases hsame : (e, b) = (e', b')
  · cases hsame
    exact flagBoundary_not_mem_own_flagInterior_cast G e b hv' z hmem
  · have hne : (⟨(e, b), rfl⟩ :
        {p : G.Edge × Bool // G.endpoint p.1 p.2 = G.endpoint e b}) ≠
        ⟨(e', b'), hv'⟩ := fun hh => hsame (congrArg Subtype.val hh)
    have hdisj := G.flag_collar_disjoint (G.endpoint e b) ⟨(e, b), rfl⟩ ⟨(e', b'), hv'⟩ hne
    have hball : Disjoint (_root_.Set.range (G.flag e b).ball)
        (hv' ▸ _root_.Set.range (G.flag e' b').ball) :=
      hdisj.mono (G.flag e b).ball_subset_collar
        (flagBall_cast_subset_collar G e' b' (G.endpoint e b) hv')
    refine Set.disjoint_left.mp hball
      (_root_.Set.mem_range_self (f := (G.flag e b).ball) (sphereToClosedCell z)) ?_
    exact (mem_flagBall_cast_iff G e' b' (G.endpoint e b) hv' _).mpr
      (((mem_flagInterior_cast_iff G e' b' (G.endpoint e b) hv' _).mp hmem).1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.flagBoundary_not_mem_removedBallSet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.flagBoundary_not_mem_removedBallSet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.flagBoundary_not_mem_removedBallSet ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.flagBoundary_not_mem_removedBallSet

theorem flagBall_not_mem_removedBallSet (S : Finset G.Edge) (e : G.Edge) (b : Bool)
    (he : e ∉ S) (x : ClosedCell 3) :
    (G.flag e b).ball x ∉ G.removedBallSet S (G.endpoint e b) := by
  rintro ⟨e', he', b', hv', hmem⟩
  have hne : (⟨(e, b), rfl⟩ :
      {p : G.Edge × Bool // G.endpoint p.1 p.2 = G.endpoint e b}) ≠
      ⟨(e', b'), hv'⟩ := by
    intro hh
    have hv : e = e' := congrArg (fun p : G.Edge × Bool => p.1) (congrArg Subtype.val hh)
    exact he (hv ▸ he')
  have hdisj := G.flag_collar_disjoint (G.endpoint e b) ⟨(e, b), rfl⟩ ⟨(e', b'), hv'⟩ hne
  have hball : Disjoint (_root_.Set.range (G.flag e b).ball)
      (hv' ▸ _root_.Set.range (G.flag e' b').ball) :=
    hdisj.mono (G.flag e b).ball_subset_collar
      (flagBall_cast_subset_collar G e' b' (G.endpoint e b) hv')
  refine Set.disjoint_left.mp hball (_root_.Set.mem_range_self (f := (G.flag e b).ball) x) ?_
  exact (mem_flagBall_cast_iff G e' b' (G.endpoint e b) hv' _).mpr
    (((mem_flagInterior_cast_iff G e' b' (G.endpoint e b) hv' _).mp hmem).1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.flagBall_not_mem_removedBallSet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.flagBall_not_mem_removedBallSet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.flagBall_not_mem_removedBallSet ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.flagBall_not_mem_removedBallSet

def flagBoundaryPoint (S : Finset G.Edge) (e : G.Edge) (b : Bool) (z : S²) :
    G.puncturedCarrier S (G.endpoint e b) :=
  ⟨(G.flag e b).boundary z, G.flagBoundary_not_mem_removedBallSet S e b z⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.flagBoundaryPoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.flagBoundaryPoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.flagBoundaryPoint ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.flagBoundaryPoint

def flagBallPoint (S : Finset G.Edge) (e : G.Edge) (b : Bool) (he : e ∉ S)
    (x : ClosedCell 3) : G.puncturedCarrier S (G.endpoint e b) :=
  ⟨(G.flag e b).ball x, G.flagBall_not_mem_removedBallSet S e b he x⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.flagBallPoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.flagBallPoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.flagBallPoint ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.flagBallPoint

theorem flagBoundaryPoint_coe (S : Finset G.Edge) (e : G.Edge) (b : Bool) (z : S²) :
    (G.flagBoundaryPoint S e b z).1 = (G.flag e b).boundary z := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.flagBoundaryPoint_coe then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.flagBoundaryPoint_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.flagBoundaryPoint_coe ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.flagBoundaryPoint_coe

theorem flagBallPoint_coe (S : Finset G.Edge) (e : G.Edge) (b : Bool) (he : e ∉ S)
    (x : ClosedCell 3) : (G.flagBallPoint S e b he x).1 = (G.flag e b).ball x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.flagBallPoint_coe then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.flagBallPoint_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.flagBallPoint_coe ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.flagBallPoint_coe

end MarkedManifoldGraph

def tubeEndLevel (b : Bool) : Set.Icc (-2 : ℝ) 2 :=
  if b then ⟨2, by norm_num⟩ else ⟨-2, by norm_num⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.tubeEndLevel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.tubeEndLevel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.tubeEndLevel ``Submission.DifferentialGeometry.Topology.tubeEndLevel

@[simp] theorem tubeEndLevel_false : tubeEndLevel _root_.Bool.false = ⟨-2, by norm_num⟩ := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.tubeEndLevel_false then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.tubeEndLevel_false"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.tubeEndLevel_false ``Submission.DifferentialGeometry.Topology.tubeEndLevel_false

@[simp] theorem tubeEndLevel_true : tubeEndLevel _root_.Bool.true = ⟨2, by norm_num⟩ := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.tubeEndLevel_true then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.tubeEndLevel_true"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.tubeEndLevel_true ``Submission.DifferentialGeometry.Topology.tubeEndLevel_true

def sphereBasePoint : S² := ⟨EuclideanSpace.single 0 1, by simp⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereBasePoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereBasePoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereBasePoint ``Submission.DifferentialGeometry.Topology.sphereBasePoint

namespace MarkedManifoldGraph

variable (G : MarkedManifoldGraph.{u})

abbrev stepCarrier (S : Finset G.Edge) (e : G.Edge) : Type u :=
  G.puncturedCarrier (_root_.Insert.insert e S) (G.endpoint e _root_.Bool.false) ⊕ Tube ⊕
    G.puncturedCarrier (_root_.Insert.insert e S) (G.endpoint e _root_.Bool.true)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.stepCarrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.stepCarrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.stepCarrier ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.stepCarrier

def stepRel (S : Finset G.Edge) (e : G.Edge) :
    G.stepCarrier S e → G.stepCarrier S e → Prop :=
  fun x y =>
    (∃ z : S², x = Sum.inl (G.flagBoundaryPoint (_root_.Insert.insert e S) e _root_.Bool.false z) ∧
      y = Sum.inr (Sum.inl (z, tubeEndLevel _root_.Bool.false))) ∨
    (∃ z : S², y = Sum.inl (G.flagBoundaryPoint (_root_.Insert.insert e S) e _root_.Bool.false z) ∧
      x = Sum.inr (Sum.inl (z, tubeEndLevel _root_.Bool.false))) ∨
    (∃ z : S², x = Sum.inr (Sum.inl (z, tubeEndLevel _root_.Bool.true)) ∧
      y = Sum.inr (Sum.inr (G.flagBoundaryPoint (_root_.Insert.insert e S) e _root_.Bool.true z))) ∨
    (∃ z : S², y = Sum.inr (Sum.inl (z, tubeEndLevel _root_.Bool.true)) ∧
      x = Sum.inr (Sum.inr (G.flagBoundaryPoint (_root_.Insert.insert e S) e _root_.Bool.true z)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.stepRel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.stepRel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.stepRel ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.stepRel

abbrev stepQuotient (S : Finset G.Edge) (e : G.Edge) : Type u := Quot (G.stepRel S e)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.stepQuotient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.stepQuotient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.stepQuotient ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.stepQuotient

def stepQuotientMap (S : Finset G.Edge) (e : G.Edge) :
    C(G.stepCarrier S e, G.stepQuotient S e) :=
  ⟨Quot.mk _, continuous_quot_mk⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.stepQuotientMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.stepQuotientMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.stepQuotientMap ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.stepQuotientMap

theorem stepQuotientMap_isQuotientMap (S : Finset G.Edge) (e : G.Edge) :
    Topology.IsQuotientMap (G.stepQuotientMap S e :
      G.stepCarrier S e → G.stepQuotient S e) :=
  isQuotientMap_quot_mk

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.stepQuotientMap_isQuotientMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.stepQuotientMap_isQuotientMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.stepQuotientMap_isQuotientMap ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.stepQuotientMap_isQuotientMap

theorem stepQuotient_seam_source (S : Finset G.Edge) (e : G.Edge) (z : S²) :
    Quot.mk (G.stepRel S e) (Sum.inl (G.flagBoundaryPoint (_root_.Insert.insert e S) e _root_.Bool.false z)) =
      Quot.mk (G.stepRel S e) (Sum.inr (Sum.inl (z, tubeEndLevel _root_.Bool.false))) :=
  Quot.sound (Or.inl ⟨z, rfl, rfl⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.stepQuotient_seam_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.stepQuotient_seam_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.stepQuotient_seam_source ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.stepQuotient_seam_source

theorem stepQuotient_seam_target (S : Finset G.Edge) (e : G.Edge) (z : S²) :
    Quot.mk (G.stepRel S e) (Sum.inr (Sum.inl (z, tubeEndLevel _root_.Bool.true))) =
      Quot.mk (G.stepRel S e) (Sum.inr (Sum.inr (G.flagBoundaryPoint (_root_.Insert.insert e S) e _root_.Bool.true z))) :=
  Quot.sound (Or.inr (Or.inr (Or.inl ⟨z, rfl, rfl⟩)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.stepQuotient_seam_target then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.stepQuotient_seam_target"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.stepQuotient_seam_target ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.stepQuotient_seam_target

theorem nonempty_stepQuotient (S : Finset G.Edge) (e : G.Edge) :
    Nonempty (G.stepQuotient S e) :=
  ⟨Quot.mk (G.stepRel S e)
    (Sum.inl (G.flagBoundaryPoint (_root_.Insert.insert e S) e _root_.Bool.false sphereBasePoint))⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.nonempty_stepQuotient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.nonempty_stepQuotient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.nonempty_stepQuotient ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.nonempty_stepQuotient

theorem stepQuotient_seam_source_sphereBasePoint (S : Finset G.Edge) (e : G.Edge) :
    Quot.mk (G.stepRel S e)
        (Sum.inl (G.flagBoundaryPoint (_root_.Insert.insert e S) e _root_.Bool.false sphereBasePoint)) =
      Quot.mk (G.stepRel S e) (Sum.inr (Sum.inl (sphereBasePoint, tubeEndLevel _root_.Bool.false))) :=
  G.stepQuotient_seam_source S e sphereBasePoint

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.stepQuotient_seam_source_sphereBasePoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.stepQuotient_seam_source_sphereBasePoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.stepQuotient_seam_source_sphereBasePoint ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.stepQuotient_seam_source_sphereBasePoint

theorem adjunctionCell_flagBoundaryPoint_eq_adjunctionLower (S : Finset G.Edge) (e : G.Edge)
    (z : S²) :
    adjunctionCell (G.flagBoundaryPoint (_root_.Insert.insert e S) e _root_.Bool.false)
        (fun z : S² => (z, tubeEndLevel _root_.Bool.false))
        (G.flagBoundaryPoint (_root_.Insert.insert e S) e _root_.Bool.false z) =
      adjunctionLower (i := G.flagBoundaryPoint (_root_.Insert.insert e S) e _root_.Bool.false)
        (fun z : S² => (z, tubeEndLevel _root_.Bool.false)) (z, tubeEndLevel _root_.Bool.false) :=
  adjunction_coherence _ _ z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.adjunctionCell_flagBoundaryPoint_eq_adjunctionLower then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.adjunctionCell_flagBoundaryPoint_eq_adjunctionLower"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.adjunctionCell_flagBoundaryPoint_eq_adjunctionLower ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.adjunctionCell_flagBoundaryPoint_eq_adjunctionLower

end MarkedManifoldGraph

namespace PartialRealization

variable {G : MarkedManifoldGraph.{u}} {S : Finset G.Edge}

def cylinderEnd (P : PartialRealization G S) (e : G.Edge) (he : e ∈ S) (b : Bool) :
    S² → P.realization.Carrier :=
  fun z => P.cylinderPiece e he (z, tubeEndLevel b)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PartialRealization.cylinderEnd then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PartialRealization.cylinderEnd"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PartialRealization.cylinderEnd ``Submission.DifferentialGeometry.Topology.PartialRealization.cylinderEnd

def SeamEquation (P : PartialRealization G S) (e : G.Edge) (he : e ∈ S) : Prop :=
  (∀ z : S², P.cylinderEnd e he _root_.Bool.false z =
      P.vertexPiece (G.endpoint e _root_.Bool.false) (G.flagBoundaryPoint S e _root_.Bool.false z)) ∧
    (∀ z : S², P.cylinderEnd e he _root_.Bool.true z =
      P.vertexPiece (G.endpoint e _root_.Bool.true) (G.flagBoundaryPoint S e _root_.Bool.true z))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PartialRealization.SeamEquation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PartialRealization.SeamEquation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PartialRealization.SeamEquation ``Submission.DifferentialGeometry.Topology.PartialRealization.SeamEquation

theorem range_cylinderEnd_source_eq (P : PartialRealization G S) (e : G.Edge) (he : e ∈ S)
    (h : P.SeamEquation e he) :
    _root_.Set.range (P.cylinderEnd e he _root_.Bool.false) =
      range (fun z : S² => P.vertexPiece (G.endpoint e _root_.Bool.false) (G.flagBoundaryPoint S e _root_.Bool.false z)) :=
  congrArg _root_.Set.range (funext h.1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PartialRealization.range_cylinderEnd_source_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PartialRealization.range_cylinderEnd_source_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PartialRealization.range_cylinderEnd_source_eq ``Submission.DifferentialGeometry.Topology.PartialRealization.range_cylinderEnd_source_eq

theorem range_cylinderEnd_target_eq (P : PartialRealization G S) (e : G.Edge) (he : e ∈ S)
    (h : P.SeamEquation e he) :
    _root_.Set.range (P.cylinderEnd e he _root_.Bool.true) =
      range (fun z : S² => P.vertexPiece (G.endpoint e _root_.Bool.true) (G.flagBoundaryPoint S e _root_.Bool.true z)) :=
  congrArg _root_.Set.range (funext h.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PartialRealization.range_cylinderEnd_target_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PartialRealization.range_cylinderEnd_target_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PartialRealization.range_cylinderEnd_target_eq ``Submission.DifferentialGeometry.Topology.PartialRealization.range_cylinderEnd_target_eq

theorem range_cylinderEnd_source_subset_vertexPiece (P : PartialRealization G S) (e : G.Edge)
    (he : e ∈ S) (h : P.SeamEquation e he) :
    range (P.cylinderEnd e he _root_.Bool.false) ⊆ _root_.Set.range (P.vertexPiece (G.endpoint e _root_.Bool.false)) :=
  fun _ ⟨z, hz⟩ => ⟨G.flagBoundaryPoint S e _root_.Bool.false z, (h.1 z).symm.trans hz⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PartialRealization.range_cylinderEnd_source_subset_vertexPiece then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PartialRealization.range_cylinderEnd_source_subset_vertexPiece"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PartialRealization.range_cylinderEnd_source_subset_vertexPiece ``Submission.DifferentialGeometry.Topology.PartialRealization.range_cylinderEnd_source_subset_vertexPiece

theorem range_cylinderEnd_target_subset_vertexPiece (P : PartialRealization G S) (e : G.Edge)
    (he : e ∈ S) (h : P.SeamEquation e he) :
    range (P.cylinderEnd e he _root_.Bool.true) ⊆ _root_.Set.range (P.vertexPiece (G.endpoint e _root_.Bool.true)) :=
  fun _ ⟨z, hz⟩ => ⟨G.flagBoundaryPoint S e _root_.Bool.true z, (h.2 z).symm.trans hz⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PartialRealization.range_cylinderEnd_target_subset_vertexPiece then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PartialRealization.range_cylinderEnd_target_subset_vertexPiece"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PartialRealization.range_cylinderEnd_target_subset_vertexPiece ``Submission.DifferentialGeometry.Topology.PartialRealization.range_cylinderEnd_target_subset_vertexPiece

variable {e : G.Edge}

def stepMap (P : PartialRealization G (_root_.Insert.insert e S)) :
    G.stepCarrier S e → P.realization.Carrier :=
  Sum.elim (P.vertexPiece (G.endpoint e _root_.Bool.false))
    (Sum.elim (P.cylinderPiece e (Finset.mem_insert_self e S))
      (P.vertexPiece (G.endpoint e _root_.Bool.true)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PartialRealization.stepMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PartialRealization.stepMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PartialRealization.stepMap ``Submission.DifferentialGeometry.Topology.PartialRealization.stepMap

@[simp] theorem stepMap_left (P : PartialRealization G (_root_.Insert.insert e S))
    (y : G.puncturedCarrier (_root_.Insert.insert e S) (G.endpoint e _root_.Bool.false)) :
    P.stepMap (Sum.inl y) = P.vertexPiece (G.endpoint e _root_.Bool.false) y := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PartialRealization.stepMap_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PartialRealization.stepMap_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PartialRealization.stepMap_left ``Submission.DifferentialGeometry.Topology.PartialRealization.stepMap_left

@[simp] theorem stepMap_cylinder (P : PartialRealization G (_root_.Insert.insert e S))
    (q : Tube) :
    P.stepMap (Sum.inr (Sum.inl q)) = P.cylinderPiece e (Finset.mem_insert_self e S) q := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PartialRealization.stepMap_cylinder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PartialRealization.stepMap_cylinder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PartialRealization.stepMap_cylinder ``Submission.DifferentialGeometry.Topology.PartialRealization.stepMap_cylinder

@[simp] theorem stepMap_right (P : PartialRealization G (_root_.Insert.insert e S))
    (w : G.puncturedCarrier (_root_.Insert.insert e S) (G.endpoint e _root_.Bool.true)) :
    P.stepMap (Sum.inr (Sum.inr w)) = P.vertexPiece (G.endpoint e _root_.Bool.true) w := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PartialRealization.stepMap_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PartialRealization.stepMap_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PartialRealization.stepMap_right ``Submission.DifferentialGeometry.Topology.PartialRealization.stepMap_right

theorem stepMap_continuous (P : PartialRealization G (_root_.Insert.insert e S)) :
    Continuous (P.stepMap) :=
  (P.vertexPiece (G.endpoint e _root_.Bool.false)).continuous.sumElim
    ((P.cylinderPiece e (Finset.mem_insert_self e S)).continuous.sumElim
      (P.vertexPiece (G.endpoint e _root_.Bool.true)).continuous)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PartialRealization.stepMap_continuous then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PartialRealization.stepMap_continuous"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PartialRealization.stepMap_continuous ``Submission.DifferentialGeometry.Topology.PartialRealization.stepMap_continuous

theorem seamEquation_iff_stepRel_related (P : PartialRealization G (_root_.Insert.insert e S)) :
    P.SeamEquation e (Finset.mem_insert_self e S) ↔
      ∀ x y, G.stepRel S e x y → P.stepMap x = P.stepMap y := by
  constructor
  · rintro ⟨hs, ht⟩ x y h
    rcases h with ⟨z, rfl, rfl⟩ | ⟨z, rfl, rfl⟩ | ⟨z, rfl, rfl⟩ | ⟨z, rfl, rfl⟩
    · simpa [cylinderEnd] using (hs z).symm
    · simpa [cylinderEnd] using hs z
    · simpa [cylinderEnd] using ht z
    · simpa [cylinderEnd] using (ht z).symm
  · intro h
    exact ⟨fun z => by simpa [cylinderEnd] using (h _ _ (Or.inl ⟨z, rfl, rfl⟩)).symm,
      fun z => by
        simpa [cylinderEnd] using h _ _ (Or.inr (Or.inr (Or.inl ⟨z, rfl, rfl⟩)))⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PartialRealization.seamEquation_iff_stepRel_related then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PartialRealization.seamEquation_iff_stepRel_related"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PartialRealization.seamEquation_iff_stepRel_related ``Submission.DifferentialGeometry.Topology.PartialRealization.seamEquation_iff_stepRel_related

theorem eqvGen_stepMap_eq (P : PartialRealization G (_root_.Insert.insert e S))
    (h : ∀ x y, G.stepRel S e x y → P.stepMap x = P.stepMap y) {x y : G.stepCarrier S e}
    (hxy : Relation.EqvGen (G.stepRel S e) x y) : P.stepMap x = P.stepMap y := by
  induction hxy with
  | rel a b hab => exact h a b hab
  | refl => rfl
  | symm a b hab ih => exact ih.symm
  | trans a b c hab hbc ih1 ih2 => exact ih1.trans ih2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PartialRealization.eqvGen_stepMap_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PartialRealization.eqvGen_stepMap_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PartialRealization.eqvGen_stepMap_eq ``Submission.DifferentialGeometry.Topology.PartialRealization.eqvGen_stepMap_eq

theorem seamEquation_iff_factorsThrough (P : PartialRealization G (_root_.Insert.insert e S)) :
    P.SeamEquation e (Finset.mem_insert_self e S) ↔
      Function.FactorsThrough (P.stepMap) (Quot.mk (G.stepRel S e)) := by
  constructor
  · intro hs x y hxy
    exact P.eqvGen_stepMap_eq ((P.seamEquation_iff_stepRel_related).mp hs)
      (Quot.eq.mp hxy)
  · intro hf
    exact (P.seamEquation_iff_stepRel_related).mpr fun x y hr => hf (Quot.sound hr)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PartialRealization.seamEquation_iff_factorsThrough then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PartialRealization.seamEquation_iff_factorsThrough"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PartialRealization.seamEquation_iff_factorsThrough ``Submission.DifferentialGeometry.Topology.PartialRealization.seamEquation_iff_factorsThrough

theorem exists_stepLift (P : PartialRealization G (_root_.Insert.insert e S))
    (h : P.SeamEquation e (Finset.mem_insert_self e S)) :
    ∃ F : C(G.stepQuotient S e, P.realization.Carrier),
      ∀ x, F (Quot.mk (G.stepRel S e) x) = P.stepMap x := by
  have hq := G.stepQuotientMap_isQuotientMap S e
  refine ⟨hq.lift ⟨P.stepMap, P.stepMap_continuous⟩
    ((P.seamEquation_iff_factorsThrough).mp h), ?_⟩
  intro x
  exact congrArg (fun k : C(G.stepCarrier S e, P.realization.Carrier) =>
    (k : G.stepCarrier S e → P.realization.Carrier) x)
    (hq.lift_comp ⟨P.stepMap, P.stepMap_continuous⟩
      ((P.seamEquation_iff_factorsThrough).mp h))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PartialRealization.exists_stepLift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PartialRealization.exists_stepLift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PartialRealization.exists_stepLift ``Submission.DifferentialGeometry.Topology.PartialRealization.exists_stepLift

end PartialRealization

theorem adjunctionLower_eq_of_not_mem_range {A : Type v} {B : Type w} {X : Type u}
    {i : A → B} {φ : A → X} {x y : X} (hx : x ∉ _root_.Set.range φ)
    (h : adjunctionLower (i := i) φ x = adjunctionLower (i := i) φ y) : x = y := by
  have key : ∀ p q : B ⊕ X, Relation.EqvGen (adjunctionRel i φ) p q →
      (p = Sum.inr x ↔ q = Sum.inr x) := by
    intro p q hpq
    induction hpq with
    | rel a b hab =>
      obtain ⟨c, hc | hc⟩ := hab
      · obtain ⟨rfl, rfl⟩ := hc
        exact ⟨fun h => absurd h (by simp),
          fun h => absurd (hx ⟨c, Sum.inr.inj h⟩) (by simp)⟩
      · obtain ⟨rfl, rfl⟩ := hc
        exact ⟨fun h => absurd (hx ⟨c, Sum.inr.inj h⟩) (by simp),
          fun h => absurd h (by simp)⟩
    | refl a => exact Iff.rfl
    | symm a b hab ih => exact ih.symm
    | trans a b c hab hbc ih1 ih2 => exact ih1.trans ih2
  have hgen : Relation.EqvGen (adjunctionRel i φ) (Sum.inr x) (Sum.inr y) :=
    Quot.eq.mp (show Quot.mk (adjunctionRel i φ) (Sum.inr x) =
      Quot.mk (adjunctionRel i φ) (Sum.inr y) from h)
  exact (Sum.inr.inj ((key (Sum.inr x) (Sum.inr y) hgen).mp rfl)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.adjunctionLower_eq_of_not_mem_range then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.adjunctionLower_eq_of_not_mem_range"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.adjunctionLower_eq_of_not_mem_range ``Submission.DifferentialGeometry.Topology.adjunctionLower_eq_of_not_mem_range

theorem injOn_adjunctionLower_compl_range {A : Type v} {B : Type w} {X : Type u}
    {i : A → B} (φ : A → X) :
    Set.InjOn (adjunctionLower (i := i) φ) (_root_.Set.range φ)ᶜ := by
  intro x hx y hy h
  exact adjunctionLower_eq_of_not_mem_range hx h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.injOn_adjunctionLower_compl_range then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.injOn_adjunctionLower_compl_range"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.injOn_adjunctionLower_compl_range ``Submission.DifferentialGeometry.Topology.injOn_adjunctionLower_compl_range


namespace MarkedManifoldGraph

theorem disjoint_collar_if_flags_ne {N : ClosedOrientedManifold.{u} 3} {B B' : MarkedBall N}
    (hdisj : Disjoint B.collar B'.collar) {b b' : Bool} (hbb : b ≠ b') :
    Disjoint (if b then B' else B).collar (if b' then B' else B).collar := by
  have hsymm := hdisj.symm
  cases b <;> cases b' <;> simp_all

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.disjoint_collar_if_flags_ne then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.disjoint_collar_if_flags_ne"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.disjoint_collar_if_flags_ne ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.disjoint_collar_if_flags_ne

abbrev oneVertexLoop (N : ConnectedClosedOrientedManifold.{0} 3)
    (B B' : MarkedBall N.toClosedOrientedManifold) (hdisj : Disjoint B.collar B'.collar) :
    MarkedManifoldGraph.{0} where
  Vertex := PUnit
  Edge := PUnit
  vertexFintype := inferInstance
  edgeFintype := inferInstance
  edgeDecidableEq := inferInstance
  endpoint := fun _ _ => PUnit.unit
  vertexManifold := fun _ => N
  flag := fun _ b => if b then B' else B
  flag_collar_disjoint := fun v f f' hne => by
    obtain ⟨⟨u, b⟩, hb⟩ := f
    obtain ⟨⟨u', b'⟩, hb'⟩ := f'
    have hbb : b ≠ b' := fun h => hne (Subtype.ext (Prod.ext (Subsingleton.elim u u') h))
    subst hb
    cases hb'
    exact disjoint_collar_if_flags_ne hdisj hbb
  attach := fun _ b => (if b then B' else B).boundary
  attach_eq := fun _ b z => rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.oneVertexLoop then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.oneVertexLoop"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.oneVertexLoop ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.oneVertexLoop

end MarkedManifoldGraph

namespace PartialRealization

variable {G : MarkedManifoldGraph.{u}} {S : Finset G.Edge}

def FlagMarkerTransport (P : PartialRealization G S) (marked : Bool → MarkedBall P.realization)
    (e : G.Edge) (he : e ∉ S) : Prop :=
  ∀ (b : Bool) (x : ClosedCell 3),
    (marked b).ball x = P.vertexPiece (G.endpoint e b) (G.flagBallPoint S e b he x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PartialRealization.FlagMarkerTransport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PartialRealization.FlagMarkerTransport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PartialRealization.FlagMarkerTransport ``Submission.DifferentialGeometry.Topology.PartialRealization.FlagMarkerTransport

def MarkerReserve (P : PartialRealization G S) (marked : Bool → MarkedBall P.realization)
    (e : G.Edge) : Prop :=
  ∀ b : Bool, (marked b).collarBudget ≤ (G.flag e b).collarBudget

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PartialRealization.MarkerReserve then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PartialRealization.MarkerReserve"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PartialRealization.MarkerReserve ``Submission.DifferentialGeometry.Topology.PartialRealization.MarkerReserve

def MarkerCollarTransport (P : PartialRealization G S) (marked : Bool → MarkedBall P.realization)
    (e : G.Edge) : Prop :=
  ∀ b : Bool, _root_.Set.range (fun x : {y : (G.vertexManifold (G.endpoint e b)).Carrier //
      y ∈ (G.flag e b).collar ∧ y ∉ G.removedBallSet S (G.endpoint e b)} =>
        P.vertexPiece (G.endpoint e b) ⟨x.1, x.2.2⟩) ⊆ (marked b).collar

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PartialRealization.MarkerCollarTransport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PartialRealization.MarkerCollarTransport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PartialRealization.MarkerCollarTransport ``Submission.DifferentialGeometry.Topology.PartialRealization.MarkerCollarTransport

theorem range_markedBall_subset_vertexPiece (P : PartialRealization G S)
    {marked : Bool → MarkedBall P.realization} {e : G.Edge} {he : e ∉ S}
    (h : P.FlagMarkerTransport marked e he) (b : Bool) :
    range (marked b).ball ⊆ _root_.Set.range (P.vertexPiece (G.endpoint e b)) :=
  fun _ ⟨x, hx⟩ => ⟨G.flagBallPoint S e b he x, (h b x).symm.trans hx⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PartialRealization.range_markedBall_subset_vertexPiece then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PartialRealization.range_markedBall_subset_vertexPiece"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PartialRealization.range_markedBall_subset_vertexPiece ``Submission.DifferentialGeometry.Topology.PartialRealization.range_markedBall_subset_vertexPiece

theorem exists_markedBall_eq_vertexPiece (P : PartialRealization G S)
    {marked : Bool → MarkedBall P.realization} {e : G.Edge} {he : e ∉ S}
    (h : P.FlagMarkerTransport marked e he) (b : Bool) (x : ClosedCell 3) :
    ∃ y : G.puncturedCarrier S (G.endpoint e b),
      (marked b).ball x = P.vertexPiece (G.endpoint e b) y :=
  ⟨G.flagBallPoint S e b he x, h b x⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PartialRealization.exists_markedBall_eq_vertexPiece then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PartialRealization.exists_markedBall_eq_vertexPiece"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PartialRealization.exists_markedBall_eq_vertexPiece ``Submission.DifferentialGeometry.Topology.PartialRealization.exists_markedBall_eq_vertexPiece

end PartialRealization

namespace PartialRealization

def oneVertexLoopEmpty (N : ConnectedClosedOrientedManifold.{0} 3)
    (B B' : MarkedBall N.toClosedOrientedManifold) (hdisj : Disjoint B.collar B'.collar) :
    PartialRealization (MarkedManifoldGraph.oneVertexLoop N B B' hdisj) (∅ : Finset PUnit) where
  realization := N.toClosedOrientedManifold
  vertexPiece := fun _ => ⟨Subtype.val, continuous_subtype_val⟩
  cylinderPiece := fun e he => absurd he (Finset.notMem_empty e)
  survivingFlag := fun _ _ => B
  covers := fun x =>
    Or.inl ⟨PUnit.unit,
      ⟨x, by rintro ⟨e, he, -, -⟩; exact Finset.notMem_empty e he⟩, rfl⟩
  survivingFlag_collar_disjoint := fun _ _ _ _ hne => absurd rfl hne

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PartialRealization.oneVertexLoopEmpty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PartialRealization.oneVertexLoopEmpty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PartialRealization.oneVertexLoopEmpty ``Submission.DifferentialGeometry.Topology.PartialRealization.oneVertexLoopEmpty

theorem flagMarkerTransport_oneVertexLoopEmpty (N : ConnectedClosedOrientedManifold.{0} 3)
    (B B' : MarkedBall N.toClosedOrientedManifold) (hdisj : Disjoint B.collar B'.collar) :
    (oneVertexLoopEmpty N B B' hdisj).FlagMarkerTransport (fun b => if b then B' else B)
      PUnit.unit (Finset.notMem_empty PUnit.unit) :=
  fun _ _ => rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PartialRealization.flagMarkerTransport_oneVertexLoopEmpty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PartialRealization.flagMarkerTransport_oneVertexLoopEmpty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PartialRealization.flagMarkerTransport_oneVertexLoopEmpty ``Submission.DifferentialGeometry.Topology.PartialRealization.flagMarkerTransport_oneVertexLoopEmpty

theorem markerReserve_oneVertexLoopEmpty (N : ConnectedClosedOrientedManifold.{0} 3)
    (B B' : MarkedBall N.toClosedOrientedManifold) (hdisj : Disjoint B.collar B'.collar) :
    (oneVertexLoopEmpty N B B' hdisj).MarkerReserve (fun b => if b then B' else B) PUnit.unit :=
  fun _ => le_refl _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PartialRealization.markerReserve_oneVertexLoopEmpty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PartialRealization.markerReserve_oneVertexLoopEmpty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PartialRealization.markerReserve_oneVertexLoopEmpty ``Submission.DifferentialGeometry.Topology.PartialRealization.markerReserve_oneVertexLoopEmpty

theorem markerCollarTransport_oneVertexLoopEmpty (N : ConnectedClosedOrientedManifold.{0} 3)
    (B B' : MarkedBall N.toClosedOrientedManifold) (hdisj : Disjoint B.collar B'.collar) :
    (oneVertexLoopEmpty N B B' hdisj).MarkerCollarTransport (fun b => if b then B' else B)
      PUnit.unit := by
  intro b y hy
  obtain ⟨x, rfl⟩ := hy
  exact x.2.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PartialRealization.markerCollarTransport_oneVertexLoopEmpty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PartialRealization.markerCollarTransport_oneVertexLoopEmpty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PartialRealization.markerCollarTransport_oneVertexLoopEmpty ``Submission.DifferentialGeometry.Topology.PartialRealization.markerCollarTransport_oneVertexLoopEmpty

theorem injOn_vertexPiece_oneVertexLoopEmpty (N : ConnectedClosedOrientedManifold.{0} 3)
    (B B' : MarkedBall N.toClosedOrientedManifold) (hdisj : Disjoint B.collar B'.collar) :
    Set.InjOn ((oneVertexLoopEmpty N B B' hdisj).vertexPiece PUnit.unit)
      (_root_.Set.range ((MarkedManifoldGraph.oneVertexLoop N B B' hdisj).flagBallPoint ∅ PUnit.unit _root_.Bool.false
          (Finset.notMem_empty PUnit.unit)) ∪
        _root_.Set.range ((MarkedManifoldGraph.oneVertexLoop N B B' hdisj).flagBallPoint ∅ PUnit.unit _root_.Bool.true
          (Finset.notMem_empty PUnit.unit))) := by
  intro a _ b _ h
  exact Subtype.ext h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PartialRealization.injOn_vertexPiece_oneVertexLoopEmpty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PartialRealization.injOn_vertexPiece_oneVertexLoopEmpty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PartialRealization.injOn_vertexPiece_oneVertexLoopEmpty ``Submission.DifferentialGeometry.Topology.PartialRealization.injOn_vertexPiece_oneVertexLoopEmpty

theorem not_flagMarkerTransport_survivingFlag_oneVertexLoopEmpty
    (N : ConnectedClosedOrientedManifold.{0} 3)
    (B B' : MarkedBall N.toClosedOrientedManifold) (hdisj : Disjoint B.collar B'.collar)
    (hinj : Set.InjOn ((oneVertexLoopEmpty N B B' hdisj).vertexPiece PUnit.unit)
      (_root_.Set.range ((MarkedManifoldGraph.oneVertexLoop N B B' hdisj).flagBallPoint ∅ PUnit.unit _root_.Bool.false
          (Finset.notMem_empty PUnit.unit)) ∪
        _root_.Set.range ((MarkedManifoldGraph.oneVertexLoop N B B' hdisj).flagBallPoint ∅ PUnit.unit _root_.Bool.true
          (Finset.notMem_empty PUnit.unit)))) :
    ¬ (oneVertexLoopEmpty N B B' hdisj).FlagMarkerTransport
      (fun _ => (oneVertexLoopEmpty N B B' hdisj).survivingFlag PUnit.unit
        (Finset.notMem_empty PUnit.unit))
      PUnit.unit (Finset.notMem_empty PUnit.unit) := by
  intro htrans
  have hballs : B.ball = B'.ball := by
    funext x
    have h1 := htrans _root_.Bool.false x
    have h2 := htrans _root_.Bool.true x
    have h3 := h1.symm.trans h2
    exact congrArg Subtype.val (hinj
      (Or.inl (_root_.Set.mem_range_self (f := (MarkedManifoldGraph.oneVertexLoop N B B' hdisj).flagBallPoint
        ∅ PUnit.unit _root_.Bool.false (Finset.notMem_empty PUnit.unit)) x))
      (Or.inr (_root_.Set.mem_range_self (f := (MarkedManifoldGraph.oneVertexLoop N B B' hdisj).flagBallPoint
        ∅ PUnit.unit _root_.Bool.true (Finset.notMem_empty PUnit.unit)) x)) h3)
  refine Set.disjoint_left.mp (MarkedBall.disjoint_range_ball hdisj)
    (_root_.Set.mem_range_self (f := B.ball) (⟨0, by simp⟩ : ClosedCell 3)) ?_
  rw [← hballs]
  exact _root_.Set.mem_range_self (f := B.ball) (⟨0, by simp⟩ : ClosedCell 3)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PartialRealization.not_flagMarkerTransport_survivingFlag_oneVertexLoopEmpty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PartialRealization.not_flagMarkerTransport_survivingFlag_oneVertexLoopEmpty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PartialRealization.not_flagMarkerTransport_survivingFlag_oneVertexLoopEmpty ``Submission.DifferentialGeometry.Topology.PartialRealization.not_flagMarkerTransport_survivingFlag_oneVertexLoopEmpty

end PartialRealization

section OrientationSign

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem det_neg_trans_neg_pos (L M : E ≃ₗ[ℝ] E) (hL : (LinearEquiv.det L : ℝ) < 0)
    (hM : (LinearEquiv.det M : ℝ) < 0) : 0 < (LinearEquiv.det (L.trans M) : ℝ) := by
  rw [LinearEquiv.det_trans, Units.val_mul]
  exact mul_pos_of_neg_of_neg hM hL

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.det_neg_trans_neg_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.det_neg_trans_neg_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.det_neg_trans_neg_pos ``Submission.DifferentialGeometry.Topology.det_neg_trans_neg_pos

theorem det_neg_symm_neg (L : E ≃ₗ[ℝ] E) (hL : (LinearEquiv.det L : ℝ) < 0) :
    (LinearEquiv.det L.symm : ℝ) < 0 := by
  rw [LinearEquiv.det_symm, map_inv, Units.val_inv_eq_inv_val]
  exact inv_lt_zero'.mpr hL

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.det_neg_symm_neg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.det_neg_symm_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.det_neg_symm_neg ``Submission.DifferentialGeometry.Topology.det_neg_symm_neg

theorem exists_det_neg : ∃ σ : ℝ, σ < 0 := ⟨-1, by norm_num⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_det_neg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_det_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_det_neg ``Submission.DifferentialGeometry.Topology.exists_det_neg

end OrientationSign

end DifferentialGeometry.Topology
