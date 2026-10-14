import Submission.DifferentialGeometry.Topology.ThreeManifold.PartialRealizationAnalytic
import Submission.DifferentialGeometry.Topology.Attachment.SequentialGluing

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.Topology

local instance seamClosedCellCharted : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  Handle.closedCellChartedSpaceSucc 2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.seamClosedCellCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.seamClosedCellCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.seamClosedCellCharted ``Submission.DifferentialGeometry.Topology.seamClosedCellCharted

local instance seamClosedCellIsManifold : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) :=
  Handle.closedCellIsManifold 2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.seamClosedCellIsManifold then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.seamClosedCellIsManifold"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.seamClosedCellIsManifold ``Submission.DifferentialGeometry.Topology.seamClosedCellIsManifold

universe u

local notation "S²" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
local notation "Tube" => S² × Set.Icc (-2 : ℝ) 2

theorem sphereToClosedCell_injective : Function.Injective sphereToClosedCell := by
  intro z w h
  exact Subtype.ext (congrArg (fun u : ClosedCell 3 => (u : EuclideanSpace ℝ (Fin 3))) h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereToClosedCell_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereToClosedCell_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereToClosedCell_injective ``Submission.DifferentialGeometry.Topology.sphereToClosedCell_injective

theorem isEmbedding_sphereToClosedCell : Topology.IsEmbedding sphereToClosedCell :=
  ⟨Topology.IsInducing.subtypeVal.of_comp_iff.mp
      (show Topology.IsInducing
        ((Subtype.val : ClosedCell 3 → EuclideanSpace ℝ (Fin 3)) ∘ sphereToClosedCell)
        from Topology.IsInducing.subtypeVal),
    sphereToClosedCell_injective⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isEmbedding_sphereToClosedCell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isEmbedding_sphereToClosedCell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isEmbedding_sphereToClosedCell ``Submission.DifferentialGeometry.Topology.isEmbedding_sphereToClosedCell

theorem tubeEndLevel_false_ne_true : tubeEndLevel _root_.Bool.false ≠ tubeEndLevel true := by
  intro h
  have hval := congrArg (fun t : Set.Icc (-2 : ℝ) 2 => (t : ℝ)) h
  rw [tubeEndLevel_false, tubeEndLevel_true] at hval
  norm_num at hval

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.tubeEndLevel_false_ne_true then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.tubeEndLevel_false_ne_true"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.tubeEndLevel_false_ne_true ``Submission.DifferentialGeometry.Topology.tubeEndLevel_false_ne_true

theorem tubeEndLevel_ne {b b' : Bool} (h : b ≠ b') : tubeEndLevel b ≠ tubeEndLevel b' := by
  cases b <;> cases b'
  · exact absurd rfl h
  · exact tubeEndLevel_false_ne_true
  · exact fun hh => tubeEndLevel_false_ne_true hh.symm
  · exact absurd rfl h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.tubeEndLevel_ne then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.tubeEndLevel_ne"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.tubeEndLevel_ne ``Submission.DifferentialGeometry.Topology.tubeEndLevel_ne

namespace MarkedBall

variable {N : ClosedOrientedManifold.{u} 3}

theorem ball_ne_of_disjoint_collar {B B' : MarkedBall N} (h : Disjoint B.collar B'.collar) :
    B.ball ≠ B'.ball := by
  intro hball
  have hx : B.ball (closedCellCenter 3) ∈ _root_.Set.range B.ball := _root_.Set.mem_range_self _
  exact (Set.disjoint_left.mp (disjoint_range_ball h) hx) (by rw [← hball]; exact hx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedBall.ball_ne_of_disjoint_collar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedBall.ball_ne_of_disjoint_collar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedBall.ball_ne_of_disjoint_collar ``Submission.DifferentialGeometry.Topology.MarkedBall.ball_ne_of_disjoint_collar

end MarkedBall

namespace MarkedManifoldGraph

variable (G : MarkedManifoldGraph.{u})

theorem flagBoundary_injective (S : Finset G.Edge) (e : G.Edge) (b : Bool) :
    Function.Injective (G.flagBoundaryPoint S e b) := by
  intro z w h
  have hb : (G.flag e b).ball (sphereToClosedCell z) =
      (G.flag e b).ball (sphereToClosedCell w) := congrArg Subtype.val h
  exact sphereToClosedCell_injective ((G.flag e b).ball_embedding.isEmbedding.injective hb)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.flagBoundary_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.flagBoundary_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.flagBoundary_injective ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.flagBoundary_injective

theorem isEmbedding_flagBoundaryPoint (S : Finset G.Edge) (e : G.Edge) (b : Bool) :
    Topology.IsEmbedding (G.flagBoundaryPoint S e b) :=
  ((G.flag e b).ball_embedding.isEmbedding.comp isEmbedding_sphereToClosedCell).codRestrict
    {x | x ∉ G.removedBallSet S (G.endpoint e b)} fun z => (G.flagBoundaryPoint S e b z).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.isEmbedding_flagBoundaryPoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.isEmbedding_flagBoundaryPoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.isEmbedding_flagBoundaryPoint ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.isEmbedding_flagBoundaryPoint

def stepLeftLeg (S : Finset G.Edge) (e : G.Edge) : Bool → S² → G.stepCarrier S e
  | false, z => Sum.inl (G.flagBoundaryPoint (_root_.Insert.insert e S) e _root_.Bool.false z)
  | true, z => Sum.inr (Sum.inr (G.flagBoundaryPoint (_root_.Insert.insert e S) e _root_.Bool.true z))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.stepLeftLeg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.stepLeftLeg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.stepLeftLeg ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.stepLeftLeg

def stepTubeEndLeg (S : Finset G.Edge) (e : G.Edge) (b : Bool) : S² → G.stepCarrier S e :=
  fun z => Sum.inr (Sum.inl (z, tubeEndLevel b))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.stepTubeEndLeg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.stepTubeEndLeg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.stepTubeEndLeg ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.stepTubeEndLeg

theorem isEmbedding_stepLeftLeg (S : Finset G.Edge) (e : G.Edge) (b : Bool) :
    Topology.IsEmbedding (G.stepLeftLeg S e b) := by
  cases b with
  | false =>
    exact Topology.IsEmbedding.inl.comp (isEmbedding_flagBoundaryPoint G (_root_.Insert.insert e S) e _root_.Bool.false)
  | true =>
    exact Topology.IsEmbedding.inr.comp (Topology.IsEmbedding.inr.comp
      (isEmbedding_flagBoundaryPoint G (_root_.Insert.insert e S) e _root_.Bool.true))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.isEmbedding_stepLeftLeg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.isEmbedding_stepLeftLeg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.isEmbedding_stepLeftLeg ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.isEmbedding_stepLeftLeg

theorem isEmbedding_stepTubeEndLeg (S : Finset G.Edge) (e : G.Edge) (b : Bool) :
    Topology.IsEmbedding (G.stepTubeEndLeg S e b) :=
  Topology.IsEmbedding.inr.comp
    (Topology.IsEmbedding.inl.comp (isEmbedding_prodMkLeft (tubeEndLevel b)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.isEmbedding_stepTubeEndLeg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.isEmbedding_stepTubeEndLeg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.isEmbedding_stepTubeEndLeg ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.isEmbedding_stepTubeEndLeg

def stepAttaching (S : Finset G.Edge) (e : G.Edge) (b : Bool) :
    ↥(_root_.Set.range (G.stepLeftLeg S e b)) ≃ₜ ↥(_root_.Set.range (G.stepTubeEndLeg S e b)) :=
  ((isEmbedding_stepLeftLeg G S e b).toHomeomorph).symm.trans
    ((isEmbedding_stepTubeEndLeg G S e b).toHomeomorph)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.stepAttaching then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.stepAttaching"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.stepAttaching ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.stepAttaching

def stepBoundaryGluing (S : Finset G.Edge) (e : G.Edge) :
    BoundaryGluing (G.stepCarrier S e) Bool where
  left b := _root_.Set.range (G.stepLeftLeg S e b)
  right b := _root_.Set.range (G.stepTubeEndLeg S e b)
  attaching b := stepAttaching G S e b
  isClosed_left b := isClosed_range_of_continuous_of_compactSpace
    (isEmbedding_stepLeftLeg G S e b).toIsInducing.continuous
  isClosed_right b := isClosed_range_of_continuous_of_compactSpace
    (isEmbedding_stepTubeEndLeg G S e b).toIsInducing.continuous
  disjoint_left_right b := by
    rw [Set.disjoint_left]
    intro x hx hy
    cases b with
    | false =>
      rcases hx with ⟨z, rfl⟩
      rcases hy with ⟨w, hw⟩
      have hw' : (Sum.inr (Sum.inl (w, tubeEndLevel _root_.Bool.false)) : G.stepCarrier S e) =
          Sum.inl (G.flagBoundaryPoint (_root_.Insert.insert e S) e _root_.Bool.false z) := hw
      injection hw'
    | true =>
      rcases hx with ⟨z, rfl⟩
      rcases hy with ⟨w, hw⟩
      have hw' : (Sum.inr (Sum.inl (w, tubeEndLevel _root_.Bool.true)) : G.stepCarrier S e) =
          Sum.inr (Sum.inr (G.flagBoundaryPoint (_root_.Insert.insert e S) e _root_.Bool.true z)) := hw
      injection hw' with h1
      injection h1
  disjoint_blocks i j hij := by
    cases i <;> cases j
    · exact absurd rfl hij
    · rw [Set.disjoint_left]
      intro x hx hy
      rcases hx with ⟨z, rfl⟩ | ⟨z, rfl⟩
      · rcases hy with ⟨w, hw⟩ | ⟨w, hw⟩
        · have hw' : (Sum.inr (Sum.inr (G.flagBoundaryPoint (_root_.Insert.insert e S) e _root_.Bool.true w)) :
              G.stepCarrier S e) = Sum.inl (G.flagBoundaryPoint (_root_.Insert.insert e S) e _root_.Bool.false z) := hw
          injection hw'
        · have hw' : (Sum.inr (Sum.inl (w, tubeEndLevel _root_.Bool.true)) : G.stepCarrier S e) =
              Sum.inl (G.flagBoundaryPoint (_root_.Insert.insert e S) e _root_.Bool.false z) := hw
          injection hw'
      · rcases hy with ⟨w, hw⟩ | ⟨w, hw⟩
        · have hw' : (Sum.inr (Sum.inr (G.flagBoundaryPoint (_root_.Insert.insert e S) e _root_.Bool.true w)) :
              G.stepCarrier S e) = Sum.inr (Sum.inl (z, tubeEndLevel _root_.Bool.false)) := hw
          injection hw' with h1
          injection h1
        · have hw' : (Sum.inr (Sum.inl (w, tubeEndLevel _root_.Bool.true)) : G.stepCarrier S e) =
              Sum.inr (Sum.inl (z, tubeEndLevel _root_.Bool.false)) := hw
          injection hw' with h1
          injection h1 with h2
          injection h2 with _ h3
          exact tubeEndLevel_ne (by simp) h3
    · rw [Set.disjoint_left]
      intro x hx hy
      rcases hx with ⟨z, rfl⟩ | ⟨z, rfl⟩
      · rcases hy with ⟨w, hw⟩ | ⟨w, hw⟩
        · have hw' : (Sum.inl (G.flagBoundaryPoint (_root_.Insert.insert e S) e _root_.Bool.false w) :
              G.stepCarrier S e) =
              Sum.inr (Sum.inr (G.flagBoundaryPoint (_root_.Insert.insert e S) e _root_.Bool.true z)) := hw
          injection hw'
        · have hw' : (Sum.inr (Sum.inl (w, tubeEndLevel _root_.Bool.false)) : G.stepCarrier S e) =
              Sum.inr (Sum.inr (G.flagBoundaryPoint (_root_.Insert.insert e S) e _root_.Bool.true z)) := hw
          injection hw' with h1
          injection h1
      · rcases hy with ⟨w, hw⟩ | ⟨w, hw⟩
        · have hw' : (Sum.inl (G.flagBoundaryPoint (_root_.Insert.insert e S) e _root_.Bool.false w) :
              G.stepCarrier S e) = Sum.inr (Sum.inl (z, tubeEndLevel _root_.Bool.true)) := hw
          injection hw'
        · have hw' : (Sum.inr (Sum.inl (w, tubeEndLevel _root_.Bool.false)) : G.stepCarrier S e) =
              Sum.inr (Sum.inl (z, tubeEndLevel _root_.Bool.true)) := hw
          injection hw' with h1
          injection h1 with h2
          injection h2 with _ h3
          exact tubeEndLevel_ne (by simp) h3
    · exact absurd rfl hij

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.stepBoundaryGluing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.stepBoundaryGluing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.stepBoundaryGluing ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.stepBoundaryGluing

theorem stepAttaching_coe (S : Finset G.Edge) (e : G.Edge) (b : Bool) (z : S²)
    (hx : G.stepLeftLeg S e b z ∈ _root_.Set.range (G.stepLeftLeg S e b)) :
    ((stepAttaching G S e b) ⟨G.stepLeftLeg S e b z, hx⟩ : G.stepCarrier S e) =
      G.stepTubeEndLeg S e b z := by
  have hstep : ((isEmbedding_stepLeftLeg G S e b).toHomeomorph).symm
      ⟨G.stepLeftLeg S e b z, hx⟩ = z := by
    refine ((isEmbedding_stepLeftLeg G S e b).toHomeomorph).injective ?_
    rw [Homeomorph.apply_symm_apply]
    exact Subtype.ext
      (Topology.IsEmbedding.toHomeomorph_apply_coe (isEmbedding_stepLeftLeg G S e b) z)
  rw [stepAttaching, Homeomorph.trans_apply, hstep]
  exact Topology.IsEmbedding.toHomeomorph_apply_coe (isEmbedding_stepTubeEndLeg G S e b) z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.stepAttaching_coe then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.stepAttaching_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.stepAttaching_coe ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.stepAttaching_coe

theorem stepBoundaryGluing_attaching_coe (S : Finset G.Edge) (e : G.Edge) (b : Bool) (z : S²)
    (hx : G.stepLeftLeg S e b z ∈ (G.stepBoundaryGluing S e).left b) :
    ((G.stepBoundaryGluing S e).attaching b ⟨G.stepLeftLeg S e b z, hx⟩ :
        G.stepCarrier S e) = G.stepTubeEndLeg S e b z :=
  stepAttaching_coe G S e b z hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.stepBoundaryGluing_attaching_coe then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.stepBoundaryGluing_attaching_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.stepBoundaryGluing_attaching_coe ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.stepBoundaryGluing_attaching_coe

theorem stepBoundaryGluing_attaching_symm_coe (S : Finset G.Edge) (e : G.Edge) (b : Bool)
    (z : S²) (hy : G.stepTubeEndLeg S e b z ∈ (G.stepBoundaryGluing S e).right b) :
    (((G.stepBoundaryGluing S e).attaching b).symm ⟨G.stepTubeEndLeg S e b z, hy⟩ :
        G.stepCarrier S e) = G.stepLeftLeg S e b z := by
  have hs : ((G.stepBoundaryGluing S e).attaching b).symm
      ⟨G.stepTubeEndLeg S e b z, hy⟩ =
      ⟨G.stepLeftLeg S e b z, _root_.Set.mem_range_self z⟩ := by
    apply ((G.stepBoundaryGluing S e).attaching b).injective
    rw [Homeomorph.apply_symm_apply]
    exact Subtype.ext (stepBoundaryGluing_attaching_coe G S e b z (_root_.Set.mem_range_self _)).symm
  exact congrArg Subtype.val hs

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.stepBoundaryGluing_attaching_symm_coe then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.stepBoundaryGluing_attaching_symm_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.stepBoundaryGluing_attaching_symm_coe ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.stepBoundaryGluing_attaching_symm_coe

theorem stepBoundaryGluing_flip_left (S : Finset G.Edge) (e : G.Edge) (b : Bool) (z : S²) :
    (G.stepBoundaryGluing S e).flip b (G.stepLeftLeg S e b z) = G.stepTubeEndLeg S e b z := by
  rw [BoundaryGluing.flip_of_mem_left (G := G.stepBoundaryGluing S e) (_root_.Set.mem_range_self _)]
  exact stepBoundaryGluing_attaching_coe G S e b z (_root_.Set.mem_range_self _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.stepBoundaryGluing_flip_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.stepBoundaryGluing_flip_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.stepBoundaryGluing_flip_left ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.stepBoundaryGluing_flip_left

theorem stepBoundaryGluing_flip_right (S : Finset G.Edge) (e : G.Edge) (b : Bool) (z : S²) :
    (G.stepBoundaryGluing S e).flip b (G.stepTubeEndLeg S e b z) = G.stepLeftLeg S e b z := by
  rw [BoundaryGluing.flip_of_mem_right (G := G.stepBoundaryGluing S e) (_root_.Set.mem_range_self _)]
  exact stepBoundaryGluing_attaching_symm_coe G S e b z (_root_.Set.mem_range_self _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.stepBoundaryGluing_flip_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.stepBoundaryGluing_flip_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.stepBoundaryGluing_flip_right ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.stepBoundaryGluing_flip_right

theorem stepBoundaryGluing_rel_of_stepRel (S : Finset G.Edge) (e : G.Edge)
    {x y : G.stepCarrier S e} (h : G.stepRel S e x y) :
    (G.stepBoundaryGluing S e).rel x y := by
  have hsymm : ∀ {a b : G.stepCarrier S e}, (G.stepBoundaryGluing S e).rel a b →
      (G.stepBoundaryGluing S e).rel b a := fun hab =>
    (G.stepBoundaryGluing S e).isEquivalence_rel.symm hab
  rcases h with ⟨z, rfl, rfl⟩ | ⟨z, rfl, rfl⟩ | ⟨z, rfl, rfl⟩ | ⟨z, rfl, rfl⟩
  · have hrel := BoundaryGluing.rel_of_attaching (G.stepBoundaryGluing S e) _root_.Bool.false
      ⟨G.stepLeftLeg S e _root_.Bool.false z, _root_.Set.mem_range_self _⟩
    rw [stepBoundaryGluing_attaching_coe G S e _root_.Bool.false z (_root_.Set.mem_range_self _)] at hrel
    exact hsymm hrel
  · have hrel := BoundaryGluing.rel_of_attaching (G.stepBoundaryGluing S e) _root_.Bool.false
      ⟨G.stepLeftLeg S e _root_.Bool.false z, _root_.Set.mem_range_self _⟩
    rw [stepBoundaryGluing_attaching_coe G S e _root_.Bool.false z (_root_.Set.mem_range_self _)] at hrel
    exact hrel
  · have hrel := BoundaryGluing.rel_of_attaching (G.stepBoundaryGluing S e) _root_.Bool.true
      ⟨G.stepLeftLeg S e _root_.Bool.true z, _root_.Set.mem_range_self _⟩
    rw [stepBoundaryGluing_attaching_coe G S e _root_.Bool.true z (_root_.Set.mem_range_self _)] at hrel
    exact hrel
  · have hrel := BoundaryGluing.rel_of_attaching (G.stepBoundaryGluing S e) _root_.Bool.true
      ⟨G.stepLeftLeg S e _root_.Bool.true z, _root_.Set.mem_range_self _⟩
    rw [stepBoundaryGluing_attaching_coe G S e _root_.Bool.true z (_root_.Set.mem_range_self _)] at hrel
    exact hsymm hrel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.stepBoundaryGluing_rel_of_stepRel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.stepBoundaryGluing_rel_of_stepRel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.stepBoundaryGluing_rel_of_stepRel ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.stepBoundaryGluing_rel_of_stepRel

theorem stepBoundaryGluing_rel_of_eqvGen (S : Finset G.Edge) (e : G.Edge)
    {x y : G.stepCarrier S e} (h : Relation.EqvGen (G.stepRel S e) x y) :
    (G.stepBoundaryGluing S e).rel x y := by
  induction h with
  | rel a b hab => exact stepBoundaryGluing_rel_of_stepRel G S e hab
  | refl => exact Or.inl rfl
  | symm a b hab ih => exact (G.stepBoundaryGluing S e).isEquivalence_rel.symm ih
  | trans a b c hab hbc ih1 ih2 =>
    exact (G.stepBoundaryGluing S e).isEquivalence_rel.trans ih1 ih2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.stepBoundaryGluing_rel_of_eqvGen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.stepBoundaryGluing_rel_of_eqvGen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.stepBoundaryGluing_rel_of_eqvGen ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.stepBoundaryGluing_rel_of_eqvGen

theorem eqvGen_stepRel_of_stepBoundaryGluing_rel (S : Finset G.Edge) (e : G.Edge)
    {x y : G.stepCarrier S e} (h : (G.stepBoundaryGluing S e).rel x y) :
    Relation.EqvGen (G.stepRel S e) x y := by
  rcases h with rfl | ⟨i, hx, hy⟩
  · exact Relation.EqvGen.refl x
  · subst hy
    cases i with
    | false =>
      rcases (_root_.Set.mem_union x _ _).mp hx with hxl | hxr
      · obtain ⟨z, rfl⟩ := hxl
        rw [stepBoundaryGluing_flip_left]
        exact Relation.EqvGen.rel _ _ (Or.inl ⟨z, rfl, rfl⟩)
      · obtain ⟨z, rfl⟩ := hxr
        rw [stepBoundaryGluing_flip_right]
        exact Relation.EqvGen.rel _ _ (Or.inr (Or.inl ⟨z, rfl, rfl⟩))
    | true =>
      rcases (_root_.Set.mem_union x _ _).mp hx with hxl | hxr
      · obtain ⟨z, rfl⟩ := hxl
        rw [stepBoundaryGluing_flip_left]
        exact Relation.EqvGen.rel _ _ (Or.inr (Or.inr (Or.inr ⟨z, rfl, rfl⟩)))
      · obtain ⟨z, rfl⟩ := hxr
        rw [stepBoundaryGluing_flip_right]
        exact Relation.EqvGen.rel _ _ (Or.inr (Or.inr (Or.inl ⟨z, rfl, rfl⟩)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.eqvGen_stepRel_of_stepBoundaryGluing_rel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.eqvGen_stepRel_of_stepBoundaryGluing_rel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.eqvGen_stepRel_of_stepBoundaryGluing_rel ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.eqvGen_stepRel_of_stepBoundaryGluing_rel

theorem stepBoundaryGluing_rel_iff_eqvGen (S : Finset G.Edge) (e : G.Edge)
    (x y : G.stepCarrier S e) :
    (G.stepBoundaryGluing S e).rel x y ↔ Relation.EqvGen (G.stepRel S e) x y :=
  ⟨eqvGen_stepRel_of_stepBoundaryGluing_rel G S e,
    stepBoundaryGluing_rel_of_eqvGen G S e⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.stepBoundaryGluing_rel_iff_eqvGen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.stepBoundaryGluing_rel_iff_eqvGen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.stepBoundaryGluing_rel_iff_eqvGen ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.stepBoundaryGluing_rel_iff_eqvGen

theorem eq_of_eqvGen_stepRel_of_notMem_block (S : Finset G.Edge) (e : G.Edge)
    {x y : G.stepCarrier S e} (hx : ∀ i : Bool, x ∉ (G.stepBoundaryGluing S e).block i)
    (h : Relation.EqvGen (G.stepRel S e) x y) : x = y :=
  BoundaryGluing.eq_of_rel_of_notMem (G.stepBoundaryGluing S e) hx
    ((stepBoundaryGluing_rel_iff_eqvGen G S e x y).mpr h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.eq_of_eqvGen_stepRel_of_notMem_block then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.eq_of_eqvGen_stepRel_of_notMem_block"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.eq_of_eqvGen_stepRel_of_notMem_block ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.eq_of_eqvGen_stepRel_of_notMem_block

def stepQuotientHomeomorphBoundaryGluing (S : Finset G.Edge) (e : G.Edge) :
    G.stepQuotient S e ≃ₜ Quotient (G.stepBoundaryGluing S e).setoid where
  toFun := Quot.lift (fun x => Quotient.mk'' x)
    (fun _ _ hab => Quotient.sound (stepBoundaryGluing_rel_of_stepRel G S e hab))
  invFun := Quotient.lift (fun x => Quot.mk (G.stepRel S e) x)
    (fun _ _ hab => Quot.eq.mpr ((stepBoundaryGluing_rel_iff_eqvGen G S e _ _).mp hab))
  left_inv := by
    intro q
    induction q using Quot.inductionOn with
    | _ x => rfl
  right_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | _ x => rfl
  continuous_toFun := continuous_quot_lift _ continuous_quotient_mk'
  continuous_invFun := Continuous.quotient_lift continuous_quot_mk _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.stepQuotientHomeomorphBoundaryGluing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.stepQuotientHomeomorphBoundaryGluing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.stepQuotientHomeomorphBoundaryGluing ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.stepQuotientHomeomorphBoundaryGluing

theorem stepBoundaryGluing_setoid_eq_sup (S : Finset G.Edge) (e : G.Edge) :
    (G.stepBoundaryGluing S e).setoid =
      ((G.stepBoundaryGluing S e).restrict ({_root_.Bool.false} : Set Bool)).setoid ⊔
        ((G.stepBoundaryGluing S e).restrict ({_root_.Bool.true} : Set Bool)).setoid := by
  have huniv : (({_root_.Bool.false} : Set Bool) ∪ {_root_.Bool.true}) = univ := by
    ext b
    cases b <;> simp
  have hsup := BoundaryGluing.setoid_restrict_union (G.stepBoundaryGluing S e)
    ({_root_.Bool.false} : Set Bool) {_root_.Bool.true}
  rw [huniv, BoundaryGluing.setoid_restrict_univ] at hsup
  exact hsup

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.stepBoundaryGluing_setoid_eq_sup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.stepBoundaryGluing_setoid_eq_sup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.stepBoundaryGluing_setoid_eq_sup ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.stepBoundaryGluing_setoid_eq_sup

theorem t2Space_stepQuotient (S : Finset G.Edge) (e : G.Edge)
    [CompactSpace (G.stepCarrier S e)] : T2Space (G.stepQuotient S e) :=
  Homeomorph.t2Space (G.stepQuotientHomeomorphBoundaryGluing S e).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.t2Space_stepQuotient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.t2Space_stepQuotient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.t2Space_stepQuotient ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.t2Space_stepQuotient

abbrev assemblyCarrier (S : Finset G.Edge) : Type u :=
  (Σ v : G.Vertex, G.puncturedCarrier S v) ⊕
    (Σ f : {f : G.Edge // f ∈ S}, G.cylinderCarrier f.1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.assemblyCarrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.assemblyCarrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.assemblyCarrier ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.assemblyCarrier

def stepAssemblyRel (S : Finset G.Edge) (e : G.Edge) :
    G.assemblyCarrier (_root_.Insert.insert e S) → G.assemblyCarrier (_root_.Insert.insert e S) → Prop :=
  fun x y =>
    (∃ z : S², x = Sum.inl ⟨G.endpoint e _root_.Bool.false,
        G.flagBoundaryPoint (_root_.Insert.insert e S) e _root_.Bool.false z⟩ ∧
      y = Sum.inr ⟨⟨e, Finset.mem_insert_self e S⟩, (z, tubeEndLevel _root_.Bool.false)⟩) ∨
    (∃ z : S², y = Sum.inl ⟨G.endpoint e _root_.Bool.false,
        G.flagBoundaryPoint (_root_.Insert.insert e S) e _root_.Bool.false z⟩ ∧
      x = Sum.inr ⟨⟨e, Finset.mem_insert_self e S⟩, (z, tubeEndLevel _root_.Bool.false)⟩) ∨
    (∃ z : S², x = Sum.inr ⟨⟨e, Finset.mem_insert_self e S⟩, (z, tubeEndLevel _root_.Bool.true)⟩ ∧
      y = Sum.inl ⟨G.endpoint e _root_.Bool.true,
        G.flagBoundaryPoint (_root_.Insert.insert e S) e _root_.Bool.true z⟩) ∨
    (∃ z : S², y = Sum.inr ⟨⟨e, Finset.mem_insert_self e S⟩, (z, tubeEndLevel _root_.Bool.true)⟩ ∧
      x = Sum.inl ⟨G.endpoint e _root_.Bool.true,
        G.flagBoundaryPoint (_root_.Insert.insert e S) e _root_.Bool.true z⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.stepAssemblyRel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.stepAssemblyRel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.stepAssemblyRel ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.stepAssemblyRel

theorem stepAssemblyRel_quot_mk_pointSet (S : Finset G.Edge) (e : G.Edge) :
    Continuous (Quot.mk (G.stepAssemblyRel S e)) ∧
      Function.Surjective (Quot.mk (G.stepAssemblyRel S e)) ∧
      (∀ z : S², Quot.mk (G.stepAssemblyRel S e)
          (Sum.inl ⟨G.endpoint e _root_.Bool.false,
            G.flagBoundaryPoint (_root_.Insert.insert e S) e _root_.Bool.false z⟩) =
        Quot.mk (G.stepAssemblyRel S e)
          (Sum.inr ⟨⟨e, Finset.mem_insert_self e S⟩, (z, tubeEndLevel _root_.Bool.false)⟩)) ∧
      (∀ z : S², Quot.mk (G.stepAssemblyRel S e)
          (Sum.inr ⟨⟨e, Finset.mem_insert_self e S⟩, (z, tubeEndLevel _root_.Bool.true)⟩) =
        Quot.mk (G.stepAssemblyRel S e)
          (Sum.inl ⟨G.endpoint e _root_.Bool.true,
            G.flagBoundaryPoint (_root_.Insert.insert e S) e _root_.Bool.true z⟩)) ∧
      (∀ p q : G.assemblyCarrier (_root_.Insert.insert e S),
        Quot.mk (G.stepAssemblyRel S e) p = Quot.mk (G.stepAssemblyRel S e) q →
          Relation.EqvGen (G.stepAssemblyRel S e) p q) :=
  ⟨continuous_quot_mk, Quot.exists_rep, fun z => Quot.sound (Or.inl ⟨z, rfl, rfl⟩),
    fun z => Quot.sound (Or.inr (Or.inr (Or.inl ⟨z, rfl, rfl⟩))),
    fun _ _ h => Quot.eq.mp h⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MarkedManifoldGraph.stepAssemblyRel_quot_mk_pointSet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MarkedManifoldGraph.stepAssemblyRel_quot_mk_pointSet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MarkedManifoldGraph.stepAssemblyRel_quot_mk_pointSet ``Submission.DifferentialGeometry.Topology.MarkedManifoldGraph.stepAssemblyRel_quot_mk_pointSet

end MarkedManifoldGraph

namespace PartialRealization

variable {G : MarkedManifoldGraph.{u}} {S : Finset G.Edge} {e : G.Edge}

structure FlagMarking (P : PartialRealization G S) where
  marked : (e : G.Edge) → (b : Bool) → e ∉ S → MarkedBall P.realization
  transport : ∀ (e : G.Edge) (b : Bool) (he : e ∉ S) (x : ClosedCell 3),
    (marked e b he).ball x = P.vertexPiece (G.endpoint e b) (G.flagBallPoint S e b he x)
  reserve : ∀ (e : G.Edge) (b : Bool) (he : e ∉ S),
    (marked e b he).collarBudget ≤ (G.flag e b).collarBudget
  collar_disjoint : ∀ (e e' : G.Edge) (b b' : Bool) (he : e ∉ S) (he' : e' ∉ S),
    (e, b) ≠ (e', b') → Disjoint (marked e b he).collar (marked e' b' he').collar

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PartialRealization.FlagMarking then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PartialRealization.FlagMarking"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PartialRealization.FlagMarking ``Submission.DifferentialGeometry.Topology.PartialRealization.FlagMarking

namespace FlagMarking

variable {P : PartialRealization G S} (M : P.FlagMarking)

def toSurvivingFlag (e : G.Edge) (he : e ∉ S) : MarkedBall P.realization :=
  M.marked e _root_.Bool.false he

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PartialRealization.FlagMarking.toSurvivingFlag then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PartialRealization.FlagMarking.toSurvivingFlag"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PartialRealization.FlagMarking.toSurvivingFlag ``Submission.DifferentialGeometry.Topology.PartialRealization.FlagMarking.toSurvivingFlag

theorem disjoint_toSurvivingFlag (e e' : G.Edge) (he : e ∉ S) (he' : e' ∉ S) (hne : e ≠ e') :
    Disjoint (M.toSurvivingFlag e he).collar (M.toSurvivingFlag e' he').collar :=
  M.collar_disjoint e e' _root_.Bool.false _root_.Bool.false he he' fun h => hne (Prod.mk.inj h).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PartialRealization.FlagMarking.disjoint_toSurvivingFlag then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PartialRealization.FlagMarking.disjoint_toSurvivingFlag"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PartialRealization.FlagMarking.disjoint_toSurvivingFlag ``Submission.DifferentialGeometry.Topology.PartialRealization.FlagMarking.disjoint_toSurvivingFlag

theorem toSurvivingFlag_transport (e : G.Edge) (he : e ∉ S) (x : ClosedCell 3) :
    (M.toSurvivingFlag e he).ball x = P.vertexPiece (G.endpoint e _root_.Bool.false)
      (G.flagBallPoint S e _root_.Bool.false he x) :=
  M.transport e _root_.Bool.false he x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PartialRealization.FlagMarking.toSurvivingFlag_transport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PartialRealization.FlagMarking.toSurvivingFlag_transport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PartialRealization.FlagMarking.toSurvivingFlag_transport ``Submission.DifferentialGeometry.Topology.PartialRealization.FlagMarking.toSurvivingFlag_transport

end FlagMarking

def flagMarkingOneVertexLoopEmpty (N : ConnectedClosedOrientedManifold.{0} 3)
    (B B' : MarkedBall N.toClosedOrientedManifold) (hdisj : Disjoint B.collar B'.collar) :
    (oneVertexLoopEmpty N B B' hdisj).FlagMarking where
  marked := fun _ b _ => if b then B' else B
  transport := fun _ _ _ _ => rfl
  reserve := fun _ _ _ => le_refl _
  collar_disjoint := fun _ _ b b' _ _ hne => by
    have hbb : b ≠ b' := fun h => hne (Prod.ext rfl h)
    exact MarkedManifoldGraph.disjoint_collar_if_flags_ne hdisj hbb

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PartialRealization.flagMarkingOneVertexLoopEmpty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PartialRealization.flagMarkingOneVertexLoopEmpty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PartialRealization.flagMarkingOneVertexLoopEmpty ``Submission.DifferentialGeometry.Topology.PartialRealization.flagMarkingOneVertexLoopEmpty

theorem not_flagMarkerTransport_constBall_oneVertexLoopEmpty
    (N : ConnectedClosedOrientedManifold.{0} 3)
    (B B' : MarkedBall N.toClosedOrientedManifold) (hdisj : Disjoint B.collar B'.collar) :
    ¬ (oneVertexLoopEmpty N B B' hdisj).FlagMarkerTransport (fun _ => B)
      PUnit.unit (Finset.notMem_empty PUnit.unit) := by
  intro htrans
  have htrue : B.ball = B'.ball := by
    funext x
    have h : B.ball x = (if _root_.Bool.true then B' else B).ball x := htrans _root_.Bool.true x
    simpa using h
  exact MarkedBall.ball_ne_of_disjoint_collar hdisj htrue

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PartialRealization.not_flagMarkerTransport_constBall_oneVertexLoopEmpty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PartialRealization.not_flagMarkerTransport_constBall_oneVertexLoopEmpty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PartialRealization.not_flagMarkerTransport_constBall_oneVertexLoopEmpty ``Submission.DifferentialGeometry.Topology.PartialRealization.not_flagMarkerTransport_constBall_oneVertexLoopEmpty

theorem seamEquation_iff_boundaryGluing_rel (P : PartialRealization G (_root_.Insert.insert e S)) :
    P.SeamEquation e (Finset.mem_insert_self e S) ↔
      ∀ x y : G.stepCarrier S e,
        (G.stepBoundaryGluing S e).rel x y → P.stepMap x = P.stepMap y := by
  constructor
  · intro h x y hxy
    exact P.eqvGen_stepMap_eq ((P.seamEquation_iff_stepRel_related).mp h)
      (MarkedManifoldGraph.eqvGen_stepRel_of_stepBoundaryGluing_rel G S e hxy)
  · intro h
    exact (P.seamEquation_iff_stepRel_related).mpr fun x y hxy =>
      h x y (MarkedManifoldGraph.stepBoundaryGluing_rel_of_stepRel G S e hxy)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PartialRealization.seamEquation_iff_boundaryGluing_rel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PartialRealization.seamEquation_iff_boundaryGluing_rel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PartialRealization.seamEquation_iff_boundaryGluing_rel ``Submission.DifferentialGeometry.Topology.PartialRealization.seamEquation_iff_boundaryGluing_rel

structure StepAssemblyData (G : MarkedManifoldGraph.{u}) (S : Finset G.Edge) (e : G.Edge) where
  realization : ClosedOrientedManifold.{u} 3
  quotient : Quot (G.stepAssemblyRel S e) ≃ₜ realization.Carrier
  survivingFlag : (f : G.Edge) → (b : Bool) → f ∉ _root_.Insert.insert e S → MarkedBall realization
  survivingFlag_transport : ∀ (f : G.Edge) (b : Bool) (hf : f ∉ _root_.Insert.insert e S)
    (x : ClosedCell 3),
    (survivingFlag f b hf).ball x = quotient (Quot.mk (G.stepAssemblyRel S e)
      (Sum.inl ⟨G.endpoint f b, G.flagBallPoint (_root_.Insert.insert e S) f b hf x⟩))
  survivingFlag_reserve : ∀ (f : G.Edge) (b : Bool) (hf : f ∉ _root_.Insert.insert e S),
    (survivingFlag f b hf).collarBudget ≤ (G.flag f b).collarBudget
  survivingFlag_collar_disjoint : ∀ (f f' : G.Edge) (b b' : Bool) (hf : f ∉ _root_.Insert.insert e S)
    (hf' : f' ∉ _root_.Insert.insert e S), (f, b) ≠ (f', b') →
    Disjoint (survivingFlag f b hf).collar (survivingFlag f' b' hf').collar

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PartialRealization.StepAssemblyData then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PartialRealization.StepAssemblyData"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PartialRealization.StepAssemblyData ``Submission.DifferentialGeometry.Topology.PartialRealization.StepAssemblyData

namespace StepAssemblyData

variable {G : MarkedManifoldGraph.{u}} {S : Finset G.Edge} {e : G.Edge}
variable (D : StepAssemblyData G S e)

def partialRealization : PartialRealization G (_root_.Insert.insert e S) where
  realization := D.realization
  vertexPiece v :=
    ⟨fun y => D.quotient (Quot.mk (G.stepAssemblyRel S e) (Sum.inl ⟨v, y⟩)),
      D.quotient.continuous.comp ((continuous_quot_mk).comp
        (continuous_inl.comp continuous_sigmaMk))⟩
  cylinderPiece f hf :=
    ⟨fun q => D.quotient (Quot.mk (G.stepAssemblyRel S e) (Sum.inr ⟨⟨f, hf⟩, q⟩)),
      D.quotient.continuous.comp ((continuous_quot_mk).comp
        (continuous_inr.comp continuous_sigmaMk))⟩
  survivingFlag f hf := D.survivingFlag f _root_.Bool.false hf
  covers x := by
    obtain ⟨s, hs⟩ := Quot.exists_rep (D.quotient.symm x)
    have hx : D.quotient (Quot.mk (G.stepAssemblyRel S e) s) = x := by
      rw [hs, Homeomorph.apply_symm_apply]
    rcases s with p | q
    · refine Or.inl ⟨p.1, ⟨p.2, ?_⟩⟩
      change D.quotient (Quot.mk (G.stepAssemblyRel S e) (Sum.inl ⟨p.1, p.2⟩)) = x
      exact hx
    · refine Or.inr ⟨q.1.1, q.1.2, ⟨q.2, ?_⟩⟩
      change D.quotient (Quot.mk (G.stepAssemblyRel S e) (Sum.inr ⟨q.1, q.2⟩)) = x
      exact hx
  survivingFlag_collar_disjoint f f' hf hf' hne :=
    D.survivingFlag_collar_disjoint f f' _root_.Bool.false _root_.Bool.false hf hf'
      (fun h => hne (Prod.mk.inj h).1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PartialRealization.StepAssemblyData.partialRealization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PartialRealization.StepAssemblyData.partialRealization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PartialRealization.StepAssemblyData.partialRealization ``Submission.DifferentialGeometry.Topology.PartialRealization.StepAssemblyData.partialRealization

theorem partialRealization_seamEquation :
    (D.partialRealization).SeamEquation e (Finset.mem_insert_self e S) := by
  constructor
  · intro z
    have hq : Quot.mk (G.stepAssemblyRel S e)
          (Sum.inr ⟨⟨e, Finset.mem_insert_self e S⟩, (z, tubeEndLevel _root_.Bool.false)⟩) =
        Quot.mk (G.stepAssemblyRel S e)
          (Sum.inl ⟨G.endpoint e _root_.Bool.false, G.flagBoundaryPoint (_root_.Insert.insert e S) e _root_.Bool.false z⟩) :=
      Quot.sound (Or.inr (Or.inl ⟨z, rfl, rfl⟩))
    exact congrArg D.quotient hq
  · intro z
    have hq : Quot.mk (G.stepAssemblyRel S e)
          (Sum.inr ⟨⟨e, Finset.mem_insert_self e S⟩, (z, tubeEndLevel _root_.Bool.true)⟩) =
        Quot.mk (G.stepAssemblyRel S e)
          (Sum.inl ⟨G.endpoint e _root_.Bool.true, G.flagBoundaryPoint (_root_.Insert.insert e S) e _root_.Bool.true z⟩) :=
      Quot.sound (Or.inr (Or.inr (Or.inl ⟨z, rfl, rfl⟩)))
    exact congrArg D.quotient hq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PartialRealization.StepAssemblyData.partialRealization_seamEquation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PartialRealization.StepAssemblyData.partialRealization_seamEquation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PartialRealization.StepAssemblyData.partialRealization_seamEquation ``Submission.DifferentialGeometry.Topology.PartialRealization.StepAssemblyData.partialRealization_seamEquation

def partialRealizationFlagMarking : (D.partialRealization).FlagMarking where
  marked := D.survivingFlag
  transport := fun f b hf x => D.survivingFlag_transport f b hf x
  reserve := fun f b hf => D.survivingFlag_reserve f b hf
  collar_disjoint := fun f f' b b' hf hf' hne =>
    D.survivingFlag_collar_disjoint f f' b b' hf hf' hne

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PartialRealization.StepAssemblyData.partialRealizationFlagMarking then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PartialRealization.StepAssemblyData.partialRealizationFlagMarking"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PartialRealization.StepAssemblyData.partialRealizationFlagMarking ``Submission.DifferentialGeometry.Topology.PartialRealization.StepAssemblyData.partialRealizationFlagMarking

theorem exists_partialRealization_and_flagMarking (D : StepAssemblyData G S e) :
    ∃ P' : PartialRealization G (_root_.Insert.insert e S),
      P'.SeamEquation e (Finset.mem_insert_self e S) ∧ Nonempty P'.FlagMarking :=
  ⟨D.partialRealization, D.partialRealization_seamEquation,
    ⟨D.partialRealizationFlagMarking⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PartialRealization.StepAssemblyData.exists_partialRealization_and_flagMarking then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PartialRealization.StepAssemblyData.exists_partialRealization_and_flagMarking"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PartialRealization.StepAssemblyData.exists_partialRealization_and_flagMarking ``Submission.DifferentialGeometry.Topology.PartialRealization.StepAssemblyData.exists_partialRealization_and_flagMarking

end StepAssemblyData

end PartialRealization

end DifferentialGeometry.Topology
