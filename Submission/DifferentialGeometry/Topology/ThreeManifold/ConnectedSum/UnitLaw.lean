import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.Construction
import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.Finite
import Submission.DifferentialGeometry.Topology.ThreeManifold.StandardSphere

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology
open _root_.Set _root_.Function

namespace DifferentialGeometry.Topology

universe u

abbrev csE3 : Type := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.csE3 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.csE3"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.csE3 ``Submission.DifferentialGeometry.Topology.csE3

abbrev csS2 : Type := Metric.sphere (0 : csE3) 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.csS2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.csS2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.csS2 ``Submission.DifferentialGeometry.Topology.csS2

theorem finiteConnectedSum_singleton_unit (M : ConnectedClosedOrientedManifold.{u} 3) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (finiteConnectedSum [M]).toClosedOrientedManifold M.toClosedOrientedManifold) :=
  ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl M.toClosedOrientedManifold⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.finiteConnectedSum_singleton_unit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.finiteConnectedSum_singleton_unit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.finiteConnectedSum_singleton_unit ``Submission.DifferentialGeometry.Topology.finiteConnectedSum_singleton_unit

theorem finiteConnectedSum_nil_unit :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (finiteConnectedSum ([] : List (ConnectedClosedOrientedManifold.{u} 3))).toClosedOrientedManifold
      standardThreeSphereLift.{u}.toClosedOrientedManifold) :=
  ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl standardThreeSphereLift.{u}.toClosedOrientedManifold⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.finiteConnectedSum_nil_unit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.finiteConnectedSum_nil_unit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.finiteConnectedSum_nil_unit ``Submission.DifferentialGeometry.Topology.finiteConnectedSum_nil_unit

theorem finiteConnectedSum_append_nil
    (L : List (ConnectedClosedOrientedManifold.{u} 3)) :
    finiteConnectedSum (L ++ []) = finiteConnectedSum L := by
  induction L using List.reverseRecOn with
  | nil => rfl
  | append_singleton L M _ => rw [List.append_assoc, List.append_nil]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.finiteConnectedSum_append_nil then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.finiteConnectedSum_append_nil"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.finiteConnectedSum_append_nil ``Submission.DifferentialGeometry.Topology.finiteConnectedSum_append_nil

namespace ConnectedSumUnit

variable {M : ConnectedClosedOrientedManifold.{u} 3}

abbrev BallImage (c : OrientedBallChart M.toClosedOrientedManifold) : Set M.Carrier :=
  c.toBallChart.chart '' Metric.closedBall (0 : csE3) 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumUnit.BallImage then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumUnit.BallImage"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumUnit.BallImage ``Submission.DifferentialGeometry.Topology.ConnectedSumUnit.BallImage

structure UnitFilling (c : OrientedBallChart M.toClosedOrientedManifold)
    (d : OrientedBallChart standardThreeSphereLift.{u}.toClosedOrientedManifold)
    (a : BoundaryAttachment) where
  fill : d.toBallChart.Punctured ≃ₜ {x : M.Carrier // x ∈ BallImage c}
  map_boundary : ∀ z : csS2,
    fill (d.toBallChart.boundaryMap (a.1 z)) =
      ⟨c.toBallChart.chart z, ⟨z, Metric.mem_closedBall.mpr (by
        rw [dist_zero_right]
        exact le_of_eq (by simpa only [Metric.mem_sphere, dist_zero_right] using z.2)),
        rfl⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumUnit.UnitFilling then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumUnit.UnitFilling"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumUnit.UnitFilling ``Submission.DifferentialGeometry.Topology.ConnectedSumUnit.UnitFilling

variable {c : OrientedBallChart M.toClosedOrientedManifold}
  {d : OrientedBallChart standardThreeSphereLift.{u}.toClosedOrientedManifold}
  {a : BoundaryAttachment}

def quotientMap (F : UnitFilling c d a) :
    ConnectedSumQuotient c.toBallChart d.toBallChart a.1.toHomeomorph → M.Carrier :=
  Quot.lift (Sum.elim (fun p : c.toBallChart.Punctured => (p : M.Carrier))
      (fun q : d.toBallChart.Punctured => (F.fill q : M.Carrier)))
    (by
      rintro u v ⟨z, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · exact (congrArg Subtype.val (F.map_boundary z)).symm
      · exact congrArg Subtype.val (F.map_boundary z))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumUnit.quotientMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumUnit.quotientMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumUnit.quotientMap ``Submission.DifferentialGeometry.Topology.ConnectedSumUnit.quotientMap

theorem continuous_quotientMap (F : UnitFilling c d a) : Continuous (quotientMap F) :=
  continuous_adjunction_lift c.toBallChart.boundaryMap
    (d.toBallChart.boundaryMap ∘ a.1.toHomeomorph)
    (by
      rintro u v ⟨z, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · exact (congrArg Subtype.val (F.map_boundary z)).symm
      · exact congrArg Subtype.val (F.map_boundary z))
    (Continuous.sumElim continuous_subtype_val (continuous_subtype_val.comp F.fill.continuous))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumUnit.continuous_quotientMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumUnit.continuous_quotientMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumUnit.continuous_quotientMap ``Submission.DifferentialGeometry.Topology.ConnectedSumUnit.continuous_quotientMap

theorem quotientMap_injective (F : UnitFilling c d a) : Function.Injective (quotientMap F) := by
  intro x y hxy
  rcases ConnectedSumQuotient.jointly_surjective c.toBallChart d.toBallChart a.1.toHomeomorph x with
    ⟨p, rfl⟩ | ⟨q, rfl⟩
  · rcases ConnectedSumQuotient.jointly_surjective c.toBallChart d.toBallChart a.1.toHomeomorph y with
      ⟨p', rfl⟩ | ⟨q', rfl⟩
    · exact congrArg (ConnectedSumQuotient.inl c.toBallChart d.toBallChart a.1.toHomeomorph)
        (Subtype.ext hxy)
    · have hval : (p : M.Carrier) = (F.fill q' : M.Carrier) := hxy
      have hmem : (p : M.Carrier) ∈ BallImage c := by
        rw [hval]
        exact (F.fill q').2
      rw [BallImage] at hmem
      obtain ⟨w, hw, hwval⟩ := hmem
      have hpnot : (p : M.Carrier) ∉ c.toBallChart.chart '' Metric.ball (0 : csE3) 1 := p.2
      have hnorm : ‖w‖ = 1 := by
        have hle : _root_.Dist.dist w (0 : csE3) ≤ 1 := Metric.mem_closedBall.mp hw
        have hnle : ¬ _root_.Dist.dist w (0 : csE3) < 1 := by
          intro hlt
          exact hpnot ⟨w, hlt, hwval⟩
        rw [dist_zero_right] at hle hnle
        exact le_antisymm hle (le_of_not_gt hnle)
      have hdist : _root_.Dist.dist w (0 : csE3) = 1 := by
        rw [dist_zero_right]; exact hnorm
      have hz : (p : M.Carrier) = c.toBallChart.boundaryMap ⟨w, hdist⟩ := by
        rw [← hwval]
        rfl
      have hFq : F.fill q' = ⟨c.toBallChart.boundaryMap ⟨w, hdist⟩,
          ⟨w, Metric.mem_closedBall.mpr (le_of_eq hdist), rfl⟩⟩ := by
        refine Subtype.ext ?_
        rw [← hval, hz]
      have hq' : q' = d.toBallChart.boundaryMap (a.1 ⟨w, hdist⟩) := by
        refine F.fill.injective ?_
        exact hFq.trans (F.map_boundary ⟨w, hdist⟩).symm
      have hp : p = c.toBallChart.boundaryMap ⟨w, hdist⟩ := Subtype.ext hz
      rw [hq', hp]
      exact ConnectedSumQuotient.boundary_eq c.toBallChart d.toBallChart a.1.toHomeomorph
        ⟨w, hdist⟩
  · rcases ConnectedSumQuotient.jointly_surjective c.toBallChart d.toBallChart a.1.toHomeomorph y with
      ⟨p', rfl⟩ | ⟨q', rfl⟩
    · have hval : (F.fill q : M.Carrier) = (p' : M.Carrier) := hxy
      have hmem : (p' : M.Carrier) ∈ BallImage c := by
        rw [← hval]
        exact (F.fill q).2
      rw [BallImage] at hmem
      obtain ⟨w, hw, hwval⟩ := hmem
      have hpnot : (p' : M.Carrier) ∉ c.toBallChart.chart '' Metric.ball (0 : csE3) 1 := p'.2
      have hnorm : ‖w‖ = 1 := by
        have hle : _root_.Dist.dist w (0 : csE3) ≤ 1 := Metric.mem_closedBall.mp hw
        have hnle : ¬ _root_.Dist.dist w (0 : csE3) < 1 := by
          intro hlt
          exact hpnot ⟨w, hlt, hwval⟩
        rw [dist_zero_right] at hle hnle
        exact le_antisymm hle (le_of_not_gt hnle)
      have hdist : _root_.Dist.dist w (0 : csE3) = 1 := by
        rw [dist_zero_right]; exact hnorm
      have hz : (p' : M.Carrier) = c.toBallChart.boundaryMap ⟨w, hdist⟩ := by
        rw [← hwval]
        rfl
      have hFq : F.fill q = ⟨c.toBallChart.boundaryMap ⟨w, hdist⟩,
          ⟨w, Metric.mem_closedBall.mpr (le_of_eq hdist), rfl⟩⟩ := by
        refine Subtype.ext ?_
        rw [hval, hz]
      have hq : q = d.toBallChart.boundaryMap (a.1 ⟨w, hdist⟩) := by
        refine F.fill.injective ?_
        exact hFq.trans (F.map_boundary ⟨w, hdist⟩).symm
      have hp : p' = c.toBallChart.boundaryMap ⟨w, hdist⟩ := Subtype.ext hz
      rw [hq, hp]
      exact (ConnectedSumQuotient.boundary_eq c.toBallChart d.toBallChart a.1.toHomeomorph
        ⟨w, hdist⟩).symm
    · exact congrArg (ConnectedSumQuotient.inr c.toBallChart d.toBallChart a.1.toHomeomorph)
        (F.fill.injective (Subtype.ext hxy))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumUnit.quotientMap_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumUnit.quotientMap_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumUnit.quotientMap_injective ``Submission.DifferentialGeometry.Topology.ConnectedSumUnit.quotientMap_injective

theorem quotientMap_surjective (F : UnitFilling c d a) : Function.Surjective (quotientMap F) := by
  intro y
  by_cases hy : y ∈ c.toBallChart.chart '' Metric.ball (0 : csE3) 1
  · obtain ⟨w, hw, hwval⟩ := hy
    have hmem : y ∈ BallImage c := ⟨w, Metric.ball_subset_closedBall hw, hwval⟩
    refine ⟨ConnectedSumQuotient.inr c.toBallChart d.toBallChart a.1.toHomeomorph
      (F.fill.symm ⟨y, hmem⟩), ?_⟩
    change (F.fill (F.fill.symm ⟨y, hmem⟩) : M.Carrier) = y
    rw [F.fill.apply_symm_apply]
  · refine ⟨ConnectedSumQuotient.inl c.toBallChart d.toBallChart a.1.toHomeomorph
      ⟨y, hy⟩, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumUnit.quotientMap_surjective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumUnit.quotientMap_surjective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumUnit.quotientMap_surjective ``Submission.DifferentialGeometry.Topology.ConnectedSumUnit.quotientMap_surjective

theorem quotientMap_bijective (F : UnitFilling c d a) : Function.Bijective (quotientMap F) :=
  ⟨quotientMap_injective F, quotientMap_surjective F⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumUnit.quotientMap_bijective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumUnit.quotientMap_bijective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumUnit.quotientMap_bijective ``Submission.DifferentialGeometry.Topology.ConnectedSumUnit.quotientMap_bijective

def quotientEquiv (F : UnitFilling c d a) :
    ConnectedSumQuotient c.toBallChart d.toBallChart a.1.toHomeomorph ≃ M.Carrier :=
  Equiv.ofBijective (quotientMap F) (quotientMap_bijective F)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumUnit.quotientEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumUnit.quotientEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumUnit.quotientEquiv ``Submission.DifferentialGeometry.Topology.ConnectedSumUnit.quotientEquiv

theorem homeomorph_of_unitFilling (F : UnitFilling c d a) :
    Nonempty (ConnectedSumQuotient c.toBallChart d.toBallChart a.1.toHomeomorph ≃ₜ M.Carrier) :=
  ⟨Continuous.homeoOfEquivCompactToT2 (f := quotientEquiv F) (continuous_quotientMap F)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumUnit.homeomorph_of_unitFilling then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumUnit.homeomorph_of_unitFilling"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumUnit.homeomorph_of_unitFilling ``Submission.DifferentialGeometry.Topology.ConnectedSumUnit.homeomorph_of_unitFilling

def BallComplementCollar (F : UnitFilling c d a) : Prop :=
  ∀ p : ConnectedSumQuotient.K, (p.2 : ℝ) < 0 →
    (F.fill (ConnectedSumQuotient.radialRightClamp d.toBallChart (a.1 p.1) p) : M.Carrier) =
      c.toBallChart.chart ((1 + (p.2 : ℝ)) • p.1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumUnit.BallComplementCollar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumUnit.BallComplementCollar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumUnit.BallComplementCollar ``Submission.DifferentialGeometry.Topology.ConnectedSumUnit.BallComplementCollar

theorem quotientMap_collarMap (F : UnitFilling c d a) (hcollar : BallComplementCollar F)
    (p : ConnectedSumQuotient.K) :
    quotientMap F (ConnectedSumQuotient.collarMap c.toBallChart d.toBallChart a.1 p) =
      c.toBallChart.chart (ConnectedSumQuotient.rad p) := by
  by_cases ht : 0 ≤ (p.2 : ℝ)
  · rw [ConnectedSumQuotient.collarMap_of_nonneg c.toBallChart d.toBallChart a.1 p ht]
    rfl
  · rw [ConnectedSumQuotient.collarMap_eq_if]
    simp only [if_neg (not_le.mpr (lt_of_not_ge ht)), ConnectedSumQuotient.collarRight]
    exact hcollar p (lt_of_not_ge ht)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumUnit.quotientMap_collarMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumUnit.quotientMap_collarMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumUnit.quotientMap_collarMap ``Submission.DifferentialGeometry.Topology.ConnectedSumUnit.quotientMap_collarMap

def BallComplementSmooth (F : UnitFilling c d a) : Prop :=
  IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞
    (fun x : d.toBallChart.interior => (F.fill (d.toBallChart.interiorToPunctured x) : M.Carrier))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumUnit.BallComplementSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumUnit.BallComplementSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumUnit.BallComplementSmooth ``Submission.DifferentialGeometry.Topology.ConnectedSumUnit.BallComplementSmooth

def BallComplementOrientation (F : UnitFilling c d a) (h : BallComplementSmooth F) : Prop :=
  ∀ x : d.toBallChart.interior,
    Orientation.map (Fin 3)
      ((h x).mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv
      (standardThreeSphereLift.{u}.orientation.orientation x.1) =
    M.orientation.orientation (F.fill (d.toBallChart.interiorToPunctured x))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumUnit.BallComplementOrientation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumUnit.BallComplementOrientation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumUnit.BallComplementOrientation ``Submission.DifferentialGeometry.Topology.ConnectedSumUnit.BallComplementOrientation

end ConnectedSumUnit

end DifferentialGeometry.Topology
