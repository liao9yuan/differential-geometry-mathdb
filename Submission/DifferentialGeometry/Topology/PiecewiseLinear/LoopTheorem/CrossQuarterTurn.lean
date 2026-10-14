/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.CylinderSplice
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossRegluedSourceTubeRestriction
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossSeamResolvedCell

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

def crossQuarterTurn (p : (ℝ × ℝ) × ℝ) : (ℝ × ℝ) × ℝ := ((-p.1.2, p.1.1), p.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.crossQuarterTurn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.crossQuarterTurn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.crossQuarterTurn ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.crossQuarterTurn

theorem crossQuarterTurn_iterate_four (p : (ℝ × ℝ) × ℝ) :
    crossQuarterTurn (crossQuarterTurn (crossQuarterTurn (crossQuarterTurn p))) = p := by
  obtain ⟨⟨a, b⟩, t⟩ := p
  simp [crossQuarterTurn]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.crossQuarterTurn_iterate_four then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.crossQuarterTurn_iterate_four"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.crossQuarterTurn_iterate_four ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.crossQuarterTurn_iterate_four

theorem injective_crossQuarterTurn : Function.Injective crossQuarterTurn :=
  Function.LeftInverse.injective
    (g := fun p => crossQuarterTurn (crossQuarterTurn (crossQuarterTurn p)))
    crossQuarterTurn_iterate_four

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.injective_crossQuarterTurn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.injective_crossQuarterTurn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.injective_crossQuarterTurn ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.injective_crossQuarterTurn

theorem continuous_crossQuarterTurn : Continuous crossQuarterTurn := by
  unfold crossQuarterTurn
  exact (continuous_fst.snd.neg.prodMk continuous_fst.fst).prodMk continuous_snd

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.continuous_crossQuarterTurn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.continuous_crossQuarterTurn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.continuous_crossQuarterTurn ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.continuous_crossQuarterTurn

theorem image_crossQuarterTurn_of_mapsTo {S : Set ((ℝ × ℝ) × ℝ)}
    (h : _root_.Set.MapsTo crossQuarterTurn S S) : crossQuarterTurn '' S = S := by
  refine Subset.antisymm ?_ fun p hp => ⟨_, h (h (h hp)), crossQuarterTurn_iterate_four p⟩
  rintro _ ⟨p, hp, rfl⟩
  exact h hp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.image_crossQuarterTurn_of_mapsTo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.image_crossQuarterTurn_of_mapsTo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.image_crossQuarterTurn_of_mapsTo ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.image_crossQuarterTurn_of_mapsTo

theorem mapsTo_crossQuarterTurn_prod {S : Set (ℝ × ℝ)} {I : Set ℝ}
    (hS : _root_.Set.MapsTo (fun q : ℝ × ℝ => (-q.2, q.1)) S S) :
    MapsTo crossQuarterTurn (S ×ˢ I) (S ×ˢ I) :=
  fun _ hp => ⟨hS hp.1, hp.2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_crossQuarterTurn_prod then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_crossQuarterTurn_prod"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_crossQuarterTurn_prod ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_crossQuarterTurn_prod

theorem mapsTo_crossQuarterTurn_spliceSquare :
    MapsTo (fun q : ℝ × ℝ => (-q.2, q.1)) spliceSquare spliceSquare := by
  rintro ⟨a, b⟩ ⟨ha, hb⟩
  refine ⟨?_, ha⟩
  rw [Set.mem_Icc] at hb ⊢
  exact ⟨by linarith [hb.2], by linarith [hb.1]⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_crossQuarterTurn_spliceSquare then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_crossQuarterTurn_spliceSquare"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_crossQuarterTurn_spliceSquare ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_crossQuarterTurn_spliceSquare

theorem mapsTo_crossQuarterTurn_origin :
    _root_.Set.MapsTo (fun q : ℝ × ℝ => (-q.2, q.1)) ({((0 : ℝ), (0 : ℝ))} : Set (ℝ × ℝ))
      ({((0 : ℝ), (0 : ℝ))} : Set (ℝ × ℝ)) := by
  intro q hq
  rw [Set.mem_singleton_iff] at hq
  subst hq
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_crossQuarterTurn_origin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_crossQuarterTurn_origin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_crossQuarterTurn_origin ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_crossQuarterTurn_origin

theorem mapsTo_crossQuarterTurn_crossingArc :
    _root_.Set.MapsTo (fun q : ℝ × ℝ => (-q.2, q.1)) (crossingArcX ∪ crossingArcY)
      (crossingArcX ∪ crossingArcY) := by
  rintro q (⟨hq, hx⟩ | ⟨hq, hy⟩)
  · exact Or.inr ⟨mapsTo_crossQuarterTurn_spliceSquare hq, hx⟩
  · refine Or.inl ⟨mapsTo_crossQuarterTurn_spliceSquare hq, ?_⟩
    change -q.2 = 0
    simp [hy]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_crossQuarterTurn_crossingArc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_crossQuarterTurn_crossingArc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_crossQuarterTurn_crossingArc ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_crossQuarterTurn_crossingArc

theorem mapsTo_crossQuarterTurn_spliceSquareBoundary :
    MapsTo (fun q : ℝ × ℝ => (-q.2, q.1)) spliceSquareBoundary spliceSquareBoundary := by
  rintro q ⟨hq, hb⟩
  refine ⟨mapsTo_crossQuarterTurn_spliceSquare hq, ?_⟩
  rcases hb with h | h | h | h
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))
  · refine Or.inr (Or.inl ?_)
    change -q.2 = 1
    simp [h]
  · refine Or.inl ?_
    change -q.2 = -1
    simp [h]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_crossQuarterTurn_spliceSquareBoundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_crossQuarterTurn_spliceSquareBoundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_crossQuarterTurn_spliceSquareBoundary ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_crossQuarterTurn_spliceSquareBoundary

theorem mapsTo_crossQuarterTurn_spliceCylinder :
    MapsTo crossQuarterTurn spliceCylinder spliceCylinder :=
  mapsTo_crossQuarterTurn_prod mapsTo_crossQuarterTurn_spliceSquare

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_crossQuarterTurn_spliceCylinder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_crossQuarterTurn_spliceCylinder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_crossQuarterTurn_spliceCylinder ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_crossQuarterTurn_spliceCylinder

theorem mapsTo_crossQuarterTurn_spliceEndDisks :
    MapsTo crossQuarterTurn spliceEndDisks spliceEndDisks :=
  mapsTo_crossQuarterTurn_prod mapsTo_crossQuarterTurn_spliceSquare

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_crossQuarterTurn_spliceEndDisks then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_crossQuarterTurn_spliceEndDisks"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_crossQuarterTurn_spliceEndDisks ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_crossQuarterTurn_spliceEndDisks

theorem mapsTo_crossQuarterTurn_spliceCore :
    MapsTo crossQuarterTurn spliceCore spliceCore :=
  mapsTo_crossQuarterTurn_prod mapsTo_crossQuarterTurn_origin

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_crossQuarterTurn_spliceCore then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_crossQuarterTurn_spliceCore"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_crossQuarterTurn_spliceCore ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_crossQuarterTurn_spliceCore

theorem mapsTo_crossQuarterTurn_crossingFigure :
    MapsTo crossQuarterTurn crossingFigure crossingFigure :=
  mapsTo_crossQuarterTurn_prod mapsTo_crossQuarterTurn_crossingArc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_crossQuarterTurn_crossingFigure then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_crossQuarterTurn_crossingFigure"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_crossQuarterTurn_crossingFigure ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_crossQuarterTurn_crossingFigure

theorem mapsTo_crossQuarterTurn_lateral :
    _root_.Set.MapsTo crossQuarterTurn (spliceSquareBoundary ×ˢ _root_.Set.Icc (0 : ℝ) 1)
      (spliceSquareBoundary ×ˢ _root_.Set.Icc (0 : ℝ) 1) :=
  mapsTo_crossQuarterTurn_prod mapsTo_crossQuarterTurn_spliceSquareBoundary

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_crossQuarterTurn_lateral then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_crossQuarterTurn_lateral"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_crossQuarterTurn_lateral ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_crossQuarterTurn_lateral

theorem image_crossQuarterTurn_spliceCylinder :
    crossQuarterTurn '' spliceCylinder = spliceCylinder :=
  image_crossQuarterTurn_of_mapsTo mapsTo_crossQuarterTurn_spliceCylinder

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.image_crossQuarterTurn_spliceCylinder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.image_crossQuarterTurn_spliceCylinder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.image_crossQuarterTurn_spliceCylinder ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.image_crossQuarterTurn_spliceCylinder

theorem image_crossQuarterTurn_spliceEndDisks :
    crossQuarterTurn '' spliceEndDisks = spliceEndDisks :=
  image_crossQuarterTurn_of_mapsTo mapsTo_crossQuarterTurn_spliceEndDisks

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.image_crossQuarterTurn_spliceEndDisks then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.image_crossQuarterTurn_spliceEndDisks"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.image_crossQuarterTurn_spliceEndDisks ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.image_crossQuarterTurn_spliceEndDisks

theorem image_crossQuarterTurn_spliceCore :
    crossQuarterTurn '' spliceCore = spliceCore :=
  image_crossQuarterTurn_of_mapsTo mapsTo_crossQuarterTurn_spliceCore

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.image_crossQuarterTurn_spliceCore then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.image_crossQuarterTurn_spliceCore"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.image_crossQuarterTurn_spliceCore ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.image_crossQuarterTurn_spliceCore

theorem image_crossQuarterTurn_crossingFigure :
    crossQuarterTurn '' crossingFigure = crossingFigure :=
  image_crossQuarterTurn_of_mapsTo mapsTo_crossQuarterTurn_crossingFigure

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.image_crossQuarterTurn_crossingFigure then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.image_crossQuarterTurn_crossingFigure"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.image_crossQuarterTurn_crossingFigure ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.image_crossQuarterTurn_crossingFigure

theorem image_crossQuarterTurn_lateral :
    crossQuarterTurn '' (spliceSquareBoundary ×ˢ _root_.Set.Icc (0 : ℝ) 1) =
      spliceSquareBoundary ×ˢ _root_.Set.Icc (0 : ℝ) 1 :=
  image_crossQuarterTurn_of_mapsTo mapsTo_crossQuarterTurn_lateral

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.image_crossQuarterTurn_lateral then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.image_crossQuarterTurn_lateral"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.image_crossQuarterTurn_lateral ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.image_crossQuarterTurn_lateral

def crossQuarterTurnLinear : ((ℝ × ℝ) × ℝ) →ₗ[ℝ] ((ℝ × ℝ) × ℝ) where
  toFun := crossQuarterTurn
  map_add' p q := by
    rcases p with ⟨⟨p1, p2⟩, p3⟩
    rcases q with ⟨⟨q1, q2⟩, q3⟩
    refine Prod.ext (Prod.ext ?_ ?_) ?_
    · change -(p2 + q2) = -p2 + -q2
      ring
    · change p1 + q1 = p1 + q1
      rfl
    · change p3 + q3 = p3 + q3
      rfl
  map_smul' c p := by
    rcases p with ⟨⟨p1, p2⟩, p3⟩
    refine Prod.ext (Prod.ext ?_ ?_) ?_
    · change -(c * p2) = c * -p2
      ring
    · change c * p1 = c * p1
      rfl
    · change c * p3 = c * p3
      rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.crossQuarterTurnLinear then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.crossQuarterTurnLinear"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.crossQuarterTurnLinear ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.crossQuarterTurnLinear

theorem isPiecewiseAffineOn_crossQuarterTurn :
    IsPiecewiseAffineOn crossQuarterTurn spliceCylinder :=
  (isPiecewiseAffineOn_of_affine_of_isHPolytope
    crossQuarterTurnLinear.toAffineMap isHPolytope_spliceCylinder).congr
    fun _ _ => rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_crossQuarterTurn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_crossQuarterTurn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_crossQuarterTurn ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_crossQuarterTurn

theorem isPLHomeomorphOn_crossQuarterTurn_spliceCylinder :
    IsPLHomeomorphOn crossQuarterTurn spliceCylinder spliceCylinder := by
  have hbij : _root_.Set.BijOn crossQuarterTurn spliceCylinder spliceCylinder := by
    have h := injective_crossQuarterTurn.injOn.bijOn_image (s := spliceCylinder)
    rwa [image_crossQuarterTurn_spliceCylinder] at h
  refine ⟨hbij, isPiecewiseAffineOn_crossQuarterTurn, ?_⟩
  let L3 := crossQuarterTurnLinear.comp (crossQuarterTurnLinear.comp crossQuarterTurnLinear)
  have hPA : IsPiecewiseAffineOn L3.toAffineMap spliceCylinder :=
    isPiecewiseAffineOn_of_affine_of_isHPolytope L3.toAffineMap isHPolytope_spliceCylinder
  refine hPA.congr fun y hy => ?_
  apply injective_crossQuarterTurn
  rw [hbij.invOn_invFunOn.2 hy]
  change y = crossQuarterTurn (crossQuarterTurn (crossQuarterTurn (crossQuarterTurn y)))
  rw [crossQuarterTurn_iterate_four]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_crossQuarterTurn_spliceCylinder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_crossQuarterTurn_spliceCylinder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_crossQuarterTurn_spliceCylinder ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_crossQuarterTurn_spliceCylinder

theorem nonempty_plSeamTubeChart_comp_crossQuarterTurn
    {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {chart : (ℝ × ℝ) × ℝ → M} (C : PLSeamTubeChart M chart) :
    Nonempty (PLSeamTubeChart M (chart ∘ crossQuarterTurn)) := by
  have hPL : IsPLHomeomorphOn crossQuarterTurn spliceCylinder
      (crossQuarterTurn '' spliceCylinder) := by
    rw [image_crossQuarterTurn_spliceCylinder]
    exact isPLHomeomorphOn_crossQuarterTurn_spliceCylinder
  exact PLSeamTubeChart.nonempty_precomp C hPL mapsTo_crossQuarterTurn_spliceCylinder

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.nonempty_plSeamTubeChart_comp_crossQuarterTurn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.nonempty_plSeamTubeChart_comp_crossQuarterTurn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.nonempty_plSeamTubeChart_comp_crossQuarterTurn ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.nonempty_plSeamTubeChart_comp_crossQuarterTurn

end DifferentialGeometry.Topology.PiecewiseLinear
