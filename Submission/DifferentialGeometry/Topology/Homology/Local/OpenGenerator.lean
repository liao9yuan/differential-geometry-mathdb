/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.Homology.Local.NeighborhoodGenerator

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Set _root_.Metric

noncomputable section

namespace DifferentialGeometry.Homology

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (d + 1))
local notation "Z" => ModuleCat.of ℤ ℤ

def euclideanOpenLocalGenerator {U : Set E} (hU : IsOpen U) (x : E) (hx : x ∈ U) :
    relativeHomology (TopCat.of U) ({(⟨x, hx⟩ : U)}ᶜ : Set U) Z (d + 1) :=
  (puncturedNeighborhoodHomologyIso (TopCat.of E) U x hx Z hU (d + 1)).inv
    (euclideanLocalGeneratorAt x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.euclideanOpenLocalGenerator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.euclideanOpenLocalGenerator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.euclideanOpenLocalGenerator ``Submission.DifferentialGeometry.Homology.euclideanOpenLocalGenerator

theorem euclideanOpenLocalGenerator_inclusion {U : Set E}
    (hU : IsOpen U) (x : E) (hx : x ∈ U) :
    (puncturedNeighborhoodHomologyIso (TopCat.of E) U x hx Z hU (d + 1)).hom
      (euclideanOpenLocalGenerator hU x hx) = euclideanLocalGeneratorAt x := by
  exact congrArg (fun g => g (euclideanLocalGeneratorAt x))
    (puncturedNeighborhoodHomologyIso (TopCat.of E) U x hx Z hU (d + 1)).inv_hom_id

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.euclideanOpenLocalGenerator_inclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.euclideanOpenLocalGenerator_inclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.euclideanOpenLocalGenerator_inclusion ``Submission.DifferentialGeometry.Homology.euclideanOpenLocalGenerator_inclusion

theorem euclideanOpenLocalGenerator_ball (x : E) (r : ℝ) (hr : 0 < r) :
    euclideanOpenLocalGenerator _root_.Metric.isOpen_ball x (_root_.Metric.mem_ball_self hr) =
      euclideanBallLocalGenerator x r hr := by
  apply (ModuleCat.mono_iff_injective
    (puncturedNeighborhoodHomologyIso (TopCat.of E) (_root_.Metric.ball x r) x
      (_root_.Metric.mem_ball_self hr) Z _root_.Metric.isOpen_ball (d + 1)).hom).mp inferInstance
  rw [euclideanOpenLocalGenerator_inclusion, euclideanBallLocalGenerator_inclusion]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.euclideanOpenLocalGenerator_ball then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.euclideanOpenLocalGenerator_ball"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.euclideanOpenLocalGenerator_ball ``Submission.DifferentialGeometry.Homology.euclideanOpenLocalGenerator_ball

theorem euclideanOpenLocalGenerator_smul_injective {U : Set E}
    (hU : IsOpen U) (x : E) (hx : x ∈ U) :
    Function.Injective (fun m : ℤ => m • euclideanOpenLocalGenerator hU x hx) := by
  intro m n hmn
  let q := puncturedNeighborhoodHomologyIso (TopCat.of E) U x hx Z hU (d + 1)
  let t := localTranslationHomologyIso E x Z (d + 1)
  let s := localEuclideanSphereHomologyIso Z (d + 1) d
  let a := q.toLinearEquiv.toAddEquiv.trans
    (t.toLinearEquiv.toAddEquiv.trans
      (s.toLinearEquiv.toAddEquiv.trans
        (DifferentialGeometry.LocalDegree.euclideanSphereTopReducedHomologyEquiv d)))
  have ha : a (euclideanOpenLocalGenerator hU x hx) = 1 := by
    change DifferentialGeometry.LocalDegree.euclideanSphereTopReducedHomologyEquiv d
      (s.hom (t.hom (q.hom (euclideanOpenLocalGenerator hU x hx)))) = 1
    rw [euclideanOpenLocalGenerator_inclusion, euclideanLocalGeneratorAt_translate]
    simp [s, euclideanLocalGenerator,
      DifferentialGeometry.LocalDegree.euclideanSphereTopReducedHomologyEquiv_generator]
  have h := congrArg a hmn
  simpa only [map_zsmul, ha, smul_eq_mul, mul_one] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.euclideanOpenLocalGenerator_smul_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.euclideanOpenLocalGenerator_smul_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.euclideanOpenLocalGenerator_smul_injective ``Submission.DifferentialGeometry.Homology.euclideanOpenLocalGenerator_smul_injective

theorem euclideanOpenLocalGenerator_map_inclusion {U V : Set E}
    (hU : IsOpen U) (hV : IsOpen V) (hUV : U ⊆ V) (x : E) (hx : x ∈ U)
    (j : TopCat.of U ⟶ TopCat.of V)
    (hj : ∀ z : U, (j z : E) = (z : E))
    (hjpunct : _root_.Set.MapsTo j ({(⟨x, hx⟩ : U)}ᶜ : Set U)
      ({(⟨x, hUV hx⟩ : V)}ᶜ : Set V)) :
    relativeHomologyMap Z j hjpunct (d + 1) (euclideanOpenLocalGenerator hU x hx) =
      euclideanOpenLocalGenerator hV x (hUV hx) := by
  let iU := puncturedNeighborhoodHomologyIso (TopCat.of E) U x hx Z hU (d + 1)
  let iV := puncturedNeighborhoodHomologyIso (TopCat.of E) V x (hUV hx) Z hV (d + 1)
  have heq : relativeHomologyMap Z j hjpunct (d + 1) ≫ iV.hom = iU.hom := by
    dsimp only [iU, iV]
    rw [puncturedNeighborhoodHomologyIso_hom, puncturedNeighborhoodHomologyIso_hom,
      ← relativeHomologyMap_comp]
    congr 1
    exact TopCat.ext hj
  apply (ModuleCat.mono_iff_injective iV.hom).mp inferInstance
  change (relativeHomologyMap Z j hjpunct (d + 1) ≫ iV.hom)
    (euclideanOpenLocalGenerator hU x hx) = _
  rw [heq]
  exact (euclideanOpenLocalGenerator_inclusion hU x hx).trans
    (euclideanOpenLocalGenerator_inclusion hV x (hUV hx)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.euclideanOpenLocalGenerator_map_inclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.euclideanOpenLocalGenerator_map_inclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.euclideanOpenLocalGenerator_map_inclusion ``Submission.DifferentialGeometry.Homology.euclideanOpenLocalGenerator_map_inclusion

end DifferentialGeometry.Homology
