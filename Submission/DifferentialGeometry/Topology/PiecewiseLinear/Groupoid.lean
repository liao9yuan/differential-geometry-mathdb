/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PiecewiseAffine
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.HasGroupoid

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable (n : ℕ)

def plPregroupoid : Pregroupoid (EuclideanSpace ℝ (Fin n)) where
  property f u := IsPiecewiseAffineOn f u
  comp hf hg _ _ _ := hg.comp hf
  id_mem := isPiecewiseAffineOn_id isOpen_univ
  locality _ h := isPiecewiseAffineOn_of_locally h
  congr _ hfg hf := hf.congr fun x hx => hfg x hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.plPregroupoid then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.plPregroupoid"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.plPregroupoid ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.plPregroupoid

def plGroupoid : StructureGroupoid (EuclideanSpace ℝ (Fin n)) := (plPregroupoid n).groupoid

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.plGroupoid then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.plGroupoid"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.plGroupoid ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.plGroupoid

variable {n}

theorem mem_plGroupoid_iff
    {e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n))} :
    e ∈ plGroupoid n ↔ IsPiecewiseAffineOn e e.source ∧ IsPiecewiseAffineOn e.symm e.target :=
  mem_groupoid_of_pregroupoid

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mem_plGroupoid_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mem_plGroupoid_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mem_plGroupoid_iff ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mem_plGroupoid_iff

theorem mem_plGroupoid_of_isPiecewiseAffineOn
    {e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n))}
    (he : IsPiecewiseAffineOn e e.source) : e ∈ plGroupoid n :=
  mem_plGroupoid_iff.mpr ⟨he, he.symm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mem_plGroupoid_of_isPiecewiseAffineOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mem_plGroupoid_of_isPiecewiseAffineOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mem_plGroupoid_of_isPiecewiseAffineOn ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mem_plGroupoid_of_isPiecewiseAffineOn

theorem ofSet_mem_plGroupoid {s : Set (EuclideanSpace ℝ (Fin n))} (hs : IsOpen s) :
    OpenPartialHomeomorph.ofSet s hs ∈ plGroupoid n :=
  mem_plGroupoid_of_isPiecewiseAffineOn (isPiecewiseAffineOn_id hs)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.ofSet_mem_plGroupoid then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.ofSet_mem_plGroupoid"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.ofSet_mem_plGroupoid ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.ofSet_mem_plGroupoid

instance _root_.Submission.DifferentialGeometry.Topology.PiecewiseLinear.instClosedUnderRestrictionEuclideanSpaceRealFinPlGroupoid : ClosedUnderRestriction (plGroupoid n) :=
  (closedUnderRestriction_iff_id_le _).mpr <| by
    rw [StructureGroupoid.le_iff]
    rintro e ⟨s, hs, hes⟩
    exact (plGroupoid n).mem_of_eqOnSource (ofSet_mem_plGroupoid hs) hes

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.instClosedUnderRestrictionEuclideanSpaceRealFinPlGroupoid then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.instClosedUnderRestrictionEuclideanSpaceRealFinPlGroupoid"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.instClosedUnderRestrictionEuclideanSpaceRealFinPlGroupoid ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.instClosedUnderRestrictionEuclideanSpaceRealFinPlGroupoid

end DifferentialGeometry.Topology.PiecewiseLinear
