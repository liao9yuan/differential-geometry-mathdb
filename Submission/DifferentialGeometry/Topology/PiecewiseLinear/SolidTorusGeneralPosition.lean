/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.CombinatorialSolidTorus
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

section RelativeGeneralPosition

def Fits (A U S : Set (EuclideanSpace ℝ (Fin 3))) : Prop :=
  IsCombinatorialSolidTorus S ∧ A ⊆ interior S ∧ S ⊆ U

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.Fits then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.Fits"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.Fits ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.Fits

def PairGP (R S : Set (EuclideanSpace ℝ (Fin 3))) : Prop :=
  (∀ x ∈ frontier R ∩ frontier S, HasPLCrossingAt (frontier R) (frontier S) x) ∧
    ∃ (ι : Type) (_ : Finite ι) (G : ι → Set (EuclideanSpace ℝ (Fin 3))),
      (∀ i, IsPLSphere 1 (G i)) ∧ (Pairwise fun i i' => Disjoint (G i) (G i')) ∧
        frontier R ∩ frontier S = ⋃ i, G i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.PairGP then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.PairGP"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.PairGP ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.PairGP

theorem PairGP.symm {R S : Set (EuclideanSpace ℝ (Fin 3))} (h : PairGP R S) : PairGP S R := by
  obtain ⟨hcross, ι, hι, G, hG, hdisj, heq⟩ := h
  refine ⟨fun x hx => ?_, ι, hι, G, hG, hdisj, ?_⟩
  · rw [_root_.Set.inter_comm] at hx
    exact (hcross x hx).symm
  · rw [_root_.Set.inter_comm]
    exact heq

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Topology.PiecewiseLinear.PairGP
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.PairGP.symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.PairGP.symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.PairGP.symm ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.PairGP.symm

end RelativeGeneralPosition

end DifferentialGeometry.Topology.PiecewiseLinear
