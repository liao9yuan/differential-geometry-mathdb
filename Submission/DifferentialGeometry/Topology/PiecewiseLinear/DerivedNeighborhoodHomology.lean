/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.Homology.BettiNumber
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodRetraction
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.EulerPolyhedra

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces]

open _root_.Classical in
noncomputable instance finite_derivedNeighborhood_faces
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] :
    Finite (derivedNeighborhood K L).faces :=
  (derivedNeighborhood_faces_finite K L).to_subtype

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.finite_derivedNeighborhood_faces then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.finite_derivedNeighborhood_faces"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.finite_derivedNeighborhood_faces ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.finite_derivedNeighborhood_faces

open _root_.Classical in
noncomputable def derivedNeighborhoodHomotopyEquiv (hL : L.faces ⊆ K.faces) :
    ContinuousMap.HomotopyEquiv (derivedNeighborhood K L).space L.space := by
  let e : derivedNeighborhoodSubcomplex K L ≃ₜ L.space := {
    toFun := fun x => ⟨x.1.1, x.2⟩
    invFun := fun x => ⟨⟨x.1, subcomplex_space_subset_derivedNeighborhood hL x.2⟩, x.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _ }
  exact (derivedNeighborhoodStrongDeformationRetract hL).toHomotopyEquiv.trans e.toHomotopyEquiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodHomotopyEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodHomotopyEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodHomotopyEquiv ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodHomotopyEquiv

open _root_.Classical in
theorem bettiNumber_derivedNeighborhood_eq (k : Type) [Field k] (hL : L.faces ⊆ K.faces) (q : ℕ) :
    Homology.bettiNumber k (TopCat.of (derivedNeighborhood K L).space) q =
      Homology.bettiNumber k (TopCat.of L.space) q :=
  Homology.bettiNumber_eq_of_homotopyEquiv k
    (X := TopCat.of (derivedNeighborhood K L).space) (Y := TopCat.of L.space)
    (derivedNeighborhoodHomotopyEquiv hL) q

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.bettiNumber_derivedNeighborhood_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.bettiNumber_derivedNeighborhood_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.bettiNumber_derivedNeighborhood_eq ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.bettiNumber_derivedNeighborhood_eq

open _root_.Classical in
theorem bettiOne_derivedNeighborhood_eq (hL : L.faces ⊆ K.faces) :
    Homology.bettiOne (derivedNeighborhood K L).space = Homology.bettiOne L.space :=
  bettiNumber_derivedNeighborhood_eq ℚ hL 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.bettiOne_derivedNeighborhood_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.bettiOne_derivedNeighborhood_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.bettiOne_derivedNeighborhood_eq ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.bettiOne_derivedNeighborhood_eq

open _root_.Classical in
theorem eulerChar_derivedNeighborhood_eq [Finite L.faces] (hL : L.faces ⊆ K.faces) :
    eulerChar (derivedNeighborhood K L) = eulerChar L := by
  rw [eulerChar_eq_singular (derivedNeighborhood K L) ℚ, eulerChar_eq_singular L ℚ]
  exact Homology.eulerChar_eq_of_homotopyEquiv ℚ
    (X := TopCat.of (derivedNeighborhood K L).space) (Y := TopCat.of L.space)
    (derivedNeighborhoodHomotopyEquiv hL)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.eulerChar_derivedNeighborhood_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.eulerChar_derivedNeighborhood_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.eulerChar_derivedNeighborhood_eq ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.eulerChar_derivedNeighborhood_eq

end DifferentialGeometry.Topology.PiecewiseLinear
