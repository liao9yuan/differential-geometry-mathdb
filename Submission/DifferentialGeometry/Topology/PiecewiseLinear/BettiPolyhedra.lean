/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.Homology.BettiNumber
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.EulerPolyhedra
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.ManifoldInvariance
import Submission.DifferentialGeometry.Topology.SimplicialComplex.GeometricConnectivity
import Submission.DifferentialGeometry.Topology.SimplicialComplex.GeometricHomology

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]

theorem bettiNumber_zero_of_isConnected (k : Type) [Field k] (hconn : IsConnected K.space) :
    Homology.bettiNumber k (TopCat.of K.space) 0 = 1 := by
  let _ : PathConnectedSpace K.space := isPathConnected_iff_pathConnectedSpace.mp
    (SimplicialComplex.isPathConnected_geometricSpace K hconn)
  exact Homology.bettiNumber_zero_of_pathConnectedSpace k (TopCat.of K.space)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.bettiNumber_zero_of_isConnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.bettiNumber_zero_of_isConnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.bettiNumber_zero_of_isConnected ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.bettiNumber_zero_of_isConnected

theorem bettiNumber_eq_zero_of_card_le (k : Type) [Field k] (d : ℕ)
    (hd : ∀ s ∈ K.faces, s.card ≤ d) (q : ℕ) (hq : d ≤ q) :
    Homology.bettiNumber k (TopCat.of K.space) q = 0 := by
  let _ := ModuleCat.subsingleton_of_isZero
    (SimplicialComplex.isZero_singularHomology_geometricSpace_of_card_le
      K (ModuleCat.of k k) d hd q hq)
  exact Module.finrank_zero_of_subsingleton

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.bettiNumber_eq_zero_of_card_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.bettiNumber_eq_zero_of_card_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.bettiNumber_eq_zero_of_card_le ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.bettiNumber_eq_zero_of_card_le

theorem eulerChar_eq_sum_bettiNumber (k : Type) [Field k] (n : ℕ)
    (hd : ∀ s ∈ K.faces, s.card ≤ n + 1) :
    eulerChar K = ∑ q ∈ Finset.range (n + 1),
      (-1 : ℤ) ^ q * (Homology.bettiNumber k (TopCat.of K.space) q : ℤ) := by
  rw [eulerChar_eq_singular K k]
  exact Homology.eulerChar_eq_sum k n fun q hq =>
    SimplicialComplex.isZero_singularHomology_geometricSpace_of_card_le
      K (ModuleCat.of k k) (n + 1) hd q hq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.eulerChar_eq_sum_bettiNumber then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.eulerChar_eq_sum_bettiNumber"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.eulerChar_eq_sum_bettiNumber ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.eulerChar_eq_sum_bettiNumber

theorem eulerChar_eq_bettiZero_sub_bettiOne_add_bettiTwo
    (hd : ∀ s ∈ K.faces, s.card ≤ 3) :
    eulerChar K = (Homology.bettiNumber ℚ (TopCat.of K.space) 0 : ℤ) -
      (Homology.bettiOne K.space : ℤ) + (Homology.bettiNumber ℚ (TopCat.of K.space) 2 : ℤ) := by
  rw [eulerChar_eq_sum_bettiNumber K ℚ 2 hd]
  norm_num [Finset.sum_range_succ, Homology.bettiOne]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.eulerChar_eq_bettiZero_sub_bettiOne_add_bettiTwo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.eulerChar_eq_bettiZero_sub_bettiOne_add_bettiTwo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.eulerChar_eq_bettiZero_sub_bettiOne_add_bettiTwo ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.eulerChar_eq_bettiZero_sub_bettiOne_add_bettiTwo

theorem eulerChar_eq_one_sub_bettiOne_add_bettiTwo
    (hd : ∀ s ∈ K.faces, s.card ≤ 3) (hconn : IsConnected K.space) :
    eulerChar K = 1 - (Homology.bettiOne K.space : ℤ) +
      (Homology.bettiNumber ℚ (TopCat.of K.space) 2 : ℤ) := by
  rw [eulerChar_eq_bettiZero_sub_bettiOne_add_bettiTwo K hd,
    bettiNumber_zero_of_isConnected K ℚ hconn, Nat.cast_one]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.eulerChar_eq_one_sub_bettiOne_add_bettiTwo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.eulerChar_eq_one_sub_bettiOne_add_bettiTwo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.eulerChar_eq_one_sub_bettiOne_add_bettiTwo ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.eulerChar_eq_one_sub_bettiOne_add_bettiTwo

theorem bettiOne_graph (hd : ∀ s ∈ K.faces, s.card ≤ 2) (hconn : IsConnected K.space) :
    (Homology.bettiOne K.space : ℤ) = 1 - eulerChar K := by
  have h := eulerChar_eq_sum_bettiNumber K ℚ 1 hd
  norm_num [Finset.sum_range_succ, bettiNumber_zero_of_isConnected K ℚ hconn] at h
  change (Homology.bettiNumber ℚ (TopCat.of K.space) 1 : ℤ) = 1 - eulerChar K
  omega

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.bettiOne_graph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.bettiOne_graph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.bettiOne_graph ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.bettiOne_graph

theorem bettiOne_polygon [FiniteDimensional ℝ E] (hK : IsPLSphere 1 K.space) :
    Homology.bettiOne K.space = 1 := by
  have hd : ∀ s ∈ K.faces, s.card ≤ 2 := fun _ hs =>
    hK.isCombinatorialManifold.card_le K hs
  have h := bettiOne_graph K hd hK.isConnected
  rw [eulerChar_of_isPLSphere_one K hK] at h
  omega

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.bettiOne_polygon then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.bettiOne_polygon"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.bettiOne_polygon ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.bettiOne_polygon

end DifferentialGeometry.Topology.PiecewiseLinear
