import Mathlib.Topology.Homotopy.Equiv
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open scoped _root_.ContinuousMap

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

def homotopyEquiv_of_retraction {K U : Type*} [TopologicalSpace K] [TopologicalSpace U]
    (i : C(K, U)) (r : C(U, K)) (hri : r.comp i = ContinuousMap.id K)
    (hh : (i.comp r).Homotopic (ContinuousMap.id U)) : K ≃ₕ U where
  toFun := i
  invFun := r
  left_inv := by simpa only [hri] using ContinuousMap.Homotopic.refl (ContinuousMap.id K)
  right_inv := hh

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.homotopyEquiv_of_retraction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.homotopyEquiv_of_retraction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.homotopyEquiv_of_retraction ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.homotopyEquiv_of_retraction

theorem simplyConnectedSpace_iff_of_homotopyRetract {K U : Type*} [TopologicalSpace K]
    [TopologicalSpace U] (i : C(K, U)) (r : C(U, K))
    (hri : r.comp i = ContinuousMap.id K)
    (hh : (i.comp r).Homotopic (ContinuousMap.id U)) :
    SimplyConnectedSpace K ↔ SimplyConnectedSpace U :=
  (homotopyEquiv_of_retraction i r hri hh).simplyConnectedSpace_iff

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.simplyConnectedSpace_iff_of_homotopyRetract then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.simplyConnectedSpace_iff_of_homotopyRetract"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.simplyConnectedSpace_iff_of_homotopyRetract ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.simplyConnectedSpace_iff_of_homotopyRetract

theorem simplyConnectedSpace_of_homotopyRetract {K U : Type*} [TopologicalSpace K]
    [TopologicalSpace U] (i : C(K, U)) (r : C(U, K))
    (hri : r.comp i = ContinuousMap.id K)
    (hh : (i.comp r).Homotopic (ContinuousMap.id U)) [SimplyConnectedSpace K] :
    SimplyConnectedSpace U :=
  (simplyConnectedSpace_iff_of_homotopyRetract i r hri hh).mp ‹_›

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.simplyConnectedSpace_of_homotopyRetract then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.simplyConnectedSpace_of_homotopyRetract"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.simplyConnectedSpace_of_homotopyRetract ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.simplyConnectedSpace_of_homotopyRetract

theorem simplyConnectedSpace_of_homotopySection {K U : Type*} [TopologicalSpace K]
    [TopologicalSpace U] (i : C(K, U)) (r : C(U, K))
    (hri : r.comp i = ContinuousMap.id K)
    (hh : (i.comp r).Homotopic (ContinuousMap.id U)) [SimplyConnectedSpace U] :
    SimplyConnectedSpace K :=
  (simplyConnectedSpace_iff_of_homotopyRetract i r hri hh).mpr ‹_›

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.simplyConnectedSpace_of_homotopySection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.simplyConnectedSpace_of_homotopySection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.simplyConnectedSpace_of_homotopySection ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.simplyConnectedSpace_of_homotopySection

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
