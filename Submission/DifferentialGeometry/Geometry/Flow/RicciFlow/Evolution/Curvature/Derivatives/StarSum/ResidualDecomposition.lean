import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.Derivatives.StarSum.SpatialCommutator

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

def rmGammaCost (d k : ℕ) : Real :=
  (d : Real) ^ 2 * (12 + 3 * k)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.rmGammaCost then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.rmGammaCost"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.rmGammaCost ``Submission.DifferentialGeometry.PDE.RicciFlow.rmGammaCost

theorem commStarCost_nonneg (d k : ℕ) :
    0 ≤ commStarCost d k := by
  unfold commStarCost
  positivity

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.commStarCost_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.commStarCost_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.commStarCost_nonneg ``Submission.DifferentialGeometry.PDE.RicciFlow.commStarCost_nonneg

theorem rmGammaCost_nonneg (d k : ℕ) :
    0 ≤ rmGammaCost d k := by
  unfold rmGammaCost
  positivity

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.rmGammaCost_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.rmGammaCost_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.rmGammaCost_nonneg ``Submission.DifferentialGeometry.PDE.RicciFlow.rmGammaCost_nonneg

def rmResidualCost (d : ℕ) : ℕ → Real
  | 0 => 12 * (d : Real) ^ 2
  | k + 1 =>
      2 * rmResidualCost d k + commStarCost d k + rmGammaCost d k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.rmResidualCost then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.rmResidualCost"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.rmResidualCost ``Submission.DifferentialGeometry.PDE.RicciFlow.rmResidualCost

theorem rmResidualCost_nonneg (d k : ℕ) :
    0 ≤ rmResidualCost d k := by
  induction k with
  | zero =>
      simp only [rmResidualCost]
      positivity
  | succ k ih =>
      simp only [rmResidualCost]
      have hcomm := commStarCost_nonneg d k
      have hgamma := rmGammaCost_nonneg d k
      positivity

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.rmResidualCost_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.rmResidualCost_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.rmResidualCost_nonneg ``Submission.DifferentialGeometry.PDE.RicciFlow.rmResidualCost_nonneg

end DifferentialGeometry.PDE.RicciFlow
