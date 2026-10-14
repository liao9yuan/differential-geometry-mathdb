/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.EmbeddedDiskTower
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.SphericalShellCompression

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.Topology.PiecewiseLinear

def LemmaTwoStatement : Prop :=
  ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {M : ℕ} {S : NormalSystem F} {T : NormalSystem (EuclideanSpace ℝ (Fin M))},
    NormalSystem.DoubleCoverReduction S T →
    T.sourceComplex.space ∩ T.singularMap ⁻¹' T.boundaryComplex.space =
      frontier T.sourceComplex.space →
    T.basepoint = T.boundaryLoop 0 →
    Nonempty (NormalSystem.EmbeddedDisk T) → Nonempty (NormalSystem.EmbeddedDisk S)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.LemmaTwoStatement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.LemmaTwoStatement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.LemmaTwoStatement ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.LemmaTwoStatement

theorem moise304_of_lemmaTwo (lemmaTwo : LemmaTwoStatement) : Moise304 :=
  moise304_of_moise252 (moise252_of_lemmaTwo lemmaTwo)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.moise304_of_lemmaTwo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.moise304_of_lemmaTwo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.moise304_of_lemmaTwo ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.moise304_of_lemmaTwo

end DifferentialGeometry.Topology.PiecewiseLinear
