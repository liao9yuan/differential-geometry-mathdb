/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.LocallyFiniteInwardPush
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.SkeletonReduction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

theorem moise352InwardPush_three : Moise352InwardPush.{u} 3 := by
  intro M₁ M₂ _ _ _ _ _ _ _ _ _ K hK h hemb ψ hψ hψpos
  exact hK.exists_isPLOn_injOn_leftInvOn_dist_lt
    (continuousOn_iff_continuous_domRestrict.mpr hemb.continuous) hψ hψpos

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.moise352InwardPush_three then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.moise352InwardPush_three"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.moise352InwardPush_three ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.moise352InwardPush_three

end DifferentialGeometry.Topology.PiecewiseLinear
