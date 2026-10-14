/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.LinearAlgebra.Determinant

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open scoped _root_.ContDiff _root_.Manifold

namespace IsLocalDiffeomorphAt
open _root_.IsLocalDiffeomorphAt

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {n : WithTop ℕ∞} {f : E → E} {x : E}

open _root_.IsLocalDiffeomorphAt in
theorem det_fderiv_ne_zero (hf : IsLocalDiffeomorphAt 𝓘(𝕜, E) 𝓘(𝕜, E) n f x)
    (hn : n ≠ 0) : LinearMap.det (fderiv 𝕜 f x : E →ₗ[𝕜] E) ≠ 0 := by
  rw [← mfderiv_eq_fderiv]
  exact (hf.mfderivToContinuousLinearEquiv hn).toLinearEquiv.isUnit_det'.ne_zero

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsLocalDiffeomorphAt.det_fderiv_ne_zero then
    throwError "Refusing to shadow existing declaration IsLocalDiffeomorphAt.det_fderiv_ne_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `IsLocalDiffeomorphAt.det_fderiv_ne_zero ``Submission.IsLocalDiffeomorphAt.det_fderiv_ne_zero

end IsLocalDiffeomorphAt
