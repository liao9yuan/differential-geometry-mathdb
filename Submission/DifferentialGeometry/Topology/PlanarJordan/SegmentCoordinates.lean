/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PlanarJordan.PlanarLocalAffine
import Mathlib.Geometry.Manifold.Diffeomorph

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set
open scoped _root_.ContDiff _root_.Manifold

namespace DifferentialGeometry.Topology.PlanarJordan

open _root_.Submission.Schoenflies (Plane)

theorem exists_diffeomorph_lineMap {p q : Plane} (hpq : p ≠ q) :
    ∃ D : Plane ≃ₘ[ℝ] Plane, ∀ t : ℝ,
      D (Plane.mk t 0) = AffineMap.lineMap p q t := by
  let d := q - p
  let L : Plane →L[ℝ] Plane :=
    (EuclideanSpace.proj 0).smulRight d + (EuclideanSpace.proj 1).smulRight (Plane.perp d)
  have hdet : LinearMap.det (L : Plane →ₗ[ℝ] Plane) ≠ 0 := by
    rw [det_eq_planeDet]
    have h0 : L (EuclideanSpace.single 0 1) = d := by simp [L]
    have h1 : L (EuclideanSpace.single 1 1) = Plane.perp d := by simp [L]
    rw [h0, h1, Plane.det_perp_self]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hpq.symm))
  let T : Plane ≃ₘ[ℝ] Plane := {
    toEquiv := Equiv.addRight p
    contMDiff_toFun := (contDiff_id.add contDiff_const).contMDiff
    contMDiff_invFun := (contDiff_id.sub contDiff_const).contMDiff }
  refine ⟨(L.toContinuousLinearEquivOfDetNeZero hdet).toDiffeomorph.trans T, fun t => ?_⟩
  change (L.toContinuousLinearEquivOfDetNeZero hdet) (Plane.mk t 0) + p = _
  rw [ContinuousLinearMap.toContinuousLinearEquivOfDetNeZero_apply]
  change t • (q - p) + (0 : ℝ) • Plane.perp (q - p) + p = _
  simp only [zero_smul, add_zero, AffineMap.lineMap_apply_module']

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PlanarJordan.exists_diffeomorph_lineMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PlanarJordan.exists_diffeomorph_lineMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PlanarJordan.exists_diffeomorph_lineMap ``Submission.DifferentialGeometry.Topology.PlanarJordan.exists_diffeomorph_lineMap

end DifferentialGeometry.Topology.PlanarJordan
