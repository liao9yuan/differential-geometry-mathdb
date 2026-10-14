/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.MoiseChain
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.ExistsAnnulusParametrizationOfProductCircleCut
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.EssentialPolygonProductCoordinates

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem moise286 : Moise286 := by
  classical
  intro S hS n G hn hG hGS hdisj hess x hx
  obtain ⟨J, Q, f, q, hJ, hQ, hf, hq, hinj, hfamily⟩ :=
    exists_product_coordinates_for_disjoint_essential_polygons hS G hn hG hGS hdisj hess
  have hG_eq : G = fun i => f '' (J ×ˢ {q i}) := funext hfamily
  rw [hG_eq] at hx ⊢
  obtain ⟨i, j, hij, ρ, hρ, hzero, hone⟩ :=
    exists_annulus_parametrization_of_product_circle_cut hJ hQ hf hn q hq hinj hx
  exact ⟨i, j, hij, J, ρ, hJ, hρ, hzero, hone⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.moise286 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.moise286"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.moise286 ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.moise286

end DifferentialGeometry.Topology.PiecewiseLinear
