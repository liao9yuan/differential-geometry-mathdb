/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.NonseparatingPolygonCarrier
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.SeparatingPolygonDisk

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem carriesGenerator_or_exists_isPLCell_of_polygon_disjoint_carrier
    {S K G : Set (EuclideanSpace ℝ (Fin 3))} (hS : IsCombinatorialSolidTorus S)
    (hK : IsPLSphere 1 K) (hKS : K ⊆ frontier S) (hKgen : CarriesFundamentalGroupOnto K S)
    (hG : IsPLSphere 1 G) (hGS : G ⊆ frontier S) (hGK : Disjoint G K) :
    CarriesFundamentalGroupOnto G S ∨
      ∃ (Δ : Set (EuclideanSpace ℝ (Fin 3))) (r : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)),
        IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) Δ ∧ Δ ⊆ frontier S ∧
          G = r '' stdSimplexBoundary 2 := by
  by_cases hsep : IsPreconnected (frontier S \ G)
  · exact Or.inl (hS.carriesFundamentalGroupOnto_of_isPreconnected_sdiff hK hKS hKgen hG hGS hGK
      hsep)
  · exact Or.inr
      (hS.isPLTorus_frontier.exists_isPLHomeomorphOn_disk_of_not_isPreconnected_sdiff hG hGS hsep)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.carriesGenerator_or_exists_isPLCell_of_polygon_disjoint_carrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.carriesGenerator_or_exists_isPLCell_of_polygon_disjoint_carrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.carriesGenerator_or_exists_isPLCell_of_polygon_disjoint_carrier ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.carriesGenerator_or_exists_isPLCell_of_polygon_disjoint_carrier

end DifferentialGeometry.Topology.PiecewiseLinear
