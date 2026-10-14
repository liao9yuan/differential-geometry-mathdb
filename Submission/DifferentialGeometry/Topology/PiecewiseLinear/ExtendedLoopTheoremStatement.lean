/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.Connected.TwoSided
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Orientation
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Topology.Homotopy.Contractible

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

open _root_.Classical in
def Moise264Orientable : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) (_ : Finite K.faces),
    IsCombinatorialManifoldWithBoundary 3 K → IsOrientable 3 K →
    ∀ (L : Geometry.SimplicialComplex ℝ E) (_ : Finite L.faces),
      IsCombinatorialManifold 2 L →
    ∀ hLK : L.space ⊆ K.space \ (boundaryComplex 3 K).space,
      IsTwoSided (((↑) : K.space → E) ⁻¹' L.space) →
    ∀ (x : L.space) (g : FundamentalGroup L.space x),
      g ≠ 1 →
      FundamentalGroup.map
        (⟨Set.inclusion (hLK.trans _root_.Set.sdiff_subset), continuous_inclusion _⟩ :
          C(L.space, K.space)) x g = 1 →
      ∃ (Δ : Set E) (r : (Fin 3 → ℝ) → E),
        IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) Δ ∧
        Δ ⊆ K.space \ (boundaryComplex 3 K).space ∧
        Δ ∩ L.space = r '' stdSimplexBoundary 2 ∧
        ∃ hb : r '' stdSimplexBoundary 2 ⊆ L.space,
          ¬ (⟨Set.inclusion hb, continuous_inclusion hb⟩ :
            C(r '' stdSimplexBoundary 2, L.space)).Nullhomotopic

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.Moise264Orientable then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.Moise264Orientable"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.Moise264Orientable ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.Moise264Orientable

end DifferentialGeometry.Topology.PiecewiseLinear
