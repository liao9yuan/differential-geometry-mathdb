/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.SimplicialComplex.GeometricRealizationHomeomorphism
import Submission.DifferentialGeometry.Topology.SimplicialSet.FiniteRealizationHomology
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Nondegenerate

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicTopology

namespace DifferentialGeometry.Topology.SimplicialComplex

universe u

theorem isZero_singularHomology_geometricSpace_of_card_le
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {k : Type u} [Ring k] (R : ModuleCat.{u} k) (d : ℕ)
    (hd : ∀ s ∈ K.faces, s.card ≤ d) (q : ℕ) (hq : d ≤ q) :
    IsZero (((_root_.AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) q).obj R).obj (TopCat.of K.space)) := by
  classical
  let _ := linearOrderOfSTO (WellOrderingRel : E → E → Prop)
  let X := orderedSimplicialSet K.toPreAbstractSimplicialComplex
  let _ : X.HasDimensionLT d := orderedSimplicialSet_hasDimensionLT K.toPreAbstractSimplicialComplex
      d hd
  have hX := X.isZero_homology_of_hasDimensionLT R q d hq
  have hT := hX.of_iso (DifferentialGeometry.SSet.realizationHomologyIso R X q).symm
  exact hT.of_iso (((_root_.AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) q).obj R).mapIso
    (TopCat.isoOfHomeo (geometricRealizationHomeomorphism K))).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.isZero_singularHomology_geometricSpace_of_card_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.isZero_singularHomology_geometricSpace_of_card_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.isZero_singularHomology_geometricSpace_of_card_le ``Submission.DifferentialGeometry.Topology.SimplicialComplex.isZero_singularHomology_geometricSpace_of_card_le

end DifferentialGeometry.Topology.SimplicialComplex
