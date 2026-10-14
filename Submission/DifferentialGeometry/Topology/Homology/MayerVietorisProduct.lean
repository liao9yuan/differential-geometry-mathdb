/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.Homology.Algebra.PushoutHomologyProduct
import Submission.DifferentialGeometry.Topology.Homology.SmallChains.IntersectionPreimage
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.Integral

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicTopology

namespace DifferentialGeometry.Topology

theorem bijective_integralSingularHomologyMap_intersection
    {X : Type} [TopologicalSpace X] {U V : Set X}
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = _root_.Set.univ) (n : ℕ)
    (hn : Subsingleton (integralSingularHomology n X))
    (hn' : Subsingleton (integralSingularHomology (n + 1) X)) :
    Function.Bijective (fun a : integralSingularHomology n (U ∩ V : Set X) =>
      (integralSingularHomologyMap n
        (⟨inclusion _root_.Set.inter_subset_left, continuous_inclusion inter_subset_left⟩ :
          C((U ∩ V : Set X), U)) a,
      integralSingularHomologyMap n
        (⟨inclusion _root_.Set.inter_subset_right, continuous_inclusion inter_subset_right⟩ :
          C((U ∩ V : Set X), V)) a)) := by
  let T := TopCat.of X
  let R := integralSingularCoefficients
  let F := Homology.twoSetFamily T U V
  have hopen : ∀ i, IsOpen (F i) := by
    intro i
    cases i
    · exact hV
    · exact hU
  have hcov : ∀ x : T, ∃ i, x ∈ F i := by
    intro x
    have hx : x ∈ U ∪ V := hcover.symm ▸ _root_.Set.mem_univ x
    rcases hx with hx | hx
    · exact ⟨true, hx⟩
    · exact ⟨false, hx⟩
  have hsmall (k : ℕ) (hk : Subsingleton (integralSingularHomology k X)) :
      Subsingleton (((Homology.smallSingularSimplices T F : SSet).chainComplex R).homology k) := by
    let e := Homology.smallChainHomologyIso T F R hopen hcov k
    refine ⟨fun a b => (ModuleCat.mono_iff_injective e.hom).mp inferInstance ?_⟩
    exact hk.elim _ _
  let _ : _root_.CategoryTheory.Mono (Homology.subspaceInclusion T
      (show U ∩ V ⊆ U from _root_.Set.inter_subset_left)) :=
    (TopCat.mono_iff_injective _).mpr (_root_.Set.inclusion_injective _root_.Set.inter_subset_left)
  let _ : _root_.CategoryTheory.Mono (SSet.chainComplexMap (TopCat.toSSet.map
      (Homology.subspaceInclusion T (show U ∩ V ⊆ U from _root_.Set.inter_subset_left))) R) := by
    unfold SSet.chainComplexMap
    infer_instance
  exact DifferentialGeometry.HomologicalComplex.bijective_homologyMap_pair_of_pushout
    (Homology.subspaceSmallChainSquare T U V R) (n + 1) n rfl (hsmall (n + 1) hn') (hsmall n hn)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.bijective_integralSingularHomologyMap_intersection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.bijective_integralSingularHomologyMap_intersection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.bijective_integralSingularHomologyMap_intersection ``Submission.DifferentialGeometry.Topology.bijective_integralSingularHomologyMap_intersection

end DifferentialGeometry.Topology
