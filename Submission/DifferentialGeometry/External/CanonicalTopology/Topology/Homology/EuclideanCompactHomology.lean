import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.LocalStarConvex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Sets.Compacts

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
noncomputable section

open _root_.Set

universe u

namespace DifferentialGeometry.Topology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem bounded_star_convex_local_class_restrict
    (n : ℕ) {p : E} {K L : Set E}
    (hpK : p ∈ K) (hsK : StarConvex ℝ p K) (hbK : Bornology.IsBounded K)
    (hpL : p ∈ L) (hsL : StarConvex ℝ p L) (hbL : Bornology.IsBounded L)
    (hKL : K ⊆ L) (a : integralLocalHomology n p) :
    integralRelativeHomologyMap n (ContinuousMap.id E)
        (show _root_.Set.MapsTo (ContinuousMap.id E) Lᶜ Kᶜ from compl_subset_compl.mpr hKL)
        ((integralBoundedStarConvexLocalHomologyIso n hpL hsL hbL).toLinearEquiv.symm a) =
      (integralBoundedStarConvexLocalHomologyIso n hpK hsK hbK).toLinearEquiv.symm a := by
  let eK := (integralBoundedStarConvexLocalHomologyIso n hpK hsK hbK).toLinearEquiv
  let eL := (integralBoundedStarConvexLocalHomologyIso n hpL hsL hbL).toLinearEquiv
  apply eK.injective
  have hcomp := LinearMap.congr_fun (integralRelativeHomologyMap_comp n
    (ContinuousMap.id E) (ContinuousMap.id E)
    (show _root_.Set.MapsTo (ContinuousMap.id E) Lᶜ Kᶜ from compl_subset_compl.mpr hKL)
    (show _root_.Set.MapsTo (ContinuousMap.id E) Kᶜ ({p}ᶜ : Set E) from
      compl_subset_compl.mpr (singleton_subset_iff.mpr hpK))) (eL.symm a)
  exact hcomp.symm.trans ((eL.apply_symm_apply a).trans (eK.apply_symm_apply a).symm)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.bounded_star_convex_local_class_restrict
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.bounded_star_convex_local_class_restrict target :: scope.openDecls } }

private theorem bounded_star_convex_local_class_independent
    (n : ℕ) {p : E} {S K L : Set E}
    (hpK : p ∈ K) (hsK : StarConvex ℝ p K) (hbK : Bornology.IsBounded K)
    (hpL : p ∈ L) (hsL : StarConvex ℝ p L) (hbL : Bornology.IsBounded L)
    (hSK : S ⊆ K) (hSL : S ⊆ L) (a : integralLocalHomology n p) :
    integralRelativeHomologyMap n (ContinuousMap.id E)
        (show _root_.Set.MapsTo (ContinuousMap.id E) Kᶜ Sᶜ from compl_subset_compl.mpr hSK)
        ((integralBoundedStarConvexLocalHomologyIso n hpK hsK hbK).toLinearEquiv.symm a) =
      integralRelativeHomologyMap n (ContinuousMap.id E)
        (show _root_.Set.MapsTo (ContinuousMap.id E) Lᶜ Sᶜ from compl_subset_compl.mpr hSL)
        ((integralBoundedStarConvexLocalHomologyIso n hpL hsL hbL).toLinearEquiv.symm a) := by
  let b := (integralBoundedStarConvexLocalHomologyIso n (K := K ∪ L) (c := p)
    (Or.inl hpK : p ∈ K ∪ L)
    (hsK.union hsL) (hbK.union hbL)).toLinearEquiv.symm a
  have hK := bounded_star_convex_local_class_restrict n hpK hsK hbK
    (Or.inl hpK : p ∈ K ∪ L) (hsK.union hsL) (hbK.union hbL) _root_.Set.subset_union_left a
  have hL := bounded_star_convex_local_class_restrict n hpL hsL hbL
    (Or.inl hpK : p ∈ K ∪ L) (hsK.union hsL) (hbK.union hbL) _root_.Set.subset_union_right a
  have hcompK := LinearMap.congr_fun (integralRelativeHomologyMap_comp n
    (ContinuousMap.id E) (ContinuousMap.id E)
    (show _root_.Set.MapsTo (ContinuousMap.id E) (K ∪ L)ᶜ Kᶜ from
      compl_subset_compl.mpr _root_.Set.subset_union_left)
    (show _root_.Set.MapsTo (ContinuousMap.id E) Kᶜ Sᶜ from compl_subset_compl.mpr hSK)) b
  have hcompL := LinearMap.congr_fun (integralRelativeHomologyMap_comp n
    (ContinuousMap.id E) (ContinuousMap.id E)
    (show _root_.Set.MapsTo (ContinuousMap.id E) (K ∪ L)ᶜ Lᶜ from
      compl_subset_compl.mpr _root_.Set.subset_union_right)
    (show _root_.Set.MapsTo (ContinuousMap.id E) Lᶜ Sᶜ from compl_subset_compl.mpr hSL)) b
  simp only [LinearMap.comp_apply] at hcompK hcompL
  rw [hK] at hcompK
  rw [hL] at hcompL
  exact hcompK.symm.trans hcompL

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.bounded_star_convex_local_class_independent
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.bounded_star_convex_local_class_independent target :: scope.openDecls } }

end DifferentialGeometry.Topology

end

noncomputable section

open _root_.TopologicalSpace _root_.Set _root_.Metric

universe u

namespace DifferentialGeometry.Topology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

private theorem exists_compact_star_convex_superset (p : E) (K : _root_.TopologicalSpace.Compacts E) :
    ∃ L : _root_.TopologicalSpace.Compacts E, K ≤ L ∧ p ∈ (L : Set E) ∧ StarConvex ℝ p (L : Set E) := by
  obtain ⟨r, hr, hKr⟩ := K.isCompact.isBounded.subset_closedBall_lt 0 p
  have hp : p ∈ _root_.Metric.closedBall p r := _root_.Metric.mem_closedBall_self hr.le
  exact ⟨⟨closedBall p r, _root_.ProperSpace.isCompact_closedBall p r⟩, hKr, hp,
    (convex_closedBall p r).starConvex hp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.exists_compact_star_convex_superset
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.exists_compact_star_convex_superset target :: scope.openDecls } }

theorem exists_unique_compact_homology_family_of_local_class
    (n : ℕ) (p : E) (a : integralLocalHomology n p) :
    ∃! c : ∀ K : _root_.TopologicalSpace.Compacts E, integralRelativeHomology n (K : Set E)ᶜ,
      (∀ (K L : _root_.TopologicalSpace.Compacts E) (h : K ≤ L),
        integralRelativeHomologyMap n (ContinuousMap.id E)
          (show _root_.Set.MapsTo (ContinuousMap.id E) (L : Set E)ᶜ (K : Set E)ᶜ from
            compl_subset_compl.mpr h) (c L) = c K) ∧ c {p} = a := by
  choose L hKL hpL hsL using exists_compact_star_convex_superset p
  let e (K : _root_.TopologicalSpace.Compacts E) := (integralBoundedStarConvexLocalHomologyIso n
    (hpL K) (hsL K) (L K).isCompact.isBounded).toLinearEquiv
  let c (K : _root_.TopologicalSpace.Compacts E) : integralRelativeHomology n (K : Set E)ᶜ :=
    integralRelativeHomologyMap n (ContinuousMap.id E)
      (show _root_.Set.MapsTo (ContinuousMap.id E) (L K : Set E)ᶜ (K : Set E)ᶜ from
        compl_subset_compl.mpr (hKL K)) ((e K).symm a)
  refine ⟨c, ⟨?_, ?_⟩, ?_⟩
  · intro K J hKJ
    have hcomp := LinearMap.congr_fun (integralRelativeHomologyMap_comp n
      (ContinuousMap.id E) (ContinuousMap.id E)
      (show _root_.Set.MapsTo (ContinuousMap.id E) (L J : Set E)ᶜ (J : Set E)ᶜ from
        compl_subset_compl.mpr (hKL J))
      (show _root_.Set.MapsTo (ContinuousMap.id E) (J : Set E)ᶜ (K : Set E)ᶜ from
        compl_subset_compl.mpr hKJ)) ((e J).symm a)
    have hind := bounded_star_convex_local_class_independent n
      (hpL J) (hsL J) (L J).isCompact.isBounded
      (hpL K) (hsL K) (L K).isCompact.isBounded
      (hKJ.trans (hKL J)) (hKL K) a
    exact hcomp.symm.trans hind
  · exact (e {p}).apply_symm_apply a
  · intro d hd
    funext K
    have hdp : (e K) (d (L K)) = a :=
      (hd.1 {p} (L K) (singleton_subset_iff.mpr (hpL K))).trans hd.2
    have hdL : d (L K) = (e K).symm a :=
      (e K).injective (hdp.trans ((e K).apply_symm_apply a).symm)
    exact (hd.1 K (L K) (hKL K)).symm.trans
      (congrArg (integralRelativeHomologyMap n (ContinuousMap.id E)
        (show _root_.Set.MapsTo (ContinuousMap.id E) (L K : Set E)ᶜ (K : Set E)ᶜ from
          compl_subset_compl.mpr (hKL K))) hdL)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_unique_compact_homology_family_of_local_class then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_unique_compact_homology_family_of_local_class"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_unique_compact_homology_family_of_local_class ``Submission.DifferentialGeometry.Topology.exists_unique_compact_homology_family_of_local_class

end DifferentialGeometry.Topology

end
