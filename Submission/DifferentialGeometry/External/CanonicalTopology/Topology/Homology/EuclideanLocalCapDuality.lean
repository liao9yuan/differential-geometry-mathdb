import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SphereCapDuality
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.EuclideanLocalTop
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.RelativeCapCohomologyConnecting
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.EuclideanLocalCohomologyVanishing

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

universe u

namespace DifferentialGeometry.Topology

section

open _root_.Set _root_.Metric

private theorem integralEuclideanLocalTopZeroEquiv_cap_top_bijective
    (n : ℕ) (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (hd : Module.finrank ℝ E = n + 2) :
    Function.Bijective (fun α : integralRelativeCohomology (n + 2) ({0}ᶜ : Set E) =>
      integralRelativeCohomologyCapToAbsolute ({0}ᶜ : Set E) (n + 2) 0 α
        ((integralEuclideanLocalTopZeroEquiv E n hd).symm 1)) := by
  let _ := unitSphere_pathConnected_of_finrank (E := E) (by omega)
  let A : Set E := {0}ᶜ
  let e := puncturedSpaceSphereHomotopyEquiv E
  let c := (integralEuclideanLocalTopZeroEquiv E n hd).symm 1
  let s := (integralSphereTopHomologyEquiv n E hd).symm 1
  have hc : integralSingularHomologyMap (n + 1) e.toFun
      (integralRelativeConnecting (n + 1) A c) = s := by
    apply (integralSphereTopHomologyEquiv n E hd).injective
    change integralEuclideanLocalTopZeroEquiv E n hd c =
      integralSphereTopHomologyEquiv n E hd s
    rw [(integralEuclideanLocalTopZeroEquiv E n hd).apply_symm_apply,
      (integralSphereTopHomologyEquiv n E hd).apply_symm_apply]
  let f := fun α : integralRelativeCohomology (n + 2) A =>
    integralRelativeCohomologyCapToAbsolute A (n + 2) 0 α c
  let h := integralRelativeCohomologyConnecting (n + 1) A ∘
    integralSingularCohomologyMap (n + 1) e.toFun
  have hh : Function.Bijective h :=
    (integralRelativeCohomologyConnecting_bijective_of_contractibleSpace
      (n + 1) (by omega) A).comp
      (integralSingularCohomologyMap_bijective_of_homotopyEquiv e (n + 1))
  have heq : (fun α => integralZeroAugmentation (f α)) ∘ h =
      fun β : integralSingularCohomology (n + 1) (_root_.Metric.sphere (0 : E) 1) =>
        integralZeroAugmentation (integralSingularCohomologyCapProduct (n + 1) 0 β s) := by
    funext β
    have hcap := integralRelativeCohomologyCapToAbsolute_connecting A (n + 1) 0
      (integralSingularCohomologyMap (n + 1) e.toFun β) c
    change f (h β) = integralSingularHomologyMap 0 (singularSubspaceInclusion A)
      (integralSingularCohomologyCapProduct (n + 1) 0
        (integralSingularCohomologyMap (n + 1) e.toFun β)
        (integralRelativeConnecting (n + 1) A c)) at hcap
    change integralZeroAugmentation (f (h β)) = _
    rw [hcap]
    calc
      _ = integralZeroAugmentation (integralSingularCohomologyCapProduct (n + 1) 0
          (integralSingularCohomologyMap (n + 1) e.toFun β)
          (integralRelativeConnecting (n + 1) A c)) :=
        LinearMap.congr_fun (integralZeroAugmentation_natural (singularSubspaceInclusion A)) _
      _ = integralZeroAugmentation (integralSingularHomologyMap 0 e.toFun
          (integralSingularCohomologyCapProduct (n + 1) 0
            (integralSingularCohomologyMap (n + 1) e.toFun β)
            (integralRelativeConnecting (n + 1) A c))) :=
        (LinearMap.congr_fun (integralZeroAugmentation_natural e.toFun) _).symm
      _ = _ := by
        rw [integralSingularCohomologyCapProduct_natural]
        change integralZeroAugmentation (integralSingularCohomologyCapProduct (n + 1) 0 β
          (integralSingularHomologyMap (n + 1) e.toFun
            (integralRelativeConnecting (n + 1) A c))) = _
        rw [hc]
  have hb : Function.Bijective ((fun α => integralZeroAugmentation (f α)) ∘ h) := by
    rw [heq]
    exact integralConnectedZeroAugmentationEquiv.bijective.comp
      (integralSphereTopHomologyEquiv_cap_bijective n E hd)
  have hf := (Function.Bijective.of_comp_iff (fun α => integralZeroAugmentation (f α)) hh).mp hb
  exact (Function.Bijective.of_comp_iff' integralConnectedZeroAugmentationEquiv.bijective f).mp hf

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.integralEuclideanLocalTopZeroEquiv_cap_top_bijective
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.integralEuclideanLocalTopZeroEquiv_cap_top_bijective target :: scope.openDecls } }

end

section

open _root_.Set

private theorem integralBoundedStarConvexLocalHomologyIso_cap_top_bijective
    (n : ℕ) (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (hd : Module.finrank ℝ E = n + 2)
    {K : Set E} (h0 : (0 : E) ∈ K) (hs : StarConvex ℝ 0 K) (hK : Bornology.IsBounded K) :
    Function.Bijective (fun α : integralRelativeCohomology (n + 2) Kᶜ =>
      integralRelativeCohomologyCapToAbsolute Kᶜ (n + 2) 0 α
        ((integralBoundedStarConvexLocalHomologyIso (n + 2) h0 hs hK).toLinearEquiv.symm
          ((integralEuclideanLocalTopZeroEquiv E n hd).symm 1))) := by
  let hf : _root_.Set.MapsTo (ContinuousMap.id E) Kᶜ ({0}ᶜ : Set E) :=
    compl_subset_compl.mpr (singleton_subset_iff.mpr h0)
  have hcoh : Function.Bijective
      (integralRelativeCohomologyMap (n + 2) (ContinuousMap.id E) hf) :=
    integralRelativeCohomologyMap_boundedStarConvex_bijective (n + 2) h0 hs hK
  let i := (integralBoundedStarConvexLocalHomologyIso (n + 2) h0 hs hK).toLinearEquiv
  let c0 := (integralEuclideanLocalTopZeroEquiv E n hd).symm 1
  let c := i.symm c0
  have hc : integralRelativeHomologyMap (n + 2) (ContinuousMap.id E) hf c = c0 := by
    change i c = c0
    exact i.apply_symm_apply c0
  let f := fun α : integralRelativeCohomology (n + 2) Kᶜ =>
    integralRelativeCohomologyCapToAbsolute Kᶜ (n + 2) 0 α c
  have hcap : f ∘ integralRelativeCohomologyMap (n + 2) (ContinuousMap.id E) hf =
      fun β : integralRelativeCohomology (n + 2) ({0}ᶜ : Set E) =>
        integralRelativeCohomologyCapToAbsolute ({0}ᶜ : Set E) (n + 2) 0 β c0 := by
    funext β
    have hn := integralRelativeCohomologyCapToAbsolute_natural (n + 2) 0
      (ContinuousMap.id E) hf β c
    rw [integralSingularHomologyMap_id] at hn
    change f (integralRelativeCohomologyMap (n + 2) (ContinuousMap.id E) hf β) =
      integralRelativeCohomologyCapToAbsolute ({0}ᶜ : Set E) (n + 2) 0 β
        (integralRelativeHomologyMap (n + 2) (ContinuousMap.id E) hf c) at hn
    rw [hc] at hn
    exact hn
  apply (Function.Bijective.of_comp_iff f hcoh).mp
  rw [hcap]
  exact integralEuclideanLocalTopZeroEquiv_cap_top_bijective n E hd

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.integralBoundedStarConvexLocalHomologyIso_cap_top_bijective
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.integralBoundedStarConvexLocalHomologyIso_cap_top_bijective target :: scope.openDecls } }

end

section

open _root_.CategoryTheory _root_.Metric _root_.Module _root_.Set

theorem integralEuclideanLocalTopZeroEquiv_cap_bijective_of_add_eq
    (n k m : ℕ) (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (hd : _root_.Module.finrank ℝ E = n + 2) (hkm : k + m = n + 2) :
    Function.Bijective (fun α : integralRelativeCohomology k ({0}ᶜ : Set E) =>
      integralRelativeCohomologyCapToAbsolute ({0}ᶜ : Set E) k m α
        ((_root_.CategoryTheory.eqToHom (congrArg (fun j => integralRelativeHomology j ({0}ᶜ : Set E)) hkm.symm))
          ((integralEuclideanLocalTopZeroEquiv E n hd).symm 1))) := by
  by_cases hm : m = 0
  · subst m
    have hk : k = n + 2 := by omega
    subst k
    exact integralEuclideanLocalTopZeroEquiv_cap_top_bijective n E hd
  let _ := integralEuclideanRelativeCohomology_subsingleton n k E hd (by omega)
  let _ := integralSingularHomology_subsingleton_of_contractible m hm E
  exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun β => ⟨0, Subsingleton.elim _ β⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralEuclideanLocalTopZeroEquiv_cap_bijective_of_add_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralEuclideanLocalTopZeroEquiv_cap_bijective_of_add_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralEuclideanLocalTopZeroEquiv_cap_bijective_of_add_eq ``Submission.DifferentialGeometry.Topology.integralEuclideanLocalTopZeroEquiv_cap_bijective_of_add_eq

theorem integralBoundedStarConvexLocalHomologyIso_cap_bijective_of_add_eq
    (n k m : ℕ) (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (hd : _root_.Module.finrank ℝ E = n + 2) (hkm : k + m = n + 2)
    {K : Set E} (h0 : (0 : E) ∈ K) (hs : StarConvex ℝ 0 K) (hK : Bornology.IsBounded K) :
    Function.Bijective (fun α : integralRelativeCohomology k Kᶜ =>
      integralRelativeCohomologyCapToAbsolute Kᶜ k m α
        ((_root_.CategoryTheory.eqToHom (congrArg (fun j => integralRelativeHomology j Kᶜ) hkm.symm))
          ((integralBoundedStarConvexLocalHomologyIso (n + 2) h0 hs hK).toLinearEquiv.symm
            ((integralEuclideanLocalTopZeroEquiv E n hd).symm 1)))) := by
  by_cases hm : m = 0
  · subst m
    have hk : k = n + 2 := by omega
    subst k
    exact integralBoundedStarConvexLocalHomologyIso_cap_top_bijective n E hd h0 hs hK
  let _ := integralBoundedStarConvexRelativeCohomology_subsingleton n k E hd (by omega) h0 hs hK
  let _ := integralSingularHomology_subsingleton_of_contractible m hm E
  exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun β => ⟨0, Subsingleton.elim _ β⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralBoundedStarConvexLocalHomologyIso_cap_bijective_of_add_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralBoundedStarConvexLocalHomologyIso_cap_bijective_of_add_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralBoundedStarConvexLocalHomologyIso_cap_bijective_of_add_eq ``Submission.DifferentialGeometry.Topology.integralBoundedStarConvexLocalHomologyIso_cap_bijective_of_add_eq

end

theorem integralEuclideanLocalTopZeroEquiv_cap_bijective
    (n : ℕ) (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (hd : Module.finrank ℝ E = n + 2) :
    Function.Bijective (fun α : integralRelativeCohomology (n + 2) ({0}ᶜ : Set E) =>
      integralRelativeCohomologyCapToAbsolute ({0}ᶜ : Set E) (n + 2) 0 α
        ((integralEuclideanLocalTopZeroEquiv E n hd).symm 1)) :=
  integralEuclideanLocalTopZeroEquiv_cap_bijective_of_add_eq n (n + 2) 0 E hd rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralEuclideanLocalTopZeroEquiv_cap_bijective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralEuclideanLocalTopZeroEquiv_cap_bijective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralEuclideanLocalTopZeroEquiv_cap_bijective ``Submission.DifferentialGeometry.Topology.integralEuclideanLocalTopZeroEquiv_cap_bijective

theorem integralBoundedStarConvexLocalHomologyIso_cap_bijective
    (n : ℕ) (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (hd : Module.finrank ℝ E = n + 2)
    {K : Set E} (h0 : (0 : E) ∈ K) (hs : StarConvex ℝ 0 K) (hK : Bornology.IsBounded K) :
    Function.Bijective (fun α : integralRelativeCohomology (n + 2) Kᶜ =>
      integralRelativeCohomologyCapToAbsolute Kᶜ (n + 2) 0 α
        ((integralBoundedStarConvexLocalHomologyIso (n + 2) h0 hs hK).toLinearEquiv.symm
          ((integralEuclideanLocalTopZeroEquiv E n hd).symm 1))) :=
  integralBoundedStarConvexLocalHomologyIso_cap_bijective_of_add_eq n (n + 2) 0 E hd rfl h0 hs hK

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralBoundedStarConvexLocalHomologyIso_cap_bijective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralBoundedStarConvexLocalHomologyIso_cap_bijective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralBoundedStarConvexLocalHomologyIso_cap_bijective ``Submission.DifferentialGeometry.Topology.integralBoundedStarConvexLocalHomologyIso_cap_bijective

end DifferentialGeometry.Topology

end
