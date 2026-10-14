import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.EuclideanLocalCapDuality
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.RelativeEmpty
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.ConnectedZeroCohomology
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Algebra.Module.Pairing
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.OneDimensionalLocalCapDuality

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
noncomputable section

open _root_.CategoryTheory _root_.Metric _root_.Module _root_.Set

universe u

namespace DifferentialGeometry.Topology

private theorem exists_innerProduct_local_top_cap_bijective
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] :
    ∃ c : integralLocalHomology (_root_.Module.finrank ℝ E) (0 : E),
      Function.Bijective (fun α : integralRelativeCohomology (_root_.Module.finrank ℝ E)
          ({0}ᶜ : Set E) =>
        integralRelativeCohomologyCapToAbsolute ({0}ᶜ : Set E) (_root_.Module.finrank ℝ E) 0 α c) := by
  by_cases hlarge : 2 ≤ _root_.Module.finrank ℝ E
  · have hd : _root_.Module.finrank ℝ E = (_root_.Module.finrank ℝ E - 2) + 2 := by omega
    rw [hd]
    exact ⟨(integralEuclideanLocalTopZeroEquiv E (_root_.Module.finrank ℝ E - 2) hd).symm 1,
      integralEuclideanLocalTopZeroEquiv_cap_bijective (_root_.Module.finrank ℝ E - 2) E hd⟩
  by_cases hzero : _root_.Module.finrank ℝ E = 0
  · have hempty : ({0}ᶜ : Set E) = ∅ := by
      ext x
      constructor
      · intro hx
        exact (hx (finrank_zero_iff_forall_zero.mp hzero x)).elim
      · intro hx
        exact hx.elim
    change ∃ c : integralRelativeHomology (_root_.Module.finrank ℝ E) ({0}ᶜ : Set E),
      Function.Bijective (fun α : integralRelativeCohomology (_root_.Module.finrank ℝ E)
          ({0}ᶜ : Set E) =>
        integralRelativeCohomologyCapToAbsolute ({0}ᶜ : Set E) (_root_.Module.finrank ℝ E) 0 α c)
    rw [hzero, hempty]
    let e := integralSingularHomologyZeroEquiv (X := E)
    let c := e.symm 1
    have hc : Function.Bijective (fun z : ℤ => z • c) := by
      have hfun : (fun z : ℤ => z • c) = e.symm := by
        funext z
        change z • e.symm 1 = e.symm z
        rw [← map_zsmul]
        congr 1
        exact mul_one z
      rw [hfun]
      exact e.symm.bijective
    have hcap : Function.Bijective (fun α : integralSingularCohomology 0 E =>
        integralSingularCohomologyCapProduct 0 0 α c) :=
      (integralSingularCohomologyCapProduct_zero_bijective_iff 0 c).mpr hc
    refine ⟨integralAbsoluteToRelative 0 (∅ : Set E) c, ?_⟩
    have hfun : (fun α : integralRelativeCohomology 0 (∅ : Set E) =>
        integralRelativeCohomologyCapToAbsolute (∅ : Set E) 0 0 α
          (integralAbsoluteToRelative 0 (∅ : Set E) c)) =
        (fun α : integralSingularCohomology 0 E =>
          integralSingularCohomologyCapProduct 0 0 α c) ∘
            integralRelativeToAbsoluteCohomology 0 (∅ : Set E) := by
      funext α
      exact integralRelativeCohomologyCapToAbsolute_absoluteToRelative (∅ : Set E) 0 0 α c
    rw [hfun]
    exact hcap.comp (integralRelativeToAbsoluteCohomologyEmptyEquiv 0 E).bijective
  have hone : _root_.Module.finrank ℝ E = 1 := by omega
  change ∃ c : integralRelativeHomology (_root_.Module.finrank ℝ E) ({0}ᶜ : Set E),
    Function.Bijective (fun α : integralRelativeCohomology (_root_.Module.finrank ℝ E)
        ({0}ᶜ : Set E) =>
      integralRelativeCohomologyCapToAbsolute ({0}ᶜ : Set E) (_root_.Module.finrank ℝ E) 0 α c)
  rw [hone]
  exact exists_integralLocalHomology_cap_bijective_of_finrank_one E hone

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.exists_innerProduct_local_top_cap_bijective
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.exists_innerProduct_local_top_cap_bijective target :: scope.openDecls } }

private theorem exists_normed_local_top_cap_bijective
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (p : E) :
    ∃ c : integralLocalHomology (_root_.Module.finrank ℝ E) p,
      Function.Bijective (fun α : integralRelativeCohomology (_root_.Module.finrank ℝ E)
          ({p}ᶜ : Set E) =>
        integralRelativeCohomologyCapToAbsolute ({p}ᶜ : Set E) (_root_.Module.finrank ℝ E) 0 α c) := by
  let ι := Module.Free.ChooseBasisIndex ℝ E
  let b : _root_.Module.Basis ι ℝ E := Module.Free.chooseBasis ℝ E
  let e : E ≃L[ℝ] EuclideanSpace ℝ ι :=
    b.equivFunL.trans (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm
  let h := e.symm.toHomeomorph.trans (Homeomorph.addRight p)
  have hp : h 0 = p := by
    change e.symm 0 + p = p
    rw [map_zero, zero_add]
  have hex : ∃ c : integralLocalHomology (_root_.Module.finrank ℝ E) (0 : EuclideanSpace ℝ ι),
      Function.Bijective (fun α : integralRelativeCohomology (_root_.Module.finrank ℝ E)
          ({0}ᶜ : Set (EuclideanSpace ℝ ι)) =>
        integralRelativeCohomologyCapToAbsolute ({0}ᶜ : Set (EuclideanSpace ℝ ι))
          (_root_.Module.finrank ℝ E) 0 α c) := by
    rw [e.toLinearEquiv.finrank_eq]
    exact exists_innerProduct_local_top_cap_bijective (EuclideanSpace ℝ ι)
  let f : ContinuousMap (EuclideanSpace ℝ ι) E := ⟨h, h.continuous⟩
  have hf : _root_.Set.MapsTo f ({0}ᶜ : Set (EuclideanSpace ℝ ι)) ({h 0}ᶜ : Set E) :=
    fun _ hx => h.injective.ne hx
  let g := h.subtype (p := fun x : EuclideanSpace ℝ ι => x ∈ ({0}ᶜ : Set (EuclideanSpace ℝ ι)))
    (q := fun y : E => y ∈ ({h 0}ᶜ : Set E)) (fun x => h.injective.ne_iff.symm)
  have hcoh : Function.Bijective (integralRelativeCohomologyMap (_root_.Module.finrank ℝ E) f hf) := by
    apply integralRelativeCohomologyMap_bijective_of_absolute_and_subspace
    · intro n
      exact integralSingularCohomologyMap_bijective_of_homotopyEquiv h.toHomotopyEquiv n
    · intro n
      exact integralSingularCohomologyMap_bijective_of_homotopyEquiv g.toHomotopyEquiv n
  obtain ⟨c, hc⟩ := hex
  have hcap := integralRelativeCohomologyCapToAbsolute_bijective_map (_root_.Module.finrank ℝ E) 0 f hf
    (integralSingularHomologyZeroMapEquiv f).bijective hcoh c hc
  have hout : ∃ d : integralLocalHomology (_root_.Module.finrank ℝ E) (h 0),
      Function.Bijective (fun α : integralRelativeCohomology (_root_.Module.finrank ℝ E)
          ({h 0}ᶜ : Set E) =>
        integralRelativeCohomologyCapToAbsolute ({h 0}ᶜ : Set E) (_root_.Module.finrank ℝ E) 0 α d) :=
    ⟨integralRelativeHomologyMap (_root_.Module.finrank ℝ E) f hf c, hcap⟩
  rwa [hp] at hout

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.exists_normed_local_top_cap_bijective
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.exists_normed_local_top_cap_bijective target :: scope.openDecls } }

theorem integralLocalHomology_cap_bijective_of_generator
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (p : E) (c : integralLocalHomology (_root_.Module.finrank ℝ E) p)
    (hc : Function.Bijective (fun z : ℤ => z • c)) :
    Function.Bijective (fun α : integralRelativeCohomology (_root_.Module.finrank ℝ E) ({p}ᶜ : Set E) =>
      integralRelativeCohomologyCapToAbsolute ({p}ᶜ : Set E) (_root_.Module.finrank ℝ E) 0 α c) := by
  let f : ℤ →+ integralLocalHomology (_root_.Module.finrank ℝ E) p :=
    { toFun := fun z => z • c
      map_zero' := zero_zsmul c
      map_add' := fun z w => add_zsmul c z w }
  let e := (AddEquiv.ofBijective f hc).symm
  have he : e.symm 1 = c := one_zsmul c
  obtain ⟨d, hd⟩ := exists_normed_local_top_cap_bijective p
  let B := fun α : integralRelativeCohomology (_root_.Module.finrank ℝ E) ({p}ᶜ : Set E) =>
    integralZeroAugmentation.toAddMonoidHom.comp
      ((integralRelativeCohomologyCapToAbsolute ({p}ᶜ : Set E) (_root_.Module.finrank ℝ E) 0 α).toAddMonoidHom)
  have hdB : Function.Bijective (fun α => B α d) :=
    integralConnectedZeroAugmentationEquiv.bijective.comp hd
  have h := additive_pairing_bijective_at_generator B e d hdB
  rw [he] at h
  exact (Function.Bijective.of_comp_iff' integralConnectedZeroAugmentationEquiv.bijective _).mp h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralLocalHomology_cap_bijective_of_generator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralLocalHomology_cap_bijective_of_generator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralLocalHomology_cap_bijective_of_generator ``Submission.DifferentialGeometry.Topology.integralLocalHomology_cap_bijective_of_generator

end DifferentialGeometry.Topology
