import Submission.DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.DoubleCylinderMappingTorus

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Function
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology.DoubleCylinder

private abbrev IC := (𝓡 2).prod 𝓘(ℝ, ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.DoubleCylinder.IC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.DoubleCylinder.IC target :: scope.openDecls } }

abbrev Interior := sphereMappingTorusInteriorDomain

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.DoubleCylinder.Interior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.DoubleCylinder.Interior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.DoubleCylinder.Interior ``Submission.DifferentialGeometry.Topology.DoubleCylinder.Interior

def interiorCore (f : SphereTwo ≃ₘ⟮𝓡 2, 𝓡 2⟯ SphereTwo) (p : Interior) : Space f :=
  core f (p.val.1, ⟨p.val.2, p.property.2.1.le, p.property.2.2.le⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.DoubleCylinder.interiorCore then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.DoubleCylinder.interiorCore"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.DoubleCylinder.interiorCore ``Submission.DifferentialGeometry.Topology.DoubleCylinder.interiorCore

def interiorBand (f : SphereTwo ≃ₘ⟮𝓡 2, 𝓡 2⟯ SphereTwo) (p : Interior) : Space f :=
  band f (p.val.1, ⟨p.val.2, p.property.2.1.le, p.property.2.2.le⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.DoubleCylinder.interiorBand then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.DoubleCylinder.interiorBand"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.DoubleCylinder.interiorBand ``Submission.DifferentialGeometry.Topology.DoubleCylinder.interiorBand

private def halfParameter (p : Interior) : sphereMappingTorusInteriorDomain :=
  ⟨(p.val.1, p.val.2 / 2), _root_.Set.mem_univ _, by constructor <;> linarith [p.property.2.1, p.property.2.2]⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.DoubleCylinder.halfParameter
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.DoubleCylinder.halfParameter target :: scope.openDecls } }

private def reverseParameter (f : SphereTwo ≃ₘ⟮𝓡 2, 𝓡 2⟯ SphereTwo)
    (p : Interior) : sphereMappingTorusInteriorDomain :=
  ⟨(f.symm p.val.1, 1 - p.val.2 / 2), _root_.Set.mem_univ _,
    by constructor <;> linarith [p.property.2.1, p.property.2.2]⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.DoubleCylinder.reverseParameter
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.DoubleCylinder.reverseParameter target :: scope.openDecls } }

private def halfDiffeomorph : Diffeomorph IC IC (SphereTwo × ℝ) (SphereTwo × ℝ) ∞ where
  toFun p := (p.1, p.2 / 2)
  invFun p := (p.1, 2 * p.2)
  left_inv p := by refine Prod.ext rfl ?_; dsimp; ring
  right_inv p := by refine Prod.ext rfl ?_; dsimp; ring
  contMDiff_toFun := contMDiff_fst.prodMk (contMDiff_snd.div_const 2)
  contMDiff_invFun := contMDiff_fst.prodMk (contMDiff_const.mul contMDiff_snd)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.DoubleCylinder.halfDiffeomorph
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.DoubleCylinder.halfDiffeomorph target :: scope.openDecls } }

private def reverseDiffeomorph (f : SphereTwo ≃ₘ⟮𝓡 2, 𝓡 2⟯ SphereTwo) :
    Diffeomorph IC IC (SphereTwo × ℝ) (SphereTwo × ℝ) ∞ where
  toFun p := (f.symm p.1, 1 - p.2 / 2)
  invFun p := (f p.1, 2 - 2 * p.2)
  left_inv p := by refine Prod.ext (f.apply_symm_apply _) ?_; dsimp; ring
  right_inv p := by refine Prod.ext (f.symm_apply_apply _) ?_; dsimp; ring
  contMDiff_toFun := (f.symm.contMDiff.comp contMDiff_fst).prodMk
    (contMDiff_const.sub (contMDiff_snd.div_const 2))
  contMDiff_invFun := (f.contMDiff.comp contMDiff_fst).prodMk
    (contMDiff_const.sub (contMDiff_const.mul contMDiff_snd))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.DoubleCylinder.reverseDiffeomorph
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.DoubleCylinder.reverseDiffeomorph target :: scope.openDecls } }

private theorem halfParameter_isLocalDiffeomorph : IsLocalDiffeomorph IC IC ∞ halfParameter := by
  have hloc := DifferentialGeometry.isLocalDiffeomorph_restrict_open Interior
    (halfDiffeomorph.isLocalDiffeomorph.isLocalDiffeomorphOn Interior)
  intro p
  exact DifferentialGeometry.isLocalDiffeomorphAt_subtypeCodRestrict
    (fun q : Interior => (halfParameter q).property) (hloc p)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.DoubleCylinder.halfParameter_isLocalDiffeomorph
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.DoubleCylinder.halfParameter_isLocalDiffeomorph target :: scope.openDecls } }

private theorem reverseParameter_isLocalDiffeomorph
    (f : SphereTwo ≃ₘ⟮𝓡 2, 𝓡 2⟯ SphereTwo) : IsLocalDiffeomorph IC IC ∞ (reverseParameter f) := by
  have hloc := DifferentialGeometry.isLocalDiffeomorph_restrict_open Interior
    ((reverseDiffeomorph f).isLocalDiffeomorph.isLocalDiffeomorphOn Interior)
  intro p
  exact DifferentialGeometry.isLocalDiffeomorphAt_subtypeCodRestrict
    (fun q : Interior => (reverseParameter f q).property) (hloc p)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.DoubleCylinder.reverseParameter_isLocalDiffeomorph
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.DoubleCylinder.reverseParameter_isLocalDiffeomorph target :: scope.openDecls } }

theorem interiorCore_isLocalDiffeomorph (D : SphereMappingTorusIsotopy)
    (hD : ContMDiff IC (𝓡 2) ∞ (fun p : SphereTwo × ℝ => D.isotopy p.2 p.1))
    (hDi : ContMDiff IC (𝓡 2) ∞ (fun p : SphereTwo × ℝ => (D.isotopy p.2).symm p.1)) :
    let _ := sphereMappingTorusChartedSpace D.flatten
    let _ := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace
      (H := ModelProd (EuclideanSpace ℝ (Fin 2)) ℝ) (mappingTorusHomeomorph D.target)
    IsLocalDiffeomorph IC IC ∞ (interiorCore D.target) := by
  let _ := sphereMappingTorusChartedSpace D.flatten
  let _ := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace
    (H := ModelProd (EuclideanSpace ℝ (Fin 2)) ℝ) (mappingTorusHomeomorph D.target)
  have h := DifferentialGeometry.isLocalDiffeomorph_comp
    (DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph
      (I := IC) (n := ∞) (mappingTorusHomeomorph D.target)).symm.isLocalDiffeomorph
    (DifferentialGeometry.isLocalDiffeomorph_comp
      (sphereMappingTorusInterior_isLocalDiffeomorph D.flatten
        (D.contMDiff_flatten_apply hD) (D.contMDiff_flatten_symm_apply hDi))
      halfParameter_isLocalDiffeomorph)
  have heq : (DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph
      (I := IC) (n := ∞) (mappingTorusHomeomorph D.target)).symm ∘
      (sphereMappingTorusInterior D.target ∘ halfParameter) = interiorCore D.target := by
    funext p
    apply (mappingTorusHomeomorph D.target).injective
    change mappingTorusHomeomorph D.target ((mappingTorusHomeomorph D.target).symm _) = _
    rw [Homeomorph.apply_symm_apply]
    rfl
  rw [heq] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.DoubleCylinder.interiorCore_isLocalDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.DoubleCylinder.interiorCore_isLocalDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.DoubleCylinder.interiorCore_isLocalDiffeomorph ``Submission.DifferentialGeometry.Topology.DoubleCylinder.interiorCore_isLocalDiffeomorph

theorem interiorBand_isLocalDiffeomorph (D : SphereMappingTorusIsotopy)
    (hD : ContMDiff IC (𝓡 2) ∞ (fun p : SphereTwo × ℝ => D.isotopy p.2 p.1))
    (hDi : ContMDiff IC (𝓡 2) ∞ (fun p : SphereTwo × ℝ => (D.isotopy p.2).symm p.1)) :
    let _ := sphereMappingTorusChartedSpace D.flatten
    let _ := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace
      (H := ModelProd (EuclideanSpace ℝ (Fin 2)) ℝ) (mappingTorusHomeomorph D.target)
    IsLocalDiffeomorph IC IC ∞ (interiorBand D.target) := by
  let _ := sphereMappingTorusChartedSpace D.flatten
  let _ := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace
    (H := ModelProd (EuclideanSpace ℝ (Fin 2)) ℝ) (mappingTorusHomeomorph D.target)
  have h := DifferentialGeometry.isLocalDiffeomorph_comp
    (DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph
      (I := IC) (n := ∞) (mappingTorusHomeomorph D.target)).symm.isLocalDiffeomorph
    (DifferentialGeometry.isLocalDiffeomorph_comp
      (sphereMappingTorusInterior_isLocalDiffeomorph D.flatten
        (D.contMDiff_flatten_apply hD) (D.contMDiff_flatten_symm_apply hDi))
      (reverseParameter_isLocalDiffeomorph D.target))
  have heq : (DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph
      (I := IC) (n := ∞) (mappingTorusHomeomorph D.target)).symm ∘
      (sphereMappingTorusInterior D.target ∘ reverseParameter D.target) = interiorBand D.target := by
    funext p
    apply (mappingTorusHomeomorph D.target).injective
    change mappingTorusHomeomorph D.target ((mappingTorusHomeomorph D.target).symm _) = _
    rw [Homeomorph.apply_symm_apply]
    rfl
  rw [heq] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.DoubleCylinder.interiorBand_isLocalDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.DoubleCylinder.interiorBand_isLocalDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.DoubleCylinder.interiorBand_isLocalDiffeomorph ``Submission.DifferentialGeometry.Topology.DoubleCylinder.interiorBand_isLocalDiffeomorph

end DifferentialGeometry.Topology.DoubleCylinder
