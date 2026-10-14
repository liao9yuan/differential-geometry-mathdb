import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildCoreDeformationRetract
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutCapTransitionSkeleton
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Connected.TotallyDisconnected

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Topology _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ContinuousMap _root_.unitInterval

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace TubeSystem

section Retraction

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] (T : TubeSystem M)

local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.instFactLtRealNegOfNat_2 : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.instFactLtRealNegOfNat_2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.instFactLtRealNegOfNat_2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.instFactLtRealNegOfNat_2 ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.instFactLtRealNegOfNat_2

def coreInclusion : C(↥T.core, ↥T.puncturedCore) where
  toFun x := ⟨x.1, T.core_subset_puncturedCore x.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.coreInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.coreInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.coreInclusion ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.coreInclusion

def coreRetraction
    (hsm : ∀ a : T.Index, _root_.Manifold.IsSmoothEmbedding ((𝓡 2).prod (𝓡∂ 1)) ThreeModel ∞ (T.tube a)) :
    C(↥T.puncturedCore, ↥T.core) where
  toFun u := ⟨T.coreFun ((1 : I), (u : M)),
    T.coreFun_mem_core (p := ((1 : I), (u : M))) u.2⟩
  continuous_toFun := by
    have hpair : Continuous fun u : ↥T.puncturedCore => ((1 : I), u) :=
      (continuous_const : Continuous fun _ : ↥T.puncturedCore => (1 : I)).prodMk
        (continuous_id : Continuous fun u : ↥T.puncturedCore => u)
    have hmain : Continuous fun u : ↥T.puncturedCore => T.coreFun ((1 : I), (u : M)) :=
      Continuous.comp
        (g := fun p : I × ↥T.puncturedCore => T.coreFun (p.1, (p.2 : M)))
        (f := fun u : ↥T.puncturedCore => ((1 : I), u))
        (T.continuous_coreFun hsm) hpair
    exact hmain.subtype_mk _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.coreRetraction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.coreRetraction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.coreRetraction ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.coreRetraction

theorem coreRetraction_comp_coreInclusion
    (hsm : ∀ a : T.Index, _root_.Manifold.IsSmoothEmbedding ((𝓡 2).prod (𝓡∂ 1)) ThreeModel ∞ (T.tube a)) :
    (coreRetraction T hsm).comp (coreInclusion T) = ContinuousMap.id ↥T.core := by
  ext x
  simpa [ContinuousMap.comp_apply, coreRetraction, coreInclusion]
    using T.coreFun_eq_self_of_mem_core x.2 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.coreRetraction_comp_coreInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.coreRetraction_comp_coreInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.coreRetraction_comp_coreInclusion ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.coreRetraction_comp_coreInclusion

def coreHomotopy
    (hsm : ∀ a : T.Index, _root_.Manifold.IsSmoothEmbedding ((𝓡 2).prod (𝓡∂ 1)) ThreeModel ∞ (T.tube a)) :
    ContinuousMap.Homotopy (ContinuousMap.id ↥T.puncturedCore)
      ((coreInclusion T).comp (coreRetraction T hsm)) where
  toFun p := ⟨T.coreFun (p.1, (p.2 : M)), T.coreFun_mem_puncturedCore p.2.2⟩
  continuous_toFun := (T.continuous_coreFun hsm).subtype_mk _
  map_zero_left u := Subtype.ext (T.coreFun_zero ((0 : I), (u : M)))
  map_one_left u := by
    apply Subtype.ext
    simp [ContinuousMap.comp_apply, coreRetraction, coreInclusion]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.coreHomotopy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.coreHomotopy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.coreHomotopy ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.coreHomotopy

theorem coreInclusion_comp_coreRetraction_homotopic_id
    (hsm : ∀ a : T.Index, _root_.Manifold.IsSmoothEmbedding ((𝓡 2).prod (𝓡∂ 1)) ThreeModel ∞ (T.tube a)) :
    ((coreInclusion T).comp (coreRetraction T hsm)).Homotopic
      (ContinuousMap.id ↥T.puncturedCore) :=
  ⟨(coreHomotopy T hsm).symm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.coreInclusion_comp_coreRetraction_homotopic_id then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.coreInclusion_comp_coreRetraction_homotopic_id"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.coreInclusion_comp_coreRetraction_homotopic_id ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.coreInclusion_comp_coreRetraction_homotopic_id

noncomputable def puncturedCoreHomotopyEquivCore
    (hsm : ∀ a : T.Index, _root_.Manifold.IsSmoothEmbedding ((𝓡 2).prod (𝓡∂ 1)) ThreeModel ∞ (T.tube a)) :
    ↥T.puncturedCore ≃ₕ ↥T.core :=
  (homotopyEquiv_of_retraction (coreInclusion T) (coreRetraction T hsm)
    (coreRetraction_comp_coreInclusion T hsm)
    (coreInclusion_comp_coreRetraction_homotopic_id T hsm)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.puncturedCoreHomotopyEquivCore then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.puncturedCoreHomotopyEquivCore"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.puncturedCoreHomotopyEquivCore ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.puncturedCoreHomotopyEquivCore

theorem simplyConnectedSpace_puncturedCore_iff_core
    (hsm : ∀ a : T.Index, _root_.Manifold.IsSmoothEmbedding ((𝓡 2).prod (𝓡∂ 1)) ThreeModel ∞ (T.tube a)) :
    SimplyConnectedSpace ↥T.puncturedCore ↔ SimplyConnectedSpace ↥T.core :=
  (puncturedCoreHomotopyEquivCore T hsm).simplyConnectedSpace_iff

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.simplyConnectedSpace_puncturedCore_iff_core then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.simplyConnectedSpace_puncturedCore_iff_core"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.simplyConnectedSpace_puncturedCore_iff_core ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.simplyConnectedSpace_puncturedCore_iff_core

theorem simplyConnectedSpace_puncturedCore_of_core
    (hsm : ∀ a : T.Index, _root_.Manifold.IsSmoothEmbedding ((𝓡 2).prod (𝓡∂ 1)) ThreeModel ∞ (T.tube a))
    [SimplyConnectedSpace ↥T.core] : SimplyConnectedSpace ↥T.puncturedCore :=
  (simplyConnectedSpace_puncturedCore_iff_core T hsm).mpr inferInstance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.simplyConnectedSpace_puncturedCore_of_core then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.simplyConnectedSpace_puncturedCore_of_core"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.simplyConnectedSpace_puncturedCore_of_core ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.simplyConnectedSpace_puncturedCore_of_core

theorem simplyConnectedSpace_core_of_puncturedCore
    (hsm : ∀ a : T.Index, _root_.Manifold.IsSmoothEmbedding ((𝓡 2).prod (𝓡∂ 1)) ThreeModel ∞ (T.tube a))
    [SimplyConnectedSpace ↥T.puncturedCore] : SimplyConnectedSpace ↥T.core :=
  (simplyConnectedSpace_puncturedCore_iff_core T hsm).mp inferInstance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.simplyConnectedSpace_core_of_puncturedCore then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.simplyConnectedSpace_core_of_puncturedCore"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.simplyConnectedSpace_core_of_puncturedCore ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.simplyConnectedSpace_core_of_puncturedCore

end Retraction

section EmptyIndex

variable {M : Type*} [TopologicalSpace M] (T : TubeSystem M)

theorem puncturedCore_eq_univ_of_isEmpty [IsEmpty T.Index] : T.puncturedCore = univ := by
  simp [puncturedCore]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.puncturedCore_eq_univ_of_isEmpty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.puncturedCore_eq_univ_of_isEmpty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.puncturedCore_eq_univ_of_isEmpty ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.puncturedCore_eq_univ_of_isEmpty

noncomputable def puncturedCoreHomeomorphOfIsEmpty [IsEmpty T.Index] : ↥T.puncturedCore ≃ₜ M where
  toFun x := x.1
  invFun x := ⟨x, by rw [puncturedCore_eq_univ_of_isEmpty T]; trivial⟩
  left_inv x := Subtype.ext rfl
  right_inv x := rfl
  continuous_toFun := continuous_subtype_val
  continuous_invFun := continuous_id.subtype_mk fun x => by
    rw [puncturedCore_eq_univ_of_isEmpty T]
    trivial

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.puncturedCoreHomeomorphOfIsEmpty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.puncturedCoreHomeomorphOfIsEmpty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.puncturedCoreHomeomorphOfIsEmpty ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.puncturedCoreHomeomorphOfIsEmpty

theorem simplyConnectedSpace_puncturedCore_iff_of_isEmpty [IsEmpty T.Index] :
    SimplyConnectedSpace ↥T.puncturedCore ↔ SimplyConnectedSpace M :=
  (puncturedCoreHomeomorphOfIsEmpty T).toHomotopyEquiv.simplyConnectedSpace_iff

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.simplyConnectedSpace_puncturedCore_iff_of_isEmpty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.simplyConnectedSpace_puncturedCore_iff_of_isEmpty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.simplyConnectedSpace_puncturedCore_iff_of_isEmpty ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.simplyConnectedSpace_puncturedCore_iff_of_isEmpty

theorem not_simplyConnectedSpace_puncturedCore_of_not_pathConnected [IsEmpty T.Index]
    (h : ¬ PathConnectedSpace M) : ¬ SimplyConnectedSpace ↥T.puncturedCore := by
  intro hsc
  exact h ((puncturedCoreHomeomorphOfIsEmpty T).surjective.pathConnectedSpace
    (puncturedCoreHomeomorphOfIsEmpty T).continuous)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.not_simplyConnectedSpace_puncturedCore_of_not_pathConnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.not_simplyConnectedSpace_puncturedCore_of_not_pathConnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.not_simplyConnectedSpace_puncturedCore_of_not_pathConnected ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.not_simplyConnectedSpace_puncturedCore_of_not_pathConnected

end EmptyIndex

end TubeSystem

theorem subsingleton_of_pathConnectedSpace_of_totallyDisconnectedSpace {X : Type*}
    [TopologicalSpace X] [PathConnectedSpace X] [TotallyDisconnectedSpace X] :
    Subsingleton X :=
  subsingleton_of_preconnected_totallyDisconnected

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.subsingleton_of_pathConnectedSpace_of_totallyDisconnectedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.subsingleton_of_pathConnectedSpace_of_totallyDisconnectedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.subsingleton_of_pathConnectedSpace_of_totallyDisconnectedSpace ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.subsingleton_of_pathConnectedSpace_of_totallyDisconnectedSpace

theorem not_pathConnectedSpace_of_totallyDisconnectedSpace_of_nontrivial {X : Type*}
    [TopologicalSpace X] [TotallyDisconnectedSpace X] [Nontrivial X] :
    ¬ PathConnectedSpace X := by
  intro h
  obtain ⟨x, y, hxy⟩ := exists_pair_ne X
  have hsub : Subsingleton X := subsingleton_of_pathConnectedSpace_of_totallyDisconnectedSpace
  exact hxy (hsub.elim x y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_pathConnectedSpace_of_totallyDisconnectedSpace_of_nontrivial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_pathConnectedSpace_of_totallyDisconnectedSpace_of_nontrivial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_pathConnectedSpace_of_totallyDisconnectedSpace_of_nontrivial ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_pathConnectedSpace_of_totallyDisconnectedSpace_of_nontrivial

theorem exists_tubeSystem_not_simplyConnectedSpace_puncturedCore :
    ∃ (M : Type) (_ : TopologicalSpace M) (T : TubeSystem M),
      ¬ SimplyConnectedSpace ↥T.puncturedCore := by
  have hI : IsEmpty (emptyTubeSystem Bool).Index := ⟨fun a => a.elim⟩
  exact ⟨Bool, inferInstance, emptyTubeSystem Bool,
    (emptyTubeSystem Bool).not_simplyConnectedSpace_puncturedCore_of_not_pathConnected
      (not_pathConnectedSpace_of_totallyDisconnectedSpace_of_nontrivial (X := Bool))⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_tubeSystem_not_simplyConnectedSpace_puncturedCore then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_tubeSystem_not_simplyConnectedSpace_puncturedCore"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_tubeSystem_not_simplyConnectedSpace_puncturedCore ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_tubeSystem_not_simplyConnectedSpace_puncturedCore

private def productNeckTubeSystem : TubeSystem TubeDomain where
  Index := PUnit
  finiteIndex := inferInstance
  tube := fun _ => ContinuousMap.id TubeDomain
  embedding := fun _ => Topology.IsEmbedding.id
  disjoint := fun a b hab => (hab (Subsingleton.elim a b)).elim

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.productNeckTubeSystem
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.productNeckTubeSystem target :: scope.openDecls } }

private theorem mem_puncturedCore_productNeckTubeSystem (z : TubeDomain) :
    z ∈ productNeckTubeSystem.puncturedCore ↔ z.2.1 ≠ 0 := by
  rw [TubeSystem.mem_puncturedCore_iff]
  constructor
  · intro h h0
    exact h PUnit.unit ⟨z, h0, rfl⟩
  · intro h a
    rintro ⟨w, hw, hwz⟩
    have hwz' : w = z := hwz
    exact h (hwz' ▸ hw)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.mem_puncturedCore_productNeckTubeSystem
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.mem_puncturedCore_productNeckTubeSystem target :: scope.openDecls } }

private theorem not_pathConnectedSpace_productNeckTubeSystem :
    ¬ PathConnectedSpace ↥productNeckTubeSystem.puncturedCore := by
  intro h
  let x₀ : Sphere 2 := ⟨EuclideanSpace.single 0 1, by simp [Sphere, PiLp.norm_single]⟩
  let zpos : ↥productNeckTubeSystem.puncturedCore :=
    ⟨(x₀, ⟨1, by norm_num, by norm_num⟩), by
      rw [mem_puncturedCore_productNeckTubeSystem]
      norm_num⟩
  let zneg : ↥productNeckTubeSystem.puncturedCore :=
    ⟨(x₀, ⟨-1, by norm_num, by norm_num⟩), by
      rw [mem_puncturedCore_productNeckTubeSystem]
      norm_num⟩
  have hzpos : ((zpos : TubeDomain).2.1 : ℝ) = 1 := rfl
  have hzneg : ((zneg : TubeDomain).2.1 : ℝ) = -1 := rfl
  have hcoord : Continuous fun z : ↥productNeckTubeSystem.puncturedCore =>
      ((z : TubeDomain).2.1 : ℝ) :=
    (continuous_subtype_val.comp continuous_snd).comp continuous_subtype_val
  have hs : IsOpen {z : ↥productNeckTubeSystem.puncturedCore | 0 < (z : TubeDomain).2.1} :=
    isOpen_lt continuous_const hcoord
  have ht : IsOpen {z : ↥productNeckTubeSystem.puncturedCore | (z : TubeDomain).2.1 < 0} :=
    isOpen_lt hcoord continuous_const
  have hdisj : Disjoint {z : ↥productNeckTubeSystem.puncturedCore |
        0 < (z : TubeDomain).2.1}
      {z : ↥productNeckTubeSystem.puncturedCore | (z : TubeDomain).2.1 < 0} :=
    Set.disjoint_left.mpr fun z h1 h2 => by
      simp only [Set.mem_ofPred_eq] at h1 h2
      linarith
  have hcover : (_root_.Set.univ : Set ↥productNeckTubeSystem.puncturedCore) ⊆
      {z : ↥productNeckTubeSystem.puncturedCore | 0 < (z : TubeDomain).2.1} ∪
        {z : ↥productNeckTubeSystem.puncturedCore | (z : TubeDomain).2.1 < 0} := by
    intro z _
    have hz : (z : TubeDomain).2.1 ≠ 0 :=
      (mem_puncturedCore_productNeckTubeSystem z.1).mp z.2
    rcases lt_or_gt_of_ne hz with hlt | hgt
    · exact Or.inr hlt
    · exact Or.inl hgt
  have hne : (_root_.Set.univ ∩ {z : ↥productNeckTubeSystem.puncturedCore |
      0 < (z : TubeDomain).2.1}).Nonempty :=
    ⟨zpos, _root_.Set.mem_univ zpos, by
      change (0 : ℝ) < ((zpos : TubeDomain).2.1)
      rw [hzpos]
      norm_num⟩
  have hsub := isPreconnected_univ.subset_left_of_subset_union hs ht hdisj hcover hne
  have hbad := hsub (_root_.Set.mem_univ zneg)
  simp only [Set.mem_ofPred_eq] at hbad
  rw [hzneg] at hbad
  norm_num at hbad

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_pathConnectedSpace_productNeckTubeSystem
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_pathConnectedSpace_productNeckTubeSystem target :: scope.openDecls } }

theorem exists_tubeSystem_nonemptyIndex_not_simplyConnectedSpace_puncturedCore :
    ∃ (M : Type) (_ : TopologicalSpace M) (T : TubeSystem M),
      Nonempty T.Index ∧ ¬ SimplyConnectedSpace ↥T.puncturedCore :=
  ⟨TubeDomain, inferInstance, productNeckTubeSystem, ⟨⟨PUnit.unit⟩,
    fun _ => not_pathConnectedSpace_productNeckTubeSystem inferInstance⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_tubeSystem_nonemptyIndex_not_simplyConnectedSpace_puncturedCore then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_tubeSystem_nonemptyIndex_not_simplyConnectedSpace_puncturedCore"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_tubeSystem_nonemptyIndex_not_simplyConnectedSpace_puncturedCore ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_tubeSystem_nonemptyIndex_not_simplyConnectedSpace_puncturedCore

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
