/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Geometry.Manifold.Instances.Sphere
import Submission.DifferentialGeometry.Topology.FundamentalGroup.BasepointChange
import Submission.DifferentialGeometry.Topology.FundamentalGroup.Circle
import Submission.DifferentialGeometry.Topology.FundamentalGroup.HomotopyEquiv
import Submission.DifferentialGeometry.Topology.VanKampen.SimplyConnectedUnion

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.Metric _root_.Module _root_.Set
open scoped _root_.RealInnerProductSpace

universe u

namespace DifferentialGeometry.Topology

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def sphereComplPointHomeomorph (v : E) (hv : ‖v‖ = 1) :
    ({⟨v, by simp [hv]⟩}ᶜ : Set (_root_.Metric.sphere (0 : E) 1)) ≃ₜ (ℝ ∙ v)ᗮ := by
  rw [← stereographic_source hv]
  exact (stereographic hv).toHomeomorphSourceTarget.trans (Homeomorph.Set.univ _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereComplPointHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereComplPointHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereComplPointHomeomorph ``Submission.DifferentialGeometry.Topology.sphereComplPointHomeomorph

theorem simplyConnectedSpace_sphere_compl_point (v : E) (hv : ‖v‖ = 1) :
    SimplyConnectedSpace ({⟨v, by simp [hv]⟩}ᶜ : Set (_root_.Metric.sphere (0 : E) 1)) := by
  exact (sphereComplPointHomeomorph v hv).toHomotopyEquiv.simplyConnectedSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.simplyConnectedSpace_sphere_compl_point then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.simplyConnectedSpace_sphere_compl_point"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.simplyConnectedSpace_sphere_compl_point ``Submission.DifferentialGeometry.Topology.simplyConnectedSpace_sphere_compl_point

noncomputable def sphereComplAntipodesHomeomorph (v : E) (hv : ‖v‖ = 1) :
    (({⟨v, by simp [hv]⟩}ᶜ ∩ {⟨-v, by simp [hv]⟩}ᶜ) :
      Set (_root_.Metric.sphere (0 : E) 1)) ≃ₜ ({0}ᶜ : Set ((ℝ ∙ v)ᗮ)) :=
  (stereographic hv).homeomorphOfImageSubsetSource (fun _ hx ↦ hx.1) <| by
    ext w
    constructor
    · rintro ⟨x, hx, rfl⟩ hzero
      have hzero' : stereographic hv x = 0 := by simpa using hzero
      have hneg : (⟨-v, by simp [hv]⟩ : _root_.Metric.sphere (0 : E) 1) = -⟨v, by simp [hv]⟩ := by
        apply Subtype.ext
        rfl
      have hstereoSouth :
          stereographic hv (⟨-v, by simp [hv]⟩ : _root_.Metric.sphere (0 : E) 1) = 0 := by
        rw [hneg]
        exact stereographic_apply_neg ⟨v, by simp [hv]⟩
      have hsouth : (⟨-v, by simp [hv]⟩ : _root_.Metric.sphere (0 : E) 1) ∈
          (stereographic hv).source := by
        rw [stereographic_source]
        simp only [_root_.Set.mem_compl_iff, _root_.Set.mem_singleton_iff]
        intro h
        have hval : -v = v := congrArg Subtype.val h
        have htwo : (2 : ℝ) • v = 0 := by
          rw [two_smul]
          exact neg_eq_iff_add_eq_zero.mp hval
        have hvzero : v = 0 := (smul_eq_zero.mp htwo).resolve_left (by norm_num)
        simp [hvzero] at hv
      have hxeq : x = ⟨-v, by simp [hv]⟩ := by
        exact (stereographic hv).injOn hx.1 hsouth (by
          rw [hzero']
          exact hstereoSouth.symm)
      exact hx.2 hxeq
    · intro hw
      let w' : (stereographic hv).target := ⟨w, by simp⟩
      let x : _root_.Metric.sphere (0 : E) 1 := (stereographic hv).symm w'
      have hxsource : x ∈ (stereographic hv).source :=
        (stereographic hv).map_target w'.property
      have hmap : stereographic hv x = w := by
        change stereographic hv ((stereographic hv).symm w') = w
        exact (stereographic hv).right_inv w'.property
      refine ⟨x, ⟨hxsource, ?_⟩, hmap⟩
      intro hxsouth
      have : w = 0 := by
        rw [← hmap, hxsouth]
        have hneg : (⟨-v, by simp [hv]⟩ : _root_.Metric.sphere (0 : E) 1) = -⟨v, by simp [hv]⟩ := by
          apply Subtype.ext
          rfl
        rw [hneg]
        exact stereographic_apply_neg ⟨v, by simp [hv]⟩
      exact hw this

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereComplAntipodesHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereComplAntipodesHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereComplAntipodesHomeomorph ``Submission.DifferentialGeometry.Topology.sphereComplAntipodesHomeomorph

theorem simplyConnectedSpace_sphere_of_orthogonal_rank_gt_one
    (v : E) (hv : ‖v‖ = 1) (horth : 1 < Module.rank ℝ ((ℝ ∙ v)ᗮ)) :
    SimplyConnectedSpace (_root_.Metric.sphere (0 : E) 1) := by
  let north : _root_.Metric.sphere (0 : E) 1 := ⟨v, by simp [hv]⟩
  let south : _root_.Metric.sphere (0 : E) 1 := ⟨-v, by simp [hv]⟩
  let U : Set (_root_.Metric.sphere (0 : E) 1) := {north}ᶜ
  let V : Set (_root_.Metric.sphere (0 : E) 1) := {south}ᶜ
  have hnorth_ne_south : north ≠ south := by
    intro h
    have hval : v = -v := congrArg Subtype.val h
    have htwo : (2 : ℝ) • v = 0 := by
      rw [two_smul]
      exact eq_neg_iff_add_eq_zero.mp hval
    have hvzero : v = 0 := (smul_eq_zero.mp htwo).resolve_left (by norm_num)
    simp [hvzero] at hv
  have hU : IsOpen U := isOpen_compl_singleton
  have hV : IsOpen V := isOpen_compl_singleton
  have hcover : U ∪ V = univ := by
    ext x
    simp only [U, V, _root_.Set.mem_union, _root_.Set.mem_compl_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_univ, iff_true]
    by_contra h
    rw [not_or] at h
    exact hnorth_ne_south ((not_ne_iff.mp h.1).symm.trans (not_ne_iff.mp h.2))
  let _ : SimplyConnectedSpace U := by
    simpa only [U, north] using simplyConnectedSpace_sphere_compl_point v hv
  have hvneg : ‖-v‖ = 1 := by simpa using hv
  let _ : SimplyConnectedSpace V := by
    simpa only [V, south, north] using simplyConnectedSpace_sphere_compl_point (-v) hvneg
  let e : ↑(U ∩ V) ≃ₜ ({0}ᶜ : Set ((ℝ ∙ v)ᗮ)) := by
    simpa only [U, V, north, south] using sphereComplAntipodesHomeomorph v hv
  have htarget : IsPathConnected ({0}ᶜ : Set ((ℝ ∙ v)ᗮ)) :=
    isPathConnected_compl_singleton_of_one_lt_rank horth 0
  let _ : PathConnectedSpace ({0}ᶜ : Set ((ℝ ∙ v)ᗮ)) :=
    isPathConnected_iff_pathConnectedSpace.mp htarget
  let _ : PathConnectedSpace (↑(U ∩ V)) :=
    e.symm.surjective.pathConnectedSpace e.symm.continuous
  let w₀ : ({0}ᶜ : Set ((ℝ ∙ v)ᗮ)) := Classical.choice inferInstance
  let x₀ : _root_.Metric.sphere (0 : E) 1 := (e.symm w₀).1
  have hx₀ : x₀ ∈ U ∩ V := (e.symm w₀).2
  exact DifferentialGeometry.Topology.VanKampen.simplyConnectedSpace_of_open_cover
    U V hU hV hcover x₀ hx₀

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.simplyConnectedSpace_sphere_of_orthogonal_rank_gt_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.simplyConnectedSpace_sphere_of_orthogonal_rank_gt_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.simplyConnectedSpace_sphere_of_orthogonal_rank_gt_one ``Submission.DifferentialGeometry.Topology.simplyConnectedSpace_sphere_of_orthogonal_rank_gt_one

abbrev SphereTwo := _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereTwo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereTwo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereTwo ``Submission.DifferentialGeometry.Topology.SphereTwo

noncomputable abbrev sphereTwoNorthVector : EuclideanSpace ℝ (Fin 3) :=
  EuclideanSpace.single 0 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereTwoNorthVector then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereTwoNorthVector"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereTwoNorthVector ``Submission.DifferentialGeometry.Topology.sphereTwoNorthVector

theorem norm_sphereTwoNorthVector : ‖sphereTwoNorthVector‖ = 1 := by
  simp [sphereTwoNorthVector]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.norm_sphereTwoNorthVector then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.norm_sphereTwoNorthVector"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.norm_sphereTwoNorthVector ``Submission.DifferentialGeometry.Topology.norm_sphereTwoNorthVector

theorem one_lt_rank_sphereTwoNorthOrthogonal :
    1 < Module.rank ℝ ((ℝ ∙ sphereTwoNorthVector)ᗮ) := by
  let _ : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  have hnonzero : sphereTwoNorthVector ≠ 0 := by
    simp [sphereTwoNorthVector]
  have hfin : Module.finrank ℝ ((ℝ ∙ sphereTwoNorthVector)ᗮ) = 2 :=
    Submodule.finrank_orthogonal_span_singleton (n := 2) hnonzero
  rw [← Module.finrank_eq_rank']
  simp [hfin]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.one_lt_rank_sphereTwoNorthOrthogonal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.one_lt_rank_sphereTwoNorthOrthogonal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.one_lt_rank_sphereTwoNorthOrthogonal ``Submission.DifferentialGeometry.Topology.one_lt_rank_sphereTwoNorthOrthogonal

instance sphereTwoSimplyConnectedSpace : SimplyConnectedSpace SphereTwo :=
  simplyConnectedSpace_sphere_of_orthogonal_rank_gt_one sphereTwoNorthVector
    norm_sphereTwoNorthVector one_lt_rank_sphereTwoNorthOrthogonal

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereTwoSimplyConnectedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereTwoSimplyConnectedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereTwoSimplyConnectedSpace ``Submission.DifferentialGeometry.Topology.sphereTwoSimplyConnectedSpace

noncomputable def sphereTwoNorth : SphereTwo :=
  ⟨sphereTwoNorthVector, by simp⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereTwoNorth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereTwoNorth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereTwoNorth ``Submission.DifferentialGeometry.Topology.sphereTwoNorth

noncomputable def fundamentalGroupSphereTwoProdCircleEquivInt :
    FundamentalGroup (SphereTwo × Circle) (sphereTwoNorth, 1) ≃* Multiplicative ℤ :=
  fundamentalGroupProdCircleEquivIntOfSimplyConnected sphereTwoNorth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.fundamentalGroupSphereTwoProdCircleEquivInt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.fundamentalGroupSphereTwoProdCircleEquivInt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.fundamentalGroupSphereTwoProdCircleEquivInt ``Submission.DifferentialGeometry.Topology.fundamentalGroupSphereTwoProdCircleEquivInt

noncomputable def circleSphereOneHomeomorph :
    Circle ≃ₜ _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
  (Complex.orthonormalBasisOneI.repr.toHomeomorph).subtype (fun z => by
    change z ∈ (_root_.Metric.sphere (0 : ℂ) 1 : Set ℂ) ↔
      Complex.orthonormalBasisOneI.repr.toHomeomorph z ∈
        (_root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 : Set (EuclideanSpace ℝ (Fin 2)))
    rw [LinearIsometryEquiv.coe_toHomeomorph, mem_sphere_zero_iff_norm,
      mem_sphere_zero_iff_norm, Complex.orthonormalBasisOneI.repr.norm_map])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.circleSphereOneHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.circleSphereOneHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.circleSphereOneHomeomorph ``Submission.DifferentialGeometry.Topology.circleSphereOneHomeomorph

noncomputable def fundamentalGroupSphereOneEquivInt
    (y : _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
    FundamentalGroup (_root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) y ≃* Multiplicative ℤ :=
  (fundamentalGroupMulEquivOfHomotopyEquiv circleSphereOneHomeomorph.toHomotopyEquiv
      (circleSphereOneHomeomorph.symm y) y
      (circleSphereOneHomeomorph.apply_symm_apply y)).symm.trans
    ((fundamentalGroupChangeBasepoint
        (PathConnectedSpace.somePath (1 : Circle) (circleSphereOneHomeomorph.symm y))).trans
      fundamentalGroupCircleEquivInt)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.fundamentalGroupSphereOneEquivInt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.fundamentalGroupSphereOneEquivInt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.fundamentalGroupSphereOneEquivInt ``Submission.DifferentialGeometry.Topology.fundamentalGroupSphereOneEquivInt

noncomputable def fundamentalGroupProdSphereOneEquivInt
    {X : Type*} [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    (y : _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
    FundamentalGroup (X × _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) (x, y) ≃*
      Multiplicative ℤ :=
  (fundamentalGroupProdRightEquivOfSimplyConnected x y).trans
    (fundamentalGroupSphereOneEquivInt y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.fundamentalGroupProdSphereOneEquivInt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.fundamentalGroupProdSphereOneEquivInt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.fundamentalGroupProdSphereOneEquivInt ``Submission.DifferentialGeometry.Topology.fundamentalGroupProdSphereOneEquivInt

abbrev SphereThree := _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereThree then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereThree"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereThree ``Submission.DifferentialGeometry.Topology.SphereThree

noncomputable abbrev sphereThreeNorthVector : EuclideanSpace ℝ (Fin 4) :=
  EuclideanSpace.single 0 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereThreeNorthVector then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereThreeNorthVector"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereThreeNorthVector ``Submission.DifferentialGeometry.Topology.sphereThreeNorthVector

theorem norm_sphereThreeNorthVector : ‖sphereThreeNorthVector‖ = 1 := by
  simp [sphereThreeNorthVector]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.norm_sphereThreeNorthVector then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.norm_sphereThreeNorthVector"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.norm_sphereThreeNorthVector ``Submission.DifferentialGeometry.Topology.norm_sphereThreeNorthVector

theorem one_lt_rank_sphereThreeNorthOrthogonal :
    1 < Module.rank ℝ ((ℝ ∙ sphereThreeNorthVector)ᗮ) := by
  let _ : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩
  have hnonzero : sphereThreeNorthVector ≠ 0 := by
    simp [sphereThreeNorthVector]
  have hfin : Module.finrank ℝ ((ℝ ∙ sphereThreeNorthVector)ᗮ) = 3 :=
    Submodule.finrank_orthogonal_span_singleton (n := 3) hnonzero
  rw [← Module.finrank_eq_rank']
  simp [hfin]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.one_lt_rank_sphereThreeNorthOrthogonal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.one_lt_rank_sphereThreeNorthOrthogonal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.one_lt_rank_sphereThreeNorthOrthogonal ``Submission.DifferentialGeometry.Topology.one_lt_rank_sphereThreeNorthOrthogonal

instance sphereThreeSimplyConnectedSpace : SimplyConnectedSpace SphereThree :=
  simplyConnectedSpace_sphere_of_orthogonal_rank_gt_one sphereThreeNorthVector
    norm_sphereThreeNorthVector one_lt_rank_sphereThreeNorthOrthogonal

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereThreeSimplyConnectedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereThreeSimplyConnectedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereThreeSimplyConnectedSpace ``Submission.DifferentialGeometry.Topology.sphereThreeSimplyConnectedSpace

noncomputable def sphereThreeNorth : SphereThree :=
  ⟨sphereThreeNorthVector, by simp⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereThreeNorth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereThreeNorth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereThreeNorth ``Submission.DifferentialGeometry.Topology.sphereThreeNorth

end DifferentialGeometry.Topology
