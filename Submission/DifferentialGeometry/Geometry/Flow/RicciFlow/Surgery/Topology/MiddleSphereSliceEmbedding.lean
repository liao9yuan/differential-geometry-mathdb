import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildCarrierCollaredStarCover
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildCoreComponentRetraction
import Submission.DifferentialGeometry.Topology.Manifold.SmoothEmbeddingComposition

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Submission.Set _root_.Topology _root_.Manifold _root_.Submission.Manifold _root_.Function _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactLtRealNegOfNat_differentialGeometry_1 : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactLtRealNegOfNat_differentialGeometry_1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactLtRealNegOfNat_differentialGeometry_1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactLtRealNegOfNat_differentialGeometry_1 ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactLtRealNegOfNat_differentialGeometry_1

def middleLevel : _root_.Set.Icc (-2 : ℝ) 2 := ⟨0, by norm_num⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.middleLevel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.middleLevel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.middleLevel ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.middleLevel

def middleSphereSlice : Sphere 2 → TubeDomain := fun y => (y, middleLevel)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.middleSphereSlice then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.middleSphereSlice"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.middleSphereSlice ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.middleSphereSlice

@[simp] theorem middleSphereSlice_apply (y : Sphere 2) :
    middleSphereSlice y = (y, middleLevel) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.middleSphereSlice_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.middleSphereSlice_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.middleSphereSlice_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.middleSphereSlice_apply

theorem injective_middleSphereSlice : _root_.Function.Injective middleSphereSlice := by
  intro y₁ y₂ h
  simpa [middleSphereSlice] using congrArg Prod.fst h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.injective_middleSphereSlice then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.injective_middleSphereSlice"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.injective_middleSphereSlice ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.injective_middleSphereSlice

theorem isEmbedding_middleSphereSlice : _root_.Topology.IsEmbedding middleSphereSlice :=
  isEmbedding_prodMkLeft middleLevel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isEmbedding_middleSphereSlice then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isEmbedding_middleSphereSlice"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isEmbedding_middleSphereSlice ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isEmbedding_middleSphereSlice

theorem contMDiff_middleSphereSlice :
    ContMDiff (𝓡 2) ((𝓡 2).prod (𝓡∂ 1)) ∞ middleSphereSlice :=
  contMDiff_id.prodMk contMDiff_const

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.contMDiff_middleSphereSlice then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.contMDiff_middleSphereSlice"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.contMDiff_middleSphereSlice ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.contMDiff_middleSphereSlice

theorem range_middleSphereSlice :
    range middleSphereSlice = {z : TubeDomain | z.2.1 = 0} := by
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    rfl
  · intro hz
    exact ⟨z.1, Prod.ext rfl (Subtype.ext (by simpa [middleLevel] using hz.symm))⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.range_middleSphereSlice then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.range_middleSphereSlice"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.range_middleSphereSlice ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.range_middleSphereSlice

theorem chartAt_middleLevel_apply :
    (chartAt (EuclideanHalfSpace 1) middleLevel) middleLevel =
      ⟨WithLp.toLp 2 (fun _ => (2 : ℝ)), by norm_num⟩ := by
  rw [Icc_chartedSpaceChartAt_of_le_top (z := middleLevel) (by norm_num [middleLevel])]
  simp [IccLeftChart_apply, middleLevel]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.chartAt_middleLevel_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.chartAt_middleLevel_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.chartAt_middleLevel_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.chartAt_middleLevel_apply

theorem chartAt_middleLevel_extend_apply :
    ((chartAt (EuclideanHalfSpace 1) middleLevel).extend (𝓡∂ 1)) middleLevel =
      WithLp.toLp 2 (fun _ => (2 : ℝ)) := by
  rw [OpenPartialHomeomorph.extend_coe, Function.comp_apply, chartAt_middleLevel_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.chartAt_middleLevel_extend_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.chartAt_middleLevel_extend_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.chartAt_middleLevel_extend_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.chartAt_middleLevel_extend_apply

theorem chartAt_middleLevel_extend_ne_zero :
    ((chartAt (EuclideanHalfSpace 1) middleLevel).extend (𝓡∂ 1)) middleLevel ≠ 0 := by
  rw [chartAt_middleLevel_extend_apply]
  intro h
  simpa using congrArg (fun v : EuclideanSpace ℝ (Fin 1) => v 0) h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.chartAt_middleLevel_extend_ne_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.chartAt_middleLevel_extend_ne_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.chartAt_middleLevel_extend_ne_zero ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.chartAt_middleLevel_extend_ne_zero

namespace TubeSystem

variable {M : Type*} [TopologicalSpace M] (T : TubeSystem M)

theorem middleSphere_eq_image_middleSphereSlice (a : T.Index) :
    T.middleSphere a = T.tube a '' _root_.Set.range middleSphereSlice := by
  rw [range_middleSphereSlice]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.middleSphere_eq_image_middleSphereSlice then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.middleSphere_eq_image_middleSphereSlice"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.middleSphere_eq_image_middleSphereSlice ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.middleSphere_eq_image_middleSphereSlice

theorem range_tube_middleSphereSlice (a : T.Index) :
    range (fun y : Sphere 2 => T.tube a (middleSphereSlice y)) = T.middleSphere a := by
  rw [show (fun y : Sphere 2 => T.tube a (middleSphereSlice y)) =
      (T.tube a) ∘ middleSphereSlice from rfl,
    Set.range_comp, range_middleSphereSlice]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.range_tube_middleSphereSlice then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.range_tube_middleSphereSlice"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.range_tube_middleSphereSlice ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.range_tube_middleSphereSlice

theorem isEmbedding_tube_middleSphereSlice (a : T.Index) :
    IsEmbedding (fun y : Sphere 2 => T.tube a (middleSphereSlice y)) :=
  (T.embedding a).comp isEmbedding_middleSphereSlice

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.isEmbedding_tube_middleSphereSlice then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.isEmbedding_tube_middleSphereSlice"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.isEmbedding_tube_middleSphereSlice ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.isEmbedding_tube_middleSphereSlice

def middleSphereSliceSmoothEmbedding : Prop :=
  _root_.Manifold.IsSmoothEmbedding (𝓡 2) ((𝓡 2).prod (𝓡∂ 1)) ∞ middleSphereSlice

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.middleSphereSliceSmoothEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.middleSphereSliceSmoothEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.middleSphereSliceSmoothEmbedding ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.middleSphereSliceSmoothEmbedding

section Smooth

variable [ChartedSpace ThreeSpace M]

theorem contMDiff_tube_middleSphereSlice (a : T.Index)
    (hsm : _root_.Manifold.IsSmoothEmbedding ((𝓡 2).prod (𝓡∂ 1)) ThreeModel ∞ (T.tube a)) :
    ContMDiff (𝓡 2) ThreeModel ∞ (fun y : Sphere 2 => T.tube a (middleSphereSlice y)) :=
  hsm.contMDiff.comp contMDiff_middleSphereSlice

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.contMDiff_tube_middleSphereSlice then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.contMDiff_tube_middleSphereSlice"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.contMDiff_tube_middleSphereSlice ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.contMDiff_tube_middleSphereSlice

theorem isSmoothEmbedding_tube_middleSphereSlice
    (hsm : ∀ a : T.Index, _root_.Manifold.IsSmoothEmbedding ((𝓡 2).prod (𝓡∂ 1)) ThreeModel ∞ (T.tube a))
    (hslice : middleSphereSliceSmoothEmbedding) (a : T.Index) :
    IsSmoothEmbedding (𝓡 2) ThreeModel ∞ (fun y : Sphere 2 => T.tube a (middleSphereSlice y)) :=
  IsSmoothEmbedding.comp (I := 𝓡 2) (J := (𝓡 2).prod (𝓡∂ 1)) (J' := ThreeModel)
    (f := middleSphereSlice) (g := fun z => T.tube a z) (hsm a) hslice (by decide)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.isSmoothEmbedding_tube_middleSphereSlice then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.isSmoothEmbedding_tube_middleSphereSlice"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.isSmoothEmbedding_tube_middleSphereSlice ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.isSmoothEmbedding_tube_middleSphereSlice

end Smooth

end TubeSystem

theorem continuousLinearMap_eq_zero_of_eqOn_of_mem_nhds {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {D : E →L[ℝ] F} {U : Set E} {z : E} {c : F} (hU : U ∈ 𝓝 z) (h : ∀ w ∈ U, D w = c) :
    c = 0 := by
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hU
  have hz : D z = c := h z (hball (by rw [Metric.mem_ball, dist_self]; exact hδ))
  have hw : ∀ w : E, D w = 0 := by
    intro w
    have hpos : 0 < δ / (2 * (‖w‖ + 1)) := by positivity
    have hsmall : δ / (2 * (‖w‖ + 1)) * ‖w‖ < δ := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [norm_nonneg w]
    have hmem : z + (δ / (2 * (‖w‖ + 1))) • w ∈ U :=
      hball (by
        rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
          abs_of_pos hpos]
        exact hsmall)
    have h1 : D z + (δ / (2 * (‖w‖ + 1))) • D w = D z := by
      rw [← map_smul, ← map_add, h (z + _ • w) hmem, hz]
    have h2 : (δ / (2 * (‖w‖ + 1))) • D w = 0 :=
      add_left_cancel (show D z + (δ / (2 * (‖w‖ + 1))) • D w = D z + 0 by rw [add_zero]; exact h1)
    exact (smul_eq_zero.mp h2).resolve_left (ne_of_gt hpos)
  rw [← hz, hw z]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.continuousLinearMap_eq_zero_of_eqOn_of_mem_nhds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.continuousLinearMap_eq_zero_of_eqOn_of_mem_nhds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.continuousLinearMap_eq_zero_of_eqOn_of_mem_nhds ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.continuousLinearMap_eq_zero_of_eqOn_of_mem_nhds


theorem not_exists_eqOn_canonicalProductChart (y : Sphere 2)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (equiv : (EuclideanSpace ℝ (Fin 2) × F) ≃L[ℝ]
      (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1))) :
    ¬ _root_.Set.EqOn ((((chartAt (EuclideanSpace ℝ (Fin 2)) y).prod
            (chartAt (EuclideanHalfSpace 1) middleLevel)).extend ((𝓡 2).prod (𝓡∂ 1))) ∘
          middleSphereSlice ∘
          (((chartAt (EuclideanSpace ℝ (Fin 2)) y).extend (𝓡 2)).symm))
        (fun z => equiv (z, 0))
        (((chartAt (EuclideanSpace ℝ (Fin 2)) y).extend (𝓡 2)).target) := by
  intro h
  let χ := chartAt (EuclideanSpace ℝ (Fin 2)) y
  let e := chartAt (EuclideanHalfSpace 1) middleLevel
  let D : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 1) :=
    (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 1))).comp
      ((equiv : (EuclideanSpace ℝ (Fin 2) × F) →L[ℝ]
        (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1))).comp
        (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin 2)) F))
  have hconst : ∀ z ∈ (χ.extend (𝓡 2)).target, D z = (e.extend (𝓡∂ 1)) middleLevel := by
    intro z hz
    have hw : ((χ.extend (𝓡 2)).symm z) ∈ χ.source := by
      have hm := (χ.extend (𝓡 2)).map_target hz
      rwa [χ.extend_source] at hm
    have hmem_pair : (((χ.extend (𝓡 2)).symm z), middleLevel) ∈ (χ.prod e).source :=
      ⟨hw, mem_chart_source _ _⟩
    have hval : ((χ.prod e).extend ((𝓡 2).prod (𝓡∂ 1)))
        ((χ.extend (𝓡 2)).symm z, middleLevel) = (z, (e.extend (𝓡∂ 1)) middleLevel) := by
      rw [OpenPartialHomeomorph.extend_prod χ e, PartialEquiv.prod_coe]
      exact Prod.ext ((χ.extend (𝓡 2)).right_inv hz) rfl
    have hz'' : ((χ.prod e).extend ((𝓡 2).prod (𝓡∂ 1)))
        ((χ.extend (𝓡 2)).symm z, middleLevel) = equiv (z, 0) := by
      simpa only [Function.comp_apply, middleSphereSlice_apply] using h hz
    rw [hval] at hz''
    have hsnd := congrArg Prod.snd hz''
    simpa [D] using hsnd.symm
  have hmem : (χ.extend (𝓡 2)).target ∈ 𝓝 ((χ.extend (𝓡 2)) y) :=
    χ.isOpen_extend_target.mem_nhds (by
      rw [χ.extend_target_eq_image_source]
      exact _root_.Set.mem_image_of_mem _ (mem_chart_source _ y))
  refine chartAt_middleLevel_extend_ne_zero ?_
  simpa only [e] using continuousLinearMap_eq_zero_of_eqOn_of_mem_nhds hmem hconst

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_exists_eqOn_canonicalProductChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_exists_eqOn_canonicalProductChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_exists_eqOn_canonicalProductChart ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_exists_eqOn_canonicalProductChart

namespace SmoothCutCapTransition

variable {P Q D N : OrientedThreeStage.{u}} (E : SmoothCutCapTransition P Q D N)

def middleSphereCuttingSeparation : Prop :=
  ∀ c : ConnectedComponents Q.Carrier,
    SimplyConnectedSpace (P.component (E.childParent c)).Carrier →
      SimplyConnectedSpace ↥(E.trace.tubes.puncturedCoreComponent (E.childCoreComponent c))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.middleSphereCuttingSeparation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.middleSphereCuttingSeparation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.middleSphereCuttingSeparation ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.middleSphereCuttingSeparation

theorem childCoreSimplyConnectedOfParent_of_middleSphereCuttingSeparation
    (hsep : E.middleSphereCuttingSeparation) : E.childCoreSimplyConnectedOfParent :=
  fun c hpar => E.simplyConnectedSpace_childCore_of_puncturedCoreComponent c (hsep c hpar)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCoreSimplyConnectedOfParent_of_middleSphereCuttingSeparation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCoreSimplyConnectedOfParent_of_middleSphereCuttingSeparation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCoreSimplyConnectedOfParent_of_middleSphereCuttingSeparation ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCoreSimplyConnectedOfParent_of_middleSphereCuttingSeparation

theorem componentwisePuncturedCoreOfParent_of_middleSphereCuttingSeparation
    (hsep : E.middleSphereCuttingSeparation) : E.ComponentwisePuncturedCoreOfParent :=
  fun c hpar => hsep c hpar

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.componentwisePuncturedCoreOfParent_of_middleSphereCuttingSeparation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.componentwisePuncturedCoreOfParent_of_middleSphereCuttingSeparation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.componentwisePuncturedCoreOfParent_of_middleSphereCuttingSeparation ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.componentwisePuncturedCoreOfParent_of_middleSphereCuttingSeparation

end SmoothCutCapTransition

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
