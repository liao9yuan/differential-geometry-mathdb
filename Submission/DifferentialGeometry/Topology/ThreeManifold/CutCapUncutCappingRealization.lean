import Submission.DifferentialGeometry.Topology.Manifold.InverseFunctionTheorem.Basic
import Submission.DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open
import Submission.DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.OpenCodRestrict
import Submission.DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.PartialDiffeomorph
import Submission.DifferentialGeometry.Topology.ThreeManifold.CutCapCappedPresentationRealization
import Submission.DifferentialGeometry.Topology.ThreeManifold.CutCapGraphSumFrontier
import Submission.DifferentialGeometry.Topology.ThreeManifold.CutCapUncutComponentRealization
import Submission.DifferentialGeometry.Topology.ThreeManifold.PoincareStandardDiscarded

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Manifold _root_.Submission.Manifold _root_.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology

universe u

namespace SphericalCutCapTransition

variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)

local instance instUncutCappingCoreChartedSpace :
    ChartedSpace (EuclideanHalfSpace 3) E.tubes.core :=
  E.capping.coreCharts

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.instUncutCappingCoreChartedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.instUncutCappingCoreChartedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.instUncutCappingCoreChartedSpace ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.instUncutCappingCoreChartedSpace

local instance instUncutCappingCoreIsManifold :
    IsManifold (𝓡∂ 3) ∞ E.tubes.core :=
  E.capping.coreSmooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.instUncutCappingCoreIsManifold then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.instUncutCappingCoreIsManifold"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.instUncutCappingCoreIsManifold ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.instUncutCappingCoreIsManifold

abbrev uncutCoreInclusion (C : ConnectedComponents M.Carrier) (hC : E.cutIndices C = ∅) :
    (M.component C).Carrier → E.tubes.core :=
  fun y => ⟨y.1, E.componentSet_subset_core_of_cutIndices_eq_empty C hC y.2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.uncutCoreInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.uncutCoreInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.uncutCoreInclusion ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.uncutCoreInclusion

private theorem eventually_isInvertible_fderiv {G : EuclideanSpace ℝ (Fin 3) →
    EuclideanSpace ℝ (Fin 3)} {V : Set (EuclideanSpace ℝ (Fin 3))}
    {x : EuclideanSpace ℝ (Fin 3)}
    (hV : IsOpen V) (hx : x ∈ V) (hG : ContDiffOn ℝ ∞ G V)
    (hinv : (fderiv ℝ G x).IsInvertible) :
    ∀ᶠ y in 𝓝 x, (fderiv ℝ G y).IsInvertible := by
  obtain ⟨e, he⟩ := hinv
  have hinv_nhds : {L : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) |
      L.IsInvertible} ∈ 𝓝 (fderiv ℝ G x) := by
    rw [← he]
    exact e.nhds
  exact ((hG.contDiffAt (hV.mem_nhds hx)).continuousAt_fderiv (by simp)).preimage_mem_nhds
    hinv_nhds

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.eventually_isInvertible_fderiv
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphericalCutCapTransition.eventually_isInvertible_fderiv target :: scope.openDecls } }

private noncomputable def smoothEuclideanChart {N : Type u} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N] (y : N) :
    PartialDiffeomorph (𝓡 3) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) N
      (EuclideanSpace ℝ (Fin 3)) ∞ where
  toPartialEquiv := extChartAt (𝓡 3) y
  open_source := isOpen_extChartAt_source y
  open_target := isOpen_extChartAt_target y
  contMDiffOn_toFun := by
    simpa only [extChartAt_source] using contMDiffOn_extChartAt (I := 𝓡 3) (x := y)
  contMDiffOn_invFun := contMDiffOn_extChartAt_symm y

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.smoothEuclideanChart
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphericalCutCapTransition.smoothEuclideanChart target :: scope.openDecls } }

theorem isLocalDiffeomorphAt_of_isInteriorPoint_of_bijective_mfderiv
    {N : Type u} [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
    [IsManifold (𝓡 3) ∞ N]
    {f : E.tubes.core → N} (hf : ContMDiff (𝓡∂ 3) (𝓡 3) ∞ f)
    {z : E.tubes.core} (hz : (𝓡∂ 3).IsInteriorPoint z)
    (hbi : Function.Bijective (mfderiv (𝓡∂ 3) (𝓡 3) f z)) :
    IsLocalDiffeomorphAt (𝓡∂ 3) (𝓡 3) ∞ f z := by
  let c : PartialDiffeomorph (𝓡∂ 3) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) E.tubes.core
      (EuclideanSpace ℝ (Fin 3)) ∞ :=
    DifferentialGeometry.Manifold.interiorChart (𝓡∂ 3) ∞ z
  let d := smoothEuclideanChart (f z)
  let V : Set (EuclideanSpace ℝ (Fin 3)) :=
    c.target ∩ (c.symm : EuclideanSpace ℝ (Fin 3) → E.tubes.core)
      ⁻¹' (_root_.Set.univ ∩ f ⁻¹' d.source)
  let K : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) :=
    fun w => d (f (c.symm w))
  have hV : IsOpen V :=
    c.symm.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage c.open_target
      ((hf.contMDiffOn.continuousOn).isOpen_inter_preimage isOpen_univ d.open_source)
  have hzc : z ∈ c.source := by
    rw [DifferentialGeometry.Manifold.mem_interiorChart_source_iff]
    exact hz
  have hczV : c z ∈ V := by
    refine ⟨c.toPartialEquiv.map_source hzc, ?_⟩
    change c.toPartialEquiv.symm (c.toPartialEquiv z) ∈ _root_.Set.univ ∩ f ⁻¹' d.source
    rw [c.toPartialEquiv.left_inv hzc]
    exact ⟨trivial, mem_extChartAt_source (f z)⟩
  have hinner : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (𝓡 3) ∞
      (fun w => f (c.symm w)) V :=
    hf.comp_contMDiffOn (c.contMDiffOn_invFun.mono _root_.Set.inter_subset_left)
  have hK : ContDiffOn ℝ ∞ K V :=
    (d.contMDiffOn_toFun.comp hinner (fun w hw => hw.2.2)).contDiffOn
  have hinvK : (fderiv ℝ K (c z)).IsInvertible := by
    have hKdef : K = writtenInExtChartAt (𝓡∂ 3) (𝓡 3) z f := rfl
    have hcz : c z = extChartAt (𝓡∂ 3) z z := rfl
    rw [hKdef, hcz]
    have hmd : MDifferentiableAt (𝓡∂ 3) (𝓡 3) f z :=
      hf.contMDiffAt.mdifferentiableAt (by simp)
    have hderiv : fderiv ℝ (writtenInExtChartAt (𝓡∂ 3) (𝓡 3) z f)
        (extChartAt (𝓡∂ 3) z z) = mfderiv (𝓡∂ 3) (𝓡 3) f z := by
      rw [hmd.mfderiv]
      exact (fderivWithin_of_mem_nhds (mem_interior_iff_mem_nhds.mp hz)).symm
    rw [hderiv]
    exact ⟨(LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) (𝓡 3) f z).toLinearMap
      hbi).toContinuousLinearEquiv, rfl⟩
  have hevent := eventually_isInvertible_fderiv hV hczV hK hinvK
  have hgood : {w : EuclideanSpace ℝ (Fin 3) | (fderiv ℝ K w).IsInvertible} ∩ V ∈
      𝓝 (c z) :=
    _root_.Filter.inter_mem hevent (hV.mem_nhds hczV)
  obtain ⟨W, hWsub, hW, hczW⟩ := mem_nhds_iff.mp hgood
  refine DifferentialGeometry.Coordinates.isLocalDiffeomorphAt_of_coordinates c d hW hzc hczW
    (fun w hw => (hWsub hw).2.2.2) ?_ ?_
  · exact hK.mono (fun _ hw => (hWsub hw).2)
  · intro w hw
    exact (hWsub hw).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.isLocalDiffeomorphAt_of_isInteriorPoint_of_bijective_mfderiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.isLocalDiffeomorphAt_of_isInteriorPoint_of_bijective_mfderiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.isLocalDiffeomorphAt_of_isInteriorPoint_of_bijective_mfderiv ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.isLocalDiffeomorphAt_of_isInteriorPoint_of_bijective_mfderiv

theorem continuous_uncutCoreInclusion (C : ConnectedComponents M.Carrier)
    (hC : E.cutIndices C = ∅) :
    Continuous (uncutCoreInclusion E C hC) :=
  continuous_subtype_val.subtype_mk _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.continuous_uncutCoreInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.continuous_uncutCoreInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.continuous_uncutCoreInclusion ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.continuous_uncutCoreInclusion

theorem contMDiffAt_uncutCoreInclusion (C : ConnectedComponents M.Carrier)
    (hC : E.cutIndices C = ∅) (y : (M.component C).Carrier) :
    ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (𝓡∂ 3) ∞
      (uncutCoreInclusion E C hC) y := by
  have hcont : ContinuousAt (uncutCoreInclusion E C hC) y :=
    (continuous_uncutCoreInclusion E C hC).continuousAt
  rw [ContMDiffAt.iff_comp_isImmersionAt (φ := (Subtype.val : E.tubes.core → M.Carrier))
    (E.capping.core_induced.isImmersion.isImmersionAt (uncutCoreInclusion E C hC y))]
  exact ⟨hcont, (contMDiff_subtype_val (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))
    (U := ClosedOrientedManifold.componentOpen M C)).contMDiffAt⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.contMDiffAt_uncutCoreInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.contMDiffAt_uncutCoreInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.contMDiffAt_uncutCoreInclusion ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.contMDiffAt_uncutCoreInclusion

theorem isLocalDiffeomorphAt_uncutCoreInclusion (C : ConnectedComponents M.Carrier)
    (hC : E.cutIndices C = ∅) (y : (M.component C).Carrier) :
    IsLocalDiffeomorphAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (𝓡∂ 3) ∞
      (uncutCoreInclusion E C hC) y := by
  have hint : (𝓡∂ 3).IsInteriorPoint (uncutCoreInclusion E C hC y) :=
    E.isInteriorPoint_of_mem_coreComponentSet C hC y.2
  have hg : IsLocalDiffeomorphAt (𝓡∂ 3) (𝓡 3) ∞
      (Subtype.val : E.tubes.core → M.Carrier) (uncutCoreInclusion E C hC y) :=
    E.isLocalDiffeomorphAt_of_isInteriorPoint_of_bijective_mfderiv
      E.capping.core_induced.contMDiff hint
      (E.capping.core_positive (uncutCoreInclusion E C hC y) hint).1
  have hgi : IsLocalDiffeomorphAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (𝓡 3) ∞
      (fun z : (M.component C).Carrier =>
        ((uncutCoreInclusion E C hC z : E.tubes.core) : M.Carrier)) y :=
    (DifferentialGeometry.isLocalDiffeomorph_subtype_val
      (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))
      (U := ClosedOrientedManifold.componentOpen M C)) y
  have hpre : IsLocalDiffeomorphAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (𝓡∂ 3) ∞
      (hg.localInverse ∘ fun z : (M.component C).Carrier =>
        ((uncutCoreInclusion E C hC z : E.tubes.core) : M.Carrier)) y :=
    IsLocalDiffeomorphAt.comp (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) (J := 𝓡 3)
      (K := 𝓡∂ 3) (n := ∞) (hf := hgi) (hg := hg.localInverse_isLocalDiffeomorphAt)
  have hcont : _root_.Filter.Tendsto (uncutCoreInclusion E C hC) (𝓝 y)
      (𝓝 (uncutCoreInclusion E C hC y)) :=
    (continuous_uncutCoreInclusion E C hC).continuousAt
  have heq : (hg.localInverse ∘ fun z : (M.component C).Carrier =>
      ((uncutCoreInclusion E C hC z : E.tubes.core) : M.Carrier)) =ᶠ[𝓝 y]
      (uncutCoreInclusion E C hC) :=
    hcont.eventually hg.localInverse_eventuallyEq_left
  exact DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq heq.symm hpre

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.isLocalDiffeomorphAt_uncutCoreInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.isLocalDiffeomorphAt_uncutCoreInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.isLocalDiffeomorphAt_uncutCoreInclusion ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.isLocalDiffeomorphAt_uncutCoreInclusion

theorem isLocalDiffeomorphAt_coreInclusion (C : ConnectedComponents M.Carrier)
    (hC : E.cutIndices C = ∅) (y : (M.component C).Carrier) :
    IsLocalDiffeomorphAt (𝓡∂ 3) (𝓡 3) ∞ (⇑E.capping.coreInclusion)
      (uncutCoreInclusion E C hC y) :=
  E.isLocalDiffeomorphAt_of_isInteriorPoint_of_bijective_mfderiv
    E.capping.core_embedding.contMDiff
    (E.isInteriorPoint_of_mem_coreComponentSet C hC y.2)
    (E.capping.core_positive (uncutCoreInclusion E C hC y)
      (E.isInteriorPoint_of_mem_coreComponentSet C hC y.2)).2.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.isLocalDiffeomorphAt_coreInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.isLocalDiffeomorphAt_coreInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.isLocalDiffeomorphAt_coreInclusion ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.isLocalDiffeomorphAt_coreInclusion

theorem mdifferentiableAt_uncutCoreInclusion (C : ConnectedComponents M.Carrier)
    (hC : E.cutIndices C = ∅) (y : (M.component C).Carrier) :
    MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (𝓡∂ 3)
      (uncutCoreInclusion E C hC) y :=
  (isLocalDiffeomorphAt_uncutCoreInclusion E C hC y).mdifferentiableAt (by simp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.mdifferentiableAt_uncutCoreInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.mdifferentiableAt_uncutCoreInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.mdifferentiableAt_uncutCoreInclusion ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.mdifferentiableAt_uncutCoreInclusion

theorem mdifferentiableAt_subtypeVal_core (x : E.tubes.core) :
    MDifferentiableAt (𝓡∂ 3) (𝓡 3) (Subtype.val : E.tubes.core → M.Carrier) x :=
  (E.capping.core_induced.contMDiff.contMDiffAt (x := x)).mdifferentiableAt (by simp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.mdifferentiableAt_subtypeVal_core then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.mdifferentiableAt_subtypeVal_core"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.mdifferentiableAt_subtypeVal_core ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.mdifferentiableAt_subtypeVal_core

theorem mfderiv_uncutCoreInclusion (C : ConnectedComponents M.Carrier)
    (hC : E.cutIndices C = ∅) (y : (M.component C).Carrier) :
    (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (𝓡∂ 3)
        (uncutCoreInclusion E C hC) y) =
      (((LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) (𝓡 3)
          (Subtype.val : E.tubes.core → M.Carrier) (uncutCoreInclusion E C hC y)).toLinearMap
        (E.capping.core_positive (uncutCoreInclusion E C hC y)
          (E.isInteriorPoint_of_mem_coreComponentSet C hC y.2)).1).symm.toContinuousLinearEquiv :
        TangentSpace (𝓡 3) ((uncutCoreInclusion E C hC y : E.tubes.core) : M.Carrier) →L[ℝ]
          TangentSpace (𝓡∂ 3) (uncutCoreInclusion E C hC y))) := by
  obtain ⟨hi, -, -⟩ := E.capping.core_positive (uncutCoreInclusion E C hC y)
    (E.isInteriorPoint_of_mem_coreComponentSet C hC y.2)
  apply ContinuousLinearMap.ext
  intro v
  have hchain := mfderiv_comp
    (g := (Subtype.val : E.tubes.core → M.Carrier)) (f := uncutCoreInclusion E C hC)
    (x := y) (mdifferentiableAt_subtypeVal_core E (uncutCoreInclusion E C hC y))
    (mdifferentiableAt_uncutCoreInclusion E C hC y)
  have hval := congrArg (fun L => L v) hchain
  have hfun : ((Subtype.val : E.tubes.core → M.Carrier) ∘ uncutCoreInclusion E C hC) =
      (Subtype.val : (M.component C).Carrier → M.Carrier) := rfl
  rw [hfun] at hval
  have hsub_apply : (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (𝓡 3)
      (Subtype.val : (M.component C).Carrier → M.Carrier) y) v = v :=
    DifferentialGeometry.mfderiv_subtype_val_apply
      (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))
      (U := ClosedOrientedManifold.componentOpen M C) y v
  have hv : (mfderiv (𝓡∂ 3) (𝓡 3) (Subtype.val : E.tubes.core → M.Carrier)
      (uncutCoreInclusion E C hC y))
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (𝓡∂ 3)
        (uncutCoreInclusion E C hC) y v) = v := by
    have h2 : (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (𝓡 3)
        (Subtype.val : (M.component C).Carrier → M.Carrier) y) v =
        ((mfderiv (𝓡∂ 3) (𝓡 3) (Subtype.val : E.tubes.core → M.Carrier)
          (uncutCoreInclusion E C hC y)).comp
          (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (𝓡∂ 3)
            (uncutCoreInclusion E C hC) y)) v := hval
    exact h2.symm.trans hsub_apply
  exact (LinearEquiv.eq_symm_apply _).mpr hv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.mfderiv_uncutCoreInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.mfderiv_uncutCoreInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.mfderiv_uncutCoreInclusion ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.mfderiv_uncutCoreInclusion

def uncutMap (C : ConnectedComponents M.Carrier) (hC : E.cutIndices C = ∅)
    (x : E.tubes.core) (hx : x ∈ E.coreComponentSet C) :
    (M.component C).Carrier →
      (E.capped.component (ConnectedComponents.mk (E.capping.coreInclusion x))).Carrier :=
  fun y => ⟨E.capping.coreInclusion (uncutCoreInclusion E C hC y), by
    change E.capping.coreInclusion (uncutCoreInclusion E C hC y) ∈
      E.capped.componentSet (ConnectedComponents.mk (E.capping.coreInclusion x))
    rw [← E.image_coreComponentSet_eq_componentSet C hC hx]
    exact ⟨uncutCoreInclusion E C hC y, y.2, rfl⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.uncutMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.uncutMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.uncutMap ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.uncutMap

theorem uncutMap_apply (C : ConnectedComponents M.Carrier) (hC : E.cutIndices C = ∅)
    (x : E.tubes.core) (hx : x ∈ E.coreComponentSet C) (y : (M.component C).Carrier) :
    (uncutMap E C hC x hx y).1 = E.capping.coreInclusion (uncutCoreInclusion E C hC y) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.uncutMap_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.uncutMap_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.uncutMap_apply ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.uncutMap_apply

theorem isLocalDiffeomorphAt_uncutMap (C : ConnectedComponents M.Carrier)
    (hC : E.cutIndices C = ∅) (x : E.tubes.core) (hx : x ∈ E.coreComponentSet C)
    (y : (M.component C).Carrier) :
    IsLocalDiffeomorphAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
      𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞ (uncutMap E C hC x hx) y := by
  have hcomp : IsLocalDiffeomorphAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (𝓡 3) ∞
      (fun z : (M.component C).Carrier =>
        E.capping.coreInclusion (uncutCoreInclusion E C hC z)) y :=
    IsLocalDiffeomorphAt.comp (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) (J := 𝓡∂ 3)
      (K := 𝓡 3) (n := ∞) (hf := isLocalDiffeomorphAt_uncutCoreInclusion E C hC y)
      (hg := isLocalDiffeomorphAt_coreInclusion E C hC y)
  have hres := DifferentialGeometry.isLocalDiffeomorphAt_subtypeCodRestrict
    (V := ClosedOrientedManifold.componentOpen E.capped
      (ConnectedComponents.mk (E.capping.coreInclusion x)))
    (f := fun z : (M.component C).Carrier =>
      E.capping.coreInclusion (uncutCoreInclusion E C hC z)) (fun z => ?_) hcomp
  · convert hres using 1 <;> try rfl
  · change E.capping.coreInclusion (uncutCoreInclusion E C hC z) ∈
      E.capped.componentSet (ConnectedComponents.mk (E.capping.coreInclusion x))
    rw [← E.image_coreComponentSet_eq_componentSet C hC hx]
    exact ⟨uncutCoreInclusion E C hC z, z.2, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.isLocalDiffeomorphAt_uncutMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.isLocalDiffeomorphAt_uncutMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.isLocalDiffeomorphAt_uncutMap ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.isLocalDiffeomorphAt_uncutMap

theorem contMDiff_uncutMap (C : ConnectedComponents M.Carrier) (hC : E.cutIndices C = ∅)
    (x : E.tubes.core) (hx : x ∈ E.coreComponentSet C) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞
      (uncutMap E C hC x hx) :=
  fun y => (isLocalDiffeomorphAt_uncutMap E C hC x hx y).contMDiffAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.contMDiff_uncutMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.contMDiff_uncutMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.contMDiff_uncutMap ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.contMDiff_uncutMap

theorem uncutMap_injective (C : ConnectedComponents M.Carrier) (hC : E.cutIndices C = ∅)
    (x : E.tubes.core) (hx : x ∈ E.coreComponentSet C) :
    Function.Injective (uncutMap E C hC x hx) := by
  intro y y' h
  have hcoe : E.capping.coreInclusion (uncutCoreInclusion E C hC y) =
      E.capping.coreInclusion (uncutCoreInclusion E C hC y') := congrArg Subtype.val h
  have hcore : uncutCoreInclusion E C hC y = uncutCoreInclusion E C hC y' :=
    E.capping.core_embedding.isEmbedding.injective hcoe
  exact Subtype.ext (congrArg (fun z : E.tubes.core => (z : M.Carrier)) hcore)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.uncutMap_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.uncutMap_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.uncutMap_injective ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.uncutMap_injective

theorem uncutMap_surjective (C : ConnectedComponents M.Carrier) (hC : E.cutIndices C = ∅)
    (x : E.tubes.core) (hx : x ∈ E.coreComponentSet C) :
    Function.Surjective (uncutMap E C hC x hx) := by
  intro z
  have hz : z.1 ∈ E.capping.coreInclusion '' E.coreComponentSet C := by
    have hz' : z.1 ∈ E.capped.componentSet
        (ConnectedComponents.mk (E.capping.coreInclusion x)) := z.2
    rwa [← E.image_coreComponentSet_eq_componentSet C hC hx] at hz'
  obtain ⟨w, hw, hweq⟩ := hz
  exact ⟨⟨(w : M.Carrier), hw⟩, Subtype.ext hweq⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.uncutMap_surjective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.uncutMap_surjective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.uncutMap_surjective ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.uncutMap_surjective

theorem uncutMap_bijective (C : ConnectedComponents M.Carrier) (hC : E.cutIndices C = ∅)
    (x : E.tubes.core) (hx : x ∈ E.coreComponentSet C) :
    Function.Bijective (uncutMap E C hC x hx) :=
  ⟨uncutMap_injective E C hC x hx, uncutMap_surjective E C hC x hx⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.uncutMap_bijective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.uncutMap_bijective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.uncutMap_bijective ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.uncutMap_bijective

noncomputable def uncutMapDiffeomorph (C : ConnectedComponents M.Carrier)
    (hC : E.cutIndices C = ∅) (x : E.tubes.core) (hx : x ∈ E.coreComponentSet C) :
    Diffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
      (M.component C).Carrier
      (E.capped.component (ConnectedComponents.mk (E.capping.coreInclusion x))).Carrier ∞ :=
  IsLocalDiffeomorph.diffeomorphOfBijective
    (fun y => isLocalDiffeomorphAt_uncutMap E C hC x hx y) (uncutMap_bijective E C hC x hx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.uncutMapDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.uncutMapDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.uncutMapDiffeomorph ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.uncutMapDiffeomorph

theorem mfderiv_uncutMap (C : ConnectedComponents M.Carrier) (hC : E.cutIndices C = ∅)
    (x : E.tubes.core) (hx : x ∈ E.coreComponentSet C) (y : (M.component C).Carrier) :
    (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
        (uncutMap E C hC x hx) y) =
      ((mfderiv (𝓡∂ 3) (𝓡 3) (⇑E.capping.coreInclusion)
          (uncutCoreInclusion E C hC y)).comp
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (𝓡∂ 3)
          (uncutCoreInclusion E C hC) y)) := by
  have hdiff : MDifferentiableAt (𝓡∂ 3) (𝓡 3) (⇑E.capping.coreInclusion)
      (uncutCoreInclusion E C hC y) :=
    (E.capping.core_embedding.contMDiff.contMDiffAt
      (x := uncutCoreInclusion E C hC y)).mdifferentiableAt (by simp)
  have hchain := mfderiv_comp (x := y) (g := (⇑E.capping.coreInclusion))
    (f := uncutCoreInclusion E C hC) hdiff (mdifferentiableAt_uncutCoreInclusion E C hC y)
  have hfun : ((⇑E.capping.coreInclusion) ∘ uncutCoreInclusion E C hC) =
      (fun z : (M.component C).Carrier => (uncutMap E C hC x hx z).1) := rfl
  rw [hfun] at hchain
  have hsub := DifferentialGeometry.mfderiv_subtypeVal_comp
    (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))
    (U := ClosedOrientedManifold.componentOpen E.capped
      (ConnectedComponents.mk (E.capping.coreInclusion x)))
    (f := uncutMap E C hC x hx) y
  exact hsub.symm.trans hchain

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.mfderiv_uncutMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.mfderiv_uncutMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.mfderiv_uncutMap ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.mfderiv_uncutMap
theorem uncutMapDiffeomorph_preservesOrientation (C : ConnectedComponents M.Carrier)
    (hC : E.cutIndices C = ∅) (x : E.tubes.core) (hx : x ∈ E.coreComponentSet C) :
    (uncutMapDiffeomorph E C hC x hx).preservesOrientation
      (M.component C).orientation
      (E.capped.component (ConnectedComponents.mk (E.capping.coreInclusion x))).orientation := by
  intro y
  obtain ⟨hi, hj, hpos⟩ := E.capping.core_positive (uncutCoreInclusion E C hC y)
    (E.isInteriorPoint_of_mem_coreComponentSet C hC y.2)
  let A : TangentSpace (𝓡∂ 3) (uncutCoreInclusion E C hC y) ≃ₗ[ℝ]
      TangentSpace (𝓡 3) ((uncutCoreInclusion E C hC y : E.tubes.core) : M.Carrier) :=
    LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) (𝓡 3)
      (Subtype.val : E.tubes.core → M.Carrier) (uncutCoreInclusion E C hC y)).toLinearMap hi
  let B : TangentSpace (𝓡∂ 3) (uncutCoreInclusion E C hC y) ≃ₗ[ℝ]
      TangentSpace (𝓡 3) (E.capping.coreInclusion (uncutCoreInclusion E C hC y)) :=
    LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) (𝓡 3) (⇑E.capping.coreInclusion)
      (uncutCoreInclusion E C hC y)).toLinearMap hj
  have hL : (((uncutMapDiffeomorph E C hC x hx).mfderivToContinuousLinearEquiv (by simp)
        y).toLinearEquiv :
      TangentSpace (𝓡 3) y.1 ≃ₗ[ℝ]
        TangentSpace (𝓡 3) (E.capping.coreInclusion (uncutCoreInclusion E C hC y))) =
      (A.symm.trans B :
        TangentSpace (𝓡 3) y.1 ≃ₗ[ℝ]
          TangentSpace (𝓡 3) (E.capping.coreInclusion (uncutCoreInclusion E C hC y))) := by
    apply LinearEquiv.ext
    intro v
    change (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
      (uncutMap E C hC x hx) y) v = (A.symm.trans B) v
    rw [mfderiv_uncutMap E C hC x hx y]
    rw [mfderiv_uncutCoreInclusion E C hC y]
    rfl
  rw [hL]
  rw [show (uncutMapDiffeomorph E C hC x hx) y = uncutMap E C hC x hx y from rfl]
  have hleft : ((M.component C).orientation).orientation y = M.orientation.orientation y.1 :=
    ClosedOrientedManifold.componentTangentOrientation_apply M C y
  have hright : ((E.capped.component
        (ConnectedComponents.mk (E.capping.coreInclusion x))).orientation).orientation
        (uncutMap E C hC x hx y) =
      E.capped.orientation.orientation
        (E.capping.coreInclusion (uncutCoreInclusion E C hC y)) := by
    change ClosedOrientedManifold.componentTangentOrientation E.capped
      (ConnectedComponents.mk (E.capping.coreInclusion x)) (uncutMap E C hC x hx y) = _
    have hct := ClosedOrientedManifold.componentTangentOrientation_apply E.capped
      (ConnectedComponents.mk (E.capping.coreInclusion x)) (uncutMap E C hC x hx y)
    exact hct.trans (by rw [uncutMap_apply])
  rw [hleft, hright]
  exact hpos

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.uncutMapDiffeomorph_preservesOrientation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.uncutMapDiffeomorph_preservesOrientation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.uncutMapDiffeomorph_preservesOrientation ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.uncutMapDiffeomorph_preservesOrientation

theorem uncutCappingRealization : E.UncutCappingRealization := by
  intro C hC x hx
  exact ⟨⟨uncutMapDiffeomorph E C hC x hx,
    uncutMapDiffeomorph_preservesOrientation E C hC x hx⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.uncutCappingRealization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.uncutCappingRealization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.uncutCappingRealization ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.uncutCappingRealization

theorem noTubeRealization_of_cappedPresentationRealization
    (h : E.CappedPresentationRealization) : E.NoTubeRealization :=
  E.noTubeRealization_of_uncutCappingRealization_of_cappedPresentationRealization
    E.uncutCappingRealization h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.noTubeRealization_of_cappedPresentationRealization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.noTubeRealization_of_cappedPresentationRealization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.noTubeRealization_of_cappedPresentationRealization ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.noTubeRealization_of_cappedPresentationRealization

theorem noTubeRealization_of_retained_of_discarded_cappedPresentation
    (h₁ : E.CappedRetainedPresentationRealization)
    (h₂ : E.CappedDiscardedPresentationRealization) : E.NoTubeRealization :=
  E.noTubeRealization_of_uncutCappingRealization_of_retained_of_discarded
    E.uncutCappingRealization h₁ h₂

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.noTubeRealization_of_retained_of_discarded_cappedPresentation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.noTubeRealization_of_retained_of_discarded_cappedPresentation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.noTubeRealization_of_retained_of_discarded_cappedPresentation ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.noTubeRealization_of_retained_of_discarded_cappedPresentation

theorem isPoincareStandard_of_capped (C : ConnectedComponents M.Carrier)
    (hC : E.cutIndices C = ∅) (x : E.tubes.core) (hx : x ∈ E.coreComponentSet C)
    (hstd : isPoincareStandard ((E.capped.component
      (ConnectedComponents.mk (E.capping.coreInclusion x))).toClosedOrientedManifold).Carrier) :
    isPoincareStandard (M.component C).Carrier :=
  E.isPoincareStandard_of_capped_of_uncutCappingRealization E.uncutCappingRealization
    C hC x hx hstd

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.isPoincareStandard_of_capped then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.isPoincareStandard_of_capped"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.isPoincareStandard_of_capped ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.isPoincareStandard_of_capped

theorem noTubeRealization : E.NoTubeRealization :=
  E.noTubeRealization_of_uncutCappingRealization E.uncutCappingRealization

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.noTubeRealization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.noTubeRealization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.noTubeRealization ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.noTubeRealization

theorem graphSumRealization_iff_cutComponentRealization :
    E.graphSumRealization ↔ E.cutComponentRealization :=
  E.graphSumRealization_iff_noTubeRealization_and_cutComponentRealization.trans
    ⟨fun h => h.2, fun h => ⟨E.noTubeRealization, h⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.graphSumRealization_iff_cutComponentRealization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.graphSumRealization_iff_cutComponentRealization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.graphSumRealization_iff_cutComponentRealization ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.graphSumRealization_iff_cutComponentRealization

theorem componentConnectedSumDecomposition_iff_cutComponentRealization :
    E.componentConnectedSumDecomposition ↔ E.cutComponentRealization :=
  E.componentConnectedSumDecomposition_iff_noTubeRealization_and_cutComponentRealization.trans
    ⟨fun h => h.2, fun h => ⟨E.noTubeRealization, h⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.componentConnectedSumDecomposition_iff_cutComponentRealization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.componentConnectedSumDecomposition_iff_cutComponentRealization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.componentConnectedSumDecomposition_iff_cutComponentRealization ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.componentConnectedSumDecomposition_iff_cutComponentRealization

theorem exists_core_presentation_eq_inr_component_of_isEmpty_index [IsEmpty E.tubes.Index]
    (D : ConnectedComponents E.discarded.Carrier) :
    ∃ (x : E.tubes.core) (d : E.discarded.Carrier),
      ConnectedComponents.mk d = D ∧
        E.presentation (E.capping.coreInclusion x) = Sum.inr d ∧
        x ∈ E.coreComponentSet (ConnectedComponents.mk x.val) ∧
        E.cutIndices (ConnectedComponents.mk x.val) = ∅ := by
  obtain ⟨d, hd⟩ := ConnectedComponents.surjective_coe D
  obtain ⟨x, hx⟩ := Set.range_eq_univ.mp E.range_coreInclusion_eq_univ_of_isEmpty_index
    (E.presentation.symm (Sum.inr d))
  have hxd : E.presentation (E.capping.coreInclusion x) = Sum.inr d := by
    rw [hx, E.presentation.apply_symm_apply]
  exact ⟨x, d, hd, hxd, (ClosedOrientedManifold.mem_componentSet M _ _).mpr rfl,
    E.exists_cutIndices_eq_empty_of_isEmpty_index _⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.exists_core_presentation_eq_inr_component_of_isEmpty_index then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.exists_core_presentation_eq_inr_component_of_isEmpty_index"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.exists_core_presentation_eq_inr_component_of_isEmpty_index ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.exists_core_presentation_eq_inr_component_of_isEmpty_index


theorem isPoincareStandard_discardedComponent_of_cutIndices_eq_empty
    (C : ConnectedComponents M.Carrier) (hC : E.cutIndices C = ∅)
    (x : E.tubes.core) (hx : x ∈ E.coreComponentSet C)
    (d : E.discarded.Carrier)
    (hd : E.presentation (E.capping.coreInclusion x) = Sum.inr d)
    (hstd : isPoincareStandard (M.component C).Carrier) :
    isPoincareStandard (E.discarded.component (ConnectedComponents.mk d)).Carrier := by
  obtain ⟨e⟩ := E.uncutCappingRealization C hC x hx
  obtain ⟨f⟩ := E.cappedDiscardedPresentationRealization x d hd
  exact isPoincareStandard_of_diffeomorph (e.val.trans f.val).symm hstd

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.isPoincareStandard_discardedComponent_of_cutIndices_eq_empty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.isPoincareStandard_discardedComponent_of_cutIndices_eq_empty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.isPoincareStandard_discardedComponent_of_cutIndices_eq_empty ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.isPoincareStandard_discardedComponent_of_cutIndices_eq_empty


end SphericalCutCapTransition

end DifferentialGeometry.Topology
