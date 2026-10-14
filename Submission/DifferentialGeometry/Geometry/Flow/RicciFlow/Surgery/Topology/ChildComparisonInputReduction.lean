import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildComparisonAssembly
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildComparisonCanonicalSupport
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildComparisonFrontierReduction
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildParentReduction
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildSimplicityFrontierReduction
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.PuncturedCoreTwoCover

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology

theorem exists_eq_zsmul_and_exists_linearMap_eq_one_not_pos :
    ∃ (k : ℤ) (x y : ℤ), x = k • y ∧ ¬ 0 < k ∧ ∃ φ : ℤ →ₗ[ℤ] ℤ, φ x = 1 :=
  ⟨-1, 1, -1, by norm_num [zsmul_eq_mul], by norm_num, ⟨LinearMap.id, rfl⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_eq_zsmul_and_exists_linearMap_eq_one_not_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_eq_zsmul_and_exists_linearMap_eq_one_not_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_eq_zsmul_and_exists_linearMap_eq_one_not_pos ``Submission.DifferentialGeometry.Topology.exists_eq_zsmul_and_exists_linearMap_eq_one_not_pos

end DifferentialGeometry.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace TubeSystem

variable {M : Type u} [TopologicalSpace M] (T : TubeSystem M)

namespace PuncturedCoreCutChain

def ofSimplyConnectedComponent (c : ConnectedComponents ↥T.core)
    (h : SimplyConnectedSpace ↥(T.puncturedCoreComponent c)) : T.PuncturedCoreCutChain c where
  n := 0
  W := fun _ => T.puncturedCoreComponent c
  L := fun _ => _root_.Set.univ
  R := fun _ => _root_.Set.univ
  isOpen_L := fun _ => isOpen_univ
  isOpen_R := fun _ => isOpen_univ
  cover := fun _ => by simp
  next := fun _ => Or.inl (by simp)
  simplyConnected_overlap := fun _ => by
    rw [Set.inter_univ, Set.inter_univ]
    exact h
  pathConnected_left := fun _ => by
    rw [Set.inter_univ]
    let _ : SimplyConnectedSpace ↥(T.puncturedCoreComponent c) := h
    infer_instance
  pathConnected_right := fun _ => by
    rw [Set.inter_univ]
    let _ : SimplyConnectedSpace ↥(T.puncturedCoreComponent c) := h
    infer_instance
  terminal := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.PuncturedCoreCutChain.ofSimplyConnectedComponent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.PuncturedCoreCutChain.ofSimplyConnectedComponent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.PuncturedCoreCutChain.ofSimplyConnectedComponent ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.PuncturedCoreCutChain.ofSimplyConnectedComponent

end PuncturedCoreCutChain

end TubeSystem

namespace SmoothCutCapTransition

variable {P Q D N : OrientedThreeStage.{u}} (E : SmoothCutCapTransition P Q D N)

theorem puncturedCoreCutChainProducer_iff_middleSphereCuttingSeparation :
    E.PuncturedCoreCutChainProducer ↔ E.middleSphereCuttingSeparation :=
  ⟨E.middleSphereCuttingSeparation_of_cutChainProducer, fun h c hpar =>
    ⟨TubeSystem.PuncturedCoreCutChain.ofSimplyConnectedComponent E.trace.tubes
      (E.childCoreComponent c) (h c hpar), h c hpar⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.puncturedCoreCutChainProducer_iff_middleSphereCuttingSeparation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.puncturedCoreCutChainProducer_iff_middleSphereCuttingSeparation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.puncturedCoreCutChainProducer_iff_middleSphereCuttingSeparation ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.puncturedCoreCutChainProducer_iff_middleSphereCuttingSeparation

theorem childSimplicityFrontier_iff_childCollaredStarCoverProducer_and_puncturedCoreCutChainProducer :
    E.ChildSimplicityFrontier ↔ E.childCollaredStarCoverProducer ∧ E.PuncturedCoreCutChainProducer := by
  constructor
  · rintro ⟨hcover, hsep⟩
    exact ⟨hcover, E.puncturedCoreCutChainProducer_iff_middleSphereCuttingSeparation.mpr hsep⟩
  · rintro ⟨hcover, hchain⟩
    exact ⟨hcover, E.puncturedCoreCutChainProducer_iff_middleSphereCuttingSeparation.mp hchain⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childSimplicityFrontier_iff_childCollaredStarCoverProducer_and_puncturedCoreCutChainProducer then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childSimplicityFrontier_iff_childCollaredStarCoverProducer_and_puncturedCoreCutChainProducer"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childSimplicityFrontier_iff_childCollaredStarCoverProducer_and_puncturedCoreCutChainProducer ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childSimplicityFrontier_iff_childCollaredStarCoverProducer_and_puncturedCoreCutChainProducer

theorem not_nonempty_childCarrierCollaredStarCover_of_not_simplyConnectedSpace
    (c : ConnectedComponents Q.Carrier) (hcore : SimplyConnectedSpace (E.ChildCore c))
    (hcar : ¬ SimplyConnectedSpace (E.ChildCarrier c)) :
    ¬ Nonempty (E.ChildCarrierCollaredStarCover c) :=
  fun hd => hcar (E.simplyConnectedSpace_childCarrier_of_collaredStarCover c hcore hd.some)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.not_nonempty_childCarrierCollaredStarCover_of_not_simplyConnectedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.not_nonempty_childCarrierCollaredStarCover_of_not_simplyConnectedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.not_nonempty_childCarrierCollaredStarCover_of_not_simplyConnectedSpace ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.not_nonempty_childCarrierCollaredStarCover_of_not_simplyConnectedSpace

theorem not_nonempty_childCarrierCollaredStarCover_of_capRange_eq_univ
    (c : ConnectedComponents Q.Carrier) {b₁ b₂ : E.ChildCapBoundary c} (hne : b₁ ≠ b₂)
    (huniv : (⋃ b : E.ChildCapBoundary c, Set.range (E.childCap c b)) = Set.univ)
    (hcore : SimplyConnectedSpace (E.ChildCore c)) :
    ¬ Nonempty (E.ChildCarrierCollaredStarCover c) :=
  E.not_nonempty_childCarrierCollaredStarCover_of_not_simplyConnectedSpace c hcore
    (not_simplyConnectedSpace_childCarrier_of_capRange_eq_univ E c hne huniv)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.not_nonempty_childCarrierCollaredStarCover_of_capRange_eq_univ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.not_nonempty_childCarrierCollaredStarCover_of_capRange_eq_univ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.not_nonempty_childCarrierCollaredStarCover_of_capRange_eq_univ ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.not_nonempty_childCarrierCollaredStarCover_of_capRange_eq_univ

theorem not_nonempty_childCarrierCollaredStarCover_of_middleSphereCuttingSeparation
    (hmiddle : E.middleSphereCuttingSeparation) (c : ConnectedComponents Q.Carrier)
    [SimplyConnectedSpace (P.component (E.childParent c)).Carrier]
    {b₁ b₂ : E.ChildCapBoundary c} (hne : b₁ ≠ b₂)
    (huniv : (⋃ b : E.ChildCapBoundary c, Set.range (E.childCap c b)) = Set.univ) :
    ¬ Nonempty (E.ChildCarrierCollaredStarCover c) :=
  E.not_nonempty_childCarrierCollaredStarCover_of_capRange_eq_univ c hne huniv
    ((E.simplyConnectedSpace_puncturedCoreComponent_iff_childCore c).mp (hmiddle c inferInstance))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.not_nonempty_childCarrierCollaredStarCover_of_middleSphereCuttingSeparation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.not_nonempty_childCarrierCollaredStarCover_of_middleSphereCuttingSeparation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.not_nonempty_childCarrierCollaredStarCover_of_middleSphereCuttingSeparation ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.not_nonempty_childCarrierCollaredStarCover_of_middleSphereCuttingSeparation

end SmoothCutCapTransition

namespace GeometricCutoffRecord

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
  (G : GeometricCutoffRecord H i parameters)

structure ChildComparisonReducedInputs
    (a : (c : ConnectedComponents (H.stage i.succ).Carrier) →
      IntegralHomology (G.Parent c).Carrier 3)
    (b : (c : ConnectedComponents (H.stage i.succ).Carrier) →
      IntegralHomology (G.Child c).Carrier 3) where
  Kc : (c : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c
  distanceControl : ∀ c : ConnectedComponents (H.stage i.succ).Carrier,
    (Kc c).LocalTerminalDistanceControl (Kc c).rfs_whole_parent_map
  convergenceTime : ℝ
  convergenceTime_mem : convergenceTime ∈ _root_.Set.Ico (H.time i.castSucc) (H.time i.succ)
  scale : ℝ → ℝ
  scale_one : ∀ s ∈ _root_.Set.Ioo convergenceTime (H.time i.succ), 1 ≤ scale s
  scale_tendsto : Filter.Tendsto scale (𝓝[<] (H.time i.succ)) (𝓝 1)
  localEDist : G.LocalEDistComparison Kc convergenceTime scale
  multiplier : (c : ConnectedComponents (H.stage i.succ).Carrier) → ℤ
  map_eq : ∀ c : ConnectedComponents (H.stage i.succ).Carrier,
    integralHomologyMap 3 (Kc c).rfs_whole_parent_map (a c) = multiplier c • b c
  generator : ∀ c : ConnectedComponents (H.stage i.succ).Carrier,
    ∃ φ : IntegralHomology (G.Child c).Carrier 3 →ₗ[ℤ] ℤ,
      φ (integralHomologyMap 3 (Kc c).rfs_whole_parent_map (a c)) = 1
  positive : ∀ c : ConnectedComponents (H.stage i.succ).Carrier, 0 < multiplier c

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ChildComparisonReducedInputs then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ChildComparisonReducedInputs"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ChildComparisonReducedInputs ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ChildComparisonReducedInputs

variable {G}

def ChildComparisonInputs.toReducedInputs
    {a : (c : ConnectedComponents (H.stage i.succ).Carrier) →
      IntegralHomology (G.Parent c).Carrier 3}
    {b : (c : ConnectedComponents (H.stage i.succ).Carrier) →
      IntegralHomology (G.Child c).Carrier 3}
    (h : G.ChildComparisonInputs a b) : G.ChildComparisonReducedInputs a b where
  Kc := h.Kc
  distanceControl := fun c =>
    ComparisonSupport.localTerminalDistanceControl_of_localTerminalEDistComparison
      (c := c) h.Kc h.collapse
  convergenceTime := h.convergenceTime
  convergenceTime_mem := h.convergenceTime_mem
  scale := h.scale
  scale_one := h.scale_one
  scale_tendsto := h.scale_tendsto
  localEDist := G.localEDistComparison_of_terminal_comparisons h.Kc h.collapse h.convergence
  multiplier := h.multiplier
  map_eq := h.map_eq
  generator := h.generator
  positive := h.positive

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ChildComparisonInputs.toReducedInputs then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ChildComparisonInputs.toReducedInputs"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ChildComparisonInputs.toReducedInputs ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ChildComparisonInputs.toReducedInputs

theorem rfs_child_comparison_of_reducedInputs
    (a : (c : ConnectedComponents (H.stage i.succ).Carrier) →
      IntegralHomology (G.Parent c).Carrier 3)
    (b : (c : ConnectedComponents (H.stage i.succ).Carrier) →
      IntegralHomology (G.Child c).Carrier 3)
    (h : G.ChildComparisonReducedInputs a b) :
    ∃ f : (c : ConnectedComponents (H.stage i.succ).Carrier) →
        C((G.Parent c).Carrier, (G.Child c).Carrier),
      (∀ c, ∃ K : G.ComparisonSupport c, f c = K.rfs_whole_parent_map) ∧
      (∀ c, integralHomologyMap 3 (f c) (a c) = b c) ∧
      ∃ s₀ ∈ _root_.Set.Ico (H.time i.castSucc) (H.time i.succ), ∃ ell : ℝ → ℝ,
        (∀ s ∈ _root_.Set.Ioo s₀ (H.time i.succ), 1 ≤ ell s) ∧
        Filter.Tendsto ell (𝓝[<] (H.time i.succ)) (𝓝 1) ∧
        ∀ c, ∀ s ∈ _root_.Set.Ioo s₀ (H.time i.succ), ∀ x y : (G.Parent c).Carrier,
          riemannianEDistOf ((H.stage i.succ).componentMetric (H.event i).outputMetric c)
            (f c x) (f c y) ≤ ENNReal.ofReal (ell s) *
            riemannianEDistOf ((H.stage i.castSucc).componentMetric
              ((H.event i).incoming.flow.base.metric s) (G.transition.childParent c)) x y := by
  obtain ⟨f, hf, hlen⟩ := G.rfs_child_comparison_metric_of_local_length_comparison h.Kc
    (G.localLengthComparison_of_localEDistComparison h.Kc h.convergenceTime_mem h.localEDist
      h.scale_one h.scale_tendsto)
  refine ⟨f, fun c => ⟨h.Kc c, hf c⟩, fun c => ?_, hlen⟩
  rw [hf c]
  exact (ComparisonSupport.rfs_collapse_degree_of_localTerminalDistanceControl_and_class_generator
    (K := h.Kc c) (a c) (b c) (h.distanceControl c) (h.map_eq c) (h.generator c)
    (h.positive c)).2.2.2.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.rfs_child_comparison_of_reducedInputs then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.rfs_child_comparison_of_reducedInputs"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.rfs_child_comparison_of_reducedInputs ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.rfs_child_comparison_of_reducedInputs

theorem rfs_child_comparison_of_canonicalReducedInputs
    (hSC : ∀ p : ConnectedComponents (H.stage i.castSucc).Carrier,
      SimplyConnectedSpace ((H.stage i.castSucc).component p).Carrier)
    (a : (c : ConnectedComponents (H.stage i.succ).Carrier) →
      IntegralHomology (G.Parent c).Carrier 3)
    (b : (c : ConnectedComponents (H.stage i.succ).Carrier) →
      IntegralHomology (G.Child c).Carrier 3)
    (hdistanceControl : ∀ c : ConnectedComponents (H.stage i.succ).Carrier,
      (G.canonicalComparisonSupport hSC c).LocalTerminalDistanceControl
        (G.canonicalComparisonSupport hSC c).rfs_whole_parent_map)
    (convergenceTime : ℝ)
    (hconvergenceTime : convergenceTime ∈ _root_.Set.Ico (H.time i.castSucc) (H.time i.succ))
    (scale : ℝ → ℝ)
    (hscale_one : ∀ s ∈ _root_.Set.Ioo convergenceTime (H.time i.succ), 1 ≤ scale s)
    (hscale_tendsto : Filter.Tendsto scale (𝓝[<] (H.time i.succ)) (𝓝 1))
    (hlocalEDist : G.LocalEDistComparison (G.canonicalComparisonSupport hSC) convergenceTime scale)
    (multiplier : (c : ConnectedComponents (H.stage i.succ).Carrier) → ℤ)
    (hmap : ∀ c : ConnectedComponents (H.stage i.succ).Carrier,
      integralHomologyMap 3 (G.canonicalComparisonSupport hSC c).rfs_whole_parent_map (a c) =
        multiplier c • b c)
    (hgenerator : ∀ c : ConnectedComponents (H.stage i.succ).Carrier,
      ∃ φ : IntegralHomology (G.Child c).Carrier 3 →ₗ[ℤ] ℤ,
        φ (integralHomologyMap 3 (G.canonicalComparisonSupport hSC c).rfs_whole_parent_map
          (a c)) = 1)
    (hpositive : ∀ c : ConnectedComponents (H.stage i.succ).Carrier, 0 < multiplier c) :
    ∃ f : (c : ConnectedComponents (H.stage i.succ).Carrier) →
        C((G.Parent c).Carrier, (G.Child c).Carrier),
      (∀ c, ∃ K : G.ComparisonSupport c, f c = K.rfs_whole_parent_map) ∧
      (∀ c, integralHomologyMap 3 (f c) (a c) = b c) ∧
      ∃ s₀ ∈ _root_.Set.Ico (H.time i.castSucc) (H.time i.succ), ∃ ell : ℝ → ℝ,
        (∀ s ∈ _root_.Set.Ioo s₀ (H.time i.succ), 1 ≤ ell s) ∧
        Filter.Tendsto ell (𝓝[<] (H.time i.succ)) (𝓝 1) ∧
        ∀ c, ∀ s ∈ _root_.Set.Ioo s₀ (H.time i.succ), ∀ x y : (G.Parent c).Carrier,
          riemannianEDistOf ((H.stage i.succ).componentMetric (H.event i).outputMetric c)
            (f c x) (f c y) ≤ ENNReal.ofReal (ell s) *
            riemannianEDistOf ((H.stage i.castSucc).componentMetric
              ((H.event i).incoming.flow.base.metric s) (G.transition.childParent c)) x y :=
  G.rfs_child_comparison_of_reducedInputs a b
    { Kc := G.canonicalComparisonSupport hSC
      distanceControl := hdistanceControl
      convergenceTime := convergenceTime
      convergenceTime_mem := hconvergenceTime
      scale := scale
      scale_one := hscale_one
      scale_tendsto := hscale_tendsto
      localEDist := hlocalEDist
      multiplier := multiplier
      map_eq := hmap
      generator := hgenerator
      positive := hpositive }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.rfs_child_comparison_of_canonicalReducedInputs then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.rfs_child_comparison_of_canonicalReducedInputs"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.rfs_child_comparison_of_canonicalReducedInputs ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.rfs_child_comparison_of_canonicalReducedInputs

theorem rfs_child_comparison_of_canonicalTerminalInputs
    (hSC : ∀ p : ConnectedComponents (H.stage i.castSucc).Carrier,
      SimplyConnectedSpace ((H.stage i.castSucc).component p).Carrier)
    (a : (c : ConnectedComponents (H.stage i.succ).Carrier) →
      IntegralHomology (G.Parent c).Carrier 3)
    (b : (c : ConnectedComponents (H.stage i.succ).Carrier) →
      IntegralHomology (G.Child c).Carrier 3)
    (hcollapse : G.LocalTerminalEDistComparison (G.canonicalComparisonSupport hSC))
    (s₀ : ℝ) (hs₀ : s₀ ∈ _root_.Set.Ico (H.time i.castSucc) (H.time i.succ))
    (ell : ℝ → ℝ) (hell : ∀ s ∈ _root_.Set.Ioo s₀ (H.time i.succ), 1 ≤ ell s)
    (htend : Filter.Tendsto ell (𝓝[<] (H.time i.succ)) (𝓝 1))
    (hquad : G.TerminalParentQuadFormComparison s₀ ell)
    (hregion : G.TerminalParentRegionConvexity (G.canonicalComparisonSupport hSC) s₀)
    (multiplier : (c : ConnectedComponents (H.stage i.succ).Carrier) → ℤ)
    (hmap : ∀ c : ConnectedComponents (H.stage i.succ).Carrier,
      integralHomologyMap 3 (G.canonicalComparisonSupport hSC c).rfs_whole_parent_map (a c) =
        multiplier c • b c)
    (hgenerator : ∀ c : ConnectedComponents (H.stage i.succ).Carrier,
      ∃ φ : IntegralHomology (G.Child c).Carrier 3 →ₗ[ℤ] ℤ,
        φ (integralHomologyMap 3 (G.canonicalComparisonSupport hSC c).rfs_whole_parent_map
          (a c)) = 1)
    (hpositive : ∀ c : ConnectedComponents (H.stage i.succ).Carrier, 0 < multiplier c) :
    ∃ f : (c : ConnectedComponents (H.stage i.succ).Carrier) →
        C((G.Parent c).Carrier, (G.Child c).Carrier),
      (∀ c, ∃ K : G.ComparisonSupport c, f c = K.rfs_whole_parent_map) ∧
      (∀ c, integralHomologyMap 3 (f c) (a c) = b c) ∧
      ∃ s₀ ∈ _root_.Set.Ico (H.time i.castSucc) (H.time i.succ), ∃ ell : ℝ → ℝ,
        (∀ s ∈ _root_.Set.Ioo s₀ (H.time i.succ), 1 ≤ ell s) ∧
        Filter.Tendsto ell (𝓝[<] (H.time i.succ)) (𝓝 1) ∧
        ∀ c, ∀ s ∈ _root_.Set.Ioo s₀ (H.time i.succ), ∀ x y : (G.Parent c).Carrier,
          riemannianEDistOf ((H.stage i.succ).componentMetric (H.event i).outputMetric c)
            (f c x) (f c y) ≤ ENNReal.ofReal (ell s) *
            riemannianEDistOf ((H.stage i.castSucc).componentMetric
              ((H.event i).incoming.flow.base.metric s) (G.transition.childParent c)) x y :=
  G.rfs_child_comparison_of_canonicalReducedInputs hSC a b
    (fun c =>
      ComparisonSupport.localTerminalDistanceControl_of_localTerminalEDistComparison
        (c := c) (G.canonicalComparisonSupport hSC) hcollapse)
    s₀ hs₀ ell hell htend
    (G.localEDistComparison_of_terminal_comparisons (G.canonicalComparisonSupport hSC) hcollapse
      (G.localTerminalParentEDistComparison_of_quadFormComparison_of_regionConvexity
        (G.canonicalComparisonSupport hSC) hquad hregion hell))
    multiplier hmap hgenerator hpositive

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.rfs_child_comparison_of_canonicalTerminalInputs then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.rfs_child_comparison_of_canonicalTerminalInputs"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.rfs_child_comparison_of_canonicalTerminalInputs ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.rfs_child_comparison_of_canonicalTerminalInputs

theorem rfs_child_comparison_of_canonicalUniformConvergence
    (hSC : ∀ p : ConnectedComponents (H.stage i.castSucc).Carrier,
      SimplyConnectedSpace ((H.stage i.castSucc).component p).Carrier)
    (a : (c : ConnectedComponents (H.stage i.succ).Carrier) →
      IntegralHomology (G.Parent c).Carrier 3)
    (b : (c : ConnectedComponents (H.stage i.succ).Carrier) →
      IntegralHomology (G.Child c).Carrier 3)
    (hcollapse : G.LocalTerminalEDistComparison (G.canonicalComparisonSupport hSC))
    (s₀ : ℝ) (hs₀ : s₀ ∈ _root_.Set.Ico (H.time i.castSucc) (H.time i.succ))
    (hregion : G.TerminalParentRegionConvexity (G.canonicalComparisonSupport hSC) s₀)
    (huniform : G.TerminalParentUniformConvergence s₀)
    (multiplier : (c : ConnectedComponents (H.stage i.succ).Carrier) → ℤ)
    (hmap : ∀ c : ConnectedComponents (H.stage i.succ).Carrier,
      integralHomologyMap 3 (G.canonicalComparisonSupport hSC c).rfs_whole_parent_map (a c) =
        multiplier c • b c)
    (hgenerator : ∀ c : ConnectedComponents (H.stage i.succ).Carrier,
      ∃ φ : IntegralHomology (G.Child c).Carrier 3 →ₗ[ℤ] ℤ,
        φ (integralHomologyMap 3 (G.canonicalComparisonSupport hSC c).rfs_whole_parent_map
          (a c)) = 1)
    (hpositive : ∀ c : ConnectedComponents (H.stage i.succ).Carrier, 0 < multiplier c) :
    ∃ f : (c : ConnectedComponents (H.stage i.succ).Carrier) →
        C((G.Parent c).Carrier, (G.Child c).Carrier),
      (∀ c, ∃ K : G.ComparisonSupport c, f c = K.rfs_whole_parent_map) ∧
      (∀ c, integralHomologyMap 3 (f c) (a c) = b c) ∧
      ∃ s₀ ∈ _root_.Set.Ico (H.time i.castSucc) (H.time i.succ), ∃ ell : ℝ → ℝ,
        (∀ s ∈ _root_.Set.Ioo s₀ (H.time i.succ), 1 ≤ ell s) ∧
        Filter.Tendsto ell (𝓝[<] (H.time i.succ)) (𝓝 1) ∧
        ∀ c, ∀ s ∈ _root_.Set.Ioo s₀ (H.time i.succ), ∀ x y : (G.Parent c).Carrier,
          riemannianEDistOf ((H.stage i.succ).componentMetric (H.event i).outputMetric c)
            (f c x) (f c y) ≤ ENNReal.ofReal (ell s) *
            riemannianEDistOf ((H.stage i.castSucc).componentMetric
              ((H.event i).incoming.flow.base.metric s) (G.transition.childParent c)) x y := by
  obtain ⟨s₁, hs₁, ell, hell, htend, hquad⟩ :=
    G.exists_quadFormComparison_of_uniformConvergence huniform
  exact G.rfs_child_comparison_of_canonicalTerminalInputs hSC a b hcollapse s₁
    ⟨le_of_lt (lt_of_le_of_lt hs₀.1 hs₁.1), hs₁.2⟩ ell hell htend hquad
    (TerminalParentRegionConvexity.mono G hregion (le_of_lt hs₁.1))
    multiplier hmap hgenerator hpositive

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.rfs_child_comparison_of_canonicalUniformConvergence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.rfs_child_comparison_of_canonicalUniformConvergence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.rfs_child_comparison_of_canonicalUniformConvergence ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.rfs_child_comparison_of_canonicalUniformConvergence

namespace ComparisonSupport

variable {c : ConnectedComponents (H.stage i.succ).Carrier}

theorem rfs_whole_parent_map_class_eq_of_multiplierForm
    (K : G.ComparisonSupport c)
    (a : IntegralHomology (G.Parent c).Carrier 3)
    (b : IntegralHomology (G.Child c).Carrier 3)
    {k : ℤ}
    (hmap : integralHomologyMap 3 K.rfs_whole_parent_map a = k • b)
    (hgen : ∃ φ : IntegralHomology (G.Child c).Carrier 3 →ₗ[ℤ] ℤ,
      φ (integralHomologyMap 3 K.rfs_whole_parent_map a) = 1)
    (hk : 0 < k) :
    integralHomologyMap 3 K.rfs_whole_parent_map a = b :=
  (DifferentialGeometry.Topology.eq_of_pos_zsmul_and_linearMap_eq_one
    (A := IntegralHomology (G.Child c).Carrier 3)
    ⟨k, hgen.choose, hmap, hk, hgen.choose_spec⟩).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.rfs_whole_parent_map_class_eq_of_multiplierForm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.rfs_whole_parent_map_class_eq_of_multiplierForm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.rfs_whole_parent_map_class_eq_of_multiplierForm ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.rfs_whole_parent_map_class_eq_of_multiplierForm

end ComparisonSupport

theorem rfs_child_comparison_of_localEDistComparison_and_class_generator
    (Kc : (c : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c)
    (a : (c : ConnectedComponents (H.stage i.succ).Carrier) →
      IntegralHomology (G.Parent c).Carrier 3)
    (b : (c : ConnectedComponents (H.stage i.succ).Carrier) →
      IntegralHomology (G.Child c).Carrier 3)
    (convergenceTime : ℝ)
    (hconvergenceTime : convergenceTime ∈ _root_.Set.Ico (H.time i.castSucc) (H.time i.succ))
    (scale : ℝ → ℝ)
    (hscale_one : ∀ s ∈ _root_.Set.Ioo convergenceTime (H.time i.succ), 1 ≤ scale s)
    (hscale_tendsto : Filter.Tendsto scale (𝓝[<] (H.time i.succ)) (𝓝 1))
    (hlocalEDist : G.LocalEDistComparison Kc convergenceTime scale)
    (multiplier : (c : ConnectedComponents (H.stage i.succ).Carrier) → ℤ)
    (hmap : ∀ c : ConnectedComponents (H.stage i.succ).Carrier,
      integralHomologyMap 3 (Kc c).rfs_whole_parent_map (a c) = multiplier c • b c)
    (hgenerator : ∀ c : ConnectedComponents (H.stage i.succ).Carrier,
      ∃ φ : IntegralHomology (G.Child c).Carrier 3 →ₗ[ℤ] ℤ,
        φ (integralHomologyMap 3 (Kc c).rfs_whole_parent_map (a c)) = 1)
    (hpositive : ∀ c : ConnectedComponents (H.stage i.succ).Carrier, 0 < multiplier c) :
    ∃ f : (c : ConnectedComponents (H.stage i.succ).Carrier) →
        C((G.Parent c).Carrier, (G.Child c).Carrier),
      (∀ c, ∃ K : G.ComparisonSupport c, f c = K.rfs_whole_parent_map) ∧
      (∀ c, integralHomologyMap 3 (f c) (a c) = b c) ∧
      ∃ s₀ ∈ _root_.Set.Ico (H.time i.castSucc) (H.time i.succ), ∃ ell : ℝ → ℝ,
        (∀ s ∈ _root_.Set.Ioo s₀ (H.time i.succ), 1 ≤ ell s) ∧
        Filter.Tendsto ell (𝓝[<] (H.time i.succ)) (𝓝 1) ∧
        ∀ c, ∀ s ∈ _root_.Set.Ioo s₀ (H.time i.succ), ∀ x y : (G.Parent c).Carrier,
          riemannianEDistOf ((H.stage i.succ).componentMetric (H.event i).outputMetric c)
            (f c x) (f c y) ≤ ENNReal.ofReal (ell s) *
            riemannianEDistOf ((H.stage i.castSucc).componentMetric
              ((H.event i).incoming.flow.base.metric s) (G.transition.childParent c)) x y := by
  obtain ⟨f, hf, hlen⟩ := G.rfs_child_comparison_metric_of_local_length_comparison Kc
    (G.localLengthComparison_of_localEDistComparison Kc hconvergenceTime hlocalEDist
      hscale_one hscale_tendsto)
  exact ⟨f, fun c => ⟨Kc c, hf c⟩, fun c => by
      rw [hf c]
      exact ComparisonSupport.rfs_whole_parent_map_class_eq_of_multiplierForm (Kc c) (a c) (b c)
        (hmap c) (hgenerator c) (hpositive c), hlen⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.rfs_child_comparison_of_localEDistComparison_and_class_generator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.rfs_child_comparison_of_localEDistComparison_and_class_generator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.rfs_child_comparison_of_localEDistComparison_and_class_generator ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.rfs_child_comparison_of_localEDistComparison_and_class_generator

theorem rfs_child_comparison_of_canonicalLocalEDistComparison_and_class_generator
    (hSC : ∀ p : ConnectedComponents (H.stage i.castSucc).Carrier,
      SimplyConnectedSpace ((H.stage i.castSucc).component p).Carrier)
    (a : (c : ConnectedComponents (H.stage i.succ).Carrier) →
      IntegralHomology (G.Parent c).Carrier 3)
    (b : (c : ConnectedComponents (H.stage i.succ).Carrier) →
      IntegralHomology (G.Child c).Carrier 3)
    (convergenceTime : ℝ)
    (hconvergenceTime : convergenceTime ∈ _root_.Set.Ico (H.time i.castSucc) (H.time i.succ))
    (scale : ℝ → ℝ)
    (hscale_one : ∀ s ∈ _root_.Set.Ioo convergenceTime (H.time i.succ), 1 ≤ scale s)
    (hscale_tendsto : Filter.Tendsto scale (𝓝[<] (H.time i.succ)) (𝓝 1))
    (hlocalEDist : G.LocalEDistComparison (G.canonicalComparisonSupport hSC) convergenceTime scale)
    (multiplier : (c : ConnectedComponents (H.stage i.succ).Carrier) → ℤ)
    (hmap : ∀ c : ConnectedComponents (H.stage i.succ).Carrier,
      integralHomologyMap 3 (G.canonicalComparisonSupport hSC c).rfs_whole_parent_map (a c) =
        multiplier c • b c)
    (hgenerator : ∀ c : ConnectedComponents (H.stage i.succ).Carrier,
      ∃ φ : IntegralHomology (G.Child c).Carrier 3 →ₗ[ℤ] ℤ,
        φ (integralHomologyMap 3 (G.canonicalComparisonSupport hSC c).rfs_whole_parent_map
          (a c)) = 1)
    (hpositive : ∀ c : ConnectedComponents (H.stage i.succ).Carrier, 0 < multiplier c) :
    ∃ f : (c : ConnectedComponents (H.stage i.succ).Carrier) →
        C((G.Parent c).Carrier, (G.Child c).Carrier),
      (∀ c, ∃ K : G.ComparisonSupport c, f c = K.rfs_whole_parent_map) ∧
      (∀ c, integralHomologyMap 3 (f c) (a c) = b c) ∧
      ∃ s₀ ∈ _root_.Set.Ico (H.time i.castSucc) (H.time i.succ), ∃ ell : ℝ → ℝ,
        (∀ s ∈ _root_.Set.Ioo s₀ (H.time i.succ), 1 ≤ ell s) ∧
        Filter.Tendsto ell (𝓝[<] (H.time i.succ)) (𝓝 1) ∧
        ∀ c, ∀ s ∈ _root_.Set.Ioo s₀ (H.time i.succ), ∀ x y : (G.Parent c).Carrier,
          riemannianEDistOf ((H.stage i.succ).componentMetric (H.event i).outputMetric c)
            (f c x) (f c y) ≤ ENNReal.ofReal (ell s) *
            riemannianEDistOf ((H.stage i.castSucc).componentMetric
              ((H.event i).incoming.flow.base.metric s) (G.transition.childParent c)) x y :=
  G.rfs_child_comparison_of_localEDistComparison_and_class_generator
    (G.canonicalComparisonSupport hSC) a b convergenceTime hconvergenceTime scale hscale_one
    hscale_tendsto hlocalEDist multiplier hmap hgenerator hpositive

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.rfs_child_comparison_of_canonicalLocalEDistComparison_and_class_generator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.rfs_child_comparison_of_canonicalLocalEDistComparison_and_class_generator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.rfs_child_comparison_of_canonicalLocalEDistComparison_and_class_generator ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.rfs_child_comparison_of_canonicalLocalEDistComparison_and_class_generator

end GeometricCutoffRecord

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open _root_.Lean in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for n in [``DifferentialGeometry.Topology.exists_eq_zsmul_and_exists_linearMap_eq_one_not_pos,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.PuncturedCoreCutChain.ofSimplyConnectedComponent,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.puncturedCoreCutChainProducer_iff_middleSphereCuttingSeparation,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childSimplicityFrontier_iff_childCollaredStarCoverProducer_and_puncturedCoreCutChainProducer,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.not_nonempty_childCarrierCollaredStarCover_of_not_simplyConnectedSpace,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.not_nonempty_childCarrierCollaredStarCover_of_capRange_eq_univ,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.not_nonempty_childCarrierCollaredStarCover_of_middleSphereCuttingSeparation,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ChildComparisonReducedInputs,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ChildComparisonInputs.toReducedInputs,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.rfs_child_comparison_of_reducedInputs,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.rfs_child_comparison_of_canonicalReducedInputs,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.rfs_child_comparison_of_canonicalTerminalInputs,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.rfs_child_comparison_of_canonicalUniformConvergence,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.rfs_whole_parent_map_class_eq_of_multiplierForm,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.rfs_child_comparison_of_localEDistComparison_and_class_generator,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.rfs_child_comparison_of_canonicalLocalEDistComparison_and_class_generator] do
    let axs ← Lean.collectAxioms n
    unless axs.all (fun a => allowed.contains a) do
      throwError "unexpected dependencies for {n}: {axs}"
