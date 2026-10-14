import Submission.DifferentialGeometry.Geometry.Boundary.ProductHalfSpace
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StandardNeckCutCap
import Submission.DifferentialGeometry.Topology.Manifold.SmoothEmbeddingCompositionBoundarySource
import Mathlib.Geometry.Manifold.Instances.Icc

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private abbrev NeckE3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NeckE3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NeckE3 target :: scope.openDecls } }
private abbrev NeckE4 := EuclideanSpace ℝ (Fin 4)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NeckE4
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NeckE4 target :: scope.openDecls } }

local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactLtRealNegOfNat_differentialGeometry : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactLtRealNegOfNat_differentialGeometry then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactLtRealNegOfNat_differentialGeometry"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactLtRealNegOfNat_differentialGeometry ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactLtRealNegOfNat_differentialGeometry

private theorem contMDiff_neckHeight :
    ContMDiff ((𝓡 2).prod (𝓡∂ 1)) 𝓘(ℝ, ℝ) ∞
      (fun z : TubeDomain => Real.sqrt (1 - ((z.2 : ℝ) / 4) ^ 2)) := by
  have hg : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
      (fun t : ℝ => Real.sqrt (1 - (t / 4) ^ 2)) (_root_.Set.Icc (-2 : ℝ) 2) := by
    apply ContDiffOn.contMDiffOn
    refine ContDiffOn.sqrt ?_ ?_
    · apply ContDiffOn.sub contDiffOn_const
      apply ContDiffOn.pow
      exact contDiffOn_id.div_const 4
    · intro t ht
      have h1 : |t| ≤ 2 := abs_le.mpr ⟨ht.1, ht.2⟩
      have h2 : t ^ 2 ≤ 4 := by
        have h3 : |t| ^ 2 ≤ 2 ^ 2 := by nlinarith [abs_nonneg t, h1]
        norm_num at h3
        exact h3
      have h4 : (t / 4) ^ 2 ≤ 1 := by nlinarith
      nlinarith [sq_nonneg (t / 4)]
  exact hg.comp_contMDiff ((contMDiff_subtypeVal_Icc (x := (-2 : ℝ)) (y := 2)).comp
    contMDiff_snd) (fun z => z.2.2)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.contMDiff_neckHeight
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.contMDiff_neckHeight target :: scope.openDecls } }

private theorem snocR_three (f : Fin 3 → ℝ) (a : ℝ) : snocR f a (3 : Fin 4) = a := by
  rw [show (3 : Fin 4) = Fin.last 3 from rfl, snocR_last]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.snocR_three
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.snocR_three target :: scope.openDecls } }

private theorem contMDiff_neckCoord_last :
    ContMDiff ((𝓡 2).prod (𝓡∂ 1)) 𝓘(ℝ, ℝ) ∞
      (fun z : TubeDomain => (z.2 : ℝ) / 4) :=
  ((contMDiff_subtypeVal_Icc (x := (-2 : ℝ)) (y := 2)).comp contMDiff_snd).div_const 4

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.contMDiff_neckCoord_last
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.contMDiff_neckCoord_last target :: scope.openDecls } }

private theorem contMDiff_sphereCoord (j : Fin 3) :
    ContMDiff ((𝓡 2).prod (𝓡∂ 1)) 𝓘(ℝ, ℝ) ∞
      (fun z : TubeDomain => ((z.1 : NeckE3) j)) :=
  ((EuclideanSpace.proj j).contMDiff).comp <|
    (contMDiff_coe_sphere (n := 2) (E := NeckE3)).comp contMDiff_fst

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.contMDiff_sphereCoord
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.contMDiff_sphereCoord target :: scope.openDecls } }

private def neckCoordFun (z : TubeDomain) : Fin 4 → ℝ :=
  snocR (fun j : Fin 3 => Real.sqrt (1 - ((z.2 : ℝ) / 4) ^ 2) * ((z.1 : NeckE3) j))
    ((z.2 : ℝ) / 4)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.neckCoordFun
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.neckCoordFun target :: scope.openDecls } }

private theorem contMDiff_neckCoordFun :
    ContMDiff ((𝓡 2).prod (𝓡∂ 1)) 𝓘(ℝ, (Fin 4 → ℝ)) ∞ neckCoordFun := by
  rw [contMDiff_pi_space]
  intro i
  refine Fin.lastCases ?_ ?_ i
  · simp only [neckCoordFun, snocR_last]
    exact contMDiff_neckCoord_last
  · intro j
    simp only [neckCoordFun, snocR_castSucc]
    exact contMDiff_neckHeight.mul (contMDiff_sphereCoord j)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.contMDiff_neckCoordFun
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.contMDiff_neckCoordFun target :: scope.openDecls } }

private theorem contMDiff_neckPoint :
    ContMDiff ((𝓡 2).prod (𝓡∂ 1)) 𝓘(ℝ, NeckE4) ∞
      (fun z : TubeDomain => (neckPoint z.1 z.2.1 : NeckE4)) := by
  have hE : ContMDiff ((𝓡 2).prod (𝓡∂ 1)) 𝓘(ℝ, NeckE4) ∞
      (fun z : TubeDomain => (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin 4)).symm
        (neckCoordFun z)) :=
    ((EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin 4)).symm :
      (Fin 4 → ℝ) →L[ℝ] NeckE4).contMDiff.comp contMDiff_neckCoordFun
  refine hE.congr ?_
  intro z
  simp only [EuclideanSpace.equiv, PiLp.continuousLinearEquiv_symm_apply, neckCoordFun, neckPoint,
    snocR]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.contMDiff_neckPoint
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.contMDiff_neckPoint target :: scope.openDecls } }

theorem contMDiff_standardNeckTubeFun :
    letI : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩
    ContMDiff ((𝓡 2).prod (𝓡∂ 1)) ThreeModel ∞ standardNeckTubeFun := by
  have h := contMDiff_neckPoint.codRestrict_sphere (n := 3)
    (fun z : TubeDomain => neckPoint_mem_sphere z.1 z.2)
  rwa [show (_root_.Set.codRestrict (fun z : TubeDomain => (neckPoint z.1 z.2.1 : NeckE4))
      (Metric.sphere 0 1) _) = standardNeckTubeFun from rfl] at h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.contMDiff_standardNeckTubeFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.contMDiff_standardNeckTubeFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.contMDiff_standardNeckTubeFun ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.contMDiff_standardNeckTubeFun

theorem standardNeckTube_isImmersion_of_isSmoothEmbedding
    (h : standardNeckTubeIsSmoothEmbedding) :
    letI : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩
    IsImmersion ((𝓡 2).prod (𝓡∂ 1)) ThreeModel ∞ standardNeckTube :=
  h.isImmersion

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckTube_isImmersion_of_isSmoothEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckTube_isImmersion_of_isSmoothEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckTube_isImmersion_of_isSmoothEmbedding ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckTube_isImmersion_of_isSmoothEmbedding

theorem standardNeckTubeIsSmoothEmbedding_of_isImmersion
    (h : letI : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩
      _root_.Manifold.IsImmersion ((𝓡 2).prod (𝓡∂ 1)) ThreeModel ∞ standardNeckTube) :
    standardNeckTubeIsSmoothEmbedding :=
  ⟨h, isEmbedding_standardNeckTubeFun⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckTubeIsSmoothEmbedding_of_isImmersion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckTubeIsSmoothEmbedding_of_isImmersion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckTubeIsSmoothEmbedding_of_isImmersion ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckTubeIsSmoothEmbedding_of_isImmersion

theorem standardNeckTube_isImmersion_of_cylinder_immersion (g : Sphere 2 × ℝ → Sphere 3)
    (hg : _root_.Manifold.IsImmersion ((𝓡 2).prod 𝓘(ℝ)) ThreeModel ∞ g)
    (hsub : ∀ z : TubeDomain, g (z.1, (z.2 : ℝ)) = standardNeckTubeFun z) :
    IsImmersion ((𝓡 2).prod (𝓡∂ 1)) ThreeModel ∞ standardNeckTubeFun := by
  have hf : _root_.Manifold.IsImmersion ((𝓡 2).prod (𝓡∂ 1)) ((𝓡 2).prod 𝓘(ℝ)) ∞
      (Prod.map (id : Sphere 2 → Sphere 2) (Subtype.val : _root_.Set.Icc (-2 : ℝ) 2 → ℝ)) :=
    IsImmersion.prodMap IsImmersion.id
      (isImmersionOfComplement_subtypeVal_Icc (x := (-2 : ℝ)) (y := 2)).isImmersion
  exact (IsImmersion.comp_of_smoothBoundary hf hg).congr (funext hsub)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckTube_isImmersion_of_cylinder_immersion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckTube_isImmersion_of_cylinder_immersion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckTube_isImmersion_of_cylinder_immersion ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckTube_isImmersion_of_cylinder_immersion

theorem standardNeckTubeIsSmoothEmbedding_of_cylinder_isSmoothEmbedding
    (g : Sphere 2 × ℝ → Sphere 3)
    (hg : _root_.Manifold.IsSmoothEmbedding ((𝓡 2).prod 𝓘(ℝ)) ThreeModel ∞ g)
    (hsub : ∀ z : TubeDomain, g (z.1, (z.2 : ℝ)) = standardNeckTubeFun z) :
    standardNeckTubeIsSmoothEmbedding :=
  ⟨standardNeckTube_isImmersion_of_cylinder_immersion g hg.isImmersion hsub,
    isEmbedding_standardNeckTubeFun⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckTubeIsSmoothEmbedding_of_cylinder_isSmoothEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckTubeIsSmoothEmbedding_of_cylinder_isSmoothEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckTubeIsSmoothEmbedding_of_cylinder_isSmoothEmbedding ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckTubeIsSmoothEmbedding_of_cylinder_isSmoothEmbedding

theorem TubeSystem.coreBoundarySphere_disjoint {M : Type u} [TopologicalSpace M]
    (T : TubeSystem M) {b b' : T.Boundary} (h : b ≠ b') :
    Disjoint (Set.range (T.coreBoundarySphere b)) (Set.range (T.coreBoundarySphere b')) := by
  rcases b with ⟨a, s⟩
  rcases b' with ⟨a', s'⟩
  rw [Set.disjoint_left]
  rintro p ⟨y, rfl⟩ ⟨y', hy'⟩
  have h' : T.boundarySphere (a', s') y' = T.boundarySphere (a, s) y :=
    congrArg (fun q : T.core => (q : M)) hy'
  by_cases ha : a = a'
  · subst ha
    have hcoord : TubeSystem.boundaryLevel s' = TubeSystem.boundaryLevel s := by
      have hinj := (T.embedding a).injective h'
      exact congrArg (fun z : TubeDomain => z.2) hinj
    cases s <;> cases s'
    · exact absurd rfl h
    · norm_num [TubeSystem.boundaryLevel] at hcoord
    · norm_num [TubeSystem.boundaryLevel] at hcoord
    · exact absurd rfl h
  · refine Set.disjoint_left.mp (T.disjoint ha)
      (Set.mem_range_self (f := T.tube a) ⟨y, TubeSystem.boundaryLevel s⟩) ?_
    exact ⟨⟨y', TubeSystem.boundaryLevel s'⟩, h'⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.coreBoundarySphere_disjoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.coreBoundarySphere_disjoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.coreBoundarySphere_disjoint ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.coreBoundarySphere_disjoint

theorem TubeSystem.coreBoundarySphere_mem_boundary {M : Type u} [TopologicalSpace M]
    (T : TubeSystem M) [ChartedSpace (EuclideanHalfSpace 3) T.core]
    [IsManifold (𝓡∂ 3) ∞ T.core]
    (hcore : (𝓡∂ 3).boundary T.core = ⋃ b, Set.range (T.coreBoundarySphere b))
    (b : T.Boundary) (y : Sphere 2) :
    T.coreBoundarySphere b y ∈ (𝓡∂ 3).boundary T.core := by
  rw [hcore]
  exact Set.mem_iUnion.mpr ⟨b, Set.mem_range_self y⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.coreBoundarySphere_mem_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.coreBoundarySphere_mem_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.coreBoundarySphere_mem_boundary ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.coreBoundarySphere_mem_boundary

theorem CutCapTransitionData.coreBoundarySphere_mem_boundary {P Q D N : OrientedThreeStage.{u}}
    (X : CutCapTransitionData P Q D N) (b : X.trace.tubes.Boundary) (y : Sphere 2) :
    letI : ChartedSpace (EuclideanHalfSpace 3) X.trace.tubes.core := X.coreCharts
    letI : IsManifold (𝓡∂ 3) ∞ X.trace.tubes.core := X.coreSmooth
    X.trace.tubes.coreBoundarySphere b y ∈ (𝓡∂ 3).boundary X.trace.tubes.core :=
  @TubeSystem.coreBoundarySphere_mem_boundary _ _ X.trace.tubes X.coreCharts X.coreSmooth
    X.core_boundary b y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTransitionData.coreBoundarySphere_mem_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTransitionData.coreBoundarySphere_mem_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTransitionData.coreBoundarySphere_mem_boundary ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTransitionData.coreBoundarySphere_mem_boundary

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
