import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BallDiffeomorph

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

set_option autoImplicit false
noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instChartedSpaceEuclideanHalfSpaceOfNatNatClosedCell_1 : ChartedSpace (EuclideanHalfSpace 3)
    (DifferentialGeometry.Topology.ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instChartedSpaceEuclideanHalfSpaceOfNatNatClosedCell_1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instChartedSpaceEuclideanHalfSpaceOfNatNatClosedCell_1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instChartedSpaceEuclideanHalfSpaceOfNatNatClosedCell_1 ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instChartedSpaceEuclideanHalfSpaceOfNatNatClosedCell_1

local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instIsManifoldRealEuclideanSpaceFinOfNatNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpaceSomeENatTopClosedCell_1 : IsManifold (𝓡∂ 3) ∞ (DifferentialGeometry.Topology.ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instIsManifoldRealEuclideanSpaceFinOfNatNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpaceSomeENatTopClosedCell_1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instIsManifoldRealEuclideanSpaceFinOfNatNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpaceSomeENatTopClosedCell_1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instIsManifoldRealEuclideanSpaceFinOfNatNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpaceSomeENatTopClosedCell_1 ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instIsManifoldRealEuclideanSpaceFinOfNatNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpaceSomeENatTopClosedCell_1

private theorem linearEquiv_symm_trans_comp_eq {U V W X : Type*}
    [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] [AddCommGroup X] [Module ℝ X]
    (A : U →ₗ[ℝ] W) (B : U →ₗ[ℝ] X) (A' : V →ₗ[ℝ] W) (B' : V →ₗ[ℝ] X)
    (D : U →ₗ[ℝ] V) (hA : A = A'.comp D) (hB : B = B'.comp D)
    (hi : Function.Bijective A) (hi' : Function.Bijective A')
    (hj : Function.Bijective B) (hj' : Function.Bijective B') :
    (LinearEquiv.ofBijective A hi).symm.trans (LinearEquiv.ofBijective B hj) =
      (LinearEquiv.ofBijective A' hi').symm.trans (LinearEquiv.ofBijective B' hj') := by
  refine LinearEquiv.ext fun w => ?_
  have h1 : A' ((LinearEquiv.ofBijective A' hi').symm w) = w := by
    simpa only [LinearEquiv.ofBijective_apply] using
      LinearEquiv.apply_symm_apply (LinearEquiv.ofBijective A' hi') w
  have h2 : A ((LinearEquiv.ofBijective A hi).symm w) = w := by
    simpa only [LinearEquiv.ofBijective_apply] using
      LinearEquiv.apply_symm_apply (LinearEquiv.ofBijective A hi) w
  have hgen : ∀ y : U, A y = A' (D y) := fun y => by rw [hA]; rfl
  have key : (LinearEquiv.ofBijective A' hi').symm w =
      D ((LinearEquiv.ofBijective A hi).symm w) := by
    apply hi'.injective
    calc A' ((LinearEquiv.ofBijective A' hi').symm w)
        = w := h1
      _ = A ((LinearEquiv.ofBijective A hi).symm w) := h2.symm
      _ = A' (D ((LinearEquiv.ofBijective A hi).symm w)) := hgen _
  simp only [LinearEquiv.trans_apply, LinearEquiv.ofBijective_apply]
  rw [key, ← LinearMap.comp_apply, ← hB]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.linearEquiv_symm_trans_comp_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.linearEquiv_symm_trans_comp_eq target :: scope.openDecls } }

namespace SmoothCutCapTransition

variable {P Q D N : OrientedThreeStage.{u}}

noncomputable def capClosedCell (X : SmoothCutCapTransition P Q D N)
    (b : X.trace.tubes.Boundary) :
    C(DifferentialGeometry.Topology.ClosedCell 3, N.Carrier) :=
  letI : ChartedSpace (EuclideanHalfSpace 3) ThreeBall := X.ballCharts
  letI : IsManifold (𝓡∂ 3) ∞ ThreeBall := X.ballSmooth
  ⟨fun z => X.trace.capping.cap b (X.closedCellBallDiffeomorph z),
    (X.trace.capping.cap b).continuous.comp X.closedCellBallDiffeomorph.continuous⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.capClosedCell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.capClosedCell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.capClosedCell ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.capClosedCell

theorem capClosedCell_apply (X : SmoothCutCapTransition P Q D N)
    (b : X.trace.tubes.Boundary) (z : DifferentialGeometry.Topology.ClosedCell 3) :
    X.capClosedCell b z = X.trace.capping.cap b (X.closedCellBallDiffeomorph z) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.capClosedCell_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.capClosedCell_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.capClosedCell_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.capClosedCell_apply

theorem range_capClosedCell (X : SmoothCutCapTransition P Q D N)
    (b : X.trace.tubes.Boundary) :
    Set.range (X.capClosedCell b) = Set.range (X.trace.capping.cap b) :=
  Function.Surjective.range_comp (f := (X.closedCellBallDiffeomorph :
      DifferentialGeometry.Topology.ClosedCell 3 → ThreeBall))
    X.closedCellBallDiffeomorph.surjective ⇑(X.trace.capping.cap b)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.range_capClosedCell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.range_capClosedCell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.range_capClosedCell ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.range_capClosedCell

theorem iUnion_range_capClosedCell (X : SmoothCutCapTransition P Q D N) :
    (⋃ b, Set.range (X.capClosedCell b)) =
      ⋃ b, Set.range (X.trace.capping.cap b) :=
  _root_.Set.iUnion_congr fun b => range_capClosedCell X b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.iUnion_range_capClosedCell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.iUnion_range_capClosedCell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.iUnion_range_capClosedCell ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.iUnion_range_capClosedCell

theorem capClosedCell_isSmoothEmbedding (X : SmoothCutCapTransition P Q D N)
    (b : X.trace.tubes.Boundary) :
    IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ (X.capClosedCell b) :=
  X.cap_isSmoothEmbedding_closedCell b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.capClosedCell_isSmoothEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.capClosedCell_isSmoothEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.capClosedCell_isSmoothEmbedding ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.capClosedCell_isSmoothEmbedding

theorem coreBoundarySphere_ofSmoothCutCapTransition (X : SmoothCutCapTransition P Q D N)
    (b : X.trace.tubes.Boundary) :
    (SphericalTubeSystem.ofSmoothCutCapTransition X).coreBoundarySphere b =
      X.trace.tubes.coreBoundarySphere b := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.coreBoundarySphere_ofSmoothCutCapTransition then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.coreBoundarySphere_ofSmoothCutCapTransition"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.coreBoundarySphere_ofSmoothCutCapTransition ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.coreBoundarySphere_ofSmoothCutCapTransition

theorem capClosedCell_boundary_eq (X : SmoothCutCapTransition P Q D N)
    (b : X.trace.tubes.Boundary)
    (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    X.capClosedCell b (DifferentialGeometry.Topology.sphereToClosedCell z) =
      X.trace.capping.coreInclusion
        ((SphericalTubeSystem.ofSmoothCutCapTransition X).coreBoundarySphere b
          (X.attaching b z)) := by
  rw [capClosedCell_apply, X.closedCellBallDiffeomorph_sphereToClosedCell,
    X.trace.capping.boundary_eq b z, coreBoundarySphere_ofSmoothCutCapTransition,
    ← X.attaching_eq b]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.capClosedCell_boundary_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.capClosedCell_boundary_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.capClosedCell_boundary_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.capClosedCell_boundary_eq

theorem exhaustive_capClosedCell (X : SmoothCutCapTransition P Q D N) :
    Set.range (X.trace.capping.coreInclusion) ∪
        (⋃ b, Set.range (X.capClosedCell b)) = Set.univ := by
  rw [iUnion_range_capClosedCell]
  exact X.trace.capping.exhaustive

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.exhaustive_capClosedCell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.exhaustive_capClosedCell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.exhaustive_capClosedCell ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.exhaustive_capClosedCell

theorem core_cap_intersection_capClosedCell (X : SmoothCutCapTransition P Q D N)
    (b : X.trace.tubes.Boundary) :
    Set.range (X.trace.capping.coreInclusion) ∩ Set.range (X.capClosedCell b) =
      Set.range (X.trace.capping.coreInclusion.comp
        ((SphericalTubeSystem.ofSmoothCutCapTransition X).coreBoundarySphere b)) := by
  rw [range_capClosedCell, coreBoundarySphere_ofSmoothCutCapTransition]
  exact X.trace.capping.core_cap_intersection b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.core_cap_intersection_capClosedCell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.core_cap_intersection_capClosedCell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.core_cap_intersection_capClosedCell ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.core_cap_intersection_capClosedCell

theorem cap_disjoint_capClosedCell (X : SmoothCutCapTransition P Q D N) :
    Pairwise fun b b' => Disjoint (Set.range (X.capClosedCell b))
      (Set.range (X.capClosedCell b')) :=
  fun b b' hne => (X.trace.capping.cap_disjoint hne).mono
    (range_capClosedCell X b).le (range_capClosedCell X b').le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.cap_disjoint_capClosedCell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.cap_disjoint_capClosedCell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.cap_disjoint_capClosedCell ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.cap_disjoint_capClosedCell

theorem capClosedCell_positive (X : SmoothCutCapTransition P Q D N)
    (b : X.trace.tubes.Boundary)
    (x : DifferentialGeometry.Topology.ClosedCell 3)
    (hx : (𝓡∂ 3).IsInteriorPoint x) :
    ∃ hi : Function.Bijective (mfderiv (𝓡∂ 3) (𝓡 3)
        (Subtype.val : DifferentialGeometry.Topology.ClosedCell 3 →
          EuclideanSpace ℝ (Fin 3)) x),
      ∃ hj : Function.Bijective (mfderiv (𝓡∂ 3) (𝓡 3) (X.capClosedCell b) x),
        Orientation.map (Fin 3)
          ((LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) (𝓡 3)
            (Subtype.val : DifferentialGeometry.Topology.ClosedCell 3 →
              EuclideanSpace ℝ (Fin 3)) x).toLinearMap hi).symm.trans
            (LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) (𝓡 3)
              (X.capClosedCell b) x).toLinearMap hj))
          ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation) =
            (if b.2 then (1 : ℝˣ) else -1) •
              N.orientation.orientation (X.capClosedCell b x) :=
  letI : ChartedSpace (EuclideanHalfSpace 3) ThreeBall := X.ballCharts
  letI : IsManifold (𝓡∂ 3) ∞ ThreeBall := X.ballSmooth
  by
    have hmde : MDifferentiableAt (𝓡∂ 3) (𝓡∂ 3) (⇑X.closedCellBallDiffeomorph) x :=
      X.closedCellBallDiffeomorph.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
    have hmdφ : MDifferentiableAt (𝓡∂ 3) (𝓡 3) (⇑(X.trace.capping.cap b))
        (X.closedCellBallDiffeomorph x) :=
      (X.cap_smooth b).contMDiff.contMDiffAt.mdifferentiableAt (by simp)
    have hmdψ : MDifferentiableAt (𝓡∂ 3) (𝓡 3)
        (Subtype.val : ThreeBall → EuclideanSpace ℝ (Fin 3))
        (X.closedCellBallDiffeomorph x) :=
      X.ball_induced.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
    have hy : (𝓡∂ 3).IsInteriorPoint (X.closedCellBallDiffeomorph x) :=
      (IsLocalDiffeomorphAt.isInteriorPoint_iff (n := ∞) (by simp)
        (X.closedCellBallDiffeomorph.isLocalDiffeomorph x)).mp hx
    obtain ⟨hi', hj', hsign⟩ := X.cap_positive b (X.closedCellBallDiffeomorph x) hy
    have hchainCap : mfderiv (𝓡∂ 3) (𝓡 3)
        (fun z => X.trace.capping.cap b (X.closedCellBallDiffeomorph z)) x =
        (mfderiv (𝓡∂ 3) (𝓡 3) (⇑(X.trace.capping.cap b))
          (X.closedCellBallDiffeomorph x)).comp
          (mfderiv (𝓡∂ 3) (𝓡∂ 3) (⇑X.closedCellBallDiffeomorph) x) :=
      mfderiv_comp x hmdφ hmde
    have hchainVal : mfderiv (𝓡∂ 3) (𝓡 3)
        (Subtype.val : DifferentialGeometry.Topology.ClosedCell 3 →
          EuclideanSpace ℝ (Fin 3)) x =
        (mfderiv (𝓡∂ 3) (𝓡 3)
          (Subtype.val : ThreeBall → EuclideanSpace ℝ (Fin 3))
          (X.closedCellBallDiffeomorph x)).comp
          (mfderiv (𝓡∂ 3) (𝓡∂ 3) (⇑X.closedCellBallDiffeomorph) x) :=
      mfderiv_comp x hmdψ hmde
    have hD : Function.Bijective (⇑(mfderiv (𝓡∂ 3) (𝓡∂ 3)
        (⇑X.closedCellBallDiffeomorph) x)) := by
      rw [← Diffeomorph.mfderivToContinuousLinearEquiv_coe (X.closedCellBallDiffeomorph) (by simp)]
      exact (X.closedCellBallDiffeomorph.mfderivToContinuousLinearEquiv (by simp) x).bijective
    have hA : (mfderiv (𝓡∂ 3) (𝓡 3)
        (Subtype.val : DifferentialGeometry.Topology.ClosedCell 3 →
          EuclideanSpace ℝ (Fin 3)) x).toLinearMap =
        ((mfderiv (𝓡∂ 3) (𝓡 3)
          (Subtype.val : ThreeBall → EuclideanSpace ℝ (Fin 3))
          (X.closedCellBallDiffeomorph x)).toLinearMap).comp
          ((mfderiv (𝓡∂ 3) (𝓡∂ 3) (⇑X.closedCellBallDiffeomorph) x).toLinearMap) := by
      rw [hchainVal]
      rfl
    have hcapfun : ⇑(X.capClosedCell b) =
        fun z => X.trace.capping.cap b (X.closedCellBallDiffeomorph z) := rfl
    have hB : (mfderiv (𝓡∂ 3) (𝓡 3) (⇑(X.capClosedCell b)) x).toLinearMap =
        ((mfderiv (𝓡∂ 3) (𝓡 3) (⇑(X.trace.capping.cap b))
          (X.closedCellBallDiffeomorph x)).toLinearMap).comp
          ((mfderiv (𝓡∂ 3) (𝓡∂ 3) (⇑X.closedCellBallDiffeomorph) x).toLinearMap) := by
      rw [hcapfun, hchainCap]
      rfl
    have hi : Function.Bijective (mfderiv (𝓡∂ 3) (𝓡 3)
        (Subtype.val : DifferentialGeometry.Topology.ClosedCell 3 →
          EuclideanSpace ℝ (Fin 3)) x) := by
      have h := hi'.comp hD
      rw [hchainVal]
      exact h
    have hj : Function.Bijective (mfderiv (𝓡∂ 3) (𝓡 3) (X.capClosedCell b) x) := by
      have h := hj'.comp hD
      rw [hcapfun, hchainCap]
      exact h
    refine ⟨hi, hj, ?_⟩
    rw [linearEquiv_symm_trans_comp_eq
      ((mfderiv (𝓡∂ 3) (𝓡 3)
        (Subtype.val : DifferentialGeometry.Topology.ClosedCell 3 →
          EuclideanSpace ℝ (Fin 3)) x).toLinearMap)
      ((mfderiv (𝓡∂ 3) (𝓡 3) (⇑(X.capClosedCell b)) x).toLinearMap)
      ((mfderiv (𝓡∂ 3) (𝓡 3)
        (Subtype.val : ThreeBall → EuclideanSpace ℝ (Fin 3))
        (X.closedCellBallDiffeomorph x)).toLinearMap)
      ((mfderiv (𝓡∂ 3) (𝓡 3) (⇑(X.trace.capping.cap b))
        (X.closedCellBallDiffeomorph x)).toLinearMap)
      ((mfderiv (𝓡∂ 3) (𝓡∂ 3) (⇑X.closedCellBallDiffeomorph) x).toLinearMap)
      hA hB hi hi' hj hj']
    exact hsign

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.capClosedCell_positive then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.capClosedCell_positive"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.capClosedCell_positive ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.capClosedCell_positive

def boundaryFrameReversing (X : SmoothCutCapTransition P Q D N) : Prop :=
  ∀ (b : (SphericalTubeSystem.ofSmoothCutCapTransition X).Boundary)
    (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (v w : TangentSpace (𝓡 2) z),
    let f : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 →
        P.toClosedOrientedManifold.Carrier :=
      (SphericalTubeSystem.ofSmoothCutCapTransition X).boundarySphere b ∘ X.attaching b
    let _ : FiniteDimensional ℝ (TangentSpace (𝓡 3) (f z)) :=
      inferInstanceAs (FiniteDimensional ℝ (EuclideanSpace ℝ (Fin 3)))
    let d := mfderiv (𝓡 2) (𝓡 3) f z
    let e := mfderiv (𝓡 2) (𝓡 3)
      (Subtype.val : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 →
        EuclideanSpace ℝ (Fin 3)) z
    (0 < ((P.toClosedOrientedManifold.orientation.orientation (f z)).someBasis (by
      change Fintype.card (Fin 3) = Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))
      simp)).det
      (Fin.cons ((SphericalTubeSystem.ofSmoothCutCapTransition X).outwardVector b
          (X.attaching b z)) (Fin.cons (d v) (Fin.cons (d w) ![])))) ↔
      (if b.2 then (1 : ℝ) else -1) *
        (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.det
          (Fin.cons z.1 (Fin.cons (e v) (Fin.cons (e w) ![]))) < 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.boundaryFrameReversing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.boundaryFrameReversing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.boundaryFrameReversing ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.boundaryFrameReversing

noncomputable def toSphericalCapping (X : SmoothCutCapTransition P Q D N)
    (hboundary : X.boundaryFrameReversing) :
    DifferentialGeometry.Topology.SphericalCapping P.toClosedOrientedManifold
      N.toClosedOrientedManifold (SphericalTubeSystem.ofSmoothCutCapTransition X) where
  coreCharts := X.coreCharts
  coreSmooth := X.coreSmooth
  core_induced := X.core_induced
  core_compact := isCompact_iff_compactSpace.mpr X.core_compact
  core_boundary := X.core_boundary
  coreInclusion := X.trace.capping.coreInclusion
  core_embedding := X.core_inclusion_smooth
  cap := fun b => X.capClosedCell b
  cap_embedding := fun b => X.capClosedCell_isSmoothEmbedding b
  attaching := X.attaching
  boundary_eq := fun b z => X.capClosedCell_boundary_eq b z
  exhaustive := X.exhaustive_capClosedCell
  core_cap_intersection := fun b => X.core_cap_intersection_capClosedCell b
  cap_disjoint := X.cap_disjoint_capClosedCell
  core_positive := X.core_positive
  cap_positive := fun b x hx => X.capClosedCell_positive b x hx
  boundary_orientation_reversing := hboundary

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.toSphericalCapping then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.toSphericalCapping"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.toSphericalCapping ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.toSphericalCapping

noncomputable def toSphericalCappingCompletion (X : SmoothCutCapTransition P Q D N)
    (hboundary : X.boundaryFrameReversing) : SphericalCappingCompletion X where
  capping := X.toSphericalCapping hboundary
  coreInclusion_eq := fun _ => rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.toSphericalCappingCompletion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.toSphericalCappingCompletion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.toSphericalCappingCompletion ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.toSphericalCappingCompletion

noncomputable def toSmoothCutCapCompletion (X : SmoothCutCapTransition P Q D N)
    (hboundary : X.boundaryFrameReversing) : SmoothCutCapCompletion X :=
  SmoothCutCapCompletion.ofSphericalCappingCompletion X (X.toSphericalCappingCompletion hboundary)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.toSmoothCutCapCompletion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.toSmoothCutCapCompletion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.toSmoothCutCapCompletion ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.toSmoothCutCapCompletion

end SmoothCutCapTransition

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end

end

section

set_option autoImplicit false
noncomputable section

open _root_.Set _root_.Function _root_.Manifold _root_.Submission.Manifold _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactLtRealNegOfNat_differentialGeometry : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactLtRealNegOfNat_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactLtRealNegOfNat_differentialGeometry target :: scope.openDecls } }

variable {P Q D N : OrientedThreeStage.{u}} (X : SmoothCutCapTransition P Q D N)

theorem SmoothCutCapTransition.outwardVector_eq (b : X.trace.tubes.Boundary)
    (z : Sphere 2) :
    (SphericalTubeSystem.ofSmoothCutCapTransition X).outwardVector b z =
      mfderiv ((𝓡 2).prod (𝓡∂ 1)) (𝓡 3) (X.trace.tubes.tube b.1)
        (z, TubeSystem.boundaryLevel b.2)
        (0, (if b.2 then (-1 : ℝ) else 1) • EuclideanSpace.single 0 (1 : ℝ)) := by
  rcases b with ⟨i, side⟩
  cases side <;> simp only [DifferentialGeometry.Topology.SphericalTubeSystem.outwardVector,
    Bool.false_eq_true, if_false, if_true, one_smul, neg_smul]
  all_goals rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.outwardVector_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.outwardVector_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.outwardVector_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.outwardVector_eq

theorem SmoothCutCapTransition.boundaryFrameReversing_iff_tubeFrame :
    X.boundaryFrameReversing ↔
      ∀ (b : X.trace.tubes.Boundary) (z : Sphere 2) (v w : TangentSpace (𝓡 2) z),
        let β := X.trace.tubes.boundarySphere b ∘ X.attaching b
        0 < ((P.orientation.orientation (β z)).someBasis (by
          change Fintype.card (Fin 3) = Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))
          simp)).det
          ![mfderiv ((𝓡 2).prod (𝓡∂ 1)) (𝓡 3) (X.trace.tubes.tube b.1)
              (X.attaching b z, TubeSystem.boundaryLevel b.2)
              (0, (if b.2 then (-1 : ℝ) else 1) • EuclideanSpace.single 0 (1 : ℝ)),
            mfderiv (𝓡 2) (𝓡 3) β z v, mfderiv (𝓡 2) (𝓡 3) β z w] ↔
          (if b.2 then (1 : ℝ) else -1) * (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.det
            ![z.val, mfderiv (𝓡 2) (𝓡 3) (Subtype.val : Sphere 2 → EuclideanSpace ℝ (Fin 3)) z v,
              mfderiv (𝓡 2) (𝓡 3) (Subtype.val : Sphere 2 → EuclideanSpace ℝ (Fin 3)) z w] < 0 := by
  have heq (b : X.trace.tubes.Boundary) :
      (SphericalTubeSystem.ofSmoothCutCapTransition X).boundarySphere b =
        X.trace.tubes.boundarySphere b := rfl
  constructor
  · intro h b z v w
    have hh := h b z v w
    dsimp only at hh ⊢
    erw [X.outwardVector_eq, heq] at hh
    exact hh
  · intro h b z v w
    have hh := h b z v w
    dsimp only at hh ⊢
    erw [X.outwardVector_eq, heq]
    exact hh

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.boundaryFrameReversing_iff_tubeFrame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.boundaryFrameReversing_iff_tubeFrame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.boundaryFrameReversing_iff_tubeFrame ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.boundaryFrameReversing_iff_tubeFrame

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end

end
