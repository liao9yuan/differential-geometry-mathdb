import Submission.DifferentialGeometry.Topology.Manifold.InverseFunctionTheorem.Basic
import Submission.DifferentialGeometry.Topology.Covering.Smooth.Manifold

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Function _root_.Filter
open scoped _root_.Topology _root_.ContDiff _root_.Manifold

noncomputable section

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Topology
namespace UniversalCover

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  [ConnectedSpace M] [LocallyPathConnectedSpace M]
  [DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace M]
  [Inhabited M]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
  [ConnectedSpace M] in
private theorem proj_deriv_id
    (x' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :
    HasMFDerivAt I I
      (proj : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M → M)
      x' (ContinuousLinearMap.id ℝ E) := by
  refine ⟨(proj_contMDiff (I := I) (M := M)).continuous.continuousAt, ?_⟩
  have hEq :
      writtenInExtChartAt I I x'
          (proj : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M → M)
        =ᶠ[𝓝[_root_.Set.range I] (extChartAt I x' x')] (id : E → E) := by
    have hmem : (extChartAt I x').target ∈ 𝓝[_root_.Set.range I] (extChartAt I x' x') :=
      extChartAt_target_mem_nhdsWithin x'
    refine Filter.eventuallyEq_of_mem hmem ?_
    intro y hy
    change extChartAt I (proj (X := M) x')
        (proj (X := M) ((extChartAt I x').symm y)) = y
    have hproj :=
      (extChartAt_proj_eq (I := I) (M := M) x'
        ((extChartAt I x').symm y)).symm
    rw [hproj]
    exact (extChartAt I x').right_inv hy
  have hId : HasFDerivWithinAt (id : E → E) (ContinuousLinearMap.id ℝ E)
      (_root_.Set.range I) (extChartAt I x' x') :=
    (hasFDerivAt_id _).hasFDerivWithinAt
  have hx0 :
      writtenInExtChartAt I I x'
          (proj : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M → M)
          (extChartAt I x' x') =
        (id : E → E) (extChartAt I x' x') := by
    change extChartAt I (proj (X := M) x')
        (proj (X := M) ((extChartAt I x').symm (extChartAt I x' x'))) =
      extChartAt I x' x'
    have hproj :=
      (extChartAt_proj_eq (I := I) (M := M) x'
        ((extChartAt I x').symm (extChartAt I x' x'))).symm
    rw [hproj, extChartAt_to_inv]
  exact hId.congr_of_eventuallyEq hEq hx0

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.proj_deriv_id
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.proj_deriv_id target :: scope.openDecls } }

omit [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M] in
theorem proj_localDiffeo :
    IsLocalDiffeomorph I I ∞
      (proj : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M → M) := by
  rw [isLocalDiffeomorph_iff_isLocalDiffeomorphOn_univ]
  refine DifferentialGeometry.Coordinates.contMDiffOn_isLocalDiffeomorphOn_infty isOpen_univ
    (proj_contMDiff (I := I) (M := M)).contMDiffOn ?_
  intro x _
  have hderiv := (proj_deriv_id (I := I) (M := M) x).2
  rw [ModelWithCorners.Boundaryless.range_eq_univ] at hderiv
  have hat :
      HasFDerivAt
        (writtenInExtChartAt I I x
          (proj : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M → M))
        (ContinuousLinearMap.id ℝ E) (extChartAt I x x) :=
    hderiv.hasFDerivAt_of_univ
  rw [hat.fderiv]
  change (ContinuousLinearMap.id ℝ E).IsInvertible
  exact ContinuousLinearMap.isInvertible_equiv
    (f := ContinuousLinearEquiv.refl ℝ E)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.proj_localDiffeo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.proj_localDiffeo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.proj_localDiffeo ``Submission.DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.proj_localDiffeo

end UniversalCover
end Topology
end Riemannian
end Geometry
end DifferentialGeometry
