import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChartSimplexBlend
import Submission.DifferentialGeometry.Bundle.Orientation.Map
import Mathlib.Geometry.Manifold.MFDeriv.Tangent

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Manifold _root_.Set
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M]

private theorem exists_orientation_adjustment (o : Orientation ℝ ThreeSpace (Fin 3)) :
    ∃ L : ThreeSpace ≃L[ℝ] ThreeSpace,
      Orientation.map (Fin 3) L.toLinearEquiv o = standardThreeOrientation := by
  let b₀ := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  let b := b₀.adjustToOrientation o
  let L := (b.equiv b₀ (Equiv.refl (Fin 3))).toContinuousLinearEquiv
  refine ⟨L, ?_⟩
  have hb : b.orientation = o := b₀.orientation_adjustToOrientation o
  have he : b.map L.toLinearEquiv = b₀ := by
    change b.map (b.equiv b₀ (Equiv.refl (Fin 3))) = b₀
    simp
  rw [← hb, ← Module.Basis.orientation_map, he]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_orientation_adjustment
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_orientation_adjustment target :: scope.openDecls } }


theorem exists_open_orientedChartSimplex (o : TangentOrientationSection M) (p : M) :
    ∃ (e : OpenPartialHomeomorph M ThreeSpace) (U : Set M),
      IsOpen U ∧ p ∈ U ∧ ∀ y ∈ U, ∃ T : OrientedChartSimplex o y, T.chart = e := by
  have hp : p ∈ (_root_.FiberBundle.trivializationAt ThreeSpace (TangentSpace ThreeModel) p).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt ThreeSpace (TangentSpace ThreeModel) p
  obtain ⟨L, hL⟩ := exists_orientation_adjustment
    (Orientation.map (Fin 3) (tangentChartEquiv M p p hp) (o.orientation p))
  obtain ⟨U, hUopen, hpU, hU, hconst⟩ := o.locally_constant p p hp
  let e₀ := chartAt ThreeSpace p
  let e : OpenPartialHomeomorph M ThreeSpace :=
    e₀.trans L.toHomeomorph.toOpenPartialHomeomorph
  refine ⟨e, U, hUopen, hpU, fun y hy => ?_⟩
  have hy₀ : y ∈ e₀.source := hU hy
  have hyE : y ∈ e.source := by
    change y ∈ e₀.source ∩ e₀ ⁻¹' Set.univ
    exact ⟨hy₀, Set.mem_univ _⟩
  have hd₀ : MDifferentiableAt ThreeModel ThreeModel e₀ y :=
    mdifferentiableAt_extChartAt (I := ThreeModel) hy₀
  have hLd : HasMFDerivAt ThreeModel ThreeModel L (e₀ y)
      (L : ThreeSpace →L[ℝ] ThreeSpace) :=
    L.toContinuousLinearMap.hasFDerivAt.hasMFDerivAt
  have hd : MDifferentiableAt ThreeModel ThreeModel e y :=
    hLd.mdifferentiableAt.comp y hd₀
  have hD : (mfderiv ThreeModel ThreeModel e₀ y).toLinearMap =
      (tangentChartEquiv M p y (hU hy)).toLinearMap := by
    rw [mfderiv_chartAt_eq_tangentCoordChange hy₀]
    rfl
  have hderiv : mfderiv ThreeModel ThreeModel e y =
      (L : ThreeSpace →L[ℝ] ThreeSpace).comp
        (mfderiv ThreeModel ThreeModel e₀ y) := by
    have h := mfderiv_comp y hLd.mdifferentiableAt hd₀
    change mfderiv ThreeModel ThreeModel e y = _ at h
    rw [hLd.mfderiv] at h
    exact h
  have hbij₀ : Function.Bijective (mfderiv ThreeModel ThreeModel e₀ y) := by
    change Function.Bijective (mfderiv ThreeModel ThreeModel e₀ y).toLinearMap
    rw [hD]
    exact (tangentChartEquiv M p y (hU hy)).bijective
  have hbij : Function.Bijective (mfderiv ThreeModel ThreeModel e y) := by
    rw [hderiv]
    exact L.bijective.comp hbij₀
  have hlinear :
      LinearEquiv.ofBijective (mfderiv ThreeModel ThreeModel e y).toLinearMap hbij =
        (tangentChartEquiv M p y (hU hy)).trans L.toLinearEquiv := by
    ext v
    change mfderiv ThreeModel ThreeModel e y v = L (tangentChartEquiv M p y (hU hy) v)
    rw [hderiv]
    exact congrArg L (DFunLike.congr_fun hD v)
  have hpositive : Orientation.map (Fin 3)
      (LinearEquiv.ofBijective (mfderiv ThreeModel ThreeModel e y).toLinearMap hbij)
        (o.orientation y) = standardThreeOrientation := by
    refine (congrArg (fun f => Orientation.map (Fin 3) f (o.orientation y)) hlinear).trans ?_
    exact (DifferentialGeometry.VectorBundle.map_orientation_trans_between
      (tangentChartEquiv M p y (hU hy)) L.toLinearEquiv (o.orientation y)).symm.trans
        ((congrArg (Orientation.map (Fin 3) L.toLinearEquiv) (hconst y hy)).trans hL)
  obtain ⟨r, hr, hins⟩ := compact_family_small_scaling positiveTetrahedron
    e.open_target (e.map_source hyE)
  have hins' : ∀ q : stdSimplex ℝ (Fin 4),
      e y + r • positiveTetrahedron q ∈ e.target :=
    hins r ⟨hr.le, le_rfl⟩
  exact ⟨{
    chart := e
    center_mem := hyE
    differentiableAt := hd
    derivative_bijective := hbij
    positive := hpositive
    radius := r
    radius_pos := hr
    simplex_inside := hins' }, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_open_orientedChartSimplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_open_orientedChartSimplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_open_orientedChartSimplex ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_open_orientedChartSimplex

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
