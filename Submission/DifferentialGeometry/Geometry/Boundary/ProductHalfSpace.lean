import Submission.DifferentialGeometry.Geometry.Boundary.Model.Basic
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Linear

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Function _root_.Topology
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Geometry.Boundary

open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem interior_range_productHalfSpace :
    interior (_root_.Set.range ((𝓘(ℝ, E)).prod (𝓡∂ 1))) =
      {y : E × EuclideanSpace ℝ (Fin 1) | 0 < y.2 0} := by
  rw [ModelWithCorners.range_prod, ModelWithCorners.Boundaryless.range_eq_univ,
    interior_prod_eq, interior_univ, interior_range_modelWithCornersEuclideanHalfSpace]
  ext y
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Boundary.interior_range_productHalfSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Boundary.interior_range_productHalfSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Boundary.interior_range_productHalfSpace ``Submission.DifferentialGeometry.Geometry.Boundary.interior_range_productHalfSpace

theorem frontier_range_productHalfSpace :
    frontier (_root_.Set.range ((𝓘(ℝ, E)).prod (𝓡∂ 1))) =
      {y : E × EuclideanSpace ℝ (Fin 1) | y.2 0 = 0} := by
  rw [ModelWithCorners.range_prod, ModelWithCorners.Boundaryless.range_eq_univ,
    frontier_univ_prod_eq, frontier_range_modelWithCornersEuclideanHalfSpace]
  ext y
  simp [eq_comm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Boundary.frontier_range_productHalfSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Boundary.frontier_range_productHalfSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Boundary.frontier_range_productHalfSpace ``Submission.DifferentialGeometry.Geometry.Boundary.frontier_range_productHalfSpace

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
private theorem range_boundary_inclusion :
    _root_.Set.range (fun x : E ↦ (x, (0 : EuclideanSpace ℝ (Fin 1)))) =
      {y : E × EuclideanSpace ℝ (Fin 1) | y.2 0 = 0} := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    rfl
  · intro hy
    change y.2 0 = 0 at hy
    have hz : y.2 = 0 := by
      ext i
      have hi : i = 0 := Subsingleton.elim _ _
      simpa only [hi, PiLp.zero_apply] using hy
    exact ⟨y.1, Prod.ext rfl hz.symm⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Boundary.range_boundary_inclusion
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Boundary.range_boundary_inclusion target :: scope.openDecls } }

private theorem boundary_basisAddHaar_zero [FiniteDimensional ℝ E] :
    letI : MeasurableSpace (E × EuclideanSpace ℝ (Fin 1)) := borel _
    haveI : BorelSpace (E × EuclideanSpace ℝ (Fin 1)) := ⟨rfl⟩
    ((Module.finBasis ℝ (E × EuclideanSpace ℝ (Fin 1))).addHaar :
      MeasureTheory.Measure (E × EuclideanSpace ℝ (Fin 1)))
      (frontier (_root_.Set.range ((𝓘(ℝ, E)).prod (𝓡∂ 1)))) = 0 := by
  let : MeasurableSpace (E × EuclideanSpace ℝ (Fin 1)) := borel _
  have : BorelSpace (E × EuclideanSpace ℝ (Fin 1)) := ⟨rfl⟩
  let L : (E × EuclideanSpace ℝ (Fin 1)) →L[ℝ] ℝ :=
    (EuclideanSpace.proj 0).comp (ContinuousLinearMap.snd ℝ E (EuclideanSpace ℝ (Fin 1)))
  rw [frontier_range_productHalfSpace]
  have hker : {y : E × EuclideanSpace ℝ (Fin 1) | y.2 0 = 0} =
      (L.toLinearMap.ker : Set (E × EuclideanSpace ℝ (Fin 1))) := rfl
  rw [hker]
  apply MeasureTheory.Measure.addHaar_submodule
  intro htop
  have hv : ((0 : E), EuclideanSpace.single 0 (1 : ℝ)) ∈ L.toLinearMap.ker := by
    rw [htop]
    exact Submodule.mem_top
  change (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) 0 = 0 at hv
  norm_num [PiLp.single_apply] at hv

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Boundary.boundary_basisAddHaar_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Boundary.boundary_basisAddHaar_zero target :: scope.openDecls } }

instance instHasSmoothBoundaryProductHalfSpace [FiniteDimensional ℝ E] :
    HasSmoothBoundary (E × EuclideanSpace ℝ (Fin 1))
      (ModelProd E (EuclideanHalfSpace 1)) ((𝓘(ℝ, E)).prod (𝓡∂ 1)) where
  boundaryE := E
  boundaryENormedGroup := inferInstance
  boundaryENormedSpace := inferInstance
  boundaryEInnerProductSpace := inferInstance
  boundaryEFiniteDimensional := inferInstance
  boundaryH := E
  boundaryHTopologicalSpace := inferInstance
  boundaryI := 𝓘(ℝ, E)
  boundaryIBoundaryless := inferInstance
  inclH := fun x ↦ (x, (0 : EuclideanHalfSpace 1))
  inclH_continuous := continuous_id.prodMk continuous_const
  inclH_injective := fun _ _ h ↦ congrArg Prod.fst h
  inclH_isInducing := isInducing_prodMkLeft (0 : EuclideanHalfSpace 1)
  inclH_isClosed_image := by
    change IsClosed (_root_.Set.range (fun x : E ↦ (x, (0 : EuclideanSpace ℝ (Fin 1)))))
    rw [range_boundary_inclusion]
    exact isClosed_eq ((PiLp.continuous_apply 2 _ 0).comp continuous_snd) continuous_const
  projE := Prod.fst
  projE_continuous := continuous_fst
  projE_contDiff := contDiff_fst
  I_inclH_boundaryI_symm_contDiff := by
    change ContDiff ℝ ∞ (fun x : E ↦ (x, (0 : EuclideanSpace ℝ (Fin 1))))
    exact contDiff_id.prodMk contDiff_const
  range_I_inclH := by
    change _root_.Set.range (fun x : E ↦ (x, (0 : EuclideanSpace ℝ (Fin 1)))) = _
    rw [range_boundary_inclusion, frontier_range_productHalfSpace]
  proj_inclH_compat := fun _ ↦ rfl
  inwardCoordE := ((0 : E), EuclideanSpace.single (0 : Fin 1) (1 : ℝ))
  inwardCoordE_enters := by
    intro y hy
    rw [frontier_range_productHalfSpace] at hy
    change y.2 0 = 0 at hy
    refine ⟨1, zero_lt_one, ?_⟩
    intro t ht
    rw [interior_range_productHalfSpace]
    change 0 < ((y.2 + t • EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) :
      EuclideanSpace ℝ (Fin 1)) 0
    simpa only [PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply, ite_true,
      smul_eq_mul, hy, zero_add, mul_one] using ht.1
  inwardCoordE_transverse := by
    intro y
    change ((0 : E), EuclideanSpace.single 0 (1 : ℝ)) ∉
      _root_.Set.range (fderiv ℝ (ContinuousLinearMap.inl ℝ E (EuclideanSpace ℝ (Fin 1)) :
        E → E × EuclideanSpace ℝ (Fin 1)) y)
    rw [(ContinuousLinearMap.inl ℝ E (EuclideanSpace ℝ (Fin 1))).fderiv]
    rintro ⟨x, hx⟩
    have h := congrArg (fun z : E × EuclideanSpace ℝ (Fin 1) ↦ z.2 0) hx
    change (0 : ℝ) = (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) 0 at h
    norm_num [PiLp.single_apply] at h
  range_frontier_basis_addHaar_zero := by
    intro _
    exact boundary_basisAddHaar_zero E
  finrank_boundaryE_succ := by
    intro _
    simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Boundary.instHasSmoothBoundaryProductHalfSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Boundary.instHasSmoothBoundaryProductHalfSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Boundary.instHasSmoothBoundaryProductHalfSpace ``Submission.DifferentialGeometry.Geometry.Boundary.instHasSmoothBoundaryProductHalfSpace

end DifferentialGeometry.Geometry.Boundary
