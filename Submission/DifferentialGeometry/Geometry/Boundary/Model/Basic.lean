import Mathlib.Init
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Defs.Induced
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.Set _root_.Function _root_.Topology
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem
namespace WithBoundary

universe uE uH

class HasSmoothBoundary
    (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : Type uH) [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H) where
  boundaryE : Type uE
  [boundaryENormedGroup : NormedAddCommGroup boundaryE]
  [boundaryENormedSpace : NormedSpace ℝ boundaryE]
  [boundaryEInnerProductSpace : InnerProductSpace ℝ boundaryE]
  [boundaryEFiniteDimensional : FiniteDimensional ℝ boundaryE]
  boundaryH : Type uH
  [boundaryHTopologicalSpace : TopologicalSpace boundaryH]
  boundaryI : ModelWithCorners ℝ boundaryE boundaryH
  [boundaryIBoundaryless : boundaryI.Boundaryless]
  inclH : boundaryH → H
  inclH_continuous : Continuous inclH
  inclH_injective : Function.Injective inclH
  inclH_isInducing : _root_.Topology.IsInducing inclH
  inclH_isClosed_image : IsClosed (Set.range (I ∘ inclH))
  projE : E → boundaryE
  projE_continuous : Continuous projE
  projE_contDiff : ContDiff ℝ ∞ projE
  I_inclH_boundaryI_symm_contDiff : ContDiff ℝ ∞ (I ∘ inclH ∘ boundaryI.symm)
  range_I_inclH : Set.range (I ∘ inclH) = frontier (Set.range I)
  proj_inclH_compat : ∀ x : boundaryH, projE (I (inclH x)) = boundaryI x
  inwardCoordE : E
  inwardCoordE_enters :
    ∀ y ∈ frontier (Set.range I), ∃ ε : ℝ, 0 < ε ∧
      ∀ t ∈ Set.Ioc 0 ε,
        y + t • inwardCoordE ∈ interior (Set.range I)
  inwardCoordE_transverse :
    ∀ y : boundaryE, inwardCoordE ∉ Set.range
      (fderiv ℝ ((I : H → E) ∘ inclH ∘ boundaryI.symm) y)
  range_frontier_basis_addHaar_zero :
    ∀ [_h : FiniteDimensional ℝ E],
      letI : MeasurableSpace E := borel E
      haveI : BorelSpace E := ⟨rfl⟩
      ((Module.finBasis ℝ E).addHaar : MeasureTheory.Measure E)
          (frontier (Set.range I)) = 0
  finrank_boundaryE_succ :
    ∀ [_h : FiniteDimensional ℝ E],
      Module.finrank ℝ boundaryE + 1 = Module.finrank ℝ E

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary

instance HasSmoothBoundary.instNormedAddCommGroupBoundaryE
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [hI : HasSmoothBoundary E H I] :
    NormedAddCommGroup hI.boundaryE := hI.boundaryENormedGroup

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.instNormedAddCommGroupBoundaryE then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.instNormedAddCommGroupBoundaryE"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.instNormedAddCommGroupBoundaryE ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.instNormedAddCommGroupBoundaryE

instance HasSmoothBoundary.instNormedSpaceBoundaryE
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [hI : HasSmoothBoundary E H I] :
    NormedSpace ℝ hI.boundaryE := hI.boundaryENormedSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.instNormedSpaceBoundaryE then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.instNormedSpaceBoundaryE"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.instNormedSpaceBoundaryE ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.instNormedSpaceBoundaryE

instance HasSmoothBoundary.instInnerProductSpaceBoundaryE
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [hI : HasSmoothBoundary E H I] :
    InnerProductSpace ℝ hI.boundaryE := hI.boundaryEInnerProductSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.instInnerProductSpaceBoundaryE then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.instInnerProductSpaceBoundaryE"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.instInnerProductSpaceBoundaryE ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.instInnerProductSpaceBoundaryE

instance HasSmoothBoundary.instFiniteDimensionalBoundaryE
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [hI : HasSmoothBoundary E H I] :
    FiniteDimensional ℝ hI.boundaryE := hI.boundaryEFiniteDimensional

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.instFiniteDimensionalBoundaryE then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.instFiniteDimensionalBoundaryE"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.instFiniteDimensionalBoundaryE ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.instFiniteDimensionalBoundaryE

instance HasSmoothBoundary.instTopologicalSpaceBoundaryH
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [hI : HasSmoothBoundary E H I] :
    TopologicalSpace hI.boundaryH := hI.boundaryHTopologicalSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.instTopologicalSpaceBoundaryH then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.instTopologicalSpaceBoundaryH"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.instTopologicalSpaceBoundaryH ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.instTopologicalSpaceBoundaryH

instance HasSmoothBoundary.instBoundarylessBoundaryI
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [hI : HasSmoothBoundary E H I] :
    hI.boundaryI.Boundaryless := hI.boundaryIBoundaryless

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.instBoundarylessBoundaryI then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.instBoundarylessBoundaryI"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.instBoundarylessBoundaryI ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.instBoundarylessBoundaryI

namespace HasSmoothBoundary

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H]

abbrev boundaryModelE (I : ModelWithCorners ℝ E H) [hI : HasSmoothBoundary E H I] :
    Type _ := hI.boundaryE

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.boundaryModelE then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.boundaryModelE"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.boundaryModelE ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.boundaryModelE

abbrev boundaryModelH (I : ModelWithCorners ℝ E H) [hI : HasSmoothBoundary E H I] :
    Type _ := hI.boundaryH

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.boundaryModelH then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.boundaryModelH"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.boundaryModelH ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.boundaryModelH

abbrev boundaryModel
    (I : ModelWithCorners ℝ E H) [hI : HasSmoothBoundary E H I] :
    ModelWithCorners ℝ hI.boundaryE hI.boundaryH := hI.boundaryI

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.boundaryModel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.boundaryModel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.boundaryModel ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.boundaryModel

section Inclusion

variable (I : ModelWithCorners ℝ E H) [hI : HasSmoothBoundary E H I]

theorem inclH_isEmbedding : _root_.Topology.IsEmbedding hI.inclH where
  toIsInducing := hI.inclH_isInducing
  injective := hI.inclH_injective

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.inclH_isEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.inclH_isEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.inclH_isEmbedding ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.inclH_isEmbedding

theorem continuous_I_inclH : Continuous (I ∘ hI.inclH) :=
  I.continuous.comp hI.inclH_continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.continuous_I_inclH then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.continuous_I_inclH"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.continuous_I_inclH ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.continuous_I_inclH

theorem injective_I_inclH : Function.Injective (I ∘ hI.inclH) :=
  I.injective.comp hI.inclH_injective

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.injective_I_inclH then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.injective_I_inclH"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.injective_I_inclH ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.injective_I_inclH

end Inclusion

section Range

variable (I : ModelWithCorners ℝ E H) [hI : HasSmoothBoundary E H I]

theorem range_I_inclH_subset_frontier :
    Set.range (I ∘ hI.inclH) ⊆ frontier (Set.range I) := by
  rw [hI.range_I_inclH]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.range_I_inclH_subset_frontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.range_I_inclH_subset_frontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.range_I_inclH_subset_frontier ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.range_I_inclH_subset_frontier

theorem frontier_subset_range_I_inclH :
    frontier (Set.range I) ⊆ Set.range (I ∘ hI.inclH) := by
  rw [hI.range_I_inclH]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.frontier_subset_range_I_inclH then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.frontier_subset_range_I_inclH"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.frontier_subset_range_I_inclH ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.frontier_subset_range_I_inclH

theorem mem_frontier_range_iff_exists_inclH (y : E) :
    y ∈ frontier (Set.range I) ↔ ∃ x : hI.boundaryH, y = I (hI.inclH x) := by
  rw [← hI.range_I_inclH]
  refine ⟨?_, ?_⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.mem_frontier_range_iff_exists_inclH then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.mem_frontier_range_iff_exists_inclH"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.mem_frontier_range_iff_exists_inclH ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.mem_frontier_range_iff_exists_inclH

theorem frontier_range_eq_range_I_inclH :
    frontier (Set.range I) = Set.range (I ∘ hI.inclH) := hI.range_I_inclH.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.frontier_range_eq_range_I_inclH then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.frontier_range_eq_range_I_inclH"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.frontier_range_eq_range_I_inclH ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.frontier_range_eq_range_I_inclH

theorem mem_range_inclH_iff (h : H) :
    (∃ z : hI.boundaryH, hI.inclH z = h) ↔ I h ∈ frontier (Set.range I) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨z, rfl⟩
    rw [hI.range_I_inclH.symm]
    exact ⟨z, rfl⟩
  · intro hH
    rw [← hI.range_I_inclH] at hH
    obtain ⟨z, hz⟩ := hH
    refine ⟨z, ?_⟩
    have hz' : I (hI.inclH z) = I h := hz
    exact I.injective hz'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.mem_range_inclH_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.mem_range_inclH_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.mem_range_inclH_iff ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.mem_range_inclH_iff

end Range

section Compat

variable (I : ModelWithCorners ℝ E H) [hI : HasSmoothBoundary E H I]

theorem proj_inclH_apply (x : hI.boundaryH) :
    hI.projE (I (hI.inclH x)) = hI.boundaryI x := hI.proj_inclH_compat x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.proj_inclH_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.proj_inclH_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.proj_inclH_apply ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.proj_inclH_apply

theorem projE_comp_I_comp_inclH :
    hI.projE ∘ I ∘ hI.inclH = hI.boundaryI := by
  funext x
  simpa [Function.comp] using hI.proj_inclH_compat x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.projE_comp_I_comp_inclH then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.projE_comp_I_comp_inclH"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.projE_comp_I_comp_inclH ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.projE_comp_I_comp_inclH

end Compat

section TopologicalDerived

variable (I : ModelWithCorners ℝ E H) [hI : HasSmoothBoundary E H I]

theorem mem_range_I_inclH_iff (y : E) :
    y ∈ Set.range (I ∘ hI.inclH) ↔ ∃ x : hI.boundaryH, I (hI.inclH x) = y := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.mem_range_I_inclH_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.mem_range_I_inclH_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.mem_range_I_inclH_iff ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.mem_range_I_inclH_iff

theorem isClosed_range_I_inclH : IsClosed (Set.range (I ∘ hI.inclH)) :=
  hI.inclH_isClosed_image

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.isClosed_range_I_inclH then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.isClosed_range_I_inclH"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.isClosed_range_I_inclH ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.isClosed_range_I_inclH

omit hI in
theorem isClosed_frontier_range :
    IsClosed (frontier (Set.range I)) := isClosed_frontier

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.isClosed_frontier_range then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.isClosed_frontier_range"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.isClosed_frontier_range ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.isClosed_frontier_range

end TopologicalDerived

section EmbeddingDerived

variable (I : ModelWithCorners ℝ E H) [hI : HasSmoothBoundary E H I]

theorem isInducing_I_inclH : _root_.Topology.IsInducing (I ∘ hI.inclH) := by
  have hI_inducing : _root_.Topology.IsInducing (I : H → E) := I.isClosedEmbedding.isEmbedding.isInducing
  exact hI_inducing.comp hI.inclH_isInducing

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.isInducing_I_inclH then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.isInducing_I_inclH"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.isInducing_I_inclH ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.isInducing_I_inclH

theorem isEmbedding_I_inclH : _root_.Topology.IsEmbedding (I ∘ hI.inclH) where
  toIsInducing := isInducing_I_inclH I
  injective := injective_I_inclH I

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.isEmbedding_I_inclH then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.isEmbedding_I_inclH"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.isEmbedding_I_inclH ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.isEmbedding_I_inclH

theorem isClosedEmbedding_I_inclH : _root_.Topology.IsClosedEmbedding (I ∘ hI.inclH) where
  toIsEmbedding := isEmbedding_I_inclH I
  isClosed_range := hI.inclH_isClosed_image

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.isClosedEmbedding_I_inclH then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.isClosedEmbedding_I_inclH"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.isClosedEmbedding_I_inclH ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.isClosedEmbedding_I_inclH

end EmbeddingDerived

section SmoothnessDerived

variable (I : ModelWithCorners ℝ E H) [hI : HasSmoothBoundary E H I]

theorem projE_contDiffOn (s : Set E) : ContDiffOn ℝ ∞ hI.projE s :=
  hI.projE_contDiff.contDiffOn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.projE_contDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.projE_contDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.projE_contDiffOn ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.projE_contDiffOn

theorem I_inclH_boundaryI_symm_contDiffOn (s : Set hI.boundaryE) :
    ContDiffOn ℝ ∞ ((I : H → E) ∘ hI.inclH ∘ hI.boundaryI.symm) s :=
  hI.I_inclH_boundaryI_symm_contDiff.contDiffOn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.I_inclH_boundaryI_symm_contDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.I_inclH_boundaryI_symm_contDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.I_inclH_boundaryI_symm_contDiffOn ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.I_inclH_boundaryI_symm_contDiffOn

end SmoothnessDerived

section NullSetDerived

variable (I : ModelWithCorners ℝ E H) [hI : HasSmoothBoundary E H I]
variable [FiniteDimensional ℝ E]

theorem range_frontier_basisAddHaar_volume_zero :
    letI : MeasurableSpace E := borel E
    haveI : BorelSpace E := ⟨rfl⟩
    ((Module.finBasis ℝ E).addHaar : MeasureTheory.Measure E)
        (frontier (Set.range I)) = 0 := by
  exact hI.range_frontier_basis_addHaar_zero

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.range_frontier_basisAddHaar_volume_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.range_frontier_basisAddHaar_volume_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.range_frontier_basisAddHaar_volume_zero ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.range_frontier_basisAddHaar_volume_zero

theorem range_inclH_basisAddHaar_volume_zero :
    letI : MeasurableSpace E := borel E
    haveI : BorelSpace E := ⟨rfl⟩
    ((Module.finBasis ℝ E).addHaar : MeasureTheory.Measure E)
        (Set.range ((I : H → E) ∘ hI.inclH)) = 0 := by
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  rw [hI.range_I_inclH]
  exact hI.range_frontier_basis_addHaar_zero

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.range_inclH_basisAddHaar_volume_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.range_inclH_basisAddHaar_volume_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.range_inclH_basisAddHaar_volume_zero ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.range_inclH_basisAddHaar_volume_zero

theorem subset_range_frontier_basisAddHaar_volume_zero
    {S : Set E} (hS : S ⊆ frontier (Set.range I)) :
    letI : MeasurableSpace E := borel E
    haveI : BorelSpace E := ⟨rfl⟩
    ((Module.finBasis ℝ E).addHaar : MeasureTheory.Measure E) S = 0 := by
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  exact MeasureTheory.measure_mono_null hS hI.range_frontier_basis_addHaar_zero

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.subset_range_frontier_basisAddHaar_volume_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.subset_range_frontier_basisAddHaar_volume_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.subset_range_frontier_basisAddHaar_volume_zero ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.subset_range_frontier_basisAddHaar_volume_zero

end NullSetDerived

section Boundaryless

variable (I : ModelWithCorners ℝ E H) [hI : HasSmoothBoundary E H I]

theorem boundaryH_isEmpty_of_boundaryless [I.Boundaryless] :
    IsEmpty hI.boundaryH := by
  refine ⟨fun x => ?_⟩
  have h_in : I (hI.inclH x) ∈ Set.range (I ∘ hI.inclH) := ⟨x, rfl⟩
  rw [hI.range_I_inclH] at h_in
  rw [show frontier (Set.range I) = ∅ from ?_] at h_in
  · exact (Set.notMem_empty _ h_in)
  · rw [I.range_eq_univ, frontier_univ]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.boundaryH_isEmpty_of_boundaryless then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.boundaryH_isEmpty_of_boundaryless"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.boundaryH_isEmpty_of_boundaryless ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.boundaryH_isEmpty_of_boundaryless

end Boundaryless

end HasSmoothBoundary

end WithBoundary
end DivergenceTheorem
end Integral
end DifferentialGeometry
