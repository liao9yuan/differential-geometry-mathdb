import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedSobolev
import Submission.DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.Divergence.PartialDerivWithin
import Submission.DifferentialGeometry.Geometry.Boundary.Model.EuclideanHalfSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.MeasureTheory _root_.Set _root_.Filter _root_.Topology
open scoped _root_.ENNReal _root_.NNReal _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Euclidean

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

def closedHalfSpace : Set E := {y : E | 0 ≤ y 0}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace

def openHalfSpace : Set E := {y : E | 0 < y 0}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.openHalfSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.openHalfSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.openHalfSpace ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.openHalfSpace

def boundaryHyperplane : Set E := {y : E | y 0 = 0}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.boundaryHyperplane then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.boundaryHyperplane"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.boundaryHyperplane ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.boundaryHyperplane

@[simp] lemma closedHalfSpace_def :
    closedHalfSpace (d := d) = {y : E | 0 ≤ y 0} := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace_def ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace_def

omit [NeZero d] in
theorem measurableSet_closedHalfSpace [NeZero d] :
    MeasurableSet (closedHalfSpace (d := d)) := by
  have hcont : Continuous (fun y : E => y 0) :=
    PiLp.continuous_apply 2 _ 0
  have heq : closedHalfSpace (d := d) =
      (fun y : E => y 0) ⁻¹' Set.Ici 0 := rfl
  rw [heq]
  exact hcont.measurable measurableSet_Ici

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.measurableSet_closedHalfSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.measurableSet_closedHalfSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.measurableSet_closedHalfSpace ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.measurableSet_closedHalfSpace

@[simp] lemma openHalfSpace_def :
    openHalfSpace (d := d) = {y : E | 0 < y 0} := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.openHalfSpace_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.openHalfSpace_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.openHalfSpace_def ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.openHalfSpace_def

@[simp] lemma boundaryHyperplane_def :
    boundaryHyperplane (d := d) = {y : E | y 0 = 0} := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.boundaryHyperplane_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.boundaryHyperplane_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.boundaryHyperplane_def ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.boundaryHyperplane_def

theorem openHalfSpace_subset_closedHalfSpace :
    openHalfSpace (d := d) ⊆ closedHalfSpace := by
  intro y hy
  change (0 : ℝ) ≤ y 0
  exact le_of_lt hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.openHalfSpace_subset_closedHalfSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.openHalfSpace_subset_closedHalfSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.openHalfSpace_subset_closedHalfSpace ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.openHalfSpace_subset_closedHalfSpace

theorem closedHalfSpace_eq_union :
    closedHalfSpace (d := d) = openHalfSpace ∪ boundaryHyperplane := by
  ext y
  simp only [closedHalfSpace, openHalfSpace, boundaryHyperplane,
    _root_.Set.mem_ofPred_eq, _root_.Set.mem_union]
  constructor
  · intro h
    rcases lt_or_eq_of_le h with h | h
    · exact Or.inl h
    · exact Or.inr h.symm
  · rintro (h | h)
    · exact le_of_lt h
    · exact le_of_eq h.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace_eq_union then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace_eq_union"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace_eq_union ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace_eq_union

omit [NeZero d] in
theorem isOpen_openHalfSpace [NeZero d] :
    IsOpen (openHalfSpace (d := d)) := by
  have hcont : Continuous (fun y : E => y 0) := PiLp.continuous_apply 2 _ 0
  have heq : openHalfSpace (d := d) = (fun y : E => y 0) ⁻¹' Set.Ioi 0 := rfl
  rw [heq]
  exact hcont.isOpen_preimage _ isOpen_Ioi

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.isOpen_openHalfSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.isOpen_openHalfSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.isOpen_openHalfSpace ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.isOpen_openHalfSpace

omit [NeZero d] in
theorem isClosed_boundaryHyperplane [NeZero d] :
    IsClosed (boundaryHyperplane (d := d)) := by
  have hcont : Continuous (fun y : E => y 0) := PiLp.continuous_apply 2 _ 0
  have heq : boundaryHyperplane (d := d) = (fun y : E => y 0) ⁻¹' {0} := rfl
  rw [heq]
  exact isClosed_singleton.preimage hcont

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.isClosed_boundaryHyperplane then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.isClosed_boundaryHyperplane"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.isClosed_boundaryHyperplane ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.isClosed_boundaryHyperplane

omit [NeZero d] in
theorem volume_boundaryHyperplane_eq_zero [NeZero d] :
    (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) (boundaryHyperplane (d := d)) = 0 := by
  classical
  set ker : Submodule ℝ E :=
    (EuclideanSpace.proj (0 : Fin d) :
      E →L[ℝ] ℝ).toLinearMap.ker with hker_def
  have hsubm :
      (boundaryHyperplane (d := d) : Set E) = (ker : Set E) := by
    ext y
    simp [hker_def, boundaryHyperplane, LinearMap.mem_ker,
      EuclideanSpace.proj]
  rw [hsubm]
  refine MeasureTheory.Measure.addHaar_submodule
    (μ := (_root_.MeasureTheory.MeasureSpace.volume : MeasureTheory.Measure E)) ker ?_
  intro hker_eq
  have h_in_top : EuclideanSpace.single (0 : Fin d) (1 : ℝ) ∈
      (⊤ : Submodule ℝ E) := Submodule.mem_top
  rw [← hker_eq] at h_in_top
  have h_proj_zero :
      (EuclideanSpace.proj (0 : Fin d) : E →L[ℝ] ℝ)
        (EuclideanSpace.single (0 : Fin d) (1 : ℝ)) = 0 := by
    have := h_in_top
    simp only [hker_def, LinearMap.mem_ker,
      ContinuousLinearMap.coe_coe] at this
    exact this
  have h_eval :
      (EuclideanSpace.proj (0 : Fin d) : E →L[ℝ] ℝ)
        (EuclideanSpace.single (0 : Fin d) (1 : ℝ)) =
      (EuclideanSpace.single (0 : Fin d) (1 : ℝ)) 0 := rfl
  have h_one : (EuclideanSpace.single (0 : Fin d) (1 : ℝ)) 0 = 1 := by
    rw [show (EuclideanSpace.single (0 : Fin d) (1 : ℝ)) =
          PiLp.single 2 (0 : Fin d) (1 : ℝ) from rfl]
    rw [PiLp.single_apply]
    simp
  rw [h_one] at h_eval
  exact one_ne_zero (h_proj_zero.symm.trans h_eval).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.volume_boundaryHyperplane_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.volume_boundaryHyperplane_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.volume_boundaryHyperplane_eq_zero ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.volume_boundaryHyperplane_eq_zero

def interiorHalfSpace (Ω : Set E) : Set E := Ω ∩ openHalfSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace

@[simp] lemma interiorHalfSpace_def (Ω : Set E) :
    interiorHalfSpace (d := d) Ω = Ω ∩ openHalfSpace := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace_def ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace_def

theorem interiorHalfSpace_subset (Ω : Set E) :
    interiorHalfSpace (d := d) Ω ⊆ Ω := _root_.Set.inter_subset_left

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace_subset ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace_subset

theorem interiorHalfSpace_subset_openHalfSpace (Ω : Set E) :
    interiorHalfSpace (d := d) Ω ⊆ openHalfSpace := _root_.Set.inter_subset_right

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace_subset_openHalfSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace_subset_openHalfSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace_subset_openHalfSpace ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace_subset_openHalfSpace

def IsHalfSpaceRelOpen (Ω : Set E) : Prop :=
  ∃ U : Set E, IsOpen U ∧ Ω = U ∩ closedHalfSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.IsHalfSpaceRelOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.IsHalfSpaceRelOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.IsHalfSpaceRelOpen ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.IsHalfSpaceRelOpen

theorem IsHalfSpaceRelOpen.of_isOpen_subset_open
    {Ω : Set E} (hΩ : IsOpen Ω) (hsub : Ω ⊆ openHalfSpace) :
    IsHalfSpaceRelOpen (d := d) Ω := by
  refine ⟨Ω, hΩ, ?_⟩
  apply Set.Subset.antisymm
  · intro y hy
    refine ⟨hy, ?_⟩
    exact openHalfSpace_subset_closedHalfSpace (hsub hy)
  · intro y ⟨hy, _⟩
    exact hy

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.IsHalfSpaceRelOpen
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.IsHalfSpaceRelOpen.of_isOpen_subset_open then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.IsHalfSpaceRelOpen.of_isOpen_subset_open"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.IsHalfSpaceRelOpen.of_isOpen_subset_open ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.IsHalfSpaceRelOpen.of_isOpen_subset_open

theorem IsHalfSpaceRelOpen.subset_closedHalfSpace
    {Ω : Set E} (hΩ : IsHalfSpaceRelOpen (d := d) Ω) :
    Ω ⊆ closedHalfSpace := by
  obtain ⟨U, _hU, hU_eq⟩ := hΩ
  rw [hU_eq]
  exact _root_.Set.inter_subset_right

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.IsHalfSpaceRelOpen.subset_closedHalfSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.IsHalfSpaceRelOpen.subset_closedHalfSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.IsHalfSpaceRelOpen.subset_closedHalfSpace ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.IsHalfSpaceRelOpen.subset_closedHalfSpace

theorem interiorHalfSpace_eq_inter_openHalfSpace
    {Ω : Set E} {U : Set E}
    (hU_eq : Ω = U ∩ closedHalfSpace) :
    interiorHalfSpace (d := d) Ω = U ∩ openHalfSpace := by
  unfold interiorHalfSpace
  rw [hU_eq]
  ext y
  simp only [_root_.Set.mem_inter_iff, closedHalfSpace, openHalfSpace, _root_.Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨hU, _⟩, h_open⟩
    exact ⟨hU, h_open⟩
  · rintro ⟨hU, h_open⟩
    exact ⟨⟨hU, le_of_lt h_open⟩, h_open⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace_eq_inter_openHalfSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace_eq_inter_openHalfSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace_eq_inter_openHalfSpace ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace_eq_inter_openHalfSpace

omit [NeZero d] in
theorem interiorHalfSpace_isOpen [NeZero d]
    {Ω : Set E} (hΩ : IsHalfSpaceRelOpen (d := d) Ω) :
    IsOpen (interiorHalfSpace (d := d) Ω) := by
  obtain ⟨U, hU, hU_eq⟩ := hΩ
  rw [interiorHalfSpace_eq_inter_openHalfSpace hU_eq]
  exact hU.inter (isOpen_openHalfSpace (d := d))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace_isOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace_isOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace_isOpen ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace_isOpen

theorem symmDiff_interiorHalfSpace_subset_boundaryHyperplane
    {Ω : Set E} (hΩ : IsHalfSpaceRelOpen (d := d) Ω) :
    Ω \ interiorHalfSpace Ω ⊆ boundaryHyperplane := by
  intro y ⟨hy_in, hy_notIn⟩
  unfold interiorHalfSpace at hy_notIn
  simp only [_root_.Set.mem_inter_iff, openHalfSpace, _root_.Set.mem_ofPred_eq, not_and, not_lt]
    at hy_notIn
  have h_le : y 0 ≤ 0 := hy_notIn hy_in
  have h_ge : 0 ≤ y 0 := hΩ.subset_closedHalfSpace hy_in
  exact le_antisymm h_le h_ge

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.symmDiff_interiorHalfSpace_subset_boundaryHyperplane then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.symmDiff_interiorHalfSpace_subset_boundaryHyperplane"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.symmDiff_interiorHalfSpace_subset_boundaryHyperplane ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.symmDiff_interiorHalfSpace_subset_boundaryHyperplane

omit [NeZero d] in
theorem ae_eq_interiorHalfSpace [NeZero d]
    {Ω : Set E} (hΩ : IsHalfSpaceRelOpen (d := d) Ω) :
    Ω =ᵐ[(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)] interiorHalfSpace (d := d) Ω := by
  have h_diff1 : (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) (Ω \ interiorHalfSpace Ω) = 0 := by
    have hsub :=
      symmDiff_interiorHalfSpace_subset_boundaryHyperplane (d := d) hΩ
    have h_zero := volume_boundaryHyperplane_eq_zero (d := d)
    exact MeasureTheory.measure_mono_null hsub h_zero
  have h_diff2 : (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) (interiorHalfSpace Ω \ Ω) = 0 := by
    have h_empty : interiorHalfSpace Ω \ Ω = ∅ := by
      ext y
      simp only [Set.mem_sdiff, Set.mem_empty_iff_false, iff_false]
      intro hy
      exact hy.2 (interiorHalfSpace_subset Ω hy.1)
    rw [h_empty]
    exact _root_.MeasureTheory.measure_empty
  exact (MeasureTheory.ae_eq_set).mpr ⟨h_diff1, h_diff2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.ae_eq_interiorHalfSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.ae_eq_interiorHalfSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.ae_eq_interiorHalfSpace ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.ae_eq_interiorHalfSpace

omit [NeZero d] in
theorem volume_restrict_interiorHalfSpace_eq [NeZero d]
    {Ω : Set E} (hΩ : IsHalfSpaceRelOpen (d := d) Ω) :
    (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E).restrict Ω =
      (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E).restrict (interiorHalfSpace (d := d) Ω) :=
  MeasureTheory.Measure.restrict_congr_set (ae_eq_interiorHalfSpace hΩ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.volume_restrict_interiorHalfSpace_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.volume_restrict_interiorHalfSpace_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.volume_restrict_interiorHalfSpace_eq ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.volume_restrict_interiorHalfSpace_eq

def MemWkpHalfSpace (k : ℕ) (p : ℝ≥0∞) (u : E → ℝ) (Ω : Set E) : Prop :=
  MemWkp (d := d) k p u (interiorHalfSpace Ω)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace

@[simp] lemma MemWkpHalfSpace_def
    (k : ℕ) (p : ℝ≥0∞) (u : E → ℝ) (Ω : Set E) :
    MemWkpHalfSpace (d := d) k p u Ω ↔
      MemWkp (d := d) k p u (interiorHalfSpace Ω) := Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace_def ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace_def

theorem MemWkpHalfSpace_iff_memWkp_of_subset_openHalfSpace
    {k : ℕ} {p : ℝ≥0∞} {Ω : Set E} {u : E → ℝ}
    (hsub : Ω ⊆ openHalfSpace) :
    MemWkpHalfSpace (d := d) k p u Ω ↔ MemWkp (d := d) k p u Ω := by
  unfold MemWkpHalfSpace interiorHalfSpace
  rw [show Ω ∩ openHalfSpace = Ω from _root_.Set.inter_eq_self_of_subset_left hsub]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace_iff_memWkp_of_subset_openHalfSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace_iff_memWkp_of_subset_openHalfSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace_iff_memWkp_of_subset_openHalfSpace ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace_iff_memWkp_of_subset_openHalfSpace

theorem MemWkpHalfSpace.zero_iff_memLp
    {p : ℝ≥0∞} {Ω : Set E} {u : E → ℝ} :
    MemWkpHalfSpace (d := d) 0 p u Ω ↔
      MemLp u p ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E).restrict (interiorHalfSpace Ω)) :=
  MemWkp.zero_iff_memLp

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace.zero_iff_memLp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace.zero_iff_memLp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace.zero_iff_memLp ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace.zero_iff_memLp

omit [NeZero d] in
theorem MemWkpHalfSpace.zero_iff_memLp_of_relOpen [NeZero d]
    {p : ℝ≥0∞} {Ω : Set E} (hΩ : IsHalfSpaceRelOpen (d := d) Ω) {u : E → ℝ} :
    MemWkpHalfSpace (d := d) 0 p u Ω ↔
      MemLp u p ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E).restrict Ω) := by
  rw [MemWkpHalfSpace.zero_iff_memLp,
      ← volume_restrict_interiorHalfSpace_eq hΩ]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace.zero_iff_memLp_of_relOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace.zero_iff_memLp_of_relOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace.zero_iff_memLp_of_relOpen ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace.zero_iff_memLp_of_relOpen

theorem MemWkpHalfSpace.le_succ
    {k : ℕ} {p : ℝ≥0∞} {Ω : Set E} {u : E → ℝ}
    (h : MemWkpHalfSpace (d := d) (k + 1) p u Ω) :
    MemWkpHalfSpace (d := d) k p u Ω :=
  MemWkp.le_succ h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace.le_succ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace.le_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace.le_succ ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace.le_succ

theorem MemWkpHalfSpace.le_of_le
    {k k' : ℕ} {p : ℝ≥0∞} {Ω : Set E} {u : E → ℝ}
    (hk : k ≤ k') (h : MemWkpHalfSpace (d := d) k' p u Ω) :
    MemWkpHalfSpace (d := d) k p u Ω :=
  MemWkp.le_of_le hk h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace.le_of_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace.le_of_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace.le_of_le ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace.le_of_le

theorem MemWkpHalfSpace.memLp
    {k : ℕ} {p : ℝ≥0∞} {Ω : Set E} {u : E → ℝ}
    (h : MemWkpHalfSpace (d := d) k p u Ω) :
    MemLp u p ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E).restrict (interiorHalfSpace Ω)) :=
  MemWkp.memLp h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace.memLp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace.memLp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace.memLp ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace.memLp

omit [NeZero d] in
theorem MemWkpHalfSpace.memLp_of_relOpen [NeZero d]
    {k : ℕ} {p : ℝ≥0∞} {Ω : Set E} (hΩ : IsHalfSpaceRelOpen (d := d) Ω)
    {u : E → ℝ}
    (h : MemWkpHalfSpace (d := d) k p u Ω) :
    MemLp u p ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E).restrict Ω) := by
  rw [volume_restrict_interiorHalfSpace_eq hΩ]
  exact h.memLp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace.memLp_of_relOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace.memLp_of_relOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace.memLp_of_relOpen ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace.memLp_of_relOpen

omit [NeZero d] in
theorem MemWkpHalfSpace_zero_fun [NeZero d]
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E}
    (hΩ : IsHalfSpaceRelOpen (d := d) Ω) :
    MemWkpHalfSpace (d := d) k p (fun _ : E => (0 : ℝ)) Ω :=
  MemWkp_zero_fun (d := d) hp (interiorHalfSpace_isOpen hΩ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace_zero_fun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace_zero_fun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace_zero_fun ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace_zero_fun

omit [NeZero d] in
theorem MemWkpHalfSpace.add [NeZero d]
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E}
    (hΩ : IsHalfSpaceRelOpen (d := d) Ω)
    {u v : E → ℝ}
    (hu : MemWkpHalfSpace (d := d) k p u Ω)
    (hv : MemWkpHalfSpace (d := d) k p v Ω) :
    MemWkpHalfSpace (d := d) k p (fun x => u x + v x) Ω :=
  MemWkp.add (d := d) hp (interiorHalfSpace_isOpen hΩ) hu hv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace.add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace.add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace.add ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace.add

omit [NeZero d] in
theorem MemWkpHalfSpace.const_smul [NeZero d]
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E}
    (hΩ : IsHalfSpaceRelOpen (d := d) Ω)
    {u : E → ℝ}
    (hu : MemWkpHalfSpace (d := d) k p u Ω) (c : ℝ) :
    MemWkpHalfSpace (d := d) k p (fun x => c * u x) Ω :=
  MemWkp.const_smul (d := d) hp (interiorHalfSpace_isOpen hΩ) hu c

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace.const_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace.const_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace.const_smul ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace.const_smul

omit [NeZero d] in
theorem MemWkpHalfSpace.neg [NeZero d]
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E}
    (hΩ : IsHalfSpaceRelOpen (d := d) Ω)
    {u : E → ℝ}
    (hu : MemWkpHalfSpace (d := d) k p u Ω) :
    MemWkpHalfSpace (d := d) k p (fun x => - u x) Ω :=
  MemWkp.neg (d := d) hp (interiorHalfSpace_isOpen hΩ) hu

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace.neg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace.neg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace.neg ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace.neg

omit [NeZero d] in
theorem MemWkpHalfSpace.sub [NeZero d]
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E}
    (hΩ : IsHalfSpaceRelOpen (d := d) Ω)
    {u v : E → ℝ}
    (hu : MemWkpHalfSpace (d := d) k p u Ω)
    (hv : MemWkpHalfSpace (d := d) k p v Ω) :
    MemWkpHalfSpace (d := d) k p (fun x => u x - v x) Ω :=
  MemWkp.sub (d := d) hp (interiorHalfSpace_isOpen hΩ) hu hv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace.sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace.sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace.sub ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace.sub

omit [NeZero d] in
theorem MemWkpHalfSpace_congr_ae [NeZero d]
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E}
    (hΩ : IsHalfSpaceRelOpen (d := d) Ω)
    {u v : E → ℝ}
    (huv : u =ᵐ[(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E).restrict (interiorHalfSpace Ω)] v) :
    MemWkpHalfSpace (d := d) k p u Ω ↔ MemWkpHalfSpace (d := d) k p v Ω :=
  MemWkp_congr_ae (d := d) hp (interiorHalfSpace_isOpen hΩ) huv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace_congr_ae then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace_congr_ae"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace_congr_ae ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace_congr_ae

omit [NeZero d] in
theorem MemWkpHalfSpace_congr_ae_of_carrier [NeZero d]
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E}
    (hΩ : IsHalfSpaceRelOpen (d := d) Ω)
    {u v : E → ℝ}
    (huv : u =ᵐ[(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E).restrict Ω] v) :
    MemWkpHalfSpace (d := d) k p u Ω ↔ MemWkpHalfSpace (d := d) k p v Ω := by
  rw [volume_restrict_interiorHalfSpace_eq hΩ] at huv
  exact MemWkpHalfSpace_congr_ae (d := d) hp hΩ huv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace_congr_ae_of_carrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace_congr_ae_of_carrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace_congr_ae_of_carrier ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace_congr_ae_of_carrier

def wkpNormHalfSpace (k : ℕ) (p : ℝ≥0∞) (u : E → ℝ) (Ω : Set E) : ℝ≥0∞ :=
  iteratedWeakSobolevNorm (d := d) k p u (interiorHalfSpace Ω)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace

@[simp] lemma wkpNormHalfSpace_def
    (k : ℕ) (p : ℝ≥0∞) (u : E → ℝ) (Ω : Set E) :
    wkpNormHalfSpace (d := d) k p u Ω =
      iteratedWeakSobolevNorm (d := d) k p u (interiorHalfSpace Ω) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace_def ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace_def

theorem wkpNormHalfSpace_zero
    (p : ℝ≥0∞) (u : E → ℝ) (Ω : Set E) :
    wkpNormHalfSpace (d := d) 0 p u Ω =
      eLpNorm u p ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E).restrict (interiorHalfSpace Ω)) :=
  wkpNorm_zero (d := d) p u (interiorHalfSpace Ω)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace_zero ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace_zero

omit [NeZero d] in
theorem wkpNormHalfSpace_zero_of_relOpen [NeZero d]
    {p : ℝ≥0∞} {Ω : Set E} (hΩ : IsHalfSpaceRelOpen (d := d) Ω)
    (u : E → ℝ) :
    wkpNormHalfSpace (d := d) 0 p u Ω =
      eLpNorm u p ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E).restrict Ω) := by
  rw [wkpNormHalfSpace_zero, ← volume_restrict_interiorHalfSpace_eq hΩ]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace_zero_of_relOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace_zero_of_relOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace_zero_of_relOpen ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace_zero_of_relOpen

omit [NeZero d] in
theorem wkpNormHalfSpace_zero_fun_zero [NeZero d]
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E}
    (hΩ : IsHalfSpaceRelOpen (d := d) Ω) :
    wkpNormHalfSpace (d := d) k p (fun _ : E => (0 : ℝ)) Ω = 0 :=
  wkpNorm_zero_fun_zero (d := d) hp (interiorHalfSpace_isOpen hΩ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace_zero_fun_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace_zero_fun_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace_zero_fun_zero ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace_zero_fun_zero

theorem wkpNormHalfSpace_lt_top_of_memWkpHalfSpace
    {k : ℕ} {p : ℝ≥0∞} {Ω : Set E} {u : E → ℝ}
    (h : MemWkpHalfSpace (d := d) k p u Ω) :
    wkpNormHalfSpace (d := d) k p u Ω < (⊤ : ℝ≥0∞) :=
  wkpNorm_lt_top_of_memWkp h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace_lt_top_of_memWkpHalfSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace_lt_top_of_memWkpHalfSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace_lt_top_of_memWkpHalfSpace ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace_lt_top_of_memWkpHalfSpace

omit [NeZero d] in
theorem wkpNormHalfSpace_add_le [NeZero d]
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E}
    (hΩ : IsHalfSpaceRelOpen (d := d) Ω)
    {u v : E → ℝ}
    (hu : MemWkpHalfSpace (d := d) k p u Ω)
    (hv : MemWkpHalfSpace (d := d) k p v Ω) :
    wkpNormHalfSpace (d := d) k p (fun x => u x + v x) Ω ≤
      wkpNormHalfSpace (d := d) k p u Ω +
        wkpNormHalfSpace (d := d) k p v Ω :=
  wkpNorm_add_le (d := d) hp (interiorHalfSpace_isOpen hΩ) hu hv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace_add_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace_add_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace_add_le ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace_add_le

omit [NeZero d] in
theorem wkpNormHalfSpace_const_smul [NeZero d]
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E}
    (hΩ : IsHalfSpaceRelOpen (d := d) Ω)
    {u : E → ℝ}
    (hu : MemWkpHalfSpace (d := d) k p u Ω) (c : ℝ) :
    wkpNormHalfSpace (d := d) k p (fun x => c * u x) Ω =
      ‖c‖ₑ * wkpNormHalfSpace (d := d) k p u Ω :=
  wkpNorm_const_smul (d := d) hp (interiorHalfSpace_isOpen hΩ) hu c

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace_const_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace_const_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace_const_smul ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace_const_smul

omit [NeZero d] in
theorem fderiv_isWeakPartialDeriv_of_smooth_interiorHalfSpace [NeZero d]
    {Ω : Set E} (hΩ : IsHalfSpaceRelOpen (d := d) Ω)
    {u : E → ℝ} (hu_smooth : ContDiff ℝ 1 u) (i : Fin d) :
    DeGiorgi.HasWeakPartialDeriv i
      (fun x => (fderiv ℝ u x) (EuclideanSpace.single i 1))
      u (interiorHalfSpace Ω) :=
  DeGiorgi.HasWeakPartialDeriv.of_contDiff (interiorHalfSpace_isOpen hΩ)
    hu_smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.fderiv_isWeakPartialDeriv_of_smooth_interiorHalfSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.fderiv_isWeakPartialDeriv_of_smooth_interiorHalfSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.fderiv_isWeakPartialDeriv_of_smooth_interiorHalfSpace ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.fderiv_isWeakPartialDeriv_of_smooth_interiorHalfSpace

theorem fderiv_memLp_of_smooth_compactSupport
    {p : ℝ≥0∞} {Ω : Set E}
    {u : E → ℝ} (hu_smooth : ContDiff ℝ ∞ u)
    (hu_support : HasCompactSupport u) (i : Fin d) :
    _root_.MeasureTheory.MemLp (fun x => (fderiv ℝ u x) (EuclideanSpace.single i 1)) p
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E).restrict (interiorHalfSpace Ω)) := by
  have h_smooth : ContDiff ℝ ∞
      (fun x => (fderiv ℝ u x) (EuclideanSpace.single i 1)) := by
    have h_fderiv : ContDiff ℝ ∞ (fun x => fderiv ℝ u x) :=
      hu_smooth.fderiv_right (m := (∞ : WithTop ℕ∞)) (by
        rw [ENat.coe_top_add_one])
    exact h_fderiv.clm_apply contDiff_const
  have h_support : HasCompactSupport
      (fun x => (fderiv ℝ u x) (EuclideanSpace.single i 1)) :=
    hu_support.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)
  have h_global : _root_.MeasureTheory.MemLp
      (fun x => (fderiv ℝ u x) (EuclideanSpace.single i 1)) p volume :=
    h_smooth.continuous.memLp_of_hasCompactSupport h_support
  exact h_global.restrict (interiorHalfSpace Ω)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.fderiv_memLp_of_smooth_compactSupport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.fderiv_memLp_of_smooth_compactSupport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.fderiv_memLp_of_smooth_compactSupport ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.fderiv_memLp_of_smooth_compactSupport

theorem memLp_of_smooth_compactSupport
    {p : ℝ≥0∞} {Ω : Set E}
    {u : E → ℝ} (hu_smooth : ContDiff ℝ ∞ u)
    (hu_support : HasCompactSupport u) :
    MemLp u p ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E).restrict (interiorHalfSpace Ω)) := by
  have h_global : _root_.MeasureTheory.MemLp u p (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) :=
    hu_smooth.continuous.memLp_of_hasCompactSupport hu_support
  exact h_global.restrict (interiorHalfSpace Ω)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.memLp_of_smooth_compactSupport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.memLp_of_smooth_compactSupport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.memLp_of_smooth_compactSupport ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.memLp_of_smooth_compactSupport

theorem memW1p_of_smooth_compactSupport_interiorHalfSpace
    {p : ℝ≥0∞} {Ω : Set E} (hΩ : IsHalfSpaceRelOpen (d := d) Ω)
    {u : E → ℝ} (hu_smooth : ContDiff ℝ ∞ u)
    (hu_support : HasCompactSupport u) :
    DeGiorgi.MemW1p p u (interiorHalfSpace Ω) := by
  refine ⟨memLp_of_smooth_compactSupport hu_smooth hu_support, ?_⟩
  intro i
  refine ⟨fun x => (fderiv ℝ u x) (EuclideanSpace.single i 1),
    fderiv_memLp_of_smooth_compactSupport hu_smooth hu_support i, ?_⟩
  exact fderiv_isWeakPartialDeriv_of_smooth_interiorHalfSpace hΩ
    (hu_smooth.of_le (by norm_cast)) i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.memW1p_of_smooth_compactSupport_interiorHalfSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.memW1p_of_smooth_compactSupport_interiorHalfSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.memW1p_of_smooth_compactSupport_interiorHalfSpace ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.memW1p_of_smooth_compactSupport_interiorHalfSpace

theorem partialDerivWithin_interiorHalfSpace_eq_partialDeriv
    {Ω : Set E} (hΩ : IsHalfSpaceRelOpen (d := d) Ω)
    (i : Fin (Module.finrank ℝ E)) (u : E → ℝ) {y : E}
    (hy : y ∈ interiorHalfSpace Ω) :
    DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.partialDerivWithin
        (interiorHalfSpace Ω) i u y =
      DifferentialGeometry.Tensor.Coordinates.partialDeriv
        i u y :=
  Integral.DivergenceTheorem.WithBoundary.partialDerivWithin_eq_partialDeriv_of_isOpen
    (interiorHalfSpace_isOpen hΩ) hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.partialDerivWithin_interiorHalfSpace_eq_partialDeriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.partialDerivWithin_interiorHalfSpace_eq_partialDeriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.partialDerivWithin_interiorHalfSpace_eq_partialDeriv ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.partialDerivWithin_interiorHalfSpace_eq_partialDeriv

section EuclideanHalfSpaceChartTargets

variable {n : ℕ} [NeZero n]

theorem range_modelWithCornersEuclideanHalfSpace_eq_closedHalfSpace :
    Set.range (modelWithCornersEuclideanHalfSpace n :
        EuclideanHalfSpace n → EuclideanSpace ℝ (Fin n)) =
      closedHalfSpace (d := n) := by
  rw [range_modelWithCornersEuclideanHalfSpace]
  ext y
  simp [closedHalfSpace]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.range_modelWithCornersEuclideanHalfSpace_eq_closedHalfSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.range_modelWithCornersEuclideanHalfSpace_eq_closedHalfSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.range_modelWithCornersEuclideanHalfSpace_eq_closedHalfSpace ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.range_modelWithCornersEuclideanHalfSpace_eq_closedHalfSpace

theorem extChartAt_target_isHalfSpaceRelOpen
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace n) M]
    (α : M) :
    IsHalfSpaceRelOpen (d := n)
      (extChartAt (modelWithCornersEuclideanHalfSpace n) α).target := by
  refine ⟨(modelWithCornersEuclideanHalfSpace n).symm ⁻¹'
      (chartAt (EuclideanHalfSpace n) α).target, ?_, ?_⟩
  · exact (chartAt (EuclideanHalfSpace n) α).open_target.preimage
      (modelWithCornersEuclideanHalfSpace n).continuous_symm
  · rw [extChartAt_target,
      range_modelWithCornersEuclideanHalfSpace_eq_closedHalfSpace]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.extChartAt_target_isHalfSpaceRelOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.extChartAt_target_isHalfSpaceRelOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.extChartAt_target_isHalfSpaceRelOpen ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.extChartAt_target_isHalfSpaceRelOpen

end EuclideanHalfSpaceChartTargets

end Euclidean
end Sobolev
end Analysis
end DifferentialGeometry
