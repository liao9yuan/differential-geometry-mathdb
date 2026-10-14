import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Topology.Order.Lattice

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open scoped _root_.BigOperators

namespace DifferentialGeometry.Simplex

variable {I : Type*} [Fintype I] [Nonempty I]


def minimumCoordinate (x : stdSimplex ℝ I) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty x.val

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.minimumCoordinate then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.minimumCoordinate"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.minimumCoordinate ``Submission.DifferentialGeometry.Simplex.minimumCoordinate


theorem continuous_minimumCoordinate : Continuous (minimumCoordinate (I := I)) :=
  Continuous.finset_inf'_apply Finset.univ_nonempty (fun i _ ↦
    (continuous_apply i).comp continuous_subtype_val)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.continuous_minimumCoordinate then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.continuous_minimumCoordinate"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.continuous_minimumCoordinate ``Submission.DifferentialGeometry.Simplex.continuous_minimumCoordinate


theorem minimumCoordinate_le (x : stdSimplex ℝ I) (i : I) : minimumCoordinate x ≤ x.val i :=
  Finset.inf'_le _ (Finset.mem_univ i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.minimumCoordinate_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.minimumCoordinate_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.minimumCoordinate_le ``Submission.DifferentialGeometry.Simplex.minimumCoordinate_le


theorem minimumCoordinate_nonneg (x : stdSimplex ℝ I) : 0 ≤ minimumCoordinate x :=
  Finset.le_inf' Finset.univ_nonempty _ (fun i _ ↦ x.property.1 i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.minimumCoordinate_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.minimumCoordinate_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.minimumCoordinate_nonneg ``Submission.DifferentialGeometry.Simplex.minimumCoordinate_nonneg


theorem exists_minimumCoordinate (x : stdSimplex ℝ I) :
    ∃ i : I, minimumCoordinate x = x.val i := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty x.val
  exact ⟨i, hi⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.exists_minimumCoordinate then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.exists_minimumCoordinate"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.exists_minimumCoordinate ``Submission.DifferentialGeometry.Simplex.exists_minimumCoordinate

private theorem card_mul_minimumCoordinate_le (x : stdSimplex ℝ I) :
    (Fintype.card I : ℝ) * minimumCoordinate x ≤ 1 := by
  have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset I)) ↦
    minimumCoordinate_le x i)
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    x.property.2] using h

run_cmd do
  let target := ``Submission.DifferentialGeometry.Simplex.card_mul_minimumCoordinate_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Simplex.card_mul_minimumCoordinate_le target :: scope.openDecls } }


theorem normalizationDenominator_pos (x : stdSimplex ℝ I) (hx : x ≠ stdSimplex.barycenter) :
    0 < 1 - (Fintype.card I : ℝ) * minimumCoordinate x := by
  have hle := card_mul_minimumCoordinate_le x
  have hcard : (0 : ℝ) < Fintype.card I := Nat.cast_pos.mpr Fintype.card_pos
  by_contra h
  have he : (Fintype.card I : ℝ) * minimumCoordinate x = 1 := by linarith
  have hm : minimumCoordinate x = (Fintype.card I : ℝ)⁻¹ := by
    apply (mul_left_cancel₀ (ne_of_gt hcard))
    rw [he, mul_inv_cancel₀ (ne_of_gt hcard)]
  have hsum : ∑ _ : I, minimumCoordinate x = ∑ i : I, x.val i := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      x.property.2] using he
  have heq := (Finset.sum_eq_sum_iff_of_le
    (fun i (_ : i ∈ (Finset.univ : Finset I)) ↦ minimumCoordinate_le x i)).mp hsum
  apply hx
  apply Subtype.ext
  funext i
  exact (heq i (Finset.mem_univ i)).symm.trans hm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.normalizationDenominator_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.normalizationDenominator_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.normalizationDenominator_pos ``Submission.DifferentialGeometry.Simplex.normalizationDenominator_pos


theorem minimumCoordinate_lt_barycenter (x : stdSimplex ℝ I) (hx : x ≠ stdSimplex.barycenter) :
    minimumCoordinate x < (Fintype.card I : ℝ)⁻¹ := by
  have hd := normalizationDenominator_pos x hx
  have hcard : (0 : ℝ) < Fintype.card I := Nat.cast_pos.mpr Fintype.card_pos
  by_contra h
  have hm := mul_le_mul_of_nonneg_left (le_of_not_gt h) hcard.le
  rw [mul_inv_cancel₀ (ne_of_gt hcard)] at hm
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.minimumCoordinate_lt_barycenter then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.minimumCoordinate_lt_barycenter"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.minimumCoordinate_lt_barycenter ``Submission.DifferentialGeometry.Simplex.minimumCoordinate_lt_barycenter


def boundary (I : Type*) [Fintype I] : Set (stdSimplex ℝ I) :=
  {x | ∃ i : I, x.val i = 0}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.boundary ``Submission.DifferentialGeometry.Simplex.boundary


def punctured (I : Type*) [Fintype I] [Nonempty I] : Set (stdSimplex ℝ I) :=
  {x | x ≠ stdSimplex.barycenter}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.punctured then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.punctured"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.punctured ``Submission.DifferentialGeometry.Simplex.punctured


theorem isOpen_punctured : IsOpen (punctured I) :=
  isOpen_compl_singleton

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.isOpen_punctured then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.isOpen_punctured"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.isOpen_punctured ``Submission.DifferentialGeometry.Simplex.isOpen_punctured

omit [Nonempty I] in
theorem isClosed_boundary : IsClosed (boundary I) := by
  change IsClosed (Set.ofPred (fun x : stdSimplex ℝ I ↦ ∃ i : I, x.val i = 0))
  rw [Set.ofPred_exists]
  exact isClosed_iUnion_of_finite (fun i ↦
    isClosed_eq ((continuous_apply i).comp continuous_subtype_val) continuous_const)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.isClosed_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.isClosed_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.isClosed_boundary ``Submission.DifferentialGeometry.Simplex.isClosed_boundary


theorem minimumCoordinate_eq_zero {x : stdSimplex ℝ I} (hx : x ∈ boundary I) :
    minimumCoordinate x = 0 := by
  obtain ⟨i, hi⟩ := hx
  exact le_antisymm (hi ▸ minimumCoordinate_le x i) (minimumCoordinate_nonneg x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.minimumCoordinate_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.minimumCoordinate_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.minimumCoordinate_eq_zero ``Submission.DifferentialGeometry.Simplex.minimumCoordinate_eq_zero


theorem boundary_ne_barycenter {x : stdSimplex ℝ I} (hx : x ∈ boundary I) :
    x ≠ stdSimplex.barycenter := by
  obtain ⟨i, hi⟩ := hx
  intro he
  rw [he, stdSimplex.barycenter_apply] at hi
  have hp : (0 : ℝ) < (Fintype.card I : ℝ)⁻¹ :=
    inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)
  exact (ne_of_gt hp) hi

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.boundary_ne_barycenter then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.boundary_ne_barycenter"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.boundary_ne_barycenter ``Submission.DifferentialGeometry.Simplex.boundary_ne_barycenter


theorem boundary_subset_punctured : boundary I ⊆ punctured I :=
  fun _ hx ↦ boundary_ne_barycenter hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.boundary_subset_punctured then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.boundary_subset_punctured"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.boundary_subset_punctured ``Submission.DifferentialGeometry.Simplex.boundary_subset_punctured


def boundaryInclusion : C(boundary I, punctured I) :=
  ⟨fun x ↦ ⟨x.val, boundary_ne_barycenter x.property⟩,
    continuous_subtype_val.subtype_mk _⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.boundaryInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.boundaryInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.boundaryInclusion ``Submission.DifferentialGeometry.Simplex.boundaryInclusion

private def radialRetractionPoint (x : punctured I) : boundary I :=
  ⟨⟨fun i ↦ (x.val.val i - minimumCoordinate x.val) /
      (1 - (Fintype.card I : ℝ) * minimumCoordinate x.val),
    ⟨fun i ↦ div_nonneg (sub_nonneg.mpr (minimumCoordinate_le x.val i))
      (normalizationDenominator_pos x.val x.property).le, by
      simp only [div_eq_mul_inv, ← Finset.sum_mul]
      rw [Finset.sum_sub_distrib, x.val.property.2,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      exact mul_inv_cancel₀ (ne_of_gt (normalizationDenominator_pos x.val x.property))⟩⟩, by
    obtain ⟨i, hi⟩ := exists_minimumCoordinate x.val
    exact ⟨i, by change (x.val.val i - minimumCoordinate x.val) / _ = 0
                 rw [← hi, sub_self, zero_div]⟩⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Simplex.radialRetractionPoint
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Simplex.radialRetractionPoint target :: scope.openDecls } }

def radialRetraction : C(punctured I, boundary I) :=
  ⟨radialRetractionPoint, by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    exact (((continuous_apply i).comp
      (continuous_subtype_val.comp continuous_subtype_val)).sub
        (continuous_minimumCoordinate.comp continuous_subtype_val)).div
      (continuous_const.sub (continuous_const.mul
        (continuous_minimumCoordinate.comp continuous_subtype_val)))
      (fun x ↦ ne_of_gt (normalizationDenominator_pos x.val x.property))⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.radialRetraction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.radialRetraction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.radialRetraction ``Submission.DifferentialGeometry.Simplex.radialRetraction


theorem radialRetraction_apply (x : punctured I) (i : I) :
    (radialRetraction x).val.val i = (x.val.val i - minimumCoordinate x.val) /
      (1 - (Fintype.card I : ℝ) * minimumCoordinate x.val) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.radialRetraction_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.radialRetraction_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.radialRetraction_apply ``Submission.DifferentialGeometry.Simplex.radialRetraction_apply


@[simp]
theorem radialRetraction_boundary (x : boundary I) :
    radialRetraction (boundaryInclusion x) = x := by
  apply Subtype.ext
  apply Subtype.ext
  funext i
  change (x.val.val i - minimumCoordinate x.val) /
    (1 - (Fintype.card I : ℝ) * minimumCoordinate x.val) = x.val.val i
  rw [minimumCoordinate_eq_zero x.property, sub_zero, _root_.MulZeroClass.mul_zero, sub_zero, div_one]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.radialRetraction_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.radialRetraction_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.radialRetraction_boundary ``Submission.DifferentialGeometry.Simplex.radialRetraction_boundary

private def radialHomotopyPoint (t : unitInterval) (x : punctured I) : punctured I :=
  ⟨⟨(1 - (t : ℝ)) • x.val.val + (t : ℝ) • (radialRetraction x).val.val,
    convex_stdSimplex ℝ I x.val.property (radialRetraction x).val.property
      (sub_nonneg.mpr t.property.2) t.property.1 (sub_add_cancel _ _)⟩, by
    obtain ⟨i, hi⟩ := exists_minimumCoordinate x.val
    have hq : (radialRetraction x).val.val i = 0 := by
      change (x.val.val i - minimumCoordinate x.val) / _ = 0
      rw [← hi, sub_self, zero_div]
    have hm := minimumCoordinate_lt_barycenter x.val x.property
    have htm : (1 - (t : ℝ)) * minimumCoordinate x.val ≤ minimumCoordinate x.val := by
      nlinarith [t.property.1, minimumCoordinate_nonneg x.val]
    intro he
    have hei := congrArg (fun y : stdSimplex ℝ I ↦ y.val i) he
    change (1 - (t : ℝ)) * x.val.val i + (t : ℝ) * (radialRetraction x).val.val i =
      (Fintype.card I : ℝ)⁻¹ at hei
    rw [← hi, hq, _root_.MulZeroClass.mul_zero, add_zero] at hei
    linarith⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Simplex.radialHomotopyPoint
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Simplex.radialHomotopyPoint target :: scope.openDecls } }

def radialDeformation : ContinuousMap.HomotopyRel (ContinuousMap.id (punctured I))
    (boundaryInclusion.comp radialRetraction) {x | x.val ∈ boundary I} where
  toFun tx := radialHomotopyPoint tx.1 tx.2
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
      (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd))).add
      ((continuous_subtype_val.comp continuous_fst).smul
        (continuous_subtype_val.comp (continuous_subtype_val.comp
          (radialRetraction.continuous.comp continuous_snd))))
  map_zero_left x := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    change (1 - (0 : ℝ)) * x.val.val i + 0 * (radialRetraction x).val.val i = x.val.val i
    ring
  map_one_left x := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    change (1 - (1 : ℝ)) * x.val.val i + 1 * (radialRetraction x).val.val i =
      (radialRetraction x).val.val i
    ring
  prop' t := by
    intro x hx
    have hr : (radialRetraction x).val = x.val :=
      congrArg Subtype.val (radialRetraction_boundary (⟨x.val, hx⟩ : boundary I))
    apply Subtype.ext
    apply Subtype.ext
    funext i
    change (1 - (t : ℝ)) * x.val.val i + (t : ℝ) * (radialRetraction x).val.val i = x.val.val i
    rw [hr]
    ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.radialDeformation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.radialDeformation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.radialDeformation ``Submission.DifferentialGeometry.Simplex.radialDeformation

def radialHomotopyEquiv : ContinuousMap.HomotopyEquiv (punctured I) (boundary I) where
  toFun := radialRetraction
  invFun := boundaryInclusion
  left_inv := ⟨radialDeformation.toHomotopy.symm⟩
  right_inv := by
    have he : (radialRetraction (I := I)).comp boundaryInclusion = ContinuousMap.id _ := by
      apply ContinuousMap.ext
      intro x
      exact radialRetraction_boundary x
    rw [he]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.radialHomotopyEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.radialHomotopyEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.radialHomotopyEquiv ``Submission.DifferentialGeometry.Simplex.radialHomotopyEquiv

end DifferentialGeometry.Simplex
