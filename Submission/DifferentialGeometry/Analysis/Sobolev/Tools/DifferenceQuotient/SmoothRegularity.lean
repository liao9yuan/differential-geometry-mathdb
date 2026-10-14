import Submission.DifferentialGeometry.Analysis.Sobolev.Tools.DifferenceQuotient

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.MeasureTheory _root_.Metric _root_.Filter _root_.Topology _root_.Set _root_.Function
open scoped _root_.ENNReal _root_.NNReal _root_.Convolution _root_.Pointwise _root_.BigOperators

namespace DifferentialGeometry.Analysis.Sobolev

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
theorem contDiff_diffQuot_of_contDiff
    {v : E → ℝ} (hv : ContDiff ℝ (⊤ : ℕ∞) v) (k : Fin d) {h : ℝ} (hh : h ≠ 0) :
    ContDiff ℝ (⊤ : ℕ∞)
      (DifferentialGeometry.Analysis.Sobolev.diffQuot k h v) := by
  have h_translate :
      ContDiff ℝ (⊤ : ℕ∞) (fun y : E => y + h • EuclideanSpace.single k 1) :=
    contDiff_id.add contDiff_const
  have h_comp :
      ContDiff ℝ (⊤ : ℕ∞) (fun y : E => v (y + h • EuclideanSpace.single k 1)) :=
    hv.comp h_translate
  have h_sub :
      ContDiff ℝ (⊤ : ℕ∞)
        (fun y : E => v (y + h • EuclideanSpace.single k 1) - v y) :=
    h_comp.sub hv
  have h_div :
      ContDiff ℝ (⊤ : ℕ∞)
        (fun y : E => (v (y + h • EuclideanSpace.single k 1) - v y) / h) := by
    have heq :
        (fun y : E => (v (y + h • EuclideanSpace.single k 1) - v y) / h) =
          fun y : E =>
            h⁻¹ • (v (y + h • EuclideanSpace.single k 1) - v y) := by
      funext y
      rw [div_eq_inv_mul, smul_eq_mul]
    rw [heq]
    exact h_sub.const_smul h⁻¹
  have heq_fun :
      (DifferentialGeometry.Analysis.Sobolev.diffQuot k h v) =
        fun y : E => (v (y + h • EuclideanSpace.single k 1) - v y) / h := by
    funext y
    exact DifferentialGeometry.Analysis.Sobolev.diffQuot_apply_of_ne
      (d := d) k hh v y
  rw [heq_fun]
  exact h_div

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.contDiff_diffQuot_of_contDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.contDiff_diffQuot_of_contDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.contDiff_diffQuot_of_contDiff ``Submission.DifferentialGeometry.Analysis.Sobolev.contDiff_diffQuot_of_contDiff

omit [NeZero d] in
private lemma hasFDerivAt_translate (k : Fin d) (h : ℝ) (x : E) :
    HasFDerivAt
      (fun y : E => y + h • EuclideanSpace.single k 1)
      (ContinuousLinearMap.id ℝ E) x := by
  exact (hasFDerivAt_id x).add_const _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.hasFDerivAt_translate
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.hasFDerivAt_translate target :: scope.openDecls } }

omit [NeZero d] in
theorem fderiv_diffQuot_apply_eq_diffQuot_partial
    {g : E → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (k j : Fin d) {h : ℝ} (hh : h ≠ 0) (x : E) :
    (fderiv ℝ
        (DifferentialGeometry.Analysis.Sobolev.diffQuot k h g) x)
      (EuclideanSpace.single j 1) =
      DifferentialGeometry.Analysis.Sobolev.diffQuot k h
        (fun y : E => (fderiv ℝ g y) (EuclideanSpace.single j 1)) x := by
  have hg_diff : Differentiable ℝ g := hg.differentiable (by simp)
  have hg_at : ∀ y : E, HasFDerivAt g (fderiv ℝ g y) y :=
    fun y => (hg_diff y).hasFDerivAt
  have h_translate_at : ∀ y : E,
      HasFDerivAt
        (fun z : E => z + h • EuclideanSpace.single k 1)
        (ContinuousLinearMap.id ℝ E) y :=
    fun y => hasFDerivAt_translate (d := d) k h y
  have h_comp_at : ∀ y : E,
      HasFDerivAt (fun z : E => g (z + h • EuclideanSpace.single k 1))
        (fderiv ℝ g (y + h • EuclideanSpace.single k 1)) y := by
    intro y
    have hcomp :=
      (hg_at (y + h • EuclideanSpace.single k 1)).comp y (h_translate_at y)
    have heq :
        ((fderiv ℝ g (y + h • EuclideanSpace.single k 1)).comp
          (ContinuousLinearMap.id ℝ E)) =
          fderiv ℝ g (y + h • EuclideanSpace.single k 1) := by
      ext z
      rfl
    rw [heq] at hcomp
    exact hcomp
  have h_diff_at : ∀ y : E,
      HasFDerivAt
        (fun z : E => g (z + h • EuclideanSpace.single k 1) - g z)
        (fderiv ℝ g (y + h • EuclideanSpace.single k 1) - fderiv ℝ g y) y := by
    intro y
    exact (h_comp_at y).sub (hg_at y)
  have h_div_at : ∀ y : E,
      HasFDerivAt
        (fun z : E =>
          (g (z + h • EuclideanSpace.single k 1) - g z) / h)
        (h⁻¹ • (fderiv ℝ g (y + h • EuclideanSpace.single k 1) -
          fderiv ℝ g y)) y := by
    intro y
    have hcs := (h_diff_at y).const_smul h⁻¹
    have heq_fun :
        (h⁻¹ • fun z : E => g (z + h • EuclideanSpace.single k 1) - g z) =
          fun z : E =>
            (g (z + h • EuclideanSpace.single k 1) - g z) / h := by
      funext z
      change h⁻¹ • (g (z + h • EuclideanSpace.single k 1) - g z) =
        (g (z + h • EuclideanSpace.single k 1) - g z) / h
      rw [div_eq_inv_mul, smul_eq_mul]
    rw [heq_fun] at hcs
    exact hcs
  have heq_diffQuot :
      (DifferentialGeometry.Analysis.Sobolev.diffQuot k h g) =
        fun y : E => (g (y + h • EuclideanSpace.single k 1) - g y) / h := by
    funext y
    exact DifferentialGeometry.Analysis.Sobolev.diffQuot_apply_of_ne
      (d := d) k hh g y
  rw [heq_diffQuot]
  have h_at : HasFDerivAt
      (fun y : E => (g (y + h • EuclideanSpace.single k 1) - g y) / h)
      (h⁻¹ • (fderiv ℝ g (x + h • EuclideanSpace.single k 1) -
        fderiv ℝ g x)) x := h_div_at x
  rw [h_at.fderiv]
  set ej : E := EuclideanSpace.single j 1 with hej
  have h_apply :
      (h⁻¹ • (fderiv ℝ g (x + h • EuclideanSpace.single k 1) -
          fderiv ℝ g x)) ej =
        h⁻¹ • ((fderiv ℝ g (x + h • EuclideanSpace.single k 1)) ej -
          (fderiv ℝ g x) ej) := by
    rw [smul_apply]
    rw [sub_apply]
  rw [h_apply]
  rw [DifferentialGeometry.Analysis.Sobolev.diffQuot_apply_of_ne
    (d := d) k hh _ x]
  rw [div_eq_inv_mul, smul_eq_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.fderiv_diffQuot_apply_eq_diffQuot_partial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.fderiv_diffQuot_apply_eq_diffQuot_partial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.fderiv_diffQuot_apply_eq_diffQuot_partial ``Submission.DifferentialGeometry.Analysis.Sobolev.fderiv_diffQuot_apply_eq_diffQuot_partial

omit [NeZero d] in
theorem contDiff_translate (k : Fin d) (h : ℝ) {φ : E → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) : ContDiff ℝ (⊤ : ℕ∞) (translate k h φ) := by
  unfold translate
  have htrans_smooth : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : E => y + h • EuclideanSpace.single k 1) :=
    contDiff_id.add contDiff_const
  exact hφ.comp htrans_smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.contDiff_translate then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.contDiff_translate"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.contDiff_translate ``Submission.DifferentialGeometry.Analysis.Sobolev.contDiff_translate

omit [NeZero d] in
theorem fderiv_translate_apply (k j : Fin d) (h : ℝ) {φ : E → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (x : E) :
    (fderiv ℝ (translate k h φ) x) (EuclideanSpace.single j 1) =
      (fderiv ℝ φ (x + h • EuclideanSpace.single k 1))
        (EuclideanSpace.single j 1) := by
  have hφ_diff : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hφ_at : HasFDerivAt φ
      (fderiv ℝ φ (x + h • EuclideanSpace.single k 1))
      (x + h • EuclideanSpace.single k 1) :=
    (hφ_diff (x + h • EuclideanSpace.single k 1)).hasFDerivAt
  have h_translate_at : HasFDerivAt
      (fun z : E => z + h • EuclideanSpace.single k 1)
      (ContinuousLinearMap.id ℝ E) x :=
    (hasFDerivAt_id x).add_const _
  have h_comp_at : HasFDerivAt
      (fun z : E => φ (z + h • EuclideanSpace.single k 1))
      (fderiv ℝ φ (x + h • EuclideanSpace.single k 1)) x := by
    have hcomp := hφ_at.comp x h_translate_at
    have heq :
        ((fderiv ℝ φ (x + h • EuclideanSpace.single k 1)).comp
            (ContinuousLinearMap.id ℝ E)) =
          fderiv ℝ φ (x + h • EuclideanSpace.single k 1) := by
      ext z
      rfl
    rw [heq] at hcomp
    exact hcomp
  have h_at : HasFDerivAt (translate k h φ)
      (fderiv ℝ φ (x + h • EuclideanSpace.single k 1)) x := h_comp_at
  rw [h_at.fderiv]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.fderiv_translate_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.fderiv_translate_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.fderiv_translate_apply ``Submission.DifferentialGeometry.Analysis.Sobolev.fderiv_translate_apply

end DifferentialGeometry.Analysis.Sobolev
