import Submission.DifferentialGeometry.Analysis.ODE.IndexForm.Uniqueness

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.Set
open scoped _root_.ContDiff _root_.RealInnerProductSpace

noncomputable section


namespace DifferentialGeometry.Analysis.ODE

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

def indexTestFieldTo (L : ℝ) (q : F) (t : ℝ) : F :=
  (t * (L - t)) • q

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.indexTestFieldTo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.indexTestFieldTo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.indexTestFieldTo ``Submission.DifferentialGeometry.Analysis.ODE.indexTestFieldTo

def indexTestDerivTo (L : ℝ) (q : F) (t : ℝ) : F :=
  (L - 2 * t) • q

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.indexTestDerivTo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.indexTestDerivTo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.indexTestDerivTo ``Submission.DifferentialGeometry.Analysis.ODE.indexTestDerivTo

theorem indexTestFieldTo_hasDerivAt (L : ℝ) (q : F) (t : ℝ) :
    HasDerivAt (indexTestFieldTo L q) (indexTestDerivTo L q t) t := by
  have hscalar :
      HasDerivAt (fun s : ℝ => s * (L - s)) (L - 2 * t) t := by
    change HasDerivAt ((fun s : ℝ => s) * fun s => L - s) (L - 2 * t) t
    have hder : L - 2 * t = 1 * (L - t) + t * -1 := by ring
    rw [hder]
    exact (hasDerivAt_id' t).mul ((hasDerivAt_id' t).const_sub L)
  unfold indexTestFieldTo indexTestDerivTo
  exact hscalar.smul_const q

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.indexTestFieldTo_hasDerivAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.indexTestFieldTo_hasDerivAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.indexTestFieldTo_hasDerivAt ``Submission.DifferentialGeometry.Analysis.ODE.indexTestFieldTo_hasDerivAt

theorem indexTestFieldTo_continuous (L : ℝ) (q : F) :
    Continuous (indexTestFieldTo L q) := by
  unfold indexTestFieldTo
  fun_prop

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.indexTestFieldTo_continuous then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.indexTestFieldTo_continuous"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.indexTestFieldTo_continuous ``Submission.DifferentialGeometry.Analysis.ODE.indexTestFieldTo_continuous

theorem indexTestDerivTo_continuous (L : ℝ) (q : F) :
    Continuous (indexTestDerivTo L q) := by
  unfold indexTestDerivTo
  fun_prop

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.indexTestDerivTo_continuous then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.indexTestDerivTo_continuous"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.indexTestDerivTo_continuous ``Submission.DifferentialGeometry.Analysis.ODE.indexTestDerivTo_continuous

theorem indexTestFieldTo_contDiff (L : ℝ) (q : F) :
    ContDiff ℝ ∞ (indexTestFieldTo L q) := by
  unfold indexTestFieldTo
  fun_prop

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.indexTestFieldTo_contDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.indexTestFieldTo_contDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.indexTestFieldTo_contDiff ``Submission.DifferentialGeometry.Analysis.ODE.indexTestFieldTo_contDiff

abbrev indexTestField (q : F) (t : ℝ) : F :=
  indexTestFieldTo 1 q t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.indexTestField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.indexTestField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.indexTestField ``Submission.DifferentialGeometry.Analysis.ODE.indexTestField

abbrev indexTestDeriv (q : F) (t : ℝ) : F :=
  indexTestDerivTo 1 q t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.indexTestDeriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.indexTestDeriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.indexTestDeriv ``Submission.DifferentialGeometry.Analysis.ODE.indexTestDeriv

theorem indexTestField_hasDerivAt (q : F) (t : ℝ) :
    HasDerivAt (indexTestField q) (indexTestDeriv q t) t := by
  simpa only [indexTestField, indexTestDeriv] using indexTestFieldTo_hasDerivAt 1 q t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.indexTestField_hasDerivAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.indexTestField_hasDerivAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.indexTestField_hasDerivAt ``Submission.DifferentialGeometry.Analysis.ODE.indexTestField_hasDerivAt

theorem indexTestField_continuous (q : F) : Continuous (indexTestField q) := by
  simpa only [indexTestField] using indexTestFieldTo_continuous 1 q

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.indexTestField_continuous then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.indexTestField_continuous"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.indexTestField_continuous ``Submission.DifferentialGeometry.Analysis.ODE.indexTestField_continuous

theorem indexTestDeriv_continuous (q : F) : Continuous (indexTestDeriv q) := by
  simpa only [indexTestDeriv] using indexTestDerivTo_continuous 1 q

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.indexTestDeriv_continuous then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.indexTestDeriv_continuous"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.indexTestDeriv_continuous ``Submission.DifferentialGeometry.Analysis.ODE.indexTestDeriv_continuous

theorem indexTestField_contDiff (q : F) :
    ContDiff ℝ ∞ (indexTestField q) := by
  simpa only [indexTestField] using indexTestFieldTo_contDiff 1 q

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.indexTestField_contDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.indexTestField_contDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.indexTestField_contDiff ``Submission.DifferentialGeometry.Analysis.ODE.indexTestField_contDiff

theorem contDiffOn_jacobi_system
    {R : ℝ → F →L[ℝ] F} {y v : ℝ → F} {J : Set ℝ}
    (hJ : IsOpen J)
    (hR : ContDiffOn ℝ ∞ R J)
    (hy : ∀ t ∈ J, HasDerivAt y (v t) t)
    (hv : ∀ t ∈ J, HasDerivAt v (-(R t) (y t)) t)
    (n : ℕ) :
    ContDiffOn ℝ n y J ∧ ContDiffOn ℝ n v J := by
  have hdy : DifferentiableOn ℝ y J :=
    fun t ht => (hy t ht).differentiableAt.differentiableWithinAt
  have hdv : DifferentiableOn ℝ v J :=
    fun t ht => (hv t ht).differentiableAt.differentiableWithinAt
  have hddy : ∀ t ∈ J, deriv y t = v t :=
    fun t ht => (hy t ht).deriv
  have hddv : ∀ t ∈ J, deriv v t = -(R t) (y t) :=
    fun t ht => (hv t ht).deriv
  induction n with
  | zero =>
      exact
        ⟨contDiffOn_zero.mpr hdy.continuousOn,
          contDiffOn_zero.mpr hdv.continuousOn⟩
  | succ n ih =>
      obtain ⟨hyn, hvn⟩ := ih
      have hRn : ContDiffOn ℝ n R J := contDiffOn_infty.mp hR n
      have hderiv_y : ContDiffOn ℝ n (deriv y) J :=
        hvn.congr hddy
      have hderiv_v : ContDiffOn ℝ n (deriv v) J :=
        ((hRn.clm_apply hyn).neg).congr hddv
      exact
        ⟨(contDiffOn_succ_iff_deriv_of_isOpen hJ).mpr
            ⟨hdy, by simp, hderiv_y⟩,
          (contDiffOn_succ_iff_deriv_of_isOpen hJ).mpr
            ⟨hdv, by simp, hderiv_v⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.contDiffOn_jacobi_system then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.contDiffOn_jacobi_system"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.contDiffOn_jacobi_system ``Submission.DifferentialGeometry.Analysis.ODE.contDiffOn_jacobi_system

theorem contDiffOn_infty_jacobi_system
    {R : ℝ → F →L[ℝ] F} {y v : ℝ → F} {J : Set ℝ}
    (hJ : IsOpen J)
    (hR : ContDiffOn ℝ ∞ R J)
    (hy : ∀ t ∈ J, HasDerivAt y (v t) t)
    (hv : ∀ t ∈ J, HasDerivAt v (-(R t) (y t)) t) :
    ContDiffOn ℝ ∞ y J ∧ ContDiffOn ℝ ∞ v J :=
  ⟨contDiffOn_infty.mpr fun n => (contDiffOn_jacobi_system hJ hR hy hv n).1,
    contDiffOn_infty.mpr fun n => (contDiffOn_jacobi_system hJ hR hy hv n).2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.contDiffOn_infty_jacobi_system then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.contDiffOn_infty_jacobi_system"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.contDiffOn_infty_jacobi_system ``Submission.DifferentialGeometry.Analysis.ODE.contDiffOn_infty_jacobi_system

private theorem exists_quad_neg {κ Q : ℝ} (hκ : 0 < κ) :
    ∃ s : ℝ, 2 * s * κ + s ^ 2 * Q < 0 := by
  have hden : 0 < |Q| + 1 := by positivity
  let s : ℝ := -κ / (|Q| + 1)
  have hsneg : s < 0 := by
    exact div_neg_of_neg_of_pos (neg_neg_of_pos hκ) hden
  have hsQ : |s * Q| < κ := by
    simp only [s]
    rw [abs_mul, abs_div, abs_neg, abs_of_pos hκ, abs_of_pos hden,
      div_mul_eq_mul_div, div_lt_iff₀ hden]
    nlinarith [abs_nonneg Q]
  have hsum : 0 < 2 * κ + s * Q := by
    linarith [(abs_lt.mp hsQ).1]
  refine ⟨s, ?_⟩
  calc
    2 * s * κ + s ^ 2 * Q = s * (2 * κ + s * Q) := by ring
    _ < 0 := mul_neg_of_neg_of_pos hsneg hsum

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.ODE.exists_quad_neg
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.ODE.exists_quad_neg target :: scope.openDecls } }

namespace IsJacobiFieldOn

theorem mono
    {R : ℝ → F →L[ℝ] F} {a b a' b' : ℝ} {y v : ℝ → F}
    (hsol : IsJacobiFieldOn R a b y v)
    (ha : a ≤ a') (hb : b' ≤ b) :
    IsJacobiFieldOn R a' b' y v := by
  have hsub : _root_.Set.Icc a' b' ⊆ _root_.Set.Icc a b := _root_.Set.Icc_subset_Icc ha hb
  exact
    { deriv_fst := fun t ht => (hsol.deriv_fst t (hsub ht)).mono hsub
      deriv_snd := fun t ht => (hsol.deriv_snd t (hsub ht)).mono hsub }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.IsJacobiFieldOn.mono then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.IsJacobiFieldOn.mono"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.IsJacobiFieldOn.mono ``Submission.DifferentialGeometry.Analysis.ODE.IsJacobiFieldOn.mono

theorem velocity_ne_zero_of_position_eq_zero
    {R : ℝ → F →L[ℝ] F} {a b c : ℝ} {y v : ℝ → F}
    (hsol : IsJacobiFieldOn R a b y v)
    (hc : c ∈ _root_.Set.Ioo a b)
    (hR : ContinuousOn R (_root_.Set.Icc a b))
    (hyc : y c = 0)
    (hne : ∃ t ∈ _root_.Set.Icc a b, y t ≠ 0) :
    v c ≠ 0 := by
  have hnorm : ContinuousOn (fun t : ℝ => ‖R t‖) (_root_.Set.Icc a b) :=
    continuous_norm.comp_continuousOn hR
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hnorm
  have hC0 : 0 ≤ _root_.Max.max C 0 := le_max_right _ _
  have hRbound : ∀ t ∈ _root_.Set.Icc a b, ‖R t‖ ≤ _root_.Max.max C 0 := by
    intro t ht
    exact (hC ⟨t, ht, rfl⟩).trans (le_max_left _ _)
  intro hvc
  have hzero := hsol.eq_zero_of_interior hc hC0 hRbound hyc hvc
  obtain ⟨t, ht, hyt⟩ := hne
  exact hyt (hzero t ht).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.IsJacobiFieldOn.velocity_ne_zero_of_position_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.IsJacobiFieldOn.velocity_ne_zero_of_position_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.IsJacobiFieldOn.velocity_ne_zero_of_position_eq_zero ``Submission.DifferentialGeometry.Analysis.ODE.IsJacobiFieldOn.velocity_ne_zero_of_position_eq_zero

theorem indexForm_indexTestFieldTo
    {R : ℝ → F →L[ℝ] F} {L c : ℝ} {y v : ℝ → F}
    (hsol : IsJacobiFieldOn R 0 c y v)
    (hc : 0 ≤ c)
    (hR : ContinuousOn R (_root_.Set.Icc 0 c)) :
    indexForm R 0 c y v
        (indexTestFieldTo L (v c)) (indexTestDerivTo L (v c))
      = c * (L - c) * ‖v c‖ ^ 2 := by
  rw [hsol.indexForm_eq_sub hc hR
    (fun t _ => (indexTestFieldTo_hasDerivAt L (v c) t).hasDerivWithinAt)
    (by
      unfold indexTestDerivTo
      fun_prop)]
  simp [indexTestFieldTo, real_inner_smul_right]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.IsJacobiFieldOn.indexForm_indexTestFieldTo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.IsJacobiFieldOn.indexForm_indexTestFieldTo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.IsJacobiFieldOn.indexForm_indexTestFieldTo ``Submission.DifferentialGeometry.Analysis.ODE.IsJacobiFieldOn.indexForm_indexTestFieldTo

theorem indexForm_indexTestField
    {R : ℝ → F →L[ℝ] F} {c : ℝ} {y v : ℝ → F}
    (hsol : IsJacobiFieldOn R 0 c y v)
    (hc : 0 ≤ c)
    (hR : ContinuousOn R (_root_.Set.Icc 0 c)) :
    indexForm R 0 c y v (indexTestField (v c)) (indexTestDeriv (v c))
      = c * (1 - c) * ‖v c‖ ^ 2 := by
  simpa only [indexTestField, indexTestDeriv] using
    hsol.indexForm_indexTestFieldTo (L := 1) hc hR

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.IsJacobiFieldOn.indexForm_indexTestField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.IsJacobiFieldOn.indexForm_indexTestField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.IsJacobiFieldOn.indexForm_indexTestField ``Submission.DifferentialGeometry.Analysis.ODE.IsJacobiFieldOn.indexForm_indexTestField

theorem indexForm_indexTestFieldTo_pos
    {R : ℝ → F →L[ℝ] F} {L c : ℝ} {y v : ℝ → F}
    (hsol : IsJacobiFieldOn R 0 c y v)
    (hc : c ∈ _root_.Set.Ioo (0 : ℝ) L)
    (hR : ContinuousOn R (_root_.Set.Icc 0 c))
    (hvc : v c ≠ 0) :
    0 < indexForm R 0 c y v
      (indexTestFieldTo L (v c)) (indexTestDerivTo L (v c)) := by
  rw [hsol.indexForm_indexTestFieldTo hc.1.le hR]
  have hnorm : 0 < ‖v c‖ := norm_pos_iff.mpr hvc
  exact mul_pos (mul_pos hc.1 (sub_pos.mpr hc.2)) (sq_pos_of_pos hnorm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.IsJacobiFieldOn.indexForm_indexTestFieldTo_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.IsJacobiFieldOn.indexForm_indexTestFieldTo_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.IsJacobiFieldOn.indexForm_indexTestFieldTo_pos ``Submission.DifferentialGeometry.Analysis.ODE.IsJacobiFieldOn.indexForm_indexTestFieldTo_pos

theorem indexForm_indexTestField_pos
    {R : ℝ → F →L[ℝ] F} {c : ℝ} {y v : ℝ → F}
    (hsol : IsJacobiFieldOn R 0 c y v)
    (hc : c ∈ _root_.Set.Ioo (0 : ℝ) 1)
    (hR : ContinuousOn R (_root_.Set.Icc 0 c))
    (hvc : v c ≠ 0) :
    0 < indexForm R 0 c y v
      (indexTestField (v c)) (indexTestDeriv (v c)) := by
  simpa only [indexTestField, indexTestDeriv] using
    hsol.indexForm_indexTestFieldTo_pos (L := 1) hc hR hvc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.IsJacobiFieldOn.indexForm_indexTestField_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.IsJacobiFieldOn.indexForm_indexTestField_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.IsJacobiFieldOn.indexForm_indexTestField_pos ``Submission.DifferentialGeometry.Analysis.ODE.IsJacobiFieldOn.indexForm_indexTestField_pos

theorem exists_split_neg_on
    {R : ℝ → F →L[ℝ] F} {L c : ℝ} {y v : ℝ → F}
    (hsol : IsJacobiFieldOn R 0 L y v)
    (hc : c ∈ _root_.Set.Ioo (0 : ℝ) L)
    (hR : ContinuousOn R (_root_.Set.Icc 0 L))
    (hSym : ∀ t, ∀ x x' : F, ⟪R t x, x'⟫ = ⟪x, R t x'⟫)
    (hy0 : y 0 = 0) (hyc : y c = 0)
    (hne : ∃ t ∈ _root_.Set.Icc (0 : ℝ) L, y t ≠ 0) :
    ∃ s : ℝ,
      indexForm R 0 c
          (y + s • indexTestFieldTo L (v c))
          (v + s • indexTestDerivTo L (v c))
          (y + s • indexTestFieldTo L (v c))
          (v + s • indexTestDerivTo L (v c))
        + indexForm R c L
          (s • indexTestFieldTo L (v c))
          (s • indexTestDerivTo L (v c))
          (s • indexTestFieldTo L (v c))
          (s • indexTestDerivTo L (v c)) < 0 := by
  have hsol0c : IsJacobiFieldOn R 0 c y v :=
    hsol.mono le_rfl hc.2.le
  have hR0c : ContinuousOn R (_root_.Set.Icc 0 c) :=
    hR.mono (_root_.Set.Icc_subset_Icc le_rfl hc.2.le)
  have hRcL : ContinuousOn R (_root_.Set.Icc c L) :=
    hR.mono (_root_.Set.Icc_subset_Icc hc.1.le le_rfl)
  have hvc : v c ≠ 0 :=
    hsol.velocity_ne_zero_of_position_eq_zero hc hR hyc hne
  have hcross : 0 < indexForm R 0 c y v
      (indexTestFieldTo L (v c)) (indexTestDerivTo L (v c)) :=
    hsol0c.indexForm_indexTestFieldTo_pos hc hR0c hvc
  have hself : indexForm R 0 c y v y v = 0 :=
    hsol0c.indexForm_self_zero hc.1.le hR0c hy0 hyc
  have hyy : IntervalIntegrable
      (indexIntegrand R y v y v) MeasureTheory.volume 0 c :=
    intInt_indexIntegrand
      (by simpa only [_root_.Set.uIcc_of_le hc.1.le] using hR0c)
      (by simpa only [_root_.Set.uIcc_of_le hc.1.le] using hsol0c.contOn_fst)
      (by simpa only [_root_.Set.uIcc_of_le hc.1.le] using hsol0c.contOn_snd)
      (by simpa only [_root_.Set.uIcc_of_le hc.1.le] using hsol0c.contOn_fst)
      (by simpa only [_root_.Set.uIcc_of_le hc.1.le] using hsol0c.contOn_snd)
  have hyz : IntervalIntegrable
      (indexIntegrand R y v
        (indexTestFieldTo L (v c)) (indexTestDerivTo L (v c)))
      MeasureTheory.volume 0 c :=
    intInt_indexIntegrand
      (by simpa only [_root_.Set.uIcc_of_le hc.1.le] using hR0c)
      (by simpa only [_root_.Set.uIcc_of_le hc.1.le] using hsol0c.contOn_fst)
      (by simpa only [_root_.Set.uIcc_of_le hc.1.le] using hsol0c.contOn_snd)
      (by
        simpa only [_root_.Set.uIcc_of_le hc.1.le] using
          (indexTestFieldTo_continuous L (v c)).continuousOn)
      (by
        simpa only [_root_.Set.uIcc_of_le hc.1.le] using
          (indexTestDerivTo_continuous L (v c)).continuousOn)
  have hzz0c : IntervalIntegrable
      (indexIntegrand R
        (indexTestFieldTo L (v c)) (indexTestDerivTo L (v c))
        (indexTestFieldTo L (v c)) (indexTestDerivTo L (v c)))
      MeasureTheory.volume 0 c :=
    intInt_indexIntegrand
      (by simpa only [_root_.Set.uIcc_of_le hc.1.le] using hR0c)
      (by
        simpa only [_root_.Set.uIcc_of_le hc.1.le] using
          (indexTestFieldTo_continuous L (v c)).continuousOn)
      (by
        simpa only [_root_.Set.uIcc_of_le hc.1.le] using
          (indexTestDerivTo_continuous L (v c)).continuousOn)
      (by
        simpa only [_root_.Set.uIcc_of_le hc.1.le] using
          (indexTestFieldTo_continuous L (v c)).continuousOn)
      (by
        simpa only [_root_.Set.uIcc_of_le hc.1.le] using
          (indexTestDerivTo_continuous L (v c)).continuousOn)
  have hzzcL : IntervalIntegrable
      (indexIntegrand R
        (indexTestFieldTo L (v c)) (indexTestDerivTo L (v c))
        (indexTestFieldTo L (v c)) (indexTestDerivTo L (v c)))
      MeasureTheory.volume c L :=
    intInt_indexIntegrand
      (by simpa only [_root_.Set.uIcc_of_le hc.2.le] using hRcL)
      (by
        simpa only [_root_.Set.uIcc_of_le hc.2.le] using
          (indexTestFieldTo_continuous L (v c)).continuousOn)
      (by
        simpa only [_root_.Set.uIcc_of_le hc.2.le] using
          (indexTestDerivTo_continuous L (v c)).continuousOn)
      (by
        simpa only [_root_.Set.uIcc_of_le hc.2.le] using
          (indexTestFieldTo_continuous L (v c)).continuousOn)
      (by
        simpa only [_root_.Set.uIcc_of_le hc.2.le] using
          (indexTestDerivTo_continuous L (v c)).continuousOn)
  have hzero_cont : Continuous (fun _ : ℝ => (0 : F)) := continuous_const
  have h00 : IntervalIntegrable
      (indexIntegrand R (fun _ => 0) (fun _ => 0)
        (fun _ => 0) (fun _ => 0))
      MeasureTheory.volume c L :=
    intInt_indexIntegrand
      (by simpa only [_root_.Set.uIcc_of_le hc.2.le] using hRcL)
      (by simpa only [_root_.Set.uIcc_of_le hc.2.le] using hzero_cont.continuousOn)
      (by simpa only [_root_.Set.uIcc_of_le hc.2.le] using hzero_cont.continuousOn)
      (by simpa only [_root_.Set.uIcc_of_le hc.2.le] using hzero_cont.continuousOn)
      (by simpa only [_root_.Set.uIcc_of_le hc.2.le] using hzero_cont.continuousOn)
  have h0z : IntervalIntegrable
      (indexIntegrand R (fun _ => 0) (fun _ => 0)
        (indexTestFieldTo L (v c)) (indexTestDerivTo L (v c)))
      MeasureTheory.volume c L :=
    intInt_indexIntegrand
      (by simpa only [_root_.Set.uIcc_of_le hc.2.le] using hRcL)
      (by simpa only [_root_.Set.uIcc_of_le hc.2.le] using hzero_cont.continuousOn)
      (by simpa only [_root_.Set.uIcc_of_le hc.2.le] using hzero_cont.continuousOn)
      (by
        simpa only [_root_.Set.uIcc_of_le hc.2.le] using
          (indexTestFieldTo_continuous L (v c)).continuousOn)
      (by
        simpa only [_root_.Set.uIcc_of_le hc.2.le] using
          (indexTestDerivTo_continuous L (v c)).continuousOn)
  have hleft (s : ℝ) :
      indexForm R 0 c
          (y + s • indexTestFieldTo L (v c))
          (v + s • indexTestDerivTo L (v c))
          (y + s • indexTestFieldTo L (v c))
          (v + s • indexTestDerivTo L (v c))
        = indexForm R 0 c y v y v
          + 2 * s * indexForm R 0 c y v
            (indexTestFieldTo L (v c)) (indexTestDerivTo L (v c))
          + s ^ 2 * indexForm R 0 c
            (indexTestFieldTo L (v c)) (indexTestDerivTo L (v c))
            (indexTestFieldTo L (v c)) (indexTestDerivTo L (v c)) :=
    indexForm_add_smul hSym hyy hyz hzz0c s
  have hright (s : ℝ) :
      indexForm R c L
          (s • indexTestFieldTo L (v c))
          (s • indexTestDerivTo L (v c))
          (s • indexTestFieldTo L (v c))
          (s • indexTestDerivTo L (v c))
        = s ^ 2 * indexForm R c L
            (indexTestFieldTo L (v c)) (indexTestDerivTo L (v c))
            (indexTestFieldTo L (v c)) (indexTestDerivTo L (v c)) := by
    have h := indexForm_add_smul
      (R := R) (a := c) (b := L)
      (y := fun _ => (0 : F)) (v := fun _ => (0 : F))
      (z := indexTestFieldTo L (v c)) (w := indexTestDerivTo L (v c))
      hSym h00 h0z hzzcL s
    simpa [indexForm, indexIntegrand] using h
  let κ : ℝ := indexForm R 0 c y v
    (indexTestFieldTo L (v c)) (indexTestDerivTo L (v c))
  let Q : ℝ :=
    indexForm R 0 c
        (indexTestFieldTo L (v c)) (indexTestDerivTo L (v c))
        (indexTestFieldTo L (v c)) (indexTestDerivTo L (v c))
      + indexForm R c L
        (indexTestFieldTo L (v c)) (indexTestDerivTo L (v c))
        (indexTestFieldTo L (v c)) (indexTestDerivTo L (v c))
  have hκ : 0 < κ := by simpa only [κ] using hcross
  obtain ⟨s, hs⟩ := exists_quad_neg hκ (Q := Q)
  refine ⟨s, ?_⟩
  calc
    indexForm R 0 c
          (y + s • indexTestFieldTo L (v c))
          (v + s • indexTestDerivTo L (v c))
          (y + s • indexTestFieldTo L (v c))
          (v + s • indexTestDerivTo L (v c))
        + indexForm R c L
          (s • indexTestFieldTo L (v c))
          (s • indexTestDerivTo L (v c))
          (s • indexTestFieldTo L (v c))
          (s • indexTestDerivTo L (v c))
        = 2 * s * κ + s ^ 2 * Q := by
          rw [hleft s, hright s, hself]
          simp only [zero_add]
          dsimp only [κ, Q]
          ring
    _ < 0 := hs

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.IsJacobiFieldOn.exists_split_neg_on then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.IsJacobiFieldOn.exists_split_neg_on"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.IsJacobiFieldOn.exists_split_neg_on ``Submission.DifferentialGeometry.Analysis.ODE.IsJacobiFieldOn.exists_split_neg_on

theorem exists_split_neg
    {R : ℝ → F →L[ℝ] F} {c : ℝ} {y v : ℝ → F}
    (hsol : IsJacobiFieldOn R 0 1 y v)
    (hc : c ∈ _root_.Set.Ioo (0 : ℝ) 1)
    (hR : ContinuousOn R (_root_.Set.Icc 0 1))
    (hSym : ∀ t, ∀ x x' : F, ⟪R t x, x'⟫ = ⟪x, R t x'⟫)
    (hy0 : y 0 = 0) (hyc : y c = 0)
    (hne : ∃ t ∈ _root_.Set.Icc (0 : ℝ) 1, y t ≠ 0) :
    ∃ s : ℝ,
      indexForm R 0 c
          (y + s • indexTestField (v c))
          (v + s • indexTestDeriv (v c))
          (y + s • indexTestField (v c))
          (v + s • indexTestDeriv (v c))
        + indexForm R c 1
          (s • indexTestField (v c))
          (s • indexTestDeriv (v c))
          (s • indexTestField (v c))
          (s • indexTestDeriv (v c)) < 0 := by
  simpa only [indexTestField, indexTestDeriv] using
    hsol.exists_split_neg_on hc hR hSym hy0 hyc hne

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.IsJacobiFieldOn.exists_split_neg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.IsJacobiFieldOn.exists_split_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.IsJacobiFieldOn.exists_split_neg ``Submission.DifferentialGeometry.Analysis.ODE.IsJacobiFieldOn.exists_split_neg

theorem exists_smooth_split
    {R : ℝ → F →L[ℝ] F} {A B c : ℝ} {y v : ℝ → F}
    (hA : A < 0) (hB : 1 < B)
    (hc : c ∈ _root_.Set.Ioo (0 : ℝ) 1)
    (hR : ContDiffOn ℝ ∞ R (_root_.Set.Ioo A B))
    (hSym : ∀ t, ∀ x x' : F, ⟪R t x, x'⟫ = ⟪x, R t x'⟫)
    (hy : ∀ t ∈ _root_.Set.Ioo A B, HasDerivAt y (v t) t)
    (hv : ∀ t ∈ _root_.Set.Ioo A B, HasDerivAt v (-(R t) (y t)) t)
    (hy0 : y 0 = 0) (hyc : y c = 0)
    (hne : ∃ t ∈ _root_.Set.Icc (0 : ℝ) 1, y t ≠ 0) :
    ∃ W₀ W₁ : ℝ → F,
      ContDiffOn ℝ ∞ W₀ (_root_.Set.Ioo A B)
        ∧ ContDiff ℝ ∞ W₁
        ∧ W₀ 0 = 0
        ∧ W₁ 1 = 0
        ∧ W₀ c = W₁ c
        ∧ indexForm R 0 c W₀ (deriv W₀) W₀ (deriv W₀)
          + indexForm R c 1 W₁ (deriv W₁) W₁ (deriv W₁) < 0 := by
  have h01 : _root_.Set.Icc (0 : ℝ) 1 ⊆ _root_.Set.Ioo A B := by
    intro t ht
    exact ⟨hA.trans_le ht.1, ht.2.trans_lt hB⟩
  have hR01 : ContinuousOn R (_root_.Set.Icc (0 : ℝ) 1) :=
    hR.continuousOn.mono h01
  have hsol : IsJacobiFieldOn R 0 1 y v :=
    { deriv_fst := fun t ht => (hy t (h01 ht)).hasDerivWithinAt
      deriv_snd := fun t ht => (hv t (h01 ht)).hasDerivWithinAt }
  obtain ⟨s, hs⟩ :=
    hsol.exists_split_neg hc hR01 hSym hy0 hyc hne
  let Z : ℝ → F := indexTestField (v c)
  let DZ : ℝ → F := indexTestDeriv (v c)
  have hZd : ∀ t, HasDerivAt Z (DZ t) t := by
    intro t
    exact indexTestField_hasDerivAt (v c) t
  have hW₀d : ∀ t ∈ _root_.Set.Ioo A B,
      HasDerivAt (y + s • Z) (v t + s • DZ t) t := by
    intro t ht
    exact (hy t ht).add ((hZd t).const_smul s)
  have hdW₀ : ∀ t ∈ _root_.Set.Ioo A B,
      deriv (y + s • Z) t = (v + s • DZ) t := by
    intro t ht
    simpa only [Pi.add_apply, Pi.smul_apply] using (hW₀d t ht).deriv
  have hdW₁ : ∀ t,
      deriv (s • Z) t = (s • DZ) t := by
    intro t
    simpa only [Pi.smul_apply] using ((hZd t).const_smul s).deriv
  have hySmooth : ContDiffOn ℝ ∞ y (_root_.Set.Ioo A B) :=
    (contDiffOn_infty_jacobi_system isOpen_Ioo hR hy hv).1
  have hZSmooth : ContDiff ℝ ∞ Z := by
    exact indexTestField_contDiff (v c)
  have hW₀Smooth : ContDiffOn ℝ ∞ (y + s • Z) (_root_.Set.Ioo A B) :=
    hySmooth.add (hZSmooth.const_smul s).contDiffOn
  have hW₁Smooth : ContDiff ℝ ∞ (s • Z) :=
    hZSmooth.const_smul s
  have h0c : _root_.Set.Icc (0 : ℝ) c ⊆ _root_.Set.Icc (0 : ℝ) 1 :=
    _root_.Set.Icc_subset_Icc le_rfl hc.2.le
  have hsub0c : _root_.Set.Icc (0 : ℝ) c ⊆ _root_.Set.Ioo A B :=
    h0c.trans h01
  have e₀ :
      indexForm R 0 c (y + s • Z) (deriv (y + s • Z))
          (y + s • Z) (deriv (y + s • Z))
        = indexForm R 0 c (y + s • Z) (v + s • DZ)
          (y + s • Z) (v + s • DZ) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [_root_.Set.uIcc_of_le hc.1.le] at ht
    simp only [indexIntegrand]
    rw [hdW₀ t (hsub0c ht)]
  have e₁ :
      indexForm R c 1 (s • Z) (deriv (s • Z))
          (s • Z) (deriv (s • Z))
        = indexForm R c 1 (s • Z) (s • DZ)
          (s • Z) (s • DZ) := by
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [indexIntegrand]
    rw [hdW₁ t]
  refine ⟨y + s • Z, s • Z, hW₀Smooth, hW₁Smooth, ?_, ?_, ?_, ?_⟩
  · simp [Z, indexTestField, indexTestFieldTo, hy0]
  · simp [Z, indexTestField, indexTestFieldTo]
  · simp [hyc]
  · rw [e₀, e₁]
    exact hs

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.IsJacobiFieldOn.exists_smooth_split then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.IsJacobiFieldOn.exists_smooth_split"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.IsJacobiFieldOn.exists_smooth_split ``Submission.DifferentialGeometry.Analysis.ODE.IsJacobiFieldOn.exists_smooth_split

end IsJacobiFieldOn

end DifferentialGeometry.Analysis.ODE
