import Mathlib.Analysis.InnerProductSpace.Calculus
import Submission.DifferentialGeometry.Analysis.Calculus.SmoothExtension.BoundaryDerivLimit
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.Set _root_.intervalIntegral _root_.MeasureTheory
open scoped _root_.RealInnerProductSpace

noncomputable section

namespace DifferentialGeometry.Analysis.ODE

section Normed

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

structure IsJacobiFieldOn (R : ℝ → F →L[ℝ] F) (a b : ℝ) (y v : ℝ → F) : Prop where
  deriv_fst : ∀ t ∈ _root_.Set.Icc a b, HasDerivWithinAt y (v t) (_root_.Set.Icc a b) t
  deriv_snd : ∀ t ∈ _root_.Set.Icc a b, HasDerivWithinAt v (-(R t) (y t)) (_root_.Set.Icc a b) t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.IsJacobiFieldOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.IsJacobiFieldOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.IsJacobiFieldOn ``Submission.DifferentialGeometry.Analysis.ODE.IsJacobiFieldOn

namespace IsJacobiFieldOn

variable {R : ℝ → F →L[ℝ] F} {a b : ℝ} {y v z w : ℝ → F}

theorem contOn_fst (h : IsJacobiFieldOn R a b y v) : ContinuousOn y (_root_.Set.Icc a b) :=
  fun t ht => (h.deriv_fst t ht).continuousWithinAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.IsJacobiFieldOn.contOn_fst then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.IsJacobiFieldOn.contOn_fst"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.IsJacobiFieldOn.contOn_fst ``Submission.DifferentialGeometry.Analysis.ODE.IsJacobiFieldOn.contOn_fst

theorem contOn_snd (h : IsJacobiFieldOn R a b y v) : ContinuousOn v (_root_.Set.Icc a b) :=
  fun t ht => (h.deriv_snd t ht).continuousWithinAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.IsJacobiFieldOn.contOn_snd then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.IsJacobiFieldOn.contOn_snd"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.IsJacobiFieldOn.contOn_snd ``Submission.DifferentialGeometry.Analysis.ODE.IsJacobiFieldOn.contOn_snd

theorem of_hasDerivAt_Ioo {R : ℝ → F →L[ℝ] F} {a b : ℝ} {y v : ℝ → F}
    (hy : ContinuousOn y (_root_.Set.Icc a b)) (hv : ContinuousOn v (_root_.Set.Icc a b))
    (hacc : ContinuousOn (fun t => -(R t) (y t)) (_root_.Set.Icc a b))
    (hode : ∀ t ∈ _root_.Set.Ioo a b,
      HasDerivAt y (v t) t ∧ HasDerivAt v (-(R t) (y t)) t) :
    IsJacobiFieldOn R a b y v := by
  exact ⟨fun t ht => Calculus.SmoothExtension.hasDerivWithinAt_Icc_of_hasDerivAt_Ioo
    hy hv (fun r hr => (hode r hr).1) ht,
    fun t ht => Calculus.SmoothExtension.hasDerivWithinAt_Icc_of_hasDerivAt_Ioo
      hv hacc (fun r hr => (hode r hr).2) ht⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.IsJacobiFieldOn.of_hasDerivAt_Ioo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.IsJacobiFieldOn.of_hasDerivAt_Ioo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.IsJacobiFieldOn.of_hasDerivAt_Ioo ``Submission.DifferentialGeometry.Analysis.ODE.IsJacobiFieldOn.of_hasDerivAt_Ioo

end IsJacobiFieldOn

end Normed

section InnerProduct

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

def indexIntegrand (R : ℝ → F →L[ℝ] F) (y v z w : ℝ → F) (t : ℝ) : ℝ :=
  ⟪v t, w t⟫ - ⟪R t (y t), z t⟫

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.indexIntegrand then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.indexIntegrand"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.indexIntegrand ``Submission.DifferentialGeometry.Analysis.ODE.indexIntegrand

def indexForm (R : ℝ → F →L[ℝ] F) (a b : ℝ) (y v z w : ℝ → F) : ℝ :=
  ∫ t in a..b, indexIntegrand R y v z w t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.indexForm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.indexForm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.indexForm ``Submission.DifferentialGeometry.Analysis.ODE.indexForm

theorem indexForm_def (R : ℝ → F →L[ℝ] F) (a b : ℝ) (y v z w : ℝ → F) :
    indexForm R a b y v z w = ∫ t in a..b, indexIntegrand R y v z w t := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.indexForm_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.indexForm_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.indexForm_def ``Submission.DifferentialGeometry.Analysis.ODE.indexForm_def

theorem indexIntegrand_symm {R : ℝ → F →L[ℝ] F}
    (hR : ∀ t, ∀ x x' : F, ⟪R t x, x'⟫ = ⟪x, R t x'⟫)
    (y v z w : ℝ → F) (t : ℝ) :
    indexIntegrand R y v z w t = indexIntegrand R z w y v t := by
  unfold indexIntegrand
  rw [real_inner_comm (v t) (w t), hR t (y t) (z t),
    real_inner_comm (y t) (R t (z t))]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.indexIntegrand_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.indexIntegrand_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.indexIntegrand_symm ``Submission.DifferentialGeometry.Analysis.ODE.indexIntegrand_symm

theorem indexForm_symm {R : ℝ → F →L[ℝ] F}
    (hR : ∀ t, ∀ x x' : F, ⟪R t x, x'⟫ = ⟪x, R t x'⟫)
    (a b : ℝ) (y v z w : ℝ → F) :
    indexForm R a b y v z w = indexForm R a b z w y v :=
  intervalIntegral.integral_congr fun t _ => indexIntegrand_symm hR y v z w t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.indexForm_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.indexForm_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.indexForm_symm ``Submission.DifferentialGeometry.Analysis.ODE.indexForm_symm

theorem contOn_indexIntegrand {R : ℝ → F →L[ℝ] F} {y v z w : ℝ → F} {s : Set ℝ}
    (hR : ContinuousOn R s) (hy : ContinuousOn y s) (hv : ContinuousOn v s)
    (hz : ContinuousOn z s) (hw : ContinuousOn w s) :
    ContinuousOn (indexIntegrand R y v z w) s :=
  (hv.inner hw).sub ((hR.clm_apply hy).inner hz)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.contOn_indexIntegrand then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.contOn_indexIntegrand"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.contOn_indexIntegrand ``Submission.DifferentialGeometry.Analysis.ODE.contOn_indexIntegrand

theorem intInt_indexIntegrand {R : ℝ → F →L[ℝ] F} {y v z w : ℝ → F} {a b : ℝ}
    (hR : ContinuousOn R (_root_.Set.uIcc a b)) (hy : ContinuousOn y (_root_.Set.uIcc a b))
    (hv : ContinuousOn v (_root_.Set.uIcc a b)) (hz : ContinuousOn z (_root_.Set.uIcc a b))
    (hw : ContinuousOn w (_root_.Set.uIcc a b)) :
    IntervalIntegrable (indexIntegrand R y v z w) _root_.MeasureTheory.MeasureSpace.volume a b :=
  (contOn_indexIntegrand hR hy hv hz hw).intervalIntegrable

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.intInt_indexIntegrand then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.intInt_indexIntegrand"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.intInt_indexIntegrand ``Submission.DifferentialGeometry.Analysis.ODE.intInt_indexIntegrand

theorem IsJacobiFieldOn.hasDerivAt_inner {R : ℝ → F →L[ℝ] F} {a b : ℝ}
    {y v z w : ℝ → F}
    (hy : IsJacobiFieldOn R a b y v)
    (hz : ∀ t ∈ _root_.Set.Icc a b, HasDerivWithinAt z (w t) (_root_.Set.Icc a b) t)
    {t : ℝ} (ht : t ∈ _root_.Set.Ioo a b) :
    HasDerivAt (fun s => (⟪v s, z s⟫ : ℝ)) (indexIntegrand R y v z w t) t := by
  have hmem : _root_.Set.Icc a b ∈ nhds t := Icc_mem_nhds ht.1 ht.2
  have hv : HasDerivAt v (-(R t) (y t)) t :=
    (hy.deriv_snd t (_root_.Set.Ioo_subset_Icc_self ht)).hasDerivAt hmem
  have hzt : HasDerivAt z (w t) t :=
    (hz t (_root_.Set.Ioo_subset_Icc_self ht)).hasDerivAt hmem
  have h := hv.inner ℝ hzt
  have hcalc : (⟪v t, w t⟫ : ℝ) + ⟪-(R t) (y t), z t⟫
      = indexIntegrand R y v z w t := by
    unfold indexIntegrand
    rw [inner_neg_left]
    ring
  rw [← hcalc]
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.IsJacobiFieldOn.hasDerivAt_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.IsJacobiFieldOn.hasDerivAt_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.IsJacobiFieldOn.hasDerivAt_inner ``Submission.DifferentialGeometry.Analysis.ODE.IsJacobiFieldOn.hasDerivAt_inner

theorem IsJacobiFieldOn.indexForm_eq_sub {R : ℝ → F →L[ℝ] F} {a b : ℝ}
    {y v z w : ℝ → F}
    (hab : a ≤ b) (hR : ContinuousOn R (_root_.Set.Icc a b))
    (hy : IsJacobiFieldOn R a b y v)
    (hz : ∀ t ∈ _root_.Set.Icc a b, HasDerivWithinAt z (w t) (_root_.Set.Icc a b) t)
    (hw : ContinuousOn w (_root_.Set.Icc a b)) :
    indexForm R a b y v z w = ⟪v b, z b⟫ - ⟪v a, z a⟫ := by
  have hzc : ContinuousOn z (_root_.Set.Icc a b) := fun t ht => (hz t ht).continuousWithinAt
  have huIcc : _root_.Set.uIcc a b = _root_.Set.Icc a b := _root_.Set.uIcc_of_le hab
  have hint : IntervalIntegrable (indexIntegrand R y v z w) _root_.MeasureTheory.MeasureSpace.volume a b := by
    refine intInt_indexIntegrand ?_ ?_ ?_ ?_ ?_ <;> rw [huIcc]
    exacts [hR, hy.contOn_fst, hy.contOn_snd, hzc, hw]
  have hcont : ContinuousOn (fun s => (⟪v s, z s⟫ : ℝ)) (_root_.Set.Icc a b) :=
    hy.contOn_snd.inner hzc
  have hderiv : ∀ t ∈ _root_.Set.Ioo a b,
      HasDerivWithinAt (fun s => (⟪v s, z s⟫ : ℝ))
        (indexIntegrand R y v z w t) (_root_.Set.Ioi t) t :=
    fun t ht => (hy.hasDerivAt_inner hz ht).hasDerivWithinAt
  exact intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab hcont
    hderiv hint

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.IsJacobiFieldOn.indexForm_eq_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.IsJacobiFieldOn.indexForm_eq_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.IsJacobiFieldOn.indexForm_eq_sub ``Submission.DifferentialGeometry.Analysis.ODE.IsJacobiFieldOn.indexForm_eq_sub

theorem IsJacobiFieldOn.indexForm_self_zero {R : ℝ → F →L[ℝ] F} {a b : ℝ}
    {y v : ℝ → F}
    (hab : a ≤ b) (hR : ContinuousOn R (_root_.Set.Icc a b))
    (hy : IsJacobiFieldOn R a b y v) (hya : y a = 0) (hyb : y b = 0) :
    indexForm R a b y v y v = 0 := by
  rw [hy.indexForm_eq_sub hab hR hy.deriv_fst hy.contOn_snd, hya, hyb]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.IsJacobiFieldOn.indexForm_self_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.IsJacobiFieldOn.indexForm_self_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.IsJacobiFieldOn.indexForm_self_zero ``Submission.DifferentialGeometry.Analysis.ODE.IsJacobiFieldOn.indexForm_self_zero

theorem indexForm_add_adjacent {R : ℝ → F →L[ℝ] F} {a c b : ℝ}
    {y v z w : ℝ → F}
    (h₁ : IntervalIntegrable (indexIntegrand R y v z w) _root_.MeasureTheory.MeasureSpace.volume a c)
    (h₂ : IntervalIntegrable (indexIntegrand R y v z w) _root_.MeasureTheory.MeasureSpace.volume c b) :
    indexForm R a c y v z w + indexForm R c b y v z w
      = indexForm R a b y v z w :=
  intervalIntegral.integral_add_adjacent_intervals h₁ h₂

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.indexForm_add_adjacent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.indexForm_add_adjacent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.indexForm_add_adjacent ``Submission.DifferentialGeometry.Analysis.ODE.indexForm_add_adjacent

@[simp] theorem indexForm_same (R : ℝ → F →L[ℝ] F) (a : ℝ) (y v z w : ℝ → F) :
    indexForm R a a y v z w = 0 := intervalIntegral.integral_same

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.indexForm_same then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.indexForm_same"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.indexForm_same ``Submission.DifferentialGeometry.Analysis.ODE.indexForm_same

theorem indexIntegrand_add_smul {R : ℝ → F →L[ℝ] F}
    (hR : ∀ t, ∀ x x' : F, ⟪R t x, x'⟫ = ⟪x, R t x'⟫)
    (y v z w : ℝ → F) (c : ℝ) (t : ℝ) :
    indexIntegrand R (y + c • z) (v + c • w) (y + c • z) (v + c • w) t
      = indexIntegrand R y v y v t + 2 * c * indexIntegrand R y v z w t
        + c ^ 2 * indexIntegrand R z w z w t := by
  have hcross : (⟪R t (z t), y t⟫ : ℝ) = ⟪R t (y t), z t⟫ := by
    rw [hR t (z t) (y t), real_inner_comm (z t) (R t (y t))]
  simp only [indexIntegrand, Pi.add_apply, Pi.smul_apply, map_add, map_smul,
    inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right]
  rw [real_inner_comm (w t) (v t), hcross]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.indexIntegrand_add_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.indexIntegrand_add_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.indexIntegrand_add_smul ``Submission.DifferentialGeometry.Analysis.ODE.indexIntegrand_add_smul

theorem indexForm_add_smul {R : ℝ → F →L[ℝ] F} {a b : ℝ} {y v z w : ℝ → F}
    (hR : ∀ t, ∀ x x' : F, ⟪R t x, x'⟫ = ⟪x, R t x'⟫)
    (hyy : IntervalIntegrable (indexIntegrand R y v y v) _root_.MeasureTheory.MeasureSpace.volume a b)
    (hyz : IntervalIntegrable (indexIntegrand R y v z w) _root_.MeasureTheory.MeasureSpace.volume a b)
    (hzz : IntervalIntegrable (indexIntegrand R z w z w) _root_.MeasureTheory.MeasureSpace.volume a b)
    (c : ℝ) :
    indexForm R a b (y + c • z) (v + c • w) (y + c • z) (v + c • w)
      = indexForm R a b y v y v + 2 * c * indexForm R a b y v z w
        + c ^ 2 * indexForm R a b z w z w := by
  unfold indexForm
  rw [intervalIntegral.integral_congr
    (g := fun t => indexIntegrand R y v y v t
      + 2 * c * indexIntegrand R y v z w t
      + c ^ 2 * indexIntegrand R z w z w t)
    (fun t _ => indexIntegrand_add_smul hR y v z w c t)]
  rw [intervalIntegral.integral_add
      (hyy.add (hyz.const_mul (2 * c))) (hzz.const_mul (c ^ 2)),
    intervalIntegral.integral_add hyy (hyz.const_mul (2 * c)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.indexForm_add_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.indexForm_add_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.indexForm_add_smul ``Submission.DifferentialGeometry.Analysis.ODE.indexForm_add_smul

theorem IsJacobiFieldOn.indexForm_le
    {R : ℝ → F →L[ℝ] F} {a b : ℝ} {y v z w : ℝ → F}
    (hab : a ≤ b)
    (hR : ContinuousOn R (_root_.Set.Icc a b))
    (hR_symm : ∀ t, ∀ x x' : F, ⟪R t x, x'⟫ = ⟪x, R t x'⟫)
    (hy : IsJacobiFieldOn R a b y v)
    (hz : ∀ t ∈ _root_.Set.Icc a b, HasDerivWithinAt z (w t) (_root_.Set.Icc a b) t)
    (hw : ContinuousOn w (_root_.Set.Icc a b))
    (hza : z a = y a) (hzb : z b = y b)
    (hsub : 0 ≤ indexForm R a b (z - y) (w - v) (z - y) (w - v)) :
    indexForm R a b y v y v ≤ indexForm R a b z w z w := by
  let d : ℝ → F := z - y
  let e : ℝ → F := w - v
  have hz_cont : ContinuousOn z (_root_.Set.Icc a b) :=
    fun t ht => (hz t ht).continuousWithinAt
  have hd_cont : ContinuousOn d (_root_.Set.Icc a b) := hz_cont.sub hy.contOn_fst
  have he_cont : ContinuousOn e (_root_.Set.Icc a b) := hw.sub hy.contOn_snd
  have hd_deriv : ∀ t ∈ _root_.Set.Icc a b,
      HasDerivWithinAt d (e t) (_root_.Set.Icc a b) t := by
    intro t ht
    exact (hz t ht).sub (hy.deriv_fst t ht)
  have hyy : IntervalIntegrable
      (indexIntegrand R y v y v) _root_.MeasureTheory.MeasureSpace.volume a b :=
    intInt_indexIntegrand
      (by simpa [_root_.Set.uIcc_of_le hab] using hR)
      (by simpa [_root_.Set.uIcc_of_le hab] using hy.contOn_fst)
      (by simpa [_root_.Set.uIcc_of_le hab] using hy.contOn_snd)
      (by simpa [_root_.Set.uIcc_of_le hab] using hy.contOn_fst)
      (by simpa [_root_.Set.uIcc_of_le hab] using hy.contOn_snd)
  have hyd : IntervalIntegrable
      (indexIntegrand R y v d e) _root_.MeasureTheory.MeasureSpace.volume a b :=
    intInt_indexIntegrand
      (by simpa [_root_.Set.uIcc_of_le hab] using hR)
      (by simpa [_root_.Set.uIcc_of_le hab] using hy.contOn_fst)
      (by simpa [_root_.Set.uIcc_of_le hab] using hy.contOn_snd)
      (by simpa [_root_.Set.uIcc_of_le hab] using hd_cont)
      (by simpa [_root_.Set.uIcc_of_le hab] using he_cont)
  have hdd : IntervalIntegrable
      (indexIntegrand R d e d e) _root_.MeasureTheory.MeasureSpace.volume a b :=
    intInt_indexIntegrand
      (by simpa [_root_.Set.uIcc_of_le hab] using hR)
      (by simpa [_root_.Set.uIcc_of_le hab] using hd_cont)
      (by simpa [_root_.Set.uIcc_of_le hab] using he_cont)
      (by simpa [_root_.Set.uIcc_of_le hab] using hd_cont)
      (by simpa [_root_.Set.uIcc_of_le hab] using he_cont)
  have hda : d a = 0 := by
    dsimp only [d]
    simp only [Pi.sub_apply]
    exact sub_eq_zero.mpr hza
  have hdb : d b = 0 := by
    dsimp only [d]
    simp only [Pi.sub_apply]
    exact sub_eq_zero.mpr hzb
  have hcross : indexForm R a b y v d e = 0 := by
    rw [hy.indexForm_eq_sub hab hR hd_deriv he_cont, hda, hdb]
    simp
  have hsum := indexForm_add_smul hR_symm hyy hyd hdd (1 : ℝ)
  have hz_eq : y + (1 : ℝ) • d = z := by
    funext t
    simp [d]
  have hw_eq : v + (1 : ℝ) • e = w := by
    funext t
    simp [e]
  rw [hz_eq, hw_eq, hcross, _root_.MulZeroClass.mul_zero, add_zero, one_pow, one_mul] at hsum
  rw [hsum]
  exact le_add_of_nonneg_right hsub

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.IsJacobiFieldOn.indexForm_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.IsJacobiFieldOn.indexForm_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.IsJacobiFieldOn.indexForm_le ``Submission.DifferentialGeometry.Analysis.ODE.IsJacobiFieldOn.indexForm_le

theorem exists_indexForm_neg {R : ℝ → F →L[ℝ] F} {a b : ℝ} {y v z w : ℝ → F}
    (hR : ∀ t, ∀ x x' : F, ⟪R t x, x'⟫ = ⟪x, R t x'⟫)
    (hyy : IntervalIntegrable (indexIntegrand R y v y v) _root_.MeasureTheory.MeasureSpace.volume a b)
    (hyz : IntervalIntegrable (indexIntegrand R y v z w) _root_.MeasureTheory.MeasureSpace.volume a b)
    (hzz : IntervalIntegrable (indexIntegrand R z w z w) _root_.MeasureTheory.MeasureSpace.volume a b)
    (hself : indexForm R a b y v y v = 0)
    (hcross : indexForm R a b y v z w ≠ 0) :
    ∃ c : ℝ,
      indexForm R a b (y + c • z) (v + c • w) (y + c • z) (v + c • w) < 0 := by
  set κ := indexForm R a b y v z w with hκ
  set Q := indexForm R a b z w z w with hQ
  have hpos : (0 : ℝ) < |Q| + 1 := by positivity
  refine ⟨-κ / (|Q| + 1), ?_⟩
  rw [indexForm_add_smul hR hyy hyz hzz, hself, ← hκ, ← hQ]
  set c : ℝ := -κ / (|Q| + 1) with hc
  have hq : 0 + 2 * c * κ + c ^ 2 * Q = c * (2 * κ + c * Q) := by ring
  rw [hq]
  have hκpos : 0 < |κ| := abs_pos.mpr hcross
  have hcQ : |c * Q| < |κ| := by
    rw [hc, abs_mul, abs_div, abs_neg, abs_of_pos hpos,
      div_mul_eq_mul_div, div_lt_iff₀ hpos]
    nlinarith [abs_nonneg Q]
  rcases lt_or_gt_of_ne hcross with hneg | hpos'
  · have hcpos : 0 < c := by
      rw [hc]
      exact div_pos (neg_pos.mpr hneg) hpos
    have hsum : 2 * κ + c * Q < 0 := by
      have h2 := (abs_lt.mp hcQ).2
      rw [abs_of_neg hneg] at h2
      linarith
    exact mul_neg_of_pos_of_neg hcpos hsum
  · have hcneg : c < 0 := by
      rw [hc]
      refine div_neg_of_neg_of_pos ?_ hpos
      linarith
    have hsum : 0 < 2 * κ + c * Q := by
      have h1 := (abs_lt.mp hcQ).1
      rw [abs_of_pos hpos'] at h1
      linarith
    exact mul_neg_of_neg_of_pos hcneg hsum

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.exists_indexForm_neg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.exists_indexForm_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.exists_indexForm_neg ``Submission.DifferentialGeometry.Analysis.ODE.exists_indexForm_neg

end InnerProduct

end DifferentialGeometry.Analysis.ODE
