-- Modified 2026-04-28: updated internal import paths for project namespace
import Submission.DifferentialGeometry.External.DeGiorgi.WeakFormulation.SolutionInterfaces

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-!
# Weak Formulation: Smooth Test Functions

This module packages the smooth compactly supported test functions used to
bridge between classical gradients and the Sobolev weak-formulation layer.
-/

noncomputable section

open _root_.MeasureTheory
open scoped _root_.InnerProductSpace

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => AmbientSpace d

/-! ## Smooth Test Functions And L² Coefficient Operator -/

/-- Smooth compactly supported test functions supported in `Ω`. -/
def IsSmoothTestOn (Ω : Set E) (u : E → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) u ∧ HasCompactSupport u ∧ tsupport u ⊆ Ω

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.IsSmoothTestOn then
    throwError "Refusing to shadow existing declaration DeGiorgi.IsSmoothTestOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.IsSmoothTestOn ``Submission.DeGiorgi.IsSmoothTestOn

omit [NeZero d] in
theorem IsSmoothTestOn.zero
    {Ω : Set E} :
    IsSmoothTestOn Ω (fun _ : E => (0 : ℝ)) := by
  refine ⟨by simpa using (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : E => (0 : ℝ))),
    HasCompactSupport.zero, by simp⟩

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DeGiorgi.IsSmoothTestOn
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.IsSmoothTestOn.zero then
    throwError "Refusing to shadow existing declaration DeGiorgi.IsSmoothTestOn.zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.IsSmoothTestOn.zero ``Submission.DeGiorgi.IsSmoothTestOn.zero

omit [NeZero d] in
theorem IsSmoothTestOn.add
    {Ω : Set E} {u v : E → ℝ}
    (hu : IsSmoothTestOn Ω u) (hv : IsSmoothTestOn Ω v) :
    IsSmoothTestOn Ω (fun x => u x + v x) := by
  refine ⟨hu.1.add hv.1, hu.2.1.add hv.2.1, ?_⟩
  exact (tsupport_add u v).trans <| Set.union_subset hu.2.2 hv.2.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.IsSmoothTestOn.add then
    throwError "Refusing to shadow existing declaration DeGiorgi.IsSmoothTestOn.add"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.IsSmoothTestOn.add ``Submission.DeGiorgi.IsSmoothTestOn.add

omit [NeZero d] in
theorem IsSmoothTestOn.smul
    {Ω : Set E} (c : ℝ) {u : E → ℝ}
    (hu : IsSmoothTestOn Ω u) :
    IsSmoothTestOn Ω (fun x => c * u x) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [smul_eq_mul] using (contDiff_const.mul hu.1)
  · have hfun : (fun x : E ↦ c * u x) = (fun _ : E ↦ c) * u := by
      funext x
      rfl
    rw [hfun]
    exact hu.2.1.mul_left
  · simpa [Pi.smul_apply, smul_eq_mul] using
      (tsupport_smul_subset_right (fun _ : E => c) u).trans hu.2.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.IsSmoothTestOn.smul then
    throwError "Refusing to shadow existing declaration DeGiorgi.IsSmoothTestOn.smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.IsSmoothTestOn.smul ``Submission.DeGiorgi.IsSmoothTestOn.smul

omit [NeZero d] in
theorem IsSmoothTestOn.sub
    {Ω : Set E} {u v : E → ℝ}
    (hu : IsSmoothTestOn Ω u) (hv : IsSmoothTestOn Ω v) :
    IsSmoothTestOn Ω (fun x => u x - v x) := by
  simpa [sub_eq_add_neg, Pi.smul_apply, smul_eq_mul] using hu.add (hv.smul (-1))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.IsSmoothTestOn.sub then
    throwError "Refusing to shadow existing declaration DeGiorgi.IsSmoothTestOn.sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.IsSmoothTestOn.sub ``Submission.DeGiorgi.IsSmoothTestOn.sub

/-- Classical gradient field of a smooth scalar function. -/
noncomputable def smoothGradField (u : E → ℝ) : E → E :=
  fun x => WithLp.toLp 2 fun i => (fderiv ℝ u x) (EuclideanSpace.single i 1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.smoothGradField then
    throwError "Refusing to shadow existing declaration DeGiorgi.smoothGradField"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.smoothGradField ``Submission.DeGiorgi.smoothGradField

omit [NeZero d] in
theorem norm_smoothGradField_eq_smoothGradNorm
    {u : E → ℝ} {x : E} :
    ‖smoothGradField u x‖ = smoothGradNorm u x := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.norm_smoothGradField_eq_smoothGradNorm then
    throwError "Refusing to shadow existing declaration DeGiorgi.norm_smoothGradField_eq_smoothGradNorm"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.norm_smoothGradField_eq_smoothGradNorm ``Submission.DeGiorgi.norm_smoothGradField_eq_smoothGradNorm

omit [NeZero d] in
theorem smoothGradField_zero :
    smoothGradField (fun _ : E => (0 : ℝ)) = 0 := by
  ext x i
  simp [smoothGradField]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.smoothGradField_zero then
    throwError "Refusing to shadow existing declaration DeGiorgi.smoothGradField_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.smoothGradField_zero ``Submission.DeGiorgi.smoothGradField_zero

omit [NeZero d] in
theorem smoothGradField_add
    {u v : E → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hv : ContDiff ℝ (⊤ : ℕ∞) v) :
    smoothGradField (fun x => u x + v x) =
      fun x => smoothGradField u x + smoothGradField v x := by
  ext x i
  have hu_diff : DifferentiableAt ℝ u x :=
    (hu.contDiffAt).differentiableAt (by norm_num)
  have hv_diff : DifferentiableAt ℝ v x :=
    (hv.contDiffAt).differentiableAt (by norm_num)
  change (fderiv ℝ (u + v) x) (EuclideanSpace.single i 1) = _
  exact
    congrArg (fun L : E →L[ℝ] ℝ => L (EuclideanSpace.single i 1))
      (fderiv_add hu_diff hv_diff)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.smoothGradField_add then
    throwError "Refusing to shadow existing declaration DeGiorgi.smoothGradField_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.smoothGradField_add ``Submission.DeGiorgi.smoothGradField_add

omit [NeZero d] in
theorem smoothGradField_smul
    (c : ℝ) {u : E → ℝ} :
    smoothGradField (fun x => c * u x) =
      fun x => c • smoothGradField u x := by
  ext x i
  have hfd : fderiv ℝ (fun y => c * u y) x = c • fderiv ℝ u x := by
    change fderiv ℝ (c • u) x = c • fderiv ℝ u x
    exact congrFun (fderiv_const_smul_field (𝕜 := ℝ) (f := u) c) x
  simpa [smoothGradField, PiLp.toLp_apply] using
    congrArg (fun L : E →L[ℝ] ℝ => L (EuclideanSpace.single i 1)) hfd

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.smoothGradField_smul then
    throwError "Refusing to shadow existing declaration DeGiorgi.smoothGradField_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.smoothGradField_smul ``Submission.DeGiorgi.smoothGradField_smul

/-- Canonical `W^{1,2}` witness on `Ω` carried by a smooth compactly supported
test function supported in `Ω`. -/
noncomputable def smoothTestWitness
    {Ω : Set E} (hΩ : IsOpen Ω) {u : E → ℝ}
    (hu : IsSmoothTestOn Ω u) :
    MemW1pWitness 2 u Ω where
  memLp := (hu.1.continuous.memLp_of_hasCompactSupport hu.2.1).restrict Ω
  weakGrad := smoothGradField u
  weakGrad_component_memLp := by
    intro i
    have hderiv_smooth : ContDiff ℝ (⊤ : ℕ∞)
        (fun x => (fderiv ℝ u x) (EuclideanSpace.single i 1)) :=
      (hu.1.fderiv_right (m := (⊤ : ℕ∞)) (by norm_cast)).clm_apply contDiff_const
    exact
      (hderiv_smooth.continuous.memLp_of_hasCompactSupport
        (hu.2.1.fderiv_apply (𝕜 := ℝ) _)).restrict Ω
  isWeakGrad := by
    intro i
    simpa [smoothGradField, PiLp.toLp_apply] using
      (HasWeakPartialDeriv.of_contDiff (Ω := Ω) (i := i) (f := u) hΩ
        (hu.1.of_le (by norm_cast)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.smoothTestWitness then
    throwError "Refusing to shadow existing declaration DeGiorgi.smoothTestWitness"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.smoothTestWitness ``Submission.DeGiorgi.smoothTestWitness

theorem smoothTest_memH01
    {Ω : Set E} (hΩ : IsOpen Ω) {u : E → ℝ}
    (hu : IsSmoothTestOn Ω u) :
    MemH01 u Ω :=
  memW01p_of_contDiff_hasCompactSupport_subset hΩ hu.1 hu.2.1 hu.2.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.smoothTest_memH01 then
    throwError "Refusing to shadow existing declaration DeGiorgi.smoothTest_memH01"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.smoothTest_memH01 ``Submission.DeGiorgi.smoothTest_memH01

/-- The `L²` gradient class carried by a Sobolev witness. -/
noncomputable def gradLpOfWitness
    {Ω : Set E} {u : E → ℝ} (hu : MemW1pWitness 2 u Ω) :
    MeasureTheory.Lp E 2 (volume.restrict Ω) :=
  hu.weakGrad_memLp.toLp hu.weakGrad

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.gradLpOfWitness then
    throwError "Refusing to shadow existing declaration DeGiorgi.gradLpOfWitness"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.gradLpOfWitness ``Submission.DeGiorgi.gradLpOfWitness

theorem norm_gradLpOfWitness_eq
    {Ω : Set E} {u : E → ℝ} (hu : MemW1pWitness 2 u Ω) :
    ‖gradLpOfWitness hu‖ =
      (∫ x, ‖hu.weakGrad x‖ ^ (2 : ℝ) ∂(volume.restrict Ω)) ^ (1 / (2 : ℝ)) := by
  let _ := (inferInstance : NeZero d)
  rw [gradLpOfWitness, Lp.norm_toLp]
  rw [MeasureTheory.toReal_eLpNorm hu.weakGrad_memLp.aestronglyMeasurable]
  simpa using
    (MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal
      (μ := volume.restrict Ω) (f := hu.weakGrad) (p := (2 : ENNReal))
      (by norm_num) (by simp) hu.weakGrad_memLp.aestronglyMeasurable)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.norm_gradLpOfWitness_eq then
    throwError "Refusing to shadow existing declaration DeGiorgi.norm_gradLpOfWitness_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.norm_gradLpOfWitness_eq ``Submission.DeGiorgi.norm_gradLpOfWitness_eq

/-- The `L²` class carried by a smooth test function on `Ω`. -/
noncomputable def smoothFunToLp
    {Ω : Set E} (hΩ : IsOpen Ω) {u : E → ℝ}
    (hu : IsSmoothTestOn Ω u) :
    MeasureTheory.Lp ℝ 2 (volume.restrict Ω) :=
  (smoothTestWitness hΩ hu).memLp.toLp u

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.smoothFunToLp then
    throwError "Refusing to shadow existing declaration DeGiorgi.smoothFunToLp"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.smoothFunToLp ``Submission.DeGiorgi.smoothFunToLp

theorem smoothFunToLp_zero
    {Ω : Set E} (hΩ : IsOpen Ω) :
    smoothFunToLp hΩ IsSmoothTestOn.zero = 0 := by
  let _ := (inferInstance : NeZero d)
  let hu0 := smoothTestWitness hΩ IsSmoothTestOn.zero
  let hu0Lp := hu0.memLp
  change hu0Lp.toLp (0 : E → ℝ) = 0
  exact hu0Lp.toLp_zero

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.smoothFunToLp_zero then
    throwError "Refusing to shadow existing declaration DeGiorgi.smoothFunToLp_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.smoothFunToLp_zero ``Submission.DeGiorgi.smoothFunToLp_zero

theorem smoothFunToLp_add
    {Ω : Set E} (hΩ : IsOpen Ω) {u v : E → ℝ}
    (hu : IsSmoothTestOn Ω u) (hv : IsSmoothTestOn Ω v) :
    smoothFunToLp hΩ (hu.add hv) = smoothFunToLp hΩ hu + smoothFunToLp hΩ hv := by
  let _ := (inferInstance : NeZero d)
  let huLp := (smoothTestWitness hΩ hu).memLp
  let hvLp := (smoothTestWitness hΩ hv).memLp
  let huvLp := (smoothTestWitness hΩ (hu.add hv)).memLp
  change huvLp.toLp (fun x => u x + v x) = huLp.toLp u + hvLp.toLp v
  calc
    huvLp.toLp (fun x ↦ u x + v x) =
        (huLp.add hvLp).toLp (u + v) :=
      MemLp.toLp_congr huvLp (huLp.add hvLp)
        (Filter.Eventually.of_forall fun _ ↦ rfl)
    _ = huLp.toLp u + hvLp.toLp v := MemLp.toLp_add huLp hvLp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.smoothFunToLp_add then
    throwError "Refusing to shadow existing declaration DeGiorgi.smoothFunToLp_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.smoothFunToLp_add ``Submission.DeGiorgi.smoothFunToLp_add

theorem smoothFunToLp_smul
    {Ω : Set E} (hΩ : IsOpen Ω) (c : ℝ) {u : E → ℝ}
    (hu : IsSmoothTestOn Ω u) :
    smoothFunToLp hΩ (hu.smul c) = c • smoothFunToLp hΩ hu := by
  let _ := (inferInstance : NeZero d)
  let huLp := (smoothTestWitness hΩ hu).memLp
  let hcuLp := (smoothTestWitness hΩ (hu.smul c)).memLp
  change hcuLp.toLp (fun x => c * u x) = c • huLp.toLp u
  calc
    hcuLp.toLp (fun x ↦ c * u x) =
        (huLp.const_smul c).toLp (c • u) :=
      MemLp.toLp_congr hcuLp (huLp.const_smul c)
        (Filter.Eventually.of_forall fun _ ↦ rfl)
    _ = c • huLp.toLp u := MemLp.toLp_const_smul c huLp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.smoothFunToLp_smul then
    throwError "Refusing to shadow existing declaration DeGiorgi.smoothFunToLp_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.smoothFunToLp_smul ``Submission.DeGiorgi.smoothFunToLp_smul

theorem smoothFunToLp_sub
    {Ω : Set E} (hΩ : IsOpen Ω) {u v : E → ℝ}
    (hu : IsSmoothTestOn Ω u) (hv : IsSmoothTestOn Ω v) :
    smoothFunToLp hΩ (hu.sub hv) = smoothFunToLp hΩ hu - smoothFunToLp hΩ hv := by
  let _ := (inferInstance : NeZero d)
  let huLp := (smoothTestWitness hΩ hu).memLp
  let hvLp := (smoothTestWitness hΩ hv).memLp
  let huvLp := (smoothTestWitness hΩ (hu.sub hv)).memLp
  change huvLp.toLp (fun x ↦ u x - v x) = huLp.toLp u - hvLp.toLp v
  calc
    huvLp.toLp (fun x ↦ u x - v x) =
        (huLp.sub hvLp).toLp (u - v) :=
      MemLp.toLp_congr huvLp (huLp.sub hvLp)
        (Filter.Eventually.of_forall fun _ ↦ rfl)
    _ = huLp.toLp u - hvLp.toLp v := MemLp.toLp_sub huLp hvLp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.smoothFunToLp_sub then
    throwError "Refusing to shadow existing declaration DeGiorgi.smoothFunToLp_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.smoothFunToLp_sub ``Submission.DeGiorgi.smoothFunToLp_sub

/-- Norm of the `L²` class carried by a smooth test function. -/
theorem norm_smoothFunToLp_eq
    {Ω : Set E} (hΩ : IsOpen Ω) {u : E → ℝ}
    (hu : IsSmoothTestOn Ω u) :
    ‖smoothFunToLp hΩ hu‖ =
      (∫ x, ‖u x‖ ^ (2 : ℝ) ∂(volume.restrict Ω)) ^ (1 / (2 : ℝ)) := by
  let _ := (inferInstance : NeZero d)
  rw [smoothFunToLp, Lp.norm_toLp]
  rw [MeasureTheory.toReal_eLpNorm (smoothTestWitness hΩ hu).memLp.aestronglyMeasurable]
  simpa using
    (MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal
      (μ := volume.restrict Ω) (f := u) (p := (2 : ENNReal))
      (by norm_num) (by simp) (smoothTestWitness hΩ hu).memLp.aestronglyMeasurable)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.norm_smoothFunToLp_eq then
    throwError "Refusing to shadow existing declaration DeGiorgi.norm_smoothFunToLp_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.norm_smoothFunToLp_eq ``Submission.DeGiorgi.norm_smoothFunToLp_eq

/-- The `L²` gradient class carried by a smooth test function on `Ω`. -/
noncomputable def smoothGradToLp
    {Ω : Set E} (hΩ : IsOpen Ω) {u : E → ℝ}
    (hu : IsSmoothTestOn Ω u) :
    MeasureTheory.Lp E 2 (volume.restrict Ω) :=
  gradLpOfWitness (smoothTestWitness hΩ hu)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.smoothGradToLp then
    throwError "Refusing to shadow existing declaration DeGiorgi.smoothGradToLp"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.smoothGradToLp ``Submission.DeGiorgi.smoothGradToLp

theorem smoothGradToLp_zero
    {Ω : Set E} (hΩ : IsOpen Ω) :
    smoothGradToLp hΩ IsSmoothTestOn.zero = 0 := by
  let _ := (inferInstance : NeZero d)
  let hw0 := smoothTestWitness hΩ IsSmoothTestOn.zero
  let hzeroLp : _root_.MeasureTheory.MemLp (0 : E → E) 2 (volume.restrict Ω) :=
    MeasureTheory.MemLp.zero'
  have hcongr :
      hw0.weakGrad_memLp.toLp hw0.weakGrad = hzeroLp.toLp (0 : E → E) :=
    MemLp.toLp_congr hw0.weakGrad_memLp hzeroLp <|
      Filter.Eventually.of_forall fun x => by
        simpa [hw0, smoothTestWitness] using congrFun smoothGradField_zero x
  change hw0.weakGrad_memLp.toLp hw0.weakGrad = 0
  rw [hcongr]
  exact hzeroLp.toLp_zero

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.smoothGradToLp_zero then
    throwError "Refusing to shadow existing declaration DeGiorgi.smoothGradToLp_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.smoothGradToLp_zero ``Submission.DeGiorgi.smoothGradToLp_zero

theorem smoothGradToLp_add
    {Ω : Set E} (hΩ : IsOpen Ω) {u v : E → ℝ}
    (hu : IsSmoothTestOn Ω u) (hv : IsSmoothTestOn Ω v) :
    smoothGradToLp hΩ (hu.add hv) = smoothGradToLp hΩ hu + smoothGradToLp hΩ hv := by
  let _ := (inferInstance : NeZero d)
  let hgu := (smoothTestWitness hΩ hu).weakGrad_memLp
  let hgv := (smoothTestWitness hΩ hv).weakGrad_memLp
  let hguv := (smoothTestWitness hΩ (hu.add hv)).weakGrad_memLp
  have hcongr :
      hguv.toLp (smoothGradField (fun x => u x + v x)) =
        (hgu.add hgv).toLp (fun x => smoothGradField u x + smoothGradField v x) :=
    MemLp.toLp_congr hguv (hgu.add hgv) <|
      Filter.Eventually.of_forall fun x => by
        change smoothGradField (fun y ↦ u y + v y) x =
          smoothGradField u x + smoothGradField v x
        exact congrFun (smoothGradField_add hu.1 hv.1) x
  change hguv.toLp (smoothGradField (fun x => u x + v x)) =
      hgu.toLp (smoothGradField u) + hgv.toLp (smoothGradField v)
  rw [hcongr]
  exact MemLp.toLp_add hgu hgv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.smoothGradToLp_add then
    throwError "Refusing to shadow existing declaration DeGiorgi.smoothGradToLp_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.smoothGradToLp_add ``Submission.DeGiorgi.smoothGradToLp_add

theorem smoothGradToLp_smul
    {Ω : Set E} (hΩ : IsOpen Ω) (c : ℝ) {u : E → ℝ}
    (hu : IsSmoothTestOn Ω u) :
    smoothGradToLp hΩ (hu.smul c) = c • smoothGradToLp hΩ hu := by
  let _ := (inferInstance : NeZero d)
  let hgu := (smoothTestWitness hΩ hu).weakGrad_memLp
  let hgcu := (smoothTestWitness hΩ (hu.smul c)).weakGrad_memLp
  have hcongr :
      hgcu.toLp (smoothGradField (fun x => c * u x)) =
        (hgu.const_smul c).toLp (c • fun x => smoothGradField u x) :=
    MemLp.toLp_congr hgcu (hgu.const_smul c) <|
      Filter.Eventually.of_forall fun x => by
        change smoothGradField (fun y ↦ c * u y) x = c • smoothGradField u x
        exact congrFun (smoothGradField_smul c (u := u)) x
  change hgcu.toLp (smoothGradField (fun x => c * u x)) = c • hgu.toLp (smoothGradField u)
  rw [hcongr]
  exact MemLp.toLp_const_smul c hgu

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.smoothGradToLp_smul then
    throwError "Refusing to shadow existing declaration DeGiorgi.smoothGradToLp_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.smoothGradToLp_smul ``Submission.DeGiorgi.smoothGradToLp_smul

theorem smoothGradToLp_sub
    {Ω : Set E} (hΩ : IsOpen Ω) {u v : E → ℝ}
    (hu : IsSmoothTestOn Ω u) (hv : IsSmoothTestOn Ω v) :
    smoothGradToLp hΩ (hu.sub hv) = smoothGradToLp hΩ hu - smoothGradToLp hΩ hv := by
  calc
    smoothGradToLp hΩ (hu.sub hv)
        = smoothGradToLp hΩ hu + smoothGradToLp hΩ (hv.smul (-1)) := by
            simpa [IsSmoothTestOn.sub] using smoothGradToLp_add hΩ hu (hv.smul (-1))
    _ = smoothGradToLp hΩ hu - smoothGradToLp hΩ hv := by
          rw [smoothGradToLp_smul hΩ (-1) hv]
          simp [sub_eq_add_neg]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.smoothGradToLp_sub then
    throwError "Refusing to shadow existing declaration DeGiorgi.smoothGradToLp_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.smoothGradToLp_sub ``Submission.DeGiorgi.smoothGradToLp_sub

/-- Norm of the `L²` gradient class carried by a smooth test function. -/
theorem norm_smoothGradToLp_eq
    {Ω : Set E} (hΩ : IsOpen Ω) {u : E → ℝ}
    (hu : IsSmoothTestOn Ω u) :
    ‖smoothGradToLp hΩ hu‖ =
      (∫ x, ‖smoothGradField u x‖ ^ (2 : ℝ) ∂(volume.restrict Ω)) ^ (1 / (2 : ℝ)) := by
  change ‖gradLpOfWitness (smoothTestWitness hΩ hu)‖ =
    (∫ x, ‖(smoothTestWitness hΩ hu).weakGrad x‖ ^ (2 : ℝ)
      ∂(volume.restrict Ω)) ^ (1 / (2 : ℝ))
  exact norm_gradLpOfWitness_eq (smoothTestWitness hΩ hu)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.norm_smoothGradToLp_eq then
    throwError "Refusing to shadow existing declaration DeGiorgi.norm_smoothGradToLp_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.norm_smoothGradToLp_eq ``Submission.DeGiorgi.norm_smoothGradToLp_eq

end DeGiorgi
