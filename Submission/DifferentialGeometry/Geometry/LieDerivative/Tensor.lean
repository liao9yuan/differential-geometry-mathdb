/-
Author: Yuan Liao
Coauthor: Ayush Khaitan, Jack McCarthy
-/
import Submission.DifferentialGeometry.Tensor.RSTensor.Defs
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorField.Pullback
import Submission.DifferentialGeometry.Tensor.RSTensor.Coordinates.Field

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry
namespace TensorLieDeriv

noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.IsManifold _root_.ContinuousLinearMap _root_.Submission.ContinuousLinearMap _root_.Bundle.ContinuousLinearMap _root_.VectorField _root_.Filter
    DifferentialGeometry.Tensor0SBundle Function
open scoped _root_.Manifold _root_.Topology _root_.Bundle _root_.Submission.Bundle _root_.ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable (n : WithTop ℕ∞ := ⊤) [IsManifold I n M]
variable {x x₀ : M} {s : Set M}

section VectorSpaceLieDeriv

variable {s : ℕ}

noncomputable def fderivTensor0S (α : E → Tensor0SModel (𝕜 := 𝕜) (E := E) s)
    (x : E) : E →L[𝕜] Tensor0SModel (𝕜 := 𝕜) (E := E) s :=
  fderiv 𝕜 α x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.TensorLieDeriv.fderivTensor0S then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.TensorLieDeriv.fderivTensor0S"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.TensorLieDeriv.fderivTensor0S ``Submission.DifferentialGeometry.TensorLieDeriv.fderivTensor0S

noncomputable def vectorFieldActionOnTensor0S
    (X : E → E) (α : E → Tensor0SModel (𝕜 := 𝕜) (E := E) s) (x : E) :
    Tensor0SModel (𝕜 := 𝕜) (E := E) s :=
  fderivTensor0S α x (X x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.TensorLieDeriv.vectorFieldActionOnTensor0S then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.TensorLieDeriv.vectorFieldActionOnTensor0S"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.TensorLieDeriv.vectorFieldActionOnTensor0S ``Submission.DifferentialGeometry.TensorLieDeriv.vectorFieldActionOnTensor0S

noncomputable def substituteArg (s : ℕ) (i : Fin s)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) s)
    (f : E →L[𝕜] E) :
    Tensor0SModel (𝕜 := 𝕜) (E := E) s :=
  α.compContinuousLinearMap (fun j => if j = i then f else ContinuousLinearMap.id 𝕜 E)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.TensorLieDeriv.substituteArg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.TensorLieDeriv.substituteArg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.TensorLieDeriv.substituteArg ``Submission.DifferentialGeometry.TensorLieDeriv.substituteArg

noncomputable def lieDerivCorrection (s : ℕ)
    (DX : E →L[𝕜] E) (α : Tensor0SModel (𝕜 := 𝕜) (E := E) s) :
    Tensor0SModel (𝕜 := 𝕜) (E := E) s :=
  ∑ i : Fin s, substituteArg s i α DX

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.TensorLieDeriv.lieDerivCorrection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.TensorLieDeriv.lieDerivCorrection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.TensorLieDeriv.lieDerivCorrection ``Submission.DifferentialGeometry.TensorLieDeriv.lieDerivCorrection

noncomputable def lieDerivTensor0S (s : ℕ)
    (X : E → E) (α : E → Tensor0SModel (𝕜 := 𝕜) (E := E) s) (x : E) :
    Tensor0SModel (𝕜 := 𝕜) (E := E) s :=
  vectorFieldActionOnTensor0S X α x - lieDerivCorrection s (fderiv 𝕜 X x) (α x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.TensorLieDeriv.lieDerivTensor0S then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.TensorLieDeriv.lieDerivTensor0S"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.TensorLieDeriv.lieDerivTensor0S ``Submission.DifferentialGeometry.TensorLieDeriv.lieDerivTensor0S

noncomputable def lieDerivTensor0SWithin (s : ℕ)
    (X : E → E) (α : E → Tensor0SModel (𝕜 := 𝕜) (E := E) s) (t : Set E) (x : E) :
    Tensor0SModel (𝕜 := 𝕜) (E := E) s :=
  fderivWithin 𝕜 α t x (X x) - lieDerivCorrection s (fderivWithin 𝕜 X t x) (α x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.TensorLieDeriv.lieDerivTensor0SWithin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.TensorLieDeriv.lieDerivTensor0SWithin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.TensorLieDeriv.lieDerivTensor0SWithin ``Submission.DifferentialGeometry.TensorLieDeriv.lieDerivTensor0SWithin

end VectorSpaceLieDeriv

section ManifoldLieDeriv

variable {s : ℕ}

abbrev Tensor0SBundle (s : ℕ) (I : ModelWithCorners 𝕜 E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] :=
  TotalSpace (Tensor0SModel (𝕜 := 𝕜) (E := E) s) (fun x : M => Tensor0SSpace s I x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.TensorLieDeriv.Tensor0SBundle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.TensorLieDeriv.Tensor0SBundle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.TensorLieDeriv.Tensor0SBundle ``Submission.DifferentialGeometry.TensorLieDeriv.Tensor0SBundle

noncomputable def mpullbackTensor0S
    {H' : Type*} [TopologicalSpace H'] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {I' : ModelWithCorners 𝕜 E' H'}
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I 1 M]
    (f : M → M')
    (α : (x : M') → ContinuousMultilinearMap 𝕜 (fun _ : Fin s => TangentSpace I' x) 𝕜)
    (x : M) :
    Tensor0SSpace s I x :=
  (α (f x)).compContinuousLinearMap
    (fun _ => (mfderiv I I' f x).comp
      (ContinuousLinearMap.id 𝕜 (TangentSpace I x)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.TensorLieDeriv.mpullbackTensor0S then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.TensorLieDeriv.mpullbackTensor0S"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.TensorLieDeriv.mpullbackTensor0S ``Submission.DifferentialGeometry.TensorLieDeriv.mpullbackTensor0S

noncomputable def mpullbackWithinTensor0S
    {H' : Type*} [TopologicalSpace H'] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {I' : ModelWithCorners 𝕜 E' H'}
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I 1 M]
    (f : M → M') (t : Set M)
    (α : (x : M') → ContinuousMultilinearMap 𝕜 (fun _ : Fin s => TangentSpace I' x) 𝕜)
    (x : M) :
    Tensor0SSpace s I x :=
  (α (f x)).compContinuousLinearMap
    (fun _ => (mfderivWithin I I' f t x).comp
      (ContinuousLinearMap.id 𝕜 (TangentSpace I x)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.TensorLieDeriv.mpullbackWithinTensor0S then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.TensorLieDeriv.mpullbackWithinTensor0S"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.TensorLieDeriv.mpullbackWithinTensor0S ``Submission.DifferentialGeometry.TensorLieDeriv.mpullbackWithinTensor0S

section SmoothVectorFieldLieDeriv

variable [IsManifold I 1 M]

noncomputable def mlieDerivTensor0SWithin (s : ℕ)
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (α : (x : M) → Tensor0SSpace s I x)
    (t : Set M)
    (x₀ : M) :
    Tensor0SSpace s I x₀ := by
  let X' := _root_.VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm X (_root_.Set.range I)
  let α' : E → Tensor0SModel (𝕜 := 𝕜) (E := E) s := fun y =>
    α ((extChartAt I x₀).symm y)
  let result := lieDerivTensor0SWithin s X' α'
    ((extChartAt I x₀).symm ⁻¹' t ∩ _root_.Set.range I)
    (extChartAt I x₀ x₀)
  exact result

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.TensorLieDeriv.mlieDerivTensor0SWithin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.TensorLieDeriv.mlieDerivTensor0SWithin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.TensorLieDeriv.mlieDerivTensor0SWithin ``Submission.DifferentialGeometry.TensorLieDeriv.mlieDerivTensor0SWithin

noncomputable def mlieDerivTensor0S (s : ℕ)
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (α : (x : M) → Tensor0SSpace s I x)
    (x₀ : M) :
    Tensor0SSpace s I x₀ :=
  mlieDerivTensor0SWithin (n := n) s X α _root_.Set.univ x₀

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.TensorLieDeriv.mlieDerivTensor0S then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.TensorLieDeriv.mlieDerivTensor0S"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.TensorLieDeriv.mlieDerivTensor0S ``Submission.DifferentialGeometry.TensorLieDeriv.mlieDerivTensor0S

variable {s : ℕ}
variable {X : ContMDiffSection I E n (TangentSpace I : M → Type _)}
variable {α β : (x : M) → Tensor0SSpace s I x}

omit [IsManifold I n M] in
@[simp] lemma mlieDeriv_tensor0SWithin_univ :
    mlieDerivTensor0SWithin (I := I) (n := n) s X α _root_.Set.univ = mlieDerivTensor0S (n := n) s X α := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.TensorLieDeriv.mlieDeriv_tensor0SWithin_univ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.TensorLieDeriv.mlieDeriv_tensor0SWithin_univ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.TensorLieDeriv.mlieDeriv_tensor0SWithin_univ ``Submission.DifferentialGeometry.TensorLieDeriv.mlieDeriv_tensor0SWithin_univ

end SmoothVectorFieldLieDeriv

lemma lieDeriv_correction_add (DX : E →L[𝕜] E)
    (α β : Tensor0SModel (𝕜 := 𝕜) (E := E) s) :
    lieDerivCorrection s DX (α + β) =
    lieDerivCorrection s DX α + lieDerivCorrection s DX β := by
  unfold lieDerivCorrection
  rw [← Finset.sum_add_distrib]
  congr 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.TensorLieDeriv.lieDeriv_correction_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.TensorLieDeriv.lieDeriv_correction_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.TensorLieDeriv.lieDeriv_correction_add ``Submission.DifferentialGeometry.TensorLieDeriv.lieDeriv_correction_add

lemma lieDeriv_correction_smul (DX : E →L[𝕜] E) (c : 𝕜)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) s) :
    lieDerivCorrection s DX (c • α) = c • lieDerivCorrection s DX α := by
  unfold lieDerivCorrection
  rw [Finset.smul_sum]
  congr 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.TensorLieDeriv.lieDeriv_correction_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.TensorLieDeriv.lieDeriv_correction_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.TensorLieDeriv.lieDeriv_correction_smul ``Submission.DifferentialGeometry.TensorLieDeriv.lieDeriv_correction_smul

lemma substituteArg_add_right (i : Fin s)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) s) (DX DY : E →L[𝕜] E) :
    substituteArg s i α (DX + DY) = substituteArg s i α DX + substituteArg s i α DY := by
  ext v
  simp only [substituteArg, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    add_apply]
  convert α.map_update_add (fun j => v j) i (DX (v i)) (DY (v i))
  all_goals
    rename_i j
    by_cases hji : j = i
    · subst j
      simp
    · simp [hji]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.TensorLieDeriv.substituteArg_add_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.TensorLieDeriv.substituteArg_add_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.TensorLieDeriv.substituteArg_add_right ``Submission.DifferentialGeometry.TensorLieDeriv.substituteArg_add_right

lemma substituteArg_smul_right (i : Fin s)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) s) (c : 𝕜) (DX : E →L[𝕜] E) :
    substituteArg s i α (c • DX) = c • substituteArg s i α DX := by
  ext v
  simp only [substituteArg, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    smul_apply]
  convert α.map_update_smul (fun j => v j) i c (DX (v i))
  all_goals
    rename_i j
    by_cases hji : j = i
    · subst j
      simp
    · simp [hji]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.TensorLieDeriv.substituteArg_smul_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.TensorLieDeriv.substituteArg_smul_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.TensorLieDeriv.substituteArg_smul_right ``Submission.DifferentialGeometry.TensorLieDeriv.substituteArg_smul_right

lemma lieDeriv_correction_add_right (α : Tensor0SModel (𝕜 := 𝕜) (E := E) s)
    (DX DY : E →L[𝕜] E) :
    lieDerivCorrection s (DX + DY) α =
      lieDerivCorrection s DX α + lieDerivCorrection s DY α := by
  unfold lieDerivCorrection
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact substituteArg_add_right (s := s) i α DX DY

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.TensorLieDeriv.lieDeriv_correction_add_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.TensorLieDeriv.lieDeriv_correction_add_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.TensorLieDeriv.lieDeriv_correction_add_right ``Submission.DifferentialGeometry.TensorLieDeriv.lieDeriv_correction_add_right

lemma lieDeriv_correction_smul_right (α : Tensor0SModel (𝕜 := 𝕜) (E := E) s)
    (c : 𝕜) (DX : E →L[𝕜] E) :
    lieDerivCorrection s (c • DX) α = c • lieDerivCorrection s DX α := by
  unfold lieDerivCorrection
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact substituteArg_smul_right (s := s) i α c DX

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.TensorLieDeriv.lieDeriv_correction_smul_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.TensorLieDeriv.lieDeriv_correction_smul_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.TensorLieDeriv.lieDeriv_correction_smul_right ``Submission.DifferentialGeometry.TensorLieDeriv.lieDeriv_correction_smul_right

lemma lieDeriv_correction_zero (DX : E →L[𝕜] E)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) 0) :
    lieDerivCorrection 0 DX α = 0 := by
  dsimp[lieDerivCorrection]
  simp only [Finset.univ_eq_empty, Finset.sum_empty]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.TensorLieDeriv.lieDeriv_correction_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.TensorLieDeriv.lieDeriv_correction_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.TensorLieDeriv.lieDeriv_correction_zero ``Submission.DifferentialGeometry.TensorLieDeriv.lieDeriv_correction_zero

lemma lieDeriv_correction_modelProduct (s q : ℕ) (DX : E →L[𝕜] E)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) s)
    (β : Tensor0SModel (𝕜 := 𝕜) (E := E) q) :
    lieDerivCorrection (s + q) DX
        (Bundle.continuousMultilinearMap.modelProduct s q α β) =
      Bundle.continuousMultilinearMap.modelProduct s q
          (lieDerivCorrection s DX α) β +
        Bundle.continuousMultilinearMap.modelProduct s q
          α (lieDerivCorrection q DX β) := by
  ext v
  rw [lieDerivCorrection, Fin.sum_univ_add]
  simp only [lieDerivCorrection, sum_apply,
    add_apply, Bundle.continuousMultilinearMap.modelProduct_apply]
  congr 1
  · rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    simp only [substituteArg, ContinuousMultilinearMap.compContinuousLinearMap_apply,
      Bundle.continuousMultilinearMap.modelProduct_apply, Function.comp_apply]
    congr 1
    · congr 1
      funext j
      by_cases hji : j = i
      · subst j
        simp
      · simp [hji]
    · congr 1
      funext j
      have hneq : Fin.natAdd s j ≠ Fin.castAdd q i := by
        intro h
        have hval := congrArg Fin.val h
        simp [Fin.val_natAdd, Fin.val_castAdd] at hval
        omega
      simp [hneq]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [substituteArg, ContinuousMultilinearMap.compContinuousLinearMap_apply,
      Bundle.continuousMultilinearMap.modelProduct_apply, Function.comp_apply]
    congr 1
    · congr 1
      funext j
      have hneq : Fin.castAdd q j ≠ Fin.natAdd s i := by
        intro h
        have hval := congrArg Fin.val h
        simp [Fin.val_natAdd, Fin.val_castAdd] at hval
        omega
      simp [hneq]
    · congr 1
      funext j
      by_cases hji : j = i
      · subst j
        simp
      · simp [hji]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.TensorLieDeriv.lieDeriv_correction_modelProduct then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.TensorLieDeriv.lieDeriv_correction_modelProduct"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.TensorLieDeriv.lieDeriv_correction_modelProduct ``Submission.DifferentialGeometry.TensorLieDeriv.lieDeriv_correction_modelProduct

variable [CompleteSpace 𝕜]

noncomputable def lieDerivCorrectionL (s : ℕ) (DX : E →L[𝕜] E) :
    Tensor0SModel (𝕜 := 𝕜) (E := E) s →L[𝕜]
      Tensor0SModel (𝕜 := 𝕜) (E := E) s :=
  LinearMap.toContinuousLinearMap
    { toFun := fun α => lieDerivCorrection s DX α
      map_add' := fun α β => lieDeriv_correction_add (s := s) DX α β
      map_smul' := fun c α => lieDeriv_correction_smul (s := s) DX c α }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.TensorLieDeriv.lieDerivCorrectionL then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.TensorLieDeriv.lieDerivCorrectionL"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.TensorLieDeriv.lieDerivCorrectionL ``Submission.DifferentialGeometry.TensorLieDeriv.lieDerivCorrectionL

@[simp]
theorem lieDeriv_correctionL_apply (DX : E →L[𝕜] E)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) s) :
    lieDerivCorrectionL (𝕜 := 𝕜) (E := E) s DX α = lieDerivCorrection s DX α := by
  simp [lieDerivCorrectionL]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.TensorLieDeriv.lieDeriv_correctionL_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.TensorLieDeriv.lieDeriv_correctionL_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.TensorLieDeriv.lieDeriv_correctionL_apply ``Submission.DifferentialGeometry.TensorLieDeriv.lieDeriv_correctionL_apply

noncomputable def lieDerivCorrectionOpL (s : ℕ) :
    (E →L[𝕜] E) →L[𝕜]
      (Tensor0SModel (𝕜 := 𝕜) (E := E) s →L[𝕜]
        Tensor0SModel (𝕜 := 𝕜) (E := E) s) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun DX => lieDerivCorrectionL (𝕜 := 𝕜) (E := E) s DX
      map_add' := fun DX DY => by
        ext α
        simp [lieDeriv_correction_add_right]
      map_smul' := fun c DX => by
        ext α
        simp [lieDeriv_correction_smul_right] }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.TensorLieDeriv.lieDerivCorrectionOpL then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.TensorLieDeriv.lieDerivCorrectionOpL"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.TensorLieDeriv.lieDerivCorrectionOpL ``Submission.DifferentialGeometry.TensorLieDeriv.lieDerivCorrectionOpL

@[simp]
theorem lieDeriv_correctionOpL_apply (DX : E →L[𝕜] E) :
    lieDerivCorrectionOpL (𝕜 := 𝕜) (E := E) s DX =
      lieDerivCorrectionL (𝕜 := 𝕜) (E := E) s DX := by
  simp [lieDerivCorrectionOpL]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.TensorLieDeriv.lieDeriv_correctionOpL_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.TensorLieDeriv.lieDeriv_correctionOpL_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.TensorLieDeriv.lieDeriv_correctionOpL_apply ``Submission.DifferentialGeometry.TensorLieDeriv.lieDeriv_correctionOpL_apply

noncomputable def directionalDerivTensorRSWithin (r s : ℕ)
    (X : E → E)
    (T : E → Tensor0SModel (𝕜 := 𝕜) (E := E) r →L[𝕜] Tensor0SModel (𝕜 := 𝕜) (E := E) s)
    (t : Set E) (x : E) :
    Tensor0SModel (𝕜 := 𝕜) (E := E) r →L[𝕜] Tensor0SModel (𝕜 := 𝕜) (E := E) s :=
  fderivWithin 𝕜 T t x (X x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.TensorLieDeriv.directionalDerivTensorRSWithin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.TensorLieDeriv.directionalDerivTensorRSWithin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.TensorLieDeriv.directionalDerivTensorRSWithin ``Submission.DifferentialGeometry.TensorLieDeriv.directionalDerivTensorRSWithin

noncomputable def directionalDerivTensorRS (r s : ℕ)
    (X : E → E)
    (T : E → Tensor0SModel (𝕜 := 𝕜) (E := E) r →L[𝕜] Tensor0SModel (𝕜 := 𝕜) (E := E) s)
    (x : E) :
    Tensor0SModel (𝕜 := 𝕜) (E := E) r →L[𝕜] Tensor0SModel (𝕜 := 𝕜) (E := E) s :=
  fderiv 𝕜 T x (X x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.TensorLieDeriv.directionalDerivTensorRS then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.TensorLieDeriv.directionalDerivTensorRS"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.TensorLieDeriv.directionalDerivTensorRS ``Submission.DifferentialGeometry.TensorLieDeriv.directionalDerivTensorRS

noncomputable def lieDerivTensorRSWithin (r s : ℕ)
    (X : E → E)
    (T : E → Tensor0SModel (𝕜 := 𝕜) (E := E) r →L[𝕜] Tensor0SModel (𝕜 := 𝕜) (E := E) s)
    (t : Set E) (x : E) :
    Tensor0SModel (𝕜 := 𝕜) (E := E) r →L[𝕜] Tensor0SModel (𝕜 := 𝕜) (E := E) s :=
  let DX := fderivWithin 𝕜 X t x
  fderivWithin 𝕜 T t x (X x)
    - (lieDerivCorrectionL (𝕜 := 𝕜) (E := E) s DX).comp (T x)
    + (T x).comp (lieDerivCorrectionL (𝕜 := 𝕜) (E := E) r DX)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.TensorLieDeriv.lieDerivTensorRSWithin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.TensorLieDeriv.lieDerivTensorRSWithin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.TensorLieDeriv.lieDerivTensorRSWithin ``Submission.DifferentialGeometry.TensorLieDeriv.lieDerivTensorRSWithin

noncomputable def lieDerivTensorRS (r s : ℕ)
    (X : E → E)
    (T : E → Tensor0SModel (𝕜 := 𝕜) (E := E) r →L[𝕜] Tensor0SModel (𝕜 := 𝕜) (E := E) s)
    (x : E) :
    Tensor0SModel (𝕜 := 𝕜) (E := E) r →L[𝕜] Tensor0SModel (𝕜 := 𝕜) (E := E) s :=
  let DX := fderiv 𝕜 X x
  fderiv 𝕜 T x (X x)
    - (lieDerivCorrectionL (𝕜 := 𝕜) (E := E) s DX).comp (T x)
    + (T x).comp (lieDerivCorrectionL (𝕜 := 𝕜) (E := E) r DX)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.TensorLieDeriv.lieDerivTensorRS then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.TensorLieDeriv.lieDerivTensorRS"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.TensorLieDeriv.lieDerivTensorRS ``Submission.DifferentialGeometry.TensorLieDeriv.lieDerivTensorRS

omit [CompleteSpace 𝕜] in
theorem contDiffWithinAt_directionalDeriv_tensorRSWithin (r s : ℕ) {m n' : WithTop ℕ∞}
    {X : E → E}
    {T : E → Tensor0SModel (𝕜 := 𝕜) (E := E) r →L[𝕜] Tensor0SModel (𝕜 := 𝕜) (E := E) s}
    {u : Set E} {x : E}
    (hT : ContDiffWithinAt 𝕜 n' T u x)
    (hX : ContDiffWithinAt 𝕜 m X u x)
    (hu : UniqueDiffOn 𝕜 u) (hmn : m + 1 ≤ n') (hx : x ∈ u) :
    ContDiffWithinAt 𝕜 m (fun y => directionalDerivTensorRSWithin r s X T u y) u x := by
  simpa [directionalDerivTensorRSWithin] using hT.fderivWithin_right_apply hX hu hmn hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.TensorLieDeriv.contDiffWithinAt_directionalDeriv_tensorRSWithin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.TensorLieDeriv.contDiffWithinAt_directionalDeriv_tensorRSWithin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.TensorLieDeriv.contDiffWithinAt_directionalDeriv_tensorRSWithin ``Submission.DifferentialGeometry.TensorLieDeriv.contDiffWithinAt_directionalDeriv_tensorRSWithin

theorem contDiffWithinAt_lieDeriv_tensorRSWithin (r s : ℕ) {m n' : WithTop ℕ∞}
    {X : E → E}
    {T : E → Tensor0SModel (𝕜 := 𝕜) (E := E) r →L[𝕜] Tensor0SModel (𝕜 := 𝕜) (E := E) s}
    {u : Set E} {x : E}
    (hT : ContDiffWithinAt 𝕜 n' T u x)
    (hX : ContDiffWithinAt 𝕜 n' X u x)
    (hu : UniqueDiffOn 𝕜 u) (hmn : m + 1 ≤ n') (hx : x ∈ u) :
    ContDiffWithinAt 𝕜 m (fun y => lieDerivTensorRSWithin r s X T u y) u x := by
  have hprincipal :
      ContDiffWithinAt 𝕜 m (fun y => directionalDerivTensorRSWithin r s X T u y) u x :=
    contDiffWithinAt_directionalDeriv_tensorRSWithin r s hT
      (hX.of_le (le_trans le_self_add hmn)) hu hmn hx
  have hT_m : ContDiffWithinAt 𝕜 m T u x :=
    hT.of_le (le_trans le_self_add hmn)
  have hDX : ContDiffWithinAt 𝕜 m (fun y => fderivWithin 𝕜 X u y) u x :=
    hX.fderivWithin_right hu hmn hx
  have hCorrectionS :
      ContDiffWithinAt 𝕜 m
        (fun y => lieDerivCorrectionL (𝕜 := 𝕜) (E := E) s
          (fderivWithin 𝕜 X u y)) u x := by
    exact (hDX.continuousLinearMap_comp
      (lieDerivCorrectionOpL (𝕜 := 𝕜) (E := E) s)).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun _ => rfl) rfl
  have hCorrectionR :
      ContDiffWithinAt 𝕜 m
        (fun y => lieDerivCorrectionL (𝕜 := 𝕜) (E := E) r
          (fderivWithin 𝕜 X u y)) u x := by
    exact (hDX.continuousLinearMap_comp
      (lieDerivCorrectionOpL (𝕜 := 𝕜) (E := E) r)).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun _ => rfl) rfl
  have hOut :
      ContDiffWithinAt 𝕜 m
        (fun y => (lieDerivCorrectionL (𝕜 := 𝕜) (E := E) s
          (fderivWithin 𝕜 X u y)).comp (T y)) u x :=
    hCorrectionS.clm_comp hT_m
  have hIn :
      ContDiffWithinAt 𝕜 m
        (fun y => (T y).comp (lieDerivCorrectionL (𝕜 := 𝕜) (E := E) r
          (fderivWithin 𝕜 X u y))) u x :=
    hT_m.clm_comp hCorrectionR
  simpa [lieDerivTensorRSWithin, directionalDerivTensorRSWithin] using
    (hprincipal.sub hOut).add hIn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.TensorLieDeriv.contDiffWithinAt_lieDeriv_tensorRSWithin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.TensorLieDeriv.contDiffWithinAt_lieDeriv_tensorRSWithin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.TensorLieDeriv.contDiffWithinAt_lieDeriv_tensorRSWithin ``Submission.DifferentialGeometry.TensorLieDeriv.contDiffWithinAt_lieDeriv_tensorRSWithin

section SmoothVectorFieldRSLieDeriv

variable [IsManifold I 1 M] [IsManifold I (n + 1) M]

noncomputable def mdirectionalDerivTensorRSWithin (r s : ℕ)
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r s)
    (u : Set M) (x₀ : M) : TensorRSSpace r s I x₀ := by
  let X' := _root_.VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm X (_root_.Set.range I)
  let T' : E → Tensor0SModel (𝕜 := 𝕜) (E := E) r →L[𝕜] Tensor0SModel (𝕜 := 𝕜) (E := E) s :=
    fun y => tensorRSSpaceContinuousLinearEquiv (I := I) r s
      ((extChartAt I x₀).symm y) (T.toFun ((extChartAt I x₀).symm y))
  exact (tensorRSSpaceContinuousLinearEquiv (I := I) r s x₀).symm
    (lieDerivTensorRSWithin r s X' T'
      ((extChartAt I x₀).symm ⁻¹' u ∩ _root_.Set.range I)
      (extChartAt I x₀ x₀))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.TensorLieDeriv.mdirectionalDerivTensorRSWithin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.TensorLieDeriv.mdirectionalDerivTensorRSWithin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.TensorLieDeriv.mdirectionalDerivTensorRSWithin ``Submission.DifferentialGeometry.TensorLieDeriv.mdirectionalDerivTensorRSWithin

noncomputable def mdirectionalDerivTensorRS (r s : ℕ)
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r s)
    (x₀ : M) : TensorRSSpace r s I x₀ :=
  mdirectionalDerivTensorRSWithin (n := n) r s X T _root_.Set.univ x₀

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.TensorLieDeriv.mdirectionalDerivTensorRS then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.TensorLieDeriv.mdirectionalDerivTensorRS"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.TensorLieDeriv.mdirectionalDerivTensorRS ``Submission.DifferentialGeometry.TensorLieDeriv.mdirectionalDerivTensorRS

end SmoothVectorFieldRSLieDeriv

end ManifoldLieDeriv

end

end TensorLieDeriv
end DifferentialGeometry
