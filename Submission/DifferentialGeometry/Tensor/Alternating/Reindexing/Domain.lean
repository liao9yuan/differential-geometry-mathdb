/-
Authors: Jack McCarthy
-/
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.LinearAlgebra.Alternating.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace ContinuousAlternatingMap
open _root_.ContinuousAlternatingMap

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {M : Type*} [NormedAddCommGroup M] [NormedSpace 𝕜 M]
  {N : Type*} [NormedAddCommGroup N] [NormedSpace 𝕜 N]
  {ι ι' : Type*}

open _root_.ContinuousAlternatingMap in
def domDomCongr (σ : ι ≃ ι') (f : M [⋀^ι]→L[𝕜] N) : M [⋀^ι']→L[𝕜] N :=
  { f.toContinuousMultilinearMap.domDomCongr σ with
    toFun := fun v => f (v ∘ σ)
    map_eq_zero_of_eq' := fun v i j hv hij =>
      f.map_eq_zero_of_eq (v ∘ σ) (i := σ.symm i) (j := σ.symm j)
        (by simpa using hv) (σ.symm.injective.ne hij) }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousAlternatingMap.domDomCongr then
    throwError "Refusing to shadow existing declaration ContinuousAlternatingMap.domDomCongr"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousAlternatingMap.domDomCongr ``Submission.ContinuousAlternatingMap.domDomCongr

open _root_.ContinuousAlternatingMap in
@[simp]
theorem domDomCongr_apply (σ : ι ≃ ι') (f : M [⋀^ι]→L[𝕜] N) (v : ι' → M) :
    (domDomCongr σ f) v = f (v ∘ σ) :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousAlternatingMap.domDomCongr_apply then
    throwError "Refusing to shadow existing declaration ContinuousAlternatingMap.domDomCongr_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousAlternatingMap.domDomCongr_apply ``Submission.ContinuousAlternatingMap.domDomCongr_apply

open _root_.ContinuousAlternatingMap in
@[simp]
theorem domDomCongr_refl (f : M [⋀^ι]→L[𝕜] N) :
    domDomCongr (Equiv.refl ι) f = f :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousAlternatingMap.domDomCongr_refl then
    throwError "Refusing to shadow existing declaration ContinuousAlternatingMap.domDomCongr_refl"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousAlternatingMap.domDomCongr_refl ``Submission.ContinuousAlternatingMap.domDomCongr_refl

variable {m n : ℕ}

open _root_.ContinuousAlternatingMap in
theorem domDomCongr_add (e : Fin m ≃ Fin n)
    (f g : M [⋀^Fin m]→L[𝕜] N) :
    domDomCongr e (f + g) = domDomCongr e f + domDomCongr e g := by
  ext x; simp [domDomCongr_apply, _root_.ContinuousAlternatingMap.add_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousAlternatingMap.domDomCongr_add then
    throwError "Refusing to shadow existing declaration ContinuousAlternatingMap.domDomCongr_add"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousAlternatingMap.domDomCongr_add ``Submission.ContinuousAlternatingMap.domDomCongr_add

open _root_.ContinuousAlternatingMap in
theorem domDomCongr_smul {ι ι' : Type*} (c : 𝕜) (e : ι ≃ ι')
    (f : M [⋀^ι]→L[𝕜] N) :
    domDomCongr e (c • f) = c • domDomCongr e f := by
  ext v
  simp [domDomCongr_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousAlternatingMap.domDomCongr_smul then
    throwError "Refusing to shadow existing declaration ContinuousAlternatingMap.domDomCongr_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousAlternatingMap.domDomCongr_smul ``Submission.ContinuousAlternatingMap.domDomCongr_smul

open _root_.ContinuousAlternatingMap in
theorem domDomCongr_trans {ι ι' ι'' : Type*} (e₁ : ι ≃ ι') (e₂ : ι' ≃ ι'')
    (f : M [⋀^ι]→L[𝕜] N) :
    (f.domDomCongr e₁).domDomCongr e₂ = f.domDomCongr (e₁.trans e₂) := by
  ext v
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousAlternatingMap.domDomCongr_trans then
    throwError "Refusing to shadow existing declaration ContinuousAlternatingMap.domDomCongr_trans"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousAlternatingMap.domDomCongr_trans ``Submission.ContinuousAlternatingMap.domDomCongr_trans

open _root_.ContinuousAlternatingMap in
theorem domDomCongr_sum {ι : Type*}
    (e : Fin m ≃ Fin n) (s : Finset ι) (f : ι → M [⋀^Fin m]→L[𝕜] N) :
    domDomCongr e (∑ i ∈ s, f i) = ∑ i ∈ s, domDomCongr e (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => ext; simp [domDomCongr_apply]
  | insert _ _ hni ih =>
    rw [Finset.sum_insert hni, domDomCongr_add, ih, Finset.sum_insert hni]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousAlternatingMap.domDomCongr_sum then
    throwError "Refusing to shadow existing declaration ContinuousAlternatingMap.domDomCongr_sum"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousAlternatingMap.domDomCongr_sum ``Submission.ContinuousAlternatingMap.domDomCongr_sum

variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]

open _root_.ContinuousAlternatingMap in
theorem alternatization_domDomCongr
    (e : ι₁ ≃ ι₂) (T : MultilinearMap 𝕜 (fun _ : ι₁ => M) N) :
    MultilinearMap.alternatization (T.domDomCongr e) =
      (MultilinearMap.alternatization T).domDomCongr e := by
  ext v; simp only [MultilinearMap.alternatization_apply, AlternatingMap.domDomCongr_apply,
    MultilinearMap.domDomCongr_apply]
  rw [← Equiv.sum_comp (Equiv.permCongr e)]; congr 1; ext σ
  simp only [Equiv.Perm.sign_permCongr, Function.comp]
  congr 2; funext i; simp [Equiv.permCongr_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousAlternatingMap.alternatization_domDomCongr then
    throwError "Refusing to shadow existing declaration ContinuousAlternatingMap.alternatization_domDomCongr"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousAlternatingMap.alternatization_domDomCongr ``Submission.ContinuousAlternatingMap.alternatization_domDomCongr

end ContinuousAlternatingMap
