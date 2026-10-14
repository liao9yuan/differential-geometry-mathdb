import Submission.DifferentialGeometry.Topology.Manifold.AddCircle
import Submission.DifferentialGeometry.Topology.Manifold.OpenEmbedding
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

noncomputable section
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace AddCircle
open _root_.AddCircle

open _root_.AddCircle in
theorem isLocalDiffeomorph_coe :
    IsLocalDiffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
      (fun t : ℝ => (t : AddCircle (1 : ℝ))) :=
  DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv _
    contMDiff_coe (fun t => (bijective_mfderiv_coe t).1) rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.isLocalDiffeomorph_coe then
    throwError "Refusing to shadow existing declaration AddCircle.isLocalDiffeomorph_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.isLocalDiffeomorph_coe ``Submission.AddCircle.isLocalDiffeomorph_coe

open _root_.AddCircle in
private theorem quotient_mfderiv_eq {x y : ℝ}
    (h : (x : AddCircle (1 : ℝ)) = y) :
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => (t : AddCircle (1 : ℝ))) x =
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => (t : AddCircle (1 : ℝ))) y := by
  have heq : (fun t : ℝ => ((t + (y - x) : ℝ) : AddCircle (1 : ℝ))) =
      fun t : ℝ => (t : AddCircle (1 : ℝ)) := by
    funext t
    simp only [_root_.AddCircle.coe_add, _root_.AddCircle.coe_sub, ← h, sub_self, add_zero]
  have hder : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => t + (y - x)) x =
      ContinuousLinearMap.id ℝ ℝ := by
    rw [mfderiv_eq_fderiv]
    exact (hasFDerivAt_id x |>.add_const (y - x)).fderiv
  have hh := mfderiv_comp (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ)) (I'' := 𝓘(ℝ, ℝ))
    (f := fun t : ℝ => t + (y - x))
    (g := fun t : ℝ => (t : AddCircle (1 : ℝ))) x
    (contMDiff_coe.mdifferentiableAt (by decide))
    ((contDiff_id.add contDiff_const : ContDiff ℝ ∞ (fun t : ℝ => t + (y - x))).contMDiff.mdifferentiableAt (by decide))
  change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => ((t + (y - x) : ℝ) : AddCircle (1 : ℝ))) x = _ at hh
  rw [heq] at hh
  have hcomp : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
      (fun t : ℝ => (t : AddCircle (1 : ℝ))) x =
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
        (fun t : ℝ => (t : AddCircle (1 : ℝ))) (x + (y - x))).comp
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => t + (y - x)) x) := hh
  have hcomp' : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
      (fun t : ℝ => (t : AddCircle (1 : ℝ))) x =
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
        (fun t : ℝ => (t : AddCircle (1 : ℝ))) (x + (y - x)) := by
    rw [hder] at hcomp
    apply ContinuousLinearMap.coeFn_injective
    funext z
    exact congrFun (congrArg DFunLike.coe hcomp) z
  rw [show x + (y - x) = y by ring] at hcomp'
  exact hcomp'

run_cmd do
  let target := ``Submission.AddCircle.quotient_mfderiv_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `AddCircle.quotient_mfderiv_eq target :: scope.openDecls } }

open _root_.AddCircle in
def parameterTangent (z : AddCircle (1 : ℝ)) : TangentSpace 𝓘(ℝ, ℝ) z :=
  mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => (t : AddCircle (1 : ℝ)))
    (Quotient.out z) (1 : ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.parameterTangent then
    throwError "Refusing to shadow existing declaration AddCircle.parameterTangent"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.parameterTangent ``Submission.AddCircle.parameterTangent

open _root_.AddCircle in
theorem parameterTangent_coe (x : ℝ) :
    parameterTangent (x : AddCircle (1 : ℝ)) =
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => (t : AddCircle (1 : ℝ))) x (1 : ℝ) := by
  unfold parameterTangent
  rw [quotient_mfderiv_eq (Quotient.out_eq _)]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.parameterTangent_coe then
    throwError "Refusing to shadow existing declaration AddCircle.parameterTangent_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.parameterTangent_coe ``Submission.AddCircle.parameterTangent_coe

open _root_.AddCircle in
theorem parameterTangent_ne_zero (z : AddCircle (1 : ℝ)) : parameterTangent z ≠ 0 := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
  rw [parameterTangent_coe]
  exact fun hz => (one_ne_zero : (1 : ℝ) ≠ 0) ((bijective_mfderiv_coe x).1 (hz.trans (map_zero _).symm))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.parameterTangent_ne_zero then
    throwError "Refusing to shadow existing declaration AddCircle.parameterTangent_ne_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.parameterTangent_ne_zero ``Submission.AddCircle.parameterTangent_ne_zero


set_option backward.isDefEq.respectTransparency false in
open _root_.AddCircle in
theorem contMDiff_parameterTangent :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ).tangent ∞
      (fun z : AddCircle (1 : ℝ) =>
        (⟨z, parameterTangent z⟩ : TangentBundle 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))) := by
  have hs : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ).tangent ∞
      (fun t : ℝ => (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) := by
    intro t
    rw [Bundle.contMDiffAt_section]
    convert (contMDiffAt_const (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ))
      (c := (1 : ℝ)) (x := t)) using 1
    funext s
    simp only [TangentBundle.trivializationAt_apply, mfld_simps]
    change (fderivWithin ℝ id Set.univ s) (1 : ℝ) = 1
    rw [fderivWithin_id uniqueDiffWithinAt_univ]
    rfl
  have ht := (contMDiff_coe.contMDiff_tangentMap (m := ∞) le_rfl).comp hs
  intro z
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
  have hx := isLocalDiffeomorph_coe x
  have hc := (ht _).comp _ hx.localInverse_contMDiffAt
  apply hc.congr_of_eventuallyEq
  have heq := hx.localInverse_eventuallyEq_right
  filter_upwards [heq] with y hy
  change (⟨y, parameterTangent y⟩ : TangentBundle 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) =
    ⟨(hx.localInverse y : AddCircle (1 : ℝ)),
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
        (fun t : ℝ => (t : AddCircle (1 : ℝ))) (hx.localInverse y) (1 : ℝ)⟩
  rw [← parameterTangent_coe]
  change (hx.localInverse y : AddCircle (1 : ℝ)) = y at hy
  rw [hy]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.contMDiff_parameterTangent then
    throwError "Refusing to shadow existing declaration AddCircle.contMDiff_parameterTangent"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.contMDiff_parameterTangent ``Submission.AddCircle.contMDiff_parameterTangent

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

open _root_.AddCircle in
theorem deriv_comp_coe {f : AddCircle (1 : ℝ) → F} {x : ℝ}
    (hf : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, F) f (x : AddCircle (1 : ℝ))) :
    deriv (fun t : ℝ => f (t : AddCircle (1 : ℝ))) x =
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) f (x : AddCircle (1 : ℝ))
        (parameterTangent (x : AddCircle (1 : ℝ))) := by
  rw [parameterTangent_coe]
  have hh := mfderiv_comp (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ)) (I'' := 𝓘(ℝ, F))
    (f := fun t : ℝ => (t : AddCircle (1 : ℝ))) (g := f) x hf
    (contMDiff_coe.mdifferentiableAt (by decide))
  rw [mfderiv_eq_fderiv] at hh
  exact congrArg (fun L : ℝ →L[ℝ] F => L (1 : ℝ)) hh

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.deriv_comp_coe then
    throwError "Refusing to shadow existing declaration AddCircle.deriv_comp_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.deriv_comp_coe ``Submission.AddCircle.deriv_comp_coe


open _root_.AddCircle in
theorem contMDiffAt_mfderiv_parameterTangent {f : AddCircle (1 : ℝ) → F}
    {m n : ℕ∞ω} {z : AddCircle (1 : ℝ)}
    (hf : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, F) n f z) (hmn : m + 1 ≤ n) (hm : m ≤ ∞) :
    ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, F) m
      (fun y => mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) f y (parameterTangent y)) z := by
  let e := _root_.FiberBundle.trivializationAt ℝ (TangentSpace 𝓘(ℝ, ℝ)) z
  have hdf := hf.mfderiv_const hmn
  have hX : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) m
      (fun y => (e ⟨y, parameterTangent y⟩).2) z :=
    (Bundle.contMDiffAt_section (n := m) z).mp
      ((contMDiff_parameterTangent.of_le hm).contMDiffAt)
  refine (hdf.clm_apply hX).congr_of_eventuallyEq ?_
  filter_upwards
    [e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt ℝ
      (TangentSpace 𝓘(ℝ, ℝ)) z)] with y hy
  simp only [inTangentCoordinates, ContinuousLinearMap.inCoordinates, Function.id_def,
    TangentBundle.continuousLinearMapAt_model_space]
  change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) f y (parameterTangent y) =
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) f y
      (e.symmL ℝ y ((e ⟨y, parameterTangent y⟩).2))
  congr 1
  rw [e.symmL_apply hy]
  exact (Bundle.Trivialization.symm_apply_apply_mk e hy (parameterTangent y)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.contMDiffAt_mfderiv_parameterTangent then
    throwError "Refusing to shadow existing declaration AddCircle.contMDiffAt_mfderiv_parameterTangent"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.contMDiffAt_mfderiv_parameterTangent ``Submission.AddCircle.contMDiffAt_mfderiv_parameterTangent

open _root_.AddCircle in
theorem mdifferentiableAt_mfderiv_parameterTangent {f : AddCircle (1 : ℝ) → F}
    {z : AddCircle (1 : ℝ)} (hf : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, F) 2 f z) :
    MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, F)
      (fun y => mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) f y (parameterTangent y)) z :=
  (contMDiffAt_mfderiv_parameterTangent (m := 1) hf (by norm_num) (by norm_num)).mdifferentiableAt
    (by decide)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.mdifferentiableAt_mfderiv_parameterTangent then
    throwError "Refusing to shadow existing declaration AddCircle.mdifferentiableAt_mfderiv_parameterTangent"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.mdifferentiableAt_mfderiv_parameterTangent ``Submission.AddCircle.mdifferentiableAt_mfderiv_parameterTangent

open _root_.AddCircle in
theorem deriv_deriv_comp_coe_of_contMDiffAt {f : AddCircle (1 : ℝ) → F} {x : ℝ}
    (hf : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, F) 2 f (x : AddCircle (1 : ℝ))) :
    deriv (deriv (fun t : ℝ => f (t : AddCircle (1 : ℝ)))) x =
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F)
        (fun z => mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) f z (parameterTangent z))
        (x : AddCircle (1 : ℝ)) (parameterTangent (x : AddCircle (1 : ℝ))) := by
  have hevent : ∀ᶠ y in 𝓝 (x : AddCircle (1 : ℝ)),
      ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, F) 2 f y :=
    (contMDiffAt_iff_contMDiffAt_nhds (by norm_num)).mp hf
  have heq : deriv (fun t : ℝ => f (t : AddCircle (1 : ℝ))) =ᶠ[𝓝 x]
      fun t : ℝ => mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) f (t : AddCircle (1 : ℝ))
        (parameterTangent (t : AddCircle (1 : ℝ))) := by
    filter_upwards [(contMDiff_coe.continuous.continuousAt).eventually hevent] with t ht
    exact deriv_comp_coe (ht.mdifferentiableAt (by decide))
  rw [heq.deriv_eq]
  exact deriv_comp_coe (mdifferentiableAt_mfderiv_parameterTangent hf)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.deriv_deriv_comp_coe_of_contMDiffAt then
    throwError "Refusing to shadow existing declaration AddCircle.deriv_deriv_comp_coe_of_contMDiffAt"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.deriv_deriv_comp_coe_of_contMDiffAt ``Submission.AddCircle.deriv_deriv_comp_coe_of_contMDiffAt

open _root_.AddCircle in
theorem contMDiff_mfderiv_parameterTangent {f : AddCircle (1 : ℝ) → F}
    {m n : ℕ∞ω} (hf : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, F) n f) (hmn : m + 1 ≤ n) (hm : m ≤ ∞) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, F) m
      (fun z => mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) f z (parameterTangent z)) :=
  fun z => contMDiffAt_mfderiv_parameterTangent (hf z) hmn hm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.contMDiff_mfderiv_parameterTangent then
    throwError "Refusing to shadow existing declaration AddCircle.contMDiff_mfderiv_parameterTangent"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.contMDiff_mfderiv_parameterTangent ``Submission.AddCircle.contMDiff_mfderiv_parameterTangent

open _root_.AddCircle in
theorem deriv_deriv_comp_coe {f : AddCircle (1 : ℝ) → F}
    (hf : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, F) 2 f) (x : ℝ) :
    deriv (deriv (fun t : ℝ => f (t : AddCircle (1 : ℝ)))) x =
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F)
        (fun z => mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) f z (parameterTangent z))
        (x : AddCircle (1 : ℝ)) (parameterTangent (x : AddCircle (1 : ℝ))) :=
  deriv_deriv_comp_coe_of_contMDiffAt (hf _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.deriv_deriv_comp_coe then
    throwError "Refusing to shadow existing declaration AddCircle.deriv_deriv_comp_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.deriv_deriv_comp_coe ``Submission.AddCircle.deriv_deriv_comp_coe

set_option backward.isDefEq.respectTransparency false in
open _root_.AddCircle in
theorem exists_smul_parameterTangent (z : AddCircle (1 : ℝ))
    (v : TangentSpace 𝓘(ℝ, ℝ) z) : ∃ a : ℝ, a • parameterTangent z = v := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
  obtain ⟨a, ha⟩ := (bijective_mfderiv_coe x).2 v
  let aR : ℝ := a
  refine ⟨aR, ?_⟩
  rw [parameterTangent_coe, ← map_smul]
  change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
    (fun t : ℝ => (t : AddCircle (1 : ℝ))) x (aR * 1) = v
  simpa only [mul_one] using ha

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.exists_smul_parameterTangent then
    throwError "Refusing to shadow existing declaration AddCircle.exists_smul_parameterTangent"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.exists_smul_parameterTangent ``Submission.AddCircle.exists_smul_parameterTangent


section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

open _root_.AddCircle in
theorem mfderiv_comp_coe {f : AddCircle (1 : ℝ) → M} {x : ℝ}
    (hf : MDifferentiableAt 𝓘(ℝ, ℝ) I f (x : AddCircle (1 : ℝ))) :
    mfderiv 𝓘(ℝ, ℝ) I (fun y : ℝ => f (y : AddCircle (1 : ℝ))) x (1 : ℝ) =
      mfderiv 𝓘(ℝ, ℝ) I f (x : AddCircle (1 : ℝ))
        (parameterTangent (x : AddCircle (1 : ℝ))) := by
  rw [parameterTangent_coe]
  exact congrArg (fun L => L (1 : ℝ)) (mfderiv_comp (I := 𝓘(ℝ, ℝ))
    (I' := 𝓘(ℝ, ℝ)) (I'' := I) (f := fun y : ℝ => (y : AddCircle (1 : ℝ)))
    (g := f) x hf (contMDiff_coe.mdifferentiableAt (by simp)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.mfderiv_comp_coe then
    throwError "Refusing to shadow existing declaration AddCircle.mfderiv_comp_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.mfderiv_comp_coe ``Submission.AddCircle.mfderiv_comp_coe


end

end AddCircle

end

end
