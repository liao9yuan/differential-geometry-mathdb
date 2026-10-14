import Submission.DifferentialGeometry.Topology.FiberwiseHomeomorph
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Logic.Equiv.Prod

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open scoped _root_.Manifold _root_.ContDiff

namespace Diffeomorph
open _root_.Diffeomorph

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : ℕ∞ω} {f g : F → 𝕜}

open _root_.Diffeomorph in
def fiberwiseSmul (hf : ContDiff 𝕜 n f) (h₀ : ∀ b, f b ≠ 0) :
    Diffeomorph 𝓘(𝕜, E × F) 𝓘(𝕜, E × F) (E × F) (E × F) n where
  toEquiv := Equiv.prodCongrLeft fun b =>
    (LinearEquiv.smulOfNeZero 𝕜 E (f b) (h₀ b)).toEquiv
  contMDiff_toFun :=
    (((hf.comp contDiff_snd).smul contDiff_fst).prodMk contDiff_snd).contMDiff
  contMDiff_invFun :=
    ((((hf.inv h₀).comp contDiff_snd).smul contDiff_fst).prodMk contDiff_snd).contMDiff

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.fiberwiseSmul then
    throwError "Refusing to shadow existing declaration Diffeomorph.fiberwiseSmul"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.fiberwiseSmul ``Submission.Diffeomorph.fiberwiseSmul

open _root_.Diffeomorph in
@[simp] theorem fiberwiseSmul_apply (hf : ContDiff 𝕜 n f) (h₀ : ∀ b, f b ≠ 0)
    (p : E × F) : fiberwiseSmul hf h₀ p = (f p.2 • p.1, p.2) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.fiberwiseSmul_apply then
    throwError "Refusing to shadow existing declaration Diffeomorph.fiberwiseSmul_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.fiberwiseSmul_apply ``Submission.Diffeomorph.fiberwiseSmul_apply

open _root_.Diffeomorph in
theorem fiberwiseSmul_symm_apply (hf : ContDiff 𝕜 n f) (h₀ : ∀ b, f b ≠ 0)
    (p : E × F) : (fiberwiseSmul hf h₀).symm p = ((f p.2)⁻¹ • p.1, p.2) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.fiberwiseSmul_symm_apply then
    throwError "Refusing to shadow existing declaration Diffeomorph.fiberwiseSmul_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.fiberwiseSmul_symm_apply ``Submission.Diffeomorph.fiberwiseSmul_symm_apply

open _root_.Diffeomorph in
@[simp] theorem fiberwiseSmul_symm (hf : ContDiff 𝕜 n f) (h₀ : ∀ b, f b ≠ 0) :
    (fiberwiseSmul (E := E) hf h₀).symm =
      fiberwiseSmul (hf.inv h₀) (fun b => inv_ne_zero (h₀ b)) := by
  apply Diffeomorph.ext
  intro p
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.fiberwiseSmul_symm then
    throwError "Refusing to shadow existing declaration Diffeomorph.fiberwiseSmul_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.fiberwiseSmul_symm ``Submission.Diffeomorph.fiberwiseSmul_symm

open _root_.Diffeomorph in
@[simp] theorem fiberwiseSmul_one :
    fiberwiseSmul (E := E) (n := n) (f := fun _ : F => (1 : 𝕜))
      contDiff_const (fun _ => one_ne_zero) =
        Diffeomorph.refl 𝓘(𝕜, E × F) (E × F) n := by
  apply Diffeomorph.ext
  intro p
  rw [fiberwiseSmul_apply]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.fiberwiseSmul_one then
    throwError "Refusing to shadow existing declaration Diffeomorph.fiberwiseSmul_one"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.fiberwiseSmul_one ``Submission.Diffeomorph.fiberwiseSmul_one

open _root_.Diffeomorph in
@[simp] theorem fiberwiseSmul_trans (hf : ContDiff 𝕜 n f) (h₀ : ∀ b, f b ≠ 0)
    (hg : ContDiff 𝕜 n g) (hg₀ : ∀ b, g b ≠ 0) :
    (fiberwiseSmul (E := E) hf h₀).trans (fiberwiseSmul hg hg₀) =
      fiberwiseSmul (hg.mul hf) (fun b => mul_ne_zero (hg₀ b) (h₀ b)) := by
  apply Diffeomorph.ext
  intro p
  change fiberwiseSmul hg hg₀ (fiberwiseSmul hf h₀ p) =
    fiberwiseSmul (hg.mul hf) (fun b => mul_ne_zero (hg₀ b) (h₀ b)) p
  simp only [fiberwiseSmul_apply, smul_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.fiberwiseSmul_trans then
    throwError "Refusing to shadow existing declaration Diffeomorph.fiberwiseSmul_trans"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.fiberwiseSmul_trans ``Submission.Diffeomorph.fiberwiseSmul_trans

end Diffeomorph

namespace Diffeomorph
open _root_.Diffeomorph

section ProdCongrRight

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E₀ E₁ E₂ E₃ : Type*}
  [NormedAddCommGroup E₀] [NormedSpace 𝕜 E₀]
  [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
  [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
  [NormedAddCommGroup E₃] [NormedSpace 𝕜 E₃]
  {H₀ H₁ H₂ H₃ : Type*}
  [TopologicalSpace H₀] [TopologicalSpace H₁]
  [TopologicalSpace H₂] [TopologicalSpace H₃]
  {I : ModelWithCorners 𝕜 E₀ H₀} {J : ModelWithCorners 𝕜 E₁ H₁}
  {K : ModelWithCorners 𝕜 E₂ H₂} {L : ModelWithCorners 𝕜 E₃ H₃}
  {P M N Q : Type*}
  [TopologicalSpace P] [ChartedSpace H₀ P]
  [TopologicalSpace M] [ChartedSpace H₁ M]
  [TopologicalSpace N] [ChartedSpace H₂ N]
  [TopologicalSpace Q] [ChartedSpace H₃ Q] {n : ℕ∞ω}

open _root_.Diffeomorph in
def prodCongrRight (e : P → Diffeomorph J K M N n)
    (he : ContMDiff (I.prod J) K n (fun z : P × M => e z.1 z.2))
    (hi : ContMDiff (I.prod K) J n (fun z : P × N => (e z.1).symm z.2)) :
    Diffeomorph (I.prod J) (I.prod K) (P × M) (P × N) n where
  toEquiv := Equiv.prodCongrRight (fun p => (e p).toEquiv)
  contMDiff_toFun := contMDiff_fst.prodMk he
  contMDiff_invFun := contMDiff_fst.prodMk hi

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.prodCongrRight then
    throwError "Refusing to shadow existing declaration Diffeomorph.prodCongrRight"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.prodCongrRight ``Submission.Diffeomorph.prodCongrRight

open _root_.Diffeomorph in
@[simp] theorem prodCongrRight_apply (e : P → Diffeomorph J K M N n)
    (he : ContMDiff (I.prod J) K n (fun z : P × M => e z.1 z.2))
    (hi : ContMDiff (I.prod K) J n (fun z : P × N => (e z.1).symm z.2)) (p : P × M) :
    prodCongrRight e he hi p = (p.1, e p.1 p.2) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.prodCongrRight_apply then
    throwError "Refusing to shadow existing declaration Diffeomorph.prodCongrRight_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.prodCongrRight_apply ``Submission.Diffeomorph.prodCongrRight_apply

open _root_.Diffeomorph in
@[simp] theorem prodCongrRight_symm_apply (e : P → Diffeomorph J K M N n)
    (he : ContMDiff (I.prod J) K n (fun z : P × M => e z.1 z.2))
    (hi : ContMDiff (I.prod K) J n (fun z : P × N => (e z.1).symm z.2)) (p : P × N) :
    (prodCongrRight e he hi).symm p = (p.1, (e p.1).symm p.2) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.prodCongrRight_symm_apply then
    throwError "Refusing to shadow existing declaration Diffeomorph.prodCongrRight_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.prodCongrRight_symm_apply ``Submission.Diffeomorph.prodCongrRight_symm_apply

open _root_.Diffeomorph in
theorem prodCongrRight_symm (e : P → Diffeomorph J K M N n)
    (he : ContMDiff (I.prod J) K n (fun z : P × M => e z.1 z.2))
    (hi : ContMDiff (I.prod K) J n (fun z : P × N => (e z.1).symm z.2)) :
    (prodCongrRight e he hi).symm = prodCongrRight (fun p => (e p).symm) hi he := by
  apply Diffeomorph.ext
  intro p
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.prodCongrRight_symm then
    throwError "Refusing to shadow existing declaration Diffeomorph.prodCongrRight_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.prodCongrRight_symm ``Submission.Diffeomorph.prodCongrRight_symm

open _root_.Diffeomorph in
@[simp] theorem prodCongrRight_refl :
    prodCongrRight (fun _ : P => Diffeomorph.refl J M n)
      (contMDiff_snd (I := I)) contMDiff_snd = Diffeomorph.refl (I.prod J) (P × M) n := by
  apply Diffeomorph.ext
  intro p
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.prodCongrRight_refl then
    throwError "Refusing to shadow existing declaration Diffeomorph.prodCongrRight_refl"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.prodCongrRight_refl ``Submission.Diffeomorph.prodCongrRight_refl

open _root_.Diffeomorph in
@[simp] theorem prodCongrRight_trans (e : P → Diffeomorph J K M N n)
    (he : ContMDiff (I.prod J) K n (fun z : P × M => e z.1 z.2))
    (hi : ContMDiff (I.prod K) J n (fun z : P × N => (e z.1).symm z.2))
    (f : P → Diffeomorph K L N Q n)
    (hf : ContMDiff (I.prod K) L n (fun z : P × N => f z.1 z.2))
    (hj : ContMDiff (I.prod L) K n (fun z : P × Q => (f z.1).symm z.2)) :
    (prodCongrRight e he hi).trans (prodCongrRight f hf hj) =
      prodCongrRight (fun p => (e p).trans (f p))
        (hf.comp (contMDiff_fst.prodMk he)) (hi.comp (contMDiff_fst.prodMk hj)) := by
  apply Diffeomorph.ext
  intro p
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.prodCongrRight_trans then
    throwError "Refusing to shadow existing declaration Diffeomorph.prodCongrRight_trans"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.prodCongrRight_trans ``Submission.Diffeomorph.prodCongrRight_trans

open _root_.Diffeomorph in
def prodCongrLeft (e : P → Diffeomorph J K M N n)
    (he : ContMDiff (J.prod I) K n (fun z : M × P => e z.2 z.1))
    (hi : ContMDiff (K.prod I) J n (fun z : N × P => (e z.2).symm z.1)) :
    Diffeomorph (J.prod I) (K.prod I) (M × P) (N × P) n where
  toEquiv := Equiv.prodCongrLeft (fun p => (e p).toEquiv)
  contMDiff_toFun := he.prodMk contMDiff_snd
  contMDiff_invFun := hi.prodMk contMDiff_snd

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.prodCongrLeft then
    throwError "Refusing to shadow existing declaration Diffeomorph.prodCongrLeft"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.prodCongrLeft ``Submission.Diffeomorph.prodCongrLeft

open _root_.Diffeomorph in
@[simp] theorem prodCongrLeft_apply (e : P → Diffeomorph J K M N n)
    (he : ContMDiff (J.prod I) K n (fun z : M × P => e z.2 z.1))
    (hi : ContMDiff (K.prod I) J n (fun z : N × P => (e z.2).symm z.1)) (p : M × P) :
    prodCongrLeft e he hi p = (e p.2 p.1, p.2) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.prodCongrLeft_apply then
    throwError "Refusing to shadow existing declaration Diffeomorph.prodCongrLeft_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.prodCongrLeft_apply ``Submission.Diffeomorph.prodCongrLeft_apply

open _root_.Diffeomorph in
@[simp] theorem prodCongrLeft_symm_apply (e : P → Diffeomorph J K M N n)
    (he : ContMDiff (J.prod I) K n (fun z : M × P => e z.2 z.1))
    (hi : ContMDiff (K.prod I) J n (fun z : N × P => (e z.2).symm z.1)) (p : N × P) :
    (prodCongrLeft e he hi).symm p = ((e p.2).symm p.1, p.2) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.prodCongrLeft_symm_apply then
    throwError "Refusing to shadow existing declaration Diffeomorph.prodCongrLeft_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.prodCongrLeft_symm_apply ``Submission.Diffeomorph.prodCongrLeft_symm_apply


end ProdCongrRight

end Diffeomorph

namespace PartialDiffeomorph
open _root_.PartialDiffeomorph

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : ℕ∞ω} {f : F → 𝕜}

open _root_.PartialDiffeomorph in
def fiberwiseSmulOn {U : Set F} (hU : IsOpen U) (hf : ContDiffOn 𝕜 n f U)
    (h₀ : ∀ b ∈ U, f b ≠ 0) :
    PartialDiffeomorph 𝓘(𝕜, E × F) 𝓘(𝕜, E × F) (E × F) (E × F) n where
  toFun p := (f p.2 • p.1, p.2)
  invFun p := ((f p.2)⁻¹ • p.1, p.2)
  source := Prod.snd ⁻¹' U
  target := Prod.snd ⁻¹' U
  map_source' _ hp := hp
  map_target' _ hp := hp
  left_inv' p hp := by simp only [smul_smul, inv_mul_cancel₀ (h₀ p.2 hp), one_smul]
  right_inv' p hp := by simp only [smul_smul, mul_inv_cancel₀ (h₀ p.2 hp), one_smul]
  open_source := hU.preimage continuous_snd
  open_target := hU.preimage continuous_snd
  contMDiffOn_toFun :=
    (((hf.comp contDiff_snd.contDiffOn (fun _ hp => hp)).smul
      contDiff_fst.contDiffOn).prodMk contDiff_snd.contDiffOn).contMDiffOn
  contMDiffOn_invFun :=
    ((((hf.inv h₀).comp contDiff_snd.contDiffOn (fun _ hp => hp)).smul
      contDiff_fst.contDiffOn).prodMk contDiff_snd.contDiffOn).contMDiffOn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartialDiffeomorph.fiberwiseSmulOn then
    throwError "Refusing to shadow existing declaration PartialDiffeomorph.fiberwiseSmulOn"
  Lean.modifyEnv fun env => Lean.addAlias env `PartialDiffeomorph.fiberwiseSmulOn ``Submission.PartialDiffeomorph.fiberwiseSmulOn

open _root_.PartialDiffeomorph in
@[simp] theorem fiberwiseSmulOn_apply {U : Set F} (hU : IsOpen U)
    (hf : ContDiffOn 𝕜 n f U) (h₀ : ∀ b ∈ U, f b ≠ 0) (p : E × F) :
    fiberwiseSmulOn hU hf h₀ p = (f p.2 • p.1, p.2) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartialDiffeomorph.fiberwiseSmulOn_apply then
    throwError "Refusing to shadow existing declaration PartialDiffeomorph.fiberwiseSmulOn_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `PartialDiffeomorph.fiberwiseSmulOn_apply ``Submission.PartialDiffeomorph.fiberwiseSmulOn_apply

open _root_.PartialDiffeomorph in
theorem fiberwiseSmulOn_symm_apply {U : Set F} (hU : IsOpen U)
    (hf : ContDiffOn 𝕜 n f U) (h₀ : ∀ b ∈ U, f b ≠ 0) (p : E × F) :
    (fiberwiseSmulOn hU hf h₀).symm p = ((f p.2)⁻¹ • p.1, p.2) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartialDiffeomorph.fiberwiseSmulOn_symm_apply then
    throwError "Refusing to shadow existing declaration PartialDiffeomorph.fiberwiseSmulOn_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `PartialDiffeomorph.fiberwiseSmulOn_symm_apply ``Submission.PartialDiffeomorph.fiberwiseSmulOn_symm_apply

open _root_.PartialDiffeomorph in
@[simp] theorem fiberwiseSmulOn_source {U : Set F} (hU : IsOpen U)
    (hf : ContDiffOn 𝕜 n f U) (h₀ : ∀ b ∈ U, f b ≠ 0) :
    (fiberwiseSmulOn (E := E) hU hf h₀).source = Prod.snd ⁻¹' U := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartialDiffeomorph.fiberwiseSmulOn_source then
    throwError "Refusing to shadow existing declaration PartialDiffeomorph.fiberwiseSmulOn_source"
  Lean.modifyEnv fun env => Lean.addAlias env `PartialDiffeomorph.fiberwiseSmulOn_source ``Submission.PartialDiffeomorph.fiberwiseSmulOn_source

open _root_.PartialDiffeomorph in
@[simp] theorem fiberwiseSmulOn_target {U : Set F} (hU : IsOpen U)
    (hf : ContDiffOn 𝕜 n f U) (h₀ : ∀ b ∈ U, f b ≠ 0) :
    (fiberwiseSmulOn (E := E) hU hf h₀).target = Prod.snd ⁻¹' U := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartialDiffeomorph.fiberwiseSmulOn_target then
    throwError "Refusing to shadow existing declaration PartialDiffeomorph.fiberwiseSmulOn_target"
  Lean.modifyEnv fun env => Lean.addAlias env `PartialDiffeomorph.fiberwiseSmulOn_target ``Submission.PartialDiffeomorph.fiberwiseSmulOn_target

open _root_.PartialDiffeomorph in
def fiberwiseSmul (hf : ContDiff 𝕜 n f) :
    PartialDiffeomorph 𝓘(𝕜, E × F) 𝓘(𝕜, E × F) (E × F) (E × F) n :=
  fiberwiseSmulOn (isOpen_ne_fun hf.continuous continuous_const) hf.contDiffOn (fun _ h => h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartialDiffeomorph.fiberwiseSmul then
    throwError "Refusing to shadow existing declaration PartialDiffeomorph.fiberwiseSmul"
  Lean.modifyEnv fun env => Lean.addAlias env `PartialDiffeomorph.fiberwiseSmul ``Submission.PartialDiffeomorph.fiberwiseSmul

open _root_.PartialDiffeomorph in
@[simp] theorem fiberwiseSmul_apply (hf : ContDiff 𝕜 n f) (p : E × F) :
    fiberwiseSmul hf p = (f p.2 • p.1, p.2) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartialDiffeomorph.fiberwiseSmul_apply then
    throwError "Refusing to shadow existing declaration PartialDiffeomorph.fiberwiseSmul_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `PartialDiffeomorph.fiberwiseSmul_apply ``Submission.PartialDiffeomorph.fiberwiseSmul_apply

open _root_.PartialDiffeomorph in
theorem fiberwiseSmul_symm_apply (hf : ContDiff 𝕜 n f) (p : E × F) :
    (fiberwiseSmul hf).symm p = ((f p.2)⁻¹ • p.1, p.2) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartialDiffeomorph.fiberwiseSmul_symm_apply then
    throwError "Refusing to shadow existing declaration PartialDiffeomorph.fiberwiseSmul_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `PartialDiffeomorph.fiberwiseSmul_symm_apply ``Submission.PartialDiffeomorph.fiberwiseSmul_symm_apply

open _root_.PartialDiffeomorph in
@[simp] theorem fiberwiseSmul_source (hf : ContDiff 𝕜 n f) :
    (fiberwiseSmul (E := E) hf).source = {p | f p.2 ≠ 0} := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartialDiffeomorph.fiberwiseSmul_source then
    throwError "Refusing to shadow existing declaration PartialDiffeomorph.fiberwiseSmul_source"
  Lean.modifyEnv fun env => Lean.addAlias env `PartialDiffeomorph.fiberwiseSmul_source ``Submission.PartialDiffeomorph.fiberwiseSmul_source

open _root_.PartialDiffeomorph in
@[simp] theorem fiberwiseSmul_target (hf : ContDiff 𝕜 n f) :
    (fiberwiseSmul (E := E) hf).target = {p | f p.2 ≠ 0} := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartialDiffeomorph.fiberwiseSmul_target then
    throwError "Refusing to shadow existing declaration PartialDiffeomorph.fiberwiseSmul_target"
  Lean.modifyEnv fun env => Lean.addAlias env `PartialDiffeomorph.fiberwiseSmul_target ``Submission.PartialDiffeomorph.fiberwiseSmul_target

end PartialDiffeomorph

namespace Diffeomorph
open _root_.Diffeomorph

section RestrictFiber

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {H H' H'' : Type*} [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H'']
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F H'} {K : ModelWithCorners 𝕜 G H''}
  {M N P : Type*} [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace P]
  [ChartedSpace H M] [ChartedSpace H' N] [ChartedSpace H'' P] {n : ℕ∞ω}

open _root_.Diffeomorph in
theorem snd_symm_eq_of_snd_eq (Φ : (M × P) ≃ₘ^n⟮I.prod K, J.prod K⟯ (N × P))
    (hΦ : ∀ q, (Φ q).2 = q.2) (q : N × P) : (Φ.symm q).2 = q.2 :=
  (hΦ (Φ.symm q)).symm.trans (congrArg Prod.snd (Φ.apply_symm_apply q))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.snd_symm_eq_of_snd_eq then
    throwError "Refusing to shadow existing declaration Diffeomorph.snd_symm_eq_of_snd_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.snd_symm_eq_of_snd_eq ``Submission.Diffeomorph.snd_symm_eq_of_snd_eq

open _root_.Diffeomorph in
def restrictFiber (Φ : (M × P) ≃ₘ^n⟮I.prod K, J.prod K⟯ (N × P))
    (hΦ : ∀ q, (Φ q).2 = q.2) (p : P) : M ≃ₘ^n⟮I, J⟯ N where
  toEquiv := (Φ.toHomeomorph.restrictFiber hΦ p).toEquiv
  contMDiff_toFun := (Φ.contMDiff.comp (contMDiff_id.prodMk contMDiff_const)).fst
  contMDiff_invFun := (Φ.symm.contMDiff.comp (contMDiff_id.prodMk contMDiff_const)).fst

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.restrictFiber then
    throwError "Refusing to shadow existing declaration Diffeomorph.restrictFiber"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.restrictFiber ``Submission.Diffeomorph.restrictFiber

open _root_.Diffeomorph in
@[simp] theorem restrictFiber_apply
    (Φ : (M × P) ≃ₘ^n⟮I.prod K, J.prod K⟯ (N × P))
    (hΦ : ∀ q, (Φ q).2 = q.2) (p : P) (x : M) :
    Φ.restrictFiber hΦ p x = (Φ (x, p)).1 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.restrictFiber_apply then
    throwError "Refusing to shadow existing declaration Diffeomorph.restrictFiber_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.restrictFiber_apply ``Submission.Diffeomorph.restrictFiber_apply

open _root_.Diffeomorph in
@[simp] theorem restrictFiber_symm_apply
    (Φ : (M × P) ≃ₘ^n⟮I.prod K, J.prod K⟯ (N × P))
    (hΦ : ∀ q, (Φ q).2 = q.2) (p : P) (y : N) :
    (Φ.restrictFiber hΦ p).symm y = (Φ.symm (y, p)).1 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.restrictFiber_symm_apply then
    throwError "Refusing to shadow existing declaration Diffeomorph.restrictFiber_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.restrictFiber_symm_apply ``Submission.Diffeomorph.restrictFiber_symm_apply

open _root_.Diffeomorph in
theorem contMDiff_restrictFiber
    (Φ : (M × P) ≃ₘ^n⟮I.prod K, J.prod K⟯ (N × P)) (hΦ : ∀ q, (Φ q).2 = q.2) :
    ContMDiff (K.prod I) J n (fun q : P × M => Φ.restrictFiber hΦ q.1 q.2) :=
  (Φ.contMDiff.comp (contMDiff_snd.prodMk contMDiff_fst)).fst

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.contMDiff_restrictFiber then
    throwError "Refusing to shadow existing declaration Diffeomorph.contMDiff_restrictFiber"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.contMDiff_restrictFiber ``Submission.Diffeomorph.contMDiff_restrictFiber

open _root_.Diffeomorph in
theorem contMDiff_restrictFiber_symm
    (Φ : (M × P) ≃ₘ^n⟮I.prod K, J.prod K⟯ (N × P)) (hΦ : ∀ q, (Φ q).2 = q.2) :
    ContMDiff (K.prod J) I n (fun q : P × N => (Φ.restrictFiber hΦ q.1).symm q.2) :=
  (Φ.symm.contMDiff.comp (contMDiff_snd.prodMk contMDiff_fst)).fst

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.contMDiff_restrictFiber_symm then
    throwError "Refusing to shadow existing declaration Diffeomorph.contMDiff_restrictFiber_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.contMDiff_restrictFiber_symm ``Submission.Diffeomorph.contMDiff_restrictFiber_symm

end RestrictFiber

end Diffeomorph
