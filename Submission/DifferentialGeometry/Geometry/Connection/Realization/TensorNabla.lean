import Submission.DifferentialGeometry.Geometry.Connection.Realization.SmoothSections
import Submission.DifferentialGeometry.Geometry.Connection.Realization.ConcreteConnection
import Mathlib.Geometry.Manifold.VectorBundle.Tensoriality

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.Geometry.Connection.Realization


noncomputable section



open scoped _root_.Manifold _root_.ContDiff _root_.Topology
open _root_.Bundle _root_.Submission.Bundle _root_.CovariantDerivative

section DualConnection

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

private abbrev MDiffAtDual
    (α : Π x : M, (_root_.Submission.Bundle.dual ℝ (TangentSpace I : M → Type _)) x) (x : M) : Prop :=
  MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ))
    (fun y => TotalSpace.mk' (E →L[ℝ] ℝ)
      (E := fun x : M => (TangentSpace I x →L[ℝ] (_root_.Bundle.Trivial M ℝ) x)) y (α y)) x

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Connection.Realization.MDiffAtDual
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Connection.Realization.MDiffAtDual target :: scope.openDecls } }

private abbrev MDiffAtVec
    (Y : Π x : M, TangentSpace I x) (x : M) : Prop :=
  MDifferentiableAt I (I.prod 𝓘(ℝ, E))
    (fun y => TotalSpace.mk' E (E := TangentSpace I) y (Y y)) x

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Connection.Realization.MDiffAtVec
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Connection.Realization.MDiffAtVec target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem mdiffAt_pairing
    {α : Π x : M, (_root_.Submission.Bundle.dual ℝ (TangentSpace I : M → Type _)) x}
    {Y : Π x : M, TangentSpace I x} {x : M}
    (hα : MDiffAtDual I M α x) (hY : MDiffAtVec I M Y x) :
    MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => α y (Y y)) x := by
  have h := MDifferentiableAt.clm_bundle_apply (b := id) hα hY
  have h' : MDifferentiableAt I (I.prod 𝓘(ℝ, ℝ))
      (fun m => TotalSpace.mk' ℝ (E := _root_.Bundle.Trivial M ℝ) m (α m (Y m))) x := h
  rw [mdifferentiableAt_section (F := ℝ) (E := _root_.Bundle.Trivial M ℝ)] at h'
  exact h'

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Connection.Realization.mdiffAt_pairing
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Connection.Realization.mdiffAt_pairing target :: scope.openDecls } }

private def Psi
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (α : Π x : M, (_root_.Submission.Bundle.dual ℝ (TangentSpace I : M → Type _)) x)
    (V Y : Π x : M, TangentSpace I x) (x : M) : ℝ :=
  mvfderiv (I := I) (fun y => α y (Y y)) x (V x) - (α x) (cov Y x (V x))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Connection.Realization.Psi
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Connection.Realization.Psi target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem Psi_add_left
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (α : Π x : M, (_root_.Submission.Bundle.dual ℝ (TangentSpace I : M → Type _)) x)
    {V V' Y : Π x : M, TangentSpace I x} {x : M} :
    Psi I M cov α (V + V') Y x = Psi I M cov α V Y x + Psi I M cov α V' Y x := by
  have h_add : (V + V' : Π x : M, TangentSpace I x) x = V x + V' x := rfl
  simp only [Psi, h_add, ContinuousLinearMap.map_add]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Connection.Realization.Psi_add_left
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Connection.Realization.Psi_add_left target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem Psi_smul_left
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (α : Π x : M, (_root_.Submission.Bundle.dual ℝ (TangentSpace I : M → Type _)) x)
    {f : M → ℝ} {V Y : Π x : M, TangentSpace I x} {x : M} :
    Psi I M cov α (f • V) Y x = f x • Psi I M cov α V Y x := by
  have h_smul : (f • V : Π x : M, TangentSpace I x) x = f x • V x := rfl
  simp only [Psi, h_smul, ContinuousLinearMap.map_smul, smul_eq_mul]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Connection.Realization.Psi_smul_left
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Connection.Realization.Psi_smul_left target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem Psi_add_right
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (α : Π x : M, (_root_.Submission.Bundle.dual ℝ (TangentSpace I : M → Type _)) x)
    {V Y Y' : Π x : M, TangentSpace I x} {x : M}
    (hα : MDiffAtDual I M α x)
    (hY : MDiffAtVec I M Y x) (hY' : MDiffAtVec I M Y' x) :
    Psi I M cov α V (Y + Y') x = Psi I M cov α V Y x + Psi I M cov α V Y' x := by
  have hαY : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => α y (Y y)) x :=
    mdiffAt_pairing I M hα hY
  have hαY' : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => α y (Y' y)) x :=
    mdiffAt_pairing I M hα hY'
  have h_add_fun : (fun y => α y ((Y + Y') y)) =
      (fun y => α y (Y y)) + (fun y => α y (Y' y)) := by
    funext y
    simp [Pi.add_apply, ContinuousLinearMap.map_add]
  have hY_T : MDiffAt (T% fun y => Y y) x := hY
  have hY'_T : MDiffAt (T% fun y => Y' y) x := hY'
  simp only [Psi]
  rw [h_add_fun, mvfderiv_add hαY hαY']
  rw [show (Y + Y' : Π x : M, TangentSpace I x) = (fun x => Y x) + (fun x => Y' x) from rfl,
    cov.isCovariantDerivativeOn.add hY_T hY'_T]
  simp only [add_apply, ContinuousLinearMap.map_add]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Connection.Realization.Psi_add_right
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Connection.Realization.Psi_add_right target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem Psi_smul_right
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (α : Π x : M, (_root_.Submission.Bundle.dual ℝ (TangentSpace I : M → Type _)) x)
    {V Y : Π x : M, TangentSpace I x} {f : M → ℝ} {x : M}
    (hα : MDiffAtDual I M α x)
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x) (hY : MDiffAtVec I M Y x) :
    Psi I M cov α V (f • Y) x = f x • Psi I M cov α V Y x := by
  have hαY : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => α y (Y y)) x :=
    mdiffAt_pairing I M hα hY
  have h_fun : (fun y => α y ((f • Y) y)) = f • (fun y => α y (Y y)) := by
    funext y
    simp [smul_eq_mul]
  have hY_T : MDiffAt (T% fun y => Y y) x := hY
  simp only [Psi]
  rw [h_fun, mvfderiv_smul hf hαY]
  rw [show (f • Y : Π x : M, TangentSpace I x) = f • (fun x => Y x) from rfl,
    cov.isCovariantDerivativeOn.leibniz hY_T hf]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.map_add,
    ContinuousLinearMap.map_smul, smul_eq_mul]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Connection.Realization.Psi_smul_right
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Connection.Realization.Psi_smul_right target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem Psi_tensorialAt_left
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (α : Π x : M, (_root_.Submission.Bundle.dual ℝ (TangentSpace I : M → Type _)) x)
    {x : M} (Y : Π x : M, TangentSpace I x) :
    TensorialAt I E (fun V => Psi I M cov α V Y x) x where
  smul := fun _ _ => Psi_smul_left I M cov α
  add := fun _ _ => Psi_add_left I M cov α

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Connection.Realization.Psi_tensorialAt_left
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Connection.Realization.Psi_tensorialAt_left target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem Psi_tensorialAt_right
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (α : Π x : M, (_root_.Submission.Bundle.dual ℝ (TangentSpace I : M → Type _)) x)
    {x : M} (hα : MDiffAtDual I M α x) (V : Π x : M, TangentSpace I x) :
    TensorialAt I E (fun Y => Psi I M cov α V Y x) x where
  smul := fun hf hY => Psi_smul_right I M cov α hα hf hY
  add := fun hY hY' => Psi_add_right I M cov α hα hY hY'

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Connection.Realization.Psi_tensorialAt_right
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Connection.Realization.Psi_tensorialAt_right target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem dual_section_mdiff
    (α : Cₛ^∞⟮I; E →L[ℝ] ℝ, (_root_.Submission.Bundle.dual ℝ (TangentSpace I : M → Type _))⟯)
    (x : M) : MDiffAtDual I M (α : Π x : M,
      (_root_.Submission.Bundle.dual ℝ (TangentSpace I : M → Type _)) x) x :=
  α.contMDiff.contMDiffAt.mdifferentiableAt (by simp)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Connection.Realization.dual_section_mdiff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Connection.Realization.dual_section_mdiff target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem vec_section_mdiff
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    MDiffAtVec I M (Y : Π x : M, TangentSpace I x) x :=
  Y.contMDiff.contMDiffAt.mdifferentiableAt (by simp)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Connection.Realization.vec_section_mdiff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Connection.Realization.vec_section_mdiff target :: scope.openDecls } }

noncomputable def dualCovariantDerivativeFun
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (α : Π x : M, (_root_.Submission.Bundle.dual ℝ (TangentSpace I : M → Type _)) x)
    (x : M) :
    TangentSpace I x →L[ℝ] (_root_.Submission.Bundle.dual ℝ (TangentSpace I : M → Type _)) x := by
  classical
  by_cases hα : MDiffAtDual I M α x
  · exact TensorialAt.mkHom₂ (F := E) (F' := E)
      (V := (TangentSpace I : M → Type _)) (V' := (TangentSpace I : M → Type _))
      (fun V Y => Psi I M cov α V Y x) x
      (fun Y _ => Psi_tensorialAt_left I M cov α Y)
      (fun V _ => Psi_tensorialAt_right I M cov α hα V)
  · exact 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.Realization.dualCovariantDerivativeFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.Realization.dualCovariantDerivativeFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.Realization.dualCovariantDerivativeFun ``Submission.DifferentialGeometry.Geometry.Connection.Realization.dualCovariantDerivativeFun

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem dualCovariantDerivativeFun_apply
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (α : Π x : M, (_root_.Submission.Bundle.dual ℝ (TangentSpace I : M → Type _)) x)
    {x : M} (hα : MDiffAtDual I M α x)
    {V Y : Π x : M, TangentSpace I x}
    (hV : MDiffAtVec I M V x) (hY : MDiffAtVec I M Y x) :
    dualCovariantDerivativeFun I M cov α x (V x) (Y x) = Psi I M cov α V Y x := by
  unfold dualCovariantDerivativeFun
  rw [dif_pos hα]
  exact TensorialAt.mkHom₂_apply
    (Φ := fun V Y => Psi I M cov α V Y x)
    (fun Y _ => Psi_tensorialAt_left I M cov α Y)
    (fun V _ => Psi_tensorialAt_right I M cov α hα V) hV hY

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Connection.Realization.dualCovariantDerivativeFun_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Connection.Realization.dualCovariantDerivativeFun_apply target :: scope.openDecls } }

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem dualCovariantDerivativeFun_of_not_mdiff
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (α : Π x : M, (_root_.Submission.Bundle.dual ℝ (TangentSpace I : M → Type _)) x)
    {x : M} (hα : ¬ MDiffAtDual I M α x) :
    dualCovariantDerivativeFun I M cov α x = 0 := by
  unfold dualCovariantDerivativeFun
  rw [dif_neg hα]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Connection.Realization.dualCovariantDerivativeFun_of_not_mdiff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Connection.Realization.dualCovariantDerivativeFun_of_not_mdiff target :: scope.openDecls } }

omit [CompleteSpace E] [SigmaCompactSpace M] in
private theorem dualCovariantDerivativeFun_isCovOn
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _)) :
    IsCovariantDerivativeOn (E →L[ℝ] ℝ)
      (dualCovariantDerivativeFun I M cov) Set.univ where
  add := by
    intro α₁ α₂ x hα₁ hα₂ _hx
    have hα₁' : MDiffAtDual I M α₁ x := hα₁
    have hα₂' : MDiffAtDual I M α₂ x := hα₂
    have hα_sum : MDiffAtDual I M (α₁ + α₂) x :=
      mdifferentiableAt_add_section (F := E →L[ℝ] ℝ) hα₁ hα₂
    ext v w
    obtain ⟨V, hVx⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
      (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x v
    obtain ⟨Y, hYx⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
      (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x w
    have hV_diff : MDiffAtVec I M (V : Π x : M, TangentSpace I x) x :=
      vec_section_mdiff I M V x
    have hY_diff : MDiffAtVec I M (Y : Π x : M, TangentSpace I x) x :=
      vec_section_mdiff I M Y x
    rw [show (v : TangentSpace I x) = (V : Π x : M, TangentSpace I x) x from hVx.symm]
    rw [show (w : TangentSpace I x) = (Y : Π x : M, TangentSpace I x) x from hYx.symm]
    rw [add_apply, add_apply]
    rw [dualCovariantDerivativeFun_apply I M cov (α₁ + α₂) hα_sum hV_diff hY_diff]
    rw [dualCovariantDerivativeFun_apply I M cov α₁ hα₁' hV_diff hY_diff]
    rw [dualCovariantDerivativeFun_apply I M cov α₂ hα₂' hV_diff hY_diff]
    have h_funeq : (fun y => (α₁ + α₂) y (Y y)) =
        (fun y => α₁ y (Y y)) + (fun y => α₂ y (Y y)) := by
      funext y
      simp [Pi.add_apply, add_apply]
    have hα₁Y : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => α₁ y (Y y)) x :=
      mdiffAt_pairing I M hα₁' hY_diff
    have hα₂Y : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => α₂ y (Y y)) x :=
      mdiffAt_pairing I M hα₂' hY_diff
    simp only [Psi]
    rw [h_funeq, mvfderiv_add hα₁Y hα₂Y]
    simp only [add_apply, Pi.add_apply]
    ring
  leibniz := by
    intro α g x hα hg _hx
    have hα' : MDiffAtDual I M α x := hα
    have hgα : MDiffAtDual I M (g • α) x :=
      hg.smul_section (F := E →L[ℝ] ℝ) hα
    ext v w
    obtain ⟨V, hVx⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
      (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x v
    obtain ⟨Y, hYx⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
      (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x w
    have hV_diff : MDiffAtVec I M (V : Π x : M, TangentSpace I x) x :=
      vec_section_mdiff I M V x
    have hY_diff : MDiffAtVec I M (Y : Π x : M, TangentSpace I x) x :=
      vec_section_mdiff I M Y x
    rw [show (v : TangentSpace I x) = (V : Π x : M, TangentSpace I x) x from hVx.symm]
    rw [show (w : TangentSpace I x) = (Y : Π x : M, TangentSpace I x) x from hYx.symm]
    rw [dualCovariantDerivativeFun_apply I M cov (g • α) hgα hV_diff hY_diff]
    change Psi I M cov (g • α) V Y x =
      g x • (dualCovariantDerivativeFun I M cov α x (V x)) (Y x) +
      ((mvfderiv (I := I) g x) (V x)) * (α x) (Y x)
    rw [dualCovariantDerivativeFun_apply I M cov α hα' hV_diff hY_diff]
    have h_funeq : (fun y => (g • α) y (Y y)) = g • (fun y => α y (Y y)) := by
      funext y
      simp [smul_apply, smul_eq_mul]
    have hαY : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => α y (Y y)) x :=
      mdiffAt_pairing I M hα' hY_diff
    simp only [Psi]
    rw [h_funeq, mvfderiv_smul hg hαY]
    have hgα_apply : (g • α) x = g x • α x := rfl
    rw [hgα_apply]
    simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul]
    ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Connection.Realization.dualCovariantDerivativeFun_isCovOn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Connection.Realization.dualCovariantDerivativeFun_isCovOn target :: scope.openDecls } }

noncomputable def dualCovariantDerivative
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _)) :
    CovariantDerivative I (E →L[ℝ] ℝ)
      (_root_.Submission.Bundle.dual ℝ (TangentSpace I : M → Type _)) where
  toFun := dualCovariantDerivativeFun I M cov
  isCovariantDerivativeOnUniv := dualCovariantDerivativeFun_isCovOn I M cov

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.Realization.dualCovariantDerivative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.Realization.dualCovariantDerivative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.Realization.dualCovariantDerivative ``Submission.DifferentialGeometry.Geometry.Connection.Realization.dualCovariantDerivative

omit [CompleteSpace E] [SigmaCompactSpace M] in
private theorem dualCov_section_smooth
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [_root_.CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (α : Cₛ^∞⟮I; E →L[ℝ] ℝ, (_root_.Submission.Bundle.dual ℝ (TangentSpace I : M → Type _))⟯)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] ℝ)
        (E := fun x : M => (TangentSpace I x →L[ℝ] (_root_.Bundle.Trivial M ℝ) x))
        x ((dualCovariantDerivativeFun I M cov α x) (Y x))) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (V₁ := TangentSpace I) (V₂ := _root_.Bundle.Trivial M ℝ)
    (φ := fun x => (dualCovariantDerivativeFun I M cov α x) (Y x))
  intro Z
  have hαZ : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y => α y (Z y)) :=
    contMDiff_dual_apply_section I M α Z
  let fαZ : C^∞⟮I, M; ℝ⟯ := ⟨_, hαZ⟩
  have h_extDeriv : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] ℝ)
        (E := fun x : M => (TangentSpace I x →L[ℝ] (_root_.Bundle.Trivial M ℝ) x))
        x (mvfderiv (I := I) (fun y => α y (Z y)) x)) := by
    have := contMDiff_mvfderiv_section I M fαZ
    simpa [fαZ] using this
  have h_extDeriv_at_Y : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x => mvfderiv (I := I) (fun y => α y (Z y)) x (Y x)) := by
    let dα : Cₛ^∞⟮I; E →L[ℝ] ℝ, (_root_.Submission.Bundle.dual ℝ (TangentSpace I : M → Type _))⟯ :=
      ⟨fun x => mvfderiv (I := I) (fun y => α y (Z y)) x, h_extDeriv⟩
    have := contMDiff_dual_apply_section I M dα Y
    simpa [dα] using this
  have h_concreteConn : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x => α x ((concreteConn I M cov Y Z) x)) :=
    contMDiff_dual_apply_section I M α (concreteConn I M cov Y Z)
  have h_α_cov : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x => α x (cov Z x (Y x))) := h_concreteConn
  have h_diff : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x => mvfderiv (I := I) (fun y => α y (Z y)) x (Y x) - α x (cov Z x (Y x))) :=
    h_extDeriv_at_Y.sub h_α_cov
  have h_eq : ∀ x, (dualCovariantDerivativeFun I M cov α x) (Y x) (Z x) =
      mvfderiv (I := I) (fun y => α y (Z y)) x (Y x) - α x (cov Z x (Y x)) := by
    intro x
    have hα := dual_section_mdiff I M α x
    have hY := vec_section_mdiff I M Y x
    have hZ := vec_section_mdiff I M Z x
    rw [dualCovariantDerivativeFun_apply I M cov α hα hY hZ]
    rfl
  intro x₀
  rw [_root_.Bundle.contMDiffAt_section]
  have h_diff_at := h_diff x₀
  refine h_diff_at.congr_of_eventuallyEq ?_
  filter_upwards with x
  rw [h_eq]
  simp [_root_.Bundle.Trivial.fiberBundle_trivializationAt']

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Connection.Realization.dualCov_section_smooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Connection.Realization.dualCov_section_smooth target :: scope.openDecls } }

noncomputable instance dualCovariantDerivative_contMDiff
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [_root_.CovariantDerivative.ContMDiffCovariantDerivative cov ∞] :
    _root_.CovariantDerivative.ContMDiffCovariantDerivative (dualCovariantDerivative I M cov) ∞ where
  contMDiff := {
    contMDiff := by
      intro α hα
      have hα_smooth : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
          (fun x => TotalSpace.mk' (E →L[ℝ] ℝ)
            (E := fun x : M => (TangentSpace I x →L[ℝ] (_root_.Bundle.Trivial M ℝ) x)) x
              (α x)) := by
        rw [show (∞ : WithTop ℕ∞) = ∞ + 1 from by simp] at hα
        rwa [← contMDiffOn_univ]
      let α_section : Cₛ^∞⟮I; E →L[ℝ] ℝ, (_root_.Submission.Bundle.dual ℝ (TangentSpace I : M → Type _))⟯ :=
        ⟨α, hα_smooth⟩
      rw [contMDiffOn_univ]
      apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
        (V₁ := TangentSpace I)
        (V₂ := _root_.Submission.Bundle.dual ℝ (TangentSpace I : M → Type _))
        (φ := fun x => dualCovariantDerivativeFun I M cov α x)
      intro Y
      exact dualCov_section_smooth I M cov α_section Y
  }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.Realization.dualCovariantDerivative_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.Realization.dualCovariantDerivative_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.Realization.dualCovariantDerivative_contMDiff ``Submission.DifferentialGeometry.Geometry.Connection.Realization.dualCovariantDerivative_contMDiff

omit [CompleteSpace E] [SigmaCompactSpace M] in
theorem dualCovariantDerivative_apply
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (α : Cₛ^∞⟮I; E →L[ℝ] ℝ, (_root_.Submission.Bundle.dual ℝ (TangentSpace I : M → Type _))⟯)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (v : TangentSpace I x) :
    (dualCovariantDerivative I M cov α x v) (Y x) =
      mvfderiv (I := I) (fun y => α y (Y y)) x v - (α x) (cov Y x v) := by
  change dualCovariantDerivativeFun I M cov α x v (Y x) = _
  obtain ⟨V, hVx⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x v
  have hα_diff := dual_section_mdiff I M α x
  have hV_diff := vec_section_mdiff I M V x
  have hY_diff := vec_section_mdiff I M Y x
  rw [show v = (V : Π x : M, TangentSpace I x) x from hVx.symm]
  rw [dualCovariantDerivativeFun_apply I M cov α hα_diff hV_diff hY_diff]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.Realization.dualCovariantDerivative_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.Realization.dualCovariantDerivative_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.Realization.dualCovariantDerivative_apply ``Submission.DifferentialGeometry.Geometry.Connection.Realization.dualCovariantDerivative_apply

end DualConnection

end

end DifferentialGeometry.Geometry.Connection.Realization
