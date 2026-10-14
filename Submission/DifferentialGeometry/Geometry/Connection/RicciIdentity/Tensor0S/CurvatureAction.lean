import Submission.DifferentialGeometry.Geometry.Operator.Laplacian.Rough
import Submission.DifferentialGeometry.Geometry.Curvature.Sections.Connection

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

open _root_.Submission.DifferentialGeometry.Geometry.Operator
namespace DifferentialGeometry.Tensor.RSTensor

open _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.ContDiff _root_.BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def oneFormAtSlot0S {x : M} {s : ℕ}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (slots : Fin s → TangentSpace I x) (q : Fin s) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x :=
  dualToCotangent (I := I)
    { toFun := fun W : TangentSpace I x => alpha (Function.update slots q W)
      map_add' := by
        intro A B
        exact alpha.map_update_add slots q A B
      map_smul' := by
        intro c A
        rw [alpha.map_update_smul]
        simp [smul_eq_mul] }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.RSTensor.oneFormAtSlot0S then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.RSTensor.oneFormAtSlot0S"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.RSTensor.oneFormAtSlot0S ``Submission.DifferentialGeometry.Tensor.RSTensor.oneFormAtSlot0S

abbrev freezeSlot0SAt {x : M} {s : ℕ}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (slots : Fin s → TangentSpace I x) (q : Fin s) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x :=
  oneFormAtSlot0S (I := I) alpha slots q

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.RSTensor.freezeSlot0SAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.RSTensor.freezeSlot0SAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.RSTensor.freezeSlot0SAt ``Submission.DifferentialGeometry.Tensor.RSTensor.freezeSlot0SAt

@[simp] theorem oneFormAtSlot0S_apply {x : M} {s : ℕ}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (slots : Fin s → TangentSpace I x) (q : Fin s) (W : TangentSpace I x) :
    oneFormAtSlot0S (I := I) alpha slots q (fun _ : Fin 1 => W) =
      alpha (Function.update slots q W) := by
  change Tensor0SSpace.eval
      (dualToCotangent (I := I)
        { toFun := fun W : TangentSpace I x => alpha (Function.update slots q W)
          map_add' := by
            intro A B
            exact alpha.map_update_add slots q A B
          map_smul' := by
            intro c A
            rw [alpha.map_update_smul]
            simp [smul_eq_mul] })
      (fun _ : Fin 1 => W) = alpha (Function.update slots q W)
  exact dualToCotangent_apply _ W

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.RSTensor.oneFormAtSlot0S_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.RSTensor.oneFormAtSlot0S_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.RSTensor.oneFormAtSlot0S_apply ``Submission.DifferentialGeometry.Tensor.RSTensor.oneFormAtSlot0S_apply

def curvatureAction0SAtSlots {x : M} {s : ℕ}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (slots : Fin s → TangentSpace I x)
    (Rslot : Fin s → TangentSpace I x) : Real :=
  -∑ q : Fin s, alpha (Function.update slots q (Rslot q))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.RSTensor.curvatureAction0SAtSlots then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.RSTensor.curvatureAction0SAtSlots"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.RSTensor.curvatureAction0SAtSlots ``Submission.DifferentialGeometry.Tensor.RSTensor.curvatureAction0SAtSlots

def curvatureAction0SOperatorAt {x : M} {s : ℕ}
    (R :
      TangentSpace I x → TangentSpace I x → TangentSpace I x →
        TangentSpace I x)
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (X Y : TangentSpace I x) (slots : Fin s → TangentSpace I x) : Real :=
  curvatureAction0SAtSlots (I := I) alpha slots
    (fun q : Fin s => R X Y (slots q))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.RSTensor.curvatureAction0SOperatorAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.RSTensor.curvatureAction0SOperatorAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.RSTensor.curvatureAction0SOperatorAt ``Submission.DifferentialGeometry.Tensor.RSTensor.curvatureAction0SOperatorAt

def curvatureAction0SAt
    (Rm13 : Tensor13Section (I := I) (M := M))
    {x : M} {s : ℕ}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (X Y : TangentSpace I x) (slots : Fin s → TangentSpace I x) : Real :=
  -∑ q : Fin s,
    Rm13 x (oneFormAtSlot0S (I := I) alpha slots q)
      (vec3 X Y (slots q))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.RSTensor.curvatureAction0SAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.RSTensor.curvatureAction0SAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.RSTensor.curvatureAction0SAt ``Submission.DifferentialGeometry.Tensor.RSTensor.curvatureAction0SAt

def torsionCorrection0SAt {x : M} {s : ℕ}
    (nablaAlpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + 1) x)
    (T : TangentSpace I x) (slots : Fin s → TangentSpace I x) : Real :=
  nablaAlpha (Fin.cons T slots)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.RSTensor.torsionCorrection0SAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.RSTensor.torsionCorrection0SAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.RSTensor.torsionCorrection0SAt ``Submission.DifferentialGeometry.Tensor.RSTensor.torsionCorrection0SAt

def Tensor0SRicciIdentityAt
    (Rm13 : Tensor13Section (I := I) (M := M))
    {x : M} {s : ℕ}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + 2) x) :
    Prop :=
  ∀ X Y : TangentSpace I x, ∀ slots : Fin s → TangentSpace I x,
    nabla2Alpha (metricTraceInput (I := I) X Y slots) -
        nabla2Alpha (metricTraceInput (I := I) Y X slots) =
      curvatureAction0SAt (I := I) Rm13 alpha X Y slots

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.RSTensor.Tensor0SRicciIdentityAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.RSTensor.Tensor0SRicciIdentityAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.RSTensor.Tensor0SRicciIdentityAt ``Submission.DifferentialGeometry.Tensor.RSTensor.Tensor0SRicciIdentityAt

def Tensor0SRicciIdentityWithTorsionAt
    (Rm13 : Tensor13Section (I := I) (M := M))
    {x : M} {s : ℕ}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (nablaAlpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + 1) x)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + 2) x)
    (torsion : TangentSpace I x → TangentSpace I x → TangentSpace I x) :
    Prop :=
  ∀ X Y : TangentSpace I x, ∀ slots : Fin s → TangentSpace I x,
    nabla2Alpha (metricTraceInput (I := I) X Y slots) -
        nabla2Alpha (metricTraceInput (I := I) Y X slots) =
      curvatureAction0SAt (I := I) Rm13 alpha X Y slots -
        torsionCorrection0SAt (I := I) nablaAlpha (torsion X Y) slots

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.RSTensor.Tensor0SRicciIdentityWithTorsionAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.RSTensor.Tensor0SRicciIdentityWithTorsionAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.RSTensor.Tensor0SRicciIdentityWithTorsionAt ``Submission.DifferentialGeometry.Tensor.RSTensor.Tensor0SRicciIdentityWithTorsionAt

@[simp] theorem oneFormAtSlot0S_fin1_eq {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (slots : Fin 1 → TangentSpace I x) :
    oneFormAtSlot0S (I := I) alpha slots 0 = alpha := by
  ext v
  have hv : (fun _ : Fin 1 => v 0) = v := by
    funext q
    fin_cases q
    rfl
  rw [← hv, oneFormAtSlot0S_apply]
  have hupdate :
      Function.update slots (0 : Fin 1) (v 0) = fun _ : Fin 1 => v 0 := by
    funext q
    fin_cases q
    simp
  simp [hupdate]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.RSTensor.oneFormAtSlot0S_fin1_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.RSTensor.oneFormAtSlot0S_fin1_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.RSTensor.oneFormAtSlot0S_fin1_eq ``Submission.DifferentialGeometry.Tensor.RSTensor.oneFormAtSlot0S_fin1_eq

theorem curvatureAction0SAt_eq_slots_of_apply
    (Rm13 : Tensor13Section (I := I) (M := M))
    {x : M} {s : ℕ}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (X Y : TangentSpace I x) (slots : Fin s → TangentSpace I x)
    (Rslot : Fin s → TangentSpace I x)
    (hR : ∀ q : Fin s,
      Rm13 x (oneFormAtSlot0S (I := I) alpha slots q)
          (vec3 X Y (slots q)) =
        alpha (Function.update slots q (Rslot q))) :
    curvatureAction0SAt (I := I) Rm13 alpha X Y slots =
      curvatureAction0SAtSlots (I := I) alpha slots Rslot := by
  change
    -∑ q : Fin s,
      Rm13 x (oneFormAtSlot0S (I := I) alpha slots q)
        (vec3 X Y (slots q)) =
    -∑ q : Fin s, alpha (Function.update slots q (Rslot q))
  congr 1
  refine Finset.sum_congr rfl ?_
  intro q _
  exact hR q

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.RSTensor.curvatureAction0SAt_eq_slots_of_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.RSTensor.curvatureAction0SAt_eq_slots_of_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.RSTensor.curvatureAction0SAt_eq_slots_of_apply ``Submission.DifferentialGeometry.Tensor.RSTensor.curvatureAction0SAt_eq_slots_of_apply

theorem curvatureAction0SAt_eq_operator_of_apply
    (Rm13 : Tensor13Section (I := I) (M := M))
    {x : M} {s : ℕ}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (R :
      TangentSpace I x → TangentSpace I x → TangentSpace I x →
        TangentSpace I x)
    (X Y : TangentSpace I x) (slots : Fin s → TangentSpace I x)
    (hR : ∀ q : Fin s,
      Rm13 x (oneFormAtSlot0S (I := I) alpha slots q)
          (vec3 X Y (slots q)) =
        alpha (Function.update slots q (R X Y (slots q)))) :
    curvatureAction0SAt (I := I) Rm13 alpha X Y slots =
      curvatureAction0SOperatorAt (I := I) R alpha X Y slots := by
  simpa [curvatureAction0SOperatorAt] using
    curvatureAction0SAt_eq_slots_of_apply (I := I) Rm13 alpha X Y slots
      (fun q : Fin s => R X Y (slots q)) hR

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.RSTensor.curvatureAction0SAt_eq_operator_of_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.RSTensor.curvatureAction0SAt_eq_operator_of_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.RSTensor.curvatureAction0SAt_eq_operator_of_apply ``Submission.DifferentialGeometry.Tensor.RSTensor.curvatureAction0SAt_eq_operator_of_apply

theorem curvatureAction0SAt_eq_slots_connectionRiemannCurvature
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    {Rm13 : Tensor13Section (I := I) (M := M)}
    {s : ℕ} {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (Xsec Ysec : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (Vsec : Fin s → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (hRm13 : rm13RealizesConnection (I := I) cov Rm13) :
    curvatureAction0SAt (I := I) Rm13 alpha (Xsec x) (Ysec x)
        (fun q : Fin s => Vsec q x) =
      curvatureAction0SAtSlots (I := I) alpha (fun q : Fin s => Vsec q x)
        (fun q : Fin s =>
          (connectionRiemannCurvatureField (I := I) cov
            (fun p : M => Xsec p) (fun p : M => Ysec p)
            (fun p : M => Vsec q p)) x) := by
  refine curvatureAction0SAt_eq_slots_of_apply
    (I := I) Rm13 alpha (Xsec x) (Ysec x) (fun q : Fin s => Vsec q x)
    (fun q : Fin s =>
      (connectionRiemannCurvatureField (I := I) cov
        (fun p : M => Xsec p) (fun p : M => Ysec p)
        (fun p : M => Vsec q p)) x) ?_
  intro q
  have hRm := hRm13 Xsec Ysec (Vsec q) x
    (oneFormAtSlot0S (I := I) alpha (fun r : Fin s => Vsec r x) q)
  simpa [cotangentToDual_apply, oneFormAtSlot0S_apply] using hRm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.RSTensor.curvatureAction0SAt_eq_slots_connectionRiemannCurvature then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.RSTensor.curvatureAction0SAt_eq_slots_connectionRiemannCurvature"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.RSTensor.curvatureAction0SAt_eq_slots_connectionRiemannCurvature ``Submission.DifferentialGeometry.Tensor.RSTensor.curvatureAction0SAt_eq_slots_connectionRiemannCurvature

theorem curvatureAction0SAt_eq_neg_sum_connectionRiemannCurvature
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    {Rm13 : Tensor13Section (I := I) (M := M)}
    {s : ℕ} {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (Xsec Ysec : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (Vsec : Fin s → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (hRm13 : rm13RealizesConnection (I := I) cov Rm13) :
    curvatureAction0SAt (I := I) Rm13 alpha (Xsec x) (Ysec x)
        (fun q : Fin s => Vsec q x) =
      -∑ q : Fin s,
        alpha
          (Function.update (fun r : Fin s => Vsec r x) q
            ((connectionRiemannCurvatureField (I := I) cov
              (fun p : M => Xsec p) (fun p : M => Ysec p)
              (fun p : M => Vsec q p)) x)) := by
  simpa [curvatureAction0SAtSlots] using
    curvatureAction0SAt_eq_slots_connectionRiemannCurvature
      (I := I) (cov := cov) (Rm13 := Rm13)
      alpha Xsec Ysec Vsec hRm13

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.RSTensor.curvatureAction0SAt_eq_neg_sum_connectionRiemannCurvature then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.RSTensor.curvatureAction0SAt_eq_neg_sum_connectionRiemannCurvature"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.RSTensor.curvatureAction0SAt_eq_neg_sum_connectionRiemannCurvature ``Submission.DifferentialGeometry.Tensor.RSTensor.curvatureAction0SAt_eq_neg_sum_connectionRiemannCurvature

end DifferentialGeometry.Tensor.RSTensor
