import Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Operator.L2

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Filter
open scoped _root_.NNReal

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {X Y Z W : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {T : ℝ}

private def timeResponseFun
    (L : X →L[ℝ] timeL2 Z T) (J : Z →L[ℝ] Y)
    (C : ℝ≥0) (hC : ∀ x, ∀ᵐ t ∂timeMeasure T, ‖J (L x t)‖ ≤ (C : ℝ) * ‖x‖)
    (A : ℝ → Y →L[ℝ] W) (hA : _root_.MeasureTheory.MemLp A 2 (timeMeasure T)) (x : X) : timeL2 W T :=
  timeOpL2 A hA (fun t => J (L x t))
    (J.continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable (L x)))
    (C * ‖x‖₊) (hC x)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeResponseFun
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeResponseFun target :: scope.openDecls } }

private theorem timeResponseFun_apply_ae
    (L : X →L[ℝ] timeL2 Z T) (J : Z →L[ℝ] Y)
    (C : ℝ≥0) (hC : ∀ x, ∀ᵐ t ∂timeMeasure T, ‖J (L x t)‖ ≤ (C : ℝ) * ‖x‖)
    (A : ℝ → Y →L[ℝ] W) (hA : _root_.MeasureTheory.MemLp A 2 (timeMeasure T)) (x : X) :
    timeResponseFun L J C hC A hA x =ᵐ[timeMeasure T] fun t => A t (J (L x t)) :=
  timeOpL2_apply_ae _ _ _ _ _ _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeResponseFun_apply_ae
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeResponseFun_apply_ae target :: scope.openDecls } }

private theorem timeResponseFun_add
    (L : X →L[ℝ] timeL2 Z T) (J : Z →L[ℝ] Y)
    (C : ℝ≥0) (hC : ∀ x, ∀ᵐ t ∂timeMeasure T, ‖J (L x t)‖ ≤ (C : ℝ) * ‖x‖)
    (A : ℝ → Y →L[ℝ] W) (hA : _root_.MeasureTheory.MemLp A 2 (timeMeasure T)) (x y : X) :
    timeResponseFun L J C hC A hA (x + y) =
      timeResponseFun L J C hC A hA x + timeResponseFun L J C hC A hA y := by
  apply Lp.ext
  filter_upwards [timeResponseFun_apply_ae L J C hC A hA (x + y),
    timeResponseFun_apply_ae L J C hC A hA x,
    timeResponseFun_apply_ae L J C hC A hA y,
    Lp.coeFn_add (L x) (L y),
    Lp.coeFn_add (timeResponseFun L J C hC A hA x)
      (timeResponseFun L J C hC A hA y)] with t hsum hx hy hfield hout
  rw [hsum, hout, Pi.add_apply, hx, hy, map_add L, hfield, Pi.add_apply,
    map_add J, map_add]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeResponseFun_add
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeResponseFun_add target :: scope.openDecls } }

private theorem timeResponseFun_smul
    (L : X →L[ℝ] timeL2 Z T) (J : Z →L[ℝ] Y)
    (C : ℝ≥0) (hC : ∀ x, ∀ᵐ t ∂timeMeasure T, ‖J (L x t)‖ ≤ (C : ℝ) * ‖x‖)
    (A : ℝ → Y →L[ℝ] W) (hA : _root_.MeasureTheory.MemLp A 2 (timeMeasure T)) (c : ℝ) (x : X) :
    timeResponseFun L J C hC A hA (c • x) = c • timeResponseFun L J C hC A hA x := by
  apply Lp.ext
  filter_upwards [timeResponseFun_apply_ae L J C hC A hA (c • x),
    timeResponseFun_apply_ae L J C hC A hA x,
    Lp.coeFn_smul c (L x), Lp.coeFn_smul c (timeResponseFun L J C hC A hA x)]
    with t hsmul hx hfield hout
  rw [hsmul, hout, Pi.smul_apply, hx, map_smul L, hfield, Pi.smul_apply,
    map_smul J, map_smul]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeResponseFun_smul
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeResponseFun_smul target :: scope.openDecls } }

private theorem timeResponseFun_norm_le
    (L : X →L[ℝ] timeL2 Z T) (J : Z →L[ℝ] Y)
    (C : ℝ≥0) (hC : ∀ x, ∀ᵐ t ∂timeMeasure T, ‖J (L x t)‖ ≤ (C : ℝ) * ‖x‖)
    (A : ℝ → Y →L[ℝ] W) (hA : _root_.MeasureTheory.MemLp A 2 (timeMeasure T)) (x : X) :
    ‖timeResponseFun L J C hC A hA x‖ ≤ (C : ℝ) * ‖hA.toLp A‖ * ‖x‖ := by
  apply (timeOpL2_norm_le A hA (fun t => J (L x t))
    (J.continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable (L x)))
    (C * ‖x‖₊) (hC x)).trans_eq
  simp only [NNReal.coe_mul, coe_nnnorm]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeResponseFun_norm_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeResponseFun_norm_le target :: scope.openDecls } }

private def timeResponseLin
    (L : X →L[ℝ] timeL2 Z T) (J : Z →L[ℝ] Y)
    (C : ℝ≥0) (hC : ∀ x, ∀ᵐ t ∂timeMeasure T, ‖J (L x t)‖ ≤ (C : ℝ) * ‖x‖)
    (A : ℝ → Y →L[ℝ] W) (hA : _root_.MeasureTheory.MemLp A 2 (timeMeasure T)) : X →ₗ[ℝ] timeL2 W T where
  toFun := timeResponseFun L J C hC A hA
  map_add' := timeResponseFun_add L J C hC A hA
  map_smul' := timeResponseFun_smul L J C hC A hA

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeResponseLin
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeResponseLin target :: scope.openDecls } }

def timeResponseL
    (L : X →L[ℝ] timeL2 Z T) (J : Z →L[ℝ] Y)
    (C : ℝ≥0) (hC : ∀ x, ∀ᵐ t ∂timeMeasure T, ‖J (L x t)‖ ≤ (C : ℝ) * ‖x‖)
    (A : ℝ → Y →L[ℝ] W) (hA : _root_.MeasureTheory.MemLp A 2 (timeMeasure T)) : X →L[ℝ] timeL2 W T :=
  (timeResponseLin L J C hC A hA).mkContinuous ((C : ℝ) * ‖hA.toLp A‖)
    (timeResponseFun_norm_le L J C hC A hA)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeResponseL then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeResponseL"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeResponseL ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeResponseL

theorem timeResponseL_apply_ae
    (L : X →L[ℝ] timeL2 Z T) (J : Z →L[ℝ] Y)
    (C : ℝ≥0) (hC : ∀ x, ∀ᵐ t ∂timeMeasure T, ‖J (L x t)‖ ≤ (C : ℝ) * ‖x‖)
    (A : ℝ → Y →L[ℝ] W) (hA : _root_.MeasureTheory.MemLp A 2 (timeMeasure T)) (x : X) :
    timeResponseL L J C hC A hA x =ᵐ[timeMeasure T] fun t => A t (J (L x t)) :=
  timeResponseFun_apply_ae L J C hC A hA x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeResponseL_apply_ae then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeResponseL_apply_ae"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeResponseL_apply_ae ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeResponseL_apply_ae

theorem timeResponseL_norm_le
    (L : X →L[ℝ] timeL2 Z T) (J : Z →L[ℝ] Y)
    (C : ℝ≥0) (hC : ∀ x, ∀ᵐ t ∂timeMeasure T, ‖J (L x t)‖ ≤ (C : ℝ) * ‖x‖)
    (A : ℝ → Y →L[ℝ] W) (hA : _root_.MeasureTheory.MemLp A 2 (timeMeasure T)) :
    ‖timeResponseL L J C hC A hA‖ ≤ (C : ℝ) * ‖hA.toLp A‖ :=
  LinearMap.mkContinuous_norm_le (timeResponseLin L J C hC A hA)
    (mul_nonneg C.coe_nonneg (norm_nonneg _)) (timeResponseFun_norm_le L J C hC A hA)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeResponseL_norm_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeResponseL_norm_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeResponseL_norm_le ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeResponseL_norm_le

theorem timeResponseL_sub
    (L : X →L[ℝ] timeL2 Z T) (J : Z →L[ℝ] Y)
    (C : ℝ≥0) (hC : ∀ x, ∀ᵐ t ∂timeMeasure T, ‖J (L x t)‖ ≤ (C : ℝ) * ‖x‖)
    (A B : ℝ → Y →L[ℝ] W)
    (hA : _root_.MeasureTheory.MemLp A 2 (timeMeasure T)) (hB : _root_.MeasureTheory.MemLp B 2 (timeMeasure T)) :
    timeResponseL L J C hC A hA - timeResponseL L J C hC B hB =
      timeResponseL L J C hC (A - B) (hA.sub hB) := by
  apply ContinuousLinearMap.ext
  intro x
  apply Lp.ext
  filter_upwards [timeResponseL_apply_ae L J C hC A hA x,
    timeResponseL_apply_ae L J C hC B hB x,
    timeResponseL_apply_ae L J C hC (A - B) (hA.sub hB) x,
    Lp.coeFn_sub (timeResponseL L J C hC A hA x)
      (timeResponseL L J C hC B hB x)] with t hAx hBx hsub hout
  change (timeResponseL L J C hC A hA x - timeResponseL L J C hC B hB x) t = _
  rw [hout, Pi.sub_apply, hAx, hBx, hsub]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeResponseL_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeResponseL_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeResponseL_sub ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeResponseL_sub

theorem timeResponseL_sub_norm_le
    (L : X →L[ℝ] timeL2 Z T) (J : Z →L[ℝ] Y)
    (C : ℝ≥0) (hC : ∀ x, ∀ᵐ t ∂timeMeasure T, ‖J (L x t)‖ ≤ (C : ℝ) * ‖x‖)
    (A B : ℝ → Y →L[ℝ] W)
    (hA : _root_.MeasureTheory.MemLp A 2 (timeMeasure T)) (hB : _root_.MeasureTheory.MemLp B 2 (timeMeasure T)) :
    ‖timeResponseL L J C hC A hA - timeResponseL L J C hC B hB‖ ≤
      (C : ℝ) * ‖hA.toLp A - hB.toLp B‖ := by
  rw [timeResponseL_sub]
  exact (timeResponseL_norm_le L J C hC (A - B) (hA.sub hB)).trans_eq
    (congrArg (fun a : timeL2 (Y →L[ℝ] W) T => (C : ℝ) * ‖a‖)
      (MemLp.toLp_sub hA hB))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeResponseL_sub_norm_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeResponseL_sub_norm_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeResponseL_sub_norm_le ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeResponseL_sub_norm_le

section Naturality

variable {X₁ X₂ Y₁ Y₂ Z₁ Z₂ W₁ W₂ : Type*}
  [NormedAddCommGroup X₁] [NormedSpace ℝ X₁]
  [NormedAddCommGroup X₂] [NormedSpace ℝ X₂]
  [NormedAddCommGroup Y₁] [NormedSpace ℝ Y₁]
  [NormedAddCommGroup Y₂] [NormedSpace ℝ Y₂]
  [NormedAddCommGroup Z₁] [NormedSpace ℝ Z₁]
  [NormedAddCommGroup Z₂] [NormedSpace ℝ Z₂]
  [NormedAddCommGroup W₁] [NormedSpace ℝ W₁]
  [NormedAddCommGroup W₂] [NormedSpace ℝ W₂]
  {T : ℝ}

theorem timeResponseL_compLpL
    (S : X₁ →L[ℝ] X₂) (P : Y₁ →L[ℝ] Y₂) (R : W₁ →L[ℝ] W₂)
    (L₁ : X₁ →L[ℝ] timeL2 Z₁ T) (J₁ : Z₁ →L[ℝ] Y₁)
    (C₁ : ℝ≥0)
    (hC₁ : ∀ x, ∀ᵐ t ∂timeMeasure T, ‖J₁ (L₁ x t)‖ ≤ (C₁ : ℝ) * ‖x‖)
    (A₁ : ℝ → Y₁ →L[ℝ] W₁) (hA₁ : _root_.MeasureTheory.MemLp A₁ 2 (timeMeasure T))
    (L₂ : X₂ →L[ℝ] timeL2 Z₂ T) (J₂ : Z₂ →L[ℝ] Y₂)
    (C₂ : ℝ≥0)
    (hC₂ : ∀ x, ∀ᵐ t ∂timeMeasure T, ‖J₂ (L₂ x t)‖ ≤ (C₂ : ℝ) * ‖x‖)
    (A₂ : ℝ → Y₂ →L[ℝ] W₂) (hA₂ : _root_.MeasureTheory.MemLp A₂ 2 (timeMeasure T))
    (hfield : ∀ x, ∀ᵐ t ∂timeMeasure T,
      P (J₁ (L₁ x t)) = J₂ (L₂ (S x) t))
    (hA : ∀ᵐ t ∂timeMeasure T, R.comp (A₁ t) = (A₂ t).comp P) :
    (R.compLpL 2 (timeMeasure T)).comp (timeResponseL L₁ J₁ C₁ hC₁ A₁ hA₁) =
      (timeResponseL L₂ J₂ C₂ hC₂ A₂ hA₂).comp S := by
  apply ContinuousLinearMap.ext
  intro x
  apply Lp.ext
  filter_upwards [R.coeFn_compLpL (p := 2) (μ := timeMeasure T)
      (timeResponseL L₁ J₁ C₁ hC₁ A₁ hA₁ x),
    timeResponseL_apply_ae L₁ J₁ C₁ hC₁ A₁ hA₁ x,
    timeResponseL_apply_ae L₂ J₂ C₂ hC₂ A₂ hA₂ (S x),
    hfield x, hA] with t hout h₁ h₂ hfield_t hA_t
  change (R.compLpL 2 (timeMeasure T) (timeResponseL L₁ J₁ C₁ hC₁ A₁ hA₁ x)) t =
    (timeResponseL L₂ J₂ C₂ hC₂ A₂ hA₂ (S x)) t
  rw [hout, h₁, h₂, ← hfield_t]
  exact congrArg (fun K : Y₁ →L[ℝ] W₂ => K (J₁ (L₁ x t))) hA_t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeResponseL_compLpL then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeResponseL_compLpL"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeResponseL_compLpL ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeResponseL_compLpL

end Naturality

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev

end
