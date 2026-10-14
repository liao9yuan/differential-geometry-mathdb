import Submission.DifferentialGeometry.Analysis.FunctionalAnalysis.PiLpMap
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Analysis.Normed.Lp.PiLp

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open scoped _root_.ENNReal _root_.BigOperators

namespace MeasureTheory.Lp
open _root_.MeasureTheory _root_.MeasureTheory.Lp

variable {α ι : Type*} [MeasurableSpace α] [Fintype ι]
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {X : ι → Type*} [∀ i, NormedAddCommGroup (X i)] [∀ i, NormedSpace 𝕜 (X i)]
  (μ : Measure α)

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
private def piLpForward :
    Lp (PiLp 2 X) 2 μ →L[𝕜] PiLp 2 (fun i => _root_.MeasureTheory.Lp (X i) 2 μ) :=
  (PiLp.continuousLinearEquiv 2 𝕜 (fun i => _root_.MeasureTheory.Lp (X i) 2 μ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => (PiLp.proj (𝕜 := 𝕜) 2 X i).compLpL 2 μ)

run_cmd do
  let target := ``Submission.MeasureTheory.Lp.piLpForward
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `MeasureTheory.Lp.piLpForward target :: scope.openDecls } }

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
private theorem piLpForward_apply (u : _root_.MeasureTheory.Lp (PiLp 2 X) 2 μ) (i : ι) :
    (piLpForward (𝕜 := 𝕜) μ u i : α → X i) =ᵐ[μ] (fun a => u a i) := by
  exact (PiLp.proj (𝕜 := 𝕜) 2 X i).coeFn_compLpL u

run_cmd do
  let target := ``Submission.MeasureTheory.Lp.piLpForward_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `MeasureTheory.Lp.piLpForward_apply target :: scope.openDecls } }

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
private def piLpBackward (u : PiLp 2 (fun i => _root_.MeasureTheory.Lp (X i) 2 μ)) :
    Lp (PiLp 2 X) 2 μ :=
  (MemLp.of_eval_piLp (fun i => Lp.memLp (u i))).toLp
    (fun a => WithLp.toLp 2 (fun i => u i a))

run_cmd do
  let target := ``Submission.MeasureTheory.Lp.piLpBackward
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `MeasureTheory.Lp.piLpBackward target :: scope.openDecls } }

omit [∀ i, NormedSpace 𝕜 (X i)] in
open _root_.MeasureTheory _root_.MeasureTheory.Lp in
private theorem piLpBackward_apply (u : PiLp 2 (fun i => _root_.MeasureTheory.Lp (X i) 2 μ)) :
    (piLpBackward μ u : α → PiLp 2 X) =ᵐ[μ]
      (fun a => WithLp.toLp 2 (fun i => u i a)) :=
  MemLp.coeFn_toLp _

run_cmd do
  let target := ``Submission.MeasureTheory.Lp.piLpBackward_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `MeasureTheory.Lp.piLpBackward_apply target :: scope.openDecls } }

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
private theorem piLpBackward_forward (u : _root_.MeasureTheory.Lp (PiLp 2 X) 2 μ) :
    piLpBackward μ (piLpForward (𝕜 := 𝕜) μ u) = u := by
  apply Lp.ext
  have hf : ∀ᵐ a ∂μ, ∀ i, piLpForward (𝕜 := 𝕜) μ u i a = u a i :=
    ae_all_iff.mpr (piLpForward_apply (𝕜 := 𝕜) μ u)
  filter_upwards [piLpBackward_apply μ (piLpForward (𝕜 := 𝕜) μ u), hf] with a hb hf
  rw [hb]
  exact PiLp.ext hf

run_cmd do
  let target := ``Submission.MeasureTheory.Lp.piLpBackward_forward
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `MeasureTheory.Lp.piLpBackward_forward target :: scope.openDecls } }

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
private theorem piLpForward_backward (u : PiLp 2 (fun i => _root_.MeasureTheory.Lp (X i) 2 μ)) :
    piLpForward (𝕜 := 𝕜) μ (piLpBackward μ u) = u := by
  apply PiLp.ext
  intro i
  apply Lp.ext
  filter_upwards [piLpForward_apply (𝕜 := 𝕜) μ (piLpBackward μ u) i, piLpBackward_apply μ u] with a hf hb
  rw [hf, hb]

run_cmd do
  let target := ``Submission.MeasureTheory.Lp.piLpForward_backward
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `MeasureTheory.Lp.piLpForward_backward target :: scope.openDecls } }

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
private theorem norm_sq_eq_integral {Y : Type*} [NormedAddCommGroup Y]
    (u : _root_.MeasureTheory.Lp Y 2 μ) : ‖u‖ ^ 2 = ∫ a, ‖u a‖ ^ 2 ∂μ := by
  have h := (Lp.memLp u).eLpNorm_eq_integral_rpow_norm
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
  have hI : 0 ≤ ∫ a, ‖u a‖ ^ 2 ∂μ := _root_.MeasureTheory.integral_nonneg (fun _ => sq_nonneg _)
  rw [Lp.norm_def, h]
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_two]
  rw [← Real.sqrt_eq_rpow, ENNReal.toReal_ofReal (Real.sqrt_nonneg _), Real.sq_sqrt hI]

run_cmd do
  let target := ``Submission.MeasureTheory.Lp.norm_sq_eq_integral
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `MeasureTheory.Lp.norm_sq_eq_integral target :: scope.openDecls } }

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
private theorem integrable_norm_sq {Y : Type*} [NormedAddCommGroup Y]
    (u : _root_.MeasureTheory.Lp Y 2 μ) : _root_.MeasureTheory.Integrable (fun a => ‖u a‖ ^ 2) μ := by
  have h := (Lp.memLp u).norm_rpow
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
  simpa using (_root_.MeasureTheory.memLp_one_iff_integrable.mp h)

run_cmd do
  let target := ``Submission.MeasureTheory.Lp.integrable_norm_sq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `MeasureTheory.Lp.integrable_norm_sq target :: scope.openDecls } }

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
private theorem piLpForward_norm (u : _root_.MeasureTheory.Lp (PiLp 2 X) 2 μ) :
    ‖piLpForward (𝕜 := 𝕜) μ u‖ = ‖u‖ := by
  have hn : ‖piLpForward (𝕜 := 𝕜) μ u‖ ^ 2 = ‖u‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, norm_sq_eq_integral μ]
    simp_rw [norm_sq_eq_integral μ]
    rw [← _root_.MeasureTheory.integral_finsetSum _ (fun i _ => integrable_norm_sq μ (piLpForward (𝕜 := 𝕜) μ u i))]
    apply _root_.MeasureTheory.integral_congr_ae
    have hf : ∀ᵐ a ∂μ, ∀ i, piLpForward (𝕜 := 𝕜) μ u i a = u a i :=
      ae_all_iff.mpr (piLpForward_apply (𝕜 := 𝕜) μ u)
    filter_upwards [hf] with a ha
    simp only [ha, PiLp.norm_sq_eq_of_L2]
  nlinarith only [hn, norm_nonneg (piLpForward (𝕜 := 𝕜) μ u), norm_nonneg u]

run_cmd do
  let target := ``Submission.MeasureTheory.Lp.piLpForward_norm
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `MeasureTheory.Lp.piLpForward_norm target :: scope.openDecls } }

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
def piLpEquiv :
    _root_.MeasureTheory.Lp (PiLp 2 X) 2 μ ≃ₗᵢ[𝕜] PiLp 2 (fun i => _root_.MeasureTheory.Lp (X i) 2 μ) where
  toFun := piLpForward (𝕜 := 𝕜) μ
  invFun := piLpBackward μ
  left_inv := piLpBackward_forward (𝕜 := 𝕜) μ
  right_inv := piLpForward_backward (𝕜 := 𝕜) μ
  map_add' := map_add (piLpForward (𝕜 := 𝕜) μ)
  map_smul' := map_smul (piLpForward (𝕜 := 𝕜) μ)
  norm_map' := piLpForward_norm (𝕜 := 𝕜) μ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.Lp.piLpEquiv then
    throwError "Refusing to shadow existing declaration MeasureTheory.Lp.piLpEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.Lp.piLpEquiv ``Submission.MeasureTheory.Lp.piLpEquiv

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
theorem piLpEquiv_apply (u : _root_.MeasureTheory.Lp (PiLp 2 X) 2 μ) (i : ι) :
    (piLpEquiv (𝕜 := 𝕜) μ u i : α → X i) =ᵐ[μ] (fun a => u a i) :=
  piLpForward_apply (𝕜 := 𝕜) μ u i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.Lp.piLpEquiv_apply then
    throwError "Refusing to shadow existing declaration MeasureTheory.Lp.piLpEquiv_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.Lp.piLpEquiv_apply ``Submission.MeasureTheory.Lp.piLpEquiv_apply

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
theorem piLpEquiv_symm_apply (u : PiLp 2 (fun i => _root_.MeasureTheory.Lp (X i) 2 μ)) :
    ((piLpEquiv (𝕜 := 𝕜) μ).symm u : α → PiLp 2 X) =ᵐ[μ]
      (fun a => WithLp.toLp 2 (fun i => u i a)) :=
  piLpBackward_apply μ u

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.Lp.piLpEquiv_symm_apply then
    throwError "Refusing to shadow existing declaration MeasureTheory.Lp.piLpEquiv_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.Lp.piLpEquiv_symm_apply ``Submission.MeasureTheory.Lp.piLpEquiv_symm_apply

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
theorem piLpEquiv_apply_eq (u : _root_.MeasureTheory.Lp (PiLp 2 X) 2 μ) (i : ι) :
    piLpEquiv (𝕜 := 𝕜) μ u i = (PiLp.proj (𝕜 := 𝕜) 2 X i).compLpL 2 μ u := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.Lp.piLpEquiv_apply_eq then
    throwError "Refusing to shadow existing declaration MeasureTheory.Lp.piLpEquiv_apply_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.Lp.piLpEquiv_apply_eq ``Submission.MeasureTheory.Lp.piLpEquiv_apply_eq

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
theorem proj_comp_piLpEquiv (i : ι) :
    (PiLp.proj (𝕜 := 𝕜) 2 (fun i => _root_.MeasureTheory.Lp (X i) 2 μ) i).comp
        (piLpEquiv (𝕜 := 𝕜) (X := X) μ).toContinuousLinearEquiv.toContinuousLinearMap =
      (PiLp.proj (𝕜 := 𝕜) 2 X i).compLpL 2 μ := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.Lp.proj_comp_piLpEquiv then
    throwError "Refusing to shadow existing declaration MeasureTheory.Lp.proj_comp_piLpEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.Lp.proj_comp_piLpEquiv ``Submission.MeasureTheory.Lp.proj_comp_piLpEquiv

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
theorem compLpL_proj_piLpEquiv_symm (u : PiLp 2 (fun i => _root_.MeasureTheory.Lp (X i) 2 μ)) (i : ι) :
    (PiLp.proj (𝕜 := 𝕜) 2 X i).compLpL 2 μ ((piLpEquiv (𝕜 := 𝕜) μ).symm u) = u i := by
  rw [← piLpEquiv_apply_eq, LinearIsometryEquiv.apply_symm_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.Lp.compLpL_proj_piLpEquiv_symm then
    throwError "Refusing to shadow existing declaration MeasureTheory.Lp.compLpL_proj_piLpEquiv_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.Lp.compLpL_proj_piLpEquiv_symm ``Submission.MeasureTheory.Lp.compLpL_proj_piLpEquiv_symm

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
theorem compLpL_proj_comp_piLpEquiv_symm (i : ι) :
    ((PiLp.proj (𝕜 := 𝕜) 2 X i).compLpL 2 μ).comp
        (piLpEquiv (𝕜 := 𝕜) (X := X) μ).symm.toContinuousLinearEquiv.toContinuousLinearMap =
      PiLp.proj (𝕜 := 𝕜) 2 (fun i => _root_.MeasureTheory.Lp (X i) 2 μ) i := by
  apply ContinuousLinearMap.ext
  intro u
  exact compLpL_proj_piLpEquiv_symm (𝕜 := 𝕜) μ u i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.Lp.compLpL_proj_comp_piLpEquiv_symm then
    throwError "Refusing to shadow existing declaration MeasureTheory.Lp.compLpL_proj_comp_piLpEquiv_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.Lp.compLpL_proj_comp_piLpEquiv_symm ``Submission.MeasureTheory.Lp.compLpL_proj_comp_piLpEquiv_symm

variable {Y : ι → Type*} [∀ i, NormedAddCommGroup (Y i)] [∀ i, NormedSpace 𝕜 (Y i)]

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
theorem piLpEquiv_compLpL (L : ∀ i, X i →L[𝕜] Y i) (u : _root_.MeasureTheory.Lp (PiLp 2 X) 2 μ) :
    piLpEquiv (𝕜 := 𝕜) μ ((ContinuousLinearMap.piLpMap 2 L).compLpL 2 μ u) =
      ContinuousLinearMap.piLpMap 2 (fun i => (L i).compLpL 2 μ) (piLpEquiv (𝕜 := 𝕜) μ u) := by
  apply PiLp.ext
  intro i
  apply Lp.ext
  filter_upwards [piLpEquiv_apply (𝕜 := 𝕜) μ ((ContinuousLinearMap.piLpMap 2 L).compLpL 2 μ u) i,
    (ContinuousLinearMap.piLpMap 2 L).coeFn_compLpL u,
    (L i).coeFn_compLpL (piLpEquiv (𝕜 := 𝕜) μ u i), piLpEquiv_apply (𝕜 := 𝕜) μ u i] with a h₁ h₂ h₃ h₄
  change piLpEquiv (𝕜 := 𝕜) μ ((ContinuousLinearMap.piLpMap 2 L).compLpL 2 μ u) i a =
    ((L i).compLpL 2 μ (piLpEquiv (𝕜 := 𝕜) μ u i)) a
  rw [h₁, h₂, ContinuousLinearMap.piLpMap_apply, h₃, h₄]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.Lp.piLpEquiv_compLpL then
    throwError "Refusing to shadow existing declaration MeasureTheory.Lp.piLpEquiv_compLpL"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.Lp.piLpEquiv_compLpL ``Submission.MeasureTheory.Lp.piLpEquiv_compLpL

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
theorem piLpEquiv_symm_piLpMap (L : ∀ i, X i →L[𝕜] Y i)
    (u : PiLp 2 (fun i => _root_.MeasureTheory.Lp (X i) 2 μ)) :
    (piLpEquiv (𝕜 := 𝕜) μ).symm
        (ContinuousLinearMap.piLpMap 2 (fun i => (L i).compLpL 2 μ) u) =
      (ContinuousLinearMap.piLpMap 2 L).compLpL 2 μ ((piLpEquiv (𝕜 := 𝕜) μ).symm u) := by
  apply (piLpEquiv (𝕜 := 𝕜) μ).injective
  rw [LinearIsometryEquiv.apply_symm_apply, piLpEquiv_compLpL,
    LinearIsometryEquiv.apply_symm_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.Lp.piLpEquiv_symm_piLpMap then
    throwError "Refusing to shadow existing declaration MeasureTheory.Lp.piLpEquiv_symm_piLpMap"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.Lp.piLpEquiv_symm_piLpMap ``Submission.MeasureTheory.Lp.piLpEquiv_symm_piLpMap

end MeasureTheory.Lp

open _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.Topology _root_.ENNReal

namespace MeasureTheory.Lp
open _root_.MeasureTheory _root_.MeasureTheory.Lp

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
theorem tendsto_piLp_iff
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {Ω X ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
    (μ : _root_.MeasureTheory.Measure Ω) {l : Filter X} {f : X → _root_.MeasureTheory.Lp (PiLp 2 E) 2 μ}
    {f0 : _root_.MeasureTheory.Lp (PiLp 2 E) 2 μ} :
    _root_.Filter.Tendsto f l (𝓝 f0) ↔ ∀ i,
      Tendsto (fun x => (PiLp.proj (𝕜 := 𝕜) 2 E i).compLpL 2 μ (f x)) l
        (𝓝 ((PiLp.proj (𝕜 := 𝕜) 2 E i).compLpL 2 μ f0)) := by
  constructor
  · intro hf i
    exact ((PiLp.proj (𝕜 := 𝕜) 2 E i).compLpL 2 μ).continuous.tendsto f0 |>.comp hf
  · intro hf
    let e := piLpEquiv (𝕜 := 𝕜) (X := E) μ
    have hc (i : ι) : _root_.Filter.Tendsto (fun x => e (f x) i) l (𝓝 (e f0 i)) := hf i
    have hp : _root_.Filter.Tendsto (fun x i => e (f x) i) l (𝓝 (fun i => e f0 i)) :=
      tendsto_pi_nhds.mpr hc
    have he : _root_.Filter.Tendsto (fun x => e (f x)) l (𝓝 (e f0)) :=
      (PiLp.continuous_toLp (p := 2) (β := fun i => _root_.MeasureTheory.Lp (E i) 2 μ)).tendsto _ |>.comp hp
    have hi : _root_.Filter.Tendsto (fun x => e.symm (e (f x))) l (𝓝 (e.symm (e f0))) :=
      (e.symm.continuous.tendsto (e f0)).comp he
    simpa only [e.symm_apply_apply] using hi

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.Lp.tendsto_piLp_iff then
    throwError "Refusing to shadow existing declaration MeasureTheory.Lp.tendsto_piLp_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.Lp.tendsto_piLp_iff ``Submission.MeasureTheory.Lp.tendsto_piLp_iff

end MeasureTheory.Lp
