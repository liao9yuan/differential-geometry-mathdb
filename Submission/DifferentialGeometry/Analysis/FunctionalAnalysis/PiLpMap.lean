import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Operator.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open scoped _root_.ENNReal

namespace ContinuousLinearMap
open _root_.ContinuousLinearMap

section Topological

variable {𝕜 ι : Type*} [Semiring 𝕜]
  {E F : ι → Type*}
  [∀ i, AddCommGroup (E i)] [∀ i, Module 𝕜 (E i)]
  [∀ i, TopologicalSpace (E i)]
  [∀ i, AddCommGroup (F i)] [∀ i, Module 𝕜 (F i)]
  [∀ i, TopologicalSpace (F i)]

open _root_.ContinuousLinearMap in
def piLpMap (p : ℝ≥0∞) (L : ∀ i, E i →L[𝕜] F i) :
    PiLp p E →L[𝕜] PiLp p F :=
  (PiLp.continuousLinearEquiv p 𝕜 F).symm.toContinuousLinearMap.comp
    ((_root_.ContinuousLinearMap.piMap L).comp (PiLp.continuousLinearEquiv p 𝕜 E).toContinuousLinearMap)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousLinearMap.piLpMap then
    throwError "Refusing to shadow existing declaration ContinuousLinearMap.piLpMap"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousLinearMap.piLpMap ``Submission.ContinuousLinearMap.piLpMap

open _root_.ContinuousLinearMap in
@[simp] theorem piLpMap_apply (p : ℝ≥0∞) (L : ∀ i, E i →L[𝕜] F i)
    (x : PiLp p E) (i : ι) : piLpMap p L x i = L i (x i) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousLinearMap.piLpMap_apply then
    throwError "Refusing to shadow existing declaration ContinuousLinearMap.piLpMap_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousLinearMap.piLpMap_apply ``Submission.ContinuousLinearMap.piLpMap_apply

open _root_.ContinuousLinearMap in
@[simp] theorem piLpMap_id (p : ℝ≥0∞) :
    piLpMap p (fun i => ContinuousLinearMap.id 𝕜 (E i)) =
      ContinuousLinearMap.id 𝕜 (PiLp p E) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousLinearMap.piLpMap_id then
    throwError "Refusing to shadow existing declaration ContinuousLinearMap.piLpMap_id"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousLinearMap.piLpMap_id ``Submission.ContinuousLinearMap.piLpMap_id

open _root_.ContinuousLinearMap in
theorem piLpMap_comp {G : ι → Type*}
    [∀ i, AddCommGroup (G i)] [∀ i, Module 𝕜 (G i)]
    [∀ i, TopologicalSpace (G i)] (p : ℝ≥0∞)
    (K : ∀ i, F i →L[𝕜] G i) (L : ∀ i, E i →L[𝕜] F i) :
    (piLpMap p K).comp (piLpMap p L) = piLpMap p (fun i => (K i).comp (L i)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousLinearMap.piLpMap_comp then
    throwError "Refusing to shadow existing declaration ContinuousLinearMap.piLpMap_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousLinearMap.piLpMap_comp ``Submission.ContinuousLinearMap.piLpMap_comp

end Topological

section Normed

variable {𝕜 ι : Type*} [NontriviallyNormedField 𝕜] [Fintype ι]
  {E F : ι → Type*}
  [∀ i, SeminormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
  [∀ i, SeminormedAddCommGroup (F i)] [∀ i, NormedSpace 𝕜 (F i)]

open _root_.ContinuousLinearMap in
theorem piLpMap_norm_le (L : ∀ i, E i →L[𝕜] F i)
    {C : ℝ} (hC : 0 ≤ C) (hL : ∀ i x, ‖L i x‖ ≤ C * ‖x‖)
    (x : PiLp 2 E) : ‖piLpMap 2 L x‖ ≤ C * ‖x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg x))).mp
  rw [PiLp.norm_sq_eq_of_L2, mul_pow, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [piLpMap_apply]
  calc
    ‖L i (x i)‖ ^ 2 ≤ (C * ‖x i‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hL i (x i)) 2
    _ = C ^ 2 * ‖x i‖ ^ 2 := mul_pow _ _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousLinearMap.piLpMap_norm_le then
    throwError "Refusing to shadow existing declaration ContinuousLinearMap.piLpMap_norm_le"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousLinearMap.piLpMap_norm_le ``Submission.ContinuousLinearMap.piLpMap_norm_le

open _root_.ContinuousLinearMap in
theorem norm_piLpMap_le (L : ∀ i, E i →L[𝕜] F i)
    {C : ℝ} (hC : 0 ≤ C) (hL : ∀ i, ‖L i‖ ≤ C) : ‖piLpMap 2 L‖ ≤ C := by
  apply _root_.ContinuousLinearMap.opNorm_le_bound _ hC
  apply piLpMap_norm_le L hC
  intro i x
  exact (L i).le_opNorm x |>.trans (mul_le_mul_of_nonneg_right (hL i) (norm_nonneg x))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousLinearMap.norm_piLpMap_le then
    throwError "Refusing to shadow existing declaration ContinuousLinearMap.norm_piLpMap_le"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousLinearMap.norm_piLpMap_le ``Submission.ContinuousLinearMap.norm_piLpMap_le

end Normed

end ContinuousLinearMap
