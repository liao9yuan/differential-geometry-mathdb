import Mathlib.Topology.VectorBundle.Basic
import Mathlib.Topology.Homotopy.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Filter
open scoped _root_.Topology

namespace VectorBundle
open _root_.VectorBundle

section ScalarMultiplication

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : B → Type*} [∀ x, AddCommMonoid (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

open _root_.VectorBundle in
theorem continuous_totalSpace_smul :
    Continuous (fun q : 𝕜 × _root_.Bundle.TotalSpace F V =>
      (⟨q.2.proj, q.1 • q.2.snd⟩ : _root_.Bundle.TotalSpace F V)) := by
  apply continuous_iff_continuousAt.mpr
  intro q₀
  rw [FiberBundle.continuousAt_totalSpace]
  have hb : Continuous (fun q : 𝕜 × _root_.Bundle.TotalSpace F V => q.2.proj) :=
    (FiberBundle.continuous_proj F V).comp continuous_snd
  refine ⟨hb.continuousAt, ?_⟩
  let e := _root_.FiberBundle.trivializationAt F V q₀.2.proj
  have he : q₀.2.proj ∈ e.baseSet := _root_.FiberBundle.mem_baseSet_trivializationAt F V q₀.2.proj
  have hc : ContinuousAt (fun q : 𝕜 × _root_.Bundle.TotalSpace F V => (e q.2).2) q₀ :=
    ((e.toOpenPartialHomeomorph.continuousAt (e.mem_source.mpr he)).comp
      continuous_snd.continuousAt).snd
  apply (continuous_fst.continuousAt.smul hc).congr_of_eventuallyEq
  filter_upwards [hb.continuousAt.preimage_mem_nhds (e.open_baseSet.mem_nhds he)] with q hq
  exact (e.linear 𝕜 hq).map_smul q.1 q.2.snd

run_cmd do
  let env ← Lean.getEnv
  if env.contains `VectorBundle.continuous_totalSpace_smul then
    throwError "Refusing to shadow existing declaration VectorBundle.continuous_totalSpace_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `VectorBundle.continuous_totalSpace_smul ``Submission.VectorBundle.continuous_totalSpace_smul

end ScalarMultiplication

variable {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type*} [∀ x, AddCommMonoid (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]

open _root_.VectorBundle in
def zeroSectionHomotopy :
    ContinuousMap.Homotopy
      (⟨fun z : _root_.Bundle.TotalSpace F V => (⟨z.proj, 0⟩ : _root_.Bundle.TotalSpace F V),
        (Bundle.Trivialization.continuous_zeroSection ℝ).comp
          (FiberBundle.continuous_proj F V)⟩ : C(_root_.Bundle.TotalSpace F V, _root_.Bundle.TotalSpace F V))
      (ContinuousMap.id (_root_.Bundle.TotalSpace F V)) where
  toFun q := ⟨q.2.proj, (q.1 : ℝ) • q.2.snd⟩
  continuous_toFun :=
    (continuous_totalSpace_smul (𝕜 := ℝ) (F := F) (V := V)).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  map_zero_left z := by
    change (⟨z.proj, (0 : ℝ) • z.snd⟩ : _root_.Bundle.TotalSpace F V) = ⟨z.proj, 0⟩
    rw [zero_smul]
  map_one_left z := by
    change (⟨z.proj, (1 : ℝ) • z.snd⟩ : _root_.Bundle.TotalSpace F V) = z
    rw [one_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `VectorBundle.zeroSectionHomotopy then
    throwError "Refusing to shadow existing declaration VectorBundle.zeroSectionHomotopy"
  Lean.modifyEnv fun env => Lean.addAlias env `VectorBundle.zeroSectionHomotopy ``Submission.VectorBundle.zeroSectionHomotopy

end VectorBundle
