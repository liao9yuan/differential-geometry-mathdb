/-
Authors: Jack McCarthy
-/
import Mathlib.Topology.VectorBundle.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Bundle

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {E : B → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜 (E x)]
  [TopologicalSpace (TotalSpace F E)] [∀ x, TopologicalSpace (E x)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]

theorem continuous_zeroSection (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    {B : Type*} [TopologicalSpace B]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {E : B → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜 (E x)]
    [TopologicalSpace (_root_.Bundle.TotalSpace F E)] [∀ x, TopologicalSpace (E x)]
    [FiberBundle F E] [VectorBundle 𝕜 F E] :
    Continuous (_root_.Bundle.zeroSection F E) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨continuousAt_id, ?_⟩
  set e := _root_.FiberBundle.trivializationAt F E x₀
  have hmem : x₀ ∈ e.baseSet := _root_.FiberBundle.mem_baseSet_trivializationAt F E x₀
  have hbase : e.baseSet ∈ nhds x₀ := e.open_baseSet.mem_nhds hmem
  apply Filter.Tendsto.congr'
  · change ∀ᶠ x in nhds x₀, (fun _ => (e (_root_.Bundle.zeroSection F E x₀)).2) x =
        (fun x => (e (_root_.Bundle.zeroSection F E x)).2) x
    filter_upwards [hbase] with x hx
    rw [e.zeroSection (R := 𝕜) hmem, e.zeroSection (R := 𝕜) hx]
  · exact tendsto_const_nhds

run_cmd do
  let env ← Lean.getEnv
  if env.contains `continuous_zeroSection then
    throwError "Refusing to shadow existing declaration continuous_zeroSection"
  Lean.modifyEnv fun env => Lean.addAlias env `continuous_zeroSection ``Submission.continuous_zeroSection
