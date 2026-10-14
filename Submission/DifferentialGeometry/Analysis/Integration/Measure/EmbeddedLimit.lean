import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.AEMeasurable

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.MeasureTheory _root_.Filter
open scoped _root_.Topology

namespace MeasureTheory
open _root_.MeasureTheory

open _root_.MeasureTheory in
theorem exists_ae_eq_comp_of_ae_mem_range
    {X M F : Type*} [MeasurableSpace X] {μ : _root_.MeasureTheory.Measure X} [Nonempty M]
    (Φ : M → F) {v : X → F} (hv : ∀ᵐ x ∂μ, v x ∈ _root_.Set.range Φ) :
    ∃ w : X → M, (fun x => Φ (w x)) =ᵐ[μ] v := by
  classical
  let w : X → M := fun x => if h : v x ∈ _root_.Set.range Φ then Classical.choose h else Classical.arbitrary M
  refine ⟨w, ?_⟩
  filter_upwards [hv] with x hx
  simp only [w, dif_pos hx]
  exact Classical.choose_spec hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.exists_ae_eq_comp_of_ae_mem_range then
    throwError "Refusing to shadow existing declaration MeasureTheory.exists_ae_eq_comp_of_ae_mem_range"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.exists_ae_eq_comp_of_ae_mem_range ``Submission.MeasureTheory.exists_ae_eq_comp_of_ae_mem_range

open _root_.MeasureTheory in
theorem exists_tendsto_ae_of_inducing_ae_limit
    {X M F : Type*} [MeasurableSpace X] {μ : _root_.MeasureTheory.Measure X} [TopologicalSpace M]
    [TopologicalSpace F] [Nonempty M]
    (Φ : M → F) (hΦ : _root_.Topology.IsInducing Φ)
    (u : ℕ → X → M) {v : X → F}
    (hv : ∀ᵐ x ∂μ, v x ∈ _root_.Set.range Φ)
    (hlim : ∀ᵐ x ∂μ, _root_.Filter.Tendsto (fun n => Φ (u n x)) _root_.Filter.atTop (𝓝 (v x))) :
    ∃ w : X → M, (fun x => Φ (w x)) =ᵐ[μ] v ∧
      ∀ᵐ x ∂μ, _root_.Filter.Tendsto (fun n => u n x) _root_.Filter.atTop (𝓝 (w x)) := by
  obtain ⟨w, hw⟩ := exists_ae_eq_comp_of_ae_mem_range Φ hv
  refine ⟨w, hw, ?_⟩
  filter_upwards [hw, hlim] with x hx hl
  apply hΦ.tendsto_nhds_iff.mpr
  simpa only [Function.comp_def, hx] using hl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.exists_tendsto_ae_of_inducing_ae_limit then
    throwError "Refusing to shadow existing declaration MeasureTheory.exists_tendsto_ae_of_inducing_ae_limit"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.exists_tendsto_ae_of_inducing_ae_limit ``Submission.MeasureTheory.exists_tendsto_ae_of_inducing_ae_limit

open _root_.MeasureTheory in
theorem exists_aemeasurable_tendsto_ae_of_closed_embedding_ae_limit
    {X M F : Type*} [MeasurableSpace X] {μ : _root_.MeasureTheory.Measure X}
    [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    [TopologicalSpace F] [MeasurableSpace F] [BorelSpace F] [Nonempty M]
    (Φ : M → F) (hΦ : _root_.Topology.IsClosedEmbedding Φ)
    (u : ℕ → X → M) {v : X → F} (hvm : AEMeasurable v μ)
    (hv : ∀ᵐ x ∂μ, v x ∈ _root_.Set.range Φ)
    (hlim : ∀ᵐ x ∂μ, _root_.Filter.Tendsto (fun n => Φ (u n x)) _root_.Filter.atTop (𝓝 (v x))) :
    ∃ w : X → M, AEMeasurable w μ ∧ (fun x => Φ (w x)) =ᵐ[μ] v ∧
      ∀ᵐ x ∂μ, _root_.Filter.Tendsto (fun n => u n x) _root_.Filter.atTop (𝓝 (w x)) := by
  obtain ⟨w, hw, hwl⟩ := exists_tendsto_ae_of_inducing_ae_limit Φ hΦ.isEmbedding.isInducing u hv hlim
  refine ⟨w, hΦ.measurableEmbedding.aemeasurable_comp_iff.mp ?_, hw, hwl⟩
  exact hvm.congr hw.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.exists_aemeasurable_tendsto_ae_of_closed_embedding_ae_limit then
    throwError "Refusing to shadow existing declaration MeasureTheory.exists_aemeasurable_tendsto_ae_of_closed_embedding_ae_limit"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.exists_aemeasurable_tendsto_ae_of_closed_embedding_ae_limit ``Submission.MeasureTheory.exists_aemeasurable_tendsto_ae_of_closed_embedding_ae_limit

end MeasureTheory
