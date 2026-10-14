import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Compactness.Lindelof

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Filter _root_.MeasureTheory _root_.Set
open scoped _root_.Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {μ : Measure E} [μ.IsAddHaarMeasure]

open _root_.LocallyLipschitzOn in
theorem LocallyLipschitzOn.ae_differentiableWithinAt_of_mem
    {f : E → F} {Ω : Set E} (hf : LocallyLipschitzOn Ω f) :
    ∀ᵐ x ∂μ, x ∈ Ω → DifferentiableWithinAt ℝ f Ω x := by
  have hlocal (x : Ω) : ∃ V : Set E, IsOpen V ∧ x.1 ∈ V ∧
      ∀ᵐ y ∂μ, y ∈ V ∩ Ω → DifferentiableWithinAt ℝ f Ω y := by
    obtain ⟨K, T, hT, hK⟩ := hf x.2
    obtain ⟨W, hW, hWT⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hT
    obtain ⟨V, hVW, hV, hxV⟩ := mem_nhds_iff.mp hW
    have hLip : LipschitzOnWith K f (V ∩ Ω) :=
      hK.mono (fun y hy => hWT ⟨hVW hy.1, hy.2⟩)
    refine ⟨V, hV, hxV, ?_⟩
    filter_upwards [hLip.ae_differentiableWithinAt_of_mem (μ := μ)] with y hy
    intro hyV
    exact (hy hyV).mono_of_mem_nhdsWithin
      (_root_.Filter.inter_mem (mem_nhdsWithin_of_mem_nhds (hV.mem_nhds hyV.1)) self_mem_nhdsWithin)
  choose V hV hxV hdiff using hlocal
  obtain ⟨S, hS, hcover⟩ := (HereditarilyLindelofSpace.isLindelof Ω).elim_countable_subcover
    V hV (fun x hx => _root_.Set.mem_iUnion_of_mem ⟨x, hx⟩ (hxV ⟨x, hx⟩))
  have hcommon : ∀ᵐ y ∂μ, ∀ x ∈ S, y ∈ V x ∩ Ω → DifferentiableWithinAt ℝ f Ω y :=
    (_root_.MeasureTheory.ae_ball_iff hS).mpr (fun x _ => hdiff x)
  filter_upwards [hcommon] with y hy
  intro hyΩ
  obtain ⟨x, hx, hyV⟩ := mem_iUnion₂.mp (hcover hyΩ)
  exact hy x hx ⟨hyV, hyΩ⟩

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.LocallyLipschitzOn
  let env ← Lean.getEnv
  if env.contains `LocallyLipschitzOn.ae_differentiableWithinAt_of_mem then
    throwError "Refusing to shadow existing declaration LocallyLipschitzOn.ae_differentiableWithinAt_of_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `LocallyLipschitzOn.ae_differentiableWithinAt_of_mem ``Submission.LocallyLipschitzOn.ae_differentiableWithinAt_of_mem

open _root_.LocallyLipschitzOn in
theorem LocallyLipschitzOn.ae_differentiableWithinAt
    {f : E → F} {Ω : Set E} (hf : LocallyLipschitzOn Ω f) (hΩ : MeasurableSet Ω) :
    ∀ᵐ x ∂μ.restrict Ω, DifferentiableWithinAt ℝ f Ω x :=
  (_root_.MeasureTheory.ae_restrict_iff' hΩ).mpr hf.ae_differentiableWithinAt_of_mem

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LocallyLipschitzOn.ae_differentiableWithinAt then
    throwError "Refusing to shadow existing declaration LocallyLipschitzOn.ae_differentiableWithinAt"
  Lean.modifyEnv fun env => Lean.addAlias env `LocallyLipschitzOn.ae_differentiableWithinAt ``Submission.LocallyLipschitzOn.ae_differentiableWithinAt

open _root_.LocallyLipschitzOn in
theorem LocallyLipschitzOn.ae_differentiableAt
    {f : E → F} {Ω : Set E} (hf : LocallyLipschitzOn Ω f) (hΩ : IsOpen Ω) :
    ∀ᵐ x ∂μ.restrict Ω, DifferentiableAt ℝ f x := by
  filter_upwards [hf.ae_differentiableWithinAt hΩ.measurableSet,
    _root_.MeasureTheory.ae_restrict_mem hΩ.measurableSet] with x hx hxΩ
  exact hx.differentiableAt (hΩ.mem_nhds hxΩ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LocallyLipschitzOn.ae_differentiableAt then
    throwError "Refusing to shadow existing declaration LocallyLipschitzOn.ae_differentiableAt"
  Lean.modifyEnv fun env => Lean.addAlias env `LocallyLipschitzOn.ae_differentiableAt ``Submission.LocallyLipschitzOn.ae_differentiableAt
