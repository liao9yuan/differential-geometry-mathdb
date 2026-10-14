import Mathlib.MeasureTheory.Function.L1Space.Integrable

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Filter
open scoped _root_.Topology

namespace MeasureTheory
open _root_.MeasureTheory

open _root_.MeasureTheory in
theorem integrable_of_dominated_convergence
    {ι α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : _root_.MeasureTheory.Measure α} {l : Filter ι} [l.IsCountablyGenerated] [_root_.Filter.NeBot l]
    {F : ι → α → E} {f : α → E} (bound : α → ℝ)
    (hF : ∀ᶠ i in l, _root_.MeasureTheory.AEStronglyMeasurable (F i) μ)
    (hbound : ∀ᶠ i in l, ∀ᵐ x ∂μ, ‖F i x‖ ≤ bound x)
    (hbound_int : _root_.MeasureTheory.Integrable bound μ)
    (hlim : ∀ᵐ x ∂μ, _root_.Filter.Tendsto (fun i => F i x) l (𝓝 (f x))) :
    Integrable f μ := by
  obtain ⟨u, hu⟩ := l.exists_seq_tendsto
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hu.eventually (hF.and hbound))
  have hseq : _root_.Filter.Tendsto (fun n => u (n + N)) _root_.Filter.atTop l :=
    hu.comp (_root_.Filter.tendsto_add_atTop_nat N)
  have hmeas : ∀ n, _root_.MeasureTheory.AEStronglyMeasurable (F (u (n + N))) μ :=
    fun n => (hN (n + N) (Nat.le_add_left N n)).1
  have hdom : ∀ n, ∀ᵐ x ∂μ, ‖F (u (n + N)) x‖ ≤ bound x :=
    fun n => (hN (n + N) (Nat.le_add_left N n)).2
  have hconv : ∀ᵐ x ∂μ,
      Tendsto (fun n => F (u (n + N)) x) _root_.Filter.atTop (𝓝 (f x)) :=
    hlim.mono fun x hx => hx.comp hseq
  exact ⟨aestronglyMeasurable_of_tendsto_ae _root_.Filter.atTop hmeas hconv,
    _root_.MeasureTheory.hasFiniteIntegral_of_dominated_convergence hbound_int.hasFiniteIntegral hdom hconv⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.integrable_of_dominated_convergence then
    throwError "Refusing to shadow existing declaration MeasureTheory.integrable_of_dominated_convergence"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.integrable_of_dominated_convergence ``Submission.MeasureTheory.integrable_of_dominated_convergence

end MeasureTheory
