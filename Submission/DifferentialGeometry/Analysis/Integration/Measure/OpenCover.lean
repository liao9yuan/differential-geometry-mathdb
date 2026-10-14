import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Compactness.Lindelof

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

set_option autoImplicit false

open _root_.Set _root_.MeasureTheory _root_.Metric

namespace MeasureTheory
open _root_.MeasureTheory

open _root_.MeasureTheory in
theorem ae_restrict_of_ae_restrict_closedBall_subset
    {X : Type*} [PseudoMetricSpace X] [SecondCountableTopology X] [MeasurableSpace X]
    {μ : _root_.MeasureTheory.Measure X} {Ω : Set X} (hΩ : IsOpen Ω) {p : X → Prop}
    (hp : ∀ c : X, ∀ r : ℝ, _root_.Metric.closedBall c r ⊆ Ω → ∀ᵐ x ∂μ.restrict (_root_.Metric.ball c r), p x) :
    ∀ᵐ x ∂μ.restrict Ω, p x := by
  classical
  have hr : ∀ c : Ω, ∃ r > 0, _root_.Metric.closedBall (c : X) r ⊆ Ω := fun c =>
    Metric.nhds_basis_closedBall.mem_iff.mp (hΩ.mem_nhds c.property)
  choose r hrpos hrsub using hr
  let U : Ω → Set X := fun c => _root_.Metric.ball c (r c)
  have hcover : Ω ⊆ ⋃ c, U c := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, _root_.Metric.mem_ball_self (hrpos _)⟩
  obtain ⟨s, hs, hsc⟩ := (HereditarilyLindelofSpace.isLindelof Ω).elim_countable_subcover
    U (fun _ => _root_.Metric.isOpen_ball) hcover
  have hu : ∀ᵐ x ∂μ.restrict (⋃ c ∈ s, U c), p x :=
    (_root_.MeasureTheory.ae_restrict_biUnion_iff U hs p).mpr fun c _ => hp c (r c) (hrsub c)
  exact _root_.MeasureTheory.ae_restrict_of_ae_restrict_of_subset hsc hu

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.ae_restrict_of_ae_restrict_closedBall_subset then
    throwError "Refusing to shadow existing declaration MeasureTheory.ae_restrict_of_ae_restrict_closedBall_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.ae_restrict_of_ae_restrict_closedBall_subset ``Submission.MeasureTheory.ae_restrict_of_ae_restrict_closedBall_subset

end MeasureTheory

end
