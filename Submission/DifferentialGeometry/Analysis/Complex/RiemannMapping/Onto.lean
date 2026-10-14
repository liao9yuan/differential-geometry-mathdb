import Submission.DifferentialGeometry.External.RiemannMapping.RiemannMapExtremal
import Submission.DifferentialGeometry.Analysis.Complex.Univalent
import Mathlib.Analysis.Complex.Conformal

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

noncomputable section

open _root_.Set _root_.Metric
open scoped _root_.Topology

namespace Complex
open _root_.Complex

open _root_.Complex in
theorem riemann_mapping
    {U : Set ℂ} (hU : IsOpen U) (hsc : IsSimplyConnected U) (hproper : U ≠ _root_.Set.univ)
    {p : ℂ} (hp : p ∈ U) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, e.source = U ∧ e.target = _root_.Metric.ball 0 1 ∧ e p = 0 ∧
      DifferentiableOn ℂ e U ∧ DifferentiableOn ℂ e.symm (_root_.Metric.ball 0 1) ∧
      (∀ z ∈ U, deriv e z ≠ 0) ∧
      (∀ z ∈ _root_.Metric.ball (0 : ℂ) 1, deriv e.symm z ≠ 0) := by
  obtain ⟨f, hf, hbij, hfp⟩ := exists_bijOn_unitBall_map_eq_zero hU hsc hproper hp
  obtain ⟨e, hes, het, heq, he, hei⟩ :=
    exists_openPartialHomeomorph_of_differentiableOn_of_bijOn hU hf hbij
  refine ⟨e, hes, het, (heq p).trans hfp, hes ▸ he, het ▸ hei, ?_, ?_⟩
  · intro z hz
    exact deriv_ne_zero_of_differentiableOn_of_injOn hU (hes ▸ he)
      (hes ▸ e.injOn) hz
  · intro z hz
    exact deriv_ne_zero_of_differentiableOn_of_injOn _root_.Metric.isOpen_ball (het ▸ hei)
      (het ▸ e.symm.injOn) hz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Complex.riemann_mapping then
    throwError "Refusing to shadow existing declaration Complex.riemann_mapping"
  Lean.modifyEnv fun env => Lean.addAlias env `Complex.riemann_mapping ``Submission.Complex.riemann_mapping

open _root_.Complex in
theorem exists_biholomorphic_map_to_unit_disk
    {U : Set ℂ} (hU : IsOpen U) (hsc : IsSimplyConnected U) (hproper : U ≠ _root_.Set.univ) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, e.source = U ∧ e.target = _root_.Metric.ball 0 1 ∧
      DifferentiableOn ℂ e U ∧ DifferentiableOn ℂ e.symm (_root_.Metric.ball 0 1) ∧
      ∀ z ∈ U, deriv e z ≠ 0 := by
  obtain ⟨p, hp⟩ := hsc.nonempty
  obtain ⟨e, hes, het, _, he, hei, hne, _⟩ := riemann_mapping hU hsc hproper hp
  exact ⟨e, hes, het, he, hei, hne⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Complex.exists_biholomorphic_map_to_unit_disk then
    throwError "Refusing to shadow existing declaration Complex.exists_biholomorphic_map_to_unit_disk"
  Lean.modifyEnv fun env => Lean.addAlias env `Complex.exists_biholomorphic_map_to_unit_disk ``Submission.Complex.exists_biholomorphic_map_to_unit_disk

end Complex

end

end
