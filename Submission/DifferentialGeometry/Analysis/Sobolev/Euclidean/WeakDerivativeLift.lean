import Submission.DifferentialGeometry.Analysis.Integration.Lp.Lifting
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.SliceWkp

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

theorem exists_lp_lift_of_weak_partials
    {Z E F : Type*} [MeasurableSpace Z]
    [NormedAddCommGroup E] [CompleteSpace E] [TopologicalSpace.SeparableSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : _root_.MeasureTheory.Measure Z} {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsOpen Ω)
    {j : E → F} (hj : Continuous j) (hinj : Function.Injective j)
    (L : _root_.MeasureTheory.Lp ℝ 2 (volume.restrict Ω) →L[ℝ] F) (A : ℝ)
    (hlift : ∀ f : _root_.MeasureTheory.Lp ℝ 2 (volume.restrict Ω), MemWkp 1 2 f Ω →
      ∃ e : E, j e = L f ∧ ‖e‖ ≤ A * (iteratedWeakSobolevNorm 1 2 f Ω).toReal)
    (P : _root_.MeasureTheory.Lp (_root_.MeasureTheory.Lp ℝ 2 (volume.restrict Ω)) 2 μ)
    (W : Fin d → _root_.MeasureTheory.Lp ℝ 2 (μ.prod (volume.restrict Ω)))
    (hweak : ∀ i, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv i
      (fun z => W i (t,z)) (P t : EuclideanSpace ℝ (Fin d) → ℝ) Ω) :
    ∃ v : _root_.MeasureTheory.Lp E 2 μ, (fun t => j (v t)) =ᵐ[μ] fun t => L (P t) := by
  obtain ⟨hP, hnorm⟩ := ae_memWkp_one_and_memLp_wkpNorm_of_lp_weak_partials hΩ P W hweak
  have hb : _root_.MeasureTheory.MemLp (fun t => A * (iteratedWeakSobolevNorm 1 2 (P t) Ω).toReal) 2 μ :=
    hnorm.const_mul A
  have hex : ∀ᵐ t ∂μ, ∃ e : E, j e = L (P t) ∧
      ‖e‖ ≤ A * (iteratedWeakSobolevNorm 1 2 (P t) Ω).toReal := by
    filter_upwards [hP] with t ht
    exact hlift (P t) ht
  obtain ⟨v, hv, _⟩ := MeasureTheory.exists_lp_lift_of_ae_exists_norm_le hj hinj
    (L.continuous.comp_aestronglyMeasurable (Lp.memLp P).1) hb hex
  exact ⟨v, hv⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_lp_lift_of_weak_partials then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_lp_lift_of_weak_partials"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_lp_lift_of_weak_partials ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_lp_lift_of_weak_partials

end DifferentialGeometry.Analysis.Sobolev.Euclidean
