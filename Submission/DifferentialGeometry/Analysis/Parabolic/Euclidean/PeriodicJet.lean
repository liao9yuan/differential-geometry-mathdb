import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Algebra.Field.Periodic
import Mathlib.Topology.Order.Compact

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open _root_.Function _root_.Function.Periodic in
theorem Function.Periodic.deriv {f : ℝ → E} {c : ℝ} (hf : Function.Periodic f c) :
    Function.Periodic (deriv f) c := by
  intro x
  rw [← deriv_comp_add_const]
  exact congrArg (fun g : ℝ → E => _root_.deriv g x) (funext hf)

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.Function
  Lean.modifyEnv fun env => env.registerNamespace `Submission.Function.Periodic
  let env ← Lean.getEnv
  if env.contains `Function.Periodic.deriv then
    throwError "Refusing to shadow existing declaration Function.Periodic.deriv"
  Lean.modifyEnv fun env => Lean.addAlias env `Function.Periodic.deriv ``Submission.Function.Periodic.deriv

namespace DifferentialGeometry.Analysis.Parabolic

theorem isCompact_image_firstJet_of_periodic
    {u : ℝ → ℝ → E} {s v : ℝ}
    (hper : ∀ x t, u (x + 1) t = u x t)
    (hu : ContinuousOn (Function.uncurry u) (_root_.Set.Icc 0 1 ×ˢ _root_.Set.Icc s v))
    (hDu : ContinuousOn (fun p : ℝ × ℝ => deriv (fun y => u y p.2) p.1)
      (_root_.Set.Icc 0 1 ×ˢ _root_.Set.Icc s v)) :
    IsCompact ((fun p : ℝ × ℝ => (p.2, u p.1 p.2, deriv (fun y => u y p.2) p.1)) ''
      (_root_.Set.univ ×ˢ _root_.Set.Icc s v)) := by
  let Φ : ℝ × ℝ → ℝ × E × E :=
    fun p => (p.2, u p.1 p.2, deriv (fun y => u y p.2) p.1)
  have hΦ : ContinuousOn Φ (_root_.Set.Icc 0 1 ×ˢ _root_.Set.Icc s v) :=
    continuousOn_snd.prodMk (hu.prodMk hDu)
  have heq : Φ '' (_root_.Set.univ ×ˢ _root_.Set.Icc s v) = Φ '' (_root_.Set.Icc 0 1 ×ˢ _root_.Set.Icc s v) := by
    apply Subset.antisymm
    · rintro _ ⟨⟨x, t⟩, hxt, rfl⟩
      have hp : Function.Periodic (fun y => Φ (y, t)) 1 := by
        intro y
        dsimp only [Φ]
        rw [hper, (show Function.Periodic (fun z => u z t) 1 from fun z => hper z t).deriv y]
      obtain ⟨y, hy, hxy⟩ := hp.exists_mem_Ico₀ (by norm_num : (0 : ℝ) < 1) x
      exact ⟨(y, t), ⟨⟨hy.1, hy.2.le⟩, hxt.2⟩, hxy.symm⟩
    · exact _root_.Set.image_mono (_root_.Set.prod_mono (_root_.Set.subset_univ _) Subset.rfl)
  change IsCompact (Φ '' (_root_.Set.univ ×ˢ _root_.Set.Icc s v))
  rw [heq]
  exact (isCompact_Icc.prod _root_.CompactIccSpace.isCompact_Icc).image_of_continuousOn hΦ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.isCompact_image_firstJet_of_periodic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.isCompact_image_firstJet_of_periodic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.isCompact_image_firstJet_of_periodic ``Submission.DifferentialGeometry.Analysis.Parabolic.isCompact_image_firstJet_of_periodic

end DifferentialGeometry.Analysis.Parabolic
