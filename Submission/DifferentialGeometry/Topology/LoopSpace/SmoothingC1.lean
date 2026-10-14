import Submission.DifferentialGeometry.Topology.LoopSpace.SmoothingDerivatives

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Function _root_.ContinuousMap _root_.Manifold
open scoped _root_.Topology _root_.ContDiff

namespace DifferentialGeometry.Topology

variable {K F : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]




theorem smoothPeriodic_uniform_C1_approximation (Γ : C(K, freeLoop F))
    (hΓ : ∀ k, ContDiff ℝ 1 (fun t : ℝ => Γ k (t : loopCircle)))
    (hd : Continuous (fun p : K × ℝ => deriv (fun t : ℝ => Γ p.1 (t : loopCircle)) p.2))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ φ : ContDiffBump (0 : ℝ), φ.rOut < δ → ∀ k t,
      _root_.Dist.dist (DifferentialGeometry.Analysis.smoothPeriodic φ (fun s : ℝ => Γ k (s : loopCircle)) t)
        (Γ k (t : loopCircle)) < ε ∧
      _root_.Dist.dist (deriv (DifferentialGeometry.Analysis.smoothPeriodic φ (fun s : ℝ => Γ k (s : loopCircle))) t)
        (deriv (fun s : ℝ => Γ k (s : loopCircle)) t) < ε := by
  let D : K → freeLoop F := fun k => regularLoopDerivative (id : F → F) contMDiff_id
    ⟨Γ k, (hΓ k).contMDiff⟩
  have hD : Continuous D := continuous_periodicLoop_family hd _
  obtain ⟨a, ha, haΓ⟩ := smoothPeriodic_uniform_approximation Γ.uncurry.continuous hε
  obtain ⟨b, hb, hbD⟩ := smoothPeriodic_uniform_approximation
    (FreeLoop.continuous_family_iff D |>.mp hD) hε
  refine ⟨min a b, lt_min ha hb, fun φ hφ k t => ?_⟩
  refine ⟨haΓ φ (hφ.trans_le (min_le_left _ _)) k t, ?_⟩
  rw [deriv_smoothPeriodic φ (Γ k) (hΓ k)]
  exact hbD φ (hφ.trans_le (min_le_right _ _)) k t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.smoothPeriodic_uniform_C1_approximation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.smoothPeriodic_uniform_C1_approximation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.smoothPeriodic_uniform_C1_approximation ``Submission.DifferentialGeometry.Topology.smoothPeriodic_uniform_C1_approximation

end DifferentialGeometry.Topology
