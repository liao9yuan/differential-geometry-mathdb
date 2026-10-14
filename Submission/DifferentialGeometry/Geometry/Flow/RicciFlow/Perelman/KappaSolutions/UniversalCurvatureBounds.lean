import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.NormalizedKLimGeometry
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.UniversalKappaGap
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.RoundFlowMixedJets

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn (I3)
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

theorem exists_universal_normalized_ancient_curvature_bounds :
    ∃ C : ℝ → ℝ, (∀ A, 0 < C A) ∧
      ∀ (kappa : ℝ) (F : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval),
        IsAncientKappaSolution kappa F → PointedFlowScalarAtBase F 1 →
          ∀ A : ℝ, ∀ y : F.M,
            riemannianEDistOf (I := I3) (F.S.base.metric 0) F.basepoint y ≤
              ENNReal.ofReal A → ∀ t : ℝ, t ≤ 0 → F.rmNormSq t y ≤ C A := by
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  obtain ⟨B, hB, hbound⟩ := exists_normalized_klim_local_curvature_constants
    (I := I3) hdim universalKappaConstant
  refine ⟨fun A => 3 * (_root_.Max.max 1 (B A)) ^ 2, fun A => by positivity, ?_⟩
  intro kappa F hF hbase A y hy t ht
  rcases ancientKappaThree_universal_kappa_gap F hF hdim with hround | huniversal
  · have hK := ancientKappaThree_toKLim F hF hdim
    have hterminal : F.S.scalar 0 y ≤ 1 := by
      rw [sphericalSpaceFormFlow_scalar_eq F hround le_rfl y F.basepoint]
      exact (show F.S.scalar 0 F.basepoint = 1 from hbase).le
    have h := hK.rmNormSq_le_of_terminal_scalar_le F hdim ht y hterminal
    exact h.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by norm_num) (le_max_left 1 (B A)) 2) (by norm_num))
  · have h := (hbound ancientTimeInterval F (ancientKappaThree_toKLim F huniversal hdim)
      hbase A y hy t ht).2
    exact h.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (hB A).le (le_max_right 1 (B A)) 2) (by norm_num))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_universal_normalized_ancient_curvature_bounds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_universal_normalized_ancient_curvature_bounds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_universal_normalized_ancient_curvature_bounds ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_universal_normalized_ancient_curvature_bounds

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
