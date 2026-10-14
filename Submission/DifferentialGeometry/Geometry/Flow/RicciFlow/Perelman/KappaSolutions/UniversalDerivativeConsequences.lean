import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.RoundFlowMixedJets
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.UniversalScalarDifferentialBounds
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.UniversalDerivativesJetBridge

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.Submission.ContDiff

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle


theorem exists_universal_scalarDifferentialBounds_unconditional :
    ∃ η : ℝ, 1 ≤ η ∧
      ∀ (kappa : ℝ) (F : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval),
        IsAncientKappaSolution (I := I3) kappa F → ScalarDifferentialBounds F η := by
  obtain ⟨C₀, _, h00⟩ := exists_universal_mixed_jet_bound_unconditional.{u} 0 0
  obtain ⟨C₁, _, h10⟩ := exists_universal_mixed_jet_bound_unconditional.{u} 1 0
  obtain ⟨C₂, _, h20⟩ := exists_universal_mixed_jet_bound_unconditional.{u} 2 0
  exact exists_universal_scalarDifferentialBounds h00 h10 h20

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_universal_scalarDifferentialBounds_unconditional then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_universal_scalarDifferentialBounds_unconditional"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_universal_scalarDifferentialBounds_unconditional ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_universal_scalarDifferentialBounds_unconditional


theorem ancientKappa_scalar_scale_comparison_universal :
    ∃ η : ℝ, 1 ≤ η ∧
      ∀ (kappa : ℝ) (F : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval),
        IsAncientKappaSolution (I := I3) kappa F → ∀ t ≤ (0 : ℝ),
          (∀ x y : F.M, riemannianEDistOf (I := I3) (F.S.base.metric t) x y ≤
              ENNReal.ofReal (η⁻¹ / Real.sqrt (F.S.scalar t x)) →
            4 / 9 * F.S.scalar t x ≤ F.S.scalar t y ∧
              F.S.scalar t y ≤ 4 * F.S.scalar t x) ∧
          (∀ x : F.M, ∀ s ∈ _root_.Set.Icc (t - (2 * η * F.S.scalar t x)⁻¹) t,
            2 / 3 * F.S.scalar t x ≤ F.S.scalar s x ∧
              F.S.scalar s x ≤ F.S.scalar t x) := by
  obtain ⟨C₀, _, h00⟩ := exists_universal_mixed_jet_bound_unconditional.{u} 0 0
  obtain ⟨C₁, _, h10⟩ := exists_universal_mixed_jet_bound_unconditional.{u} 1 0
  obtain ⟨C₂, _, h20⟩ := exists_universal_mixed_jet_bound_unconditional.{u} 2 0
  exact ancientKappa_scalar_scale_comparison_of_universal h00 h10 h20

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_scalar_scale_comparison_universal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_scalar_scale_comparison_universal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_scalar_scale_comparison_universal ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_scalar_scale_comparison_universal


theorem exists_kappa_universal_derivatives (a b : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ kappa : ℝ, 0 < kappa →
      ∀ P : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval,
        IsAncientKappaSolution (I := I3) kappa P → PointedFlowScalarAtBase P 1 →
        ∀ J : MixedCurvatureJet P.S, J.norm a b 0 P.basepoint ≤ C := by
  obtain ⟨C₁, _, hround⟩ := exists_round_mixed_jet_bound.{u} a b
  exact exists_kappa_universal_derivatives_of_round a b hround

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_kappa_universal_derivatives then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_kappa_universal_derivatives"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_kappa_universal_derivatives ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_kappa_universal_derivatives

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
