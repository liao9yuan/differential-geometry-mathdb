import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CompactAncientPositive
import Submission.DifferentialGeometry.Geometry.Curvature.PositiveRicciCover
import Submission.DifferentialGeometry.Geometry.Comparison.BonnetMyers.SectionalRicci
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornGeometry

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

theorem exists_spherical_cover_of_compact_ancientKappa
    (F : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval) {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F) [CompactSpace F.M] :
    (∃ p : DifferentialGeometry.Topology.SphereThree → F.M,
      IsCoveringMap p ∧ Function.Surjective p ∧ IsLocalDiffeomorph (𝓡 3) I3 ∞ p) ∧
      ∀ x : F.M, Finite (FundamentalGroup F.M x) := by
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  have hpos := ancientKappa_curvatureOperatorPositive_of_compact F hF hdim
  have hric : positiveRicciMetric (F.S.base.metric 0) := by
    intro x v hv
    rw [metricRicciAt_apply_eq_ricciTensor]
    apply DifferentialGeometry.Geometry.Riemannian.BonnetMyers.ricci_pos_of_sec
      (F.S.base.metric 0) x (by rw [hdim]; norm_num) ?_ hv
    intro a b ha hb hab
    apply (curvatureOperatorPositiveAt_iff_sectional (F.S.base.metric 0) x hdim).mp (hpos 0 le_rfl x)
    rw [hab, zero_pow (by norm_num), sub_zero]
    exact mul_pos ((F.S.base.metric 0).pos x a ha) ((F.S.base.metric 0).pos x b hb)
  exact DifferentialGeometry.Geometry.exists_spherical_cover_of_admits_positive_ricci
    ⟨inferInstance, hF.connected, inferInstance, hdim⟩ ⟨F.S.base.metric 0, hric⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_spherical_cover_of_compact_ancientKappa then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_spherical_cover_of_compact_ancientKappa"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_spherical_cover_of_compact_ancientKappa ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_spherical_cover_of_compact_ancientKappa

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
