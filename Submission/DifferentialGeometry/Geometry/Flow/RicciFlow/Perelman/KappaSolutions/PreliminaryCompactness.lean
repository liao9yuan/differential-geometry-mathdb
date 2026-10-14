import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedMixedComparison
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.NormalizedKLimHarnackLimit

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Set _root_.Submission.Set _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

private local instance preliminaryCompactnessC1 {D : RealTimeInterval}
    (F : PointedFlowData.{u, 0, 0} (I := I3) D) : IsManifold I3 1 F.M :=
  IsManifold.of_le (I := I3) (M := F.M) (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.preliminaryCompactnessC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.preliminaryCompactnessC1 target :: scope.openDecls } }


theorem exists_preliminary_klim_compactness
    (X : PointedFlowSeq.{u, 0, 0} (I := I3))
    (hD : X.D = ancientTimeInterval) {κ : ℝ}
    (hsource : ∀ i, KLim (I := I3) κ (X.term i))
    (hbase : ∀ i, PointedFlowScalarAtBase (I := I3) (X.term i) 1) :
    ∃ (L : PointedFlowData.{u, 0, 0} (I := I3) X.D) (phi : ℕ → ℕ),
      StrictMono phi ∧
      ∃ Phi : PointedCGHMaps (I := I3) X (L.atTime (I := I3) 0) phi,
        KLim (I := I3) κ L ∧ PointedFlowScalarAtBase (I := I3) L 1 ∧
        (∀ t : ℝ, t ≤ 0 →
          ∃ C : MetricConvergenceData (I := I3) (Phi.atTime (L := L) t),
            ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData
              (I := I3) (Phi.atTime (L := L) t) k) ∧
        ∀ a b : ℝ, a ≤ b → b ≤ 0 → ∀ K : Set L.M, IsCompact K →
          ∀ order : ℕ, ∀ ε : ℝ, 0 < ε → ∀ᶠ i in _root_.Filter.atTop,
            Nonempty (MetricComparisonOn
              (fun t => L.S.base.metric t) (fun t => (X.term (phi i)).S.base.metric t)
              (Phi.map i) K (_root_.Set.Icc a b) order ε) := by
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  obtain ⟨L, phi, hphi, Phi, hL, hbaseL, hconv⟩ :=
    exists_normalized_klim_canonical_harnack_limit X hD hdim hsource hbase
  have hcanonical (t : ℝ) (ht : t ≤ 0) :=
    hconv t (by rw [hL.carrier_eq]; exact ht)
  refine ⟨L, phi, hphi, Phi, hL, hbaseL, hcanonical, ?_⟩
  intro a b hab hb K hK order ε hε
  exact eventually_pointed_mixed_comparison Phi hsource hbase hL hcanonical
    hab hb K hK order ε hε

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_preliminary_klim_compactness then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_preliminary_klim_compactness"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_preliminary_klim_compactness ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_preliminary_klim_compactness

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
