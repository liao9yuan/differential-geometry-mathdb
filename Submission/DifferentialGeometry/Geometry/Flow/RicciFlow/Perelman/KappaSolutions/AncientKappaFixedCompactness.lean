import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.KLimThreeDimensionalBounded
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.StandardHarnackLimit
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BlowupConvergence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
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


def ancientPointedFlowSeq
    (X : ℕ → PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval) :
    PointedFlowSeq.{u, 0, 0} (I := I3) where
  D := ancientTimeInterval
  term := X

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientPointedFlowSeq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientPointedFlowSeq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientPointedFlowSeq ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientPointedFlowSeq


def ancientFlowSequence
    (X : ℕ → PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval) :
    FlowSequence.{u} where
  interval := fun _ => ancientTimeInterval
  term := X

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientFlowSequence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientFlowSequence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientFlowSequence ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientFlowSequence


@[simp] theorem ancientFlowSequence_atTime_zero
    (X : ℕ → PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval) :
    (ancientFlowSequence X).atTime 0 = (ancientPointedFlowSeq X).atTime (I := I3) 0 :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientFlowSequence_atTime_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientFlowSequence_atTime_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientFlowSequence_atTime_zero ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientFlowSequence_atTime_zero


theorem exists_ancientKappa_fixed_kappa_compactness {kappa : ℝ}
    (X : ℕ → PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval)
    (hX : ∀ i, IsAncientKappaSolution (I := I3) kappa (X i))
    (hbase : ∀ i, PointedFlowScalarAtBase (I := I3) (X i) 1) :
    ∃ (L : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval) (phi : ℕ → ℕ),
      StrictMono phi ∧
      ∃ Phi : PointedCGHMaps (I := I3) (ancientPointedFlowSeq X)
        (L.atTime (I := I3) 0) phi,
        IsAncientKappaSolution (I := I3) kappa L ∧
        PointedFlowScalarAtBase (I := I3) L 1 ∧
        KLim (I := I3) kappa L ∧
        (∀ t : ℝ, t ≤ 0 →
          ∃ C : MetricConvergenceData (I := I3)
            (Phi.atTime (X := ancientPointedFlowSeq X) (L := L) t),
            ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData
              (I := I3) (Phi.atTime (X := ancientPointedFlowSeq X) (L := L) t) k) ∧
        (∀ a b : ℝ, a ≤ b → b ≤ 0 → ∀ K : Set L.M, IsCompact K →
          ∀ order : ℕ, ∀ ε : ℝ, 0 < ε → ∀ᶠ i in _root_.Filter.atTop,
            Nonempty (MetricComparisonOn
              (fun t => L.S.base.metric t) (fun t => (X (phi i)).S.base.metric t)
              (Phi.map i) K (_root_.Set.Icc a b) order ε)) := by
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  obtain ⟨L, phi, hphi, Phi, hKL, hbaseL, hconv, hcmp, hanc⟩ :=
    exists_fixed_kappa_compactness (ancientPointedFlowSeq X) rfl
      (fun i => ancientKappaThree_toKLim (X i) (hX i) hdim) hbase
  exact ⟨L, phi, hphi, Phi, hanc, hbaseL, hKL, hconv, hcmp⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_ancientKappa_fixed_kappa_compactness then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_ancientKappa_fixed_kappa_compactness"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_ancientKappa_fixed_kappa_compactness ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_ancientKappa_fixed_kappa_compactness


theorem exists_ancientKappa_fixed_kappa_convergesOn {kappa : ℝ}
    (X : ℕ → PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval)
    (hX : ∀ i, IsAncientKappaSolution (I := I3) kappa (X i))
    (hbase : ∀ i, PointedFlowScalarAtBase (I := I3) (X i) 1) :
    ∃ (L : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval) (f : ℕ → ℕ),
      StrictMono f ∧ IsAncientKappaSolution (I := I3) kappa L ∧
        PointedFlowScalarAtBase (I := I3) L 1 ∧
        ∃ F : PointedRiemannianConvergenceMaps (I := I3) ((ancientFlowSequence X).atTime 0)
          (L.atTime (I := I3) 0) f, ConvergesOn F L.S := by
  obtain ⟨L, phi, hphi, Phi, hanc, hbaseL, _, _, hcmp⟩ :=
    exists_ancientKappa_fixed_kappa_compactness X hX hbase
  refine ⟨L, phi, hphi, hanc, hbaseL,
    Phi.atTime (X := ancientPointedFlowSeq X) (L := L) 0, ?_⟩
  intro K hK a b hab hsub order eps heps
  have hb0 : b ≤ 0 := by
    have hb := hsub (Set.right_mem_Icc.mpr hab)
    simpa only [ancientTimeInterval_carrier, Set.mem_Iic] using hb
  obtain ⟨k0, hk0⟩ := Phi.source_subset hK
  filter_upwards [hcmp a b hab hb0 K hK order eps heps,
    _root_.Filter.eventually_ge_atTop k0] with i hi hik
  exact ⟨hsub, hk0 i hik, hi⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_ancientKappa_fixed_kappa_convergesOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_ancientKappa_fixed_kappa_convergesOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_ancientKappa_fixed_kappa_convergesOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_ancientKappa_fixed_kappa_convergesOn


theorem ancientKappa_fixed_kappa_compactness_of_capture {kappa : ℝ}
    (_hkappa : 0 < kappa)
    (X : ℕ → PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval)
    (hX : ∀ i, IsAncientKappaSolution (I := I3) kappa (X i))
    (hbase : ∀ i, PointedFlowScalarAtBase (I := I3) (X i) 1)
    (hcapture : ∀ (L : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval)
      (f : ℕ → ℕ) (F : PointedRiemannianConvergenceMaps (I := I3)
        ((ancientFlowSequence X).atTime 0) (L.atTime (I := I3) 0) f),
      IsAncientKappaSolution (I := I3) kappa L → ConvergesOn F L.S →
        MetricSourceCapture F) :
    ∃ (L : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval) (f : ℕ → ℕ),
      StrictMono f ∧ IsAncientKappaSolution (I := I3) kappa L ∧
        PointedFlowScalarAtBase (I := I3) L 1 ∧
        ∃ F : PointedRiemannianConvergenceMaps (I := I3) ((ancientFlowSequence X).atTime 0)
          (L.atTime (I := I3) 0) f, MetricSourceCapture F ∧ ConvergesOn F L.S := by
  obtain ⟨L, f, hf, hanc, hbaseL, F, hconv⟩ :=
    exists_ancientKappa_fixed_kappa_convergesOn X hX hbase
  exact ⟨L, f, hf, hanc, hbaseL, F, hcapture L f F hanc hconv, hconv⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_fixed_kappa_compactness_of_capture then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_fixed_kappa_compactness_of_capture"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_fixed_kappa_compactness_of_capture ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_fixed_kappa_compactness_of_capture


private theorem chapter25_fixed_kappa_compactness_slot {kappa : ℝ} (hkappa : 0 < kappa)
    (X : ℕ → PointedFlowData.{u, 0, 0} I3 ancientTimeInterval)
    (hX : ∀ i, IsAncientKappaSolution kappa (X i))
    (hbase : ∀ i, PointedFlowScalarAtBase (X i) 1)
    (hcapture : ∀ (L : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval)
      (f : ℕ → ℕ) (F : PointedRiemannianConvergenceMaps (I := I3)
        ((ancientFlowSequence X).atTime 0) (L.atTime (I := I3) 0) f),
      IsAncientKappaSolution (I := I3) kappa L → ConvergesOn F L.S →
        MetricSourceCapture F) :
    ∃ (L : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval)
      (f : ℕ → ℕ), StrictMono f ∧ IsAncientKappaSolution kappa L ∧
        PointedFlowScalarAtBase L 1 ∧
        ∃ F : PointedRiemannianConvergenceMaps
          (({ interval := fun _ => ancientTimeInterval, term := X } : FlowSequence).atTime 0)
          (L.atTime 0) f, MetricSourceCapture F ∧ ConvergesOn F L.S :=
  ancientKappa_fixed_kappa_compactness_of_capture hkappa X hX hbase hcapture

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.chapter25_fixed_kappa_compactness_slot
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.chapter25_fixed_kappa_compactness_slot target :: scope.openDecls } }

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
