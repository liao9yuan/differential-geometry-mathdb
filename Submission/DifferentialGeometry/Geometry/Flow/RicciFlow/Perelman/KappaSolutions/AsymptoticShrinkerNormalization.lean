import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BackwardSliceNormalized
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientReducedVolumeConvergence
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientReducedVolumeMonotonicity

import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BackwardSliceSequence
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ReducedVolumeNormalization
import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.Construction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry.Geometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance normalizedSourceTopology : TopologicalSpace F.M := F.topology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedSourceTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedSourceTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedSourceTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedSourceTopology
local instance normalizedSourceCharted : ChartedSpace H F.M := F.charted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedSourceCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedSourceCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedSourceCharted ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedSourceCharted
local instance normalizedSourceSmooth : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedSourceSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedSourceSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedSourceSmooth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedSourceSmooth
local instance normalizedSourceT2 : T2Space F.M := F.t2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedSourceT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedSourceT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedSourceT2 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedSourceT2
local instance normalizedSourceSigma : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedSourceSigma then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedSourceSigma"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedSourceSigma ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedSourceSigma


attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

theorem exists_samePole_normalized_asymptotic_shrinker
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p : F.M)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (hescape : _root_.Filter.Tendsto tau _root_.Filter.atTop _root_.Filter.atTop) :
    ∃ (q : ℕ → F.M) (L : PointedRiemannianManifold.{u, uE, uH} (I := I)) (phi : ℕ → ℕ),
      StrictMono phi ∧
      (∀ i, lCost F.S 0 p (q i) (tau i) / (2 * Real.sqrt (tau i)) ≤
        (Module.finrank ℝ E : ℝ) / 2) ∧
      ∃ (Phi : PointedRiemannianConvergenceMaps (I := I) (backwardSliceSequence F tau htau q) L phi)
        (C : MetricConvergenceData (I := I) Phi),
        (∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Phi k) ∧
        MetricComplete (I := I) L ∧
        (let _ : TopologicalSpace L.M := L.topology
         let _ : ChartedSpace H L.M := L.charted
         let _ : IsManifold I ∞ L.M := L.smooth
         let _ : T2Space L.M := L.t2
         let _ : SigmaCompactSpace L.M := L.sigmaCompact
         ConnectedSpace L.M ∧
         (∃ x : L.M, metricScalarAt L.metric x ≠ 0) ∧
         (∀ x : L.M, ∀ (n : ℕ) (c : Fin n → ℝ) (v w : Fin n → TangentSpace I x),
           0 ≤ ∑ i, ∑ j, c i * c j * metricRm04StandardAt L.metric x (v i) (w i) (w j) (v j)) ∧
         ∃ f : C^∞⟮I, L.M; ℝ⟯,
           gradientRicciSoliton L.metric f 1 ∧
           IsHamiltonNormalizedPotential L.metric f ∧
           _root_.Filter.Tendsto (fun i => intrinsicReducedVolume F.S 0 p (tau (phi i)))
             atTop (𝓝 (normalizedShrinkerMass L.metric f))) := by
  classical
  choose q hq using fun i => exists_redLength_le_half_finrank_of_ancient F hF p (htau i)
  obtain ⟨L, phi, hphi, Phi, C, hcanonical, _href, hcomplete, hconnected,
    hpos, hcone, f, hsol, hmass, _hpotential⟩ :=
    exists_backward_slice_normalized_shrinker_of_reducedLength_bound
      F hF p tau htau hescape q hq
  refine ⟨q, L, phi, hphi, hq, Phi, C, hcanonical, hcomplete, hconnected,
    ⟨L.basepoint, (hpos L.basepoint).ne'⟩, ?_, f, hsol.2.1, ?_, ?_⟩
  · intro x m c v w
    exact (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff
      L.metric x).mp (hcone x) m c v w
  · exact Geometry.normalizedGradientRicciSoliton_potential_equation hsol
  · rw [hmass]
    exact (ancient_reducedVolume_tendsto_atTop F hF p).comp (hescape.comp hphi.tendsto_atTop)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_samePole_normalized_asymptotic_shrinker then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_samePole_normalized_asymptotic_shrinker"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_samePole_normalized_asymptotic_shrinker ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_samePole_normalized_asymptotic_shrinker

omit [I.Boundaryless] in
set_option backward.isDefEq.respectTransparency false in
theorem ancient_reducedVolume_antitone_of_redVolume_antitone
    (hgap : ∀ (D : RealTimeInterval)
      (S : SolutionOn (I := I) (M := F.M) D)
      (T : ℝ) (x : F.M) {tau1 tau2 : ℝ},
      IsSolutionOn (I := I) S →
      0 < tau1 → tau1 ≤ tau2 → T ∈ D.carrier →
      Set.Ico (T - tau2) T ⊆ D.regular →
      redVolume S T x tau2 ≤ redVolume S T x tau1)
    (p : F.M) :
    AntitoneOn (intrinsicReducedVolume F.S 0 p) (_root_.Set.Ioi 0) := by
  intro tau1 h1 tau2 h2 h12
  exact hgap ancientTimeInterval F.S 0 p F.isSolution h1 h12 (by simp)
    (fun t ht => ht.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_reducedVolume_antitone_of_redVolume_antitone then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_reducedVolume_antitone_of_redVolume_antitone"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_reducedVolume_antitone_of_redVolume_antitone ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_reducedVolume_antitone_of_redVolume_antitone

section IcoSlab

variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

omit [I.Boundaryless] in
def redVolumeIcoSlabAntitone {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) : Prop :=
  ∀ (T : ℝ) (x : M) {tau1 tau2 : ℝ},
    IsSolutionOn (I := I) S →
    0 < tau1 → tau1 ≤ tau2 → T ∈ D.carrier →
    Set.Ico (T - tau2) T ⊆ D.regular →
    redVolume S T x tau2 ≤ redVolume S T x tau1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.redVolumeIcoSlabAntitone then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.redVolumeIcoSlabAntitone"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.redVolumeIcoSlabAntitone ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.redVolumeIcoSlabAntitone

end IcoSlab

omit [I.Boundaryless] in
theorem ancient_reducedVolume_antitone_of_icoSlabAntitone
    (h : ∀ (D : RealTimeInterval) (S : SolutionOn (I := I) (M := F.M) D),
      redVolumeIcoSlabAntitone (I := I) (D := D) S)
    (p : F.M) :
    AntitoneOn (intrinsicReducedVolume F.S 0 p) (_root_.Set.Ioi 0) :=
  ancient_reducedVolume_antitone_of_redVolume_antitone F
    (fun D S T x => h D S T x) p

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_reducedVolume_antitone_of_icoSlabAntitone then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_reducedVolume_antitone_of_icoSlabAntitone"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_reducedVolume_antitone_of_icoSlabAntitone ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_reducedVolume_antitone_of_icoSlabAntitone

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
