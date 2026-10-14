import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.RoundBackwardSpaceForm
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AsymptoticShrinkerNormalization
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ShrinkerMassClassification
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.NoncompactShrinkerMassClassification

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

local instance universalVolumeTopology : TopologicalSpace F.M := F.topology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalVolumeTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalVolumeTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalVolumeTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalVolumeTopology
local instance universalVolumeCharted : ChartedSpace H F.M := F.charted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalVolumeCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalVolumeCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalVolumeCharted ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalVolumeCharted
local instance universalVolumeSmooth : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalVolumeSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalVolumeSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalVolumeSmooth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalVolumeSmooth
local instance universalVolumeC1 : IsManifold I 1 F.M := IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalVolumeC1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalVolumeC1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalVolumeC1 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalVolumeC1
local instance universalVolumeT2 : T2Space F.M := F.t2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalVolumeT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalVolumeT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalVolumeT2 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalVolumeT2
local instance universalVolumeSigma : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalVolumeSigma then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalVolumeSigma"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalVolumeSigma ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalVolumeSigma


theorem ancientKappaThree_reducedVolume_lower
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (hdim : Module.finrank ℝ E = 3)
    (hnotround : ¬ IsShrinkingSphericalSpaceFormFlow F) (p : F.M)
    {tau0 : ℝ} (htau0 : 0 < tau0) :
    ENNReal.ofReal (Real.exp (-1)) ≤ intrinsicReducedVolume F.S 0 p tau0 := by
  let tau : ℕ → ℝ := fun i => (i : ℝ) + 1
  have htau : ∀ i, 0 < tau i := fun i => by dsimp only [tau]; positivity
  have hescape : _root_.Filter.Tendsto tau _root_.Filter.atTop atTop := by
    apply _root_.Filter.tendsto_atTop_mono (fun i => ?_) (tendsto_natCast_atTop_atTop (R := ℝ))
    dsimp only [tau]
    linarith
  obtain ⟨q, L, phi, hphi, _hcenters, Phi, C, hcanonical, hcomplete, hgeometry⟩ :=
    exists_samePole_normalized_asymptotic_shrinker F hF p tau htau hescape
  let _ : TopologicalSpace L.M := L.topology
  let _ : ChartedSpace H L.M := L.charted
  let _ : IsManifold I ∞ L.M := L.smooth
  let _ : IsManifold I 1 L.M := IsManifold.of_le (n := ∞) (by decide)
  let _ : T2Space L.M := L.t2
  let _ : SigmaCompactSpace L.M := L.sigmaCompact
  obtain ⟨hconnected, hnonflat, hnco, f, hsoliton, hnormal, hmass⟩ := hgeometry
  have hmassLower : ENNReal.ofReal (Real.exp (-1)) ≤ normalizedShrinkerMass L.metric f := by
    rcases normalized_nonflat_three_shrinker_classification L hdim hcomplete hconnected
      hnonflat hnco f hsoliton hnormal with hround | hdouble | hsingle
    · obtain ⟨hcompact, hscalar, hEin⟩ := hround
      obtain ⟨hT, D, e, hmetric⟩ :=
        ancient_sphericalSpaceFormFlow_of_round_backward_convergence F hdim hF.connected
          tau htau hescape q hphi Phi C hcanonical hcompact (by norm_num : 0 < (3 : ℝ) / 2)
          hscalar hEin
      exact False.elim (hnotround ⟨3 / (2 * F.S.scalar 0 F.basepoint), hT, D, e, hmetric⟩)
    · rw [hdouble]
      apply ENNReal.ofReal_le_ofReal
      have hpos := Real.exp_pos (-1 : ℝ)
      linarith
    · exact hsingle.ge
  apply hmassLower.trans
  apply le_of_tendsto hmass
  have htimes : _root_.Filter.Tendsto (fun i => tau (phi i)) _root_.Filter.atTop atTop :=
    hescape.comp hphi.tendsto_atTop
  filter_upwards [htimes.eventually_ge_atTop tau0] with i hi
  exact ancient_reducedVolume_antitone F hF p htau0 (htau (phi i)) hi

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappaThree_reducedVolume_lower then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappaThree_reducedVolume_lower"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappaThree_reducedVolume_lower ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappaThree_reducedVolume_lower

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
