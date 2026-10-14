import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AsymptoticShrinkerBlowdown
import Submission.DifferentialGeometry.Geometry.Curvature.DimensionOne.Flat

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
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance reductionSourceTopology : TopologicalSpace F.M := F.topology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.reductionSourceTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.reductionSourceTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.reductionSourceTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.reductionSourceTopology
local instance reductionSourceCharted : ChartedSpace H F.M := F.charted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.reductionSourceCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.reductionSourceCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.reductionSourceCharted ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.reductionSourceCharted
local instance reductionSourceSmooth : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.reductionSourceSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.reductionSourceSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.reductionSourceSmooth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.reductionSourceSmooth
local instance reductionSourceT2 : T2Space F.M := F.t2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.reductionSourceT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.reductionSourceT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.reductionSourceT2 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.reductionSourceT2
local instance reductionSourceSigma : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.reductionSourceSigma then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.reductionSourceSigma"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.reductionSourceSigma ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.reductionSourceSigma

theorem ancientReducedVolume_rmNormSq_eq_zero_of_finrank_le_one
    (hE : Module.finrank ℝ E ≤ 1) (t : ℝ) (x : F.M) :
    F.rmNormSq t x = 0 := by
  have hzero : F.S.base.rm04 t x = 0 := by
    simpa only [SolutionFamily.rm04, metricRm04_apply] using
      metricRm04At_eq_zero_of_finrank_le_one (I := I) (M := F.M) (F.S.base.metric t) hE x
  rw [PointedFlowData.rmNormSq, hzero]
  simp only [SolutionOn.family_metric]
  simp [Tensor0SBundle.normSq0S, Tensor0SBundle.inner0S,
    Tensor0SBundle.MetricFiberData.inner]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientReducedVolume_rmNormSq_eq_zero_of_finrank_le_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientReducedVolume_rmNormSq_eq_zero_of_finrank_le_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientReducedVolume_rmNormSq_eq_zero_of_finrank_le_one ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientReducedVolume_rmNormSq_eq_zero_of_finrank_le_one

theorem not_isAncientKappaSolution_of_finrank_le_one
    {kappa : ℝ} (hE : Module.finrank ℝ E ≤ 1) :
    ¬ IsAncientKappaSolution kappa F := by
  intro hF
  obtain ⟨t, _ht, x, hx⟩ := hF.notFlat
  exact hx (ancientReducedVolume_rmNormSq_eq_zero_of_finrank_le_one F hE t x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.not_isAncientKappaSolution_of_finrank_le_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.not_isAncientKappaSolution_of_finrank_le_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.not_isAncientKappaSolution_of_finrank_le_one ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.not_isAncientKappaSolution_of_finrank_le_one

theorem two_le_finrank_of_isAncientKappaSolution
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) :
    2 ≤ Module.finrank ℝ E := by
  by_contra h
  exact not_isAncientKappaSolution_of_finrank_le_one F (by omega) hF

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.two_le_finrank_of_isAncientKappaSolution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.two_le_finrank_of_isAncientKappaSolution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.two_le_finrank_of_isAncientKappaSolution ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.two_le_finrank_of_isAncientKappaSolution

theorem neZero_finrank_of_isAncientKappaSolution
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) :
    NeZero (Module.finrank ℝ E) :=
  ⟨by have h := two_le_finrank_of_isAncientKappaSolution F hF; omega⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.neZero_finrank_of_isAncientKappaSolution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.neZero_finrank_of_isAncientKappaSolution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.neZero_finrank_of_isAncientKappaSolution ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.neZero_finrank_of_isAncientKappaSolution

theorem ancient_reducedVolume_antitone_of_finrank_le_one
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (hE : Module.finrank ℝ E ≤ 1) (p : F.M) :
    AntitoneOn (intrinsicReducedVolume F.S 0 p) (_root_.Set.Ioi 0) :=
  (not_isAncientKappaSolution_of_finrank_le_one F hE hF).elim

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_reducedVolume_antitone_of_finrank_le_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_reducedVolume_antitone_of_finrank_le_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_reducedVolume_antitone_of_finrank_le_one ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_reducedVolume_antitone_of_finrank_le_one

omit [I.Boundaryless] in
theorem ancient_reducedVolume_antitone_of_terminalLimits
    (p : F.M)
    (hregular : ∀ T : ℝ, T < 0 →
      AntitoneOn (intrinsicReducedVolume F.S T p) (_root_.Set.Ioi 0))
    (hlower : ∀ tau ∈ _root_.Set.Ioi 0,
      intrinsicReducedVolume F.S 0 p tau ≤
        _root_.Filter.liminf (fun T : ℝ => intrinsicReducedVolume F.S T p tau) (𝓝[<] (0 : ℝ)))
    (hupper : ∀ tau ∈ _root_.Set.Ioi 0,
      _root_.Filter.limsup (fun T : ℝ => intrinsicReducedVolume F.S T p tau) (𝓝[<] (0 : ℝ)) ≤
        intrinsicReducedVolume F.S 0 p tau) :
    AntitoneOn (intrinsicReducedVolume F.S 0 p) (_root_.Set.Ioi 0) := by
  intro tau1 h1 tau2 h2 h12
  have hcompare : ∀ᶠ T in 𝓝[<] (0 : ℝ),
      intrinsicReducedVolume F.S T p tau2 ≤ intrinsicReducedVolume F.S T p tau1 := by
    filter_upwards [self_mem_nhdsWithin] with T hT
    exact (hregular T hT) h1 h2 h12
  have hliminf := Filter.liminf_le_liminf hcompare
  have hlimsup := Filter.liminf_le_limsup (f := 𝓝[<] (0 : ℝ))
    (u := fun T : ℝ => intrinsicReducedVolume F.S T p tau1)
  exact (hlower tau2 h2).trans (hliminf.trans (hlimsup.trans (hupper tau1 h1)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_reducedVolume_antitone_of_terminalLimits then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_reducedVolume_antitone_of_terminalLimits"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_reducedVolume_antitone_of_terminalLimits ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_reducedVolume_antitone_of_terminalLimits

section NormalizedShrinker

variable [NeZero (Module.finrank ℝ E)]

theorem exists_samePole_normalized_asymptotic_shrinker_of_limit_shrinker
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p : F.M)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (q : ℕ → F.M)
    (hcost : ∀ i, lCost F.S 0 p (q i) (tau i) / (2 * Real.sqrt (tau i)) ≤
      (Module.finrank ℝ E : ℝ) / 2)
    (hcompact : backwardSliceApproximateMetricCompactness F hF tau htau q)
    (hlimit : ∀ (phi : ℕ → ℕ) (L : PointedRiemannianManifold.{u, uE, uH} (I := I)),
      StrictMono phi →
      ∀ (Phi : PointedRiemannianConvergenceMaps (I := I)
        (backwardSliceSequence F tau htau q) L phi)
        (C : MetricConvergenceData (I := I) Phi),
      (∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData (I := I) Phi k) →
      MetricComplete (I := I) L →
      (let _ : TopologicalSpace L.M := L.topology
       let _ : ChartedSpace H L.M := L.charted
       let _ : IsManifold I ∞ L.M := L.smooth
       let _ : T2Space L.M := L.t2
       let _ : SigmaCompactSpace L.M := L.sigmaCompact
       ConnectedSpace L.M →
       (∃ x : L.M, metricScalarAt L.metric x ≠ 0) ∧
       (∀ x : L.M, ∀ (n : ℕ) (c : Fin n → ℝ)
           (v w : Fin n → TangentSpace I x),
         0 ≤ ∑ i, ∑ j,
           c i * c j * metricRm04StandardAt L.metric x (v i) (w i) (w j) (v j)) ∧
       ∃ f : C^∞⟮I, L.M; ℝ⟯,
         gradientRicciSoliton L.metric f 1 ∧
         IsHamiltonNormalizedPotential L.metric f ∧
         _root_.Filter.Tendsto (fun i => intrinsicReducedVolume F.S 0 p (tau (phi i)))
           _root_.Filter.atTop (𝓝 (normalizedShrinkerMass L.metric f)))) :
    ∃ (q : ℕ → F.M) (L : PointedRiemannianManifold.{u, uE, uH} (I := I)) (phi : ℕ → ℕ),
      StrictMono phi ∧
      (∀ i, lCost F.S 0 p (q i) (tau i) / (2 * Real.sqrt (tau i)) ≤
        (Module.finrank ℝ E : ℝ) / 2) ∧
      ∃ (Phi : PointedRiemannianConvergenceMaps (I := I)
            (backwardSliceSequence F tau htau q) L phi)
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
         (∀ x : L.M, ∀ (n : ℕ) (c : Fin n → ℝ)
             (v w : Fin n → TangentSpace I x),
           0 ≤ ∑ i, ∑ j,
             c i * c j * metricRm04StandardAt L.metric x (v i) (w i) (w j) (v j)) ∧
         ∃ f : C^∞⟮I, L.M; ℝ⟯,
           gradientRicciSoliton L.metric f 1 ∧
           IsHamiltonNormalizedPotential L.metric f ∧
           _root_.Filter.Tendsto (fun i => intrinsicReducedVolume F.S 0 p (tau (phi i)))
             atTop (𝓝 (normalizedShrinkerMass L.metric f))) := by
  obtain ⟨L, phi, hphi, Phi, C, hdomain, hreference, hcomplete, hconnected⟩ :=
    exists_backward_slice_pointed_limit F hF tau htau q hcompact
  obtain ⟨hnonflat, hnco, hlimit⟩ := hlimit phi L hphi Phi C hdomain hcomplete hconnected
  exact ⟨q, L, phi, hphi, hcost, Phi, C, hdomain, hcomplete,
    hconnected, hnonflat, hnco, hlimit⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_samePole_normalized_asymptotic_shrinker_of_limit_shrinker then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_samePole_normalized_asymptotic_shrinker_of_limit_shrinker"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_samePole_normalized_asymptotic_shrinker_of_limit_shrinker ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_samePole_normalized_asymptotic_shrinker_of_limit_shrinker

end NormalizedShrinker

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
