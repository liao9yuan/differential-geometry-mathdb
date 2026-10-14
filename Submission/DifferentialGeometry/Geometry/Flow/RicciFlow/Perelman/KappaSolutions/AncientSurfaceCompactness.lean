import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AsymptoticShrinker
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SurfaceShrinker
import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Compact

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle _root_.Filter
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

local instance ancientSurfaceCompactTopology : TopologicalSpace F.M := F.topology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSurfaceCompactTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSurfaceCompactTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSurfaceCompactTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSurfaceCompactTopology
local instance ancientSurfaceCompactCharted : ChartedSpace H F.M := F.charted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSurfaceCompactCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSurfaceCompactCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSurfaceCompactCharted ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSurfaceCompactCharted
local instance ancientSurfaceCompactSmooth : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSurfaceCompactSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSurfaceCompactSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSurfaceCompactSmooth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSurfaceCompactSmooth
local instance ancientSurfaceCompactT2 : T2Space F.M := F.t2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSurfaceCompactT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSurfaceCompactT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSurfaceCompactT2 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSurfaceCompactT2

theorem exists_compact_backward_surface_limit
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (hdim : Module.finrank ℝ E = 2)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (hescape : _root_.Filter.Tendsto tau _root_.Filter.atTop _root_.Filter.atTop) :
    ∃ (q : ℕ → F.M) (L : PointedRiemannianManifold.{u, uE, uH} (I := I)) (phi : ℕ → ℕ),
      StrictMono phi ∧
      ∃ (Phi : PointedRiemannianConvergenceMaps (I := I) (backwardSliceSequence F tau htau q) L phi)
        (C : MetricConvergenceData (I := I) Phi),
        (∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData (I := I) Phi k) ∧
        (∀ k, (C.domain k).referenceMetric = (C.domain k).limitMetric) ∧
        MetricComplete (I := I) L ∧
        (let _ : TopologicalSpace L.M := L.topology
         let _ : ChartedSpace H L.M := L.charted
         let _ : IsManifold I ∞ L.M := L.smooth
         let _ : T2Space L.M := L.t2
         CompactSpace L.M ∧ ConnectedSpace L.M ∧
           ∀ x : L.M, metricScalarAt (I := I) L.metric x = 1) := by
  obtain ⟨q, L, phi, hphi, Phi, C, hdomain, hreference, hcomplete, hgeometry⟩ :=
    exists_backward_slice_asymptotic_shrinker F hF tau htau hescape
  let _ : TopologicalSpace L.M := L.topology
  let _ : ChartedSpace H L.M := L.charted
  let _ : IsManifold I ∞ L.M := L.smooth
  let _ : T2Space L.M := L.t2
  let _ : SigmaCompactSpace L.M := L.sigmaCompact
  obtain ⟨hconnected, hnonflat, f, hsoliton⟩ := hgeometry
  let _ : ConnectedSpace L.M := hconnected
  have hmetricComplete : RiemannianMetricComplete (I := I) L.metric := ⟨hcomplete⟩
  obtain ⟨hcompact, hscalar⟩ :=
    complete_surface_shrinker_compact_constant_scalar (I := I)
      L.metric f (by norm_num : (0 : ℝ) < 1) hdim hmetricComplete hsoliton hnonflat
  exact ⟨q, L, phi, hphi, Phi, C, hdomain, hreference, hcomplete,
    hcompact, hconnected, hscalar⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_compact_backward_surface_limit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_compact_backward_surface_limit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_compact_backward_surface_limit ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_compact_backward_surface_limit

theorem ancientKappaSurface_compact {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (hdim : Module.finrank ℝ E = 2) : CompactSpace F.M := by
  let tau : ℕ → ℝ := fun i => (i : ℝ) + 1
  have htau : ∀ i, 0 < tau i := by
    intro i
    dsimp only [tau]
    positivity
  have hescape : _root_.Filter.Tendsto tau _root_.Filter.atTop atTop := by
    apply _root_.Filter.tendsto_atTop_mono (fun i => ?_) (tendsto_natCast_atTop_atTop (R := ℝ))
    dsimp only [tau]
    linarith
  obtain ⟨q, L, phi, _, Phi, _, _, _, _, hgeometry⟩ :=
    exists_compact_backward_surface_limit F hF hdim tau htau hescape
  let _ : TopologicalSpace L.M := L.topology
  let _ : ChartedSpace H L.M := L.charted
  obtain ⟨hcompact, _, _⟩ := hgeometry
  have hconnected : ∀ k : ℕ,
      @ConnectedSpace ((backwardSliceSequence F tau htau q).obj (phi k)).M
        ((backwardSliceSequence F tau htau q).obj (phi k)).topology :=
    fun k => backwardSliceSequence_connected F hF tau htau q (phi k)
  obtain ⟨k0, hk0⟩ := compactLimit_eventually_globalizes Phi hcompact hconnected
  obtain ⟨_, _, _, _, _, _, hcompactSource⟩ := hk0 k0 le_rfl
  exact hcompactSource

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappaSurface_compact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappaSurface_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappaSurface_compact ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappaSurface_compact

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
