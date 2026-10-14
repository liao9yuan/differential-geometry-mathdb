import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Maps
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardWindowShiftConvergence
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.Background
import Submission.DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalCross
import Submission.DifferentialGeometry.Geometry.Curvature.RicciRestriction
import Submission.DifferentialGeometry.Geometry.Metric.Distance.Ball
import Submission.DifferentialGeometry.Topology.SigmaCompactOpen

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Submission.Set _root_.Filter _root_.TopologicalSpace
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instSigmaCompactSpaceSubtypeMemOpensOfChartedSpaceThreeSpace {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [SigmaCompactSpace M] (U : _root_.TopologicalSpace.Opens M) : SigmaCompactSpace U :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel U.isOpen)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instSigmaCompactSpaceSubtypeMemOpensOfChartedSpaceThreeSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instSigmaCompactSpaceSubtypeMemOpensOfChartedSpaceThreeSpace target :: scope.openDecls } }

theorem metricScalarAt_basepoint_eq_of_local_flow_limit
    {X : PointedRiemannianSeq.{u, 0, 0} ThreeModel}
    {P : PointedRiemannianManifold.{u, 0, 0} ThreeModel}
    {f : ℕ → ℕ} (hf : StrictMono f) (F : PointedRiemannianConvergenceMaps X P f)
    {W : ∀ (_ : ℕ) (n : ℕ), _root_.TopologicalSpace.Opens (X.obj n).M}
    {h : ∀ k n, ℝ → SmoothRiemannianMetric ThreeModel (W k n)}
    {V : ℕ → _root_.TopologicalSpace.Opens P.M} {N : ℕ → ℕ}
    (hV : ∀ k, (V k : Set P.M) = riemannianBallOf P.metric P.basepoint (((k + 1 : ℕ) : ℝ) / 2))
    {φ : ∀ k j, N k ≤ j → V k → W k (f j)}
    {hφ : ∀ k j (hj : N k ≤ j), IsLocalDiffeomorph ThreeModel ThreeModel ∞ (φ k j hj)}
    (hφF : ∀ k j (hj : N k ≤ j) (z : V k),
      ((φ k j hj z : W k (f j)) : (X.obj (f j)).M) = F.map j z)
    {G : ℝ → SmoothRiemannianMetric ThreeModel P.M} (hG0 : G 0 = P.metric)
    {ψ : ℕ → ℕ} (hψ : StrictMono ψ)
    (hconv : ∀ k (K : Set (V k)), IsCompact K → ∀ p : ℕ, ∀ η : ℝ, 0 < η →
      ∃ j₀ : ℕ, ∀ i ≥ j₀, ∃ hi : N k ≤ ψ i,
        ∀ t ∈ _root_.Set.Icc (-((k + 1 : ℕ) : ℝ)) 0,
          metricDerivNormSupOn K p
            (localPullMetric (h k (f (ψ i)) t) (φ k (ψ i) hi) (hφ k (ψ i) hi))
            ((G t).restrictOpen (V k)) (P.metric.restrictOpen (V k)) < η)
    (hW0 : ∀ k, ∀ᶠ n in _root_.Filter.atTop, ∀ z : W k n,
      metricScalarAt (h k n 0) z = metricScalarAt (X.obj n).metric z)
    {c : ℝ} (hbase : ∀ n, metricScalarAt (X.obj n).metric (X.obj n).basepoint = c) :
    metricScalarAt P.metric P.basepoint = c := by
  have hmem : P.basepoint ∈ (V 0 : Set P.M) := by
    rw [hV 0]
    change riemannianEDistOf P.metric P.basepoint P.basepoint < _
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr (by norm_num)
  let x₀ : V 0 := ⟨P.basepoint, hmem⟩
  let g : ℕ → SmoothRiemannianMetric ThreeModel (V 0) := fun i =>
    if hi : N 0 ≤ ψ i then localPullMetric (h 0 (f (ψ i)) 0) (φ 0 (ψ i) hi) (hφ 0 (ψ i) hi)
    else P.metric.restrictOpen (V 0)
  have hconv' : ∀ K : Set (V 0), IsCompact K → ∀ e : ℝ, 0 < e → ∀ᶠ i in _root_.Filter.atTop,
      metricDerivNormSupOn K 2 (g i) ((G 0).restrictOpen (V 0))
        (P.metric.restrictOpen (V 0)) < e := by
    intro K hK e he
    obtain ⟨j₀, hj₀⟩ := hconv 0 K hK 2 e he
    filter_upwards [_root_.Filter.eventually_ge_atTop j₀] with i hi
    obtain ⟨hNi, hbound⟩ := hj₀ i hi
    have hg : g i = localPullMetric (h 0 (f (ψ i)) 0) (φ 0 (ψ i) hNi) (hφ 0 (ψ i) hNi) :=
      dif_pos hNi
    rw [hg]
    exact hbound 0 ⟨by norm_num, le_rfl⟩
  have hlim := tendsto_metricScalarAt_of_metricDerivNormSupOn hconv'
    (tendsto_const_nhds (x := x₀))
  have hG0' : metricScalarAt ((G 0).restrictOpen (V 0)) x₀ =
      metricScalarAt P.metric P.basepoint := by
    rw [metricScalarAt_restrictOpen, hG0]
  rw [hG0'] at hlim
  have hev : ∀ᶠ i in _root_.Filter.atTop, metricScalarAt (g i) x₀ = c := by
    filter_upwards [(hf.comp hψ).tendsto_atTop.eventually (hW0 0),
      hψ.tendsto_atTop.eventually_ge_atTop (N 0)] with i hW hNi
    have hg : g i = localPullMetric (h 0 (f (ψ i)) 0) (φ 0 (ψ i) hNi) (hφ 0 (ψ i) hNi) :=
      dif_pos hNi
    have hW' : ∀ z : W 0 (f (ψ i)),
        metricScalarAt (h 0 (f (ψ i)) 0) z = metricScalarAt (X.obj (f (ψ i))).metric z := hW
    have hb : F.map (ψ i) (x₀ : P.M) = (X.obj (f (ψ i))).basepoint := F.basepoint_map (ψ i)
    rw [hg, metricScalarAt_localPull, hW', hφF, hb]
    exact hbase _
  exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hev.mono fun _ h => h.symm))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.metricScalarAt_basepoint_eq_of_local_flow_limit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.metricScalarAt_basepoint_eq_of_local_flow_limit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.metricScalarAt_basepoint_eq_of_local_flow_limit ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.metricScalarAt_basepoint_eq_of_local_flow_limit

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
