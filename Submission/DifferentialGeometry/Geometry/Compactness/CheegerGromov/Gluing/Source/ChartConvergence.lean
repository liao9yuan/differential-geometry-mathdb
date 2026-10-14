import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.CenterOfMass.Average.TwoParameterConvergence


import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Gluing.Partition.Basic
import Submission.DifferentialGeometry.Analysis.Calculus.MapConvergence.TwoParameter
import Submission.DifferentialGeometry.Geometry.Exponential.GaussLemma.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open _root_.Filter _root_.Set _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Topology _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Exponential

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type uE} [NormedAddCommGroup E]
  [NormedSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  [ConnectedSpace M] [T3Space M]

omit [Module.Finite ℝ E] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank Real E)] in
theorem chartSymmUniform
    [FiniteDimensional Real E]
    (g : SmoothRiemannianMetric I M) (p : M) {K : Set E}
    (hK : IsCompact K)
    (hKtarget : K ⊆ (NormalCoordinates.normalChartAt (I := I) g p).target) :
    letI : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    UniformContinuousOn
      (fun v : E => (NormalCoordinates.normalChartAt (I := I) g p).symm v) K := by
  let : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  let ψ := NormalCoordinates.normalChartAt (I := I) g p
  have hcont : ContinuousOn (fun v : E => ψ.symm v) K := by
    simpa [ψ] using ψ.contMDiffOn_invFun.continuousOn.mono hKtarget
  exact hK.uniformContinuousOn_of_continuous hcont

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.chartSymmUniform then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.chartSymmUniform"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.chartSymmUniform ``Submission.DifferentialGeometry.CheegerGromovCompactness.chartSymmUniform

omit [Module.Finite ℝ E] in
omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartSymmIdConvergence
    [FiniteDimensional Real E]
    (g : SmoothRiemannianMetric I M) (p : M) {K : Set E}
    (hK : IsCompact K)
    (hKtarget : K ⊆ (NormalCoordinates.normalChartAt (I := I) g p).target)
    (F : Nat → Nat → E → E)
    (hclose : ∀ δ : Real, δ > 0 → ∃ N : Nat,
      ∀ a : Nat, a ≥ N → ∀ b : Nat, b ≥ N → ∀ v : E, v ∈ K →
        _root_.Dist.dist (F a b v) v < δ) :
    letI : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    ∀ ε : Real, ε > 0 → ∃ N : Nat,
      ∀ a : Nat, a ≥ N → ∀ b : Nat, b ≥ N → ∀ v : E, v ∈ K →
        dist ((NormalCoordinates.normalChartAt (I := I) g p).symm v)
          ((NormalCoordinates.normalChartAt (I := I) g p).symm (F a b v)) < ε := by
  let : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  let ψ := NormalCoordinates.normalChartAt (I := I) g p
  obtain ⟨η, hηpos, hηtarget⟩ :=
    hK.exists_cthickening_subset_open ψ.open_target hKtarget
  let K' : Set E := Metric.cthickening η K
  have hK' : IsCompact K' := hK.cthickening
  have hK'target : K' ⊆ ψ.target := by
    simpa only [K'] using hηtarget
  have huc :
      UniformContinuousOn
        (fun v : E => ψ.symm v) K' :=
    chartSymmUniform (I := I) g p hK' hK'target
  rw [Metric.uniformContinuousOn_iff] at huc
  intro ε hε
  obtain ⟨δ, hδpos, hδ⟩ := huc ε hε
  have hminpos : 0 < _root_.Min.min δ η := lt_min hδpos hηpos
  obtain ⟨N, hN⟩ := hclose (_root_.Min.min δ η) hminpos
  refine ⟨N, fun a ha b hb v hv => ?_⟩
  have hvK' : v ∈ K' := Metric.self_subset_cthickening K hv
  have hdist : _root_.Dist.dist (F a b v) v < _root_.Min.min δ η := hN a ha b hb v hv
  have hFvK' : F a b v ∈ K' := by
    exact Metric.mem_cthickening_of_dist_le (F a b v) v η K hv
      (le_trans (le_of_lt hdist) (min_le_right δ η))
  change _root_.Dist.dist (ψ.symm v) (ψ.symm (F a b v)) < ε
  exact hδ v hvK' (F a b v) hFvK'
    (by simpa only [dist_comm] using lt_of_lt_of_le hdist (min_le_left δ η))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.chartSymmIdConvergence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.chartSymmIdConvergence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.chartSymmIdConvergence ``Submission.DifferentialGeometry.CheegerGromovCompactness.chartSymmIdConvergence

omit [Module.Finite ℝ E] in
omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartPointsConvergence
    [FiniteDimensional Real E]
    (g : SmoothRiemannianMetric I M) (p : M)
    {S : Set M} {K : Set E} (hK : IsCompact K)
    (hKtarget : K ⊆ (NormalCoordinates.normalChartAt (I := I) g p).target)
    (hSsource : ∀ x : M, x ∈ S →
      x ∈ (NormalCoordinates.normalChartAt (I := I) g p).source)
    (hScoord : ∀ x : M, x ∈ S →
      (NormalCoordinates.normalChartAt (I := I) g p) x ∈ K)
    (F : Nat → Nat → E → E)
    (hclose : ∀ δ : Real, δ > 0 → ∃ N : Nat,
      ∀ a : Nat, a ≥ N → ∀ b : Nat, b ≥ N → ∀ v : E, v ∈ K →
        _root_.Dist.dist (F a b v) v < δ) :
    letI : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    ∀ ε : Real, ε > 0 → ∃ N : Nat,
      ∀ a : Nat, a ≥ N → ∀ b : Nat, b ≥ N → ∀ x : M, x ∈ S →
        dist x ((NormalCoordinates.normalChartAt (I := I) g p).symm
          (F a b ((NormalCoordinates.normalChartAt (I := I) g p) x))) < ε := by
  let : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  let ψ := NormalCoordinates.normalChartAt (I := I) g p
  have hdecoded :
      ∀ ε : Real, ε > 0 → ∃ N : Nat,
        ∀ a : Nat, a ≥ N → ∀ b : Nat, b ≥ N → ∀ v : E, v ∈ K →
          dist (ψ.symm v) (ψ.symm (F a b v)) < ε := by
    simpa [ψ] using
      chartSymmIdConvergence (I := I) g p hK hKtarget F hclose
  intro ε hε
  obtain ⟨N, hN⟩ := hdecoded ε hε
  refine ⟨N, fun a ha b hb x hx => ?_⟩
  have hxK : ψ x ∈ K := by
    simpa [ψ] using hScoord x hx
  have hxsrc : x ∈ ψ.source := by
    simpa [ψ] using hSsource x hx
  have hdist : _root_.Dist.dist (ψ.symm (ψ x)) (ψ.symm (F a b (ψ x))) < ε :=
    hN a ha b hb (ψ x) hxK
  have hleft : ψ.symm (ψ x) = x := by
    simpa [ψ] using NormalCoordinates.normalChartAt_left_inv (I := I) g p hxsrc
  rw [hleft] at hdist
  simpa [ψ] using hdist

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.chartPointsConvergence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.chartPointsConvergence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.chartPointsConvergence ``Submission.DifferentialGeometry.CheegerGromovCompactness.chartPointsConvergence

omit [Module.Finite ℝ E] in
omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chart_points_converge_on_source_compact
    [FiniteDimensional Real E]
    (g : SmoothRiemannianMetric I M) (p : M)
    {S Ksrc : Set M} (hKsrc : IsCompact Ksrc) (hSsub : S ⊆ Ksrc)
    (hsrcK : Ksrc ⊆ (NormalCoordinates.normalChartAt (I := I) g p).source)
    (F : Nat -> Nat -> E -> E)
    (hclose : ∀ δ : Real, δ > 0 -> ∃ N : Nat,
      ∀ a : Nat, a ≥ N -> ∀ b : Nat, b ≥ N -> ∀ v : E,
        v ∈ (NormalCoordinates.normalChartAt (I := I) g p) '' Ksrc ->
          _root_.Dist.dist (F a b v) v < δ) :
    letI : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    ∀ ε : Real, ε > 0 -> ∃ N : Nat,
      ∀ a : Nat, a ≥ N -> ∀ b : Nat, b ≥ N -> ∀ x : M, x ∈ S ->
        dist x ((NormalCoordinates.normalChartAt (I := I) g p).symm
          (F a b ((NormalCoordinates.normalChartAt (I := I) g p) x))) < ε := by
  let : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  let ψ := NormalCoordinates.normalChartAt (I := I) g p
  have hcont : ContinuousOn (fun x : M => ψ x) Ksrc := by
    exact ψ.contMDiffOn_toFun.continuousOn.mono hsrcK
  have hK : IsCompact (ψ '' Ksrc) := hKsrc.image_of_continuousOn hcont
  have hKtarget : ψ '' Ksrc ⊆ ψ.target := by
    rintro v ⟨x, hx, rfl⟩
    exact ψ.map_source (hsrcK hx)
  have hSsource : ∀ x : M, x ∈ S -> x ∈ ψ.source := by
    intro x hx
    exact hsrcK (hSsub hx)
  have hScoord : ∀ x : M, x ∈ S -> ψ x ∈ ψ '' Ksrc := by
    intro x hx
    exact ⟨x, hSsub hx, rfl⟩
  simpa [ψ] using
    chartPointsConvergence (I := I) (g := g) (p := p) (S := S) (K := ψ '' Ksrc)
      hK hKtarget hSsource hScoord F hclose

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.chart_points_converge_on_source_compact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.chart_points_converge_on_source_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.chart_points_converge_on_source_compact ``Submission.DifferentialGeometry.CheegerGromovCompactness.chart_points_converge_on_source_compact

omit [Module.Finite ℝ E] in
theorem closedBall_subset_normalChartAt_source_of_radius
    [FiniteDimensional Real E]
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (P : ProperMetricOn (I := I) Y) {c : Y.M} {R : Real}
    (hR :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space Y.M := Y.t2
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      R < metricCoerciveExpRadius (I := I) Y.metric c) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : MetricSpace Y.M := P.ms
    Metric.closedBall c R ⊆
      (NormalCoordinates.normalChartAt (I := I) Y.metric c).source := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space Y.M := Y.t2
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let : MetricSpace Y.M := P.ms
  let cg : _root_.Bundle.ContinuousRiemannianMetric E (fun x : Y.M => TangentSpace I x) :=
    Y.metric.toContinuousRiemannianMetric
  let : _root_.Bundle.RiemannianBundle (fun x : Y.M => TangentSpace I x) :=
    ⟨cg.toRiemannianMetric⟩
  have hEnorm :
      ∀ x : Y.M, ∀ v : TangentSpace I x,
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (Y.metric.inner x v v)) := by
    intro x v
    exact
      DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := I) Y.metric x v
  intro y hy
  have hed :
      _root_.Manifold.riemannianEDist I c y =
        ENNReal.ofReal (_root_.Dist.dist c y) := by
    change (letI : EMetricSpace Y.M := Y.emetricSpace; _root_.EDist.edist c y) = _
    exact P.realizes c y
  have hfin : _root_.Manifold.riemannianEDist I c y ≠ (⊤ : ℝ≥0∞) := by
    rw [hed]
    exact ENNReal.ofReal_ne_top
  have hdist_le : _root_.Dist.dist c y ≤ R := by
    have hdist := (Metric.mem_closedBall.mp hy)
    simpa [dist_comm] using hdist
  have hsmall : (_root_.Manifold.riemannianEDist I c y).toReal < metricCoerciveExpRadius (I := I) Y.metric c := by
    rw [hed, ENNReal.toReal_ofReal (dist_nonneg : 0 ≤ _root_.Dist.dist c y)]
    exact lt_of_le_of_lt hdist_le hR
  exact mem_normalChartAt_source_of_dist (I := I) Y.metric c hEnorm hfin hsmall

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.closedBall_subset_normalChartAt_source_of_radius then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.closedBall_subset_normalChartAt_source_of_radius"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.closedBall_subset_normalChartAt_source_of_radius ``Submission.DifferentialGeometry.CheegerGromovCompactness.closedBall_subset_normalChartAt_source_of_radius

omit [Module.Finite ℝ E] in
theorem properBallNormal
    [FiniteDimensional Real E]
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (P : ProperMetricOn (I := I) Y) {c y : Y.M} {R : Real}
    (hR :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space Y.M := Y.t2
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      R < metricCoerciveExpRadius (I := I) Y.metric c)
    (hy : letI : MetricSpace Y.M := P.ms; y ∈ Metric.ball c R) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : MetricSpace Y.M := P.ms
    ∃ v : E,
      v ∈ (NormalCoordinates.normalChartAt (I := I) Y.metric c).target ∧
      (show TangentSpace I c from v) ∈ expDomain (I := I) Y.metric c ∧
      Real.sqrt (Y.metric.inner c v v) = _root_.Dist.dist c y ∧
      y = expMap (I := I) Y.metric c (show TangentSpace I c from v) := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space Y.M := Y.t2
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let : MetricSpace Y.M := P.ms
  let cg : _root_.Bundle.ContinuousRiemannianMetric E (fun x : Y.M => TangentSpace I x) :=
    Y.metric.toContinuousRiemannianMetric
  let : _root_.Bundle.RiemannianBundle (fun x : Y.M => TangentSpace I x) :=
    ⟨cg.toRiemannianMetric⟩
  have hEnorm : ∀ x : Y.M, ∀ w : TangentSpace I x,
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (Y.metric.inner x w w)) := by
    intro x w
    exact
      DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := I) Y.metric x w
  have hed : _root_.Manifold.riemannianEDist I c y = ENNReal.ofReal (_root_.Dist.dist c y) := by
    change (letI : EMetricSpace Y.M := Y.emetricSpace; _root_.EDist.edist c y) = _
    exact P.realizes c y
  have hfin : _root_.Manifold.riemannianEDist I c y ≠ (⊤ : ENNReal) := by
    rw [hed]
    exact ENNReal.ofReal_ne_top
  have hdist_lt : _root_.Dist.dist c y < R := by
    simpa only [Metric.mem_ball, dist_comm] using hy
  have hsmall : (_root_.Manifold.riemannianEDist I c y).toReal <
      metricCoerciveExpRadius (I := I) Y.metric c := by
    rw [hed, ENNReal.toReal_ofReal dist_nonneg]
    exact hdist_lt.trans hR
  obtain ⟨v, hvtgt, hvdom, hvlen, hyeq⟩ :=
    metricBall_subset_normalBall (I := I) Y.metric c hEnorm hfin hsmall
  refine ⟨v, hvtgt, hvdom, ?_, hyeq⟩
  calc
    Real.sqrt (Y.metric.inner c v v) = (_root_.Manifold.riemannianEDist I c y).toReal := hvlen
    _ = _root_.Dist.dist c y := by rw [hed, ENNReal.toReal_ofReal dist_nonneg]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.properBallNormal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.properBallNormal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.properBallNormal ``Submission.DifferentialGeometry.CheegerGromovCompactness.properBallNormal

omit [Module.Finite ℝ E] in
theorem properExpDist
    [FiniteDimensional Real E]
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (P : ProperMetricOn (I := I) Y) (c : Y.M) {v : E}
    (hv :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space Y.M := Y.t2
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      Real.sqrt (Y.metric.inner c v v) < metricCoerciveExpRadius (I := I) Y.metric c) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : MetricSpace Y.M := P.ms
    dist c (expMap (I := I) Y.metric c (show TangentSpace I c from v)) =
      Real.sqrt (Y.metric.inner c v v) := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space Y.M := Y.t2
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let : MetricSpace Y.M := P.ms
  let cg : _root_.Bundle.ContinuousRiemannianMetric E (fun x : Y.M => TangentSpace I x) :=
    Y.metric.toContinuousRiemannianMetric
  let : _root_.Bundle.RiemannianBundle (fun x : Y.M => TangentSpace I x) :=
    ⟨cg.toRiemannianMetric⟩
  have hEnorm : ∀ x : Y.M, ∀ w : TangentSpace I x,
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (Y.metric.inner x w w)) := by
    intro x w
    exact
      DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := I) Y.metric x w
  have hed := edist_exp_eq_radius (I := I) Y.metric c hEnorm hv
  have hdist :
      _root_.Manifold.riemannianEDist I c
          (expMap (I := I) Y.metric c (show TangentSpace I c from v)) =
        ENNReal.ofReal
          (_root_.Dist.dist c (expMap (I := I) Y.metric c (show TangentSpace I c from v))) := by
    change (letI : EMetricSpace Y.M := Y.emetricSpace
      edist c (expMap (I := I) Y.metric c (show TangentSpace I c from v))) = _
    exact P.realizes c
      (expMap (I := I) Y.metric c (show TangentSpace I c from v))
  have hofReal :
      ENNReal.ofReal
          (_root_.Dist.dist c (expMap (I := I) Y.metric c (show TangentSpace I c from v))) =
        ENNReal.ofReal (Real.sqrt (Y.metric.inner c v v)) := by
    rw [← hdist]
    exact hed
  exact (ENNReal.ofReal_eq_ofReal_iff dist_nonneg (Real.sqrt_nonneg _)).mp hofReal

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.properExpDist then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.properExpDist"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.properExpDist ``Submission.DifferentialGeometry.CheegerGromovCompactness.properExpDist

end CheegerGromovCompactness
end DifferentialGeometry
