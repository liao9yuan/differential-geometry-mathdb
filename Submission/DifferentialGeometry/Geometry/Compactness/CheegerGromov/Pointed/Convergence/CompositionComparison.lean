import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Defs
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.Metric.InverseComposition

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.ENNReal

namespace DifferentialGeometry.CheegerGromovCompactness

universe u uM uN uE uH
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H0 : Type uH} [TopologicalSpace H0] {I : ModelWithCorners ℝ E H0}
  {M : Type uM} [MetricSpace M] [ChartedSpace H0 M] [IsManifold I ∞ M]
  {N : Type uN} [TopologicalSpace N] [ChartedSpace H0 N] [IsManifold I ∞ N]

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

theorem exists_inverse_composition_distance_comparison [T2Space N]
    (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ x y : M, _root_.EDist.edist x y = riemannianEDistOf g x y)
    (p : M) (X : PointedRiemannianSeq.{u} I)
    (A : ∀ i, PartialDiffeomorph I I M (X.obj i).M ∞)
    (hsource : ∀ K : Set M, IsCompact K → ∀ᶠ i in _root_.Filter.atTop, K ⊆ (A i).source)
    (hbase : ∀ i, A i p = (X.obj i).basepoint)
    (G : ℕ → SmoothRiemannianMetric I M)
    (hG : ∀ i, ∀ y ∈ (A i).source, ∀ v w : TangentSpace I y,
      (G i).inner y v w = (X.obj i).metric.inner (A i y)
        (mfderiv I I (A i) y v) (mfderiv I I (A i) y w))
    (hconv : ∀ K : Set M, IsCompact K → MetricCPConvergenceOn K 0 G g g)
    (H : ℕ → SmoothRiemannianMetric I N) (x : ℕ → N)
    (B : ∀ i, PartialDiffeomorph I I N (X.obj i).M ∞)
    {R : ℝ} (hR : 0 < R)
    (hB : ∀ i, riemannianClosedBallOf (H i) (x i) R ⊆ (B i).source)
    (hBbase : ∀ i, B i (x i) = (X.obj i).basepoint)
    (hcapture : ∀ i, riemannianClosedBallOf (X.obj i).metric
      (X.obj i).basepoint (R / 4) ⊆ (B i) '' riemannianClosedBallOf (H i) (x i) R)
    (hBconv : ∀ eta : ℝ, 0 < eta → ∀ᶠ i in _root_.Filter.atTop,
      ∀ y ∈ riemannianClosedBallOf (H i) (x i) R, ∀ v : TangentSpace I y,
        (1 - eta) * (H i).inner y v v ≤ (X.obj i).metric.inner (B i y)
          (mfderiv I I (B i) y v) (mfderiv I I (B i) y v) ∧
        (X.obj i).metric.inner (B i y)
          (mfderiv I I (B i) y v) (mfderiv I I (B i) y v) ≤
            (1 + eta) * (H i).inner y v v) :
    let C := fun i => (A i).trans (B i).symm
    ∃ r : ℝ, 0 < r ∧ IsCompact (riemannianClosedBallOf g p r) ∧
      (∀ i, C i p = x i) ∧
      (∀ᶠ i in _root_.Filter.atTop, riemannianClosedBallOf g p r ⊆ (C i).source ∧
        riemannianClosedBallOf (H i) (x i) (r / 4) ⊆
          (C i) '' riemannianClosedBallOf g p r) ∧
      ∀ eta : ℝ, 0 < eta → ∀ᶠ i in _root_.Filter.atTop,
        ∀ a ∈ riemannianClosedBallOf g p r, ∀ b ∈ riemannianClosedBallOf g p r,
          |(riemannianEDistOf (H i) (C i a) (C i b)).toReal - (riemannianEDistOf g a b).toReal| < eta := by
  let _ : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  obtain ⟨Rsrc, hRsrc, hK⟩ := Metric.exists_isCompact_closedBall p
  have hball : riemannianClosedBallOf g p Rsrc = Metric.closedBall p Rsrc := by
    ext y
    change riemannianEDistOf g p y ≤ ENNReal.ofReal Rsrc ↔ _root_.Dist.dist y p ≤ Rsrc
    rw [← hmetric, edist_dist, ENNReal.ofReal_le_ofReal_iff hRsrc.le, dist_comm]
  have hcompact : IsCompact (riemannianClosedBallOf g p Rsrc) := hball.symm ▸ hK
  have hAsource := hsource _ hcompact
  have hAmetric : ∀ᶠ i in _root_.Filter.atTop, ∀ y ∈ riemannianClosedBallOf g p Rsrc,
      ∀ v : TangentSpace I y, (G i).inner y v v = (X.obj i).metric.inner (A i y)
        (mfderiv I I (A i) y v) (mfderiv I I (A i) y v) := by
    filter_upwards [hAsource] with i hi
    exact fun y hy v => hG i y (hi hy) v v
  have hcapture' : ∀ᶠ i in _root_.Filter.atTop,
      riemannianClosedBallOf (X.obj i).metric (B i (x i)) (R / 4) ⊆
        (B i) '' riemannianClosedBallOf (H i) (x i) R :=
    Eventually.of_forall fun i => by simpa only [hBbase] using hcapture i
  obtain ⟨r, hr, _, hKr, hcap, _, hdist⟩ :=
    exists_inverse_composition_distance_comparison_of_tendsto_marks g g G
      (fun i => (X.obj i).metric) H A B p hRsrc hR hcompact (hconv _ hcompact)
      hAsource hAmetric x (u := fun _ => p) tendsto_const_nhds
      (Eventually.of_forall fun i => (hbase i).trans (hBbase i).symm)
      (Eventually.of_forall hB) hcapture' hBconv
  have hbaseC (i : ℕ) : (A i).trans (B i).symm p = x i := by
    change (B i).symm (A i p) = x i
    rw [hbase, ← hBbase]
    apply (B i).left_inv
    apply hB i
    change riemannianEDistOf (H i) (x i) (x i) ≤ _
    rw [riemannianEDistOf_self]
    exact bot_le
  refine ⟨r, hr, hKr, hbaseC, ?_, hdist⟩
  filter_upwards [hcap] with i hi
  exact ⟨hi.1, by simpa only [hbaseC] using hi.2.1⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.exists_inverse_composition_distance_comparison then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.exists_inverse_composition_distance_comparison"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.exists_inverse_composition_distance_comparison ``Submission.DifferentialGeometry.CheegerGromovCompactness.exists_inverse_composition_distance_comparison

end DifferentialGeometry.CheegerGromovCompactness
