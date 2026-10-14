import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedModelConvergence
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedShiTerminal
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalInnerRadius
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalMetricSandwich

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

variable {M : ℕ → Type u} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace ThreeSpace (M i)]
  [∀ i, IsManifold I3 ∞ (M i)] [∀ i, T2Space (M i)] [∀ i, SigmaCompactSpace (M i)]

theorem CanonicalWitness.eventually_image_ball_sandwich_of_windowed_models
    {D : ℕ → RealTimeInterval} {S : ∀ i, SolutionOn (I := I3) (M := M i) (D i)}
    (hS : ∀ i, IsSolutionOn (S i)) {delta : ℕ → ℝ} {kappa : ℝ}
    {x : ∀ i, M i} {t : ℕ → ℝ}
    (W : ∀ i, WindowedModelWitness (delta i) kappa (S i) (x i) (t i))
    (hdelta : _root_.Filter.Tendsto delta _root_.Filter.atTop (𝓝 0))
    (hreg : ∀ i, _root_.Set.Ioo (t i - (delta i * (S i).scalar (t i) (x i))⁻¹) (t i) ⊆ (D i).regular)
    (L : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval)
    [PreconnectedSpace L.M] (hcomplete : MetricComplete (L.atTime 0))
    {phi : ℕ → ℕ} (hphi : _root_.Filter.Tendsto phi _root_.Filter.atTop _root_.Filter.atTop)
    (F : PointedRiemannianConvergenceMaps ⟨fun i => (W i).model.atTime 0⟩
      (L.atTime 0) phi)
    (hcmp : ∀ K : Set L.M, IsCompact K → ∀ A : ℝ, 0 < A → ∀ order : ℕ,
      ∀ eta : ℝ, 0 < eta → ∀ᶠ i in _root_.Filter.atTop,
        Nonempty (MetricComparisonOn L.S.base.metric (W (phi i)).model.S.base.metric
          (F.map i) K (_root_.Set.Icc (-A) 0) order eta))
    {eps C1 C2 : ℝ} (K : CanonicalWitness L.S eps C1 C2 L.basepoint 0)
    (hscalar : L.S.scalar 0 L.basepoint = 1) :
    ∀ᶠ i in _root_.Filter.atTop, ∃ r : ℝ,
      (Real.sqrt ((S (phi i)).scalar (t (phi i)) (x (phi i))))⁻¹ ≤ r ∧
      r ≤ _root_.Max.max C1 2 / Real.sqrt ((S (phi i)).scalar (t (phi i)) (x (phi i))) ∧
      riemannianBallOf ((S (phi i)).base.metric (t (phi i))) (x (phi i)) r ⊆
        (partialDiffeomorphTransMixed (F.partialDiffeomorph i) (W (phi i)).embedding) ''
          K.domain.carrier ∧
      (partialDiffeomorphTransMixed (F.partialDiffeomorph i) (W (phi i)).embedding) ''
          K.domain.carrier ⊆
        riemannianBallOf ((S (phi i)).base.metric (t (phi i))) (x (phi i)) (2 * r) := by
  obtain ⟨a, b, margin, ha, haC, hm, hreserve, hinner, houter⟩ :=
    K.exists_normalized_radial_reserve hscalar
  let eta := _root_.Min.min (1 / 8 : ℝ) (margin / 8)
  have heta : 0 < eta := lt_min (by norm_num) (by positivity)
  have heta8 : eta ≤ 1 / 8 := min_le_left _ _
  have hetam : eta ≤ margin / 8 := min_le_right _ _
  have ha0 : 0 < a := by linarith
  have hminus : 0 < 1 - eta := by linarith
  have hplus : 0 < 1 + eta := by linarith
  have hAcomp : 1 ≤ (1 - eta) * ((1 - eta)⁻¹) ^ 2 := by
    rw [pow_two, ← mul_assoc, mul_inv_cancel₀ hminus.ne', one_mul]
    exact (one_le_inv₀ hminus).mpr (by linarith)
  have hLcomp : 1 + eta ≤ (1 + eta) ^ 2 := by nlinarith
  have hratio : (1 + eta) * (2 - margin) < 2 * (1 - eta) := by
    nlinarith [mul_pos heta hm]
  have htrans : (1 + eta) * b < 2 * (a / (1 - eta)⁻¹) := by
    rw [div_inv_eq_mul]
    calc
      _ < (1 + eta) * ((2 - margin) * a) := mul_lt_mul_of_pos_left hreserve hplus
      _ = ((1 + eta) * (2 - margin)) * a := by ring
      _ < (2 * (1 - eta)) * a := mul_lt_mul_of_pos_right hratio ha0
      _ = _ := by ring
  have hnum : 1 ≤ a * (1 - eta) := by
    nlinarith [mul_lt_mul_of_pos_right ha hminus]
  have hnumC : a * (1 - eta) ≤ _root_.Max.max C1 2 :=
    (mul_le_of_le_one_right ha0.le (by linarith)).trans haC.le
  let Psi := fun i => partialDiffeomorphTransMixed (F.partialDiffeomorph i) (W (phi i)).embedding
  let g := fun i => rescaledMetric (S (phi i)) (t (phi i))
    ((S (phi i)).scalar (t (phi i)) (x (phi i))) (W (phi i)).scalar_pos
  let _ : IsManifold I3 1 L.M := IsManifold.of_le (n := ∞) (by decide)
  have hc : RiemannianMetricComplete (L.S.base.metric 0) :=
    ⟨MetricComplete.complete (L.atTime 0) hcomplete⟩
  have hcompare := WindowedModelWitness.eventually_composed_comparison hS W hdelta
    (fun i s hs => ((W i).normalized_window (hreg i)).2 hs) L hcomplete hphi F hcmp
    (hc.closedEBall_isCompact L.basepoint b) zero_lt_one 0 heta
  filter_upwards [hcompare] with i hi
  obtain ⟨hsource, ⟨cmp⟩⟩ := hi
  have hball : riemannianBallOf (L.S.base.metric 0) L.basepoint b ⊆
      riemannianClosedBallOf (L.S.base.metric 0) L.basepoint b := by
    intro y hy
    exact (show riemannianEDistOf (L.S.base.metric 0) L.basepoint y <
      ENNReal.ofReal b from hy).le
  obtain ⟨_, _, _, hin, hout⟩ := cmp.map_strict_ball_sandwich
    (show (0 : ℝ) ∈ _root_.Set.Icc (-1 : ℝ) 0 by norm_num) K.domain L.basepoint
    ha0 (inv_pos.mpr hminus) hplus hinner houter (hball.trans hsource)
    hball htrans hAcomp hLcomp
  have hbase : Psi i L.basepoint = x (phi i) := by
    change (W (phi i)).embedding (F.map i L.basepoint) = x (phi i)
    have hb : F.map i L.basepoint = (W (phi i)).model.basepoint := F.basepoint_map i
    rw [hb, (W (phi i)).base_map]
  change riemannianBallOf (g i 0) (Psi i L.basepoint) (a / (1 - eta)⁻¹) ⊆
    Psi i '' K.domain.carrier at hin
  change Psi i '' K.domain.carrier ⊆
    riemannianBallOf (g i 0) (Psi i L.basepoint) ((1 + eta) * b) at hout
  rw [hbase, div_inv_eq_mul] at hin
  rw [hbase] at hout
  have hout' : Psi i '' K.domain.carrier ⊆
      riemannianBallOf (g i 0) (x (phi i)) (2 * (a * (1 - eta))) :=
    hout.trans (riemannianBallOf_mono _ _ (by simpa only [div_inv_eq_mul] using htrans.le))
  have hQ := Real.sqrt_pos.mpr (W (phi i)).scalar_pos
  have hscale (r : ℝ) :
      riemannianBallOf ((S (phi i)).base.metric (t (phi i))) (x (phi i))
          (r / Real.sqrt ((S (phi i)).scalar (t (phi i)) (x (phi i)))) =
        riemannianBallOf (g i 0) (x (phi i)) r := by
    have heq := riemannianBallOf_scaleMetric ((S (phi i)).scalar (t (phi i)) (x (phi i)))
      (W (phi i)).scalar_pos ((S (phi i)).base.metric (t (phi i))) (x (phi i))
      (r / Real.sqrt ((S (phi i)).scalar (t (phi i)) (x (phi i))))
    have hprod : Real.sqrt ((S (phi i)).scalar (t (phi i)) (x (phi i))) *
        (r / Real.sqrt ((S (phi i)).scalar (t (phi i)) (x (phi i)))) = r := by
      rw [mul_comm, div_mul_cancel₀ _ hQ.ne']
    rw [hprod] at heq
    simpa only [g, rescaledMetric, parabolicTime_zero] using heq.symm
  refine ⟨a * (1 - eta) / Real.sqrt ((S (phi i)).scalar (t (phi i)) (x (phi i))),
    ?_, ?_, ?_, ?_⟩
  · simpa only [one_div] using div_le_div_of_nonneg_right hnum hQ.le
  · exact div_le_div_of_nonneg_right hnumC hQ.le
  · rw [hscale]
    exact hin
  · rw [show 2 * (a * (1 - eta) /
        Real.sqrt ((S (phi i)).scalar (t (phi i)) (x (phi i)))) =
        (2 * (a * (1 - eta))) /
          Real.sqrt ((S (phi i)).scalar (t (phi i)) (x (phi i))) by ring, hscale]
    exact hout'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CanonicalWitness.eventually_image_ball_sandwich_of_windowed_models then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CanonicalWitness.eventually_image_ball_sandwich_of_windowed_models"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CanonicalWitness.eventually_image_ball_sandwich_of_windowed_models ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CanonicalWitness.eventually_image_ball_sandwich_of_windowed_models

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
