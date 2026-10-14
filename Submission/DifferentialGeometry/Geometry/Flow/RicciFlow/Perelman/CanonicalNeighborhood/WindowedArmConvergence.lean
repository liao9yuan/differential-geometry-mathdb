import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedArmCapture
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ComparisonDistanceConvergence
import Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.PairedRayLimit
import Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.ComparisonAngleStability
import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Metric.Proper

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u v

variable {N : Type u} [TopologicalSpace N] [ChartedSpace ThreeSpace N]
  [IsManifold I3 ∞ N] [T2Space N] [SigmaCompactSpace N] [PreconnectedSpace N]

private local instance inverseComparisonC1 : IsManifold I3 1 N :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.inverseComparisonC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.inverseComparisonC1 target :: scope.openDecls } }

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

variable {M : ℕ → Type u} [∀ i, TopologicalSpace (M i)]
  [∀ i, ChartedSpace ThreeSpace (M i)] [∀ i, IsManifold I3 ∞ (M i)]
  [∀ i, T2Space (M i)] [∀ i, SigmaCompactSpace (M i)]

theorem WindowedModelWitness.tendsto_composed_inverse_arm_distance_sub
    {D : ℕ → RealTimeInterval} {S : ∀ i, SolutionOn (I := I3) (M := M i) (D i)}
    (hS : ∀ i, IsSolutionOn (S i)) {delta : ℕ → ℝ} {kappa : ℝ}
    {x : ∀ i, M i} {t : ℕ → ℝ}
    (W : ∀ i, WindowedModelWitness (delta i) kappa (S i) (x i) (t i))
    (hdelta : _root_.Filter.Tendsto delta _root_.Filter.atTop (𝓝 0))
    (hreg : ∀ i s, s ∈ _root_.Set.Ioo (-modelDepth (delta i)) 0 →
      parabolicTime (t i) ((S i).scalar (t i) (x i)) s ∈ (D i).regular)
    (L : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval)
    [PreconnectedSpace L.M] (hcomplete : MetricComplete (L.atTime 0))
    {phi : ℕ → ℕ} (hphi : _root_.Filter.Tendsto phi _root_.Filter.atTop _root_.Filter.atTop)
    (F : PointedRiemannianConvergenceMaps ⟨fun i => (W i).model.atTime 0⟩
      (L.atTime 0) phi)
    (hcmp : ∀ K : Set L.M, IsCompact K → ∀ B : ℝ, 0 < B → ∀ order : ℕ,
      ∀ eta : ℝ, 0 < eta → ∀ᶠ i in _root_.Filter.atTop,
        Nonempty (MetricComparisonOn L.S.base.metric (W (phi i)).model.S.base.metric
          (F.map i) K (_root_.Set.Icc (-B) 0) order eta))
    (a b : ∀ i, MinimizingArm ((S (phi i)).base.metric (t (phi i))) (x (phi i)))
    (ha : _root_.Filter.Tendsto (fun i => Real.sqrt ((S (phi i)).scalar (t (phi i)) (x (phi i))) *
      (a i).length) _root_.Filter.atTop _root_.Filter.atTop)
    (hb : _root_.Filter.Tendsto (fun i => Real.sqrt ((S (phi i)).scalar (t (phi i)) (x (phi i))) *
      (b i).length) _root_.Filter.atTop _root_.Filter.atTop)
    {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) :
    let Psi := fun i => partialDiffeomorphTransMixed
      (F.partialDiffeomorph i) (W (phi i)).embedding
    let Q := fun i => (S (phi i)).scalar (t (phi i)) (x (phi i))
    _root_.Filter.Tendsto (fun i =>
      metricDistance (L.S.base.metric 0)
        ((Psi i).symm ((a i).point (r / Real.sqrt (Q i))))
        ((Psi i).symm ((b i).point (s / Real.sqrt (Q i)))) -
      metricDistance (rescaledMetric (S (phi i)) (t (phi i)) (Q i)
        (W (phi i)).scalar_pos 0)
        ((a i).point (r / Real.sqrt (Q i))) ((b i).point (s / Real.sqrt (Q i))))
      atTop (𝓝 0) := by
  let _ : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  let Psi := fun i => partialDiffeomorphTransMixed
    (F.partialDiffeomorph i) (W (phi i)).embedding
  let Q := fun i => (S (phi i)).scalar (t (phi i)) (x (phi i))
  let A := _root_.Max.max r s
  have hA : 0 ≤ A := hr.trans (le_max_left _ _)
  let g := fun i => rescaledMetric (S (phi i)) (t (phi i)) (Q i) (W (phi i)).scalar_pos
  let y := fun i => (Psi i).symm ((a i).point (r / Real.sqrt (Q i)))
  let z := fun i => (Psi i).symm ((b i).point (s / Real.sqrt (Q i)))
  let K := riemannianClosedBallOf (L.S.base.metric 0) L.basepoint (4 * (A + 1))
  obtain ⟨hK, hcapture⟩ := WindowedModelWitness.eventually_composed_minimizingArm_prefix_capture hS W hdelta
    hreg L hcomplete hphi F hcmp A hA
  have hcaptured : ∀ᶠ i in _root_.Filter.atTop,
      y i ∈ K ∧ z i ∈ K ∧
        Psi i (y i) = (a i).point (r / Real.sqrt (Q i)) ∧
        Psi i (z i) = (b i).point (s / Real.sqrt (Q i)) := by
    filter_upwards [hcapture, ha.eventually_ge_atTop r, hb.eventually_ge_atTop s] with i hi hai hbi
    have hq : 0 < Real.sqrt (Q i) := Real.sqrt_pos.mpr (W (phi i)).scalar_pos
    have har : r / Real.sqrt (Q i) ∈ _root_.Set.Icc 0 (a i).length :=
      ⟨div_nonneg hr hq.le, (div_le_iff₀ hq).mpr (by simpa only [mul_comm] using hai)⟩
    have hbs : s / Real.sqrt (Q i) ∈ _root_.Set.Icc 0 (b i).length :=
      ⟨div_nonneg hs hq.le, (div_le_iff₀ hq).mpr (by simpa only [mul_comm] using hbi)⟩
    have hcar := hi.2.2 (a i) _ har (by
      change Real.sqrt (Q i) * (r / Real.sqrt (Q i)) ≤ A
      rw [mul_div_cancel₀ _ hq.ne']
      exact le_max_left _ _)
    have hcbs := hi.2.2 (b i) _ hbs (by
      change Real.sqrt (Q i) * (s / Real.sqrt (Q i)) ≤ A
      rw [mul_div_cancel₀ _ hq.ne']
      exact le_max_right _ _)
    exact ⟨(hcar.2.2 _ ⟨har.1, le_rfl⟩).2.1,
      (hcbs.2.2 _ ⟨hbs.1, le_rfl⟩).2.1,
      (hcar.2.2 _ ⟨har.1, le_rfl⟩).2.2.2,
      (hcbs.2.2 _ ⟨hbs.1, le_rfl⟩).2.2.2⟩
  have he := tendsto_metricDistance_sub_of_comparisons L.S.base.metric g Psi
    (show (0 : ℝ) ∈ _root_.Set.Icc (-1) 0 by norm_num)
    (⟨MetricComplete.complete _ hcomplete⟩ : RiemannianMetricComplete (L.S.base.metric 0))
    (fun eps heps K' hK' => WindowedModelWitness.eventually_composed_comparison hS W hdelta hreg L hcomplete
      hphi F hcmp hK' zero_lt_one 0 heps) hK y z (hcaptured.mono fun _ hi => ⟨hi.1, hi.2.1⟩)
  have he' := he.neg
  simp only [neg_zero] at he'
  apply he'.congr'
  filter_upwards [hcaptured] with i hi
  change -(metricDistance (g i 0) (Psi i (y i)) (Psi i (z i)) -
    metricDistance (L.S.base.metric 0) (y i) (z i)) = _
  rw [hi.2.2.1, hi.2.2.2, neg_sub]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.WindowedModelWitness.tendsto_composed_inverse_arm_distance_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.WindowedModelWitness.tendsto_composed_inverse_arm_distance_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.WindowedModelWitness.tendsto_composed_inverse_arm_distance_sub ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.WindowedModelWitness.tendsto_composed_inverse_arm_distance_sub

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
end

end

section
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Geometry.Comparison.Toponogov
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

variable {M : ℕ → Type u} [∀ i, TopologicalSpace (M i)]
  [∀ i, ChartedSpace ThreeSpace (M i)] [∀ i, IsManifold I3 ∞ (M i)]
  [∀ i, T2Space (M i)] [∀ i, SigmaCompactSpace (M i)]

theorem WindowedModelWitness.exists_composed_original_arm_rays
    {D : ℕ → RealTimeInterval} {S : ∀ i, SolutionOn (I := I3) (M := M i) (D i)}
    (hS : ∀ i, IsSolutionOn (S i)) {delta : ℕ → ℝ} {kappa : ℝ}
    {x : ∀ i, M i} {t : ℕ → ℝ}
    (W : ∀ i, WindowedModelWitness (delta i) kappa (S i) (x i) (t i))
    (hdelta : _root_.Filter.Tendsto delta _root_.Filter.atTop (𝓝 0))
    (hreg : ∀ i s, s ∈ _root_.Set.Ioo (-modelDepth (delta i)) 0 →
      parabolicTime (t i) ((S i).scalar (t i) (x i)) s ∈ (D i).regular)
    (L : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval)
    [PreconnectedSpace L.M] (hcomplete : MetricComplete (L.atTime 0))
    {phi : ℕ → ℕ} (hphi : _root_.Filter.Tendsto phi _root_.Filter.atTop _root_.Filter.atTop)
    (F : PointedRiemannianConvergenceMaps ⟨fun i => (W i).model.atTime 0⟩
      (L.atTime 0) phi)
    (hcmp : ∀ K : Set L.M, IsCompact K → ∀ B : ℝ, 0 < B → ∀ order : ℕ,
      ∀ eta : ℝ, 0 < eta → ∀ᶠ i in _root_.Filter.atTop,
        Nonempty (MetricComparisonOn L.S.base.metric (W (phi i)).model.S.base.metric
          (F.map i) K (_root_.Set.Icc (-B) 0) order eta))
    (arms : ∀ i, Fin 2 →
      MinimizingArm ((S (phi i)).base.metric (t (phi i))) (x (phi i)))
    (hlength : ∀ j, _root_.Filter.Tendsto (fun i => Real.sqrt ((S (phi i)).scalar (t (phi i)) (x (phi i))) *
      (arms i j).length) _root_.Filter.atTop _root_.Filter.atTop)
    {theta : ℝ} (htheta : 0 < theta)
    (hangle : ∀ r : ℝ, 0 < r → ∀ᶠ i in _root_.Filter.atTop,
      theta ≤ comparisonAngle r r
        (metricDistance (rescaledMetric (S (phi i)) (t (phi i))
          ((S (phi i)).scalar (t (phi i)) (x (phi i))) (W (phi i)).scalar_pos 0)
          ((arms i 0).point (r / Real.sqrt ((S (phi i)).scalar (t (phi i)) (x (phi i)))))
          ((arms i 1).point (r / Real.sqrt ((S (phi i)).scalar (t (phi i)) (x (phi i))))))) :
    let Psi : ∀ i, PartialDiffeomorph I3 I3 L.M (M (phi i)) ∞ := fun i => partialDiffeomorphTransMixed
      (F.partialDiffeomorph i) (W (phi i)).embedding
    let Q := fun i => (S (phi i)).scalar (t (phi i)) (x (phi i))
    ∃ rays : Fin 2 × ℝ≥0 → L.M,
      MapClusterPt rays _root_.Filter.atTop
        (fun i z => (Psi i).symm ((arms i z.1).point ((z.2 : ℝ) / Real.sqrt (Q i)))) ∧
      (∀ j, rays (j, 0) = L.basepoint) ∧
      (∀ j s t, metricDistance (L.S.base.metric 0) (rays (j, s)) (rays (j, t)) =
        |(s : ℝ) - t|) ∧
      ∀ r : ℝ≥0, 0 < r → theta / 2 ≤ comparisonAngle r r
        (metricDistance (L.S.base.metric 0) (rays (0, r)) (rays (1, r))) := by
  let _ : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  let _ : Nonempty L.M := ⟨L.basepoint⟩
  let _ : ConnectedSpace L.M := ⟨inferInstance⟩
  let P := properMetricOn (L.atTime 0) hcomplete
    (inferInstanceAs (ConnectedSpace L.M))
  let m : MetricSpace L.M := P.ms.replaceTopology (ProperMetricOn.top_eq _ P).symm
  let _ : MetricSpace L.M := m
  have hm : m = P.ms := MetricSpace.replaceTopology_eq _ _
  let _ : ProperSpace L.M := by
    change @ProperSpace L.M m.toPseudoMetricSpace
    rw [hm]
    exact P.proper
  have hrealizes (y z : L.M) :
      riemannianEDistOf (L.S.base.metric 0) y z = ENNReal.ofReal (_root_.Dist.dist y z) := P.realizes y z
  have hdist (y z : L.M) : metricDistance (L.S.base.metric 0) y z = _root_.Dist.dist y z := by
    rw [metricDistance, hrealizes, ENNReal.toReal_ofReal dist_nonneg]
  let Psi : ∀ i, PartialDiffeomorph I3 I3 L.M (M (phi i)) ∞ := fun i => partialDiffeomorphTransMixed
    (F.partialDiffeomorph i) (W (phi i)).embedding
  let Q := fun i => (S (phi i)).scalar (t (phi i)) (x (phi i))
  let g := fun i => rescaledMetric (S (phi i)) (t (phi i)) (Q i) (W (phi i)).scalar_pos 0
  let f : ℕ → Fin 2 × ℝ≥0 → L.M := fun i z =>
    (Psi i).symm ((arms i z.1).point ((z.2 : ℝ) / Real.sqrt (Q i)))
  have hq (i : ℕ) : 0 < Real.sqrt (Q i) := Real.sqrt_pos.mpr (W (phi i)).scalar_pos
  have hzero : ∀ i j, f i (j, 0) = L.basepoint := by
    intro i j
    have hbase : Psi i L.basepoint = x (phi i) := by
      change (W (phi i)).embedding (F.map i L.basepoint) = x (phi i)
      rw [show F.map i L.basepoint = (W (phi i)).model.basepoint from F.basepoint_map i]
      exact (W (phi i)).base_map
    have hp : L.basepoint ∈ (Psi i).source := by
      refine ⟨F.base_mem i, ?_⟩
      change F.map i L.basepoint ∈ (W (phi i)).embedding.source
      rw [show F.map i L.basepoint = (W (phi i)).model.basepoint from F.basepoint_map i]
      apply (W (phi i)).buffered_ball
      change riemannianEDistOf _ _ _ ≤ _
      rw [riemannianEDistOf_self]
      exact bot_le
    change (Psi i).symm ((arms i j).point ((0 : ℝ) / Real.sqrt (Q i))) = L.basepoint
    rw [zero_div, (arms i j).start, ← hbase]
    exact (Psi i).left_inv' hp
  have hpair (j : Fin 2) (r s : ℝ≥0) : ∀ᶠ i in _root_.Filter.atTop,
      metricDistance (g i)
        ((arms i j).point ((r : ℝ) / Real.sqrt (Q i)))
        ((arms i j).point ((s : ℝ) / Real.sqrt (Q i))) = |(r : ℝ) - s| := by
    filter_upwards [(hlength j).eventually_ge_atTop (r : ℝ),
      (hlength j).eventually_ge_atTop (s : ℝ)] with i hi hj
    have hr : (r : ℝ) / Real.sqrt (Q i) ∈ _root_.Set.Icc 0 (arms i j).length :=
      ⟨div_nonneg r.coe_nonneg (hq i).le, (div_le_iff₀ (hq i)).mpr (by simpa only [mul_comm] using hi)⟩
    have hs : (s : ℝ) / Real.sqrt (Q i) ∈ _root_.Set.Icc 0 (arms i j).length :=
      ⟨div_nonneg s.coe_nonneg (hq i).le, (div_le_iff₀ (hq i)).mpr (by simpa only [mul_comm] using hj)⟩
    change (riemannianEDistOf (rescaledMetric _ _ _ _ 0) _ _).toReal = _
    rw [edistOf_rescaledMetric_zero, (arms i j).edistOf_eq hr hs,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (hq i).le, ENNReal.toReal_ofReal (abs_nonneg _),
      ← sub_div, abs_div, abs_of_pos (hq i), mul_div_cancel₀ _ (hq i).ne']
  have hpairs : ∀ j : Fin 2, ∀ r s : ℝ≥0,
      Tendsto (fun i => _root_.Dist.dist (f i (j, r)) (f i (j, s))) _root_.Filter.atTop (𝓝 (_root_.Dist.dist r s)) := by
    intro j r s
    have he := WindowedModelWitness.tendsto_composed_inverse_arm_distance_sub
      hS W hdelta hreg L hcomplete hphi F hcmp (fun i => arms i j) (fun i => arms i j)
      (hlength j) (hlength j) r.coe_nonneg s.coe_nonneg
    have hs : _root_.Filter.Tendsto (fun i => metricDistance (g i)
        ((arms i j).point ((r : ℝ) / Real.sqrt (Q i)))
        ((arms i j).point ((s : ℝ) / Real.sqrt (Q i)))) _root_.Filter.atTop (𝓝 (_root_.Dist.dist r s)) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [hpair j r s] with i hi
      simpa only [NNReal.dist_eq] using hi.symm
    change _root_.Filter.Tendsto (fun i => metricDistance (L.S.base.metric 0) (f i (j, r)) (f i (j, s)) -
      metricDistance (g i) ((arms i j).point ((r : ℝ) / Real.sqrt (Q i)))
        ((arms i j).point ((s : ℝ) / Real.sqrt (Q i)))) _root_.Filter.atTop (𝓝 0) at he
    have hh := he.add hs
    simpa only [sub_add_cancel, zero_add, hdist] using hh
  have hangle' : ∀ r : ℝ≥0, 0 < r → ∀ᶠ i in _root_.Filter.atTop,
      theta / 2 ≤ comparisonAngle r r (_root_.Dist.dist (f i (0, r)) (f i (1, r))) := by
    intro r hr
    have hb : ∀ᶠ i in _root_.Filter.atTop,
        0 ≤ metricDistance (g i) ((arms i 0).point ((r : ℝ) / Real.sqrt (Q i)))
          ((arms i 1).point ((r : ℝ) / Real.sqrt (Q i))) ∧
        metricDistance (g i) ((arms i 0).point ((r : ℝ) / Real.sqrt (Q i)))
          ((arms i 1).point ((r : ℝ) / Real.sqrt (Q i))) ≤ 2 * r := by
      filter_upwards [hpair 0 0 r, hpair 1 0 r] with i h0 h1
      simp only [NNReal.coe_zero, zero_div, (arms i 0).start, (arms i 1).start,
        zero_sub, abs_neg, abs_of_nonneg r.coe_nonneg] at h0 h1
      refine ⟨ENNReal.toReal_nonneg, ?_⟩
      have htri := riemannianEDistOf_triangle (g i)
        ((arms i 0).point ((r : ℝ) / Real.sqrt (Q i))) (x (phi i))
        ((arms i 1).point ((r : ℝ) / Real.sqrt (Q i)))
      rw [riemannianEDistOf_comm (g i)
        ((arms i 0).point ((r : ℝ) / Real.sqrt (Q i))) (x (phi i))] at htri
      have hfin (j : Fin 2) : riemannianEDistOf (g i) (x (phi i))
          ((arms i j).point ((r : ℝ) / Real.sqrt (Q i))) ≠ ⊤ := by
        have hh : metricDistance (g i) (x (phi i))
            ((arms i j).point ((r : ℝ) / Real.sqrt (Q i))) = r := by
          fin_cases j <;> assumption
        intro ht
        simp only [metricDistance, ht, ENNReal.toReal_top] at hh
        exact (ne_of_gt (show (0 : ℝ) < r from hr)) hh.symm
      have ht := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfin 0, hfin 1⟩) htri
      rw [ENNReal.toReal_add (hfin 0) (hfin 1)] at ht
      change _ ≤ metricDistance (g i) _ _ + metricDistance (g i) _ _ at ht
      rw [h0, h1] at ht
      simpa only [two_mul, metricDistance] using ht
    have he := WindowedModelWitness.tendsto_composed_inverse_arm_distance_sub
      hS W hdelta hreg L hcomplete hphi F hcmp (fun i => arms i 0) (fun i => arms i 1)
      (hlength 0) (hlength 1) r.coe_nonneg r.coe_nonneg
    have ht := eventually_comparisonAngle_half_lt_of_sub_tendsto_zero hr htheta hb
      (Eventually.of_forall fun _ => ENNReal.toReal_nonneg) he (hangle r hr)
    filter_upwards [ht] with i hi
    have hi' : theta / 2 ≤ comparisonAngle r r
        (metricDistance (L.S.base.metric 0) (f i (0, r)) (f i (1, r))) := hi.le
    simpa only [hdist] using hi'
  obtain ⟨rays, hcluster, hiso, hbase, hang⟩ :=
    exists_isometric_rays_of_approximate_rays_comparisonAngle_lower f L.basepoint (theta / 2)
      hzero hpairs hangle'
  refine ⟨rays, hcluster, hbase, ?_, ?_⟩
  · intro j r s
    rw [hdist, (hiso j).dist_eq, NNReal.dist_eq]
  · simpa only [hdist] using hang

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.WindowedModelWitness.exists_composed_original_arm_rays then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.WindowedModelWitness.exists_composed_original_arm_rays"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.WindowedModelWitness.exists_composed_original_arm_rays ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.WindowedModelWitness.exists_composed_original_arm_rays

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
end

end
