import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.W.Potential.Smoothness
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.W.Potential.DensityInverse
import Submission.DifferentialGeometry.Analysis.Parabolic.MetricDivergenceChart
import Submission.DifferentialGeometry.Geometry.Metric.Family.TimeComposition
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BackwardFlowHeatEquation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Submission.Set _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Tensor.Coordinates _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Entropy
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology _root_.NNReal
universe u uH
variable {n : ℕ} {H : Type uH} [TopologicalSpace H]
  {I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) H} [I.Boundaryless]
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

theorem backward_flow_limit_perelmanDensity_contDiffOn_in_chart
    (F : PointedFlowData.{u, 0, uH} (I := I) ancientTimeInterval)
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p : F.M)
    (tau : ℕ → ℝ) (htau : ∀ n, 0 < tau n) (q : ℕ → F.M)
    (L : PointedFlowData.{u, 0, uH} (I := I) ancientTimeInterval)
    [PreconnectedSpace L.M]
    {subseq : ℕ → ℕ}
    (Phi : PointedCGHMaps (backwardFlowSequence F tau htau q) (L.atTime 0) subseq)
    (R : SmoothRiemannianMetric I L.M) (G : ℕ → ℝ → SmoothRiemannianMetric I L.M)
    (hG : ∀ K : Set L.M, IsCompact K → ∀ᶠ n in _root_.Filter.atTop,
      ∃ U : Set L.M, IsOpen U ∧ K ⊆ U ∧ U ⊆ Phi.source n ∧
        ∀ t : ℝ, ∀ x ∈ U, ∀ v w : TangentSpace I x,
          (G n t).inner x v w = (((backwardFlowSequence F tau htau q).term (subseq n)).S.base.metric t).inner
            (Phi.map n x) (mfderiv I I (Phi.map n) x v) (mfderiv I I (Phi.map n) x w))
    (hmetric : ∀ a b : ℝ, _root_.Set.Icc a b ⊆ _root_.Set.Iic 0 → ∀ K : Set L.M, IsCompact K →
      ∀ r : ℕ, ∀ epsilon : ℝ, 0 < epsilon → ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ _root_.Set.Icc a b,
        metricDerivNormSupOn K r (G n t) (L.S.base.metric t) R < epsilon)
    {T : ℝ} (hT : 1 < T) (ell : C(L.M × _root_.Set.Icc (1 : ℝ) T, ℝ))
    (hell : ∀ Q : Set (L.M × _root_.Set.Icc (1 : ℝ) T), IsCompact Q → TendstoUniformlyOn
      (fun n w => redLength F.S 0 p (Phi.map n w.1) (tau (subseq n) * w.2)) ell _root_.Filter.atTop Q)
    (hLip : ∀ B : ℝ, 0 ≤ B → ∃ K : ℝ≥0,
      ∀ x ∈ riemannianClosedBallOf (L.S.base.metric 0) L.basepoint B,
      ∀ y ∈ riemannianClosedBallOf (L.S.base.metric 0) L.basepoint B,
      ∀ s t : _root_.Set.Icc (1 : ℝ) T, |ell (x, s) - ell (y, t)| ≤
        (K : ℝ) * ((riemannianEDistOf (L.S.base.metric 0) x y).toReal + |(s : ℝ) - t|))
    (hescape : _root_.Filter.Tendsto (tau ∘ subseq) _root_.Filter.atTop _root_.Filter.atTop)
    (hconv : ∀ t ∈ _root_.Set.Icc (1 - T) (0 : ℝ),
      ∃ C : MetricConvergenceData (Phi.atTime
        (X := backwardFlowSequence F tau htau q) (L := L) t),
      ∀ i, C.domain i = CanonicalMetricCompactness.canonicalSourceData
        (Phi.atTime (X := backwardFlowSequence F tau htau q) (L := L) t) i)
    (hcomplete : ∀ t ∈ _root_.Set.Icc (1 - T) (0 : ℝ), MetricComplete (L.atTime t))
    (α : L.M) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun w : ℝ × EuclideanSpace ℝ (Fin n) => perelmanDensity (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) w.1
        (fun x => ell (x, _root_.Set.projIcc 1 T hT.le w.1)) ((extChartAt I α).symm w.2))
      (_root_.Set.Ioo 1 T ×ˢ (extChartAt I α).target) := by
  let _ : NeZero n := ⟨by
    have hn : 2 ≤ n := by simpa using two_le_finrank_of_isAncientKappaSolution F hF
    omega⟩
  let _ : LocallyCompactSpace H := I.locallyCompactSpace
  let _ : LocallyCompactSpace L.M := ChartedSpace.locallyCompactSpace H L.M
  let Dr := RealTimeInterval.openInfinite 1 2 (by norm_num)
  have hGrev : MetricFamilySmoothOn Dr (fun t => L.S.base.metric (1 - t)) :=
    L.isSolution.smoothMetric.comp_time
      (contDiff_const.sub contDiff_id).contDiffOn
      (continuous_const.sub continuous_id).continuousOn
      (fun t ht => show 1 - t < 0 from sub_neg.mpr ht)
      (fun t ht => show 1 - t ≤ 0 from sub_nonpos.mpr (le_of_lt ht))
  apply Analysis.Parabolic.contDiffOn_of_chart_weak_equation hGrev
    (fun t ht => ht.1) α (isOpen_extChartAt_target (I := I) α)
    (by rw [(isOpen_extChartAt_target (I := I) α).interior_eq])
    ((locallyLipschitzOn_perelmanDensity_in_chart_of_spacetime_bounds
      (L.S.base.metric 0) L.basepoint hT.le ell hLip α (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))).mono
      (fun _ hw => ⟨zero_lt_one.trans hw.1.1, hw.2⟩))
  intro φ hφ hφc hφs
  exact (backward_flow_limit_perelmanDensity_weak_eq_in_chart
    F hF p tau htau q L Phi R G hG hmetric hT ell hell hLip hescape hconv hcomplete
    α hφ hφc hφs).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backward_flow_limit_perelmanDensity_contDiffOn_in_chart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backward_flow_limit_perelmanDensity_contDiffOn_in_chart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backward_flow_limit_perelmanDensity_contDiffOn_in_chart ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backward_flow_limit_perelmanDensity_contDiffOn_in_chart

theorem backward_flow_reducedLength_limit_contDiffOn_in_chart
    (F : PointedFlowData.{u, 0, uH} (I := I) ancientTimeInterval)
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p : F.M)
    (tau : ℕ → ℝ) (htau : ∀ n, 0 < tau n) (q : ℕ → F.M)
    (L : PointedFlowData.{u, 0, uH} (I := I) ancientTimeInterval)
    [PreconnectedSpace L.M]
    {subseq : ℕ → ℕ}
    (Phi : PointedCGHMaps (backwardFlowSequence F tau htau q) (L.atTime 0) subseq)
    (R : SmoothRiemannianMetric I L.M) (G : ℕ → ℝ → SmoothRiemannianMetric I L.M)
    (hG : ∀ K : Set L.M, IsCompact K → ∀ᶠ n in _root_.Filter.atTop,
      ∃ U : Set L.M, IsOpen U ∧ K ⊆ U ∧ U ⊆ Phi.source n ∧
        ∀ t : ℝ, ∀ x ∈ U, ∀ v w : TangentSpace I x,
          (G n t).inner x v w = (((backwardFlowSequence F tau htau q).term (subseq n)).S.base.metric t).inner
            (Phi.map n x) (mfderiv I I (Phi.map n) x v) (mfderiv I I (Phi.map n) x w))
    (hmetric : ∀ a b : ℝ, _root_.Set.Icc a b ⊆ _root_.Set.Iic 0 → ∀ K : Set L.M, IsCompact K →
      ∀ r : ℕ, ∀ epsilon : ℝ, 0 < epsilon → ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ _root_.Set.Icc a b,
        metricDerivNormSupOn K r (G n t) (L.S.base.metric t) R < epsilon)
    {T : ℝ} (hT : 1 < T) (ell : C(L.M × _root_.Set.Icc (1 : ℝ) T, ℝ))
    (hell : ∀ Q : Set (L.M × _root_.Set.Icc (1 : ℝ) T), IsCompact Q → TendstoUniformlyOn
      (fun n w => redLength F.S 0 p (Phi.map n w.1) (tau (subseq n) * w.2)) ell _root_.Filter.atTop Q)
    (hLip : ∀ B : ℝ, 0 ≤ B → ∃ K : ℝ≥0,
      ∀ x ∈ riemannianClosedBallOf (L.S.base.metric 0) L.basepoint B,
      ∀ y ∈ riemannianClosedBallOf (L.S.base.metric 0) L.basepoint B,
      ∀ s t : _root_.Set.Icc (1 : ℝ) T, |ell (x, s) - ell (y, t)| ≤
        (K : ℝ) * ((riemannianEDistOf (L.S.base.metric 0) x y).toReal + |(s : ℝ) - t|))
    (hescape : _root_.Filter.Tendsto (tau ∘ subseq) _root_.Filter.atTop _root_.Filter.atTop)
    (hconv : ∀ t ∈ _root_.Set.Icc (1 - T) (0 : ℝ),
      ∃ C : MetricConvergenceData (Phi.atTime
        (X := backwardFlowSequence F tau htau q) (L := L) t),
      ∀ i, C.domain i = CanonicalMetricCompactness.canonicalSourceData
        (Phi.atTime (X := backwardFlowSequence F tau htau q) (L := L) t) i)
    (hcomplete : ∀ t ∈ _root_.Set.Icc (1 - T) (0 : ℝ), MetricComplete (L.atTime t))
    (α : L.M) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun w : ℝ × EuclideanSpace ℝ (Fin n) => ell ((extChartAt I α).symm w.2, _root_.Set.projIcc 1 T hT.le w.1))
      (_root_.Set.Ioo 1 T ×ˢ (extChartAt I α).target) := by
  let f := fun t (y : EuclideanSpace ℝ (Fin n)) => ell ((extChartAt I α).symm y, _root_.Set.projIcc 1 T hT.le t)
  let u := fun t => perelmanDensity (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) t (f t)
  let Ω := _root_.Set.Ioo 1 T ×ˢ (extChartAt I α).target
  have hu := backward_flow_limit_perelmanDensity_contDiffOn_in_chart
    F hF p tau htau q L Phi R G hG hmetric hT ell hell hLip hescape hconv hcomplete α
  have huM : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) 𝓘(ℝ) ∞
      (fun p : ℝ × EuclideanSpace ℝ (Fin n) => u p.1 p.2) Ω := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact hu.contMDiffOn
  have ht (p : ℝ × EuclideanSpace ℝ (Fin n)) (hp : p ∈ Ω) : 0 < p.1 := zero_lt_one.trans hp.1.1
  have hp (p : ℝ × EuclideanSpace ℝ (Fin n)) (hp : p ∈ Ω) : 0 < u p.1 p.2 :=
    mul_pos (prefactor_pos _ (ht p hp)) (Real.exp_pos _)
  have hpot := contMDiffOn_perelmanPotential (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) huM ht hp
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hpot
  apply hpot.contDiffOn.congr
  intro z hz
  exact (congrFun (potential_density (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) (ht z hz) (f z.1)) z.2).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backward_flow_reducedLength_limit_contDiffOn_in_chart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backward_flow_reducedLength_limit_contDiffOn_in_chart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backward_flow_reducedLength_limit_contDiffOn_in_chart ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backward_flow_reducedLength_limit_contDiffOn_in_chart

theorem backward_flow_reducedLength_limit_hamilton_jacobi_eq_in_chart
    (F : PointedFlowData.{u, 0, uH} (I := I) ancientTimeInterval)
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p : F.M)
    (tau : ℕ → ℝ) (htau : ∀ n, 0 < tau n) (q : ℕ → F.M)
    (L : PointedFlowData.{u, 0, uH} (I := I) ancientTimeInterval)
    [PreconnectedSpace L.M]
    {subseq : ℕ → ℕ}
    (Phi : PointedCGHMaps (backwardFlowSequence F tau htau q) (L.atTime 0) subseq)
    (R : SmoothRiemannianMetric I L.M) (G : ℕ → ℝ → SmoothRiemannianMetric I L.M)
    (hG : ∀ K : Set L.M, IsCompact K → ∀ᶠ n in _root_.Filter.atTop,
      ∃ U : Set L.M, IsOpen U ∧ K ⊆ U ∧ U ⊆ Phi.source n ∧
        ∀ t : ℝ, ∀ x ∈ U, ∀ v w : TangentSpace I x,
          (G n t).inner x v w = (((backwardFlowSequence F tau htau q).term (subseq n)).S.base.metric t).inner
            (Phi.map n x) (mfderiv I I (Phi.map n) x v) (mfderiv I I (Phi.map n) x w))
    (hmetric : ∀ a b : ℝ, _root_.Set.Icc a b ⊆ _root_.Set.Iic 0 → ∀ K : Set L.M, IsCompact K →
      ∀ r : ℕ, ∀ epsilon : ℝ, 0 < epsilon → ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ _root_.Set.Icc a b,
        metricDerivNormSupOn K r (G n t) (L.S.base.metric t) R < epsilon)
    {T : ℝ} (hT : 1 < T) (ell : C(L.M × _root_.Set.Icc (1 : ℝ) T, ℝ))
    (hell : ∀ Q : Set (L.M × _root_.Set.Icc (1 : ℝ) T), IsCompact Q → TendstoUniformlyOn
      (fun n w => redLength F.S 0 p (Phi.map n w.1) (tau (subseq n) * w.2)) ell _root_.Filter.atTop Q)
    (hLip : ∀ B : ℝ, 0 ≤ B → ∃ K : ℝ≥0,
      ∀ x ∈ riemannianClosedBallOf (L.S.base.metric 0) L.basepoint B,
      ∀ y ∈ riemannianClosedBallOf (L.S.base.metric 0) L.basepoint B,
      ∀ s t : _root_.Set.Icc (1 : ℝ) T, |ell (x, s) - ell (y, t)| ≤
        (K : ℝ) * ((riemannianEDistOf (L.S.base.metric 0) x y).toReal + |(s : ℝ) - t|))
    (hescape : _root_.Filter.Tendsto (tau ∘ subseq) _root_.Filter.atTop _root_.Filter.atTop)
    (hconv : ∀ t ∈ _root_.Set.Icc (1 - T) (0 : ℝ),
      ∃ C : MetricConvergenceData (Phi.atTime
        (X := backwardFlowSequence F tau htau q) (L := L) t),
      ∀ i, C.domain i = CanonicalMetricCompactness.canonicalSourceData
        (Phi.atTime (X := backwardFlowSequence F tau htau q) (L := L) t) i)
    (hcomplete : ∀ t ∈ _root_.Set.Icc (1 - T) (0 : ℝ), MetricComplete (L.atTime t))
    (α : L.M) {z : ℝ × EuclideanSpace ℝ (Fin n)}
    (hz : z ∈ _root_.Set.Ioo 1 T ×ˢ (extChartAt I α).target) :
    let f := fun w : ℝ × EuclideanSpace ℝ (Fin n) =>
      ell ((extChartAt I α).symm w.2, _root_.Set.projIcc 1 T hT.le w.1)
    fderiv ℝ f z (1, 0) + (1 / 2 : ℝ) *
      ∑ k : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))),
        ∑ j : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))),
          chartInvGramOnE (L.S.base.metric (1 - z.1)) α k j z.2 *
            fderiv ℝ f z (0, chartModelBasis (EuclideanSpace ℝ (Fin n)) j) *
            fderiv ℝ f z (0, chartModelBasis (EuclideanSpace ℝ (Fin n)) k) -
      (1 / 2 : ℝ) * metricScalarAt (L.S.base.metric (1 - z.1)) ((extChartAt I α).symm z.2) +
      f z / (2 * z.1) = 0 := by
  let _ : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) := neZero_finrank_of_isAncientKappaSolution F hF
  let f := fun w : ℝ × EuclideanSpace ℝ (Fin n) =>
    ell ((extChartAt I α).symm w.2, _root_.Set.projIcc 1 T hT.le w.1)
  have hf := backward_flow_reducedLength_limit_contDiffOn_in_chart
    F hF p tau htau q L Phi R G hG hmetric hT ell hell hLip hescape hconv hcomplete α
  have htest := backward_flow_reducedLength_limit_hamilton_jacobi_tests_in_chart
    F hF p tau htau q L Phi R G hG hmetric hT ell hell α hz f
      ((hf.of_le (by simp)).contDiffAt
        ((isOpen_Ioo.prod (isOpen_extChartAt_target (I := I) α)).mem_nhds hz))
  exact le_antisymm (htest.1 (by simpa only [f, sub_self] using
    (isLocalMax_const : IsLocalMax (fun _ : ℝ × EuclideanSpace ℝ (Fin n) => (0 : ℝ)) z)))
    (htest.2 (by simpa only [f, sub_self] using
      (isLocalMin_const : IsLocalMin (fun _ : ℝ × EuclideanSpace ℝ (Fin n) => (0 : ℝ)) z)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backward_flow_reducedLength_limit_hamilton_jacobi_eq_in_chart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backward_flow_reducedLength_limit_hamilton_jacobi_eq_in_chart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backward_flow_reducedLength_limit_hamilton_jacobi_eq_in_chart ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backward_flow_reducedLength_limit_hamilton_jacobi_eq_in_chart

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
