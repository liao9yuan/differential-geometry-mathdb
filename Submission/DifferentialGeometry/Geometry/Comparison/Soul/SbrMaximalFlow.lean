import Submission.DifferentialGeometry.Geometry.Comparison.Soul.SbrFiniteFlow
import Submission.DifferentialGeometry.Geometry.Comparison.Soul.SbrFlowUniqueness
import Submission.DifferentialGeometry.Geometry.Comparison.Soul.SbrMaxLevelLimit

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Manifold _root_.Submission.Manifold _root_.Set
open scoped _root_.Topology _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.NNReal
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Exponential

namespace DifferentialGeometry.Geometry.Topology

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)]

theorem exists_maximal_normalized_ascent_curve
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    (F : M → ℝ) (L : ℝ≥0) (hF : LipschitzWith L F)
    (hconc : ∀ (p : M) (v : TangentSpace I p),
      ConcaveOn ℝ _root_.Set.univ (fun t => F (intrinsicGeodesic g hEnorm p v t)))
    (hC : IsCompact {z : M | 0 ≤ F z})
    {a m : ℝ} (ha : 0 ≤ a) (ham : a < m)
    (hmax : ∃ q : M, F q = m ∧ ∀ z : M, F z ≤ m)
    (x : M) (hx : F x = a) :
    ∃ eta : ℝ → M,
      ContinuousOn eta (_root_.Set.Icc a m) ∧ eta a = x ∧
      _root_.Set.MapsTo eta (_root_.Set.Icc a m) {z : M | 0 ≤ F z} ∧
      (∀ t ∈ _root_.Set.Icc a m, F (eta t) = t) ∧
      (∀ s ∈ _root_.Set.Ico a m,
        let G := intrinsicGeneralizedGradient g hEnorm hF hconc (eta s)
        G ≠ 0 ∧ HasMFDerivWithinAt 𝓘(ℝ, ℝ) I eta (_root_.Set.Ici s) s
          (ContinuousLinearMap.toSpanSingleton ℝ ((g.inner (eta s) G G)⁻¹ • G))) ∧
      ∀ T ∈ _root_.Set.Ioo a m,
        LipschitzOnWith
          (Real.toNNReal (Metric.diam {z : M | 0 ≤ F z} / (m - T))) eta (_root_.Set.Icc a T) := by
  classical
  let J := {T : ℝ // T ∈ _root_.Set.Ioo a m}
  have hfinite (T : J) := exists_finite_normalized_ascent_curve
    g hEnorm F L hF hconc hC ha T.2.1 T.2.2 hmax x hx
  choose c hcLip hcStart hcMaps hcLevel hcDer using hfinite
  have hcAgree (T U : J) : _root_.Set.EqOn (c T) (c U) (_root_.Set.Icc a (_root_.Min.min T.1 U.1)) := by
    apply eqOn_normalized_intrinsicGeneralizedGradient_overlap g hEnorm hF hconc
      (c T) (c U) (hcLip T).continuous.continuousOn (hcLip U).continuous.continuousOn
      (fun s hs => (hcDer T s hs).2) (fun s hs => (hcDer U s hs).2)
      (fun s hs => hcLevel T s ⟨hs.1, hs.2.le⟩)
      (fun s hs => hcLevel U s ⟨hs.1, hs.2.le⟩)
    exact (hcStart T).trans (hcStart U).symm
  let middle (s : ℝ) (hs : s ∈ _root_.Set.Ico a m) : J :=
    ⟨(s + m) / 2, by constructor <;> linarith [hs.1, hs.2]⟩
  have hmiddle (s : ℝ) (hs : s ∈ _root_.Set.Ico a m) : s < (middle s hs).1 := by
    dsimp only [middle]
    linarith [hs.2]
  let eta : ℝ → M := fun s => if hs : s ∈ _root_.Set.Ico a m then c (middle s hs) s else x
  have hpatch (T : J) (s : ℝ) (hs : s ∈ _root_.Set.Icc a T.1) : eta s = c T s := by
    have hsm : s ∈ _root_.Set.Ico a m := ⟨hs.1, hs.2.trans_lt T.2.2⟩
    simp only [eta, dif_pos hsm]
    exact hcAgree (middle s hsm) T ⟨hs.1, le_min (hmiddle s hsm).le hs.2⟩
  have hetaData (s : ℝ) (hs : s ∈ _root_.Set.Ico a m) :
      eta s ∈ {z : M | 0 ≤ F z} ∧ F (eta s) = s := by
    have hsT : s ∈ _root_.Set.Icc a (middle s hs).1 := ⟨hs.1, (hmiddle s hs).le⟩
    rw [hpatch (middle s hs) s hsT]
    exact ⟨hcMaps (middle s hs) hsT, hcLevel (middle s hs) s hsT⟩
  have hetaStart : eta a = x := by
    have ha' : a ∈ _root_.Set.Ico a m := ⟨le_rfl, ham⟩
    rw [hpatch (middle a ha') a ⟨le_rfl, (hmiddle a ha').le⟩]
    exact hcStart _
  have hetaCont : ContinuousOn eta (_root_.Set.Ico a m) := by
    intro s hs
    let T := middle s hs
    have hsT : s < T.1 := hmiddle s hs
    apply (hcLip T).continuous.continuousAt.continuousWithinAt.congr_of_eventuallyEq
      ?_ (hpatch T s ⟨hs.1, hsT.le⟩)
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (gt_mem_nhds hsT)] with t ht htT
    exact hpatch T t ⟨ht.1, htT.le⟩
  have hetaDer (s : ℝ) (hs : s ∈ _root_.Set.Ico a m) :
      let G := intrinsicGeneralizedGradient g hEnorm hF hconc (eta s)
      G ≠ 0 ∧ HasMFDerivWithinAt 𝓘(ℝ, ℝ) I eta (_root_.Set.Ici s) s
        (ContinuousLinearMap.toSpanSingleton ℝ ((g.inner (eta s) G G)⁻¹ • G)) := by
    let T := middle s hs
    have hsT : s < T.1 := hmiddle s hs
    have hbase : eta s = c T s := hpatch T s ⟨hs.1, hsT.le⟩
    have hevent : eta =ᶠ[𝓝[_root_.Set.Ici s] s] c T := by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (gt_mem_nhds hsT)] with t ht htT
      exact hpatch T t ⟨hs.1.trans ht, htT.le⟩
    have hdata := hcDer T s ⟨hs.1, hsT⟩
    refine ⟨?_, ?_⟩
    · rw [hbase]
      exact hdata.1
    · have hder := hdata.2.congr_of_eventuallyEq hevent hbase
      rw [← hbase] at hder
      exact hder
  have hetaDist (q : M) (_hqC : q ∈ {z : M | 0 ≤ F z}) (hqm : F q = m) :
      AntitoneOn (fun s => _root_.Dist.dist (eta s) q) (_root_.Set.Ico a m) := by
    intro s hs t ht hst
    let T := middle t ht
    have htT : t < T.1 := hmiddle t ht
    have hsT : s ∈ _root_.Set.Icc a T.1 := ⟨hs.1, hst.trans htT.le⟩
    have htT' : t ∈ _root_.Set.Icc a T.1 := ⟨ht.1, htT.le⟩
    have hdist := antitoneOn_dist_fixed_normalized_intrinsicGeneralizedGradient
      g hEnorm hF hconc (c T) (hcLip T).continuous.continuousOn
      (fun r hr => (hcDer T r hr).2) q (by
        intro r hr
        rw [hcLevel T r ⟨hr.1, hr.2.le⟩, hqm]
        exact hr.2.le.trans T.2.2.le)
    change _root_.Dist.dist (eta t) q ≤ _root_.Dist.dist (eta s) q
    rw [hpatch T t htT', hpatch T s hsT]
    exact hdist hsT htT' hst
  obtain ⟨q, _hqC, _hqm, hbarCont, hbarEq, _hbarEnd, hbarData⟩ :=
    exists_continuous_level_extension_of_dist_antitone hC F hF.continuous.continuousOn
      eta ham hetaCont (fun s hs => (hetaData s hs).1)
      (fun s hs => (hetaData s hs).2) hetaDist
  let etaBar := Function.update eta m q
  have hbarPatch (T : J) (s : ℝ) (hs : s ∈ _root_.Set.Icc a T.1) : etaBar s = c T s :=
    (hbarEq ⟨hs.1, hs.2.trans_lt T.2.2⟩).trans (hpatch T s hs)
  refine ⟨etaBar, hbarCont, ?_, (fun s hs => (hbarData s hs).1),
    (fun s hs => (hbarData s hs).2), ?_, ?_⟩
  · exact (hbarEq ⟨le_rfl, ham⟩).trans hetaStart
  · intro s hs
    have hbase : etaBar s = eta s := hbarEq hs
    have hevent : etaBar =ᶠ[𝓝[_root_.Set.Ici s] s] eta := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds (gt_mem_nhds hs.2)] with t ht
      exact Function.update_of_ne ht.ne q eta
    have hdata := hetaDer s hs
    refine ⟨?_, ?_⟩
    · rw [hbase]
      exact hdata.1
    · have hder := hdata.2.congr_of_eventuallyEq hevent hbase
      rw [← hbase] at hder
      exact hder
  · intro T hT
    let U : J := ⟨T, hT⟩
    intro s hs t ht
    rw [hbarPatch U s hs, hbarPatch U t ht]
    exact hcLip U s t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.exists_maximal_normalized_ascent_curve then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.exists_maximal_normalized_ascent_curve"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.exists_maximal_normalized_ascent_curve ``Submission.DifferentialGeometry.Geometry.Topology.exists_maximal_normalized_ascent_curve

end DifferentialGeometry.Geometry.Topology
