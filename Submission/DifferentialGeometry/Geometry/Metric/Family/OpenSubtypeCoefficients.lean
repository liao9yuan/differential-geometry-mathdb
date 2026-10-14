import Submission.DifferentialGeometry.Geometry.Metric.Family.ChartCurvature.MetricFamilySmoothOn
import Submission.DifferentialGeometry.Geometry.Geodesic.Chart.OpenSubtype
import Submission.DifferentialGeometry.Topology.Manifold.OpenSubtypeModel

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Set
open scoped _root_.Manifold _root_.ContDiff _root_.Topology _root_.BigOperators

namespace DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

private theorem localFrame_opens_model (U : TopologicalSpace.Opens F) (a z : U)
    (i : Fin (Module.finrank ℝ F)) :
    (_root_.FiberBundle.trivializationAt F (TangentSpace 𝓘(ℝ, F)) a).localFrame
      (Module.finBasis ℝ F) i z = Module.finBasis ℝ F i := by
  have hz : z ∈ (_root_.FiberBundle.trivializationAt F (TangentSpace 𝓘(ℝ, F)) a).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet, ← extChartAt_source (I := 𝓘(ℝ, F)),
      DifferentialGeometry.extChartAt_opens_source]
    trivial
  rw [(_root_.FiberBundle.trivializationAt F (TangentSpace 𝓘(ℝ, F)) a).localFrame_apply_of_mem_baseSet
    (Module.finBasis ℝ F) hz]
  rw [Trivialization.basisAt, Module.Basis.map_apply]
  change ((_root_.FiberBundle.trivializationAt F (TangentSpace 𝓘(ℝ, F)) a).linearEquivAt ℝ z hz).symm
      (Module.finBasis ℝ F i) = _
  have h := congrArg (fun L : F →L[ℝ] F => L (Module.finBasis ℝ F i))
    (DifferentialGeometry.symmL_opens_model U a z)
  rw [Trivialization.linearEquivAt_symm_apply]
  exact (Trivialization.symmL_apply (R := ℝ) _ hz _).symm.trans h

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.localFrame_opens_model
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.localFrame_opens_model target :: scope.openDecls } }

theorem inner_opens_continuousAt
    {U : TopologicalSpace.Opens F} {D : RealTimeInterval}
    {G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, F) U}
    (hG : MetricFamilySmoothOn D G) {q : ℝ × U} (hq : q.1 ∈ D.regular) :
    ContinuousAt (show ℝ × U → F →L[ℝ] F →L[ℝ] ℝ from fun p => (G p.1).inner p.2) q := by
  classical
  let e := _root_.FiberBundle.trivializationAt F (TangentSpace 𝓘(ℝ, F)) q.2
  let b := Module.finBasis ℝ F
  have hframe : IsLocalFrameOn 𝓘(ℝ, F) F ∞ (e.localFrame b) e.baseSet :=
    e.isLocalFrameOn_localFrame_baseSet 𝓘(ℝ, F) ∞ b
  have hnb : (D.regular ×ˢ e.baseSet : Set (ℝ × U)) ∈ 𝓝 q :=
    prod_mem_nhds (D.regular_isOpen.mem_nhds hq)
      (e.open_baseSet.mem_nhds (by simp [e]))
  have hc (i j : Fin (Module.finrank ℝ F)) :
      ContinuousAt (fun p : ℝ × U => (G p.1).inner p.2 (b i) (b j)) q := by
    have h := ((hG.frameCompSmooth (e.localFrame b) hframe i j).continuousOn).continuousAt hnb
    simpa only [e, b, localFrame_opens_model] using h
  apply continuousAt_clm_apply.mpr
  intro v
  apply continuousAt_clm_apply.mpr
  intro w
  have hs : ContinuousAt (fun p : ℝ × U =>
      ∑ i, ∑ j, b.repr v i * b.repr w j * (G p.1).inner p.2 (b i) (b j)) q :=
    tendsto_finsetSum Finset.univ fun i _ => tendsto_finsetSum Finset.univ fun j _ =>
      continuousAt_const.mul (hc i j)
  apply hs.congr_of_eventuallyEq
  apply Filter.Eventually.of_forall
  intro p
  let A : F →L[ℝ] F →L[ℝ] ℝ := (G p.1).inner p.2
  have hbase (i j : Fin (Module.finrank ℝ F)) :
      A (b i) (b j) = (G p.1).inner p.2 (b i) (b j) := by rfl
  change A v w = _
  calc
    A v w = A (∑ i, b.repr v i • b i) (∑ j, b.repr w j • b j) := by
      rw [b.sum_repr, b.sum_repr]
    _ = ∑ i, ∑ j, (b.repr v i * b.repr w j) *
        (G p.1).inner p.2 (b i) (b j) := by
      simp only [map_sum, map_smul, sum_apply, smul_apply,
        smul_eq_mul, Finset.mul_sum, hbase]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.inner_opens_continuousAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.inner_opens_continuousAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.inner_opens_continuousAt ``Submission.DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.inner_opens_continuousAt

theorem inner_opens_continuousOn
    {U : TopologicalSpace.Opens F} {D : RealTimeInterval}
    {G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, F) U}
    (hG : MetricFamilySmoothOn D G) :
    ContinuousOn (show ℝ × U → F →L[ℝ] F →L[ℝ] ℝ from fun p => (G p.1).inner p.2)
      (D.regular ×ˢ Set.univ) :=
  fun _ hp => (inner_opens_continuousAt hG hp.1).continuousWithinAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.inner_opens_continuousOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.inner_opens_continuousOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.inner_opens_continuousOn ``Submission.DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.inner_opens_continuousOn

open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic

theorem chartChristoffelContraction_opens_continuousAt
    {U : TopologicalSpace.Opens F} {D : RealTimeInterval}
    {G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, F) U}
    (hG : MetricFamilySmoothOn D G) {q : ℝ × U × F} (hq : q.1 ∈ D.regular) :
    ContinuousAt (fun p : ℝ × U × F =>
      chartChristoffelContraction (G p.1) p.2.1 p.2.2 p.2.2 (p.2.1 : F)) q := by
  classical
  let a := q.2.1
  have hbase : Continuous (fun p : ℝ × U × F => (p.1, (p.2.1 : F))) :=
    continuous_fst.prodMk (continuous_subtype_val.comp (continuous_fst.comp continuous_snd))
  have hc (i j k : Fin (Module.finrank ℝ F)) :
      ContinuousAt (fun p : ℝ × U × F => chartChristoffel (G p.1) a i j k (p.2.1 : F)) q := by
    have h : ContinuousOn
        (fun p : ℝ × F => chartChristoffel (G p.1) a i j k p.2)
        (D.regular ×ˢ interior (extChartAt 𝓘(ℝ, F) a).target) :=
      MetricFamilySmoothOn.chartChristoffelOnE_continuousOn
        (I := 𝓘(ℝ, F)) (M := U) (g_fam := G) hG (J := D.regular)
        (fun _ h => h) D.regular_isOpen.uniqueDiffOn a i j k
    have hat : ContinuousAt
        (fun p : ℝ × F => chartChristoffel (G p.1) a i j k p.2) (q.1, (q.2.1 : F)) :=
      h.continuousAt ((D.regular_isOpen.prod isOpen_interior).mem_nhds
        ⟨hq, DifferentialGeometry.mem_interior_extChartAt_opens_target U a q.2.1⟩)
    exact ContinuousAt.comp (f := fun p : ℝ × U × F => (p.1, (p.2.1 : F)))
      (x := q) hat hbase.continuousAt
  have hp (i : Fin (Module.finrank ℝ F)) :
      ContinuousAt (fun p : ℝ × U × F => chartCoord (E := F) i p.2.2) q :=
    ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis F).coord i).toContinuousLinearMap.continuous.continuousAt.comp
      (continuous_snd.comp continuous_snd).continuousAt
  change ContinuousAt (fun p : ℝ × U × F =>
    chartChristoffelContraction (G p.1) a p.2.2 p.2.2 (p.2.1 : F)) q
  unfold chartChristoffelContraction
  exact tendsto_finsetSum Finset.univ fun k _ =>
    (tendsto_finsetSum Finset.univ fun i _ =>
      tendsto_finsetSum Finset.univ fun j _ => ((hc i j k).mul (hp i)).mul (hp j)).smul
        (continuousAt_const)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.chartChristoffelContraction_opens_continuousAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.chartChristoffelContraction_opens_continuousAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.chartChristoffelContraction_opens_continuousAt ``Submission.DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.chartChristoffelContraction_opens_continuousAt

theorem chartChristoffelContraction_opens_continuousOn
    {U : TopologicalSpace.Opens F} {D : RealTimeInterval}
    {G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, F) U}
    (hG : MetricFamilySmoothOn D G) :
    ContinuousOn (fun p : ℝ × U × F =>
      chartChristoffelContraction (G p.1) p.2.1 p.2.2 p.2.2 (p.2.1 : F))
      (D.regular ×ˢ Set.univ) :=
  fun _ hp => (chartChristoffelContraction_opens_continuousAt hG hp.1).continuousWithinAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.chartChristoffelContraction_opens_continuousOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.chartChristoffelContraction_opens_continuousOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.chartChristoffelContraction_opens_continuousOn ``Submission.DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.chartChristoffelContraction_opens_continuousOn

end DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn

end
