import Submission.DifferentialGeometry.Analysis.Calculus.MapConvergence.MovingInputs
import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Transition.IntrinsicOverlap
import Submission.DifferentialGeometry.Analysis.Calculus.MapConvergence.Composition
import Submission.DifferentialGeometry.Geometry.Exponential.NormalBall.Recenter
import Submission.DifferentialGeometry.Topology.UniformConvergence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.Filter
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.Submission.Topology _root_.ENNReal

namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

variable {E P H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : ℕ → Type*} [∀ k, TopologicalSpace (M k)] [∀ k, ChartedSpace H (M k)]
  [∀ k, IsManifold I ∞ (M k)] [∀ k, T2Space (M k)] [∀ k, SigmaCompactSpace (M k)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [∀ k, PseudoEMetricSpace (M k)]
  [∀ k, RiemannianBundle (fun x : M k => TangentSpace I x)]
  [∀ k, IsRiemannianManifold I (M k)] [∀ k, CompleteSpace (M k)]
  [∀ k, IsContinuousRiemannianBundle E (fun x : M k => TangentSpace I x)]

theorem IntrinsicBallChart.eventually_mem_target_and_dist_inv_lt
    (g : ∀ k, SmoothRiemannianMetric I (M k))
    (hEnorm : ∀ k (x : M k) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g k).inner x v v)))
    (p q : ∀ k, M k) {rho s : ℝ} (hrho : 0 < rho) (hs : s < rho / 2)
    (c : ∀ k, IntrinsicBallChart (I := I) (g k) (hEnorm k) (p k) rho)
    (d : ∀ k, IntrinsicBallChart (I := I) (g k) (hEnorm k) (q k) rho)
    (hnear : ∀ᶠ k in _root_.Filter.atTop, _root_.EDist.edist (p k) (q k) < ENNReal.ofReal (rho / 4))
    {J : E → E}
    (hJ : CheegerGromovCompactness.MapCInfConvergenceOnCompacts
      (Metric.ball (0 : E) (rho / 2))
      (fun k => ((c k).toNormalBallChart (g k) (hEnorm k) (p k) hrho).transition
        ((d k).toNormalBallChart (g k) (hEnorm k) (q k) hrho)) J)
    (hJc : ContinuousOn J (Metric.ball (0 : E) (rho / 2)))
    {U K : Set P} {Phi : ℕ → P → E} {PhiInf : P → E}
    (hPhi : CheegerGromovCompactness.MapCInfConvergenceOnCompacts U Phi PhiInf)
    (hK : IsCompact K) (hKU : K ⊆ U) (hPhiInf : ContinuousOn PhiInf K)
    (hmap : _root_.Set.MapsTo PhiInf K (Metric.ball 0 s)) {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ k in _root_.Filter.atTop, ∀ z ∈ K,
      (c k).hom (Phi k z) ∈
        ((d k).toNormalBallChart (g k) (hEnorm k) (q k) hrho).restrictBall.target ∧
      dist ((d k).hom.symm ((c k).hom (Phi k z))) (J (PhiInf z)) < eps := by
  have hL : IsCompact (Metric.closedBall (0 : E) s) := _root_.ProperSpace.isCompact_closedBall 0 s
  have hLV : Metric.closedBall (0 : E) s ⊆ Metric.ball 0 (rho / 2) :=
    Metric.closedBall_subset_ball hs
  have hPhiMap := hPhi.eventually_mapsTo hK hKU hPhiInf Metric.isOpen_ball hmap
  have hcomp := hJ.eventually_dist_comp_lt hPhi hK hKU hL hLV (hJc.mono hLV)
    (hPhiMap.mono fun _ hk => hk.mono_right Metric.ball_subset_closedBall)
    (hmap.mono_right Metric.ball_subset_closedBall) heps
  filter_upwards [hnear, hPhiMap, hcomp] with k hk hmk hck z hz
  refine ⟨?_, hck z hz⟩
  have hov := (c k).overlap_on_ball_of_edist_add_le
    (g k) (hEnorm k) (p k) (q k) (d k) hrho hrho
    (s := rho / 2) (by linarith) (show
      _root_.EDist.edist (p k) (q k) + ENNReal.ofReal (rho / 2) ≤ ENNReal.ofReal rho from by
      calc
        _root_.EDist.edist (p k) (q k) + ENNReal.ofReal (rho / 2) ≤
            ENNReal.ofReal (rho / 4) + ENNReal.ofReal (rho / 2) := add_le_add hk.le le_rfl
        _ = ENNReal.ofReal (rho / 4 + rho / 2) :=
          (ENNReal.ofReal_add (by positivity) (by positivity)).symm
        _ ≤ ENNReal.ofReal rho := ENNReal.ofReal_le_ofReal (by linarith))
  exact (hov (Phi k z) (hLV (Metric.ball_subset_closedBall (hmk hz)))).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.eventually_mem_target_and_dist_inv_lt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.eventually_mem_target_and_dist_inv_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.eventually_mem_target_and_dist_inv_lt ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.eventually_mem_target_and_dist_inv_lt

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
end

noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.Filter
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.Submission.Topology _root_.ENNReal

namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

variable {E P H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : ℕ → Type*} [∀ k, TopologicalSpace (M k)] [∀ k, ChartedSpace H (M k)]
  [∀ k, IsManifold I ∞ (M k)] [∀ k, T2Space (M k)] [∀ k, SigmaCompactSpace (M k)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [∀ k, PseudoEMetricSpace (M k)]
  [∀ k, RiemannianBundle (fun x : M k => TangentSpace I x)]
  [∀ k, IsRiemannianManifold I (M k)] [∀ k, CompleteSpace (M k)]
  [∀ k, IsContinuousRiemannianBundle E (fun x : M k => TangentSpace I x)]

private theorem IntrinsicBallChart.tendstoUniformlyOn_recenter_inv_comp
    (g : ∀ k, SmoothRiemannianMetric I (M k))
    (hEnorm : ∀ k (x : M k) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g k).inner x v v)))
    (p q : ∀ k, M k) {rho s : ℝ} (hrho : 0 < rho) (hs : s < rho / 2)
    (c : ∀ k, IntrinsicBallChart (I := I) (g k) (hEnorm k) (p k) rho)
    (d : ∀ k, IntrinsicBallChart (I := I) (g k) (hEnorm k) (q k) rho)
    (hnear : ∀ᶠ k in _root_.Filter.atTop, _root_.EDist.edist (p k) (q k) < ENNReal.ofReal (rho / 4))
    {J : E → E}
    (hJ : CheegerGromovCompactness.MapCInfConvergenceOnCompacts
      (Metric.ball (0 : E) (rho / 2))
      (fun k => ((c k).toNormalBallChart (g k) (hEnorm k) (p k) hrho).transition
        ((d k).toNormalBallChart (g k) (hEnorm k) (q k) hrho)) J)
    (hJc : ContinuousOn J (Metric.ball (0 : E) (rho / 2)))
    {U K : Set P} {Phi : ℕ → P → E} {PhiInf : P → E}
    (hPhi : CheegerGromovCompactness.MapCInfConvergenceOnCompacts U Phi PhiInf)
    (hK : IsCompact K) (hKU : K ⊆ U) (hPhiInf : ContinuousOn PhiInf K)
    (hmap : _root_.Set.MapsTo PhiInf K (Metric.ball 0 s))
    (a : E) {r : ℝ} (hr : 0 < r)
    (hball : ∀ k, Metric.ball a r ⊆ Metric.ball (0 : E)
      ((d k).toNormalBallChart (g k) (hEnorm k) (q k) hrho).radius) :
    TendstoUniformlyOn
      (fun k z => (((d k).toNormalBallChart (g k) (hEnorm k) (q k) hrho).recenter
        a hr (hball k)).inv ((c k).hom (Phi k z)))
      (fun z => J (PhiInf z) - a) _root_.Filter.atTop K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro eps heps
  filter_upwards [IntrinsicBallChart.eventually_mem_target_and_dist_inv_lt
    g hEnorm p q hrho hs c d hnear hJ hJc hPhi hK hKU hPhiInf hmap heps] with k hk z hz
  change _root_.Dist.dist (J (PhiInf z) - a) (-a + (d k).hom.symm ((c k).hom (Phi k z))) < eps
  rw [add_comm (-a), ← sub_eq_add_neg, dist_sub_right, dist_comm]
  exact (hk z hz).2

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.tendstoUniformlyOn_recenter_inv_comp
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.tendstoUniformlyOn_recenter_inv_comp target :: scope.openDecls } }

theorem IntrinsicBallChart.eventually_recenter_inv_pairs_mem_ball
    (g : ∀ k, SmoothRiemannianMetric I (M k))
    (hEnorm : ∀ k (x : M k) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g k).inner x v v)))
    (p q : ∀ k, M k) {rho s : ℝ} (hrho : 0 < rho) (hs : s < rho / 2)
    (c : ∀ k, IntrinsicBallChart (I := I) (g k) (hEnorm k) (p k) rho)
    (d : ∀ k, IntrinsicBallChart (I := I) (g k) (hEnorm k) (q k) rho)
    (hnear : ∀ᶠ k in _root_.Filter.atTop, _root_.EDist.edist (p k) (q k) < ENNReal.ofReal (rho / 4))
    {J : E → E}
    (hJ : CheegerGromovCompactness.MapCInfConvergenceOnCompacts
      (Metric.ball (0 : E) (rho / 2))
      (fun k => ((c k).toNormalBallChart (g k) (hEnorm k) (p k) hrho).transition
        ((d k).toNormalBallChart (g k) (hEnorm k) (q k) hrho)) J)
    (hJc : ContinuousOn J (Metric.ball (0 : E) (rho / 2)))
    {U K : Set P} {Phi : ℕ → P → E} {PhiInf : P → E}
    (hPhi : CheegerGromovCompactness.MapCInfConvergenceOnCompacts U Phi PhiInf)
    (hK : IsCompact K) (hKU : K ⊆ U) (hPhiInf : ContinuousOn PhiInf K)
    (hmap : _root_.Set.MapsTo PhiInf K (Metric.ball 0 s))
    (a : E) {r : ℝ} (hr : 0 < r)
    (hball : ∀ k, Metric.ball a r ⊆ Metric.ball (0 : E)
      ((d k).toNormalBallChart (g k) (hEnorm k) (q k) hrho).radius)
    {ι : Type*} [Fintype ι] {V : Set E}
    (weights : E → ι → ℝ) (xi : ℕ → E → ι → E)
    (hconfiguration : CheegerGromovCompactness.MapCInfConvergenceOnCompacts V
      (fun k z => (weights z, xi k z)) (fun z => (weights z, fun _ => z - a)))
    (B : P → E) (hB : _root_.Set.EqOn (fun z => J (PhiInf z)) B K)
    (hBV : _root_.Set.MapsTo B K V) {eps : ℝ}
    (hcenter : _root_.Set.MapsTo (fun z => B z - a) K (Metric.ball 0 eps)) :
    ∀ᶠ k in _root_.Filter.atTop, ∀ z ∈ K,
      (c k).hom (Phi k z) ∈
        ((d k).toNormalBallChart (g k) (hEnorm k) (q k) hrho).restrictBall.target ∧
      ∀ i, ((((d k).toNormalBallChart (g k) (hEnorm k) (q k) hrho).recenter
        a hr (hball k)).inv ((c k).hom (Phi k z)), xi k (B z) i) ∈
        Metric.ball (0 : E × E) eps := by
  have hPhiV : _root_.Set.MapsTo PhiInf K (Metric.ball 0 (rho / 2)) :=
    hmap.mono_right (Metric.ball_subset_ball hs.le)
  have hBc : ContinuousOn B K := (hJc.comp hPhiInf hPhiV).congr hB.symm
  have hX := (IntrinsicBallChart.tendstoUniformlyOn_recenter_inv_comp
    g hEnorm p q hrho hs c d hnear hJ hJc hPhi hK hKU hPhiInf hmap a hr hball).congr_right
      (show _root_.Set.EqOn (fun z => J (PhiInf z) - a) (fun z => B z - a) K from
        fun z hz => congrArg (fun y => y - a) (hB hz))
  have hL := hK.image_of_continuousOn hBc
  have htu := CheegerGromovCompactness.tendstoUniformlyOn_of_cPConvergence
    (hconfiguration.cPConvergenceOn hL (image_subset_iff.mpr hBV) 0)
  have hsnd := uniformContinuous_snd.comp_tendstoUniformlyOn htu
  have hxi : TendstoUniformlyOn (fun k z => xi k (B z))
      (fun z _ => B z - a) _root_.Filter.atTop K :=
    (hsnd.comp B).mono (fun z hz => ⟨z, hz, rfl⟩)
  have hpairs := hX.eventually_forall_pair_mem_ball_of_isCompact hxi hK
    (hBc.sub continuousOn_const) hcenter
  have htarget := IntrinsicBallChart.eventually_mem_target_and_dist_inv_lt
    g hEnorm p q hrho hs c d hnear hJ hJc hPhi hK hKU hPhiInf hmap zero_lt_one
  filter_upwards [hpairs, htarget] with k hk htk z hz
  exact ⟨(htk z hz).1, hk z hz⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.eventually_recenter_inv_pairs_mem_ball then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.eventually_recenter_inv_pairs_mem_ball"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.eventually_recenter_inv_pairs_mem_ball ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.eventually_recenter_inv_pairs_mem_ball

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
end
