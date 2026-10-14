import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedLength.WeakBarrier
import Submission.DifferentialGeometry.Geometry.Operator.Laplacian.Comparison
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.DimensionZero

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.Set _root_.Filter _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M] {D : RealTimeInterval}

theorem redLength_time_deriv_add_laplacian_lower_test
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (K T sigma tau : ℝ)
    (hg : RiemannianMetricComplete (I := I) (S.base.metric T))
    (htau : 0 < tau) (htausigma : tau < sigma)
    (hreg : _root_.Set.Icc (T - sigma) T ⊆ D.regular)
    (hRm : ∀ t ∈ _root_.Set.Icc (T - sigma) T, ∀ y : M,
      normSq0S (I := I) (S.base.metric t) y 4 (S.base.rm04 t y) ≤ K)
    (p q : M) (phi : ℝ × M → ℝ) (d : ℝ)
    (hphi : ContMDiffAt I 𝓘(ℝ, ℝ) 2 (fun y => phi (tau, y)) q)
    (hdt : HasDerivAt (fun t => phi (t, q)) d tau)
    (hmin : IsLocalMin (fun z : ℝ × M => redLength S T p z.2 z.1 - phi z) (tau, q)) :
    d + laplacian (I := I) (LeviCivita (I := I) (S.base.metric (T - tau)))
        (S.base.metric (T - tau)) (fun y => phi (tau, y)) q ≤
      ((Module.finrank ℝ E : ℝ) / 2 - redLength S T p q tau) / tau := by
  by_cases hdim : Module.finrank ℝ E = 0
  · let _ : Subsingleton E := Module.finrank_zero_iff.mp hdim
    let _ : Subsingleton (TangentSpace I q) := inferInstanceAs (Subsingleton E)
    have hlap : laplacian (I := I) (LeviCivita (I := I) (S.base.metric (T - tau)))
        (S.base.metric (T - tau)) (fun y => phi (tau, y)) q = 0 := by
      unfold laplacian divergence
      have heq : ((LeviCivita (I := I) (S.base.metric (T - tau)))
          (fun y => gradientFun (S.base.metric (T - tau)) (fun z => phi (tau, z)) y) q).toLinearMap = 0 :=
        Subsingleton.elim _ _
      rw [heq, map_zero]
    have htime : IsLocalMin (fun t => -phi (t, q)) tau := by
      have hc : ContinuousAt (fun t : ℝ => (t, q)) tau := continuousAt_id.prodMk continuousAt_const
      change ∀ᶠ t in 𝓝 tau, -phi (tau, q) ≤ -phi (t, q)
      simpa only [redLength, lCost_eq_zero_of_finrank_eq_zero hdim, zero_div, zero_sub] using
        hc.tendsto.eventually hmin
    have hd := htime.hasDerivAt_eq_zero hdt.neg
    simp only [hlap, hdim, Nat.cast_zero, zero_div, redLength,
      lCost_eq_zero_of_finrank_eq_zero hdim, sub_self, add_zero, neg_eq_zero.mp hd, le_refl]
  let _ : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let _ : PseudoMetricSpace M := TopologicalSpace.pseudoMetrizableSpacePseudoMetric M
  apply le_of_forall_pos_le_add
  intro eps heps
  obtain ⟨U, J, Phi, dPhi, hU, hq, hJ, ht, _hJsub, hupper, heq, hPhi, hdPhi, hbound⟩ :=
    exists_redWeak_sup S hS K T sigma tau hg htau htausigma hreg hRm p q eps heps
  have htime : IsLocalMin (fun t => Phi q t - phi (t, q)) tau := by
    have hc : ContinuousAt (fun t : ℝ => (t, q)) tau := continuousAt_id.prodMk continuousAt_const
    have hm := hc.tendsto.eventually hmin
    filter_upwards [hm, hJ.mem_nhds ht] with t hmt htJ
    change Phi q tau - phi (tau, q) ≤ Phi q t - phi (t, q)
    rw [heq]
    exact hmt.trans (sub_le_sub_right (hupper q hq t htJ) _)
  have hderiv : dPhi = d :=
    sub_eq_zero.mp (htime.hasDerivAt_eq_zero (hdPhi.sub hdt))
  have hspace : IsLocalMin (fun y => Phi y tau - phi (tau, y)) q := by
    have hc : ContinuousAt (fun y : M => (tau, y)) q := continuousAt_const.prodMk continuousAt_id
    have hm := hc.tendsto.eventually hmin
    filter_upwards [hm, hU.mem_nhds hq] with y hmy hyU
    change Phi q tau - phi (tau, q) ≤ Phi y tau - phi (tau, y)
    rw [heq]
    exact hmy.trans (sub_le_sub_right (hupper y hyU tau ht) _)
  have hPhiAt : ContMDiffAt I 𝓘(ℝ, ℝ) 2 (fun y => Phi y tau) q :=
    ((hPhi q hq).contMDiffAt (hU.mem_nhds hq)).of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  have hcov : IsMetricCompatible (I := I) (LeviCivita (I := I) (S.base.metric (T - tau)))
      (S.base.metric (T - tau)) := by
    simpa only [LeviCivita] using
      leviCivitaConnectionOfMetric_isMetricCompatible (I := I) (S.base.metric (T - tau))
  have hlap := laplacian_le_of_isLocalMin_sub
    (LeviCivita (I := I) (S.base.metric (T - tau))) (S.base.metric (T - tau)) hcov
    BoundarylessManifold.isInteriorPoint hPhiAt hphi hspace
  rw [hderiv] at hbound
  linarith only [hlap, hbound]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.redLength_time_deriv_add_laplacian_lower_test then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.redLength_time_deriv_add_laplacian_lower_test"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.redLength_time_deriv_add_laplacian_lower_test ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.redLength_time_deriv_add_laplacian_lower_test

end DifferentialGeometry.PDE.RicciFlow.Perelman
