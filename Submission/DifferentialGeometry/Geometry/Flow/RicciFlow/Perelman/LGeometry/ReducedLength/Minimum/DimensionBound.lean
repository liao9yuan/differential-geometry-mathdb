import Submission.DifferentialGeometry.Analysis.Calculus.Derivative.Right
import Submission.DifferentialGeometry.Geometry.Operator.Laplacian.Minimum
import Submission.DifferentialGeometry.Geometry.Operator.Gradient.Regularity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedLength.Minimum.TimeRegularity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ShortTime.ReducedLengthLimit
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedLength.WeakBarrier

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Function _root_.Manifold _root_.Submission.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.ContDiff _root_.ENNReal _root_.Manifold _root_.Submission.Manifold _root_.NNReal _root_.Topology _root_.Submission.Topology

open _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Tensor0SBundle

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M]
variable {D : RealTimeInterval}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem exists_redMin_seed [ConnectedSpace M]
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (K T sigma tau : Real)
    (hg : RiemannianMetricComplete (I := I) (S.base.metric T))
    (htau : 0 < tau) (htausigma : tau < sigma)
    (hreg : _root_.Set.Icc (T - sigma) T ⊆ D.regular)
    (hRm : ∀ q ∈ _root_.Set.Icc (T - sigma) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric q) z 4 (S.base.rm04 q z) ≤ K)
    (x : M) :
    ∃ a ∈ _root_.Set.Ioo (0 : Real) tau,
      redMinVal S T x a ≤ (Module.finrank Real E : Real) / 2 := by
  have hsigma : 0 < sigma := htau.trans htausigma
  have hT : T ∈ D.regular := by
    apply hreg
    exact ⟨by linarith, le_rfl⟩
  let Z0 : TangentSpace I x := 0
  have hzeroDom : (0 : Real) ∈ lRegularizedDomain S T x Z0 :=
    zero_mem_lRegularizedDomain S hS T x Z0 hT
  have hdomEv : ∀ᶠ s in 𝓝[>] (0 : Real),
      s ∈ lRegularizedDomain S T x Z0 :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      ((lRegularizedDomain_isOpen S T x Z0).mem_nhds hzeroDom)
  have hnpos : 0 < (Module.finrank Real E : Real) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (Module.finrank Real E))
  have hn2 : 0 < (Module.finrank Real E : Real) / 2 := div_pos hnpos (by norm_num)
  have hlim : _root_.Filter.Tendsto
      (fun s : Real ↦ lRegularizedAction S T (lRegularizedCurve S T x Z0) 0 s / (2 * s))
      (𝓝[>] (0 : Real)) (nhds 0) := by
    simpa only [Z0, ContinuousLinearMap.map_zero] using
      tendsto_lRegularizedAction_div_at_zero (I := I) S hS T x Z0 hT
  have hsmall : ∀ᶠ s in 𝓝[>] (0 : Real),
      lRegularizedAction S T (lRegularizedCurve S T x Z0) 0 s / (2 * s) <
        (Module.finrank Real E : Real) / 2 :=
    hlim.eventually (Iio_mem_nhds hn2)
  have htime : ∀ᶠ s in 𝓝[>] (0 : Real),
      s ∈ _root_.Set.Ioo (0 : Real) (Real.sqrt tau) :=
    Ioo_mem_nhdsGT (Real.sqrt_pos.2 htau)
  obtain ⟨s, ⟨hsact, hstime⟩, hsdom⟩ :=
    Filter.Eventually.exists ((hsmall.and htime).and hdomEv)
  let a : Real := s ^ 2
  have ha : 0 < a := by simpa only [a] using sq_pos_of_pos hstime.1
  have hatau : a < tau := by
    dsimp only [a]
    rw [← Real.sq_sqrt htau.le]
    exact (sq_lt_sq₀ hstime.1.le (Real.sqrt_nonneg tau)).2 hstime.2
  have hasigma : a < sigma := hatau.trans htausigma
  have hregA : _root_.Set.Icc (T - a) T ⊆ D.regular := by
    intro q hq
    apply hreg
    exact ⟨(sub_le_sub_left hasigma.le T).trans hq.1, hq.2⟩
  have hRmA : ∀ q ∈ _root_.Set.Icc (T - a) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric q) z 4 (S.base.rm04 q z) ≤ K := by
    intro q hq z
    exact hRm q ⟨(sub_le_sub_left hasigma.le T).trans hq.1, hq.2⟩ z
  obtain ⟨y, _Z, _hZmin, _hZend, hval, hmin⟩ :=
    exists_redMin_vec (I := I) S hS K T hg a ha hregA hRmA x
  have hbdd := lRegularizedCosts_bdd_rm (I := I) S hS K T 0 s le_rfl hstime.1.le
    (by simpa only [a] using hregA) (by simpa only [a] using hRmA)
    x (lRegularizedCurve S T x Z0 s)
  have hcost := lCost_le_ray_bdd (I := I) S hS T x Z0 s hstime.1 hsdom hbdd
  have hred : redLength S T x (lRegularizedCurve S T x Z0 s) a ≤
      lRegularizedAction S T (lRegularizedCurve S T x Z0) 0 s / (2 * s) := by
    rw [redLength, show Real.sqrt a = s by
      simpa only [a] using Real.sqrt_sq hstime.1.le]
    exact (div_le_div_iff_of_pos_right (mul_pos (by norm_num) hstime.1)).2 hcost
  refine ⟨a, ⟨ha, hatau⟩, ?_⟩
  rw [hval]
  exact (hmin (lRegularizedCurve S T x Z0 s)).trans (hred.trans hsact.le)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.exists_redMin_seed
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.exists_redMin_seed target :: scope.openDecls } }

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_redLen_le [ConnectedSpace M]
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (K T sigma tau : Real)
    (hg : RiemannianMetricComplete (I := I) (S.base.metric T))
    (htau : 0 < tau) (htausigma : tau < sigma)
    (hreg : _root_.Set.Icc (T - sigma) T ⊆ D.regular)
    (hRm : ∀ q ∈ _root_.Set.Icc (T - sigma) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric q) z 4 (S.base.rm04 q z) ≤ K)
    (x : M) :
    ∃ y : M, redLength S T x y tau ≤
      (Module.finrank Real E : Real) / 2 := by
  have hsigma : 0 < sigma := htau.trans htausigma
  obtain ⟨a, ha, hseed⟩ :=
    exists_redMin_seed (I := I) S hS K T sigma tau hg htau htausigma hreg hRm x
  let f : Real → Real := redMinVal S T x
  have hfcont : ContinuousOn f (_root_.Set.Icc a tau) := by
    apply (redMinVal_cont (I := I) S hS K T sigma hg hsigma hreg hRm x).mono
    intro r hr
    exact ⟨ha.1.trans_le hr.1, hr.2.trans_lt htausigma⟩
  have hfence : ∀ r ∈ _root_.Set.Icc a tau,
      f r ≤ (Module.finrank Real E : Real) / 2 := by
    apply le_of_upper_support hfcont (by simpa only [f] using hseed)
    intro t ht hbad
    have ht0 : 0 < t := ha.1.trans_le ht.1
    have htsigma : t < sigma := ht.2.trans htausigma
    have hregT : _root_.Set.Icc (T - t) T ⊆ D.regular := by
      intro q hq
      exact hreg ⟨(sub_le_sub_left htsigma.le T).trans hq.1, hq.2⟩
    have hRmT : ∀ q ∈ _root_.Set.Icc (T - t) T, ∀ z : M,
        normSq0S (I := I) (S.base.metric q) z 4 (S.base.rm04 q z) ≤ K := by
      intro q hq z
      exact hRm q ⟨(sub_le_sub_left htsigma.le T).trans hq.1, hq.2⟩ z
    obtain ⟨y, _Z, _hZmin, _hZend, hval, hmin⟩ :=
      exists_redMin_vec (I := I) S hS K T hg t ht0 hregT hRmT x
    let eps : Real :=
      (f t - (Module.finrank Real E : Real) / 2) / (2 * t)
    have heps : 0 < eps := by
      exact div_pos (sub_pos.mpr hbad) (mul_pos (by norm_num) ht0)
    obtain ⟨U, J, Phi, d, hUopen, hyU, hJopen, htJ, hJsub,
        hsupport, htouch, hPhiSmooth, hderiv, hbar⟩ :=
      exists_redWeak_sup (I := I) S hS K T sigma t hg ht0 htsigma
        hreg hRm x y eps heps
    have hPhiMin : IsLocalMin (fun z : M ↦ Phi z t) y := by
      filter_upwards [hUopen.mem_nhds hyU] with z hz
      calc
        Phi y t = redLength S T x y t := htouch
        _ ≤ redLength S T x z t := hmin z
        _ ≤ Phi z t := hsupport z hz t htJ
    have hPhiMD :
        MDifferentiableAt I 𝓘(Real, Real) (fun z : M ↦ Phi z t) y :=
      ((hPhiSmooth y hyU).contMDiffAt
        (hUopen.mem_nhds hyU)).mdifferentiableAt (by simp)
    have hPhiMDnear : ∀ᶠ z in nhds y,
        MDifferentiableAt I 𝓘(Real, Real) (fun w : M ↦ Phi w t) z := by
      filter_upwards [hUopen.mem_nhds hyU] with z hz
      exact ((hPhiSmooth z hz).contMDiffAt
        (hUopen.mem_nhds hz)).mdifferentiableAt (by simp)
    have hgrad := gradientFun_mdiffOn (E := E) (I := I) (M := M)
      (S.base.metric (T - t)) hUopen hPhiSmooth hyU
    have hmc : IsMetricCompatible (I := I)
        (LeviCivita (I := I) (S.base.metric (T - t)))
        (S.base.metric (T - t)) := by
      simpa only [LeviCivita] using
        (leviCivitaConnectionOfMetric_isMetricCompatible
          (I := I) (S.base.metric (T - t)))
    have hlap : 0 ≤ laplacian (I := I)
        (LeviCivita (I := I) (S.base.metric (T - t)))
        (S.base.metric (T - t)) (fun z : M ↦ Phi z t) y :=
      laplacian_nonneg_at_spatial_min_of_metricCompatible
        (I := I) (LeviCivita (I := I) (S.base.metric (T - t)))
        (S.base.metric (T - t)) hmc hPhiMin hPhiMD hPhiMDnear hgrad
    have hbar' : d + laplacian (I := I)
          (LeviCivita (I := I) (S.base.metric (T - t)))
          (S.base.metric (T - t)) (fun z : M ↦ Phi z t) y ≤
        ((Module.finrank Real E : Real) / 2 - f t) / t + eps := by
      simpa only [f, hval] using hbar
    have hrhs : ((Module.finrank Real E : Real) / 2 - f t) / t + eps =
        -eps := by
      dsimp only [eps]
      field_simp [ht0.ne']
      ring
    have hdneg : d < 0 := by
      rw [hrhs] at hbar'
      linarith
    have hupperNhds : f ≤ᶠ[nhds t] Phi y := by
      filter_upwards [hJopen.mem_nhds htJ] with rho hrho
      have hrange := hJsub hrho
      have hregRho : _root_.Set.Icc (T - rho) T ⊆ D.regular := by
        intro q hq
        exact hreg ⟨(sub_le_sub_left hrange.2.le T).trans hq.1, hq.2⟩
      have hRmRho : ∀ q ∈ _root_.Set.Icc (T - rho) T, ∀ z : M,
          normSq0S (I := I) (S.base.metric q) z 4 (S.base.rm04 q z) ≤ K := by
        intro q hq z
        exact hRm q ⟨(sub_le_sub_left hrange.2.le T).trans hq.1, hq.2⟩ z
      obtain ⟨w, _W, _hWmin, _hWend, hvalRho, hminRho⟩ :=
        exists_redMin_vec (I := I) S hS K T hg rho hrange.1
          hregRho hRmRho x
      change redMinVal S T x rho ≤ Phi y rho
      calc
        redMinVal S T x rho = redLength S T x w rho := hvalRho
        _ ≤ redLength S T x y rho := hminRho y
        _ ≤ Phi y rho := hsupport y hyU rho hrho
    have hright : f ≤ᶠ[nhdsWithin t (_root_.Set.Ioi t)] Phi y :=
      hupperNhds.filter_mono nhdsWithin_le_nhds
    have htouchF : Phi y t = f t := by
      simpa only [f, hval] using htouch
    exact ⟨Phi y, d, htouchF, hright, hderiv, hdneg⟩
  have hfinal := hfence tau ⟨ha.2.le, le_rfl⟩
  have hregTau : _root_.Set.Icc (T - tau) T ⊆ D.regular := by
    intro q hq
    exact hreg ⟨(sub_le_sub_left htausigma.le T).trans hq.1, hq.2⟩
  have hRmTau : ∀ q ∈ _root_.Set.Icc (T - tau) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric q) z 4 (S.base.rm04 q z) ≤ K := by
    intro q hq z
    exact hRm q ⟨(sub_le_sub_left htausigma.le T).trans hq.1, hq.2⟩ z
  obtain ⟨y, hy⟩ :=
    exists_redMin_rm (I := I) S hS K T hg tau htau hregTau hRmTau x
  refine ⟨y, ?_⟩
  rw [← redMinVal_eq S T x y tau hy]
  simpa only [f] using hfinal

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.exists_redLen_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.exists_redLen_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.exists_redLen_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.exists_redLen_le

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
