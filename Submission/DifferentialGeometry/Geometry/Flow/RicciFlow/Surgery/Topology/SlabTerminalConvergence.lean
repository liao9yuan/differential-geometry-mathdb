import Submission.DifferentialGeometry.Geometry.Metric.Restriction
import Submission.DifferentialGeometry.Geometry.Metric.Distance.Ball
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalTimeExtension
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabSpatialJets
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabTensorContinuity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ClosedSlabEndpoints
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Arity
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Restriction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology _root_.BigOperators
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Tensor.Coordinates _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage

universe u
variable (P : OrientedThreeStage.{u})

private theorem metricCovDeriv_frame_eq (g gRef : P.Metric) (a : ℕ)
    (frame : Fin 3 → (x : P.Carrier) → TangentSpace ThreeModel x)
    {U : Set P.Carrier} (hframe : IsLocalFrameOn ThreeModel ThreeSpace 1 frame U)
    (hU : IsOpen U) {x : P.Carrier} (hx : x ∈ U) (n : Fin (a + 2) → Fin 3) :
    metricCovDeriv g gRef a x (fun k => frame (n k) x) =
      iterCovComp (I := ThreeModel) frame
        (fun y => christoffelSymbolInFrame (leviCivitaConnectionOfMetric gRef) frame hframe y)
        (frameComp0S (metricTensorField g) frame) a x (fun k => n (acEquiv a k)) := by
  rw [metricCovDeriv_eq_covDerivOfField, covDerivOfField_eq_iterCov,
    Tensor0SField.domDomCongr_apply, Tensor0SSpace.domDomCongr_apply]
  exact (iterCovComp_eq_iterCov gRef (metricTensorField g) frame hframe hU a hx _).symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.metricCovDeriv_frame_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.metricCovDeriv_frame_eq target :: scope.openDecls } }

theorem MetricSmoothUpTo.metricDerivNorm_continuousOn
    {g : ℝ → P.Metric} {J : Set ℝ} (hg : P.MetricSmoothUpTo g J)
    (gInf gRef : P.Metric) (a : ℕ) :
    ContinuousOn (fun q : ℝ × P.Carrier => metricDerivNorm a (g q.1) gInf gRef q.2)
      (J ×ˢ _root_.Set.univ) := by
  intro q hq
  let e := _root_.FiberBundle.trivializationAt ThreeSpace (TangentSpace ThreeModel) q.2
  let b := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  let frame := e.localFrame b
  obtain ⟨U, hU, hqU, hUb, V, hV, hqV, A, hA, hEq⟩ :=
    hg.exists_covariantComponent_extension P gRef q.2 hq.1 a
  have hRef : tensor0SFamilyContinuousOnSet 2 (V ∩ J)
      (fun _ x => metricTensorField gRef x) :=
    (metricTensorField gRef).contMDiff.continuous.comp continuous_snd
  have hInf : tensor0SFamilyContinuousOnSet (a + 2) (V ∩ J)
      (fun _ x => metricCovDeriv gInf gRef a x) :=
    (metricCovDeriv gInf gRef a).contMDiff.continuous.comp continuous_snd
  have hlocal : ContinuousOn
      (fun z : ℝ × P.Carrier => metricDerivNorm a (g z.1) gInf gRef z.2)
      ((V ∩ J) ×ˢ U) := by
    have hc : Continuous (fun z : ↥((V ∩ J) ×ˢ U) =>
        normSq0S gRef z.1.2 (a + 2) (metricDiffCovDerivAt a (g z.1.1) gInf gRef z.1.2)) := by
      refine P.normSq_continuous_in_frame (Q := ↥((V ∩ J) ×ˢ U)) q.2 b
        (fun z => z.1.2) (fun _ => gRef) (fun z => metricDiffCovDerivAt a (g z.1.1) gInf gRef z.1.2)
        (fun z => hUb z.2.2) ?_ ?_
      · intro i j
        have h := continuousOn_iff_continuous_domRestrict.mp
          ((P.tensorFamily_frame_continuousOn hRef q.2 b ![i, j]).mono
            (show (V ∩ J) ×ˢ U ⊆ (V ∩ J) ×ˢ e.baseSet from fun _ hz => ⟨hz.1, hUb hz.2⟩))
        simp only [metricTensorField_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at h
        exact h
      · intro n
        have hFirst := (hA (fun k => n (acEquiv a k))).continuousOn.mono
          (show (V ∩ J) ×ˢ U ⊆ V ×ˢ U from fun _ hz => ⟨hz.1.1, hz.2⟩)
        have hSecond := (P.tensorFamily_frame_continuousOn hInf q.2 b n).mono
          (show (V ∩ J) ×ˢ U ⊆ (V ∩ J) ×ˢ e.baseSet from fun _ hz => ⟨hz.1, hUb hz.2⟩)
        have hComp : ContinuousOn
            (fun z : ℝ × P.Carrier => metricDiffCovDerivAt a (g z.1) gInf gRef z.2
              (fun k => frame (n k) z.2)) ((V ∩ J) ×ˢ U) := by
          apply (hFirst.sub hSecond).congr
          intro z hz
          change metricCovDeriv (g z.1) gRef a z.2 (fun k => frame (n k) z.2) -
            metricCovDeriv gInf gRef a z.2 (fun k => frame (n k) z.2) = _
          rw [metricCovDeriv_frame_eq P (g z.1) gRef a frame
            (e.isLocalFrameOn_localFrame_baseSet ThreeModel 1 b) e.open_baseSet (hUb hz.2)]
          exact congrArg (fun c => c - metricCovDeriv gInf gRef a z.2
            (fun k => frame (n k) z.2)) (hEq z.1 hz.1 z.2 hz.2 _).symm
        exact continuousOn_iff_continuous_domRestrict.mp hComp
    exact continuousOn_iff_continuous_domRestrict.mpr hc.sqrt
  have hn : (V ∩ J) ×ˢ U ∈ 𝓝[J ×ˢ (_root_.Set.univ : Set P.Carrier)] q := by
    rw [mem_nhdsWithin]
    refine ⟨V ×ˢ U, hV.prod hU, ⟨hqV, hqU⟩, ?_⟩
    intro z hz
    exact ⟨⟨hz.1.1, hz.2.1⟩, hz.1.2⟩
  exact (hlocal q ⟨⟨hqV, hq.1⟩, hqU⟩).mono_of_mem_nhdsWithin hn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.MetricSmoothUpTo.metricDerivNorm_continuousOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.MetricSmoothUpTo.metricDerivNorm_continuousOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.MetricSmoothUpTo.metricDerivNorm_continuousOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.MetricSmoothUpTo.metricDerivNorm_continuousOn

theorem MetricSmoothUpTo.terminal_convergence {g : ℝ → P.Metric} {u v : ℝ}
    (hg : P.MetricSmoothUpTo g (_root_.Set.Icc u v)) (huv : u < v)
    {K : Set P.Carrier} (hK : IsCompact K) (a : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ d ∈ _root_.Set.Ico u v, ∀ t ∈ _root_.Set.Ioo d v, ∀ x ∈ K,
      metricDerivNorm a (g t) (g v) (g v) x < ε := by
  have he (x : P.Carrier) :
      {q : ℝ × P.Carrier | metricDerivNorm a (g q.1) (g v) (g v) q.2 < ε} ∈
        𝓝[_root_.Set.Icc u v] v ×ˢ 𝓝 x := by
    have h := (hg.metricDerivNorm_continuousOn P (g v) (g v) a
      (v, x) ⟨⟨huv.le, le_rfl⟩, _root_.Set.mem_univ x⟩).eventually_lt_const
        (by simpa only [metricDerivNorm_self] using hε)
    simp only [nhdsWithin_prod_eq, nhdsWithin_univ] at h
    exact h
  have hprod : ∀ᶠ q in 𝓝[_root_.Set.Icc u v] v ×ˢ 𝓝ˢ K,
      metricDerivNorm a (g q.1) (g v) (g v) q.2 < ε :=
    hK.mem_prod_nhdsSet_of_forall (fun x _ => he x)
  have htime : ∀ᶠ t in 𝓝[_root_.Set.Icc u v] v, ∀ x ∈ K,
      metricDerivNorm a (g t) (g v) (g v) x < ε :=
    hprod.curry.mono (fun _ ht => ht.self_of_nhdsSet)
  have hleft : ∀ᶠ t in 𝓝[<] v, ∀ x ∈ K,
      metricDerivNorm a (g t) (g v) (g v) x < ε := by
    have h := htime.filter_mono (nhdsWithin_mono v _root_.Set.Ico_subset_Icc_self)
    simpa only [nhdsWithin_Ico_eq_nhdsLT huv] using h
  exact (mem_nhdsLT_iff_exists_mem_Ico_Ioo_subset huv).mp hleft

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.MetricSmoothUpTo.terminal_convergence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.MetricSmoothUpTo.terminal_convergence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.MetricSmoothUpTo.terminal_convergence ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.MetricSmoothUpTo.terminal_convergence

theorem ClosedSlab.terminalRegularRegion_eq_univ {u v : ℝ} (G : P.ClosedSlab u v) :
    (G.restrictIncoming le_rfl G.lt le_rfl).terminalRegularRegion = univ := by
  obtain ⟨K, hK, hbound⟩ := G.curvature_bound P
  apply _root_.Set.eq_univ_of_forall
  intro x
  refine ⟨univ, isOpen_univ, _root_.Set.mem_univ x, u, ⟨le_rfl, G.lt⟩, K, hK, ?_⟩
  intro y _ t ht
  exact hbound t ⟨ht.1, ht.2.le⟩ y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.terminalRegularRegion_eq_univ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.terminalRegularRegion_eq_univ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.terminalRegularRegion_eq_univ ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.terminalRegularRegion_eq_univ

theorem ClosedSlab.endpoint_terminalMetricConverges {u v : ℝ} (G : P.ClosedSlab u v) :
    (G.restrictIncoming le_rfl G.lt le_rfl).TerminalMetricConverges
      ((G.flow.base.metric v).restrictOpen
        (G.restrictIncoming le_rfl G.lt le_rfl).terminalRegularOpen) := by
  let : SecondCountableTopology P.Carrier :=
    ChartedSpace.secondCountable_of_sigmaCompact ThreeSpace P.Carrier
  let F := G.restrictIncoming le_rfl G.lt le_rfl
  let : LocallyCompactSpace F.terminalRegularOpen :=
    ChartedSpace.locallyCompactSpace ThreeSpace F.terminalRegularOpen
  intro K hK a ε hε
  have hc : IsCompact (Subtype.val '' K : Set P.Carrier) := hK.image continuous_subtype_val
  obtain ⟨d, hd, hbound⟩ := G.smoothUpTo.terminal_convergence P G.lt hc a hε
  refine ⟨d, hd, fun t ht x hx => ?_⟩
  rw [metricDerivNorm_restrictOpen]
  exact hbound t ht x.1 ⟨x, hx, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.endpoint_terminalMetricConverges then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.endpoint_terminalMetricConverges"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.endpoint_terminalMetricConverges ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.endpoint_terminalMetricConverges

def ClosedSlab.endpointTerminalLimitMetric {u v : ℝ} (G : P.ClosedSlab u v) :
    (G.restrictIncoming le_rfl G.lt le_rfl).TerminalLimitMetric where
  metric := (G.flow.base.metric v).restrictOpen
    (G.restrictIncoming le_rfl G.lt le_rfl).terminalRegularOpen
  converges := G.endpoint_terminalMetricConverges P

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.endpointTerminalLimitMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.endpointTerminalLimitMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.endpointTerminalLimitMetric ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.endpointTerminalLimitMetric

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage

universe u
variable {P : OrientedThreeStage.{u}}

theorem ClosedSlab.endpointTerminalLimitMetric_extendedMetric_of_le
    {a b : ℝ} (S : P.ClosedSlab a b) {v : ℝ} (hv : v ≤ b) :
    (S.endpointTerminalLimitMetric P).extendedMetric v =
      (S.flow.base.metric v).restrictOpen
        (S.restrictIncoming le_rfl S.lt le_rfl).terminalRegularOpen := by
  rcases lt_or_eq_of_le hv with hlt | rfl
  · rw [IncomingSlab.TerminalLimitMetric.extendedMetric_before _ hlt]
    rfl
  · rw [IncomingSlab.TerminalLimitMetric.extendedMetric_terminal]
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.endpointTerminalLimitMetric_extendedMetric_of_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.endpointTerminalLimitMetric_extendedMetric_of_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.endpointTerminalLimitMetric_extendedMetric_of_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.endpointTerminalLimitMetric_extendedMetric_of_le


end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage

end

section

set_option autoImplicit false
noncomputable section

open _root_.Set

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage

universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ}

theorem ClosedSlab.riemannianEDistOf_endpointTerminalLimitMetric
    (A : P.ClosedSlab a s)
    (x y : (A.restrictIncoming le_rfl A.lt le_rfl).terminalRegularOpen) :
    riemannianEDistOf (A.endpointTerminalLimitMetric P).metric x y =
      riemannianEDistOf (A.flow.base.metric s) x.val y.val := by
  exact riemannianEDistOf_restrictOpen_of_isClosed (A.flow.base.metric s)
    (A.restrictIncoming le_rfl A.lt le_rfl).terminalRegularOpen
    (by
      change IsClosed (A.restrictIncoming le_rfl A.lt le_rfl).terminalRegularRegion
      rw [A.terminalRegularRegion_eq_univ P]
      exact isClosed_univ) x y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.riemannianEDistOf_endpointTerminalLimitMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.riemannianEDistOf_endpointTerminalLimitMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.riemannianEDistOf_endpointTerminalLimitMetric ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.riemannianEDistOf_endpointTerminalLimitMetric

theorem ClosedSlab.mem_scaled_endpoint_closedBall_iff
    (A : P.ClosedSlab a s) (Q : ℝ) (hQ : 0 < Q)
    (x y : (A.restrictIncoming le_rfl A.lt le_rfl).terminalRegularOpen) (R : ℝ) :
    y ∈ riemannianClosedBallOf (scaleMetric Q hQ (A.endpointTerminalLimitMetric P).metric) x R ↔
      y.val ∈ riemannianClosedBallOf (A.flow.base.metric s) x.val (R / Real.sqrt Q) := by
  have hr : Real.sqrt Q * (R / Real.sqrt Q) = R := by
    rw [mul_div_cancel₀ R (Real.sqrt_pos.mpr hQ).ne']
  have hball := riemannianClosedBallOf_scaleMetric Q hQ
    (A.endpointTerminalLimitMetric P).metric x (R / Real.sqrt Q)
  rw [hr] at hball
  rw [hball]
  change riemannianEDistOf (A.endpointTerminalLimitMetric P).metric x y ≤ _ ↔ _
  rw [A.riemannianEDistOf_endpointTerminalLimitMetric x y]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.mem_scaled_endpoint_closedBall_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.mem_scaled_endpoint_closedBall_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.mem_scaled_endpoint_closedBall_iff ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.mem_scaled_endpoint_closedBall_iff

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage

end
end
