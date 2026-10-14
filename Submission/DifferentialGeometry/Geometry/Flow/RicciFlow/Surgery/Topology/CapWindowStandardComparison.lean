import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.WindowPersistence
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalNeighborhoodContinuationLeaves

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Submission.Set _root_.Function _root_.Submission.Function _root_.Filter _root_.Submission.Filter _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness _root_.Submission.DifferentialGeometry.Geometry.Neck
open _root_.Submission.DifferentialGeometry.Tensor.Coordinates
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology _root_.Submission.DifferentialGeometry.Topology _root_.NNReal _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory

universe u

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.instFactEqNatFinrankRealThreeSpaceOfNat : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.instFactEqNatFinrankRealThreeSpaceOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.instFactEqNatFinrankRealThreeSpaceOfNat target :: scope.openDecls } }

theorem exists_standard_comparison_of_cap_window_trace
    (Θ : ℝ) (C : ℝ≥0) (hΘ : 0 < Θ) (hΘ1 : Θ < 1) :
    ∃ P Creset Cbirth : ℝ, 0 < P ∧ 0 < Creset ∧ 0 < Cbirth ∧
    ∀ (D ε η : ℝ) (hD : 0 < D), 0 < ε → 0 < η → ∀ N : ℕ,
    ∃ R : ℝ, D + 1 < R ∧ ∃ m₀ : ℕ, 4 ≤ m₀ ∧
    ∃ ζ₀ δ₀ : ℝ, 0 < ζ₀ ∧ ζ₀ ≤ 1 / 2 ∧ 0 < δ₀ ∧
    ∀ {P₀ : OrientedThreeStage.{u}} (H : RetainedCoreHistory P₀) (p₀ : CutoffParameters)
      (δbound ρbound : ℝ) {p : CutoffParameters}
      (records : ∀ i, GeometricCutoffRecord H.toHistory i p),
      H.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records →
      δbound ≤ δ₀ → R ≤ p₀.modelRadius → m₀ ≤ p₀.modelOrder → p₀.modelAccuracy ≤ ζ₀ →
    ∀ (qcan a₀ θcap : ℝ), 0 < qcan → θcap ≤ Θ →
      (∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x) →
      (∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x) →
    ∀ (k : Fin (H.eventCount + 1)) (s : ℝ) (Gk : (H.stage k).IncomingSlab (H.time k) s),
      Gk.flow.base.metric (H.time k) = H.initialMetric k →
      H.EventSlabsDerivative C qcan k →
    ∀ (t : ℝ) (hkt : H.time k < t), t < s → Gk.DerivativeBoundBefore C qcan t →
    ∀ (j : Fin H.eventCount) (hl : j.succ ≤ k) (y : (H.stage k).Carrier)
      (A : BackwardPointTrace H.toHistory j.succ k hl y)
      (b : (H.toHistory.event j).RetainedBoundaryIndex) (x : standardCapWindow p.modelRadius),
      A.point j.succ le_rfl hl = ((records j).static b).window x →
      t - H.time j.succ ≤ θcap * (((records j).static b).neck.scale)⁻¹ →
      ‖x.val‖ < D + 1 →
      qcan ≤ Cbirth * ((records j).static b).neck.scale →
      1 ≤ a₀ * ((records j).static b).neck.scale →
    ∃ (G : (H.stage k).IncomingSlab (H.time k) t) (L : G.TerminalLimitMetric),
      (∀ v, G.flow.base.metric v = Gk.flow.base.metric v) ∧
      G.terminalRegularRegion = _root_.Set.univ ∧
      L.metric = (Gk.flow.base.metric t).restrictOpen G.terminalRegularOpen ∧
    ∃ (x₀ : (H.toHistory.event j).incoming.terminalRegularOpen) (δ : ℝ) (kd : ℕ)
      (d : normalizedDatum (H.toHistory.event j).terminal.metric x₀ δ kd)
      (w : StandardCap.CanonicalStaticInsertionWitness d p.fixed.collarLength p.fixed.collar_pos
        p.modelRadius p.modelOrder p.modelAccuracy),
      (∀ x (v z : TangentSpace ThreeModel x), w.windowMetric.inner x v z =
        ((records j).static b).neck.scale * (H.initialMetric j.succ).inner
          (((records j).static b).window x)
          (mfderiv ThreeModel ThreeModel ((records j).static b).window x v)
          (mfderiv ThreeModel ThreeModel ((records j).static b).window x z)) ∧
    ∃ hDD : D ≤ p.modelRadius,
    ∃ z : standardCapWindow D, z.val = x.val ∧
    ∃ hy : y ∈ G.terminalRegularRegion,
    ∃ Ξ : standardCapWindow D →
        H.toHistory.backwardSurvivorIncomingDomain j.succ k hl G,
      _root_.Manifold.IsSmoothEmbedding ThreeModel ThreeModel ∞ Ξ ∧
      (∀ v, H.toHistory.backwardSurvivorMap j.succ k hl j.succ le_rfl hl (Ξ v).val =
        ((records j).static b).window
          (TopologicalSpace.Opens.inclusion
            (show standardCapWindow D ≤ standardCapWindow p.modelRadius from fun w hv =>
              (show ‖w‖ < D + 1 from hv).trans_le (add_le_add hDD (le_refl 1))) v)) ∧
      H.toHistory.backwardSurvivorIncomingMap j.succ k hl G (Ξ z) = ⟨y, hy⟩ ∧
      ∃ (hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ)
        (gflow : ℝ → SmoothRiemannianMetric ThreeModel
          (H.toHistory.backwardSurvivorIncomingDomain j.succ k hl G))
        (S : SolutionOn (I := ThreeModel) (M := standardCapWindow D)
          (RealTimeInterval.closed 0
            (((records j).static b).neck.scale * (t - H.time j.succ))
            (mul_nonneg ((records j).static b).neck.scale_pos.le
              (sub_nonneg.mpr ((H.time_strictMono.monotone hl).trans hkt.le))))),
        (∀ (i : Fin H.eventCount) (hf : j.succ ≤ i.castSucc) (hi : i.succ ≤ k),
          ∀ τ ∈ _root_.Set.Icc (H.time i.castSucc) (H.time i.succ),
            gflow τ = (H.toHistory.backwardSurvivorSlabMetric j.succ k hl i hf hi τ).restrictOpen
              (H.toHistory.backwardSurvivorIncomingDomain j.succ k hl G)) ∧
        (∀ τ ∈ _root_.Set.Icc (H.time k) t,
          gflow τ = H.toHistory.backwardSurvivorIncomingMetric j.succ k hl G L τ) ∧
        IsSolutionOn S ∧ S.base.metric 0 = (w.restrictWindow hD hDD).windowMetric ∧
        (∀ τ, S.base.metric τ =
          localPullMetric (scaleMetric ((records j).static b).neck.scale
            ((records j).static b).neck.scale_pos
            (gflow (H.time j.succ + τ / ((records j).static b).neck.scale))) Ξ hΞ) ∧
        (∀ (v : standardCapWindow D) (i l : Fin (Module.finrank ℝ ThreeSpace)),
          ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ) ∞
            (fun z : ℝ × standardCapWindow D => chartGramMatrix (S.base.metric z.1) v z.2 i l)
            (_root_.Set.Icc 0 (((records j).static b).neck.scale * (t - H.time j.succ)) ×ˢ
              (_root_.FiberBundle.trivializationAt ThreeSpace (TangentSpace ThreeModel) v).baseSet)) ∧
        (∀ τ ∈ _root_.Set.Icc 0 (((records j).static b).neck.scale * (t - H.time j.succ)),
          ∀ v : standardCapWindow D,
            normSq0S (S.base.metric τ) v 4 (S.base.rm04 τ v) ≤ P ^ 2 ∧
              |S.scalar τ v| ≤ Creset) ∧
        ∃ Q : StandardSolution,
          ENNReal.ofReal (((records j).static b).neck.scale * (t - H.time j.succ)) <
            Q.val.lifetime ∧
          ∀ τ ∈ _root_.Set.Icc 0 (((records j).static b).neck.scale * (t - H.time j.succ)),
            (∀ i ≤ N, ∀ v : standardCapWindow D,
              metricDerivNorm i (S.base.metric τ)
                ((Q.val.metric τ).restrictOpen (standardCapWindow D))
                (StandardCap.metric.restrictOpen (standardCapWindow D)) v < ε) ∧
            ∀ i ≤ 2, ∀ v : standardCapWindow D,
              metricDerivNorm i (S.base.metric τ)
                ((Q.val.metric τ).restrictOpen (standardCapWindow D))
                (StandardCap.metric.restrictOpen (standardCapWindow D)) v < η := by
  obtain ⟨P, Creset, Cbirth, hP, hCreset, hCbirth, hwindow⟩ :=
    ObservedHistory.exists_uniform_prepared_incoming_cap_window_flow_of_backward_trace.{u, 0, 0, u}
      Θ C hΘ hΘ1
  refine ⟨P, Creset, Cbirth, hP, hCreset, hCbirth, ?_⟩
  intro D ε η hD hε hη N
  obtain ⟨R, hDR, m₀, hm₀, ζ₀, δ₀, hζ₀, hζhalf, hδ₀, hwindow⟩ :=
    hwindow (I := ThreeModel) D ε η hD hε hη N
  refine ⟨R, hDR, m₀, hm₀, ζ₀, δ₀, hζ₀, hζhalf, hδ₀, ?_⟩
  intro P₀ H p₀ δbound ρbound p records hfam hδb hRp hmp hζp qcan a₀ θcap hqcan hθ hHI hlow
    k s Gk hGk hderiv t hkt hts hcur j hl y A b x hanchor hage hxD hbirth haq
  obtain ⟨-, hradius, horder, haccuracy, -, hcanonical, hdelta, -⟩ := hfam
  obtain ⟨x₀, δ, kd, d, w, -, hwmetric, -⟩ := hcanonical j b
  set Sc := (records j).static b with hSc
  set q := Sc.neck.scale with hqdef
  have hq : 0 < q := Sc.neck.scale_pos
  have hR : R ≤ p.modelRadius := hradius ▸ hRp
  have hDD : D ≤ p.modelRadius := by linarith
  let F := Gk.closedPrefix t hkt hts
  let G := F.restrictIncoming le_rfl F.lt le_rfl
  let L := F.endpointTerminalLimitMetric (H.stage k)
  have hreg : G.terminalRegularRegion = univ := F.terminalRegularRegion_eq_univ (H.stage k)
  have hmetric : ∀ x' (v z : TangentSpace ThreeModel x'), w.windowMetric.inner x' v z =
      q * (H.initialMetric j.succ).inner (Sc.window x')
        (mfderiv ThreeModel ThreeModel Sc.window x' v)
        (mfderiv ThreeModel ThreeModel Sc.window x' z) := by
    intro x' v z
    have ho : (H.toHistory.event j).outputMetric = H.initialMetric j.succ := H.event_output j
    rw [hwmetric x' v z, ho]
  have hdeltas : ∀ i : Fin H.eventCount, j.succ ≤ i.castSucc → i.succ ≤ k →
      ∀ c, (records i).delta c ≤ δ₀ :=
    fun i _ _ c => ((records i).delta_le c).trans ((hdelta i).trans hδb)
  have hslabs : ∀ i : Fin H.eventCount, j.succ ≤ i.castSucc → i.succ ≤ k →
      ∀ x' : (H.stage i.castSucc).Carrier, ∀ τ ∈ _root_.Set.Ioo (H.time i.castSucc) (H.time i.succ),
        qcan < (H.toHistory.event i).incoming.flow.scalar τ x' →
        |derivWithin (fun v => (H.toHistory.event i).incoming.flow.scalar v x') (_root_.Set.Iic τ) τ| ≤
          C * (H.toHistory.event i).incoming.flow.scalar τ x' ^ 2 :=
    fun i _ hi x' τ hτ hR => hderiv i (Fin.castSucc_lt_succ.trans_le hi) x' τ hτ hR
  have hfinal : ∀ x' : (H.stage k).Carrier, ∀ τ ∈ _root_.Set.Ioo (H.time k) t,
      qcan < G.flow.scalar τ x' →
      |derivWithin (fun v => G.flow.scalar v x') (_root_.Set.Iic τ) τ| ≤ C * G.flow.scalar τ x' ^ 2 :=
    fun x' τ hτ hR => hcur x' τ hτ hR
  have htime : q * (t - H.time j.succ) ≤ Θ := by
    have h1 : q * (t - H.time j.succ) ≤ q * (θcap * q⁻¹) :=
      mul_le_mul_of_nonneg_left hage hq.le
    have h2 : q * (θcap * q⁻¹) = θcap := by field_simp
    linarith
  have hxz : (⟨x.val, hxD⟩ : standardCapWindow D).val = x.val := rfl
  have hanchor' : A.point j.succ le_rfl hl =
      Sc.window (TopologicalSpace.Opens.inclusion
        (show standardCapWindow D ≤ standardCapWindow p.modelRadius from fun w hv =>
          (show ‖w‖ < D + 1 from hv).trans_le (add_le_add hDD (le_refl 1)))
        ⟨x.val, hxD⟩) := hanchor
  obtain ⟨hy, Ξ, hΞs, hΞbirth, hΞmark, hΞ, gflow, S, hS1, hS2, hS3, hS4, hS5, hS6, hS7, Q, hQ,
      hclose⟩ :=
    hwindow w hR (horder ▸ hmp) (haccuracy ▸ hζp) H.toHistory j.succ k hl t G L hGk
      Sc.window Sc.window_smooth q qcan a₀ hq hqcan hbirth haq hmetric p records hHI hlow
      hdeltas hslabs hfinal htime ⟨x.val, hxD⟩ y A hanchor'
  exact ⟨G, L, fun _ => rfl, hreg, rfl, x₀, δ, kd, d, w, hmetric, hDD, ⟨x.val, hxD⟩, hxz, hy,
    Ξ, hΞs, hΞbirth, hΞmark, hΞ, gflow, S, hS1, hS2, hS3, hS4, hS5, hS6, hS7, Q, hQ, hclose⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.exists_standard_comparison_of_cap_window_trace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.exists_standard_comparison_of_cap_window_trace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.exists_standard_comparison_of_cap_window_trace ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.exists_standard_comparison_of_cap_window_trace

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory
