import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalNeighborhoodContinuationLeaves
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BackwardTraceScalarControl
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabGradientScalarControl
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryParabolicBall
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalCapScalar
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CrossingScalar
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabPointPicking

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Submission.Set _root_.TopologicalSpace _root_.Submission.TopologicalSpace
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace MetricCutCapEvent

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s)

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.instSigmaCompactSpaceSubtypeCarrierMemOpensTerminalRegularOpenIncoming : SigmaCompactSpace E.incoming.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
      E.incoming.terminalRegularOpen.isOpen)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.instSigmaCompactSpaceSubtypeCarrierMemOpensTerminalRegularOpenIncoming
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.instSigmaCompactSpaceSubtypeCarrierMemOpensTerminalRegularOpenIncoming target :: scope.openDecls } }

theorem RegularCrossing.rmNormSq_eq
    {p : E.incoming.terminalRegularOpen} {q : Q.Carrier}
    (h : E.RegularCrossing p.val q) :
    normSq0S E.terminal.metric p 4 (metricRm04At E.terminal.metric p) =
      normSq0S E.outputMetric q 4 (metricRm04At E.outputMetric q) := by
  obtain ⟨F, _, hp, heq, _, _, hmetric⟩ := h.exists_survivor_partialDiffeomorph E
  let U : _root_.TopologicalSpace.Opens E.incoming.terminalRegularOpen := ⟨F.source, F.open_source⟩
  let V : _root_.TopologicalSpace.Opens Q.Carrier :=
    ⟨(F : E.incoming.terminalRegularOpen → Q.Carrier) ''
      (U : Set E.incoming.terminalRegularOpen),
      DifferentialGeometry.image_opens_isOpen F Subset.rfl⟩
  let e : U ≃ₘ⟮ThreeModel, ThreeModel⟯ V :=
    DifferentialGeometry.PartialDiffeomorph.toOpensDiffeo F Subset.rfl
  have hmet : Diffeomorph.pullbackMetricCross (E.outputMetric.restrictOpen V) e =
      E.terminal.metric.restrictOpen U := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    rw [Diffeomorph.pullbackMetricCross_inner, SmoothRiemannianMetric.restrictOpen_inner,
      SmoothRiemannianMetric.restrictOpen_inner]
    have hd := DifferentialGeometry.PartialDiffeomorph.mfderiv_toOpensDiffeo
      F (show (U : Set E.incoming.terminalRegularOpen) ⊆ F.source from Subset.rfl) x
    change E.outputMetric.inner (F x.val) (mfderiv ThreeModel ThreeModel e x v)
      (mfderiv ThreeModel ThreeModel e x w) = _
    rw [hd v, hd w]
    exact hmetric x.val x.property v w
  have : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel U.isOpen)
  have hn :=
    CheegerGromovCompactness.riemannNormSq_cross (E.outputMetric.restrictOpen V) e ⟨p, hp⟩
  rw [hmet, Perelman.CanonicalNeighborhood.rmNormSq_restrictOpen,
    Perelman.CanonicalNeighborhood.rmNormSq_restrictOpen] at hn
  subst heq
  exact hn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.RegularCrossing.rmNormSq_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.RegularCrossing.rmNormSq_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.RegularCrossing.rmNormSq_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.RegularCrossing.rmNormSq_eq

end MetricCutCapEvent

namespace RetainedCoreHistory

variable {P₀ : OrientedThreeStage.{u}} (H : RetainedCoreHistory P₀)

private theorem time_lt_succ_of_activeStage_eq (t : _root_.Set.Icc (0 : ℝ) H.toHistory.horizon)
    (i : Fin H.eventCount) (hi : H.toHistory.activeStage t = i.castSucc) :
    (t : ℝ) < H.time i.succ := by
  have hval : (H.toHistory.activeStage t).val < H.toHistory.eventCount := by
    rw [hi]
    exact i.isLt
  have h := H.toHistory.activeStage_before_next t hval
  have he : (⟨(H.toHistory.activeStage t).val + 1, Nat.succ_lt_succ hval⟩ :
      Fin (H.toHistory.eventCount + 1)) = i.succ := by
    ext
    simp [hi]
  rw [he] at h
  exact h

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.time_lt_succ_of_activeStage_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.time_lt_succ_of_activeStage_eq target :: scope.openDecls } }

private theorem normSq_le_of_sqrt_le {N C R M : ℝ} (hN : 0 ≤ N) (hC : 0 ≤ C)
    (hsqrt : Real.sqrt N ≤ C * _root_.Max.max R 1) (hR : R ≤ 2 * M) (hM : 1 ≤ M) :
    N ≤ (2 * C * M) ^ 2 := by
  have hmax : _root_.Max.max R 1 ≤ 2 * M := max_le hR (by linarith)
  have h1 : Real.sqrt N ≤ 2 * C * M := hsqrt.trans (by nlinarith)
  calc N = Real.sqrt N ^ 2 := (Real.sq_sqrt hN).symm
    _ ≤ (2 * C * M) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.normSq_le_of_sqrt_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.normSq_le_of_sqrt_le target :: scope.openDecls } }

theorem sqrt_rmNormSq_stageMetric_le_of_pinched {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi) (hpinch : H.EventSlabsPinched phi)
    (v : _root_.Set.Icc (0 : ℝ) H.toHistory.horizon)
    (hv : H.toHistory.activeStage v = Fin.last H.eventCount →
      ∃ h : H.time (Fin.last H.eventCount) < H.horizon,
        Perelman.PhiAlmostNonnegative (H.finalSlab h).flow
          (_root_.Set.Icc (H.time (Fin.last H.eventCount)) H.horizon) phi)
    (z : (H.stage (H.toHistory.activeStage v)).Carrier) :
    Real.sqrt (normSq0S (H.toHistory.stageMetric (H.toHistory.activeStage v) v) z 4
        (metricRm04At (H.toHistory.stageMetric (H.toHistory.activeStage v) v) z)) ≤
      4 * Real.sqrt 3 * (1 + phi 1 + phi 0) *
        max (metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage v) v) z) 1 := by
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp
  have hlow := H.toHistory.activeStage_time_le v
  have hnext := H.time_lt_succ_of_activeStage_eq v
  have hup := v.2.2
  generalize H.toHistory.activeStage v = k at hlow hnext hv z ⊢
  cases k using Fin.lastCases with
  | last =>
    obtain ⟨h, hfp⟩ := hv rfl
    have := IsManifold.of_le (I := ThreeModel) (M := (H.stage (Fin.last H.eventCount)).Carrier)
      (n := ∞) (m := 1) (by decide)
    have hb :=
      Perelman.CanonicalNeighborhood.sqrt_rmNormSq_le_mul_max_scalar_one_of_phiAlmostNonnegative
      hphi hfp hdim ⟨hlow, hup⟩ z
    rw [ObservedHistory.stageMetric_last_of_lt (h := h)]
    exact hb
  | cast i =>
    have := IsManifold.of_le (I := ThreeModel) (M := (H.stage i.castSucc).Carrier)
      (n := ∞) (m := 1) (by decide)
    have hb :=
      Perelman.CanonicalNeighborhood.sqrt_rmNormSq_le_mul_max_scalar_one_of_phiAlmostNonnegative
      hphi (hpinch i) hdim ⟨hlow, hnext i rfl⟩ z
    rw [ObservedHistory.stageMetric_castSucc_apply]
    exact hb

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.sqrt_rmNormSq_stageMetric_le_of_pinched then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.sqrt_rmNormSq_stageMetric_le_of_pinched"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.sqrt_rmNormSq_stageMetric_le_of_pinched ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.sqrt_rmNormSq_stageMetric_le_of_pinched

private theorem trace_normSq_eq_of_stage_eq {K : ObservedHistory.{u}}
    {first last : Fin (K.eventCount + 1)} {hle : first ≤ last} {x : (K.stage last).Carrier}
    (A : BackwardPointTrace K first last hle x) {j k : Fin (K.eventCount + 1)} (hjk : j = k)
    (hj : first ≤ j) (hjl : j ≤ last) (hk : first ≤ k) (hkl : k ≤ last) (v : ℝ) :
    normSq0S (K.stageMetric j v) (A.point j hj hjl) 4
      (metricRm04At (K.stageMetric j v) (A.point j hj hjl)) =
    normSq0S (K.stageMetric k v) (A.point k hk hkl) 4
      (metricRm04At (K.stageMetric k v) (A.point k hk hkl)) := by
  subst hjk
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.trace_normSq_eq_of_stage_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.trace_normSq_eq_of_stage_eq target :: scope.openDecls } }

theorem isRmControlled_of_backwardPointTrace_of_derivative_bounds
    {Ctime : ℝ≥0} {qcan M r : ℝ} {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi) (hpinch : H.EventSlabsPinched phi)
    {u t : _root_.Set.Icc (0 : ℝ) H.toHistory.horizon} (hut : u ≤ t)
    (hlast : H.toHistory.activeStage t = Fin.last H.eventCount →
      ∃ h : H.time (Fin.last H.eventCount) < H.horizon,
        Perelman.PhiAlmostNonnegative (H.finalSlab h).flow
          (_root_.Set.Icc (H.time (Fin.last H.eventCount)) H.horizon) phi)
    {p : (H.toHistory.stage (H.toHistory.activeStage t)).Carrier}
    (A : BackwardPointTrace H.toHistory (H.toHistory.activeStage u)
      (H.toHistory.activeStage t) (H.toHistory.activeStage_mono hut) p)
    (hslabs : H.EventSlabsDerivative Ctime qcan (H.toHistory.activeStage t))
    (hcurrent : ∀ j : Fin H.eventCount, j.castSucc = H.toHistory.activeStage t →
      (H.toHistory.event j).incoming.DerivativeBoundBefore Ctime qcan t)
    (hfinal : ∀ h : H.time (Fin.last H.eventCount) < H.horizon,
      H.toHistory.activeStage t = Fin.last H.eventCount →
      ((H.finalSlab h).restrictIncoming le_rfl h le_rfl).DerivativeBoundBefore Ctime qcan t)
    (hM : 1 ≤ M) (hqcan : qcan ≤ M)
    (hscalar : metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) p ≤ M)
    (htime : Ctime * M * ((t : ℝ) - u) ≤ 1 / 2)
    (hrM : r ^ 4 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) ^ 2 ≤ 1) :
    A.isRmControlled (hat := hut) r := by
  have hC : 0 ≤ 4 * Real.sqrt 3 * (1 + phi 1 + phi 0) := by
    have := hphi.pos 0
    have := hphi.pos 1
    positivity
  have hscal := H.scalar_le_two_mul_of_backwardPointTrace_of_derivative_bounds hut A hslabs
    hcurrent hfinal (by linarith) hqcan hscalar htime
  have hall : ∀ (v : _root_.Set.Icc (0 : ℝ) H.toHistory.horizon) (huv : u ≤ v) (hvt : v ≤ t),
      r ^ 4 * normSq0S (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
        (A.point (H.toHistory.activeStage v) (H.toHistory.activeStage_mono huv)
          (H.toHistory.activeStage_mono hvt)) 4
        (metricRm04At (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
          (A.point (H.toHistory.activeStage v) (H.toHistory.activeStage_mono huv)
            (H.toHistory.activeStage_mono hvt))) ≤ 1 := by
    intro v huv hvt
    have hv : H.toHistory.activeStage v = Fin.last H.eventCount →
        ∃ h : H.time (Fin.last H.eventCount) < H.horizon,
          Perelman.PhiAlmostNonnegative (H.finalSlab h).flow
            (_root_.Set.Icc (H.time (Fin.last H.eventCount)) H.horizon) phi := fun h =>
      hlast (le_antisymm (Fin.le_last _) (h ▸ H.toHistory.activeStage_mono hvt))
    have hs := H.sqrt_rmNormSq_stageMetric_le_of_pinched hphi hpinch v hv
      (A.point (H.toHistory.activeStage v) (H.toHistory.activeStage_mono huv)
        (H.toHistory.activeStage_mono hvt))
    have hN := normSq_le_of_sqrt_le (normSq0S_nonneg _ _ _ _) hC hs (hscal v huv hvt) hM
    calc _ ≤ r ^ 4 * (2 * (4 * Real.sqrt 3 * (1 + phi 1 + phi 0)) * M) ^ 2 :=
          mul_le_mul_of_nonneg_left hN (by positivity)
      _ = r ^ 4 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) ^ 2 := by ring
      _ ≤ 1 := hrM
  refine ⟨hall, ?_⟩
  intro i hf hl x
  have hIoc := (H.toHistory.crossed_event_iff_mem_Ioc u t i).mp ⟨hf, hl⟩
  let v : _root_.Set.Icc (0 : ℝ) H.toHistory.horizon :=
    ⟨H.time i.succ, H.toHistory.time_nonneg _, H.toHistory.time_le_horizon_at _⟩
  have hav : H.toHistory.activeStage v = i.succ := H.toHistory.activeStage_at_time i.succ
  have huv : u ≤ v := hIoc.1.le
  have hvt : v ≤ t := hIoc.2
  have hb := hall v huv hvt
  rw [trace_normSq_eq_of_stage_eq A hav (H.toHistory.activeStage_mono huv)
    (H.toHistory.activeStage_mono hvt) (hf.trans (Fin.castSucc_lt_succ (i := i)).le) hl] at hb
  have hx := MetricCutCapEvent.RegularCrossing.rmNormSq_eq (H.toHistory.event i) (p := x)
    (A.crossing i hf hl)
  rw [hx, H.toHistory.event_output i, ← H.toHistory.stageMetric_initial]
  exact hb

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.isRmControlled_of_backwardPointTrace_of_derivative_bounds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.isRmControlled_of_backwardPointTrace_of_derivative_bounds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.isRmControlled_of_backwardPointTrace_of_derivative_bounds ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.isRmControlled_of_backwardPointTrace_of_derivative_bounds

theorem capWindowPoint_of_isEmpty_backwardPointTrace {p : CutoffParameters}
    (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p)
    (hcan : ∀ i b, ((records i).static b).hasCanonicalWindow)
    (hscale : ∀ i b z, ((records i).static b).neck.scale / 2 ≤
      metricScalarAt ((records i).static b).witness.metric (((records i).static b).witness.cap z))
    {Ctime : ℝ≥0} {qcan M Dcap θcap : ℝ} {u t : _root_.Set.Icc (0 : ℝ) H.toHistory.horizon}
    (hut : u ≤ t)
    (y : (H.toHistory.stage (H.toHistory.activeStage t)).Carrier)
    (hy : IsEmpty (BackwardPointTrace H.toHistory (H.toHistory.activeStage u)
      (H.toHistory.activeStage t) (H.toHistory.activeStage_mono hut) y))
    (hslabs : H.EventSlabsDerivative Ctime qcan (H.toHistory.activeStage t))
    (hcurrent : ∀ j : Fin H.eventCount, j.castSucc = H.toHistory.activeStage t →
      (H.toHistory.event j).incoming.DerivativeBoundBefore Ctime qcan t)
    (hfinal : ∀ h : H.time (Fin.last H.eventCount) < H.horizon,
      H.toHistory.activeStage t = Fin.last H.eventCount →
      ((H.finalSlab h).restrictIncoming le_rfl h le_rfl).DerivativeBoundBefore Ctime qcan t)
    (hM : 0 < M) (hqcan : qcan ≤ M)
    (hscalar : metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) y ≤ M)
    (htime : Ctime * M * ((t : ℝ) - u) ≤ 1 / 2)
    (hD : StandardCap.transitionEnd < Dcap + 1) (hθ : 4 * M * ((t : ℝ) - u) ≤ θcap) :
    H.CapWindowPoint records (H.toHistory.activeStage t) y t Dcap θcap := by
  obtain ⟨j, hf, hl, A, b, z, x, -, hz, hxn, hx⟩ :=
    H.toHistory.exists_cap_capture records hcan (H.toHistory.activeStage_mono hut) y hy
  refine ⟨j, hl, A, b, x, hx, hxn.trans_lt hD, ?_⟩
  have hju : (u : ℝ) < H.time j.succ := by
    by_contra hle
    have h := H.toHistory.le_activeStage u j.succ (not_lt.mp hle)
    exact absurd (h.trans hf) (not_le_of_gt (Fin.castSucc_lt_succ (i := j)))
  have hjt : H.time j.succ ≤ t :=
    (H.time_strictMono.monotone hl).trans (H.toHistory.activeStage_time_le t)
  have hrec := A.inv_max_stageMetric_scalar_sub_le_of_derivativeBoundBefore hM hqcan
    (H.toHistory.activeStage_time_le t) (fun i hi => H.time_lt_succ_of_activeStage_eq t i hi)
    t.2.2 hslabs hcurrent hfinal j.succ le_rfl hl le_rfl
    (fun i hi => hi ▸ H.time_strictMono (Fin.castSucc_lt_succ (i := i))) hjt
  rw [max_eq_left hscalar, H.toHistory.stageMetric_initial, ← H.toHistory.event_output j, hz,
    ← ((records j).static b).scalar_eq] at hrec
  set S := ((records j).static b).neck.scale with hSdef
  have hSpos : 0 < S := ((records j).static b).neck.scale_pos
  have hlow := hscale j b z
  set R := metricScalarAt ((records j).static b).witness.metric
    (((records j).static b).witness.cap z) with hRdef
  have hgap : M⁻¹ - (_root_.Max.max M R)⁻¹ ≤ Ctime * ((t : ℝ) - H.time j.succ) := by
    have := (abs_le.mp hrec).1
    linarith
  have hC : 0 ≤ (Ctime : ℝ) := Ctime.coe_nonneg
  have htu : (t : ℝ) - H.time j.succ ≤ (t : ℝ) - u := by linarith
  have hnn : 0 ≤ (t : ℝ) - H.time j.succ := by linarith
  have hCt : (Ctime : ℝ) * ((t : ℝ) - H.time j.succ) ≤ (2 * M)⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ (by positivity)]
    nlinarith
  have hmax : _root_.Max.max M R ≤ 2 * M := by
    have hinv : (2 * M)⁻¹ ≤ (_root_.Max.max M R)⁻¹ := by
      have htwo : M⁻¹ = 2 * (2 * M)⁻¹ := by field_simp
      linarith
    exact (inv_le_inv₀ (by positivity) (hM.trans_le (le_max_left M R))).mp hinv
  have hS : S ≤ 4 * M := by linarith [le_max_right M R]
  rw [← div_eq_mul_inv, le_div_iff₀ hSpos]
  nlinarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.capWindowPoint_of_isEmpty_backwardPointTrace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.capWindowPoint_of_isEmpty_backwardPointTrace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.capWindowPoint_of_isEmpty_backwardPointTrace ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.capWindowPoint_of_isEmpty_backwardPointTrace

theorem nonempty_backwardPointTrace_of_not_capWindowPoint {p : CutoffParameters}
    (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p)
    (hcan : ∀ i b, ((records i).static b).hasCanonicalWindow)
    (hscale : ∀ i b z, ((records i).static b).neck.scale / 2 ≤
      metricScalarAt ((records i).static b).witness.metric (((records i).static b).witness.cap z))
    {Ctime : ℝ≥0} {qcan M Dcap θcap : ℝ} {u t : _root_.Set.Icc (0 : ℝ) H.toHistory.horizon}
    (hut : u ≤ t)
    (y : (H.toHistory.stage (H.toHistory.activeStage t)).Carrier)
    (hnot : ¬ H.CapWindowPoint records (H.toHistory.activeStage t) y t Dcap θcap)
    (hslabs : H.EventSlabsDerivative Ctime qcan (H.toHistory.activeStage t))
    (hcurrent : ∀ j : Fin H.eventCount, j.castSucc = H.toHistory.activeStage t →
      (H.toHistory.event j).incoming.DerivativeBoundBefore Ctime qcan t)
    (hfinal : ∀ h : H.time (Fin.last H.eventCount) < H.horizon,
      H.toHistory.activeStage t = Fin.last H.eventCount →
      ((H.finalSlab h).restrictIncoming le_rfl h le_rfl).DerivativeBoundBefore Ctime qcan t)
    (hM : 0 < M) (hqcan : qcan ≤ M)
    (hscalar : metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) y ≤ M)
    (htime : Ctime * M * ((t : ℝ) - u) ≤ 1 / 2)
    (hD : StandardCap.transitionEnd < Dcap + 1) (hθ : 4 * M * ((t : ℝ) - u) ≤ θcap) :
    Nonempty (BackwardPointTrace H.toHistory (H.toHistory.activeStage u)
      (H.toHistory.activeStage t) (H.toHistory.activeStage_mono hut) y) := by
  by_contra h
  exact hnot (H.capWindowPoint_of_isEmpty_backwardPointTrace records hcan hscale hut y
    (not_nonempty_iff.mp h) hslabs hcurrent hfinal hM hqcan hscalar htime hD hθ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.nonempty_backwardPointTrace_of_not_capWindowPoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.nonempty_backwardPointTrace_of_not_capWindowPoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.nonempty_backwardPointTrace_of_not_capWindowPoint ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.nonempty_backwardPointTrace_of_not_capWindowPoint

theorem isParabolicallyRmControlledBall_of_forall_nonempty_backwardPointTrace
    {Ctime : ℝ≥0} {qcan M r : ℝ} {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi) (hpinch : H.EventSlabsPinched phi)
    {u t : _root_.Set.Icc (0 : ℝ) H.toHistory.horizon} (hut : u ≤ t) (hr : 0 < r)
    (hu : (u : ℝ) = t - r ^ 2)
    (hlast : H.toHistory.activeStage t = Fin.last H.eventCount →
      ∃ h : H.time (Fin.last H.eventCount) < H.horizon,
        Perelman.PhiAlmostNonnegative (H.finalSlab h).flow
          (_root_.Set.Icc (H.time (Fin.last H.eventCount)) H.horizon) phi)
    (y : (H.toHistory.stage (H.toHistory.activeStage t)).Carrier)
    (hslabs : H.EventSlabsDerivative Ctime qcan (H.toHistory.activeStage t))
    (hcurrent : ∀ j : Fin H.eventCount, j.castSucc = H.toHistory.activeStage t →
      (H.toHistory.event j).incoming.DerivativeBoundBefore Ctime qcan t)
    (hfinal : ∀ h : H.time (Fin.last H.eventCount) < H.horizon,
      H.toHistory.activeStage t = Fin.last H.eventCount →
      ((H.finalSlab h).restrictIncoming le_rfl h le_rfl).DerivativeBoundBefore Ctime qcan t)
    (hM : 1 ≤ M) (hqcan : qcan ≤ M)
    (hspace : ∀ x ∈ riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t)
        y r,
      metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) x ≤ M)
    (htime : Ctime * M * r ^ 2 ≤ 1 / 2)
    (hrM : r ^ 4 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) ^ 2 ≤ 1)
    (htrace : ∀ x ∈ riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t)
        y r,
      Nonempty (BackwardPointTrace H.toHistory (H.toHistory.activeStage u)
        (H.toHistory.activeStage t) (H.toHistory.activeStage_mono hut) x)) :
    H.toHistory.isParabolicallyRmControlledBall t y r := by
  refine ⟨hr, u, hut, hu, fun x hx => ?_⟩
  obtain ⟨A⟩ := htrace x hx
  refine ⟨A, H.isRmControlled_of_backwardPointTrace_of_derivative_bounds hphi hpinch
    hut hlast A hslabs hcurrent hfinal hM hqcan (hspace x hx) ?_ hrM⟩
  rw [hu, sub_sub_cancel]
  exact htime

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.isParabolicallyRmControlledBall_of_forall_nonempty_backwardPointTrace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.isParabolicallyRmControlledBall_of_forall_nonempty_backwardPointTrace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.isParabolicallyRmControlledBall_of_forall_nonempty_backwardPointTrace ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.isParabolicallyRmControlledBall_of_forall_nonempty_backwardPointTrace

theorem scalar_le_four_mul_max_on_ball_of_gradient_bound (t : _root_.Set.Icc (0 : ℝ) H.toHistory.horizon)
    (i : Fin H.eventCount) (hi : H.toHistory.activeStage t = i.castSucc)
    {Cgrad : ℝ≥0} {qcan r : ℝ}
    (hgrad : ∀ w, qcan < (H.toHistory.event i).incoming.flow.scalar t w →
      ∀ v : TangentSpace I3 w,
        |Perelman.CanonicalNeighborhood.scalarDifferential (H.toHistory.event i).incoming.flow
          t w v| ≤
          Cgrad * (H.toHistory.event i).incoming.flow.scalar t w *
            Real.sqrt ((H.toHistory.event i).incoming.flow.scalar t w) *
            Real.sqrt (((H.toHistory.event i).incoming.flow.base.metric t).inner w v v))
    (y : (H.toHistory.stage (H.toHistory.activeStage t)).Carrier)
    (hy : 0 < metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) y)
    (hr : (Cgrad : ℝ) * r *
      Real.sqrt (_root_.Max.max (metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) y)
        qcan) ≤ 1 / 4) :
    ∀ x ∈ riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) y r,
      metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) x ≤
        4 * _root_.Max.max (metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) y)
          qcan := by
  revert y
  rw [hi]
  intro y hy hr x hx
  rw [ObservedHistory.stageMetric_castSucc_apply] at hy hr hx ⊢
  have hx' : x ∈ riemannianClosedBallOf ((H.toHistory.event i).incoming.flow.base.metric t) y r :=
    le_of_lt (α := ENNReal) hx
  exact (H.toHistory.event i).incoming.scalar_le_four_mul_max_of_gradient_bound_at_time hgrad hy
    hr hx'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.scalar_le_four_mul_max_on_ball_of_gradient_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.scalar_le_four_mul_max_on_ball_of_gradient_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.scalar_le_four_mul_max_on_ball_of_gradient_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.scalar_le_four_mul_max_on_ball_of_gradient_bound

theorem isParabolicallyRmControlledBall_of_forall_nonempty_backwardPointTrace_of_gradient_bound
    {Ctime Cgrad : ℝ≥0} {qcan c : ℝ} {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi) (hpinch : H.EventSlabsPinched phi)
    (t : _root_.Set.Icc (0 : ℝ) H.toHistory.horizon) (i : Fin H.eventCount)
    (hi : H.toHistory.activeStage t = i.castSucc)
    (y : (H.toHistory.stage (H.toHistory.activeStage t)).Carrier)
    (hqR : qcan ≤ metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) y)
    (hR : 1 ≤ 4 * metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) y)
    (hc : 0 < c) (hcgrad : (Cgrad : ℝ) * c ≤ 1 / 4) (hctime : 8 * Ctime * c ^ 2 ≤ 1)
    (hcpinch : 3072 * (1 + phi 1 + phi 0) ^ 2 * c ^ 4 ≤ 1)
    {u : _root_.Set.Icc (0 : ℝ) H.toHistory.horizon} (hut : u ≤ t)
    (hu : (u : ℝ) = t - c ^ 2 /
      metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) y)
    (hslabs : H.EventSlabsDerivative Ctime qcan (H.toHistory.activeStage t))
    (hcurrent : (H.toHistory.event i).incoming.DerivativeBoundBefore Ctime qcan t)
    (hgrad : ∀ w, qcan < (H.toHistory.event i).incoming.flow.scalar t w →
      ∀ v : TangentSpace I3 w,
        |Perelman.CanonicalNeighborhood.scalarDifferential (H.toHistory.event i).incoming.flow
          t w v| ≤
          Cgrad * (H.toHistory.event i).incoming.flow.scalar t w *
            Real.sqrt ((H.toHistory.event i).incoming.flow.scalar t w) *
            Real.sqrt (((H.toHistory.event i).incoming.flow.base.metric t).inner w v v))
    (htrace : ∀ x ∈ riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) y
        (c / Real.sqrt
          (metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) y)),
      Nonempty (BackwardPointTrace H.toHistory (H.toHistory.activeStage u)
        (H.toHistory.activeStage t) (H.toHistory.activeStage_mono hut) x)) :
    H.toHistory.isParabolicallyRmControlledBall t y
      (c / Real.sqrt
        (metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) y)) := by
  set R := metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) y with hRdef
  have hRpos : 0 < R := by linarith
  have hsq : 0 < Real.sqrt R := Real.sqrt_pos.mpr hRpos
  have hsqsq : Real.sqrt R ^ 2 = R := Real.sq_sqrt hRpos.le
  have hmax : _root_.Max.max R qcan = R := max_eq_left hqR
  have hne : H.toHistory.activeStage t ≠ Fin.last H.eventCount := by
    rw [hi]
    exact Fin.castSucc_ne_last i
  have hr2 : (c / Real.sqrt R) ^ 2 = c ^ 2 / R := by rw [div_pow, hsqsq]
  have hr4 : (c / Real.sqrt R) ^ 4 = c ^ 4 / R ^ 2 := by
    rw [show (c / Real.sqrt R) ^ 4 = ((c / Real.sqrt R) ^ 2) ^ 2 by ring, hr2, div_pow]
    ring
  have hC : (0 : ℝ) ≤ Ctime := Ctime.coe_nonneg
  apply H.isParabolicallyRmControlledBall_of_forall_nonempty_backwardPointTrace hphi hpinch
    (M := 4 * R) hut (by positivity) (by rw [hu, hr2]) (fun h => absurd h hne) y hslabs
    (fun j hj => by
      have : j = i := Fin.castSucc_injective _ (hj.trans hi)
      subst this
      exact hcurrent)
    (fun _ h => absurd h hne) hR (by linarith [le_max_right R qcan])
  · intro x hx
    have h := H.scalar_le_four_mul_max_on_ball_of_gradient_bound t i hi hgrad y hRpos
      (by rw [← hRdef, hmax, mul_assoc, div_mul_cancel₀ c hsq.ne']; exact hcgrad) x hx
    rwa [← hRdef, hmax] at h
  · rw [hr2]
    field_simp
    nlinarith
  · rw [hr4]
    have hK : (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * (4 * R)) ^ 2 =
        3072 * (1 + phi 1 + phi 0) ^ 2 * R ^ 2 := by
      have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
      ring_nf
      rw [h3]
      ring
    rw [hK]
    field_simp
    nlinarith
  · exact htrace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.isParabolicallyRmControlledBall_of_forall_nonempty_backwardPointTrace_of_gradient_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.isParabolicallyRmControlledBall_of_forall_nonempty_backwardPointTrace_of_gradient_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.isParabolicallyRmControlledBall_of_forall_nonempty_backwardPointTrace_of_gradient_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.isParabolicallyRmControlledBall_of_forall_nonempty_backwardPointTrace_of_gradient_bound

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
