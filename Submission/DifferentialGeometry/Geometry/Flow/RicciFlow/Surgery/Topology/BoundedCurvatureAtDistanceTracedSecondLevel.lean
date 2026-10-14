import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BoundedCurvatureAtDistanceChainBuffers

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Submission.Set _root_.Filter _root_.Submission.Filter
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology _root_.NNReal _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instSigmaCompactSpaceSubtypeCarrierMemOpensTerminalRegularOpen {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s) :
    SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instSigmaCompactSpaceSubtypeCarrierMemOpensTerminalRegularOpen
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instSigmaCompactSpaceSubtypeCarrierMemOpensTerminalRegularOpen target :: scope.openDecls } }

theorem OrientedThreeStage.ClosedSlab.scaled_endpoint_scalar_eq {P : OrientedThreeStage.{u}}
    {a s Q : ℝ} (A : P.ClosedSlab a s) (hQ : 0 < Q)
    (y : (A.restrictIncoming le_rfl A.lt le_rfl).terminalRegularOpen) :
    metricScalarAt (scaleMetric Q hQ (A.endpointTerminalLimitMetric P).metric) y =
      Q⁻¹ * A.flow.scalar s y.val := by
  have h : metricScalarAt (A.endpointTerminalLimitMetric P).metric y = A.flow.scalar s y.val :=
    metricScalarAt_restrictOpen _ _ _
  rw [metricScalarAt_scaleMetric, h]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.scaled_endpoint_scalar_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.scaled_endpoint_scalar_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.scaled_endpoint_scalar_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.scaled_endpoint_scalar_eq

theorem OrientedThreeStage.ClosedSlab.scaled_endpoint_edist_eq {P : OrientedThreeStage.{u}}
    {a s Q : ℝ} (A : P.ClosedSlab a s) (hQ : 0 < Q)
    (y z : (A.restrictIncoming le_rfl A.lt le_rfl).terminalRegularOpen) :
    riemannianEDistOf (scaleMetric Q hQ (A.endpointTerminalLimitMetric P).metric) y z =
      ENNReal.ofReal (Real.sqrt Q) * riemannianEDistOf (A.flow.base.metric s) y.val z.val := by
  rw [DifferentialGeometry.edistOf_scale, A.riemannianEDistOf_endpointTerminalLimitMetric]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.scaled_endpoint_edist_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.scaled_endpoint_edist_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.scaled_endpoint_edist_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.scaled_endpoint_edist_eq

private theorem exists_ray_chain_times {T ρ : ℝ} (hρ : 0 < ρ) :
    ∃ N : ℕ, 0 < N ∧ T / N < ρ := by
  refine ⟨⌈T / ρ⌉₊ + 1, Nat.succ_pos _, ?_⟩
  have hN : T / ρ < (⌈T / ρ⌉₊ + 1 : ℕ) := by
    push_cast
    exact (Nat.le_ceil _).trans_lt (lt_add_one _)
  have hNpos : (0 : ℝ) < (⌈T / ρ⌉₊ + 1 : ℕ) := by positivity
  rw [div_lt_iff₀ hNpos]
  rw [div_lt_iff₀ hρ] at hN
  linarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_ray_chain_times
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_ray_chain_times target :: scope.openDecls } }

private theorem isCompact_image_Iic_of_ray {X : Type*} [TopologicalSpace X] {rho : ℝ}
    (g : C(_root_.Set.Ico 0 rho, X)) (T : _root_.Set.Ico 0 rho) :
    IsCompact (g '' {s : _root_.Set.Ico 0 rho | (s : ℝ) ≤ T}) := by
  refine IsCompact.image ?_ g.continuous
  have hcl : {s : _root_.Set.Ico 0 rho | (s : ℝ) ≤ T} =
      (Subtype.val : _root_.Set.Ico 0 rho → ℝ) ⁻¹' _root_.Set.Icc 0 (T : ℝ) := by
    ext s
    simp only [_root_.Set.mem_ofPred_eq, _root_.Set.mem_preimage, _root_.Set.mem_Icc]
    exact ⟨fun h => ⟨s.2.1, h⟩, fun h => h.2⟩
  rw [hcl]
  apply (Topology.IsInducing.subtypeVal).isCompact_preimage' _root_.CompactIccSpace.isCompact_Icc
  intro r hr
  exact ⟨⟨r, hr.1, hr.2.trans_lt T.2.2⟩, rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isCompact_image_Iic_of_ray
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isCompact_image_Iic_of_ray target :: scope.openDecls } }

theorem RetainedCoreHistory.exists_trace_first_on_witness_ball_of_scaled_ray_chain
    {P₀ : OrientedThreeStage.{u}} (H : RetainedCoreHistory P₀) {T : ℝ}
    (A : (H.stage (Fin.last H.eventCount)).ClosedSlab (H.time (Fin.last H.eventCount)) T)
    (x : (A.restrictIncoming le_rfl A.lt le_rfl).terminalRegularOpen)
    (hQ : 1 ≤ A.flow.scalar T x.val) {Kc lam θ D : ℝ} {Ctime Cgrad : ℝ≥0} {Phi : ℝ → ℝ}
    (hPhi : Perelman.AdmissiblePinchingFunction Phi) (hlam : 0 ≤ lam) (hθ : 0 < θ)
    (htrace : ∀ (N : ℕ) (p : ℕ → (H.stage (Fin.last H.eventCount)).Carrier) (δ : ℕ → ℝ)
      (M τ : ℝ), p 0 = x.val → (∀ k ≤ N, 0 < δ k) →
      (∀ k < N, p (k + 1) ∈ riemannianBallOf (A.flow.base.metric T) (p k) (δ k)) →
      (∀ k ≤ N, ∀ z ∈ riemannianBallOf (A.flow.base.metric T) (p k) (δ k),
        A.flow.scalar T z ≤ M) →
      Kc * A.flow.scalar T x.val ≤ M → 1 ≤ M → 0 ≤ τ → τ ≤ T →
      (Ctime : ℝ) * M * τ ≤ 1 / 2 → 4 * M * τ ≤ θ →
      2 * StandardCap.transitionEnd + Real.sqrt (8 * M) *
        Real.exp (9 * (8 * Real.sqrt 3 * (1 + Phi 1 + Phi 0) * M) * τ) *
          (lam / Real.sqrt (A.flow.scalar T x.val) + ∑ k ∈ Finset.range (N + 1), δ k) < D →
      ∀ k ≤ N, ∀ z ∈ riemannianBallOf (A.flow.base.metric T) (p k) (δ k),
        ∃ first : Fin (H.eventCount + 1), H.time first ≤ T - τ ∧
          Nonempty (BackwardPointTrace H.toHistory first (Fin.last H.eventCount)
            (Fin.le_last first) z))
    {q : ℝ} (hqQ : q ≤ A.flow.scalar T x.val)
    (hgradient : ∀ y, ∀ t ∈ _root_.Set.Ioo (H.time (Fin.last H.eventCount)) T, q < A.flow.scalar t y →
      ∀ v : TangentSpace ThreeModel y,
        |scalarDifferential (A.restrictIncoming le_rfl A.lt le_rfl).flow t y v| ≤
          Cgrad * A.flow.scalar t y * Real.sqrt (A.flow.scalar t y) *
            Real.sqrt ((A.flow.base.metric t).inner y v v))
    {eps C1 C2 : ℝ}
    (hW : ∀ y, q < A.flow.scalar T y →
      ∃ W : SpatialCanonicalWitness (A.flow.base.metric T) eps C1 C2 y, W.capTubeHasNeckChart eps)
    {K L : ℝ} (hK : 1 ≤ K) (hL : 3 ≤ L) {N : ℕ}
    (pt : ℕ → (A.restrictIncoming le_rfl A.lt le_rfl).terminalRegularOpen) (hpt0 : pt 0 = x)
    (hptR : ∀ k < N, metricScalarAt (scaleMetric (A.flow.scalar T x.val) (zero_lt_one.trans_le hQ)
      (A.endpointTerminalLimitMetric (H.stage (Fin.last H.eventCount))).metric) (pt k) ≤
        K * L + 1)
    (hptd : ∀ k < N, riemannianEDistOf (scaleMetric (A.flow.scalar T x.val)
      (zero_lt_one.trans_le hQ)
      (A.endpointTerminalLimitMetric (H.stage (Fin.last H.eventCount))).metric) (pt k)
        (pt (k + 1)) <
      ENNReal.ofReal (localPropagationRadius Cgrad / (2 * Real.sqrt (2 * ((K + 1) * L)))))
    (hyX : |metricScalarAt (scaleMetric (A.flow.scalar T x.val) (zero_lt_one.trans_le hQ)
      (A.endpointTerminalLimitMetric (H.stage (Fin.last H.eventCount))).metric) (pt N) - L| < 1)
    (hT : secondLevelTraceDepth K C2 Kc θ Ctime ≤ A.flow.scalar T x.val * T)
    (hD : 2 * StandardCap.transitionEnd +
      Real.sqrt (8 * (secondLevelTraceConstant K C2 Kc * L)) *
      Real.exp (9 * (8 * Real.sqrt 3 * (1 + Phi 1 + Phi 0)) *
        (3 / 2 * secondLevelTraceConstant K C2 Kc * secondLevelTraceDepth K C2 Kc θ Ctime)) *
      (lam + (N * (localPropagationRadius Cgrad / (2 * Real.sqrt (2 * ((K + 1) * L)))) + 1)) <
        D) :
    ∃ first : Fin (H.eventCount + 1),
      H.time first ≤ T - secondLevelTraceDepth K C2 Kc θ Ctime / A.flow.scalar T (pt N).val ∧
      ∀ z ∈ riemannianBallOf (A.flow.base.metric T) (pt N).val
        (Real.sqrt (A.flow.scalar T (pt N).val))⁻¹,
        Nonempty (BackwardPointTrace H.toHistory first (Fin.last H.eventCount)
          (Fin.le_last first) z) := by
  have hQpos : 0 < A.flow.scalar T x.val := zero_lt_one.trans_le hQ
  have hsQ : 0 < Real.sqrt (A.flow.scalar T x.val) := Real.sqrt_pos.mpr hQpos
  have hflow (k : ℕ) : A.flow.scalar T (pt k).val = A.flow.scalar T x.val *
      metricScalarAt (scaleMetric (A.flow.scalar T x.val) (zero_lt_one.trans_le hQ)
        (A.endpointTerminalLimitMetric (H.stage (Fin.last H.eventCount))).metric) (pt k) := by
    rw [A.scaled_endpoint_scalar_eq, ← mul_assoc, mul_inv_cancel₀ hQpos.ne', one_mul]
  refine RetainedCoreHistory.exists_trace_first_on_witness_ball_of_ray_chain H A x hQ hPhi hlam
    hθ htrace hqQ hgradient hW hK hL (fun k => (pt k).val) (by rw [hpt0]) (fun k hk => ?_)
    (fun k hk => ?_) ?_ ?_ hT hD
  · rw [hflow k]
    have h1 := mul_le_mul_of_nonneg_left (hptR k hk) hQpos.le
    have h2 : A.flow.scalar T x.val * (K * L + 1) ≤ (K + 1) * L * A.flow.scalar T x.val := by
      have : 0 ≤ A.flow.scalar T x.val * (L - 1) := mul_nonneg hQpos.le (by linarith)
      nlinarith
    exact h1.trans h2
  · have h := hptd k hk
    rw [A.scaled_endpoint_edist_eq] at h
    have hne : ENNReal.ofReal (Real.sqrt (A.flow.scalar T x.val)) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr hsQ).ne'
    rw [ENNReal.ofReal_div_of_pos hsQ, ENNReal.lt_div_iff_mul_lt (Or.inl hne)
      (Or.inl ENNReal.ofReal_ne_top), mul_comm]
    exact h
  · rw [hflow N]
    have := (abs_lt.mp hyX).1
    nlinarith
  · rw [hflow N]
    have := (abs_lt.mp hyX).2
    nlinarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.exists_trace_first_on_witness_ball_of_scaled_ray_chain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.exists_trace_first_on_witness_ball_of_scaled_ray_chain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.exists_trace_first_on_witness_ball_of_scaled_ray_chain ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.exists_trace_first_on_witness_ball_of_scaled_ray_chain

private theorem ray_chain_step {rho T : ℝ} {N : ℕ} (hN : 0 < N) (hT : 0 ≤ T)
    {ρ : ℝ} (hNT : T / N < ρ) (sk : ℕ → _root_.Set.Ico 0 rho)
    (hsk : ∀ k, (sk k : ℝ) = _root_.Min.min (k * T / N) T) (k : ℕ) (hk : k < N) :
    edist (sk k) (sk (k + 1)) < ENNReal.ofReal ρ := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : (k : ℝ) * T / N ≤ T := by
    rw [div_le_iff₀ hNr]
    have : (k : ℝ) ≤ N := by exact_mod_cast hk.le
    nlinarith
  have h2 : ((k + 1 : ℕ) : ℝ) * T / N ≤ T := by
    rw [div_le_iff₀ hNr]
    have : ((k + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hk
    nlinarith
  rw [edist_dist, Subtype.dist_eq, Real.dist_eq, hsk, hsk, min_eq_left h1, min_eq_left h2]
  have heq : (k : ℝ) * T / N - ((k + 1 : ℕ) : ℝ) * T / N = -(T / N) := by
    push_cast
    ring
  rw [heq, abs_neg, abs_of_nonneg (by positivity)]
  exact (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt (by positivity) hNT)).mpr hNT

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ray_chain_step
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ray_chain_step target :: scope.openDecls } }

theorem RetainedCoreHistory.eventually_second_level_traces_of_chain_traces
    (P₀ : ℕ → OrientedThreeStage.{u}) (H : ∀ i, RetainedCoreHistory (P₀ i)) (time : ℕ → ℝ)
    (A : ∀ i, ((H i).stage (Fin.last (H i).eventCount)).ClosedSlab
      ((H i).time (Fin.last (H i).eventCount)) (time i))
    (Cgrad : ℝ≥0) (q : ℕ → ℝ)
    (hgradient : ∀ i y, ∀ t ∈ _root_.Set.Ioo ((H i).time (Fin.last (H i).eventCount)) (time i),
      q i < (A i).flow.scalar t y → ∀ v : TangentSpace ThreeModel y,
        |scalarDifferential ((A i).restrictIncoming le_rfl (A i).lt le_rfl).flow t y v| ≤
          Cgrad * (A i).flow.scalar t y * Real.sqrt ((A i).flow.scalar t y) *
            Real.sqrt (((A i).flow.base.metric t).inner y v v))
    (x : ∀ i, ((A i).restrictIncoming le_rfl (A i).lt le_rfl).terminalRegularOpen)
    (hQ : ∀ i, 1 ≤ (A i).flow.scalar (time i) (x i).val)
    (hqQ : ∀ i, q i ≤ (A i).flow.scalar (time i) (x i).val)
    {eps C1 C2 : ℝ}
    (hW : ∀ i y, q i < (A i).flow.scalar (time i) y →
      ∃ W : SpatialCanonicalWitness ((A i).flow.base.metric (time i)) eps C1 C2 y,
        W.capTubeHasNeckChart eps)
    {Kc lam θ : ℝ} (hlam : 0 ≤ lam) (hθ : 0 < θ) {Ctime : ℝ≥0} {Phi : ℝ → ℝ}
    (hPhi : Perelman.AdmissiblePinchingFunction Phi) (D : ℕ → ℝ) (hD : _root_.Filter.Tendsto D _root_.Filter.atTop _root_.Filter.atTop)
    (htime : _root_.Filter.Tendsto (fun i => (A i).flow.scalar (time i) (x i).val * time i) _root_.Filter.atTop _root_.Filter.atTop)
    (htrace : ∀ i (N : ℕ) (p : ℕ → ((H i).stage (Fin.last (H i).eventCount)).Carrier)
      (δ : ℕ → ℝ) (M τ : ℝ), p 0 = (x i).val → (∀ k ≤ N, 0 < δ k) →
      (∀ k < N, p (k + 1) ∈ riemannianBallOf ((A i).flow.base.metric (time i)) (p k) (δ k)) →
      (∀ k ≤ N, ∀ z ∈ riemannianBallOf ((A i).flow.base.metric (time i)) (p k) (δ k),
        (A i).flow.scalar (time i) z ≤ M) →
      Kc * (A i).flow.scalar (time i) (x i).val ≤ M → 1 ≤ M → 0 ≤ τ → τ ≤ time i →
      (Ctime : ℝ) * M * τ ≤ 1 / 2 → 4 * M * τ ≤ θ →
      2 * StandardCap.transitionEnd + Real.sqrt (8 * M) *
        Real.exp (9 * (8 * Real.sqrt 3 * (1 + Phi 1 + Phi 0) * M) * τ) *
          (lam / Real.sqrt ((A i).flow.scalar (time i) (x i).val) +
            ∑ k ∈ Finset.range (N + 1), δ k) < D i →
      ∀ k ≤ N, ∀ z ∈ riemannianBallOf ((A i).flow.base.metric (time i)) (p k) (δ k),
        ∃ first : Fin ((H i).eventCount + 1), (H i).time first ≤ time i - τ ∧
          Nonempty (BackwardPointTrace (H i).toHistory first (Fin.last (H i).eventCount)
            (Fin.le_last first) z))
    {f : ℕ → ℕ} (hf : StrictMono f) (Pl : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
    (F : PointedRiemannianConvergenceMaps
      ({ obj := fun i =>
          { M := ((A i).restrictIncoming le_rfl (A i).lt le_rfl).terminalRegularOpen
            basepoint := x i
            metric := scaleMetric ((A i).flow.scalar (time i) (x i).val)
              (zero_lt_one.trans_le (hQ i))
              ((A i).endpointTerminalLimitMetric
                ((H i).stage (Fin.last (H i).eventCount))).metric } } :
        PointedRiemannianSeq.{u, 0, 0} ThreeModel) Pl f)
    (M : MetricConvergenceData F)
    (hcanonical : ∀ n, M.domain n = CanonicalMetricCompactness.canonicalSourceData F n)
    {rho : ℝ} (g : C(_root_.Set.Ico 0 rho, Pl.M))
    (hg : ∀ s t : _root_.Set.Ico 0 rho, riemannianEDistOf Pl.metric (g s) (g t) = _root_.EDist.edist s t)
    (s0 : _root_.Set.Ico 0 rho) (hs0 : (s0 : ℝ) = 0) (hg0 : g s0 = Pl.basepoint)
    (times : ℕ → _root_.Set.Ico 0 rho) (xs : ℕ → Pl.M) (hxs : ∀ m, xs m = g (times m)) {K : ℝ}
    (hK1 : 1 ≤ K)
    (hK : ∀ m, ∀ s : _root_.Set.Ico 0 rho, (s : ℝ) ≤ times m →
      metricScalarAt Pl.metric (g s) ≤ K * metricScalarAt Pl.metric (g (times m)))
    (h3 : ∀ m, 3 ≤ metricScalarAt Pl.metric (g (times m))) :
    ∃ θ₂ : ℝ, 0 < θ₂ ∧ ∀ m, ∀ᶠ n in _root_.Filter.atTop, ∃ first : Fin ((H (f n)).eventCount + 1),
      (H (f n)).time first ≤ time (f n) - θ₂ /
        (A (f n)).flow.scalar (time (f n)) (F.map n (xs m)).val ∧
      ∀ z ∈ riemannianBallOf ((A (f n)).flow.base.metric (time (f n)))
        (F.map n (xs m)).val
        (Real.sqrt ((A (f n)).flow.scalar (time (f n)) (F.map n (xs m)).val))⁻¹,
        Nonempty (BackwardPointTrace (H (f n)).toHistory first
          (Fin.last (H (f n)).eventCount) (Fin.le_last first) z) := by
  refine ⟨secondLevelTraceDepth K C2 Kc θ Ctime, secondLevelTraceDepth_pos Ctime hθ, fun m => ?_⟩
  have hL3 := h3 m
  have hρ : 0 < localPropagationRadius Cgrad /
      (2 * Real.sqrt (2 * ((K + 1) * metricScalarAt Pl.metric (g (times m))))) :=
    div_pos (localPropagationRadius_pos Cgrad.coe_nonneg) (by positivity)
  have hT0 : (0 : ℝ) ≤ times m := (times m).2.1
  obtain ⟨N, hN0, hNT⟩ := exists_ray_chain_times (T := (times m : ℝ)) hρ
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  obtain ⟨sk, hsk⟩ : ∃ sk : ℕ → _root_.Set.Ico 0 rho,
      ∀ k, (sk k : ℝ) = _root_.Min.min (k * (times m : ℝ) / N) (times m) :=
    ⟨fun k => ⟨min (k * (times m : ℝ) / N) (times m),
      le_min (by positivity) hT0, (min_le_right _ _).trans_lt (times m).2.2⟩, fun _ => rfl⟩
  have hsk0 : sk 0 = s0 := Subtype.ext (by
    rw [hsk, hs0, Nat.cast_zero, _root_.MulZeroClass.zero_mul, zero_div, min_eq_left hT0])
  have hskN : sk N = times m := Subtype.ext (by
    rw [hsk, mul_div_cancel_left₀ _ hNr.ne', min_self])
  have hskle (k : ℕ) : (sk k : ℝ) ≤ times m := by rw [hsk]; exact min_le_right _ _
  have hKset := isCompact_image_Iic_of_ray g (times m)
  have href : ∀ k, (M.domain k).referenceMetric = (M.domain k).limitMetric := fun k => by
    rw [hcanonical k]
    rfl
  obtain ⟨k0, hk0⟩ := Perelman.KappaSolutions.pointedScalar_uniform_on_compact_of_canonical_domains
    M hcanonical _ hKset 1 one_pos
  have hE2 : ∀ᶠ n in _root_.Filter.atTop, ∀ k ∈ Finset.range N,
      riemannianEDistOf (scaleMetric ((A (f n)).flow.scalar (time (f n)) (x (f n)).val)
        (zero_lt_one.trans_le (hQ (f n)))
        ((A (f n)).endpointTerminalLimitMetric
          ((H (f n)).stage (Fin.last (H (f n)).eventCount))).metric)
        (F.map n (g (sk k))) (F.map n (g (sk (k + 1)))) <
      ENNReal.ofReal (localPropagationRadius Cgrad /
        (2 * Real.sqrt (2 * ((K + 1) * metricScalarAt Pl.metric (g (times m)))))) := by
    refine (Filter.eventually_all_finset _).mpr fun k hk => ?_
    refine eventually_riemannianEDistOf_map_lt_of_metric_convergence M href _ _ ?_
    rw [hg]
    exact ray_chain_step hN0 hT0 hNT sk hsk k (Finset.mem_range.mp hk)
  filter_upwards [_root_.Filter.eventually_ge_atTop k0, hE2,
    (hD.comp hf.tendsto_atTop).eventually_gt_atTop
      (2 * StandardCap.transitionEnd + Real.sqrt (8 * (secondLevelTraceConstant K C2 Kc *
        metricScalarAt Pl.metric (g (times m)))) *
        Real.exp (9 * (8 * Real.sqrt 3 * (1 + Phi 1 + Phi 0)) *
          (3 / 2 * secondLevelTraceConstant K C2 Kc * secondLevelTraceDepth K C2 Kc θ Ctime)) *
        (lam + (N * (localPropagationRadius Cgrad /
          (2 * Real.sqrt (2 * ((K + 1) * metricScalarAt Pl.metric (g (times m)))))) + 1))),
    (htime.comp hf.tendsto_atTop).eventually_ge_atTop (secondLevelTraceDepth K C2 Kc θ Ctime)]
    with n hn hE hDn hTn
  obtain ⟨-, hscal⟩ := hk0 n hn
  have hmem (k : ℕ) : g (sk k) ∈ g '' {s : _root_.Set.Ico 0 rho | (s : ℝ) ≤ times m} :=
    ⟨sk k, hskle k, rfl⟩
  have key := RetainedCoreHistory.exists_trace_first_on_witness_ball_of_scaled_ray_chain
    (H (f n)) (A (f n)) (x (f n)) (hQ (f n)) hPhi hlam hθ (htrace (f n)) (hqQ (f n))
    (hgradient (f n)) (hW (f n)) hK1 hL3 (N := N) (fun k => F.map n (g (sk k)))
    (by
      change F.map n (g (sk 0)) = x (f n)
      rw [hsk0, hg0]
      simpa only [PointedRiemannianConvergenceMaps.map] using F.basepoint_map n)
    (fun k _ => by
      have h1 := hscal _ (hmem k)
      have h2 := hK m (sk k) (hskle k)
      have h3 := (abs_lt.mp h1).2
      change metricScalarAt (scaleMetric ((A (f n)).flow.scalar (time (f n)) (x (f n)).val)
        (zero_lt_one.trans_le (hQ (f n))) ((A (f n)).endpointTerminalLimitMetric
          ((H (f n)).stage (Fin.last (H (f n)).eventCount))).metric) (F.map n (g (sk k))) ≤ _
      change metricScalarAt (scaleMetric ((A (f n)).flow.scalar (time (f n)) (x (f n)).val)
        (zero_lt_one.trans_le (hQ (f n))) ((A (f n)).endpointTerminalLimitMetric
          ((H (f n)).stage (Fin.last (H (f n)).eventCount))).metric) (F.map n (g (sk k))) -
          metricScalarAt Pl.metric (g (sk k)) < 1 at h3
      linarith)
    (fun k hk => hE k (Finset.mem_range.mpr hk))
    (by
      have h1 := hscal _ (hmem N)
      have hL : metricScalarAt Pl.metric (g (sk N)) = metricScalarAt Pl.metric (g (times m)) := by
        rw [hskN]
      rw [hL] at h1
      exact h1)
    hTn hDn
  have hpN : F.map n (g (sk N)) = F.map n (xs m) := by rw [hskN, hxs m]
  obtain ⟨first, hfirst, hball⟩ := key
  refine ⟨first, ?_, fun z hz => hball z ?_⟩
  · change (H (f n)).time first ≤ time (f n) - secondLevelTraceDepth K C2 Kc θ Ctime /
      (A (f n)).flow.scalar (time (f n)) (F.map n (g (sk N))).val at hfirst
    rw [hpN] at hfirst
    exact hfirst
  · rw [hpN]
    exact hz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.eventually_second_level_traces_of_chain_traces then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.eventually_second_level_traces_of_chain_traces"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.eventually_second_level_traces_of_chain_traces ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.eventually_second_level_traces_of_chain_traces

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
