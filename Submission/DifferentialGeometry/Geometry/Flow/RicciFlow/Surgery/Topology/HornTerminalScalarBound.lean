import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HornChainBackwardTraces
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BoundedCurvatureAtDistanceBackwardTraces

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Submission.Set _root_.Filter _root_.Submission.Filter
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology _root_.NNReal _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory

universe u

private theorem exists_radius_sequence {R m : ℕ → ℝ} {K C : ℝ} (hK : 1 ≤ K) (hC : 0 ≤ C)
    (hm : ∀ n, 0 < m n) (hRm : _root_.Filter.Tendsto (fun n => R n / m n) _root_.Filter.atTop _root_.Filter.atTop) :
    ∃ D : ℕ → ℝ, (∀ n, 0 ≤ D n) ∧ _root_.Filter.Tendsto D _root_.Filter.atTop _root_.Filter.atTop ∧
      ∀ᶠ n in _root_.Filter.atTop, 8 * K * m n * (1 + C * D n) ^ 2 < R n := by
  have hX : _root_.Filter.Tendsto (fun n => R n / m n / (8 * K)) _root_.Filter.atTop atTop :=
    hRm.atTop_div_const (by positivity)
  refine ⟨fun n => Real.sqrt (R n / m n / (8 * K)) / (4 * (C + 1)), fun n => by positivity,
    (Real.tendsto_sqrt_atTop.comp hX).atTop_div_const (by positivity), ?_⟩
  filter_upwards [hX.eventually_ge_atTop 16] with n hn
  set X := R n / m n / (8 * K) with hXdef
  have hsX : 4 ≤ Real.sqrt X := by
    rw [show (4 : ℝ) = Real.sqrt 16 by
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hn
  have hsq : Real.sqrt X ^ 2 = X := Real.sq_sqrt (by linarith)
  have hCD : C * (Real.sqrt X / (4 * (C + 1))) ≤ Real.sqrt X / 4 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have h1 : 1 + C * (Real.sqrt X / (4 * (C + 1))) ≤ Real.sqrt X / 2 := by linarith
  have h0 : 0 ≤ 1 + C * (Real.sqrt X / (4 * (C + 1))) := by positivity
  have h2 : (1 + C * (Real.sqrt X / (4 * (C + 1)))) ^ 2 ≤ X / 4 := by
    calc (1 + C * (Real.sqrt X / (4 * (C + 1)))) ^ 2 ≤ (Real.sqrt X / 2) ^ 2 :=
          pow_le_pow_left₀ h0 h1 2
      _ = X / 4 := by rw [div_pow, hsq]; norm_num
  have hR : R n = 8 * K * m n * X := by
    rw [hXdef]
    field_simp
    exact (mul_div_cancel_right₀ (R n) (hm n).ne').symm
  have hRpos : 0 < R n := by
    rw [hR]
    have := hm n
    positivity
  have h3 : 8 * K * m n * (1 + C * (Real.sqrt X / (4 * (C + 1)))) ^ 2 ≤ 8 * K * m n * (X / 4) :=
    mul_le_mul_of_nonneg_left h2 (by have := hm n; positivity)
  nlinarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.exists_radius_sequence
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.exists_radius_sequence target :: scope.openDecls } }

theorem exists_eventually_terminal_scalar_bound_at_distance_of_mem_hornHalfRange :
    ∃ eta : ℝ, 0 < eta ∧
    ∀ {ε ε₁ κ C1 C2 qcan ρ : ℝ} {Ctime Cgrad : ℝ≥0} {phi : ℝ → ℝ},
      0 < ε → ε ≤ eta → 0 < κ → 0 < qcan → 0 < ρ →
      Perelman.AdmissiblePinchingFunction phi →
    ∀ (P₀ : ℕ → OrientedThreeStage.{u}) (H : ∀ n, RetainedCoreHistory (P₀ n))
      (hend : ∀ n, (H n).time (Fin.last (H n).eventCount) = (H n).horizon) (s : ℕ → ℝ)
      (G : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).IncomingSlab
        ((H n).time (Fin.last (H n).eventCount)) (s n))
      (hG : ∀ n, (G n).flow.base.metric ((H n).time (Fin.last (H n).eventCount)) =
        (H n).initialMetric (Fin.last (H n).eventCount))
      (L : ∀ n, (G n).TerminalLimitMetric) (hsing : ∀ n, (G n).SingularEndpoint)
      (parameters : ℕ → CutoffParameters) (εP Λ : ℕ → ℝ)
      (P : ∀ n, TerminalCorePresentation
        { stage := (H n).stage (Fin.last (H n).eventCount)
          startTime := (H n).time (Fin.last (H n).eventCount)
          endTime := s n
          startTime_nonneg := (H n).toHistory.time_nonneg (Fin.last (H n).eventCount)
          startTime_lt_endTime := (G n).lt
          slab := G n
          terminal := L n
          singular := hsing n
          parameters := parameters n } (εP n) (Λ n)),
      (∀ n, εP n ≤ eta) →
    ∀ (c : ∀ n, ConnectedComponents (G n).terminalRegularOpen), (∀ n, c n ∈ (P n).component) →
    ∀ (e : ∀ n, (P n).hornIndex (c n)) (x : ∀ n, (G n).terminalRegularOpen),
      (∀ n, x n ∈ (P n).hornHalfRange (c n) (e n)) →
      (∀ n, (H n).StronglyCanonicalBefore (Fin.last (H n).eventCount) (G n) ε ε₁ C1 C2 qcan
        (s n)) →
      (∀ n, (H n).EventSlabsDerivative Ctime qcan (Fin.last (H n).eventCount)) →
      (∀ n, (G n).DerivativeBoundBefore Ctime qcan (s n)) →
      (∀ n, (G n).GradientBoundBefore Cgrad qcan (s n)) →
      (∀ n, (H n).EventSlabsPinched phi) →
      (∀ n, Perelman.PhiAlmostNonnegative (G n).flow
        (_root_.Set.Ico ((H n).time (Fin.last (H n).eventCount)) (s n)) phi) →
      (∀ n, ∀ t₀ ∈ _root_.Set.Ioo ((H n).time (Fin.last (H n).eventCount)) (s n),
        (H n).TerminalNoncollapsedBefore (hend n) (G n) (hG n) κ ρ t₀) →
      _root_.Filter.Tendsto (fun n => metricScalarAt (L n).metric (x n) /
        _root_.Max.max (Λ n * ((P n).coreRadius ^ 2)⁻¹) qcan) _root_.Filter.atTop _root_.Filter.atTop →
      _root_.Filter.Tendsto (fun n => metricScalarAt (L n).metric (x n) * s n) _root_.Filter.atTop _root_.Filter.atTop →
    ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 1 ≤ Q ∧ ∀ᶠ n in _root_.Filter.atTop,
      (∀ w : (G n).terminalRegularOpen,
        riemannianEDistOf (L n).metric (x n) w <
          ENNReal.ofReal (A / Real.sqrt (metricScalarAt (L n).metric (x n))) →
        metricScalarAt (L n).metric w ≤ Q * metricScalarAt (L n).metric (x n)) ∧
      IsCompact (riemannianClosedBallOf (L n).metric (x n)
        (A / Real.sqrt (metricScalarAt (L n).metric (x n)))) := by
  obtain ⟨etab, hetab, hsup⟩ := eventually_chain_backward_traces_of_mem_hornHalfRange.{u}
  refine ⟨min etab coneAccuracy, lt_min hetab coneAccuracy_pos, ?_⟩
  intro ε ε₁ κ C1 C2 qcan ρ Ctime Cgrad phi hε hεη hκ hq hρ hphi P₀ H hend s G hG L hsing
    parameters εP Λ P hεP c hc e x hx hcan hslabs hder hgrad hpinch hpinchG hnc hgrow hRs
  have hεb : ε ≤ etab := hεη.trans (min_le_left _ _)
  have hεc : ε ≤ coneAccuracy := hεη.trans (min_le_right _ _)
  set m : ℕ → ℝ := fun n => _root_.Max.max (Λ n * ((P n).coreRadius ^ 2)⁻¹) qcan with hmdef
  have hm : ∀ n, 0 < m n := fun n => hq.trans_le (le_max_right _ _)
  obtain ⟨D, hD0, hD, hDev⟩ := exists_radius_sequence (K := _root_.Max.max (4 * C2) 1) (C := Cgrad)
    (le_max_right _ _) Cgrad.coe_nonneg hm hgrow
  have hRm : ∀ n, metricScalarAt (L n).metric (x n) =
      metricScalarAt (L n).metric (x n) / m n * m n := fun n =>
    (div_mul_cancel₀ _ (hm n).ne').symm
  have hRtend : _root_.Filter.Tendsto (fun n => metricScalarAt (L n).metric (x n)) _root_.Filter.atTop atTop := by
    refine _root_.Filter.tendsto_atTop_mono' _root_.Filter.atTop ?_ (hgrow.atTop_mul_const hq)
    filter_upwards [hgrow.eventually_ge_atTop 0] with n h
    have e := hRm n
    have h1 := mul_le_mul_of_nonneg_left (le_max_right (Λ n * ((P n).coreRadius ^ 2)⁻¹) qcan) h
    change metricScalarAt (L n).metric (x n) / m n * qcan ≤ metricScalarAt (L n).metric (x n)
    change _ ≤ metricScalarAt (L n).metric (x n) / m n * m n at h1
    linarith
  have hbig : ∀ᶠ n in _root_.Filter.atTop, 8 * _root_.Max.max (4 * C2 * (Λ n * ((P n).coreRadius ^ 2)⁻¹))
      (_root_.Max.max (Λ n * ((P n).coreRadius ^ 2)⁻¹) qcan) * (1 + Cgrad * D n) ^ 2 <
        metricScalarAt (L n).metric (x n) := by
    filter_upwards [hDev] with n hn
    have hlam : 0 < Λ n * ((P n).coreRadius ^ 2)⁻¹ :=
      mul_pos (zero_lt_one.trans_le (P n).Lambda_ge_one)
        (inv_pos.mpr (pow_pos (P n).coreRadius_pos 2))
    have hμ : _root_.Max.max (4 * C2 * (Λ n * ((P n).coreRadius ^ 2)⁻¹))
        (_root_.Max.max (Λ n * ((P n).coreRadius ^ 2)⁻¹) qcan) ≤ _root_.Max.max (4 * C2) 1 * m n := by
      refine max_le ?_ ?_
      · have h1 : 4 * C2 * (Λ n * ((P n).coreRadius ^ 2)⁻¹) ≤
            max (4 * C2) 1 * (Λ n * ((P n).coreRadius ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hlam.le
        exact h1.trans (mul_le_mul_of_nonneg_left (le_max_left _ _)
          (zero_le_one.trans (le_max_right _ _)))
      · exact le_mul_of_one_le_left (hm n).le (le_max_right _ _)
    have hsq : 0 ≤ (1 + (Cgrad : ℝ) * D n) ^ 2 := sq_nonneg _
    nlinarith
  have hqx : ∀ᶠ n in _root_.Filter.atTop, qcan < metricScalarAt (L n).metric (x n) := by
    filter_upwards [hgrow.eventually_ge_atTop 2] with n hn
    have e := hRm n
    have h1 : qcan ≤ m n := le_max_right _ _
    have h2 := mul_le_mul_of_nonneg_right hn (hm n).le
    linarith
  have hsupply := hbig.mono fun n hn =>
    hsup (H n) (G n) (L n) (hsing n) (parameters n) (P n) ((hεP n).trans (min_le_left _ _))
      (c n) (hc n) (e n) (x n) (hx n) hε hεb hq (hcan n) (hder n) (hgrad n) (hD0 n) hn
  exact RetainedCoreHistory.eventually_terminal_scalar_bound_at_distance_of_chain_backward_traces
    hεc hκ hphi (by norm_num : (0 : ℝ) < 1 / 5) P₀ H hend s G hG L x (fun _ => qcan) (fun _ => ρ)
    (fun _ => hq) (fun _ => hρ) hqx hRtend hRs
    (fun n => (hcan n).spatiallyCanonicalBefore) hslabs hder hgrad hpinch hpinchG hnc
    ((Real.tendsto_sqrt_atTop.comp hRtend).const_mul_atTop hρ) D hD hsupply

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.exists_eventually_terminal_scalar_bound_at_distance_of_mem_hornHalfRange then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.exists_eventually_terminal_scalar_bound_at_distance_of_mem_hornHalfRange"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.exists_eventually_terminal_scalar_bound_at_distance_of_mem_hornHalfRange ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.exists_eventually_terminal_scalar_bound_at_distance_of_mem_hornHalfRange

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory
