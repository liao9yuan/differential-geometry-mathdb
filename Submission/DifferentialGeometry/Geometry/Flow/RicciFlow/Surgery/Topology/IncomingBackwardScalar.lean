import Submission.DifferentialGeometry.Analysis.Calculus.Derivative.SuperlevelMonotonicity
import Submission.DifferentialGeometry.Analysis.Calculus.Derivative.ClippedReciprocal
import Submission.DifferentialGeometry.Analysis.Calculus.Derivative.LeftEndpoint
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalScalarCurvature

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Filter
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.NNReal _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s)

theorem lipschitzOnWith_inv_max_scalar_at
    (G : P.IncomingSlab a s) {q : ℝ} {C : ℝ≥0} (hq : 0 < q)
    (x : P.Carrier)
    (hbound : ∀ t ∈ _root_.Set.Ioo a s, q < G.flow.scalar t x →
      |derivWithin (fun v => G.flow.scalar v x) (_root_.Set.Iic t) t| ≤
        C * G.flow.scalar t x ^ 2) :
    LipschitzOnWith C (fun t => (_root_.Max.max q (G.flow.scalar t x))⁻¹) (_root_.Set.Ico a s) := by
  have hlip : LipschitzOnWith C (fun t => (_root_.Max.max q (G.flow.scalar t x))⁻¹) (_root_.Set.Ioo a s) := by
    apply DifferentialGeometry.Analysis.lipschitzOnWith_inv_max_of_quadratic_deriv_bound
      (r' := fun t => derivWithin (fun v => G.flow.scalar v x) (_root_.Set.Iic t) t)
      hq _root_.Set.ordConnected_Ioo
    · intro t ht
      exact (G.equation.scalarTime (K := _root_.Set.Ioo a s) ht _root_.Set.Ioo_subset_Ico_self x).continuousWithinAt
    · intro t ht _
      exact DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.hasDerivWithinAt_left_of_mem_nhdsLE
        (G.equation.scalarTime (K := _root_.Set.Ioo a s) ht _root_.Set.Ioo_subset_Ico_self x)
        (mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds ht.1 ht.2))
    · exact hbound
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro t ht v hv
  let b := (_root_.Max.max t v + s) / 2
  have hmb : _root_.Max.max t v < b := by dsimp [b]; linarith [max_lt ht.2 hv.2]
  have hbs : b < s := by dsimp [b]; linarith [max_lt ht.2 hv.2]
  have hab : a < b := (ht.1.trans (le_max_left _ _)).trans_lt hmb
  have hsub : _root_.Set.Icc a b ⊆ _root_.Set.Ico a s := fun z hz => ⟨hz.1, hz.2.trans_lt hbs⟩
  have hc : ContinuousOn (fun t => (_root_.Max.max q (G.flow.scalar t x))⁻¹) (_root_.Set.Icc a b) := by
    apply (continuous_max.comp_continuousOn (continuousOn_const.prodMk ?_)).inv₀
      (fun t _ => ne_of_gt (hq.trans_le (le_max_left _ _)))
    intro t ht
    exact (G.equation.scalarTime (hsub ht) Subset.rfl x).continuousWithinAt.mono hsub
  have hext : LipschitzOnWith C (fun t => (_root_.Max.max q (G.flow.scalar t x))⁻¹) (_root_.Set.Icc a b) := by
    rw [← closure_Ioo hab.ne]
    apply LipschitzOnWith.closure
    · simpa only [closure_Ioo hab.ne] using hc
    · exact hlip.mono (fun z hz => ⟨hz.1, hz.2.trans hbs⟩)
  exact hext.dist_le_mul t ⟨ht.1, (le_max_left _ _).trans hmb.le⟩
    v ⟨hv.1, (le_max_right _ _).trans hmb.le⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.lipschitzOnWith_inv_max_scalar_at then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.lipschitzOnWith_inv_max_scalar_at"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.lipschitzOnWith_inv_max_scalar_at ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.lipschitzOnWith_inv_max_scalar_at


theorem scalar_le_two_mul_of_time_distance_le
    {q Q : ℝ} {C : ℝ≥0} (hq : 0 < q)
    (x : P.Carrier)
    (hbound : ∀ t ∈ _root_.Set.Ioo a s, q < G.flow.scalar t x →
      |derivWithin (fun v => G.flow.scalar v x) (_root_.Set.Iic t) t| ≤ C * G.flow.scalar t x ^ 2)
    {t u : ℝ} (ht : t ∈ _root_.Set.Ioo a s) (hu : u ∈ _root_.Set.Ioo a s)
    (hqQ : q ≤ Q) (hscalar : G.flow.scalar t x ≤ Q)
    (htime : 2 * C * |u - t| * Q ≤ 1) : G.flow.scalar u x ≤ 2 * Q := by
  have hQ : 0 < Q := hq.trans_le hqQ
  have hlipschitz := (G.lipschitzOnWith_inv_max_scalar_at hq x hbound).mono _root_.Set.Ioo_subset_Ico_self
  have hlip := hlipschitz.dist_le_mul u hu t ht
  rw [Real.dist_eq, Real.dist_eq] at hlip
  have htpos : 0 < _root_.Max.max q (G.flow.scalar t x) := hq.trans_le (le_max_left _ _)
  have hup : 0 < _root_.Max.max q (G.flow.scalar u x) := hq.trans_le (le_max_left _ _)
  have hinv : Q⁻¹ ≤ (_root_.Max.max q (G.flow.scalar t x))⁻¹ :=
    inv_anti₀ htpos (max_le hqQ hscalar)
  have hhalf : C * |u - t| ≤ (2 * Q)⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ (by positivity : 0 < 2 * Q)).mpr
    nlinarith
  have htwo : Q⁻¹ = 2 * (2 * Q)⁻¹ := by field_simp
  have hlow : (2 * Q)⁻¹ ≤ (_root_.Max.max q (G.flow.scalar u x))⁻¹ := by
    have hab := (abs_le.mp hlip).1
    rw [htwo] at hinv
    linarith
  have hupper : _root_.Max.max q (G.flow.scalar u x) ≤ 2 * Q :=
    (inv_le_inv₀ (by positivity : 0 < 2 * Q) hup).mp hlow
  exact (le_max_right _ _).trans hupper

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.scalar_le_two_mul_of_time_distance_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.scalar_le_two_mul_of_time_distance_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.scalar_le_two_mul_of_time_distance_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.scalar_le_two_mul_of_time_distance_le

theorem TerminalLimitMetric.scalar_le_two_mul_of_time_sub_le
    (L : G.TerminalLimitMetric) {q Q : ℝ} {C : ℝ≥0} (hq : 0 < q)
    (x : G.terminalRegularOpen)
    (hbound : ∀ t ∈ _root_.Set.Ioo a s, q < G.flow.scalar t x.val →
      |derivWithin (fun v => G.flow.scalar v x.val) (_root_.Set.Iic t) t| ≤
        C * G.flow.scalar t x.val ^ 2) {t : ℝ} (ht : t ∈ _root_.Set.Ioo a s)
    (hqQ : q ≤ Q) (hscalar : G.flow.scalar t x.val ≤ Q)
    (htime : 2 * C * (s - t) * Q ≤ 1) : metricScalarAt L.metric x ≤ 2 * Q := by
  have hQ : 0 < Q := hq.trans_le hqQ
  apply le_of_tendsto (L.tendsto_metricScalarAt x)
  filter_upwards [Ioo_mem_nhdsLT ht.2] with u hu
  have hsmall : 2 * C * |u - t| * Q ≤ 1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr hu.1.le)]
    apply le_trans _ htime
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (sub_le_sub_right hu.2.le t) (by positivity)) hQ.le
  exact G.scalar_le_two_mul_of_time_distance_le hq x.val hbound ht
    ⟨ht.1.trans hu.1, hu.2⟩ hqQ hscalar hsmall

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.scalar_le_two_mul_of_time_sub_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.scalar_le_two_mul_of_time_sub_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.scalar_le_two_mul_of_time_sub_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.scalar_le_two_mul_of_time_sub_le

theorem monotoneOn_max_scalar_of_deriv_nonneg
    (G : P.IncomingSlab a s) {q : ℝ} (x : P.Carrier)
    (hderiv : ∀ t ∈ _root_.Set.Ioo a s, q < G.flow.scalar t x →
      0 ≤ derivWithin (fun v => G.flow.scalar v x) (_root_.Set.Iic t) t) :
    MonotoneOn (fun t => _root_.Max.max q (G.flow.scalar t x)) (_root_.Set.Ico a s) := by
  apply DifferentialGeometry.Analysis.monotoneOn_max_of_deriv_nonneg_above _root_.Set.ordConnected_Ico
  · intro t ht
    exact (G.equation.scalarTime ht Subset.rfl x).continuousWithinAt
  · intro t ht hq
    rw [interior_Ico] at ht
    have hd : DifferentiableAt ℝ (fun v => G.flow.scalar v x) t :=
      (G.equation.scalarTime (K := _root_.Set.Ioo a s) ht _root_.Set.Ioo_subset_Ico_self x).differentiableAt
        (Ioo_mem_nhds ht.1 ht.2)
    exact ⟨hd, by simpa only [hd.derivWithin (uniqueDiffWithinAt_Iic t)] using hderiv t ht hq⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.monotoneOn_max_scalar_of_deriv_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.monotoneOn_max_scalar_of_deriv_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.monotoneOn_max_scalar_of_deriv_nonneg ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.monotoneOn_max_scalar_of_deriv_nonneg

theorem TerminalLimitMetric.max_scalar_le_terminal_of_deriv_nonneg
    {G : P.IncomingSlab a s} (L : G.TerminalLimitMetric) {q : ℝ} (x : G.terminalRegularOpen)
    (hderiv : ∀ t ∈ _root_.Set.Ioo a s, q < G.flow.scalar t x.val →
      0 ≤ derivWithin (fun v => G.flow.scalar v x.val) (_root_.Set.Iic t) t)
    {t : ℝ} (ht : t ∈ _root_.Set.Ico a s) :
    max q (G.flow.scalar t x.val) ≤ _root_.Max.max q (metricScalarAt L.metric x) := by
  apply ge_of_tendsto (tendsto_const_nhds.max (L.tendsto_metricScalarAt x))
  filter_upwards [Ioo_mem_nhdsLT ht.2] with v hv
  exact G.monotoneOn_max_scalar_of_deriv_nonneg x.val hderiv ht
    ⟨ht.1.trans hv.1.le, hv.2⟩ hv.1.le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.max_scalar_le_terminal_of_deriv_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.max_scalar_le_terminal_of_deriv_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.max_scalar_le_terminal_of_deriv_nonneg ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.max_scalar_le_terminal_of_deriv_nonneg

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
