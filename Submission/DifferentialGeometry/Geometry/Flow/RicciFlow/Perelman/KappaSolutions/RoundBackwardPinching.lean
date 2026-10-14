import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.RoundMetricPinching
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.RoundPinchingTransport
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.GlobalizedMetricConvergence
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BackwardSliceSequence
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientRicciPinching

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

universe u uE uH

private theorem continuousOn_timeSlice {P : Type*} [TopologicalSpace P]
    {f : ℝ → P → ℝ}
    (h : ContinuousOn (fun q : ℝ × P => f q.1 q.2) (_root_.Set.Iic 0 ×ˢ _root_.Set.univ)) (x : P) :
    ContinuousOn (fun t => f t x) (_root_.Set.Iic 0) := by
  have hmap : Continuous (fun t : ℝ => (t, x)) := continuous_id.prodMk continuous_const
  exact h.comp hmap.continuousOn (fun _ ht => ⟨ht, _root_.Set.mem_univ x⟩)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.continuousOn_timeSlice
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.continuousOn_timeSlice target :: scope.openDecls } }

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance roundBackwardTopology : TopologicalSpace F.M := F.topology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundBackwardTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundBackwardTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundBackwardTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundBackwardTopology
local instance roundBackwardCharted : ChartedSpace H F.M := F.charted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundBackwardCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundBackwardCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundBackwardCharted ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundBackwardCharted
local instance roundBackwardSmooth : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundBackwardSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundBackwardSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundBackwardSmooth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundBackwardSmooth
local instance roundBackwardC1 : IsManifold I 1 F.M := IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundBackwardC1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundBackwardC1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundBackwardC1 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundBackwardC1
local instance roundBackwardT2 : T2Space F.M := F.t2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundBackwardT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundBackwardT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundBackwardT2 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundBackwardT2
local instance roundBackwardSigma : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundBackwardSigma then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundBackwardSigma"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundBackwardSigma ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundBackwardSigma

variable {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}

local instance roundBackwardLimitTopology : TopologicalSpace L.M := L.topology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundBackwardLimitTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundBackwardLimitTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundBackwardLimitTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundBackwardLimitTopology
local instance roundBackwardLimitCharted : ChartedSpace H L.M := L.charted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundBackwardLimitCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundBackwardLimitCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundBackwardLimitCharted ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundBackwardLimitCharted
local instance roundBackwardLimitSmooth : IsManifold I ∞ L.M := L.smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundBackwardLimitSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundBackwardLimitSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundBackwardLimitSmooth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundBackwardLimitSmooth
local instance roundBackwardLimitC1 : IsManifold I 1 L.M := IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundBackwardLimitC1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundBackwardLimitC1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundBackwardLimitC1 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundBackwardLimitC1
local instance roundBackwardLimitT2 : T2Space L.M := L.t2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundBackwardLimitT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundBackwardLimitT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundBackwardLimitT2 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundBackwardLimitT2
local instance roundBackwardLimitSigma : SigmaCompactSpace L.M := L.sigmaCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundBackwardLimitSigma then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundBackwardLimitSigma"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundBackwardLimitSigma ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundBackwardLimitSigma


theorem exists_backward_ricci_pinching_of_round_limit
    (hdim : Module.finrank ℝ E = 3) (hconn : ConnectedSpace F.M)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (hescape : _root_.Filter.Tendsto tau _root_.Filter.atTop _root_.Filter.atTop)
    (q : ℕ → F.M) {phi : ℕ → ℕ} (hphi : StrictMono phi)
    (Phi : PointedRiemannianConvergenceMaps (I := I) (backwardSliceSequence F tau htau q) L phi)
    (C : MetricConvergenceData (I := I) Phi)
    (hcanonical : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Phi k)
    (hcompact : CompactSpace L.M) {R : ℝ} (hR : 0 < R)
    (hscalar : ∀ x : L.M, metricScalarAt L.metric x = R)
    (hEin : ∀ x : L.M, ∀ v : TangentSpace I x,
      ricciTensor L.metric x v v = (R / 3) * L.metric.inner x v v) :
    ∃ rho c : ℕ → ℝ, (∀ i, 0 < rho i) ∧ _root_.Filter.Tendsto rho _root_.Filter.atTop _root_.Filter.atTop ∧
      _root_.Filter.Tendsto c _root_.Filter.atTop (𝓝 (1 / 3)) ∧ (∀ i, c i < 1 / 3) ∧
      ∀ i, ∀ x : F.M, 0 < F.S.scalar (-rho i) x ∧ ∀ v : TangentSpace I x,
        c i * F.S.scalar (-rho i) x * (F.S.family.metric (-rho i)).inner x v v ≤
          F.S.ricciAt (-rho i) x (vec2 v v) := by
  classical
  let _ : CompactSpace L.M := hcompact
  have hconnected : ∀ k : ℕ,
      @ConnectedSpace ((backwardSliceSequence F tau htau q).obj (phi k)).M
        ((backwardSliceSequence F tau htau q).obj (phi k)).topology := fun _ => hconn
  obtain ⟨k0, e, _, hconv⟩ :=
    compactLimit_global_pullback_metric_convergence Phi C hcanonical hcompact hconnected
  let G : ℕ → SmoothRiemannianMetric I L.M := fun k => Diffeomorph.pullbackMetric
    ((backwardSliceSequence F tau htau q).obj (phi (k0 + k))).metric (e k)
  have hGconv : MetricCInfConvergenceOnCompacts G L.metric L.metric := hconv
  let c : ℕ → ℝ := fun i => 1 / 3 - (1 / 3) / ((i : ℝ) + 1)
  have hc0 (i : ℕ) : 0 ≤ c i := by
    have hdiv : (1 / 3 : ℝ) / ((i : ℝ) + 1) ≤ 1 / 3 := by
      apply (div_le_iff₀ (by positivity : 0 < (i : ℝ) + 1)).mpr
      nlinarith [Nat.cast_nonneg (α := ℝ) i]
    exact sub_nonneg.mpr hdiv
  have hcUpper (i : ℕ) : c i < 1 / 3 := by
    have hp : 0 < (1 / 3 : ℝ) / ((i : ℝ) + 1) := by positivity
    dsimp only [c]
    linarith
  have hplus : _root_.Filter.Tendsto (fun i : ℕ => (i : ℝ) + 1) _root_.Filter.atTop atTop :=
    tendsto_atTop_mono (fun i => by linarith) (tendsto_natCast_atTop_atTop (R := ℝ))
  have hc : _root_.Filter.Tendsto c _root_.Filter.atTop (𝓝 (1 / 3)) := by
    have hz := tendsto_inv_atTop_zero.comp hplus
    have h : _root_.Filter.Tendsto (fun i : ℕ => (1 / 3 : ℝ) - (1 / 3) * ((i : ℝ) + 1)⁻¹)
        atTop (𝓝 ((1 / 3 : ℝ) - (1 / 3) * 0)) :=
      tendsto_const_nhds.sub (tendsto_const_nhds.mul hz)
    simpa only [c, div_eq_mul_inv, _root_.MulZeroClass.mul_zero, sub_zero] using h
  choose kPinch hkPinch using fun i =>
    metric_ricci_pinching_eventually_of_round_convergence G L.metric hdim hR hscalar hEin hGconv
      (hc0 i) (hcUpper i)
  let j : ℕ → ℕ := fun i => _root_.Max.max (kPinch i) i
  have hj : _root_.Filter.Tendsto j _root_.Filter.atTop atTop := _root_.Filter.tendsto_atTop_mono (fun i => le_max_right _ _) _root_.Filter.tendsto_id
  have hshift : _root_.Filter.Tendsto (fun k : ℕ => k0 + k) _root_.Filter.atTop atTop := by
    simpa only [Nat.add_comm] using _root_.Filter.tendsto_add_atTop_nat k0
  let rho : ℕ → ℝ := fun i => tau (phi (k0 + j i))
  have hrho (i : ℕ) : 0 < rho i := htau _
  have hrhoEscape : _root_.Filter.Tendsto rho _root_.Filter.atTop atTop :=
    hescape.comp (hphi.tendsto_atTop.comp (hshift.comp hj))
  refine ⟨rho, c, hrho, hrhoEscape, hc, hcUpper, ?_⟩
  intro i
  have hg := hkPinch i (j i) (le_max_left _ _)
  have hpinch := (ricci_trace_pinching_pullback_iff
    ((backwardSliceSequence F tau htau q).obj (phi (k0 + j i))).metric (e (j i)) (c i)).mp
      (fun x v => (hg x).2 v)
  have hsource := (ricci_trace_pinching_scaleMetric_iff (F.S.family.metric (-rho i))
    (rho i)⁻¹ (inv_pos.mpr (hrho i)) (c i)).mp hpinch
  have hpositive := scalar_positive_of_pullback_scaleMetric (F.S.family.metric (-rho i))
    (e (j i)) (rho i)⁻¹ (inv_pos.mpr (hrho i)) (fun x => (hg x).1)
  intro x
  refine ⟨hpositive x, fun v => ?_⟩
  have h := hsource x v
  change c i * metricScalarAt (F.S.family.metric (-rho i)) x *
    (F.S.family.metric (-rho i)).inner x v v ≤
      metricRicciAt (F.S.family.metric (-rho i)) x (vec2 v v)
  rw [metricRicciAt_apply_eq_ricciTensor]
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_backward_ricci_pinching_of_round_limit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_backward_ricci_pinching_of_round_limit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_backward_ricci_pinching_of_round_limit ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_backward_ricci_pinching_of_round_limit


theorem ancient_constant_sectional_of_round_backward_convergence
    (hdim : Module.finrank ℝ E = 3) (hconn : ConnectedSpace F.M)
    (hcompactF : CompactSpace F.M)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (hescape : _root_.Filter.Tendsto tau _root_.Filter.atTop _root_.Filter.atTop)
    (q : ℕ → F.M) {phi : ℕ → ℕ} (hphi : StrictMono phi)
    (Phi : PointedRiemannianConvergenceMaps (I := I) (backwardSliceSequence F tau htau q) L phi)
    (C : MetricConvergenceData (I := I) Phi)
    (hcanonical : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Phi k)
    (hcompact : CompactSpace L.M) {R : ℝ} (hR : 0 < R)
    (hscalar : ∀ x : L.M, metricScalarAt L.metric x = R)
    (hEin : ∀ x : L.M, ∀ v : TangentSpace I x,
      ricciTensor L.metric x v v = (R / 3) * L.metric.inner x v v) :
    ∀ b : ℝ, b ≤ 0 → ∃ K : ℝ, ∀ x : F.M, ∀ X Y : TangentSpace I x,
      metricRm04StandardAt (F.S.family.metric b) x X Y Y X =
        K * ((F.S.family.metric b).inner x X X * (F.S.family.metric b).inner x Y Y -
          (F.S.family.metric b).inner x X Y * (F.S.family.metric b).inner x X Y) := by
  let _ : CompactSpace F.M := hcompactF
  let _ : ConnectedSpace F.M := hconn
  obtain ⟨rho, c, _, hrho, hc, hcUpper, hpinch⟩ :=
    exists_backward_ricci_pinching_of_round_limit F hdim hconn tau htau hescape q hphi Phi C
      hcanonical hcompact hR hscalar hEin
  have ha : _root_.Filter.Tendsto (fun i => -rho i) _root_.Filter.atTop atBot := tendsto_neg_atTop_atBot.comp hrho
  exact ancient_constant_sectional_of_backward_pinching F.S F.isSolution hdim ha hc hcUpper
    (fun i x v => (hpinch i x).2 v)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_constant_sectional_of_round_backward_convergence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_constant_sectional_of_round_backward_convergence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_constant_sectional_of_round_backward_convergence ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_constant_sectional_of_round_backward_convergence


theorem ancient_scalar_monotone_of_spatially_constant
    (hconstant : ∀ t : ℝ, t ≤ 0 → ∃ R : ℝ, ∀ x : F.M, F.S.scalar t x = R)
    (x : F.M) : MonotoneOn (fun t => F.S.scalar t x) (_root_.Set.Iic 0) := by
  have hcont : ContinuousOn (fun t => F.S.scalar t x) (_root_.Set.Iic 0) :=
    continuousOn_timeSlice (P := F.M) (f := F.S.scalar) F.isSolution.scalarCont x
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Iic 0) hcont
    (f' := fun t => 2 * normSq0S (F.S.family.metric t) x 2 (F.S.ricci t x))
  · intro t ht
    have ht' : t < 0 := by simpa only [interior_Iic, _root_.Set.mem_Iio] using ht
    have h := (smoothOfSolution F.S F.isSolution).scalarEvolution (flowG F.S)
      (fun _ => rfl) (fun _ => rfl) ⟨t, ht'⟩ x
    obtain ⟨R, hR⟩ := hconstant t ht'.le
    have hf : F.S.scalar t = fun _ => R := funext hR
    simp only [hf, laplacianAt, laplacian_const, zero_add] at h
    exact h.mono interior_subset
  · intro t _ht
    exact mul_nonneg (by norm_num) (normSq0S_nonneg _ _ _ _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_scalar_monotone_of_spatially_constant then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_scalar_monotone_of_spatially_constant"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_scalar_monotone_of_spatially_constant ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_scalar_monotone_of_spatially_constant


theorem ancient_positive_constant_sectional_of_round_backward_convergence
    (hdim : Module.finrank ℝ E = 3) (hconn : ConnectedSpace F.M)
    (hcompactF : CompactSpace F.M)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (hescape : _root_.Filter.Tendsto tau _root_.Filter.atTop _root_.Filter.atTop)
    (q : ℕ → F.M) {phi : ℕ → ℕ} (hphi : StrictMono phi)
    (Phi : PointedRiemannianConvergenceMaps (I := I) (backwardSliceSequence F tau htau q) L phi)
    (C : MetricConvergenceData (I := I) Phi)
    (hcanonical : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Phi k)
    (hcompact : CompactSpace L.M) {R : ℝ} (hR : 0 < R)
    (hscalar : ∀ x : L.M, metricScalarAt L.metric x = R)
    (hEin : ∀ x : L.M, ∀ v : TangentSpace I x,
      ricciTensor L.metric x v v = (R / 3) * L.metric.inner x v v) :
    ∀ b : ℝ, b ≤ 0 → ∃ K : ℝ, 0 < K ∧ ∀ x : F.M, ∀ X Y : TangentSpace I x,
      metricRm04StandardAt (F.S.family.metric b) x X Y Y X =
        K * ((F.S.family.metric b).inner x X X * (F.S.family.metric b).inner x Y Y -
          (F.S.family.metric b).inner x X Y * (F.S.family.metric b).inner x X Y) := by
  let _ : CompactSpace F.M := hcompactF
  let _ : ConnectedSpace F.M := hconn
  obtain ⟨rho, c, hrhoPos, hrho, hc, hcUpper, hpinch⟩ :=
    exists_backward_ricci_pinching_of_round_limit F hdim hconn tau htau hescape q hphi Phi C
      hcanonical hcompact hR hscalar hEin
  have ha : _root_.Filter.Tendsto (fun i => -rho i) _root_.Filter.atTop atBot := tendsto_neg_atTop_atBot.comp hrho
  have hinitial := fun i x v => (hpinch i x).2 v
  have hconstant := ancient_scalar_constant_of_backward_pinching F.S F.isSolution hdim
    ha hc hcUpper hinitial
  have hpositive (b : ℝ) (hb : b ≤ 0) (x : F.M) : 0 < F.S.scalar b x := by
    obtain ⟨i, hi⟩ := (hrho.eventually (_root_.Filter.eventually_ge_atTop (-b))).exists
    have hab : -rho i ≤ b := by linarith
    have hm := ancient_scalar_monotone_of_spatially_constant F hconstant x
      (neg_nonpos.mpr (hrhoPos i).le) hb hab
    exact (hpinch i x).1.trans_le hm
  intro b hb
  obtain ⟨Rb, hRb⟩ := hconstant b hb
  have hRbPos : 0 < Rb := by
    rw [← hRb F.basepoint]
    exact hpositive b hb F.basepoint
  have hEinSlice := ancient_ricci_einstein_of_backward_pinching F.S F.isSolution hdim
    ha hc hcUpper hinitial b hb
  refine ⟨Rb / 6, div_pos hRbPos (by norm_num), fun x X Y => ?_⟩
  let g := F.S.family.metric b
  obtain ⟨basis, _l1, _l2, _l3, horth, _hdiag⟩ :=
    ricciEigen3 g (F.S.ricciAt b x) hdim (ricci_is_symmetric F.S b x)
  have htrace := riemann_from_ricci_trace F.S (t := b) (x := x) (basis := basis) horth
  have hneg (i j : Fin 3) : ricciCompAt basis (-(F.S.ricciAt b x)) i j =
      ((-F.S.scalar b x) / 3) * delta3 i j := by
    rw [ricciCompAt_apply]
    change -(F.S.ricciAt b x (vec2 (basis i) (basis j))) = _
    rw [hEinSlice x (basis i) (basis j)]
    change -((F.S.scalar b x / 3) * g.inner x (basis i) (basis j)) = _
    rw [horth i j]
    ring
  have hRm := rm04_einstein3_at htrace hneg X Y
  calc
    _ = -((-F.S.scalar b x) / 6) *
        (g.inner x X X * g.inner x Y Y - g.inner x X Y * g.inner x X Y) := hRm
    _ = _ := by rw [hRb x]; ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_positive_constant_sectional_of_round_backward_convergence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_positive_constant_sectional_of_round_backward_convergence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_positive_constant_sectional_of_round_backward_convergence ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_positive_constant_sectional_of_round_backward_convergence

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
