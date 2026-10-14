import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.HighCurvatureModels
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NormalizedRescaling
import Batteries.Tactic.OpenPrivate

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Filter _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.E3 target :: scope.openDecls } }

open private standard_late_slab_spatial_noncollapse nonempty_standard_tangent_orientation
  PartialStandardSolution.phiAlmostNonnegative from
  Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.HighCurvatureModels

private theorem standard_parabolic_window (S : PartialStandardSolution) {t B : ℝ}
    (ht : t ∈ S.domain) (hB : 0 < B) (htlate : 3 / 4 ≤ t) :
    _root_.Set.Icc (-(B / 2)) 0 ⊆ (parabolicInterval (lifetimeInterval S.lifetime S.lifetime_pos) t B ht).carrier ∧
    Ioo (-(B / 2)) 0 ⊆ (parabolicInterval (lifetimeInterval S.lifetime S.lifetime_pos) t B ht).regular := by
  have hdom (s : ℝ) (hs : s ∈ _root_.Set.Icc (-(B / 2)) 0) :
      0 < t + s / B ∧ ENNReal.ofReal (t + s / B) < S.lifetime := by
    have hslo : -(1 / 2 : ℝ) ≤ s / B := (le_div_iff₀ hB).mpr (by linarith [hs.1])
    have hshi : s / B ≤ 0 := div_nonpos_of_nonpos_of_nonneg hs.2 hB.le
    exact ⟨by linarith, (ENNReal.ofReal_le_ofReal (by linarith)).trans_lt
      ((mem_lifetimeInterval_carrier S.lifetime S.lifetime_pos t).mp ht).2⟩
  exact ⟨fun s hs => (mem_lifetimeInterval_carrier S.lifetime S.lifetime_pos _).mpr
    ⟨(hdom s hs).1.le, (hdom s hs).2⟩,
    fun s hs => (mem_lifetimeInterval_regular S.lifetime S.lifetime_pos _).mpr
      (hdom s ⟨hs.1.le, hs.2.le⟩)⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.standard_parabolic_window
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.standard_parabolic_window target :: scope.openDecls } }

private def standardNormalizedSource (S : PartialStandardSolution) (t B : ℝ)
    (ht : t ∈ S.domain) (hB : 0 < B) (htlate : 3 / 4 ≤ t) (p : E3) :
    PointedFlowData (𝓡 3) (RealTimeInterval.closed (-(B / 2)) 0 (by linarith)) := {
  M := E3
  basepoint := p
  S := (parabolicSolution S.toSolutionOn t B hB ht).timeRestrict
    (RealTimeInterval.closed (-(B / 2)) 0 (by linarith))
  isSolution := isSolutionOn_timeRestrict
    (parabolicSolution_isSolutionOn S.toSolutionOn S.isSolutionOn t B hB ht)
    (standard_parabolic_window S ht hB htlate).1 (standard_parabolic_window S ht hB htlate).2 }

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.standardNormalizedSource
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.standardNormalizedSource target :: scope.openDecls } }

def standardParabolicSequence (B : ℝ) (hB : 0 < B)
    (S : ℕ → PartialStandardSolution) (time : ℕ → ℝ) (point : ℕ → E3)
    (htime : ∀ i, time i ∈ (S i).domain ∧ 3 / 4 ≤ time i ∧ time i < 1) : FlowSequence := {
  interval i := RealTimeInterval.closed (-(B / 2)) 0 (by linarith)
  term i := standardNormalizedSource (S i) (time i) B (htime i).1 hB (htime i).2.1 (point i) }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.standardParabolicSequence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.standardParabolicSequence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.standardParabolicSequence ``Submission.DifferentialGeometry.PDE.RicciFlow.standardParabolicSequence

@[simp] theorem standardParabolicSequence_basepoint (B : ℝ) (hB : 0 < B)
    (S : ℕ → PartialStandardSolution) (time : ℕ → ℝ) (point : ℕ → E3)
    (htime : ∀ i, time i ∈ (S i).domain ∧ 3 / 4 ≤ time i ∧ time i < 1) (i : ℕ) :
    ((standardParabolicSequence B hB S time point htime).term i).basepoint = point i := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.standardParabolicSequence_basepoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.standardParabolicSequence_basepoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.standardParabolicSequence_basepoint ``Submission.DifferentialGeometry.PDE.RicciFlow.standardParabolicSequence_basepoint

@[simp] theorem standardParabolicSequence_metric (B : ℝ) (hB : 0 < B)
    (S : ℕ → PartialStandardSolution) (time : ℕ → ℝ) (point : ℕ → E3)
    (htime : ∀ i, time i ∈ (S i).domain ∧ 3 / 4 ≤ time i ∧ time i < 1) (i : ℕ) (s : ℝ) :
    ((standardParabolicSequence B hB S time point htime).term i).S.base.metric s =
      scaleMetric B hB ((S i).metric (time i + s / B)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.standardParabolicSequence_metric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.standardParabolicSequence_metric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.standardParabolicSequence_metric ``Submission.DifferentialGeometry.PDE.RicciFlow.standardParabolicSequence_metric

@[simp] theorem standardParabolicSequence_carrier (B : ℝ) (hB : 0 < B)
    (S : ℕ → PartialStandardSolution) (time : ℕ → ℝ) (point : ℕ → E3)
    (htime : ∀ i, time i ∈ (S i).domain ∧ 3 / 4 ≤ time i ∧ time i < 1) (i : ℕ) :
    ((standardParabolicSequence B hB S time point htime).interval i).carrier =
      Icc (-(B / 2)) 0 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.standardParabolicSequence_carrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.standardParabolicSequence_carrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.standardParabolicSequence_carrier ``Submission.DifferentialGeometry.PDE.RicciFlow.standardParabolicSequence_carrier

@[simp] theorem standardParabolicSequence_regular (B : ℝ) (hB : 0 < B)
    (S : ℕ → PartialStandardSolution) (time : ℕ → ℝ) (point : ℕ → E3)
    (htime : ∀ i, time i ∈ (S i).domain ∧ 3 / 4 ≤ time i ∧ time i < 1) (i : ℕ) :
    ((standardParabolicSequence B hB S time point htime).interval i).regular =
      Ioo (-(B / 2)) 0 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.standardParabolicSequence_regular then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.standardParabolicSequence_regular"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.standardParabolicSequence_regular ``Submission.DifferentialGeometry.PDE.RicciFlow.standardParabolicSequence_regular

@[simp] theorem standardParabolicSequence_scalar (B : ℝ) (hB : 0 < B)
    (S : ℕ → PartialStandardSolution) (time : ℕ → ℝ) (point : ℕ → E3)
    (htime : ∀ i, time i ∈ (S i).domain ∧ 3 / 4 ≤ time i ∧ time i < 1) (i : ℕ) (s : ℝ) (x : E3) :
    ((standardParabolicSequence B hB S time point htime).term i).S.scalar s x =
      B⁻¹ * metricScalarAt ((S i).metric (time i + s / B)) x := by
  change (parabolicSolution (S i).toSolutionOn (time i) B hB (htime i).1).scalar s x = _
  rw [parabolicSolution_scalar]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.standardParabolicSequence_scalar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.standardParabolicSequence_scalar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.standardParabolicSequence_scalar ``Submission.DifferentialGeometry.PDE.RicciFlow.standardParabolicSequence_scalar

theorem exists_standard_parabolic_sequence_model_threshold
    {eps : ℝ} (heps : 0 < eps) (heps1 : eps < 1) :
    ∃ B₀ : ℝ, 0 < B₀ ∧ ∀ B : ℝ, B₀ ≤ B →
      ∀ (S : ℕ → PartialStandardSolution) (time : ℕ → ℝ) (point : ℕ → E3),
        ∀ htime : (∀ i, time i ∈ (S i).domain ∧ 3 / 4 ≤ time i ∧ time i < 1),
        (∀ i, metricScalarAt ((S i).metric (time i)) (point i) = B) →
        ∃ hB : 0 < B,
          let X := standardParabolicSequence B hB S time point htime
          (∀ i, (X.interval i).carrier = _root_.Set.Icc (-(B / 2)) 0) ∧
          (∀ i, (X.interval i).regular = _root_.Set.Ioo (-(B / 2)) 0) ∧
          (∀ i, ConnectedSpace (X.term i).M) ∧
          (∀ i t, t ∈ (X.interval i).carrier → MetricComplete ((X.term i).atTime t)) ∧
          (∀ i, ∃ C : ℝ, PointedFlowRmNormSqBounded (X.term i) C) ∧
          (∀ i, PointedFlowScalarAtBase (X.term i) 1) ∧
          (∀ i, SpatiallyKappaNoncollapsedBelowScale (X.term i).S
            (standardParabolicNoncollapseCoeff / 1000000) (Real.sqrt B * Real.sqrt 1250)) ∧
          (∀ i, PhiAlmostNonnegative (X.term i).S (X.interval i).carrier
            (rescalePinchingFunction B (fun _ => 1))) ∧
          ∃ orientation : ∀ i, Surgery.Topology.TangentOrientationSection (X.term i).M,
            ∀ i s, s ∈ _root_.Set.Icc (-(B / 4)) 0 → ∀ x,
              2 ≤ (X.term i).S.scalar s x →
                OrientedWitness (X.term i).S (orientation i) eps standardModelKappa x s := by
  obtain ⟨Q₀, hQ₀, hmodel⟩ := exists_standard_high_scalar_model_threshold heps heps1
    (by norm_num : (0 : ℝ) < 1 / 2)
  let B₀ := _root_.Max.max Q₀ (2 / eps) + 1
  have hB₀ : 0 < B₀ := hQ₀.trans_le ((le_max_left _ _).trans (le_add_of_nonneg_right zero_le_one))
  refine ⟨B₀, hB₀, ?_⟩
  intro B hB₀B S time point htime hpoint
  have hB : 0 < B := hB₀.trans_le hB₀B
  have hQB : Q₀ ≤ B := ((le_max_left _ _).trans (le_add_of_nonneg_right zero_le_one)).trans hB₀B
  have heB : 2 / eps ≤ B := ((le_max_right _ _).trans (le_add_of_nonneg_right zero_le_one)).trans hB₀B
  let X := standardParabolicSequence B hB S time point htime
  have hdom (i : ℕ) (s : ℝ) (hs : s ∈ _root_.Set.Icc (-(B / 2)) 0) :
      time i + s / B ∈ (S i).domain :=
    (standard_parabolic_window (S i) (htime i).1 hB (htime i).2.1).1 hs
  obtain ⟨o⟩ := nonempty_standard_tangent_orientation
  refine ⟨hB, fun _ => rfl, fun _ => rfl, ?_, ?_, ?_, ?_, ?_, ?_, (fun _ => o), ?_⟩
  · intro i
    change ConnectedSpace E3
    infer_instance
  · intro i s hs
    exact ((S i).complete _ (hdom i s hs)).scaleMetric B hB |>.complete
  · intro i
    obtain ⟨K, _, hK⟩ := (S i).curvature_bound (time i)
      ((mem_lifetimeInterval_carrier (S i).lifetime (S i).lifetime_pos _).mp (htime i).1).1
      ((mem_lifetimeInterval_carrier (S i).lifetime (S i).lifetime_pos _).mp (htime i).1).2
    refine ⟨B⁻¹ ^ 2 * K ^ 2, ?_⟩
    intro s hs x
    have hsdom := hdom i s hs
    have hold := hK (time i + s / B)
      ⟨((mem_lifetimeInterval_carrier (S i).lifetime (S i).lifetime_pos _).mp hsdom).1,
        by have hh := div_nonpos_of_nonpos_of_nonneg hs.2 hB.le; linarith⟩ x
    have heq := parabolicRmNormSq (S i).toSolutionOn (time i) B hB (htime i).1 s x
    exact heq.le.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_iff.mp hold).2 (sq_nonneg B⁻¹))
  · intro i
    change (parabolicSolution (S i).toSolutionOn (time i) B hB (htime i).1).scalar 0 (point i) = 1
    rw [parabolicSolution_scalar]
    change B⁻¹ * metricScalarAt ((S i).metric (time i + 0 / B)) (point i) = 1
    rw [zero_div, add_zero, hpoint i, inv_mul_cancel₀ hB.ne']
  · intro i
    let D := RealTimeInterval.closed ((time i) - 1 / 2) (time i) (by linarith)
    have ha : 0 < time i - 1 / 2 := by linarith [(htime i).2.1]
    have hn := standard_late_slab_spatial_noncollapse (S i) ha
      (by linarith : time i - 1 / 2 ≤ time i) (htime i).1 (htime i).2.2
    have hn' := parabolic_spatial_noncollapse ((S i).toSolutionOn.timeRestrict D)
      (time i) B hB ⟨by linarith, le_rfl⟩
      (standardParabolicNoncollapseCoeff / 1000000) (Real.sqrt (5000 * (time i - 1 / 2))) hn
    refine ⟨mul_pos (Real.sqrt_pos.mpr hB) (Real.sqrt_pos.mpr (by norm_num)), ?_⟩
    intro s ball hr
    have hs : time i + (s : ℝ) / B ∈ D.carrier := by
      change time i - 1 / 2 ≤ time i + (s : ℝ) / B ∧ time i + (s : ℝ) / B ≤ time i
      constructor
      · have hh := (le_div_iff₀ hB).mpr (show -(1 / 2 : ℝ) * B ≤ (s : ℝ) by linarith [s.property.1]); linarith
      · have hh := div_nonpos_of_nonpos_of_nonneg s.property.2 hB.le; linarith
    exact hn'.2 ⟨s, hs⟩ ⟨ball.center, ball.radius, ball.radius_pos⟩
      (hr.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith [(htime i).2.1]))
        (Real.sqrt_nonneg B)))
  · intro i s hs x
    have hp := PartialStandardSolution.phiAlmostNonnegative (S i) (Phi := fun _ => 1) (fun _ => zero_le_one)
    have hh := phiAlmostNonnegative_paraSolution (S i).toSolutionOn hB (htime i).1 hp
    exact hh s (hdom i s hs) x
  · intro i s hs x hx
    have hsfull : s ∈ _root_.Set.Icc (-(B / 2)) 0 := ⟨by linarith [hs.1], hs.2⟩
    have hst : 1 / 2 ≤ time i + s / B := by
      have h := (le_div_iff₀ hB).mpr (show -(1 / 4 : ℝ) * B ≤ s by linarith [hs.1])
      linarith [(htime i).2.1]
    have hst1 : time i + s / B < 1 := by
      have h := div_nonpos_of_nonpos_of_nonneg hs.2 hB.le
      linarith [(htime i).2.2]
    have hscalar : (X.term i).S.scalar s x = B⁻¹ * metricScalarAt ((S i).metric (time i + s / B)) x := by
      change (parabolicSolution (S i).toSolutionOn (time i) B hB (htime i).1).scalar s x = _
      rw [parabolicSolution_scalar]
      rfl
    have hhigh : Q₀ ≤ metricScalarAt ((S i).metric (time i + s / B)) x := by
      rw [hscalar, ← div_eq_inv_mul, le_div_iff₀ hB] at hx
      linarith
    have hw := hmodel (S i) o x (time i + s / B) (hdom i s hsfull) hst hst1 hhigh
    have hp := (orientedWitness_paraSolution_iff (S i).toSolutionOn o hB (htime i).1
      s x eps standardModelKappa).mpr hw
    apply orientedWitness_timeRestrict (RealTimeInterval.closed (-(B / 2)) 0 (by linarith)) hsfull ?_ hp
    intro u hu
    have hsc : 0 < (X.term i).S.scalar s x := lt_of_lt_of_le (by norm_num) hx
    have hinv : (eps * (X.term i).S.scalar s x)⁻¹ ≤ B / 4 := by
      have hprod : 2 ≤ eps * B := by simpa [mul_comm] using (div_le_iff₀ heps).mp heB
      have heQ : 0 < eps * (X.term i).S.scalar s x := mul_pos heps hsc
      rw [inv_eq_one_div]
      apply (div_le_iff₀ heQ).mpr
      nlinarith
    change -(B / 2) ≤ u ∧ u ≤ 0
    exact ⟨by
      have hlo : s - (eps * (X.term i).S.scalar s x)⁻¹ ≤ u := hu.1
      linarith [hs.1], hu.2.trans hs.2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.exists_standard_parabolic_sequence_model_threshold then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.exists_standard_parabolic_sequence_model_threshold"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.exists_standard_parabolic_sequence_model_threshold ``Submission.DifferentialGeometry.PDE.RicciFlow.exists_standard_parabolic_sequence_model_threshold

end DifferentialGeometry.PDE.RicciFlow
