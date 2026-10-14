import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventData
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.Derivatives.TerminalFromJets
import Submission.DifferentialGeometry.Geometry.Metric.Distance.Ball
import Submission.DifferentialGeometry.Geometry.Comparison.Distance.Continuity
import Mathlib.Tactic.FieldSimp

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
  (shi_local_curvDerivNorm_terminal_of_solution_jets)
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage

universe u
variable {P : OrientedThreeStage.{u}}

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.instIsManifoldRealThreeSpaceThreeModelOfNatWithTopENatCarrier : IsManifold ThreeModel 1 P.Carrier :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.instIsManifoldRealThreeSpaceThreeModelOfNatWithTopENatCarrier
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.instIsManifoldRealThreeSpaceThreeModelOfNatWithTopENatCarrier target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.instIsManifoldRealThreeSpaceThreeModelOfNatWithTopENatCarrier_1 : IsManifold ThreeModel 2 P.Carrier :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.instIsManifoldRealThreeSpaceThreeModelOfNatWithTopENatCarrier_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.instIsManifoldRealThreeSpaceThreeModelOfNatWithTopENatCarrier_1 target :: scope.openDecls } }

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem exists_riemannianClosedBall_subset_open
    (g : P.Metric) {O : Set P.Carrier} (hO : IsOpen O) {x : P.Carrier} (hx : x ∈ O) :
    ∃ r : ℝ, 0 < r ∧ riemannianClosedBallOf g x r ⊆ O := by
  let _ : _root_.Bundle.RiemannianBundle (fun y : P.Carrier => TangentSpace ThreeModel y) :=
    ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle ThreeSpace
      (fun y : P.Carrier => TangentSpace ThreeModel y) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let _ : PseudoEMetricSpace P.Carrier :=
    PseudoEMetricSpace.ofRiemannianMetric ThreeModel P.Carrier
  obtain ⟨ε, hε, hball⟩ := EMetric.mem_nhds_iff.mp (hO.mem_nhds hx)
  obtain ⟨r, -, hr, hrε⟩ := ENNReal.lt_iff_exists_real_btwn.mp hε
  refine ⟨r, ENNReal.ofReal_pos.mp hr, ?_⟩
  intro y hy
  apply hball
  change _root_.EDist.edist y x < ε
  rw [_root_.PseudoEMetricSpace.edist_comm]
  exact hy.trans_lt hrε

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.exists_riemannianClosedBall_subset_open
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.exists_riemannianClosedBall_subset_open target :: scope.openDecls } }

theorem IncomingSlab.exists_curvature_derivative_bounds_of_mem_terminalRegularRegion
    {a s : ℝ} (G : P.IncomingSlab a s) {x : P.Carrier}
    (hx : x ∈ G.terminalRegularRegion) :
    ∃ (U : Set P.Carrier) (c : ℝ) (C : ℕ → ℝ),
      IsOpen U ∧ x ∈ U ∧ IsCompact (closure U) ∧ closure U ⊆ G.terminalRegularRegion ∧
      c ∈ _root_.Set.Ico a s ∧ (∀ m, 0 ≤ C m) ∧
      ∀ m : ℕ, ∀ t ∈ _root_.Set.Ico c s, ∀ y ∈ U,
        curvDerivNorm m (G.flow.base.metric t) y ≤ C m := by
  obtain ⟨O, hO, hxO, t₀, ht₀, K, hK, hcurv⟩ := hx
  obtain ⟨t₁, ht₀₁, ht₁s⟩ := exists_between ht₀.2
  obtain ⟨c, ht₁c, hcs⟩ := exists_between ht₁s
  have hat₁ : a < t₁ := ht₀.1.trans_lt ht₀₁
  have htc : 0 < c - t₁ := sub_pos.mpr ht₁c
  obtain ⟨r, hr, hballO⟩ :=
    exists_riemannianClosedBall_subset_open (G.flow.base.metric t₁) hO hxO
  let K₁ : ℝ := K + 1
  have hK₁ : 0 < K₁ := by dsimp [K₁]; linarith
  let R : ℝ := r * Real.sqrt K₁
  have hR : 0 < R := mul_pos hr (Real.sqrt_pos.mpr hK₁)
  have hrad : R / Real.sqrt K₁ = r :=
    mul_div_cancel_right₀ r (Real.sqrt_pos.mpr hK₁).ne'
  have hhalf : R / (2 * Real.sqrt K₁) = r / 2 := by
    dsimp [R]
    field_simp [(Real.sqrt_pos.mpr hK₁).ne']
  let U : Set P.Carrier := riemannianBallOf (G.flow.base.metric t₁) x (r / 2)
  have hU : IsOpen U :=
    isOpen_lt (continuous_riemannianEDist (G.flow.base.metric t₁) x) continuous_const
  have hxU : x ∈ U := by
    change riemannianEDistOf (G.flow.base.metric t₁) x x < ENNReal.ofReal (r / 2)
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr (half_pos hr)
  have hclosureball : closure U ⊆
      riemannianClosedBallOf (G.flow.base.metric t₁) x r := by
    apply closure_minimal
    · intro y hy
      exact hy.le.trans (ENNReal.ofReal_le_ofReal (by linarith))
    · exact isClosed_le (continuous_riemannianEDist (G.flow.base.metric t₁) x) continuous_const
  have hclosureO : closure U ⊆ O := hclosureball.trans hballO
  let C : ℕ → ℝ := fun m =>
    shiLocalUniformBound (Module.finrank ℝ ThreeSpace) m (K₁ * (s - t₁)) R * K₁ /
      Real.sqrt (c - t₁) ^ m
  refine ⟨U, c, C, hU, hxU, isClosed_closure.isCompact, ?_,
    ⟨hat₁.le.trans ht₁c.le, hcs⟩, ?_, ?_⟩
  · intro y hy
    exact ⟨O, hO, hclosureO hy, t₀, ht₀, K, hK, hcurv⟩
  · intro m
    exact div_nonneg
      (mul_nonneg (shiLocalUniformBound_nonneg _ _ _ _) hK₁.le)
      (pow_nonneg (Real.sqrt_nonneg _) _)
  · intro m t ht y hy
    have ht₁t : t₁ < t := ht₁c.trans_le ht.1
    have hcarrier : _root_.Set.Icc t₁ t ⊆ (RealTimeInterval.closedOpen a s G.lt).carrier := by
      intro u hu
      exact ⟨hat₁.le.trans hu.1, hu.2.trans_lt ht.2⟩
    have hregular : _root_.Set.Ico t₁ t ⊆ (RealTimeInterval.closedOpen a s G.lt).regular := by
      intro u hu
      exact ⟨hat₁.trans_le hu.1, hu.2.trans ht.2⟩
    have hball : IsCompact {z : P.Carrier |
        riemannianEDistOf (G.flow.base.metric t₁) x z ≤
          ENNReal.ofReal (R / Real.sqrt K₁)} :=
      (isClosed_le (continuous_riemannianEDist (G.flow.base.metric t₁) x)
        continuous_const).isCompact
    have hcurvSq : ∀ u ∈ _root_.Set.Icc t₁ t, ∀ z : P.Carrier,
        riemannianEDistOf (G.flow.base.metric t₁) x z ≤
          ENNReal.ofReal (R / Real.sqrt K₁) →
        curvDerivNormSq 0 (G.flow.base.metric u) z ≤ K₁ ^ 2 := by
      intro u hu z hz
      rw [hrad] at hz
      have hzO : z ∈ O := hballO hz
      have hu' : u ∈ _root_.Set.Ico t₀ s := ⟨ht₀₁.le.trans hu.1, hu.2.trans_lt ht.2⟩
      have hroot : Real.sqrt (curvDerivNormSq 0 (G.flow.base.metric u) z) ≤ K₁ := by
        change G.riemannNorm u z ≤ K₁
        exact (hcurv z hzO u hu').trans (by dsimp [K₁]; linarith)
      exact (Real.sqrt_le_iff.mp hroot).2
    have hyhalf : riemannianEDistOf (G.flow.base.metric t₁) x y ≤
        ENNReal.ofReal (R / (2 * Real.sqrt K₁)) := by
      rw [hhalf]
      exact hy.le
    have hshi := shi_local_curvDerivNorm_terminal_of_solution_jets G.flow G.equation
      (by simp [ThreeSpace] : 2 ≤ Module.finrank ℝ ThreeSpace)
      ht₁t hK₁ hR hcarrier hregular x hball hcurvSq m t ⟨ht₁t, le_rfl⟩ y hyhalf
    apply hshi.trans
    change _ ≤ shiLocalUniformBound (Module.finrank ℝ ThreeSpace) m
      (K₁ * (s - t₁)) R * K₁ / Real.sqrt (c - t₁) ^ m
    have hnum := mul_le_mul_of_nonneg_right
      (shiLocalUniformBound_mono (Module.finrank ℝ ThreeSpace) m hR
        (mul_nonneg hK₁.le (sub_pos.mpr ht₁t).le)
        (mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2.le t₁) hK₁.le)) hK₁.le
    apply (div_le_div_of_nonneg_right hnum
      (pow_nonneg (Real.sqrt_nonneg _) m)).trans
    apply div_le_div_of_nonneg_left
      (mul_nonneg (shiLocalUniformBound_nonneg _ _ _ _) hK₁.le)
      (pow_pos (Real.sqrt_pos.mpr htc) m)
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _)
      (Real.sqrt_le_sqrt (sub_le_sub_right ht.1 t₁)) m

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.exists_curvature_derivative_bounds_of_mem_terminalRegularRegion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.exists_curvature_derivative_bounds_of_mem_terminalRegularRegion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.exists_curvature_derivative_bounds_of_mem_terminalRegularRegion ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.exists_curvature_derivative_bounds_of_mem_terminalRegularRegion

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage
