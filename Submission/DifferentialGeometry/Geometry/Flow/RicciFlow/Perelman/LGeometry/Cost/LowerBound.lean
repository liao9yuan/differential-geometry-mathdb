import Submission.DifferentialGeometry.Analysis.Integration.Integral.Comparison
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Coercivity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Approximation
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Continuity.CarrierBaseTime
import Submission.DifferentialGeometry.Geometry.Metric.CurveEnergy

import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Integrability
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Estimates.Curvature

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open _root_.Bundle _root_.Submission.Bundle _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.Submission.Topology

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
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

private def actionRmFactor (E : Type uE) [NormedAddCommGroup E]
    [NormedSpace Real E] (K : Real) : Real :=
  (Module.finrank Real E : Real) ^ 2 * Real.sqrt K

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.actionRmFactor
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.actionRmFactor target :: scope.openDecls } }

omit [NeZero (Module.finrank Real E)] [T2Space M]
  [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
private theorem regularitySpeed_int_c1
    (S : SolutionOn (I := I) (M := M) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := M) S)
    (T a b : Real) (hab : a ≤ b) (alpha : Real → M)
    (halpha : ContMDiffOn (modelWithCornersSelf Real Real) I 1 alpha (_root_.Set.Icc a b))
    (hreg : ∀ s ∈ _root_.Set.Icc a b, T - s ^ 2 ∈ D.regular) :
    IntervalIntegrable (lRegularizedSpeedSq S T alpha) _root_.MeasureTheory.MeasureSpace.volume a b := by
  have hLag := intervalIntegrable_lRegularizedLagrangian_of_contMDiffOn_one (I := I) S hMet hSc T a b hab alpha halpha hreg
  have hcarrier : ∀ s ∈ _root_.Set.uIcc a b, T - s ^ 2 ∈ D.carrier := by
    intro s hs
    exact D.regular_subset (hreg s (by simpa only [_root_.Set.uIcc_of_le hab] using hs))
  have hpot : IntervalIntegrable
      (fun s ↦ 2 * s ^ 2 * S.scalar (T - s ^ 2) (alpha s)) _root_.MeasureTheory.MeasureSpace.volume a b :=
    lScalar_int (I := I) S hSc T a b alpha hcarrier (by
      simpa only [_root_.Set.uIcc_of_le hab] using halpha.continuousOn)
  have hhalf : IntervalIntegrable
      (fun s ↦ (1 / 2 : Real) * lRegularizedSpeedSq S T alpha s) _root_.MeasureTheory.MeasureSpace.volume a b := by
    convert hLag.sub hpot using 1
    funext s
    unfold lRegularizedLagrangian lRegularizedSpeedSq
    ring
  have htwice := hhalf.const_mul 2
  convert htwice using 1
  funext s
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.regularitySpeed_int_c1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.regularitySpeed_int_c1 target :: scope.openDecls } }

omit [NeZero (Module.finrank Real E)] [T2Space (TangentBundle I M)] in
omit [SigmaCompactSpace M] in
theorem lRegularizedCosts_bdd_rm
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (K T a b : Real) (ha : 0 ≤ a) (hab : a ≤ b)
    (hreg : _root_.Set.Icc (T - b ^ 2) T ⊆ D.regular)
    (hRm : ∀ q ∈ _root_.Set.Icc (T - b ^ 2) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric q) z 4 (S.base.rm04 q z) ≤ K)
    (x y : M) :
    BddBelow {r : Real | ∃ alpha : Real → M,
      ContMDiff (modelWithCornersSelf Real Real) I 1 alpha ∧
        alpha a = x ∧ alpha b = y ∧ lRegularizedAction S T alpha a b = r} := by
  let C : Real := -2 * b ^ 2 * actionRmFactor E K
  have hb : 0 ≤ b := ha.trans hab
  have hregBack : ∀ s ∈ _root_.Set.Icc a b, T - s ^ 2 ∈ D.regular := by
    intro s hs
    apply hreg
    have hs2 : s ^ 2 ≤ b ^ 2 := (sq_le_sq₀ (ha.trans hs.1) hb).2 hs.2
    constructor <;> linarith [sq_nonneg s]
  refine ⟨C * (b - a), ?_⟩
  intro r hr
  obtain ⟨alpha, halpha, _hstart, _hend, rfl⟩ := hr
  have hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric :=
    hS.smoothMetric
  have hSc : ScalarSTContOn (I := I) (M := M) S := ⟨hS.scalarCont⟩
  have hkin := regularitySpeed_int_c1 (I := I) S hMet hSc T a b hab alpha
    halpha.contMDiffOn hregBack
  have hLag := intervalIntegrable_lRegularizedLagrangian_of_contMDiffOn_one (I := I) S hMet hSc T a b hab alpha
    halpha.contMDiffOn hregBack
  have hbound := lRegularizedKinetic_le (I := I) S T alpha a b
    (lRegularizedAction S T alpha a b) C hab
    (fun s hs ↦ lRegularizedPot_lower_rm (I := I) S K T b hb hRm s
      ⟨ha.trans hs.1, hs.2⟩ (alpha s))
    hkin hLag le_rfl
  have hnonneg : 0 ≤ ∫ s in a..b, lRegularizedSpeedSq S T alpha s := by
    apply intervalIntegral.integral_nonneg hab
    intro s _hs
    exact lRegularizedSpeedSq_nonneg (I := I) S T alpha s
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedCosts_bdd_rm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedCosts_bdd_rm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedCosts_bdd_rm ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedCosts_bdd_rm

end DifferentialGeometry.PDE.RicciFlow.Perelman

noncomputable section

open _root_.Set _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [PseudoMetricSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [PreconnectedSpace M]
  {D : RealTimeInterval}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [PreconnectedSpace M] in
theorem lRegularizedAction_ge_riemannianEDistOf_sq_div
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (alpha : ℝ → M) (halpha : ContMDiff 𝓘(ℝ, ℝ) I 1 alpha)
    {tau : ℝ} (htau : 0 < tau) (g : SmoothRiemannianMetric I M)
    (htime : ∀ s ∈ _root_.Set.Icc 0 (Real.sqrt tau), T - s ^ 2 ∈ D.carrier)
    (hmetric : ∀ s ∈ _root_.Set.Icc 0 (Real.sqrt tau), ∀ z : M, ∀ v : TangentSpace I z,
      g.inner z v v ≤ (S.base.metric (T - s ^ 2)).inner z v v)
    (hscalar : ∀ s ∈ _root_.Set.Icc 0 (Real.sqrt tau), ∀ z : M,
      0 ≤ S.scalar (T - s ^ 2) z) :
    (riemannianEDistOf (I := I) g (alpha 0) (alpha (Real.sqrt tau))).toReal ^ 2 /
        (2 * Real.sqrt tau) ≤ lRegularizedAction S T alpha 0 (Real.sqrt tau) := by
  have hb : 0 < Real.sqrt tau := Real.sqrt_pos.mpr htau
  have hE := integrableOn_inner_mfderiv_self_of_contMDiffOn g halpha.contMDiffOn
    (a := 0) (b := Real.sqrt tau)
  have href : IntervalIntegrable
      (fun s => g.inner (alpha s) (lVelocity (I := I) alpha s)
        (lVelocity (I := I) alpha s)) _root_.MeasureTheory.MeasureSpace.volume 0 (Real.sqrt tau) := by
    apply IntegrableOn.intervalIntegrable
    simpa only [_root_.Set.uIcc_of_le hb.le, lVelocity] using hE
  have hLag : IntervalIntegrable (lRegularizedLagrangian S T alpha)
      volume 0 (Real.sqrt tau) := by
    have hcont := lRegularizedLagrangian_continuousOn_carrier S hS alpha halpha
    have hcurve := hcont.comp (s := _root_.Set.Icc 0 (Real.sqrt tau))
      (continuous_const.prodMk continuous_id).continuousOn (fun s hs => htime s hs)
    exact hcurve.intervalIntegrable_of_Icc hb.le
  have hcoerc := lRegularizedAction_ge_reference_energy_add_constant S T alpha g
    0 (Real.sqrt tau) 1 0 hb.le
    (fun s hs => by simpa only [one_mul] using hmetric s hs (alpha s) (lVelocity alpha s))
    (fun s hs => mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg s))
      (hscalar s hs (alpha s))) href hLag
  have henergy : curveEnergy g alpha 0 (Real.sqrt tau) ≤
      2 * lRegularizedAction S T alpha 0 (Real.sqrt tau) := by
    simp only [_root_.MulZeroClass.zero_mul, add_zero, intervalIntegral.integral_const_mul] at hcoerc
    change (1 / 2 : ℝ) * curveEnergy g alpha 0 (Real.sqrt tau) ≤ _ at hcoerc
    linarith
  have hdist := riemannianEDistOf_toReal_sq_le_curveEnergy g hb.le halpha.contMDiffOn hE
  rw [sub_zero] at hdist
  have hbound := hdist.trans (mul_le_mul_of_nonneg_left henergy hb.le)
  apply (div_le_iff₀ (show 0 < 2 * Real.sqrt tau by positivity)).mpr
  nlinarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction_ge_riemannianEDistOf_sq_div then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction_ge_riemannianEDistOf_sq_div"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction_ge_riemannianEDistOf_sq_div ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction_ge_riemannianEDistOf_sq_div

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lCost_ge_riemannianEDistOf_sq_div
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (x y : M) {tau : ℝ} (htau : 0 < tau)
    (g : SmoothRiemannianMetric I M)
    (htime : ∀ s ∈ _root_.Set.Icc 0 (Real.sqrt tau), T - s ^ 2 ∈ D.carrier)
    (hmetric : ∀ s ∈ _root_.Set.Icc 0 (Real.sqrt tau), ∀ z : M, ∀ v : TangentSpace I z,
      g.inner z v v ≤ (S.base.metric (T - s ^ 2)).inner z v v)
    (hscalar : ∀ s ∈ _root_.Set.Icc 0 (Real.sqrt tau), ∀ z : M,
      0 ≤ S.scalar (T - s ^ 2) z) :
    (riemannianEDistOf (I := I) g x y).toReal ^ 2 / (2 * Real.sqrt tau) ≤
      lCost S T x y tau := by
  by_contra hnot
  obtain ⟨alpha, halpha, h0, hbEnd, hact⟩ :=
    exists_lRegularizedAction_lt_of_lCost_lt_of_preconnected S T x y tau htau
      ((riemannianEDistOf (I := I) g x y).toReal ^ 2 / (2 * Real.sqrt tau))
      (lt_of_not_ge hnot)
  have hbound := lRegularizedAction_ge_riemannianEDistOf_sq_div S hS T alpha halpha
    htau g htime hmetric hscalar
  rw [h0, hbEnd] at hbound
  exact (not_lt_of_ge hbound) hact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lCost_ge_riemannianEDistOf_sq_div then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lCost_ge_riemannianEDistOf_sq_div"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lCost_ge_riemannianEDistOf_sq_div ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lCost_ge_riemannianEDistOf_sq_div

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
end

noncomputable section
open _root_.Set _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {D : RealTimeInterval}

private theorem lRegularizedAction_ge_of_scalar_lower_bound
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (γ : ℝ → M)
    {a b B : ℝ} (hab : a ≤ b)
    (hscalar : ∀ t ∈ _root_.Set.Ioo a b, -B ≤ S.scalar (T - t ^ 2) (γ t))
    (hint : IntervalIntegrable (lRegularizedLagrangian S T γ) _root_.MeasureTheory.MeasureSpace.volume a b) :
    -(2 * B / 3) * (b ^ 3 - a ^ 3) ≤ lRegularizedAction S T γ a b := by
  have hh := intervalIntegral.integral_ge_of_mul_sq_le hab hint (C := -(2 * B)) (fun t ht => ?_)
  · simpa only [neg_div, lRegularizedAction] using hh
  have hs := mul_le_mul_of_nonneg_left (hscalar t ht) (by positivity : 0 ≤ 2 * t ^ 2)
  have hk := lRegularizedSpeedSq_nonneg S T γ t
  change -(2 * B) * t ^ 2 ≤ _
  dsimp only [lRegularizedLagrangian, lRegularizedSpeedSq] at hk ⊢
  nlinarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction_ge_of_scalar_lower_bound
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction_ge_of_scalar_lower_bound target :: scope.openDecls } }


variable [T2Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lRegularizedCosts_bdd_of_scalar_lower
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) (T : ℝ)
    {a b B : ℝ} (hab : a ≤ b)
    (htime : ∀ t ∈ _root_.Set.Icc a b, T - t ^ 2 ∈ D.carrier)
    (hscalar : ∀ t ∈ _root_.Set.Ioo a b, ∀ z : M, -B ≤ S.scalar (T - t ^ 2) z)
    (x y : M) :
    BddBelow {r : ℝ | ∃ α : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 α ∧
      α a = x ∧ α b = y ∧ lRegularizedAction S T α a b = r} := by
  refine ⟨-(2 * B / 3) * (b ^ 3 - a ^ 3), ?_⟩
  rintro r ⟨α, hα, _, _, rfl⟩
  have hint : IntervalIntegrable (lRegularizedLagrangian S T α) _root_.MeasureTheory.MeasureSpace.volume a b := by
    have hc := lRegularizedLagrangian_continuousOn_carrier (I := I) S hS α hα
    have hm : ContinuousOn (fun r : ℝ => (T, r)) (_root_.Set.Icc a b) :=
      (continuous_const.prodMk continuous_id).continuousOn
    have hmap : _root_.Set.MapsTo (fun r : ℝ => (T, r)) (_root_.Set.Icc a b)
        {q : ℝ × ℝ | q.1 - q.2 ^ 2 ∈ D.carrier} := htime
    exact (hc.comp (f := fun r : ℝ => (T, r)) hm hmap).intervalIntegrable_of_Icc hab
  exact lRegularizedAction_ge_of_scalar_lower_bound (I := I) (M := M) S T α hab
    (fun t ht => hscalar t ht (α t)) hint

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedCosts_bdd_of_scalar_lower then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedCosts_bdd_of_scalar_lower"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedCosts_bdd_of_scalar_lower ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedCosts_bdd_of_scalar_lower


attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lRegularizedCosts_bdd_of_compact [CompactSpace M]
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) (T : ℝ)
    {a b : ℝ} (hab : a ≤ b) (htime : ∀ t ∈ _root_.Set.Icc a b, T - t ^ 2 ∈ D.carrier)
    (x y : M) :
    BddBelow {r : ℝ | ∃ α : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 α ∧
      α a = x ∧ α b = y ∧ lRegularizedAction S T α a b = r} := by
  have hmap : Continuous (fun q : ℝ × M => (T - q.1 ^ 2, q.2)) :=
    (continuous_const.sub (continuous_fst.pow 2)).prodMk continuous_snd
  have hmaps : _root_.Set.MapsTo (fun q : ℝ × M => (T - q.1 ^ 2, q.2))
      (_root_.Set.Icc a b ×ˢ _root_.Set.univ) (D.carrier ×ˢ _root_.Set.univ) :=
    fun q hq => ⟨htime q.1 hq.1, _root_.Set.mem_univ q.2⟩
  have hc : ContinuousOn (fun q : ℝ × M => S.scalar (T - q.1 ^ 2) q.2) (_root_.Set.Icc a b ×ˢ _root_.Set.univ) :=
    hS.scalarCont.comp (f := fun q : ℝ × M => (T - q.1 ^ 2, q.2)) hmap.continuousOn hmaps
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod isCompact_univ).bddBelow_image hc
  apply lRegularizedCosts_bdd_of_scalar_lower S hS T hab htime (B := -B)
  intro t ht z
  simpa only [neg_neg] using hB ⟨(t, z), ⟨⟨ht.1.le, ht.2.le⟩, _root_.Set.mem_univ z⟩, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedCosts_bdd_of_compact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedCosts_bdd_of_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedCosts_bdd_of_compact ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedCosts_bdd_of_compact


end DifferentialGeometry.PDE.RicciFlow.Perelman

end
