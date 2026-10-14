import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.InitialMetricTimeBounds
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.InitialWindowBounds
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardMetricControl
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardUniformExistence
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Curvature.MovingShi

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Neck _root_.Submission.DifferentialGeometry.Geometry.Metric
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ENNReal _root_.BigOperators
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instSigmaCompactSpaceSubtypeThreeSpaceMemOpens (V : TopologicalSpace.Opens ThreeSpace) : SigmaCompactSpace V :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel V.isOpen)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instSigmaCompactSpaceSubtypeThreeSpaceMemOpens
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instSigmaCompactSpaceSubtypeThreeSpaceMemOpens target :: scope.openDecls } }

theorem exists_uniform_initial_standard_cap_comparison
    (D R R₁ T ε : ℝ) (hRR₁ : R < R₁) (hR₁D : R₁ ≤ D)
    (hT : 0 < T) (hε : 0 < ε)
    (N : ℕ) (C : ℕ → ℝ) :
    ∃ η ε₀ : ℝ, 0 < η ∧ η ≤ T ∧ 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧
      ∀ {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
        {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
        {d : normalizedDatum g x₀ δ k} {A : ℝ} {hA : 0 < A} {m : ℕ} {ζ : ℝ}
        (w : CanonicalStaticInsertionWitness d A hA D m ζ),
      N ≤ m → ζ ≤ ε₀ →
      ∀ (J : RealTimeInterval) (θ : ℝ), 0 ≤ θ → θ ≤ T →
        _root_.Set.Icc 0 θ ⊆ J.carrier → _root_.Set.Ioo 0 θ ⊆ J.regular →
        ∀ L : SolutionOn (I := ThreeModel) (M := standardCapWindow D) J,
        IsSolutionOn L → L.base.metric 0 = w.windowMetric →
        (∀ (p : standardCapWindow D) (i j : Fin (Module.finrank ℝ ThreeSpace)),
          ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ, ℝ) ∞
            (fun q : ℝ × standardCapWindow D =>
              DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (L.base.metric q.1) p q.2 i j)
            (_root_.Set.Icc 0 θ ×ˢ (_root_.FiberBundle.trivializationAt ThreeSpace (TangentSpace ThreeModel) p).baseSet)) →
        (∀ j ≤ N, ∀ t ∈ _root_.Set.Icc 0 θ, ∀ x : standardCapWindow D, ‖x.val‖ < R₁ →
          curvDerivNorm j (L.base.metric t) x ≤ C j) →
        ∀ S : StandardSolution, ∀ t ∈ _root_.Set.Icc 0 (_root_.Min.min η θ),
          metricDerivNormSupOn {x : standardCapWindow D | ‖x.val‖ ≤ R} N
            (L.base.metric t) ((S.val.metric t).restrictOpen (standardCapWindow D))
            (standardCapMetric.restrictOpen (standardCapWindow D)) < ε := by
  let gRef := standardCapMetric.restrictOpen (standardCapWindow D)
  let U : Set (standardCapWindow D) := {x | ‖x.val‖ < R₁}
  let K : Set (standardCapWindow D) := {x | ‖x.val‖ ≤ R}
  have hRD : R < D := hRR₁.trans_le hR₁D
  have hU : IsOpen U := isOpen_lt (continuous_norm.comp continuous_subtype_val) continuous_const
  have hK : IsCompact K := by
    have hc : IsCompact {x : ThreeSpace | ‖x‖ ≤ R} := by
      simpa only [Metric.closedBall,dist_zero_right] using _root_.ProperSpace.isCompact_closedBall (0 : ThreeSpace) R
    exact _root_.Topology.IsInducing.subtypeVal.isCompact_preimage' hc (by
      intro x hx
      refine ⟨⟨x, ?_⟩, rfl⟩
      change ‖x‖ < D+1
      change ‖x‖ ≤ R at hx
      linarith)
  have hKU : K ⊆ U := fun _ hx => hx.trans_lt hRR₁
  obtain ⟨KRic, hKRic, hRic⟩ := exists_movingShiBoundOn_constant_of_curvature_derivative_bounds
    (I := ThreeModel) (M := standardCapWindow D) N C
  obtain ⟨η₁, hη₁, hη₁T, hvariation⟩ := exists_uniform_initial_metric_derivative_stability
    U hU gRef N T 2 KRic (ε/4) hT (by norm_num) hKRic (by positivity)
    (fun _ => 1/2) (by intros;norm_num)
  obtain ⟨α, hα, Λstd, hΛstd, Cstd, Lstd, hCstd, hLstd, hstd⟩ :=
    standard_uniform_fixed_cap_metric_bounds
  obtain ⟨αlife, hαlife, _, _, hlife, _⟩ := standard_uniform_initial_window
  let Lsum := ∑ j ∈ Finset.range (N+1), Lstd j
  have hLsum : 0 ≤ Lsum := Finset.sum_nonneg (fun j _ => hLstd j)
  let η := _root_.Min.min η₁ (_root_.Min.min α (_root_.Min.min αlife (ε/(4*(Lsum+1)))))
  let ε₀ := _root_.Min.min (1/2) (ε/4)
  have hη : 0 < η := lt_min hη₁ (lt_min hα (lt_min hαlife (div_pos hε (by positivity))))
  have hη1 : η ≤ η₁ := min_le_left _ _
  have hηα : η ≤ α := (min_le_right _ _).trans (min_le_left _ _)
  have hηlife : η ≤ αlife := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hηrate : η ≤ ε/(4*(Lsum+1)) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨η, ε₀, hη, hη1.trans hη₁T, lt_min (by norm_num) (by positivity),
    min_le_left _ _, ?_⟩
  intro E H M _ _ _ _ _ I _ _ _ _ _ g x₀ δ k d A hA m ζ w hNm hζ
    J θ hθ hθT hcarrier hregular L hL hzero hgram hcurv S t ht
  have hζhalf : ζ ≤ 1/2 := hζ.trans (min_le_left _ _)
  have hζtarget : ζ ≤ ε/4 := hζ.trans (min_le_right _ _)
  have hpoint : ∀ j ≤ N, ∀ x ∈ U, metricDerivNorm j w.windowMetric gRef gRef x < ζ := by
    intro j hj x hx
    have he := w.properties.window_close
    change metricDerivENormSupOn
      {x : standardCapWindow D | (riemannianEDistOf metric 0 x.val).toReal < D} m
      w.windowMetric (metric.restrictOpen (standardCapWindow D))
        (metric.restrictOpen (standardCapWindow D)) < ENNReal.ofReal ζ at he
    simp only [distance_zero] at he
    dsimp only [gRef]
    rw [standardCapMetric_eq_metric]
    exact metricDerivNorm_lt_of_sup_lt _ _ _ _ _ he (hj.trans hNm) (hx.trans_le hR₁D)
  have hequiv : MetricUniformEquivalentOn U gRef (L.base.metric 0) 2 := by
    rw [hzero]
    refine ⟨by norm_num, ?_⟩
    intro x hx v
    have hb := inner_bounds_of_metricDerivNorm_le gRef w.windowMetric x
      ((hpoint 0 (Nat.zero_le N) x hx).le.trans hζhalf) v
    have hn := metric_inner_self_nonneg gRef x v
    constructor
    · simpa only [show (2:ℝ)⁻¹=1/2 by norm_num,show (1:ℝ)-1/2=1/2 by norm_num] using hb.1
    · have hh := hb.2
      linarith
  have hjets : ∀ j, 1 ≤ j → j ≤ N → ∀ x ∈ U,
      metricCovDerivNorm j (L.base.metric 0) gRef x ≤ 1/2 := by
    intro j hj hjN x hx
    rw [hzero]
    have hh := w.window_metricCovDerivNorm_le (hjN.trans hNm) (hx.trans_le hR₁D)
    have hne : j ≠ 0 := by omega
    simp only [if_neg hne, zero_add] at hh
    exact hh.trans hζhalf
  have hRicL := hRic (fun _ s => L.base.metric s) U 0 θ
    (fun j hj _ s hs x hx => hcurv j hj s hs x hx)
  have htv : t ∈ _root_.Set.Icc 0 (_root_.Min.min η₁ θ) := ⟨ht.1, le_min
    ((ht.2.trans (min_le_left _ _)).trans hη1) (ht.2.trans (min_le_right _ _))⟩
  have hvar := hvariation J θ hθ hθT hcarrier hregular L hL hgram hequiv hjets hRicL K hKU t htv
  have hstdlife : ENNReal.ofReal η < S.val.lifetime :=
    (ENNReal.ofReal_le_ofReal hηlife).trans_lt (hlife S)
  have hstdrate := (hstd S.val η hη.le hηα hstdlife).2.2
  have htη : t ∈ _root_.Set.Icc 0 η := ⟨ht.1, ht.2.trans (min_le_left _ _)⟩
  have hstdsmall : Lsum*t < ε/4 := by
    have htle := htη.2.trans hηrate
    have hp : t*(4*(Lsum+1)) ≤ ε := (le_div_iff₀ (by positivity)).mp htle
    nlinarith
  have hbound : metricDerivNormSupOn K N (L.base.metric t)
      ((S.val.metric t).restrictOpen (standardCapWindow D)) gRef ≤ 3*ε/4 := by
    apply metricDerivNormSupOn_le_of_forall K N _ _ _ _ (by positivity)
    intro j hj x hx
    have h1 := (derivNorm_le_sup hK hj (L.base.metric t) (L.base.metric 0) gRef hx).trans_lt hvar
    have h2 := (hpoint j hj x (hKU hx)).trans_le hζtarget
    have h3 := hstdrate j 0 ⟨le_rfl,hη.le⟩ t htη x.val
    rw [S.val.initial, zero_sub, abs_neg, abs_of_nonneg ht.1] at h3
    have hLj : Lstd j ≤ Lsum := Finset.single_le_sum
      (fun a _ => hLstd a) (Finset.mem_range.mpr (by omega))
    have h3' : metricDerivNorm j gRef
        ((S.val.metric t).restrictOpen (standardCapWindow D)) gRef x < ε/4 := by
      dsimp only [gRef]
      rw [metricDerivNorm_restrictOpen,standardCapMetric_eq_metric]
      exact (h3.trans (mul_le_mul_of_nonneg_right hLj ht.1)).trans_lt hstdsmall
    have htri1 := metricDerivNorm_triangle j (L.base.metric t) (L.base.metric 0)
      ((S.val.metric t).restrictOpen (standardCapWindow D)) gRef x
    have htri2 := metricDerivNorm_triangle j (L.base.metric 0) gRef
      ((S.val.metric t).restrictOpen (standardCapWindow D)) gRef x
    rw [hzero] at htri1 h1 htri2
    linarith
  exact hbound.trans_lt (by linarith)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_uniform_initial_standard_cap_comparison then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_uniform_initial_standard_cap_comparison"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_uniform_initial_standard_cap_comparison ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_uniform_initial_standard_cap_comparison

end DifferentialGeometry.PDE.RicciFlow.StandardCap
