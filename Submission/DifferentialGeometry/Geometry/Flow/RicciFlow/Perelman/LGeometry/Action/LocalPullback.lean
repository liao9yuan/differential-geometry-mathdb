import Submission.DifferentialGeometry.Analysis.Calculus.Manifold.AbsolutelyContinuous
import Submission.DifferentialGeometry.Topology.Covering.SmoothLift.Regularity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.LocalPullback
import Submission.DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Basic
import Submission.DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalCross
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Defs
import Mathlib.Analysis.Convex.Contractible

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Filter _root_.MeasureTheory
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Submission.DifferentialGeometry.Geometry.Curvature

variable {E F H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  {D : RealTimeInterval}

variable [T2Space N] [I.Boundaryless] [J.Boundaryless]

namespace Perelman

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [IsManifold I ∞ M]
  [T2Space M] [IsManifold J ∞ N] [T2Space N] [I.Boundaryless] [J.Boundaryless] in
private theorem lVelocity_comp_of_mdifferentiableAt
    {p : M → N} (hp : IsLocalDiffeomorph I J ∞ p)
    {alpha : ℝ → M} {s : ℝ} (ha : MDifferentiableAt 𝓘(ℝ, ℝ) I alpha s) :
    lVelocity (I := J) (p ∘ alpha) s =
      mfderiv I J p (alpha s) (lVelocity (I := I) alpha s) := by
  unfold lVelocity
  rw [mfderiv_comp s ((hp (alpha s)).mdifferentiableAt (by simp)) ha]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lVelocity_comp_of_mdifferentiableAt
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.lVelocity_comp_of_mdifferentiableAt target :: scope.openDecls } }

theorem unweighted_action_localPullback
    (g : ℝ → SmoothRiemannianMetric J N) (p : M → N)
    (hp : IsLocalDiffeomorph I J ∞ p) (alpha : ℝ → M) (b s : ℝ)
    (ha : ∀ᵐ t ∂volume.restrict (_root_.Set.Ioc b s), MDifferentiableAt 𝓘(ℝ, ℝ) I alpha t) :
    (∫⁻ t in _root_.Set.Ioc b s, ENNReal.ofReal
      (metricScalarAt (localPullMetric (g t) p hp) (alpha t) +
        (localPullMetric (g t) p hp).inner (alpha t)
          (lVelocity (I := I) alpha t) (lVelocity (I := I) alpha t))) =
      ∫⁻ t in _root_.Set.Ioc b s, ENNReal.ofReal
        (metricScalarAt (g t) ((p ∘ alpha) t) +
          (g t).inner ((p ∘ alpha) t)
            (lVelocity (I := J) (p ∘ alpha) t) (lVelocity (I := J) (p ∘ alpha) t)) := by
  apply _root_.MeasureTheory.lintegral_congr_ae
  filter_upwards [ha] with t ht
  have hv := lVelocity_comp_of_mdifferentiableAt hp ht
  rw [metricScalarAt_localPull, localPullMetric_inner, hv]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.unweighted_action_localPullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.unweighted_action_localPullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.unweighted_action_localPullback ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.unweighted_action_localPullback

theorem unweighted_action_localPullback_of_contMDiffOn
    (g : ℝ → SmoothRiemannianMetric J N) (p : M → N)
    (hp : IsLocalDiffeomorph I J ∞ p) (alpha : ℝ → M) (b s : ℝ)
    (ha : ContMDiffOn 𝓘(ℝ, ℝ) I 1 alpha (_root_.Set.Icc b s)) :
    (∫⁻ t in _root_.Set.Ioc b s, ENNReal.ofReal
      (metricScalarAt (localPullMetric (g t) p hp) (alpha t) +
        (localPullMetric (g t) p hp).inner (alpha t)
          (lVelocity (I := I) alpha t) (lVelocity (I := I) alpha t))) =
      ∫⁻ t in _root_.Set.Ioc b s, ENNReal.ofReal
        (metricScalarAt (g t) ((p ∘ alpha) t) +
          (g t).inner ((p ∘ alpha) t)
            (lVelocity (I := J) (p ∘ alpha) t) (lVelocity (I := J) (p ∘ alpha) t)) := by
  apply unweighted_action_localPullback g p hp alpha b s
  filter_upwards [_root_.MeasureTheory.ae_restrict_mem measurableSet_Ioc,
    _root_.MeasureTheory.ae_restrict_of_ae (Measure.ae_ne _root_.MeasureTheory.MeasureSpace.volume s)] with t ht hts
  exact (ha.contMDiffAt (Icc_mem_nhds ht.1 (lt_of_le_of_ne ht.2 hts))).mdifferentiableAt one_ne_zero

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.unweighted_action_localPullback_of_contMDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.unweighted_action_localPullback_of_contMDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.unweighted_action_localPullback_of_contMDiffOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.unweighted_action_localPullback_of_contMDiffOn

theorem unweighted_action_restrictOpen
    (g : ℝ → SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    (alpha : ℝ → U) (b s : ℝ) (ha : ContMDiffOn 𝓘(ℝ, ℝ) I 1 alpha (_root_.Set.Icc b s)) :
    (∫⁻ t in _root_.Set.Ioc b s, ENNReal.ofReal
      (metricScalarAt ((g t).restrictOpen U) (alpha t) +
        ((g t).restrictOpen U).inner (alpha t)
          (lVelocity (I := I) alpha t) (lVelocity (I := I) alpha t))) =
      ∫⁻ t in _root_.Set.Ioc b s, ENNReal.ofReal
        (metricScalarAt (g t) ((alpha t).val) +
          (g t).inner (alpha t).val
            (lVelocity (I := I) (fun u => (alpha u).val) t)
            (lVelocity (I := I) (fun u => (alpha u).val) t)) := by
  simpa only [localPullMetric_subtype_val, Function.comp_def] using
    unweighted_action_localPullback_of_contMDiffOn g (Subtype.val : U → M)
      (isLocalDiffeomorph_subtype_val U) alpha b s ha

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.unweighted_action_restrictOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.unweighted_action_restrictOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.unweighted_action_restrictOpen ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.unweighted_action_restrictOpen

theorem lDensity_localPullback
    (S : SolutionOn (I := J) (M := N) D) (p : M → N)
    (hp : IsLocalDiffeomorph I J ∞ p) (T : ℝ)
    {alpha : ℝ → M} {s : ℝ} (ha : MDifferentiableAt 𝓘(ℝ, ℝ) I alpha s) :
    lDensity (S.localPullback p hp) T alpha s = lDensity S T (p ∘ alpha) s := by
  simp only [lDensity, lSpeedSq, SolutionOn.localPullback_scalar,
    SolutionOn.localPullback_metric, localPullMetric_inner,
    lVelocity_comp_of_mdifferentiableAt hp ha, Function.comp_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lDensity_localPullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lDensity_localPullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lDensity_localPullback ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lDensity_localPullback

theorem lRegularizedLagrangian_localPullback
    (S : SolutionOn (I := J) (M := N) D) (p : M → N)
    (hp : IsLocalDiffeomorph I J ∞ p) (T : ℝ)
    {alpha : ℝ → M} {s : ℝ} (ha : MDifferentiableAt 𝓘(ℝ, ℝ) I alpha s) :
    lRegularizedLagrangian (S.localPullback p hp) T alpha s =
      lRegularizedLagrangian S T (p ∘ alpha) s := by
  simp only [lRegularizedLagrangian, SolutionOn.localPullback_scalar,
    SolutionOn.localPullback_metric, localPullMetric_inner,
    lVelocity_comp_of_mdifferentiableAt hp ha, Function.comp_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedLagrangian_localPullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedLagrangian_localPullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedLagrangian_localPullback ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedLagrangian_localPullback

theorem lRegularizedAction_localPullback
    (S : SolutionOn (I := J) (M := N) D) (p : M → N)
    (hp : IsLocalDiffeomorph I J ∞ p) (T : ℝ)
    {alpha : ℝ → M} (ha : ContMDiff 𝓘(ℝ, ℝ) I 1 alpha) (a b : ℝ) :
    lRegularizedAction (S.localPullback p hp) T alpha a b =
      lRegularizedAction S T (p ∘ alpha) a b := by
  unfold lRegularizedAction
  apply intervalIntegral.integral_congr
  intro s _
  exact lRegularizedLagrangian_localPullback S p hp T (ha.mdifferentiable one_ne_zero s)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction_localPullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction_localPullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction_localPullback ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction_localPullback

theorem lLength_squareRootReparametrization_localPullback
    (S : SolutionOn (I := J) (M := N) D) (p : M → N)
    (hp : IsLocalDiffeomorph I J ∞ p) (T : ℝ)
    {alpha : ℝ → M} (ha : ContMDiff 𝓘(ℝ, ℝ) I 1 alpha) (a b : ℝ) :
    lLength (S.localPullback p hp) T (squareRootReparametrization alpha) a b =
      lLength S T (squareRootReparametrization (p ∘ alpha)) a b := by
  unfold lLength
  apply intervalIntegral.integral_congr_ae
  filter_upwards [Measure.ae_ne _root_.MeasureTheory.MeasureSpace.volume (0 : ℝ)] with s hs _
  have hsq : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) Real.sqrt s :=
    (Real.hasDerivAt_sqrt hs).differentiableAt.mdifferentiableAt
  exact lDensity_localPullback S p hp T
    ((ha.mdifferentiable one_ne_zero (Real.sqrt s)).comp s hsq)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lLength_squareRootReparametrization_localPullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lLength_squareRootReparametrization_localPullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lLength_squareRootReparametrization_localPullback ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lLength_squareRootReparametrization_localPullback

theorem exists_contMDiff_curve_lift_preserving_action
    (S : SolutionOn (I := J) (M := N) D) (p : M → N)
    (hp : IsLocalDiffeomorph I J ∞ p) (hcover : IsCoveringMap p)
    (alpha : ℝ → N) (ha : ContMDiff 𝓘(ℝ, ℝ) J 1 alpha)
    (a : ℝ) (x : M) (hx : p x = alpha a) :
    ∃ beta : C(ℝ, M), beta a = x ∧ (∀ s, p (beta s) = alpha s) ∧
      ContMDiff 𝓘(ℝ, ℝ) I 1 beta ∧
      (∀ T b c, lRegularizedAction (S.localPullback p hp) T beta b c =
        lRegularizedAction S T alpha b c) ∧
      ∀ T b c, lLength (S.localPullback p hp) T (squareRootReparametrization beta) b c =
        lLength S T (squareRootReparametrization alpha) b c := by
  have hp1 : IsLocalDiffeomorph I J 1 p := by
    intro y
    obtain ⟨φ, hy, heq⟩ := hp y
    exact ⟨DifferentialGeometry.PartialDiffeomorph.ofLE φ (by simp), hy, heq⟩
  obtain ⟨beta, hb0, hpb, hbs⟩ :=
    DifferentialGeometry.Topology.exists_contMDiff_lift_of_simplyConnected
      hcover hp1 alpha ha a x hx
  have hcomp : p ∘ beta = alpha := funext hpb
  refine ⟨beta, hb0, hpb, hbs, ?_, ?_⟩
  · intro T b c
    rw [lRegularizedAction_localPullback S p hp T hbs, hcomp]
  · intro T b c
    rw [lLength_squareRootReparametrization_localPullback S p hp T hbs, hcomp]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.exists_contMDiff_curve_lift_preserving_action then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.exists_contMDiff_curve_lift_preserving_action"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.exists_contMDiff_curve_lift_preserving_action ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.exists_contMDiff_curve_lift_preserving_action

end Perelman
end DifferentialGeometry.PDE.RicciFlow

noncomputable section

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Interval

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

variable {E : Type*} {F : Type*} {H : Type*} {G : Type*} {M : Type*} {N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N] [T2Space N]
  [I.Boundaryless] [J.Boundaryless]

theorem lRegularizedLagrangian_ae_eq_of_metric_eqOn_localPullback
    {D D' : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (S' : SolutionOn (I := J) (M := N) D')
    (p : M → N) (hp : IsLocalDiffeomorph I J ∞ p)
    (T : ℝ) {u v : ℝ} (huv : u ≤ v) (gamma : ℝ → M) (alpha : ℝ → N)
    (hgamma : Manifold.absolutelyContinuousOnInterval I gamma u v)
    (hproj : _root_.Set.EqOn (p ∘ gamma) alpha (_root_.Set.Ioo u v))
    (hmetric : ∀ r ∈ _root_.Set.Ioo u v, S.base.metric (T - r ^ 2) =
      localPullMetric (S'.base.metric (T - r ^ 2)) p hp) :
    lRegularizedLagrangian S T gamma =ᵐ[volume.restrict (Ι u v)]
      lRegularizedLagrangian S' T alpha := by
  let : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
  have hdiff := Manifold.absolutelyContinuousOnInterval_ae_mdifferentiableAt hgamma
  rw [_root_.Set.uIcc_of_le huv, ← _root_.MeasureTheory.restrict_Ioo_eq_restrict_Icc] at hdiff
  rw [_root_.Set.uIoc_of_le huv, ← _root_.MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
  filter_upwards [hdiff, _root_.MeasureTheory.ae_restrict_mem measurableSet_Ioo] with r hdr hr
  have heq : p ∘ gamma =ᶠ[𝓝 r] alpha := by
    filter_upwards [Ioo_mem_nhds hr.1 hr.2] with x hx
    exact hproj hx
  have hvel : lVelocity (I := J) (p ∘ gamma) r =
      lVelocity (I := J) alpha r :=
    congrArg (fun L => L (1 : ℝ))
      (heq.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := J))
  calc
    _ = lRegularizedLagrangian (S'.localPullback p hp) T gamma r := by
      unfold lRegularizedLagrangian SolutionOn.scalar SolutionFamily.scalar
      rw [hmetric r hr]
      rfl
    _ = lRegularizedLagrangian S' T (p ∘ gamma) r :=
      lRegularizedLagrangian_localPullback S' p hp T hdr
    _ = _ := by
      simp only [lRegularizedLagrangian]
      rw [heq.self_of_nhds, hvel]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedLagrangian_ae_eq_of_metric_eqOn_localPullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedLagrangian_ae_eq_of_metric_eqOn_localPullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedLagrangian_ae_eq_of_metric_eqOn_localPullback ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedLagrangian_ae_eq_of_metric_eqOn_localPullback

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
