import Submission.DifferentialGeometry.Geometry.Comparison.Volume.Bishop.CompactBall
import Submission.DifferentialGeometry.Geometry.Comparison.Volume.Model
import Submission.DifferentialGeometry.Geometry.Comparison.Volume.VolumeNaturality
import Submission.DifferentialGeometry.Geometry.Comparison.HopfRinow.Proper
import Mathlib.MeasureTheory.Integral.Bochner.Set

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal _root_.Topology

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open _root_.Submission.DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem volume_ball_le (g : SmoothRiemannianMetric I M)
    (hg : RiemannianMetricComplete g) (p : M) {r : ℝ} (hr : 0 < r)
    (hRic : BonnetMyers.RicciBoundedBelow (I := I) g 0) :
    riemannianVolumeMeasure (I := I) (M := M) g {x | riemannianEDistOf g p x < ENNReal.ofReal r} ≤
      ENNReal.ofReal (euclideanUnitBallVolume (Module.finrank ℝ E) * r ^ Module.finrank ℝ E) := by
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : _root_.Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  have hnorm : IsMetricNorm (I := I) g := fun x v =>
    tensor0SBundle_enorm_eq_riemannianBundle_enorm g x v
  have hcpt := hg.closedEBall_isCompact p r
  simp_rw [riemannianEDistOf_eq_riemannianEDist g hnorm] at hcpt ⊢
  have hcpt' : IsCompact (Metric.closedEBall p (ENNReal.ofReal r)) := by
    change IsCompact {x | _root_.Manifold.riemannianEDist I x p ≤ ENNReal.ofReal r}
    simpa only [_root_.Manifold.riemannianEDist_comm] using hcpt
  have h := riemannianVolumeMeasure_ball_le_hyperbolic_of_isCompact_closedEBall g hnorm p
    (q := 0) (by rfl) hr hcpt' (fun x v _ => by simpa using hRic x v)
  have hn : 1 ≤ Module.finrank ℝ E := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
  rw [← ofReal_modelVolume_neg_sq 0 r (Module.finrank ℝ E) hn (by rfl)] at h
  simpa only [zero_pow (by decide : 2 ≠ 0), neg_zero, modelVolume_zero _ _ hn] using h

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.volume_ball_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.volume_ball_le target :: scope.openDecls } }

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem integral_le_of_support_subset_ball_of_ricci_nonnegative
    (g h : SmoothRiemannianMetric I M) (hg : RiemannianMetricComplete g)
    (hRic : BonnetMyers.RicciBoundedBelow (I := I) g 0)
    (p : M) {r Q B : ℝ} (hr : 0 < r) (hQ : 0 < Q)
    (hcomp : ∀ x, riemannianEDistOf g p x < ENNReal.ofReal r →
      ∀ v : TangentSpace I x, h.inner x v v ≤ Q * g.inner x v v)
    {f : M → ℝ} (hf : ∀ x, f x ∈ _root_.Set.Icc 0 B)
    (hsupport : Function.support f ⊆ {x | riemannianEDistOf g p x < ENNReal.ofReal r}) :
    (∫ x, f x ∂riemannianVolumeMeasure (I := I) (M := M) h) ≤
      B * Real.sqrt (Q ^ Module.finrank ℝ E) *
        euclideanUnitBallVolume (Module.finrank ℝ E) * r ^ Module.finrank ℝ E := by
  let : MeasurableSpace M := borel M
  let : BorelSpace M := ⟨rfl⟩
  let A : Set M := {x | riemannianEDistOf g p x < ENNReal.ofReal r}
  have hd : Continuous (fun x => riemannianEDistOf g p x) := by
    let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
    let : _root_.Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    exact continuous_const.edist continuous_id
  have hA : MeasurableSet A := (isOpen_lt hd continuous_const).measurableSet
  have hV := (riemannianVolumeMeasure_apply_le_of_inner_le_on g h hA hQ
    (fun x hx v => hcomp x hx v)).trans
      (mul_le_mul_right (volume_ball_le g hg p hr hRic) _)
  let V := Real.sqrt (Q ^ Module.finrank ℝ E) *
    (euclideanUnitBallVolume (Module.finrank ℝ E) * r ^ Module.finrank ℝ E)
  have hω := euclideanUnitBallVolume_pos (Module.finrank ℝ E)
  have hV0 : 0 ≤ V := by dsimp [V]; positivity
  have hV' : riemannianVolumeMeasure (I := I) (M := M) h A ≤ ENNReal.ofReal V := by
    simpa only [V, ENNReal.ofReal_mul (Real.sqrt_nonneg _)] using hV
  have hfinite : riemannianVolumeMeasure (I := I) (M := M) h A < ⊤ := hV'.trans_lt ENNReal.ofReal_lt_top
  have hB : 0 ≤ B := (hf p).1.trans (hf p).2
  have hi : _root_.MeasureTheory.Integrable (A.indicator (fun _ : M => B)) (riemannianVolumeMeasure (I := I) (M := M) h) := by
    rw [_root_.MeasureTheory.integrable_indicator_iff hA]
    exact _root_.MeasureTheory.integrableOn_const hfinite.ne
  have hle : (∫ x, f x ∂riemannianVolumeMeasure (I := I) (M := M) h) ≤
      (riemannianVolumeMeasure (I := I) (M := M) h A).toReal * B := by
    calc _ ≤ ∫ x, A.indicator (fun _ : M => B) x ∂riemannianVolumeMeasure (I := I) (M := M) h := by
            apply _root_.MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => (hf x).1) hi
            filter_upwards [] with x
            by_cases hx : x ∈ A
            · simpa only [_root_.Set.indicator_of_mem hx] using (hf x).2
            · have hz : f x = 0 := not_not.mp (fun hn => hx (hsupport hn))
              simp only [_root_.Set.indicator_of_notMem hx, hz, le_refl]
         _ = _ := by simp only [_root_.MeasureTheory.integral_indicator hA, _root_.MeasureTheory.setIntegral_const, smul_eq_mul, _root_.MeasureTheory.measureReal_def]
  have hvle : (riemannianVolumeMeasure (I := I) (M := M) h A).toReal ≤ V :=
    (ENNReal.toReal_mono ENNReal.ofReal_ne_top hV').trans_eq (ENNReal.toReal_ofReal hV0)
  calc _ ≤ V * B := hle.trans (mul_le_mul_of_nonneg_right hvle hB)
       _ = _ := by dsimp [V]; ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.integral_le_of_support_subset_ball_of_ricci_nonnegative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.VolumeComparison.integral_le_of_support_subset_ball_of_ricci_nonnegative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.integral_le_of_support_subset_ball_of_ricci_nonnegative ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.integral_le_of_support_subset_ball_of_ricci_nonnegative

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
