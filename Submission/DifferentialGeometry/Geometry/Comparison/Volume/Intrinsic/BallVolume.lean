import Submission.DifferentialGeometry.Geometry.Comparison.Volume.JacobianBounds
import Submission.DifferentialGeometry.Geometry.Comparison.Convexity.Geodesic
import Submission.DifferentialGeometry.Geometry.Exponential.Intrinsic.Framed.BallChart

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open scoped _root_.ContDiff _root_.ENNReal _root_.Manifold _root_.Submission.Manifold _root_.Matrix

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace VolumeComparison

open _root_.Bundle _root_.Submission.Bundle _root_.MeasureTheory _root_.Metric _root_.Set
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Exponential
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  [T2Space (TangentBundle I M)]

private local instance _root_.Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.instCompleteSpace_differentialGeometry : CompleteSpace E :=
  FiniteDimensional.complete Real E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.instCompleteSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

noncomputable def modelCoeffMin : Real :=
  (‖(toEuclidean (E := E) : E →L[Real]
      EuclideanSpace Real (Fin (Module.finrank Real E)))‖ + 1)⁻¹

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.modelCoeffMin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.VolumeComparison.modelCoeffMin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.modelCoeffMin ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.modelCoeffMin

omit [NeZero (Module.finrank Real E)] in
theorem modelCoeffMin_pos : 0 < modelCoeffMin (E := E) := by
  apply inv_pos.mpr
  exact add_pos_of_nonneg_of_pos (norm_nonneg _) one_pos

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.modelCoeffMin_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.VolumeComparison.modelCoeffMin_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.modelCoeffMin_pos ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.modelCoeffMin_pos

omit [NeZero (Module.finrank Real E)] in
theorem modelCoeffMin_le
    (v : EuclideanSpace Real (Fin (Module.finrank Real E)))
    (hv : ‖v‖ = 1) :
    modelCoeffMin (E := E) ≤
      ‖∑ i, v i • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i‖ := by
  let L : E →L[Real] EuclideanSpace Real (Fin (Module.finrank Real E)) :=
    (toEuclidean (E := E)).toContinuousLinearMap
  let K : Real := ‖L‖ + 1
  let w : E := (toEuclidean (E := E)).symm v
  have hK : 0 < K :=
    add_pos_of_nonneg_of_pos (norm_nonneg L) one_pos
  have hanti :=
    (ContinuousLinearEquiv.antilipschitz
      ((toEuclidean (E := E)).symm)).le_mul_dist v 0
  have hone : 1 ≤ K * ‖w‖ := by
    simp only [map_zero, dist_zero_right, hv] at hanti
    have hnorm_le : (↑‖L‖₊ : Real) ≤ K := by
      simp [K, L]
    exact hanti.trans
      (mul_le_mul_of_nonneg_right hnorm_le (norm_nonneg w))
  have hmin : K⁻¹ ≤ ‖w‖ := by
    have hdiv : 1 / K ≤ ‖w‖ :=
      (div_le_iff₀ hK).2 (by simpa [mul_comm] using hone)
    simpa only [one_div] using hdiv
  have hw :
      w = ∑ i, v i • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i := by
    have hvsum :
        v = ∑ i, v i • EuclideanSpace.single i (1 : Real) := by
      let b :=
        (EuclideanSpace.basisFun
          (Fin (Module.finrank Real E)) Real).toBasis
      simpa [b, EuclideanSpace.basisFun_apply] using (b.sum_repr v).symm
    calc
      w = (toEuclidean (E := E)).symm v := rfl
      _ = (toEuclidean (E := E)).symm
          (∑ i, v i • EuclideanSpace.single i (1 : Real)) := by
            exact congrArg (toEuclidean (E := E)).symm hvsum
      _ = ∑ i, v i •
          (toEuclidean (E := E)).symm
            (EuclideanSpace.single i (1 : Real)) := by
            rw [map_sum]
            simp only [map_smul]
      _ = ∑ i, v i • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i := by
            simp only [DifferentialGeometry.Tensor.Coordinates.chartModelBasis_apply]
  simpa [modelCoeffMin, K, L, hw] using hmin

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.modelCoeffMin_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.VolumeComparison.modelCoeffMin_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.modelCoeffMin_le ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.modelCoeffMin_le

omit [NeZero (Module.finrank Real E)] [T2Space M] [SigmaCompactSpace M] in
omit [I.Boundaryless] [T2Space (TangentBundle I M)] in
theorem param_dens_ge
    (g : SmoothRiemannianMetric I M) {p : M}
    (c : NormalBallChart (I := I) p)
    (heq : c.MetricEquivOn g (Metric.ball (0 : E) c.radius))
    {z : E} (hz : z ∈ Metric.ball (0 : E) c.radius) :
    Real.sqrt
        (((1 / 2 : Real) * modelCoeffMin (E := E) ^ 2) ^
          Module.finrank Real E) ≤
      paramDensity (I := I) g c.hom z := by
  let a : Real := (1 / 2 : Real) * modelCoeffMin (E := E) ^ 2
  have ha : 0 ≤ a :=
    mul_nonneg (by norm_num) (sq_nonneg _)
  have hgram :=
    paramGramMatrix_posDef (I := I) g c.hom (c.ball_subset hz)
  have hray :
      ∀ v : EuclideanSpace Real (Fin (Module.finrank Real E)),
        ‖v‖ = 1 →
        a ≤ RCLike.re
          (_root_.Star.star (⇑v) ⬝ᵥ
            (paramGramMatrix (I := I) g c.hom z) *ᵥ (⇑v)) := by
    intro v hv
    let w : E := ∑ i, v i • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i
    have hcoeff : modelCoeffMin (E := E) ≤ ‖w‖ :=
      modelCoeffMin_le (E := E) v hv
    have haw : a ≤ (1 / 2 : Real) * ‖w‖ ^ 2 := by
      dsimp only [a]
      nlinarith [modelCoeffMin_pos (E := E), norm_nonneg w]
    have hmetric :
        c.metric g z w w =
          g.inner (c.hom z)
            (∑ i, v i •
              mfderiv (modelWithCornersSelf Real E) I c.hom z
                ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i))
            (∑ i, v i •
              mfderiv (modelWithCornersSelf Real E) I c.hom z
                ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)) := by
      have hD :
          mfderiv (modelWithCornersSelf Real E) I c.hom z w =
            ∑ i, v i •
              mfderiv (modelWithCornersSelf Real E) I c.hom z
                ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i) := by
        have hD' :
            (mfderiv (modelWithCornersSelf Real E) I c.hom z)
                ((tangentSpaceModelContinuousLinearEquiv
                  (I := modelWithCornersSelf Real E) z).symm w) =
              ∑ i, v i •
                (mfderiv (modelWithCornersSelf Real E) I c.hom z)
                  ((tangentSpaceModelContinuousLinearEquiv
                    (I := modelWithCornersSelf Real E) z).symm
                    ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)) := by
          simp only [w, map_sum, map_smul]
        simpa only [tangentSpaceModelContinuousLinearEquiv_symm_apply] using hD'
      rw [NormalBallChart.metric_apply]
      exact congrArg₂ (fun a b => g.inner (c.hom z) a b) hD hD
    have hquad :=
      paramGramMatrix_dotProduct_mulVec (I := I) g c.hom z (⇑v)
    have hfinal :
        a ≤ _root_.Star.star (⇑v) ⬝ᵥ
          (paramGramMatrix (I := I) g c.hom z) *ᵥ (⇑v) := by
      calc
      a ≤ (1 / 2 : Real) * ‖w‖ ^ 2 := haw
      _ ≤ c.metric g z w w := (heq z hz w).1
      _ = g.inner (c.hom z)
          (∑ i, v i •
            mfderiv (modelWithCornersSelf Real E) I c.hom z
              ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i))
          (∑ i, v i •
            mfderiv (modelWithCornersSelf Real E) I c.hom z
              ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)) := hmetric
      _ = _root_.Star.star (⇑v) ⬝ᵥ
          (paramGramMatrix (I := I) g c.hom z) *ᵥ (⇑v) := hquad.symm
    simpa using hfinal
  simpa only [a, paramDensity_apply, Fintype.card_fin] using
    (sqrt_pow_le_sqrt_det_of_rayleigh
      (ι := Fin (Module.finrank Real E))
      (A := paramGramMatrix (I := I) g c.hom z) (a := a)
      hgram.posSemidef ha hray)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.param_dens_ge then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.VolumeComparison.param_dens_ge"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.param_dens_ge ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.param_dens_ge

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem intrinsicBall_vol_ge
    [PseudoEMetricSpace M]
    [_root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) {r : Real} (hr : 0 < r)
    (c : IntrinsicBallChart (I := I) g hEnorm p r)
    (hmetric : ∀ z ∈ Metric.ball (0 : E) r, ∀ v : E,
      (1 / 2 : Real) * ‖v‖ ^ 2 ≤
          intrinsicFrameMetric (I := I) g hEnorm p z v v ∧
        intrinsicFrameMetric (I := I) g hEnorm p z v v ≤
          2 * ‖v‖ ^ 2) :
    ENNReal.ofReal
        (Real.sqrt
          (((1 / 2 : Real) * modelCoeffMin (E := E) ^ 2) ^
            Module.finrank Real E)) *
        (modelHaar (E := E)) (Metric.ball (0 : E) r) ≤
      riemannianVolumeMeasure (I := I) (M := M) g
        (smallNormalBall (I := I) p r) := by
  have hMetricNorm : IsMetricNorm (I := I) (M := M) g := by
    unfold IsMetricNorm
    exact hEnorm
  let nc : NormalBallChart (I := I) p :=
    c.toNormalBallChart (I := I) g hEnorm p hr
  have hnc_radius : nc.radius = r := by
    dsimp only [nc]
    unfold IntrinsicBallChart.toNormalBallChart
    rfl
  have heq :
      nc.MetricEquivOn g (Metric.ball (0 : E) nc.radius) := by
    intro z hz v
    change z ∈ Metric.ball (0 : E) r at hz
    have hev :
        c.hom =ᶠ[nhds z]
          intrinsicFramedExp (I := I) g hEnorm p :=
      Filter.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hz)
        (fun q hq => c.hom_eq hq)
    have hD :
        mfderiv (modelWithCornersSelf Real E) I c.hom z =
          mfderiv (modelWithCornersSelf Real E) I
            (intrinsicFramedExp (I := I) g hEnorm p) z :=
      Filter.EventuallyEq.mfderiv_eq
        (I := modelWithCornersSelf Real E) (I' := I) hev
    change
      (1 / 2 : Real) * ‖v‖ ^ 2 ≤
          g.inner (c.hom z)
            (mfderiv (modelWithCornersSelf Real E) I c.hom z v)
            (mfderiv (modelWithCornersSelf Real E) I c.hom z v) ∧
        g.inner (c.hom z)
            (mfderiv (modelWithCornersSelf Real E) I c.hom z v)
            (mfderiv (modelWithCornersSelf Real E) I c.hom z v) ≤
          2 * ‖v‖ ^ 2
    rw [c.hom_eq hz, hD]
    simpa only [intrinsicFrameMetric_apply] using hmetric z hz v
  have hparam :
      ENNReal.ofReal
          (Real.sqrt
            (((1 / 2 : Real) * modelCoeffMin (E := E) ^ 2) ^
              Module.finrank Real E)) *
          (modelHaar (E := E)) (Metric.ball (0 : E) r) ≤
        riemannianVolumeMeasure (I := I) (M := M) g
          (nc.hom '' Metric.ball (0 : E) r) := by
    apply param_vol_ge (I := I) g nc.hom measurableSet_ball
    · rw [← hnc_radius]
      exact nc.ball_subset
    · intro z hz
      apply param_dens_ge (I := I) g nc heq
      rw [hnc_radius]
      exact hz
  have himage :
      nc.hom '' Metric.ball (0 : E) r ⊆
        smallNormalBall (I := I) p r := by
    rintro y ⟨z, hz, rfl⟩
    change c.hom z ∈ smallNormalBall (I := I) p r
    rw [c.hom_eq hz, intrinsicFrame_apply]
    apply smallNormalBall_radial_confined (I := I) g hMetricNorm p
    · simpa only [normalFrame_sqrt, Metric.mem_ball, dist_zero_right] using hz
    · exact ⟨zero_le_one, le_rfl⟩
  exact hparam.trans (_root_.MeasureTheory.measure_mono himage)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.intrinsicBall_vol_ge then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.VolumeComparison.intrinsicBall_vol_ge"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.intrinsicBall_vol_ge ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.intrinsicBall_vol_ge

end VolumeComparison
end Riemannian
end Geometry
end DifferentialGeometry
