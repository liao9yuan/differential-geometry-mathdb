import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AsymptoticVolumeRatio
import Submission.DifferentialGeometry.Geometry.Comparison.Volume.Bishop.Ball
import Submission.DifferentialGeometry.Geometry.Comparison.Volume.Ball.Basic
import Submission.DifferentialGeometry.Geometry.Comparison.Convexity.Geodesic
import Submission.DifferentialGeometry.Geometry.Comparison.InjectivityRadius.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

open _root_.Metric _root_.Set _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.ENNReal _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.ContDiff

open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Exponential
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open _root_.Submission.DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  [T2Space (TangentBundle I M)]

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instBorelSpace_differentialGeometry target :: scope.openDecls } }

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem smoothFramedBall_eq_small
    [_root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) {R : Real} (hR : 0 < R)
    (hRexp : R < expDiffeoRadius (I := I) g hEnorm p) :
    framedExpDiffeo (I := I) g p '' _root_.Metric.ball (0 : E) R =
      smallNormalBall (I := I) p R := by
  classical
  ext q
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hzNorm : ‖z‖ < R := by
      simpa only [_root_.Metric.mem_ball, dist_zero_right] using hz
    have hzExp : ‖z‖ < expDiffeoRadius (I := I) g hEnorm p :=
      hzNorm.trans hRexp
    have hvExp : Real.sqrt
        (g.inner p (normalFrame (I := I) g p z)
          (normalFrame (I := I) g p z)) <
        expDiffeoRadius (I := I) g hEnorm p := by
      simpa only [normalFrame_sqrt] using hzExp
    have hvSrc := expDiffeo_mem_of_lt (I := I) g hEnorm p hvExp
    have hvGp : Real.sqrt
        (g.inner p (normalFrame (I := I) g p z)
          (normalFrame (I := I) g p z)) < metricCoerciveExpRadius (I := I) g p :=
      hvExp.trans_le (min_le_right _ _)
    have hzFramedSrc : z ∈ (framedExpDiffeo (I := I) g p).source := by
      rw [framedExp_source]
      exact hvSrc
    rw [mem_smallNormalBall, framedExp_eq_expMap (I := I) g p hzFramedSrc,
      framedExpMap_apply,
      edist_exp_eq_radius (I := I) g p hEnorm hvGp,
      normalFrame_sqrt]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (norm_nonneg z)).2 hzNorm
  · intro hq
    obtain ⟨v, hvExp, hvLen⟩ :=
      hopf_rinow_expMapIntrinsic_surjective_minimizing (I := I) g hEnorm p q
    have hdist : (Manifold.riemannianEDist I p q).toReal < R := by
      have hlt := (ENNReal.toReal_lt_toReal
        (riemannianEDist_ne_top (I := I) p q) ENNReal.ofReal_ne_top).2 hq
      simpa only [ENNReal.toReal_ofReal hR.le] using hlt
    have hvSmall : Real.sqrt (g.inner p (v : E) (v : E)) <
        expDiffeoRadius (I := I) g hEnorm p := by
      rw [hvLen]
      exact hdist.trans hRexp
    let z : E := (normalFrame (I := I) g p).symm v
    have hzFrame : normalFrame (I := I) g p z = v := by
      exact (normalFrame (I := I) g p).apply_symm_apply v
    have hzNorm : ‖z‖ = Real.sqrt (g.inner p (v : E) (v : E)) := by
      have h := normalFrame_sqrt (I := I) g p z
      rw [hzFrame] at h
      exact h.symm
    have hzBall : z ∈ _root_.Metric.ball (0 : E) R := by
      rw [_root_.Metric.mem_ball, dist_zero_right, hzNorm, hvLen]
      exact hdist
    refine ⟨z, hzBall, ?_⟩
    rw [framedExp_apply, hzFrame]
    calc
      expMapDiffeo (I := I) g p
          (tangentSpaceModelContinuousLinearEquiv (I := I) p v) =
          expMapIntrinsic (I := I) g hEnorm p v := by
        with_unfolding_all
          exact expDiffeo_eq_intr (I := I) g hEnorm p hvSmall
      _ = q := hvExp

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.smoothFramedBall_eq_small
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.smoothFramedBall_eq_small target :: scope.openDecls } }

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private def smoothLocalBallVolume
    [_root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) (p : M) (R : Real) : ENNReal :=
  let _ : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  riemannianVolumeMeasure (I := I) (M := M) g (_root_.Metric.ball p R)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.smoothLocalBallVolume
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.smoothLocalBallVolume target :: scope.openDecls } }

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem smoothLocalBall_eq_normal
    [_root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) {R : Real} (hR : 0 < R)
    (hRexp : R < expDiffeoRadius (I := I) g hEnorm p) :
    smoothLocalBallVolume (I := I) g p R =
      riemannianVolumeMeasure (I := I) (M := M) g
        (framedExpDiffeo (I := I) g p '' _root_.Metric.ball (0 : E) R) := by
  let : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  have hball : _root_.Metric.ball p R = smallNormalBall (I := I) p R :=
    Set.Subset.antisymm
      (metricBall_subset_smallNormalBall (I := I) (M := M))
      (smallNormalBall_subset_metricBall (I := I) (M := M))
  rw [smoothLocalBallVolume, hball]
  congr 1
  exact (smoothFramedBall_eq_small (I := I) g hEnorm p hR hRexp).symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.smoothLocalBall_eq_normal
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.smoothLocalBall_eq_normal target :: scope.openDecls } }

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem smoothExistsBallRatio
    [_root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (ε : Real) (hε : 0 < ε) :
    ∃ c : Real,
      c = paramDensity (I := I) g (framedExpDiffeo (I := I) g p) 0 ∧
      0 < c ∧ ∃ ρ : Real, 0 < ρ ∧ ∀ {r : Real}, 0 < r → r < ρ →
        ENNReal.ofReal ((1 - ε) * c) *
            (ENNReal.ofReal (r ^ Module.finrank Real E) *
              (modelHaar (E := E)) (_root_.Metric.ball (0 : E) 1)) ≤
          smoothLocalBallVolume (I := I) g p r ∧
        smoothLocalBallVolume (I := I) g p r ≤
          ENNReal.ofReal ((1 + ε) * c) *
            (ENNReal.ofReal (r ^ Module.finrank Real E) *
              (modelHaar (E := E)) (_root_.Metric.ball (0 : E) 1)) := by
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  let : MeasurableSpace M := borel M
  let : BorelSpace M := ⟨rfl⟩
  let Ψ := framedExpDiffeo (I := I) g p
  let f : E → Real := paramDensity (I := I) g Ψ
  have hzero : (0 : E) ∈ Ψ.source := by
    simpa only [Ψ] using zero_mem_framedExp_source (I := I) g p
  have hfpos : 0 < f 0 := by
    exact paramDensity_pos (I := I) g Ψ hzero
  refine ⟨f 0, by rfl, hfpos, ?_⟩
  have hcont : ContinuousWithinAt f Ψ.source 0 := by
    exact (paramDensity_contOn (I := I) g Ψ) 0 hzero
  obtain ⟨δ, hδ, hclose⟩ :=
    (Metric.continuousWithinAt_iff.mp hcont) (ε * f 0) (mul_pos hε hfpos)
  obtain ⟨s, hs, hsource⟩ := exists_framed_ball (I := I) g p
  let e : Real := expDiffeoRadius (I := I) g hEnorm p
  let ρ : Real := _root_.Min.min δ (_root_.Min.min s e)
  have he : 0 < e := by
    simpa only [e] using expDiffeoRadius_pos (I := I) g hEnorm p
  have hρ : 0 < ρ := by
    simpa only [ρ] using lt_min hδ (lt_min hs he)
  refine ⟨ρ, hρ, ?_⟩
  intro r hr hrρ
  have hrδ : r < δ := hrρ.trans_le (min_le_left _ _)
  have hrs : r < s :=
    hrρ.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hre : r < expDiffeoRadius (I := I) g hEnorm p := by
    simpa only [e] using
      hrρ.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hrsource : _root_.Metric.ball (0 : E) r ⊆ Ψ.source := by
    simpa only [Ψ] using (Metric.ball_subset_ball hrs.le).trans hsource
  have hdens (z : E) (hz : z ∈ _root_.Metric.ball (0 : E) r) :
      (1 - ε) * f 0 ≤ f z ∧ f z ≤ (1 + ε) * f 0 := by
    have hzδ : _root_.Dist.dist z (0 : E) < δ :=
      (Metric.mem_ball.mp hz).trans hrδ
    have hzclose := hclose (hrsource hz) hzδ
    rw [Real.dist_eq] at hzclose
    exact ⟨by nlinarith [neg_lt_of_abs_lt hzclose],
      by nlinarith [lt_of_abs_lt hzclose]⟩
  have hlow :
      ENNReal.ofReal ((1 - ε) * f 0) *
          (modelHaar (E := E)) (_root_.Metric.ball (0 : E) r) ≤
        riemannianVolumeMeasure (I := I) (M := M) g
          (Ψ '' _root_.Metric.ball (0 : E) r) := by
    exact param_vol_ge (I := I) g Ψ measurableSet_ball hrsource
      (fun z hz => (hdens z hz).1)
  have hupp :
      riemannianVolumeMeasure (I := I) (M := M) g
          (Ψ '' _root_.Metric.ball (0 : E) r) ≤
        ENNReal.ofReal ((1 + ε) * f 0) *
          (modelHaar (E := E)) (_root_.Metric.ball (0 : E) r) := by
    rw [riemannianVolumeMeasure_image_param_eq
      (I := I) g Ψ measurableSet_ball hrsource]
    calc
      (∫⁻ z in _root_.Metric.ball (0 : E) r, ENNReal.ofReal (f z)
          ∂(modelHaar (E := E))) ≤
          ∫⁻ _z in _root_.Metric.ball (0 : E) r, ENNReal.ofReal ((1 + ε) * f 0)
            ∂(modelHaar (E := E)) := by
        refine MeasureTheory.setLIntegral_mono' measurableSet_ball ?_
        intro z hz
        exact ENNReal.ofReal_le_ofReal (hdens z hz).2
      _ = ENNReal.ofReal ((1 + ε) * f 0) *
          (modelHaar (E := E)) (_root_.Metric.ball (0 : E) r) := by
        rw [MeasureTheory.setLIntegral_const]
  have hball : smoothLocalBallVolume (I := I) g p r =
      riemannianVolumeMeasure (I := I) (M := M) g
        (Ψ '' _root_.Metric.ball (0 : E) r) := by
    exact smoothLocalBall_eq_normal (I := I) g hEnorm p hr hre
  constructor
  · rw [hball]
    simpa only [f, Ψ, modelHaar_ball (E := E) hr] using hlow
  · rw [hball]
    simpa only [f, Ψ, modelHaar_ball (E := E) hr] using hupp

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.smoothExistsBallRatio
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.smoothExistsBallRatio target :: scope.openDecls } }

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem smoothExistsEuclidRatio
    [_root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (ε : Real) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ ρ : Real, 0 < ρ ∧ ∀ {r : Real}, 0 < r → r < ρ →
      ENNReal.ofReal (1 - ε) *
          (ENNReal.ofReal (r ^ Module.finrank Real E) *
            (MeasureTheory.volume : MeasureTheory.Measure E) (_root_.Metric.ball (0 : E) 1)) ≤
        smoothLocalBallVolume (I := I) g p r ∧
      smoothLocalBallVolume (I := I) g p r ≤
        ENNReal.ofReal (1 + ε) *
          (ENNReal.ofReal (r ^ Module.finrank Real E) *
            (MeasureTheory.volume : MeasureTheory.Measure E) (_root_.Metric.ball (0 : E) 1)) := by
  obtain ⟨c, hc, _hcpos, ρ, hρ, hratio⟩ :=
    smoothExistsBallRatio (I := I) g hEnorm p ε hε
  have hhaar :
      ENNReal.ofReal c * (modelHaar (E := E)) (_root_.Metric.ball (0 : E) 1) =
        (MeasureTheory.volume : MeasureTheory.Measure E) (_root_.Metric.ball (0 : E) 1) := by
    have h := congrArg (fun μ : MeasureTheory.Measure E => μ (_root_.Metric.ball (0 : E) 1))
      (framedDens_haar (I := I) g p)
    simpa only [MeasureTheory.Measure.smul_apply, smul_eq_mul, hc] using h
  have hoflow : ENNReal.ofReal ((1 - ε) * c) =
      ENNReal.ofReal (1 - ε) * ENNReal.ofReal c :=
    ENNReal.ofReal_mul (sub_nonneg.mpr hε1.le)
  have hofupp : ENNReal.ofReal ((1 + ε) * c) =
      ENNReal.ofReal (1 + ε) * ENNReal.ofReal c :=
    ENNReal.ofReal_mul (by positivity)
  refine ⟨ρ, hρ, ?_⟩
  intro r hr hrρ
  obtain ⟨hlow, hupp⟩ := hratio hr hrρ
  constructor
  · calc
      ENNReal.ofReal (1 - ε) *
          (ENNReal.ofReal (r ^ Module.finrank Real E) *
            (MeasureTheory.volume : MeasureTheory.Measure E) (_root_.Metric.ball (0 : E) 1)) =
          ENNReal.ofReal ((1 - ε) * c) *
            (ENNReal.ofReal (r ^ Module.finrank Real E) *
              (modelHaar (E := E)) (_root_.Metric.ball (0 : E) 1)) := by
        rw [hoflow, ← hhaar]
        simp only [mul_assoc, mul_comm, mul_left_comm]
      _ ≤ smoothLocalBallVolume (I := I) g p r := hlow
  · calc
      smoothLocalBallVolume (I := I) g p r ≤
          ENNReal.ofReal ((1 + ε) * c) *
            (ENNReal.ofReal (r ^ Module.finrank Real E) *
              (modelHaar (E := E)) (_root_.Metric.ball (0 : E) 1)) := hupp
      _ = ENNReal.ofReal (1 + ε) *
          (ENNReal.ofReal (r ^ Module.finrank Real E) *
            (MeasureTheory.volume : MeasureTheory.Measure E) (_root_.Metric.ball (0 : E) 1)) := by
        rw [hofupp, ← hhaar]
        simp only [mul_assoc, mul_comm, mul_left_comm]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.smoothExistsEuclidRatio
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.smoothExistsEuclidRatio target :: scope.openDecls } }

private theorem model_unitBall_volume_eq :
    (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) (Metric.ball (0 : E) 1) =
      euclideanUnitBallVolume (Module.finrank ℝ E) := by
  let : Nontrivial E := Module.nontrivial_of_finrank_pos
    (Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E)))
  let : Nonempty (Fin (Module.finrank ℝ E)) :=
    Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E)))
  simp only [euclideanUnitBallVolume, InnerProductSpace.volume_ball,
    finrank_euclideanSpace, Fintype.card_fin]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.model_unitBall_volume_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.model_unitBall_volume_eq target :: scope.openDecls } }

variable [ConnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem riemannianBallOf_volume_small_radius_bounds
    (g : SmoothRiemannianMetric I M) (hcomplete : RiemannianMetricComplete g)
    (p : M) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ r : ℝ, 0 < r → r < ρ →
      ENNReal.ofReal (1 - ε) *
          (euclideanUnitBallVolume (Module.finrank ℝ E) *
            ENNReal.ofReal (r ^ Module.finrank ℝ E)) ≤
        riemannianVolumeMeasure (I := I) (M := M) g (riemannianBallOf g p r) ∧
      riemannianVolumeMeasure (I := I) (M := M) g (riemannianBallOf g p r) ≤
        ENNReal.ofReal (1 + ε) *
          (euclideanUnitBallVolume (Module.finrank ℝ E) *
            ENNReal.ofReal (r ^ Module.finrank ℝ E)) := by
  let : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  let : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let : CompleteSpace M := hcomplete.complete
  have hEnorm : IsMetricNorm (I := I) g := fun x v =>
    tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g x v
  have hvolume (r : ℝ) : smoothLocalBallVolume (I := I) g p r =
      riemannianVolumeMeasure (I := I) (M := M) g (riemannianBallOf g p r) := by
    let : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    change riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p r) = _
    congr 1
    ext z
    simp only [Metric.mem_ball, riemannianBallOf, Set.mem_ofPred_eq]
    rw [dist_comm, HopfRinow.riemMetric_dist_eq (I := I)]
    change (Manifold.riemannianEDist I p z).toReal < r ↔
      Manifold.riemannianEDist I p z < ENNReal.ofReal r
    exact (ENNReal.lt_ofReal_iff_toReal_lt
      (riemannianEDist_ne_top (I := I) p z)).symm
  obtain ⟨ρ, hρ, hbounds⟩ := smoothExistsEuclidRatio (I := I) g hEnorm p ε hε hε1
  refine ⟨ρ, hρ, ?_⟩
  intro r hr hrρ
  simpa only [hvolume, model_unitBall_volume_eq, mul_comm] using hbounds hr hrρ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.riemannianBallOf_volume_small_radius_bounds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.riemannianBallOf_volume_small_radius_bounds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.riemannianBallOf_volume_small_radius_bounds ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.riemannianBallOf_volume_small_radius_bounds

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
