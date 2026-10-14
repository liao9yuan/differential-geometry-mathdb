import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AsymptoticVolumeRatio
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CrossModelBallTransport
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SurfaceProductVolume
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CoverBallVolume
import Submission.DifferentialGeometry.Geometry.Metric.Sphere.Round.Metric
import Submission.DifferentialGeometry.Geometry.Comparison.Distance.Continuity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.Submission.Set _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry.Geometry
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Topology
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal

local notation "SphereTwo" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

private local instance cylinderAvrSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderAvrSphereDimension
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderAvrSphereDimension target :: scope.openDecls } }
private local instance cylinderAvrSphereMeasurable : MeasurableSpace SphereTwo := borel SphereTwo

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderAvrSphereMeasurable
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderAvrSphereMeasurable target :: scope.openDecls } }
private local instance cylinderAvrSphereBorel : BorelSpace SphereTwo := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderAvrSphereBorel
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderAvrSphereBorel target :: scope.openDecls } }
private local instance cylinderAvrProductMeasurable : MeasurableSpace (SphereTwo × ℝ) :=
  borel (SphereTwo × ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderAvrProductMeasurable
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderAvrProductMeasurable target :: scope.openDecls } }
private local instance cylinderAvrProductBorel : BorelSpace (SphereTwo × ℝ) := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderAvrProductBorel
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderAvrProductBorel target :: scope.openDecls } }

private theorem cylinderAvr_cast_apply {X : Type*}
    {m₁ m₂ : MeasurableSpace X} (hm : m₁ = m₂) (mu : @_root_.MeasureTheory.Measure X m₁) (U : Set X) :
    (cast (congrArg (fun m : MeasurableSpace X => @_root_.MeasureTheory.Measure X m) hm) mu) U = mu U := by
  cases hm
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderAvr_cast_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderAvr_cast_apply target :: scope.openDecls } }

private theorem cylinderAvr_product_ball_volume_le
    (h : SmoothRiemannianMetric (𝓡 2) SphereTwo)
    (gP : SmoothRiemannianMetric ((𝓡 2).prod 𝓘(ℝ, ℝ)) (SphereTwo × ℝ))
    (hprod : ∀ (p : SphereTwo × ℝ)
      (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) p),
      gP.inner p v w = h.inner p.1 v.1 w.1 + v.2 * w.2)
    (p : SphereTwo × ℝ) (r : ℝ) (hr : 0 < r) :
    riemannianVolumeMeasure (I := (𝓡 2).prod 𝓘(ℝ, ℝ)) (M := SphereTwo × ℝ) gP
        (riemannianBallOf gP p r) ≤
      ENNReal.ofReal (2 * r) *
        riemannianVolumeMeasure (I := 𝓡 2) (M := SphereTwo) h univ := by
  have hball : riemannianBallOf gP p r ⊆ _root_.Set.univ ×ˢ _root_.Set.Ioo (p.2 - r) (p.2 + r) := by
    intro q hq
    refine ⟨mem_univ _, ?_⟩
    have hline : _root_.EDist.edist p.2 q.2 < ENNReal.ofReal r :=
      lt_of_le_of_lt (surfaceProduct_snd_edist_le h gP hprod p q) hq
    rw [edist_dist, Real.dist_eq] at hline
    have habs := abs_lt.mp ((ENNReal.ofReal_lt_ofReal_iff hr).mp hline)
    change p.2 - r < q.2 ∧ q.2 < p.2 + r
    constructor <;> linarith [habs.1, habs.2]
  have hproduct : ∀ (y : SphereTwo) (s : ℝ)
      (v w : TangentSpace (𝓡 2) y) (a b : ℝ),
      gP.inner (y, s) (v, a) (w, b) = h.inner y v w + a * b :=
    fun y s v w a b => hprod (y, s) (v, a) (w, b)
  calc
    riemannianVolumeMeasure (I := (𝓡 2).prod 𝓘(ℝ, ℝ)) (M := SphereTwo × ℝ) gP
        (riemannianBallOf gP p r) ≤
        riemannianVolumeMeasure (I := (𝓡 2).prod 𝓘(ℝ, ℝ)) (M := SphereTwo × ℝ) gP
          (_root_.Set.univ ×ˢ _root_.Set.Ioo (p.2 - r) (p.2 + r)) := _root_.MeasureTheory.measure_mono hball
    _ = riemannianVolumeMeasure (I := 𝓡 2) (M := SphereTwo) h _root_.Set.univ *
        (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℝ) (_root_.Set.Ioo (p.2 - r) (p.2 + r)) := by
      rw [riemannianVolumeMeasure_product_real_of_inner_eq h gP hproduct,
        cylinderAvr_cast_apply
          (@BorelSpace.measurable_eq (SphereTwo × ℝ) _
            (@Prod.instMeasurableSpace SphereTwo ℝ _ _) inferInstance),
        Measure.prod_prod]
    _ = ENNReal.ofReal (2 * r) *
        riemannianVolumeMeasure (I := 𝓡 2) (M := SphereTwo) h univ := by
      rw [Real.volume_Ioo]
      have hlength : (p.2 + r) - (p.2 - r) = 2 * r := by ring
      rw [hlength, mul_comm]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderAvr_product_ball_volume_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderAvr_product_ball_volume_le target :: scope.openDecls } }

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [LocallyPathConnectedSpace M] [SemilocallySimplyConnectedSpace M] [Inhabited M]

omit [CompleteSpace E] [T2Space M] [ConnectedSpace M] [LocallyPathConnectedSpace M]
  [SemilocallySimplyConnectedSpace M] [Inhabited M] in
private theorem cylinderAvrSecondCountable (I : ModelWithCorners ℝ E H) :
    SecondCountableTopology M := by
  let _ : SecondCountableTopology H := I.secondCountableTopology
  exact ChartedSpace.secondCountable_of_sigmaCompact H M

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderAvrSecondCountable
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderAvrSecondCountable target :: scope.openDecls } }
private local instance cylinderAvrMeasurable : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderAvrMeasurable
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderAvrMeasurable target :: scope.openDecls } }
private local instance cylinderAvrBorel : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderAvrBorel
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderAvrBorel target :: scope.openDecls } }
private local instance cylinderAvrLiftMeasurable : MeasurableSpace (UniversalCover M) :=
  borel (UniversalCover M)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderAvrLiftMeasurable
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderAvrLiftMeasurable target :: scope.openDecls } }
private local instance cylinderAvrLiftBorel : BorelSpace (UniversalCover M) := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderAvrLiftBorel
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderAvrLiftBorel target :: scope.openDecls } }
private local instance cylinderAvrC1 : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderAvrC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderAvrC1 target :: scope.openDecls } }

omit [CompleteSpace E] in
theorem cylinderCover_ball_volume_le
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric (𝓡 2) SphereTwo)
    (Psi : (SphereTwo × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), I⟯ UniversalCover M)
    (hproduct : ∀ (x : SphereTwo) (s : ℝ)
      (v w : TangentSpace (𝓡 2) x) (a b : ℝ),
      (UniversalCover.liftedMetric (I := I) g).inner (Psi (x, s))
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Psi (x, s) (v, a))
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Psi (x, s) (w, b)) =
        h.inner x v w + a * b)
    (p : M) (r : ℝ) (hr : 0 < r) :
    riemannianVolumeMeasure (I := I) (M := M) g (riemannianBallOf g p r) ≤
      ENNReal.ofReal (2 * r) *
        riemannianVolumeMeasure (I := 𝓡 2) (M := SphereTwo) h univ := by
  let _ : SecondCountableTopology M := cylinderAvrSecondCountable (I := I)
  let _ : PathConnectedSpace M := PathConnectedSpace.of_locallyPathConnectedSpace
  let p' : UniversalCover M :=
    ⟨p, Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath (_root_.Inhabited.default : M) p)⟩
  let u := Psi.symm p'
  let gLift := UniversalCover.liftedMetric (I := I) g
  let gP := Diffeomorph.pullbackMetricCross gLift Psi
  have hprod : ∀ (q : SphereTwo × ℝ)
      (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) q),
      gP.inner q v w = h.inner q.1 v.1 w.1 + v.2 * w.2 := by
    intro q v w
    change (Diffeomorph.pullbackMetricCross (UniversalCover.liftedMetric (I := I) g) Psi).inner
      q v w = _
    rw [Diffeomorph.pullbackMetricCross_inner]
    exact hproduct q.1 q.2 v.1 w.1 v.2 w.2
  have hopen : IsOpen (riemannianBallOf gLift p' r) :=
    isOpen_lt (continuous_riemannianEDist (I := I) gLift p') continuous_const
  have himage : (UniversalCover.proj : UniversalCover M → M) ''
      riemannianBallOf gLift p' r = riemannianBallOf g p r :=
    universalCover_image_ball_liftedMetric g p' r hr
  have hcover := universalCover_volume_image_le g (riemannianBallOf gLift p' r) hopen
  rw [himage] at hcover
  have hcross := riemannianBallOf_volume_pullbackMetricCross gLift Psi u r
  have hPu : Psi u = p' := Psi.apply_symm_apply p'
  rw [hPu] at hcross
  calc
    riemannianVolumeMeasure (I := I) (M := M) g (riemannianBallOf g p r) ≤
        riemannianVolumeMeasure (I := I) (M := UniversalCover M) gLift
          (riemannianBallOf gLift p' r) := hcover
    _ = riemannianVolumeMeasure (I := (𝓡 2).prod 𝓘(ℝ, ℝ)) (M := SphereTwo × ℝ) gP
        (riemannianBallOf gP u r) := hcross.symm
    _ ≤ ENNReal.ofReal (2 * r) *
        riemannianVolumeMeasure (I := 𝓡 2) (M := SphereTwo) h univ :=
      cylinderAvr_product_ball_volume_le h gP hprod u r hr

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderCover_ball_volume_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderCover_ball_volume_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderCover_ball_volume_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderCover_ball_volume_le

omit [CompleteSpace E] in
theorem cylinderCover_asymptoticVolumeRatio_eq_zero
    (g : SmoothRiemannianMetric I M) (hdim : Module.finrank ℝ E = 3)
    (h : SmoothRiemannianMetric (𝓡 2) SphereTwo)
    (Psi : (SphereTwo × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), I⟯ UniversalCover M)
    (hproduct : ∀ (x : SphereTwo) (s : ℝ)
      (v w : TangentSpace (𝓡 2) x) (a b : ℝ),
      (UniversalCover.liftedMetric (I := I) g).inner (Psi (x, s))
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Psi (x, s) (v, a))
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Psi (x, s) (w, b)) =
        h.inner x v w + a * b)
    (p : M) : asymptoticVolumeRatio g p = 0 := by
  let _ : _root_.MeasureTheory.IsFiniteMeasure (riemannianVolumeMeasure (I := 𝓡 2) (M := SphereTwo) h) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace h
  let area : ℝ := (riemannianVolumeMeasure (I := 𝓡 2) (M := SphereTwo) h _root_.Set.univ).toReal
  have harea : 0 ≤ area := ENNReal.toReal_nonneg
  have hareal : riemannianVolumeMeasure (I := 𝓡 2) (M := SphereTwo) h _root_.Set.univ =
      ENNReal.ofReal area :=
    (ENNReal.ofReal_toReal (_root_.MeasureTheory.measure_ne_top _ _)).symm
  let omega : ℝ := (euclideanUnitBallVolume 3).toReal
  have homega : 0 < omega := ENNReal.toReal_pos
    (euclideanUnitBallVolume_pos 3).ne' (euclideanUnitBallVolume_ne_top 3)
  have hwreal : euclideanUnitBallVolume 3 = ENNReal.ofReal omega :=
    (ENNReal.ofReal_toReal (euclideanUnitBallVolume_ne_top 3)).symm
  apply le_antisymm ?_ bot_le
  apply ENNReal.le_of_forall_pos_le_add
  intro eps heps _
  have hepsReal : 0 < (eps : ℝ) := heps
  let r := Real.sqrt (2 * area / (omega * eps)) + 1
  have hr : 0 < r := by dsimp only [r]; positivity
  have hsqrt : Real.sqrt (2 * area / (omega * eps)) ≤ r := by
    dsimp only [r]
    linarith
  have hsquare : 2 * area / (omega * eps) ≤ r ^ 2 := by
    rw [← Real.sq_sqrt (by positivity : 0 ≤ 2 * area / (omega * eps))]
    exact (sq_le_sq₀ (Real.sqrt_nonneg _) hr.le).mpr hsqrt
  have hcoef : 2 * area ≤ r ^ 2 * (omega * eps) :=
    (div_le_iff₀ (mul_pos homega hepsReal)).mp hsquare
  have hreal : 2 * r * area ≤ (eps : ℝ) * (omega * r ^ 3) := by
    calc
      2 * r * area = r * (2 * area) := by ring
      _ ≤ r * (r ^ 2 * (omega * eps)) := mul_le_mul_of_nonneg_left hcoef hr.le
      _ = (eps : ℝ) * (omega * r ^ 3) := by ring
  have hratio : normalizedBallVolumeRatio g p r ≤ (eps : ℝ≥0∞) := by
    unfold normalizedBallVolumeRatio
    rw [hdim]
    apply (ENNReal.div_le_iff
      (mul_ne_zero (euclideanUnitBallVolume_pos 3).ne'
        (ENNReal.ofReal_pos.mpr (pow_pos hr 3)).ne')
      (ENNReal.mul_ne_top (euclideanUnitBallVolume_ne_top 3) ENNReal.ofReal_ne_top)).mpr
    calc
      riemannianVolumeMeasure (I := I) (M := M) g (riemannianBallOf g p r) ≤
          ENNReal.ofReal (2 * r) *
            riemannianVolumeMeasure (I := 𝓡 2) (M := SphereTwo) h univ :=
        cylinderCover_ball_volume_le g h Psi hproduct p r hr
      _ = ENNReal.ofReal (2 * r * area) := by
        rw [hareal, ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * r)]
      _ ≤ ENNReal.ofReal ((eps : ℝ) * (omega * r ^ 3)) := ENNReal.ofReal_le_ofReal hreal
      _ = (eps : ℝ≥0∞) * (euclideanUnitBallVolume 3 * ENNReal.ofReal (r ^ 3)) := by
        rw [ENNReal.ofReal_mul hepsReal.le, ENNReal.ofReal_mul homega.le,
          ENNReal.ofReal_coe_nnreal, ← hwreal]
  simpa only [bot_eq_zero, zero_add] using
    (asymptoticVolumeRatio_le_ratio g p hr).trans hratio

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderCover_asymptoticVolumeRatio_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderCover_asymptoticVolumeRatio_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderCover_asymptoticVolumeRatio_eq_zero ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderCover_asymptoticVolumeRatio_eq_zero

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
