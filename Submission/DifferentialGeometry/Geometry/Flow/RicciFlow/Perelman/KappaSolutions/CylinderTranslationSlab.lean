import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CoverBallVolume
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CrossVolumeNaturality
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.RiemannianProduct
import Submission.DifferentialGeometry.Geometry.Metric.Sphere.Round.Metric
import Submission.DifferentialGeometry.Topology.Covering.DeckAction
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Algebra.Order.Floor.Ring

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
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Topology
open _root_.Submission.DifferentialGeometry.Integral.Measure
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal

private theorem cylinderSlab_image_eq_range {X Y : Type*}
    (q : X × ℝ → Y) (A : X ≃ X) (c : ℝ) (hc : c ≠ 0)
    (hdeck : ∀ x s, q (A x, s + c) = q (x, s)) :
    q '' (_root_.Set.univ ×ˢ _root_.Set.Ioo (-|c|) |c|) = _root_.Set.range q := by
  let fibers : ℝ → Set Y := fun s => _root_.Set.range (fun x : X => q (x, s))
  have hperiod : Function.Periodic fibers c := by
    intro s
    ext z
    constructor
    · rintro ⟨x, hx⟩
      refine ⟨A.symm x, ?_⟩
      exact (hdeck (A.symm x) s).symm.trans (by simpa only [A.apply_symm_apply] using hx)
    · rintro ⟨x, hx⟩
      exact ⟨A x, (hdeck x s).trans hx⟩
  have hperiodAbs : Function.Periodic fibers |c| := by
    by_cases hc0 : 0 ≤ c
    · simpa only [abs_of_nonneg hc0] using hperiod
    · simpa only [abs_of_neg (lt_of_not_ge hc0)] using hperiod.neg
  have hpos : 0 < |c| := abs_pos.mpr hc
  apply Subset.antisymm
  · rintro z ⟨p, _, hp⟩
    exact ⟨p, hp⟩
  · rintro z ⟨⟨x, s⟩, rfl⟩
    let u := s - (⌊s / |c|⌋ : ℤ) * |c|
    have hu0 : 0 ≤ u := Int.sub_floor_div_mul_nonneg s hpos
    have huL : u < |c| := Int.sub_floor_div_mul_lt s hpos
    have hfu : fibers u = fibers s := hperiodAbs.sub_int_mul_eq ⌊s / |c|⌋
    have hx : q (x, s) ∈ fibers s := ⟨x, rfl⟩
    rw [← hfu] at hx
    obtain ⟨y, hy⟩ := hx
    exact ⟨(y, u), ⟨mem_univ _, by change -|c| < u ∧ u < |c|; exact ⟨by linarith, huL⟩⟩, hy⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderSlab_image_eq_range
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderSlab_image_eq_range target :: scope.openDecls } }

private theorem cylinderSlab_cast_apply {X : Type*}
    {m₁ m₂ : MeasurableSpace X} (hm : m₁ = m₂) (mu : @_root_.MeasureTheory.Measure X m₁) (U : Set X) :
    (cast (congrArg (fun m : MeasurableSpace X => @_root_.MeasureTheory.Measure X m) hm) mu) U = mu U := by
  cases hm
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderSlab_cast_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderSlab_cast_apply target :: scope.openDecls } }

local notation "SphereTwo" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

private local instance cylinderSlabSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderSlabSphereDimension
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderSlabSphereDimension target :: scope.openDecls } }

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [LocallyPathConnectedSpace M] [SemilocallySimplyConnectedSpace M] [Inhabited M]

private local instance cylinderSlabMeasurable : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderSlabMeasurable
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderSlabMeasurable target :: scope.openDecls } }
private local instance cylinderSlabBorel : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderSlabBorel
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderSlabBorel target :: scope.openDecls } }
private local instance cylinderSlabLiftMeasurable : MeasurableSpace (UniversalCover M) :=
  borel (UniversalCover M)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderSlabLiftMeasurable
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderSlabLiftMeasurable target :: scope.openDecls } }
private local instance cylinderSlabLiftBorel : BorelSpace (UniversalCover M) := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderSlabLiftBorel
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderSlabLiftBorel target :: scope.openDecls } }
private local instance cylinderSlabSphereMeasurable : MeasurableSpace SphereTwo := borel SphereTwo

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderSlabSphereMeasurable
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderSlabSphereMeasurable target :: scope.openDecls } }
private local instance cylinderSlabSphereBorel : BorelSpace SphereTwo := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderSlabSphereBorel
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderSlabSphereBorel target :: scope.openDecls } }
private local instance cylinderSlabProductMeasurable : MeasurableSpace (SphereTwo × ℝ) :=
  borel (SphereTwo × ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderSlabProductMeasurable
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderSlabProductMeasurable target :: scope.openDecls } }
private local instance cylinderSlabProductBorel : BorelSpace (SphereTwo × ℝ) := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderSlabProductBorel
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderSlabProductBorel target :: scope.openDecls } }
private local instance cylinderSlabC1 : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderSlabC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderSlabC1 target :: scope.openDecls } }

omit [CompleteSpace E] in
theorem cylinderDeck_translation_total_volume_le
    (g : SmoothRiemannianMetric I M)
    (h : SmoothRiemannianMetric (𝓡 2) SphereTwo)
    (Psi : (SphereTwo × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), I⟯ UniversalCover M)
    (hproduct : ∀ (x : SphereTwo) (s : ℝ)
      (v w : TangentSpace (𝓡 2) x) (a b : ℝ),
      (UniversalCover.liftedMetric (I := I) g).inner (Psi (x, s))
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Psi (x, s) (v, a))
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Psi (x, s) (w, b)) =
        h.inner x v w + a * b)
    (gamma : FundamentalGroup M (_root_.Inhabited.default : M)) (A : SphereTwo ≃ SphereTwo)
    (c : ℝ) (hc : c ≠ 0)
    (hdeck : ∀ (x : SphereTwo) (s : ℝ),
      gamma • Psi (x, s) = Psi (A x, s + c)) :
    riemannianVolumeMeasure (I := I) (M := M) g _root_.Set.univ ≤
      ENNReal.ofReal (2 * |c|) *
        riemannianVolumeMeasure (I := 𝓡 2) (M := SphereTwo) h univ := by
  let _ : SecondCountableTopology H := I.secondCountableTopology
  let _ : SecondCountableTopology M :=
    ChartedSpace.secondCountable_of_sigmaCompact H M
  let _ : PathConnectedSpace M :=
    PathConnectedSpace.of_locallyPathConnectedSpace
  let _ : SigmaCompactSpace (UniversalCover M) :=
    Psi.toHomeomorph.symm.isClosedEmbedding.sigmaCompactSpace
  let q : SphereTwo × ℝ → M := fun p => UniversalCover.proj (Psi p)
  let U : Set (SphereTwo × ℝ) := _root_.Set.univ ×ˢ _root_.Set.Ioo (-|c|) |c|
  let gP := Diffeomorph.pullbackMetricCross (UniversalCover.liftedMetric (I := I) g) Psi
  have hqdeck : ∀ x s, q (A x, s + c) = q (x, s) := by
    intro x s
    change UniversalCover.proj (Psi (A x, s + c)) = UniversalCover.proj (Psi (x, s))
    rw [← hdeck x s, UniversalCover.proj_deckAct]
  have hqsurj : Function.Surjective q := by
    intro y
    let y' : UniversalCover M :=
      ⟨y, Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath (_root_.Inhabited.default : M) y)⟩
    refine ⟨Psi.symm y', ?_⟩
    change UniversalCover.proj (Psi (Psi.symm y')) = y
    rw [Psi.apply_symm_apply]
    rfl
  have hqU : q '' U = univ :=
    (cylinderSlab_image_eq_range q A c hc hqdeck).trans (range_eq_univ.mpr hqsurj)
  have hU : IsOpen U := isOpen_univ.prod isOpen_Ioo
  have himage : (UniversalCover.proj : UniversalCover M → M) ''
      ((Psi : SphereTwo × ℝ → UniversalCover M) '' U) = univ := by
    rw [← _root_.Set.image_comp]
    exact hqU
  have hcover := universalCover_volume_image_le g
    ((Psi : SphereTwo × ℝ → UniversalCover M) '' U) (Psi.toHomeomorph.isOpenMap U hU)
  rw [himage] at hcover
  have hPhiMeas : MeasurableEmbedding (Psi : SphereTwo × ℝ → UniversalCover M) :=
    Psi.toHomeomorph.toMeasurableEquiv.measurableEmbedding
  have hvolume := (volumeMeasurePreserving_pullbackMetricCross
    (UniversalCover.liftedMetric (I := I) g) Psi).measure_preimage_emb hPhiMeas
      ((Psi : SphereTwo × ℝ → UniversalCover M) '' U)
  have hpre : (Psi : SphereTwo × ℝ → UniversalCover M) ⁻¹'
      ((Psi : SphereTwo × ℝ → UniversalCover M) '' U) = U :=
    Set.preimage_image_eq U
      (show Function.Injective (Psi : SphereTwo × ℝ → UniversalCover M) from Psi.injective)
  rw [hpre] at hvolume
  have hprod : ∀ (p : SphereTwo × ℝ)
      (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) p),
      gP.inner p v w = h.inner p.1 v.1 w.1 + v.2 * w.2 := by
    intro p v w
    change (Diffeomorph.pullbackMetricCross (UniversalCover.liftedMetric (I := I) g) Psi).inner
      p v w = _
    rw [Diffeomorph.pullbackMetricCross_inner]
    exact hproduct p.1 p.2 v.1 w.1 v.2 w.2
  have hprodSeparate : ∀ (x : SphereTwo) (s : ℝ)
      (v w : TangentSpace (𝓡 2) x) (a b : ℝ),
      gP.inner (x, s) (v, a) (w, b) = h.inner x v w + a * b :=
    fun x s v w a b => hprod (x, s) (v, a) (w, b)
  calc
    riemannianVolumeMeasure (I := I) (M := M) g _root_.Set.univ ≤
        riemannianVolumeMeasure (I := I) (M := UniversalCover M)
          (UniversalCover.liftedMetric (I := I) g)
          ((Psi : SphereTwo × ℝ → UniversalCover M) '' U) := hcover
    _ = riemannianVolumeMeasure (I := (𝓡 2).prod 𝓘(ℝ, ℝ))
        (M := SphereTwo × ℝ) gP U := hvolume.symm
    _ = ENNReal.ofReal (2 * |c|) *
        riemannianVolumeMeasure (I := 𝓡 2) (M := SphereTwo) h univ := by
      rw [riemannianVolumeMeasure_product_real_of_inner_eq h gP hprodSeparate,
        cylinderSlab_cast_apply
          (@BorelSpace.measurable_eq (SphereTwo × ℝ) _
            (@Prod.instMeasurableSpace SphereTwo ℝ _ _) inferInstance)]
      change ((riemannianVolumeMeasure (I := 𝓡 2) (M := SphereTwo) h).prod
        (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℝ))
        (_root_.Set.univ ×ˢ _root_.Set.Ioo (-|c|) |c|) = _
      rw [Measure.prod_prod, Real.volume_Ioo, sub_neg_eq_add, ← two_mul, mul_comm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderDeck_translation_total_volume_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderDeck_translation_total_volume_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderDeck_translation_total_volume_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderDeck_translation_total_volume_le

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
