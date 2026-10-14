import Submission.DifferentialGeometry.Geometry.Metric.QuadraticBounds.Unit
import Submission.DifferentialGeometry.Geometry.Connection.MetricCompatibility.Tensor.Metric

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry

open _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry.Tensor0SBundle _root_.Set
open scoped _root_.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M]

def metricTimeBundleQuad
    (G : Real -> SmoothRiemannianMetric I M) (K : Set Real)
    (q : {t : Real // t ∈ K} × TangentBundle I M) : Real :=
  (G q.1.1).inner q.2.proj q.2.2 q.2.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.metricTimeBundleQuad then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.metricTimeBundleQuad"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.metricTimeBundleQuad ``Submission.DifferentialGeometry.metricTimeBundleQuad

def metricUnitTimeSlabRefQuad
    (G : Real -> SmoothRiemannianMetric I M) (K : Set Real)
    (g₀ : SmoothRiemannianMetric I M)
    (q : {t : Real // t ∈ K} × MetricUnitTangent (I := I) (M := M) g₀) :
    Real :=
  (G q.1.1).inner
    (MetricUnitTangent.base (I := I) (M := M) q.2)
    (MetricUnitTangent.vec (I := I) (M := M) q.2)
    (MetricUnitTangent.vec (I := I) (M := M) q.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.metricUnitTimeSlabRefQuad then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.metricUnitTimeSlabRefQuad"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.metricUnitTimeSlabRefQuad ``Submission.DifferentialGeometry.metricUnitTimeSlabRefQuad

omit [FiniteDimensional ℝ E] in
theorem metricUnitTimeSlabRefQuad_cont_of_bundle
    (G : Real -> SmoothRiemannianMetric I M) (K : Set Real)
    (g₀ : SmoothRiemannianMetric I M)
    (hquad : Continuous (metricTimeBundleQuad (I := I) (M := M) G K)) :
    Continuous (metricUnitTimeSlabRefQuad (I := I) (M := M) G K g₀) := by
  let incl :
      ({t : Real // t ∈ K} × MetricUnitTangent (I := I) (M := M) g₀) ->
        {t : Real // t ∈ K} × TangentBundle I M :=
    fun q => (q.1, q.2.1)
  have hincl : Continuous incl := by
    dsimp [incl]
    exact continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  change Continuous (metricTimeBundleQuad (I := I) (M := M) G K ∘ incl)
  exact hquad.comp hincl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.metricUnitTimeSlabRefQuad_cont_of_bundle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.metricUnitTimeSlabRefQuad_cont_of_bundle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.metricUnitTimeSlabRefQuad_cont_of_bundle ``Submission.DifferentialGeometry.metricUnitTimeSlabRefQuad_cont_of_bundle

noncomputable def metricUnitTimeSlabScale
    (G : Real -> SmoothRiemannianMetric I M) (K : Set Real)
    (g₀ : SmoothRiemannianMetric I M)
    (q : {t : Real // t ∈ K} × MetricUnitTangent (I := I) (M := M) g₀) :
    Real :=
  (Real.sqrt (metricUnitTimeSlabRefQuad (I := I) (M := M) G K g₀ q))⁻¹

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.metricUnitTimeSlabScale then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.metricUnitTimeSlabScale"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.metricUnitTimeSlabScale ``Submission.DifferentialGeometry.metricUnitTimeSlabScale

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] in
theorem metricUnitTimeSlabRefQuad_pos
    (G : Real -> SmoothRiemannianMetric I M) (K : Set Real)
    (g₀ : SmoothRiemannianMetric I M)
    (q : {t : Real // t ∈ K} × MetricUnitTangent (I := I) (M := M) g₀) :
    0 < metricUnitTimeSlabRefQuad (I := I) (M := M) G K g₀ q := by
  have hv : MetricUnitTangent.vec (I := I) (M := M) q.2 ≠ 0 := by
    intro hv0
    have hbad := MetricUnitTangent.unit (I := I) (M := M) q.2
    rw [hv0] at hbad
    norm_num at hbad
  exact (G q.1.1).pos
    (MetricUnitTangent.base (I := I) (M := M) q.2)
    (MetricUnitTangent.vec (I := I) (M := M) q.2) hv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.metricUnitTimeSlabRefQuad_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.metricUnitTimeSlabRefQuad_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.metricUnitTimeSlabRefQuad_pos ``Submission.DifferentialGeometry.metricUnitTimeSlabRefQuad_pos

omit [FiniteDimensional ℝ E] in
theorem metricUnitTimeSlabScale_cont
    (G : Real -> SmoothRiemannianMetric I M) (K : Set Real)
    (g₀ : SmoothRiemannianMetric I M)
    (hquad :
      Continuous (metricUnitTimeSlabRefQuad (I := I) (M := M) G K g₀)) :
    Continuous (metricUnitTimeSlabScale (I := I) (M := M) G K g₀) := by
  unfold metricUnitTimeSlabScale
  exact (Real.continuous_sqrt.comp hquad).inv₀
    (fun q => ne_of_gt
      (Real.sqrt_pos.mpr
        (metricUnitTimeSlabRefQuad_pos (I := I) (M := M) G K g₀ q)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.metricUnitTimeSlabScale_cont then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.metricUnitTimeSlabScale_cont"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.metricUnitTimeSlabScale_cont ``Submission.DifferentialGeometry.metricUnitTimeSlabScale_cont

omit [FiniteDimensional ℝ E] in
theorem metricUnitTimeSlabScale_cont_of_bundle
    (G : Real -> SmoothRiemannianMetric I M) (K : Set Real)
    (g₀ : SmoothRiemannianMetric I M)
    (hquad : Continuous (metricTimeBundleQuad (I := I) (M := M) G K)) :
    Continuous (metricUnitTimeSlabScale (I := I) (M := M) G K g₀) :=
  metricUnitTimeSlabScale_cont (I := I) (M := M) G K g₀
    (metricUnitTimeSlabRefQuad_cont_of_bundle (I := I) (M := M) G K g₀ hquad)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.metricUnitTimeSlabScale_cont_of_bundle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.metricUnitTimeSlabScale_cont_of_bundle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.metricUnitTimeSlabScale_cont_of_bundle ``Submission.DifferentialGeometry.metricUnitTimeSlabScale_cont_of_bundle

noncomputable def metricUnitTimeSlabScaledBundle
    (G : Real -> SmoothRiemannianMetric I M) (K : Set Real)
    (g₀ : SmoothRiemannianMetric I M)
    (q : {t : Real // t ∈ K} × MetricUnitTangent (I := I) (M := M) g₀) :
    TangentBundle I M :=
  ⟨MetricUnitTangent.base (I := I) (M := M) q.2,
    metricUnitTimeSlabScale (I := I) (M := M) G K g₀ q •
      MetricUnitTangent.vec (I := I) (M := M) q.2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.metricUnitTimeSlabScaledBundle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.metricUnitTimeSlabScaledBundle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.metricUnitTimeSlabScaledBundle ``Submission.DifferentialGeometry.metricUnitTimeSlabScaledBundle

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] in
theorem metricUnitTimeSlabScaledBundle_unit
    (G : Real -> SmoothRiemannianMetric I M) (K : Set Real)
    (g₀ : SmoothRiemannianMetric I M)
    (q : {t : Real // t ∈ K} × MetricUnitTangent (I := I) (M := M) g₀) :
    (G q.1.1).inner
      (metricUnitTimeSlabScaledBundle (I := I) (M := M) G K g₀ q).proj
      (metricUnitTimeSlabScaledBundle (I := I) (M := M) G K g₀ q).2
      (metricUnitTimeSlabScaledBundle (I := I) (M := M) G K g₀ q).2 = 1 := by
  let r : Real := metricUnitTimeSlabRefQuad (I := I) (M := M) G K g₀ q
  have hrpos : 0 < r := metricUnitTimeSlabRefQuad_pos (I := I) (M := M) G K g₀ q
  let s : Real := Real.sqrt r
  have hspos : 0 < s := Real.sqrt_pos.mpr hrpos
  have hsne : s ≠ 0 := ne_of_gt hspos
  let a : Real := s⁻¹
  let x : M := MetricUnitTangent.base (I := I) (M := M) q.2
  let v : TangentSpace I x := MetricUnitTangent.vec (I := I) (M := M) q.2
  have hss : s * s = r := by
    simpa [sq] using (Real.sq_sqrt (le_of_lt hrpos))
  have haa : a * a * r = 1 := by
    have hmul : (s * s) * (s⁻¹ * s⁻¹) = 1 := by
      field_simp [hsne]
    calc
      a * a * r = (s⁻¹ * s⁻¹) * (s * s) := by
        rw [hss]
      _ = (s * s) * (s⁻¹ * s⁻¹) := by ring
      _ = 1 := hmul
  calc
    (G q.1.1).inner
        (metricUnitTimeSlabScaledBundle (I := I) (M := M) G K g₀ q).proj
        (metricUnitTimeSlabScaledBundle (I := I) (M := M) G K g₀ q).2
        (metricUnitTimeSlabScaledBundle (I := I) (M := M) G K g₀ q).2
        = a * a * r := by
          change (G q.1.1).inner x (a • v) (a • v) = a * a * r
          rw [metric_smul2]
          rfl
    _ = 1 := haa

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.metricUnitTimeSlabScaledBundle_unit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.metricUnitTimeSlabScaledBundle_unit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.metricUnitTimeSlabScaledBundle_unit ``Submission.DifferentialGeometry.metricUnitTimeSlabScaledBundle_unit

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
private theorem tangentBundle_smul_cont :
    Continuous (fun p : Real × TangentBundle I M =>
      (⟨p.2.proj, p.1 • p.2.2⟩ : TangentBundle I M)) := by
  rw [continuous_iff_continuousAt]
  intro p₀
  rw [FiberBundle.continuousAt_totalSpace]
  constructor
  · change ContinuousAt (TotalSpace.proj ∘ Prod.snd) p₀
    exact (((FiberBundle.continuous_proj E (TangentSpace I)).comp
      continuous_snd).continuousAt)
  · let e := _root_.FiberBundle.trivializationAt E (TangentSpace I : M -> Type _) p₀.2.proj
    have hbase :
        e.baseSet ∈ nhds p₀.2.proj :=
      e.open_baseSet.mem_nhds
        (_root_.FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I : M -> Type _) p₀.2.proj)
    have hev :
        ∀ᶠ p : Real × TangentBundle I M in nhds p₀, p.2.proj ∈ e.baseSet :=
      (((FiberBundle.continuous_proj E (TangentSpace I)).comp continuous_snd).continuousAt)
        hbase
    have hcoord :
        ContinuousAt (fun p : Real × TangentBundle I M => (e p.2).2) p₀ := by
      have hp :
          ContinuousAt (fun p : Real × TangentBundle I M => p.2) p₀ :=
        continuous_snd.continuousAt
      exact ((FiberBundle.continuousAt_totalSpace
        (F := E) (E := (TangentSpace I : M -> Type _))
        (f := fun p : Real × TangentBundle I M => p.2)).mp hp).2
    change
      ContinuousAt
        (fun p : Real × TangentBundle I M =>
          (e (⟨p.2.proj, p.1 • p.2.2⟩ : TangentBundle I M)).2) p₀
    refine ContinuousAt.congr (continuousAt_fst.smul hcoord) ?_
    filter_upwards [hev] with p hp
    calc
      p.1 • (e p.2).2
          = p.1 • (e.linearMapAt Real p.2.proj p.2.2) := by
              rw [e.coe_linearMapAt_of_mem (R := Real) hp]
      _ = e.linearMapAt Real p.2.proj (p.1 • p.2.2) := by
              rw [map_smul]
      _ = (e (⟨p.2.proj, p.1 • p.2.2⟩ : TangentBundle I M)).2 := by
              rw [e.coe_linearMapAt_of_mem (R := Real) hp]

run_cmd do
  let target := ``Submission.DifferentialGeometry.tangentBundle_smul_cont
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.tangentBundle_smul_cont target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] in
theorem metricUnitTimeSlabScaledBundle_cont_of_bundle
    (G : Real -> SmoothRiemannianMetric I M) (K : Set Real)
    (g₀ : SmoothRiemannianMetric I M)
    (hquad : Continuous (metricTimeBundleQuad (I := I) (M := M) G K)) :
    Continuous (metricUnitTimeSlabScaledBundle (I := I) (M := M) G K g₀) := by
  have hscale :
      Continuous (metricUnitTimeSlabScale (I := I) (M := M) G K g₀) :=
    metricUnitTimeSlabScale_cont_of_bundle (I := I) (M := M) G K g₀ hquad
  let sourceToPair :
      ({t : Real // t ∈ K} × MetricUnitTangent (I := I) (M := M) g₀) ->
        Real × TangentBundle I M :=
    fun q => (metricUnitTimeSlabScale (I := I) (M := M) G K g₀ q, q.2.1)
  have hpair : Continuous sourceToPair := by
    dsimp [sourceToPair]
    exact hscale.prodMk (continuous_subtype_val.comp continuous_snd)
  change Continuous
    ((fun p : Real × TangentBundle I M ↦
      (⟨p.2.proj, p.1 • p.2.2⟩ : TangentBundle I M)) ∘ sourceToPair)
  exact tangentBundle_smul_cont (I := I) (M := M).comp hpair

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.metricUnitTimeSlabScaledBundle_cont_of_bundle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.metricUnitTimeSlabScaledBundle_cont_of_bundle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.metricUnitTimeSlabScaledBundle_cont_of_bundle ``Submission.DifferentialGeometry.metricUnitTimeSlabScaledBundle_cont_of_bundle

noncomputable def metricUnitTimeSlabParam
    (G : Real -> SmoothRiemannianMetric I M) (K : Set Real)
    (g₀ : SmoothRiemannianMetric I M)
    (q : {t : Real // t ∈ K} × MetricUnitTangent (I := I) (M := M) g₀) :
    MetricUnitTangentTimeSlab (I := I) (M := M) G K := by
  let t : Real := q.1.1
  let x : M := MetricUnitTangent.base (I := I) (M := M) q.2
  let v : TangentSpace I x := MetricUnitTangent.vec (I := I) (M := M) q.2
  have hv : v ≠ 0 := by
    intro hv0
    have hbad : (0 : Real) = 1 := by
      simpa [x, v, hv0] using
        (MetricUnitTangent.unit (I := I) (M := M) q.2)
    norm_num at hbad
  let r : Real := (G t).inner x v v
  have hrpos : 0 < r := (G t).pos x v hv
  let s : Real := Real.sqrt r
  have hspos : 0 < s := Real.sqrt_pos.mpr hrpos
  have hsne : s ≠ 0 := ne_of_gt hspos
  let a : Real := s⁻¹
  let u : TangentSpace I x := a • v
  have hss : s * s = r := by
    simpa [sq] using (Real.sq_sqrt (le_of_lt hrpos))
  have hunit : (G t).inner x u u = 1 := by
    have haa : a * a * r = 1 := by
      have hmul : (s * s) * (s⁻¹ * s⁻¹) = 1 := by
        field_simp [hsne]
      calc
        a * a * r = (s⁻¹ * s⁻¹) * (s * s) := by
          rw [hss]
        _ = (s * s) * (s⁻¹ * s⁻¹) := by ring
        _ = 1 := hmul
    calc
      (G t).inner x u u = a * a * r := by
        simpa [u, r] using metric_smul2 (I := I) (M := M) (G t) a v
      _ = 1 := haa
  exact ⟨(q.1, (⟨x, u⟩ : TangentBundle I M)), hunit⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.metricUnitTimeSlabParam then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.metricUnitTimeSlabParam"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.metricUnitTimeSlabParam ``Submission.DifferentialGeometry.metricUnitTimeSlabParam

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] in
@[simp]
theorem metricUnitTimeSlabParam_time
    (G : Real -> SmoothRiemannianMetric I M) (K : Set Real)
    (g₀ : SmoothRiemannianMetric I M)
    (q : {t : Real // t ∈ K} × MetricUnitTangent (I := I) (M := M) g₀) :
    MetricUnitTangentTimeSlab.time (I := I) (M := M)
      (metricUnitTimeSlabParam (I := I) (M := M) G K g₀ q) = q.1.1 := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.metricUnitTimeSlabParam_time then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.metricUnitTimeSlabParam_time"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.metricUnitTimeSlabParam_time ``Submission.DifferentialGeometry.metricUnitTimeSlabParam_time

omit [FiniteDimensional ℝ E] in
theorem metricUnitTimeSlabParam_cont_of_scaledBundle
    (G : Real -> SmoothRiemannianMetric I M) (K : Set Real)
    (g₀ : SmoothRiemannianMetric I M)
    (hscaled :
      Continuous (metricUnitTimeSlabScaledBundle (I := I) (M := M) G K g₀)) :
    Continuous (metricUnitTimeSlabParam (I := I) (M := M) G K g₀) := by
  let pairMap :
      ({t : Real // t ∈ K} × MetricUnitTangent (I := I) (M := M) g₀) ->
        {t : Real // t ∈ K} × TangentBundle I M :=
    fun q => (q.1, metricUnitTimeSlabScaledBundle (I := I) (M := M) G K g₀ q)
  have hpair : Continuous pairMap := by
    dsimp [pairMap]
    exact continuous_fst.prodMk hscaled
  have hsub :
      Continuous (fun q =>
        (⟨pairMap q,
          metricUnitTimeSlabScaledBundle_unit (I := I) (M := M) G K g₀ q⟩ :
          MetricUnitTangentTimeSlab (I := I) (M := M) G K)) :=
    Continuous.subtype_mk hpair
      (fun q => metricUnitTimeSlabScaledBundle_unit (I := I) (M := M) G K g₀ q)
  refine hsub.congr ?_
  intro q
  apply Subtype.ext
  simp [pairMap, metricUnitTimeSlabParam, metricUnitTimeSlabScaledBundle,
    metricUnitTimeSlabScale, metricUnitTimeSlabRefQuad,
    MetricUnitTangent.base, MetricUnitTangent.vec]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.metricUnitTimeSlabParam_cont_of_scaledBundle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.metricUnitTimeSlabParam_cont_of_scaledBundle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.metricUnitTimeSlabParam_cont_of_scaledBundle ``Submission.DifferentialGeometry.metricUnitTimeSlabParam_cont_of_scaledBundle

omit [FiniteDimensional ℝ E] in
theorem metricUnitTimeSlabParam_cont_of_bundle
    (G : Real -> SmoothRiemannianMetric I M) (K : Set Real)
    (g₀ : SmoothRiemannianMetric I M)
    (hquad : Continuous (metricTimeBundleQuad (I := I) (M := M) G K)) :
    Continuous (metricUnitTimeSlabParam (I := I) (M := M) G K g₀) :=
  metricUnitTimeSlabParam_cont_of_scaledBundle (I := I) (M := M) G K g₀
    (metricUnitTimeSlabScaledBundle_cont_of_bundle (I := I) (M := M) G K g₀ hquad)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.metricUnitTimeSlabParam_cont_of_bundle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.metricUnitTimeSlabParam_cont_of_bundle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.metricUnitTimeSlabParam_cont_of_bundle ``Submission.DifferentialGeometry.metricUnitTimeSlabParam_cont_of_bundle

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] in
theorem metricUnitTimeSlabParam_surjective
    (G : Real -> SmoothRiemannianMetric I M) (K : Set Real)
    (g₀ : SmoothRiemannianMetric I M) :
    Function.Surjective
      (metricUnitTimeSlabParam (I := I) (M := M) G K g₀) := by
  rintro ⟨⟨⟨t, ht⟩, ⟨x, v⟩⟩, hGunit⟩
  have hGtunit : (G t).inner x v v = 1 := by
    simpa using hGunit
  have hv : v ≠ 0 := by
    intro hv0
    have hbad := hGtunit
    rw [hv0] at hbad
    norm_num at hbad
  let r₀ : Real := g₀.inner x v v
  have hr₀pos : 0 < r₀ := g₀.pos x v hv
  let s₀ : Real := Real.sqrt r₀
  have hs₀pos : 0 < s₀ := Real.sqrt_pos.mpr hr₀pos
  have hs₀ne : s₀ ≠ 0 := ne_of_gt hs₀pos
  let a₀ : Real := s₀⁻¹
  let u : TangentSpace I x := a₀ • v
  have hs₀s₀ : s₀ * s₀ = r₀ := by
    simpa [sq] using (Real.sq_sqrt (le_of_lt hr₀pos))
  have hunit₀ : g₀.inner x u u = 1 := by
    have haa : a₀ * a₀ * r₀ = 1 := by
      have hmul : (s₀ * s₀) * (s₀⁻¹ * s₀⁻¹) = 1 := by
        field_simp [hs₀ne]
      calc
        a₀ * a₀ * r₀ = (s₀⁻¹ * s₀⁻¹) * (s₀ * s₀) := by
          rw [hs₀s₀]
        _ = (s₀ * s₀) * (s₀⁻¹ * s₀⁻¹) := by ring
        _ = 1 := hmul
    calc
      g₀.inner x u u = a₀ * a₀ * r₀ := by
        simpa [u, r₀] using metric_smul2 (I := I) (M := M) g₀ a₀ v
      _ = 1 := haa
  let p₀ : MetricUnitTangent (I := I) (M := M) g₀ :=
    ⟨(⟨x, u⟩ : TangentBundle I M), hunit₀⟩
  let source : {t : Real // t ∈ K} × MetricUnitTangent (I := I) (M := M) g₀ :=
    (⟨t, ht⟩, p₀)
  refine ⟨source, ?_⟩
  apply Subtype.ext
  dsimp [source, metricUnitTimeSlabParam, p₀, u, a₀]
  have hsqrtRaw :
      Real.sqrt (s₀⁻¹ * (s₀⁻¹ * (G t).inner x v v)) = s₀⁻¹ := by
    rw [hGtunit, mul_one]
    have hnonneg : 0 ≤ s₀⁻¹ := le_of_lt (inv_pos.mpr hs₀pos)
    have hsq : s₀⁻¹ * s₀⁻¹ = (s₀⁻¹) ^ 2 := by ring
    rw [hsq, Real.sqrt_sq_eq_abs]
    exact abs_of_nonneg hnonneg
  have hvecRaw :
      (Real.sqrt (s₀⁻¹ * (s₀⁻¹ * (G t).inner x v v)))⁻¹ •
          (s₀⁻¹ • v) = v := by
    rw [hsqrtRaw]
    calc
      (s₀⁻¹)⁻¹ • (s₀⁻¹ • v) = ((s₀⁻¹)⁻¹ * s₀⁻¹) • v := by
        simp [smul_smul]
      _ = v := by
        have hcoef : (s₀⁻¹)⁻¹ * s₀⁻¹ = 1 := by
          field_simp [hs₀ne]
        rw [hcoef]
        simp
  rw [hGtunit, mul_one] at hvecRaw
  congr 2
  change (Real.sqrt ((G t).inner x (s₀⁻¹ • v) (s₀⁻¹ • v)))⁻¹ •
    (s₀⁻¹ • v) = v
  rw [metric_smul2, hGtunit, mul_one]
  exact hvecRaw

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.metricUnitTimeSlabParam_surjective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.metricUnitTimeSlabParam_surjective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.metricUnitTimeSlabParam_surjective ``Submission.DifferentialGeometry.metricUnitTimeSlabParam_surjective

omit [FiniteDimensional ℝ E] in
theorem metricUnitTimeSlab_compact_of_param
    (G : Real -> SmoothRiemannianMetric I M) (K : Set Real)
    (g₀ : SmoothRiemannianMetric I M)
    (hsource :
      IsCompact
        (Set.univ :
          Set ({t : Real // t ∈ K} × MetricUnitTangent (I := I) (M := M) g₀)))
    (hcont :
      Continuous (metricUnitTimeSlabParam (I := I) (M := M) G K g₀))
    (hsurj :
      Function.Surjective
        (metricUnitTimeSlabParam (I := I) (M := M) G K g₀)) :
    IsCompact
      (Set.univ : Set (MetricUnitTangentTimeSlab (I := I) (M := M) G K)) := by
  simpa [Set.image_univ, hsurj.range_eq] using hsource.image hcont

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.metricUnitTimeSlab_compact_of_param then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.metricUnitTimeSlab_compact_of_param"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.metricUnitTimeSlab_compact_of_param ``Submission.DifferentialGeometry.metricUnitTimeSlab_compact_of_param

omit [FiniteDimensional ℝ E] in
theorem metricUnitTimeSlab_compact_of_param_cont
    (G : Real -> SmoothRiemannianMetric I M) (K : Set Real)
    (g₀ : SmoothRiemannianMetric I M)
    (hsource :
      IsCompact
        (Set.univ :
          Set ({t : Real // t ∈ K} × MetricUnitTangent (I := I) (M := M) g₀)))
    (hcont :
      Continuous (metricUnitTimeSlabParam (I := I) (M := M) G K g₀)) :
    IsCompact
      (Set.univ : Set (MetricUnitTangentTimeSlab (I := I) (M := M) G K)) :=
  metricUnitTimeSlab_compact_of_param (I := I) (M := M) G K g₀ hsource hcont
    (metricUnitTimeSlabParam_surjective (I := I) (M := M) G K g₀)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.metricUnitTimeSlab_compact_of_param_cont then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.metricUnitTimeSlab_compact_of_param_cont"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.metricUnitTimeSlab_compact_of_param_cont ``Submission.DifferentialGeometry.metricUnitTimeSlab_compact_of_param_cont

omit [FiniteDimensional ℝ E] in
theorem metricUnitTimeSlab_compact_of_param_cont_compactSpace
    (G : Real -> SmoothRiemannianMetric I M) (K : Set Real)
    (g₀ : SmoothRiemannianMetric I M)
    [CompactSpace {t : Real // t ∈ K}]
    [CompactSpace (MetricUnitTangent (I := I) (M := M) g₀)]
    (hcont :
      Continuous (metricUnitTimeSlabParam (I := I) (M := M) G K g₀)) :
    IsCompact
      (Set.univ : Set (MetricUnitTangentTimeSlab (I := I) (M := M) G K)) :=
  metricUnitTimeSlab_compact_of_param_cont (I := I) (M := M) G K g₀
    isCompact_univ hcont

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.metricUnitTimeSlab_compact_of_param_cont_compactSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.metricUnitTimeSlab_compact_of_param_cont_compactSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.metricUnitTimeSlab_compact_of_param_cont_compactSpace ``Submission.DifferentialGeometry.metricUnitTimeSlab_compact_of_param_cont_compactSpace

theorem metricUnitTimeSlab_icc_compact_of_param_cont
    [CompactSpace M] [T2Space M]
    (G : Real -> SmoothRiemannianMetric I M) (t0 t1 : Real)
    (g₀ : SmoothRiemannianMetric I M)
    (hcont :
      Continuous (metricUnitTimeSlabParam (I := I) (M := M)
        G (Set.Icc t0 t1) g₀)) :
    IsCompact
      (Set.univ :
        Set (MetricUnitTangentTimeSlab (I := I) (M := M) G
          (Set.Icc t0 t1))) := by
  let : CompactSpace {t : Real // t ∈ Set.Icc t0 t1} :=
    isCompact_iff_compactSpace.mp _root_.CompactIccSpace.isCompact_Icc
  have hsource :
      IsCompact
        (Set.univ :
          Set ({t : Real // t ∈ Set.Icc t0 t1} ×
            MetricUnitTangent (I := I) (M := M) g₀)) := by
    convert
      (isCompact_univ.prod
        (metricUnit_compact (I := I) (M := M) g₀) :
        IsCompact
          ((Set.univ : Set {t : Real // t ∈ Set.Icc t0 t1}) ×ˢ
            (Set.univ : Set (MetricUnitTangent (I := I) (M := M) g₀)))) using 1
    ext q
    simp
  exact metricUnitTimeSlab_compact_of_param_cont
    (I := I) (M := M) G (Set.Icc t0 t1) g₀ hsource hcont

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.metricUnitTimeSlab_icc_compact_of_param_cont then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.metricUnitTimeSlab_icc_compact_of_param_cont"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.metricUnitTimeSlab_icc_compact_of_param_cont ``Submission.DifferentialGeometry.metricUnitTimeSlab_icc_compact_of_param_cont

theorem metricUnitTimeSlab_icc_compact_of_bundle
    [CompactSpace M] [T2Space M]
    (G : Real -> SmoothRiemannianMetric I M) (t0 t1 : Real)
    (g₀ : SmoothRiemannianMetric I M)
    (hquad :
      Continuous (metricTimeBundleQuad (I := I) (M := M) G (Set.Icc t0 t1))) :
    IsCompact
      (Set.univ :
        Set (MetricUnitTangentTimeSlab (I := I) (M := M) G
          (Set.Icc t0 t1))) :=
  metricUnitTimeSlab_icc_compact_of_param_cont (I := I) (M := M) G t0 t1 g₀
    (metricUnitTimeSlabParam_cont_of_bundle (I := I) (M := M)
      G (Set.Icc t0 t1) g₀ hquad)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.metricUnitTimeSlab_icc_compact_of_bundle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.metricUnitTimeSlab_icc_compact_of_bundle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.metricUnitTimeSlab_icc_compact_of_bundle ``Submission.DifferentialGeometry.metricUnitTimeSlab_icc_compact_of_bundle

omit [FiniteDimensional ℝ E] in
theorem unitAbsBound_to_all
    (g : SmoothRiemannianMetric I M)
    (A : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    {C : Real}
    (hunit :
      ∀ p : MetricUnitTangent (I := I) (M := M) g,
        |quad02 (I := I) (M := M)
          (A (MetricUnitTangent.base (I := I) (M := M) p))
          (MetricUnitTangent.vec (I := I) (M := M) p)| ≤ C) :
    ∀ x (v : TangentSpace I x),
      |quad02 (I := I) (M := M) (A x) v| ≤ C * g.inner x v v := by
  intro x v
  by_cases hv : v = 0
  · subst v
    have hzero :
        quad02 (I := I) (M := M) (A x) (0 : TangentSpace I x) = 0 := by
      simpa using tensor02_smul2 (I := I) (M := M) (A x)
        0 (0 : TangentSpace I x)
    simp [hzero]
  let r : Real := g.inner x v v
  have hrpos : 0 < r := g.pos x v hv
  let s : Real := Real.sqrt r
  have hspos : 0 < s := Real.sqrt_pos.mpr hrpos
  have hsne : s ≠ 0 := ne_of_gt hspos
  let a : Real := s⁻¹
  let u : TangentSpace I x := a • v
  have hss : s * s = r := by
    simpa [sq] using (Real.sq_sqrt (le_of_lt hrpos))
  have hunit_u : g.inner x u u = 1 := by
    have haa : a * a * r = 1 := by
      have hmul : (s * s) * (s⁻¹ * s⁻¹) = 1 := by
        field_simp [hsne]
      calc
        a * a * r = (s⁻¹ * s⁻¹) * (s * s) := by
          rw [hss]
        _ = (s * s) * (s⁻¹ * s⁻¹) := by ring
        _ = 1 := hmul
    calc
      g.inner x u u = a * a * r := by
        simpa [u, r] using metric_smul2 (I := I) (M := M) g a v
      _ = 1 := haa
  have hu_bound := hunit
    (⟨(⟨x, u⟩ : TangentBundle I M), hunit_u⟩ :
      MetricUnitTangent (I := I) (M := M) g)
  have hv_from_u : s • u = v := by
    calc
      s • u = (s * a) • v := by simp [u, smul_smul]
      _ = v := by
        have hsa : s * a = 1 := by simp [a, hsne]
        simp [hsa]
  have hscale :
      quad02 (I := I) (M := M) (A x) v =
        s * s * quad02 (I := I) (M := M) (A x) u := by
    rw [← hv_from_u]
    exact tensor02_smul2 (I := I) (M := M) (A x) s u
  have hs2_nonneg : 0 ≤ s * s := mul_nonneg (le_of_lt hspos) (le_of_lt hspos)
  calc
    |quad02 (I := I) (M := M) (A x) v|
        = s * s * |quad02 (I := I) (M := M) (A x) u| := by
          rw [hscale, abs_mul, abs_of_nonneg hs2_nonneg]
    _ ≤ s * s * C := mul_le_mul_of_nonneg_left hu_bound hs2_nonneg
    _ = C * g.inner x v v := by
      rw [hss]
      ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.unitAbsBound_to_all then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.unitAbsBound_to_all"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.unitAbsBound_to_all ``Submission.DifferentialGeometry.unitAbsBound_to_all

omit [FiniteDimensional ℝ E] in
theorem compactUnitSlab_absBound
    (G : Real -> SmoothRiemannianMetric I M)
    (A : (t : Real) -> (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (t0 t1 : Real)
    [TopologicalSpace (MetricUnitTangentSlab (I := I) (M := M) G t0 t1)]
    (hcompact :
      IsCompact (Set.univ : Set (MetricUnitTangentSlab (I := I) (M := M) G t0 t1)))
    (hcont : Continuous
      (fun p : MetricUnitTangentSlab (I := I) (M := M) G t0 t1 =>
        |quad02 (I := I) (M := M)
          (A p.1.1 (MetricUnitTangent.base (I := I) (M := M) p.2))
          (MetricUnitTangent.vec (I := I) (M := M) p.2)|)) :
    ∃ C : Real, 0 ≤ C ∧
      ∀ t, t ∈ Set.Icc t0 t1 ->
        ∀ x (v : TangentSpace I x),
          |quad02 (I := I) (M := M) (A t x) v| ≤ C * (G t).inner x v v := by
  classical
  let slab := MetricUnitTangentSlab (I := I) (M := M) G t0 t1
  let f : slab -> Real :=
    fun p =>
      |quad02 (I := I) (M := M)
        (A p.1.1 (MetricUnitTangent.base (I := I) (M := M) p.2))
        (MetricUnitTangent.vec (I := I) (M := M) p.2)|
  by_cases hne : (Set.univ : Set slab).Nonempty
  · obtain ⟨p0, _hp0, hmax⟩ := hcompact.exists_isMaxOn hne hcont.continuousOn
    let C : Real := f p0
    have hC : 0 ≤ C := by
      dsimp [C, f]
      positivity
    refine ⟨C, hC, ?_⟩
    intro t ht x v
    apply unitAbsBound_to_all (I := I) (M := M) (g := G t)
      (A := A t)
    intro p
    let q : slab := ⟨⟨t, ht⟩, p⟩
    have hq := (isMaxOn_iff.mp hmax) q (Set.mem_univ q)
    exact hq
  · refine ⟨0, le_rfl, ?_⟩
    intro t ht x v
    apply unitAbsBound_to_all (I := I) (M := M) (g := G t)
      (A := A t)
    intro p
    exfalso
    exact hne ⟨⟨⟨t, ht⟩, p⟩, Set.mem_univ _⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.compactUnitSlab_absBound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.compactUnitSlab_absBound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.compactUnitSlab_absBound ``Submission.DifferentialGeometry.compactUnitSlab_absBound

omit [FiniteDimensional ℝ E] in
theorem compactUnitTimeSlab_absBound
    (G : Real -> SmoothRiemannianMetric I M)
    (A : (t : Real) -> (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (K : Set Real)
    (hcompact :
      IsCompact
        (Set.univ :
          Set (MetricUnitTangentTimeSlab (I := I) (M := M) G K)))
    (hcont : Continuous
      (fun p : MetricUnitTangentTimeSlab (I := I) (M := M) G K =>
        |quad02 (I := I) (M := M)
          (A (MetricUnitTangentTimeSlab.time (I := I) (M := M) p)
            (MetricUnitTangentTimeSlab.base (I := I) (M := M) p))
          (MetricUnitTangentTimeSlab.vec (I := I) (M := M) p)|)) :
    ∃ C : Real, 0 ≤ C ∧
      ∀ t, t ∈ K ->
        ∀ x (v : TangentSpace I x),
          |quad02 (I := I) (M := M) (A t x) v| ≤ C * (G t).inner x v v := by
  classical
  let slab := MetricUnitTangentTimeSlab (I := I) (M := M) G K
  let f : slab -> Real :=
    fun p =>
      |quad02 (I := I) (M := M)
        (A (MetricUnitTangentTimeSlab.time (I := I) (M := M) p)
          (MetricUnitTangentTimeSlab.base (I := I) (M := M) p))
        (MetricUnitTangentTimeSlab.vec (I := I) (M := M) p)|
  by_cases hne : (Set.univ : Set slab).Nonempty
  · obtain ⟨p0, _hp0, hmax⟩ := hcompact.exists_isMaxOn hne hcont.continuousOn
    let C : Real := f p0
    have hC : 0 ≤ C := by
      dsimp [C, f]
      positivity
    refine ⟨C, hC, ?_⟩
    intro t ht x v
    apply unitAbsBound_to_all (I := I) (M := M) (g := G t)
      (A := A t)
    intro p
    let q : slab := ⟨(⟨t, ht⟩, (p.1 : TangentBundle I M)), by
      exact MetricUnitTangent.unit (I := I) (M := M) p⟩
    have hq := (isMaxOn_iff.mp hmax) q (Set.mem_univ q)
    simpa [C, f, q, MetricUnitTangent.base, MetricUnitTangent.vec,
      MetricUnitTangentTimeSlab.time, MetricUnitTangentTimeSlab.base,
      MetricUnitTangentTimeSlab.vec, MetricUnitTangentTimeSlab.bundlePoint] using hq
  · refine ⟨0, le_rfl, ?_⟩
    intro t ht x v
    apply unitAbsBound_to_all (I := I) (M := M) (g := G t)
      (A := A t)
    intro p
    exfalso
    let q : slab := ⟨(⟨t, ht⟩, (p.1 : TangentBundle I M)), by
      exact MetricUnitTangent.unit (I := I) (M := M) p⟩
    exact hne ⟨q, Set.mem_univ q⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.compactUnitTimeSlab_absBound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.compactUnitTimeSlab_absBound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.compactUnitTimeSlab_absBound ``Submission.DifferentialGeometry.compactUnitTimeSlab_absBound

theorem timeSlabAbsQuadCont
    (G : Real -> SmoothRiemannianMetric I M)
    (A : (t : Real) -> (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (K : Set Real)
    (hA :
      Continuous (fun q : {t : Real // t ∈ K} × TangentBundle I M =>
        TotalSpace.mk' (Tensor0SModel 2 Real E)
          (E := fun x : M => Tensor0SSpace 2 I x) q.2.proj
          (A q.1.1 q.2.proj))) :
    Continuous
      (fun p : MetricUnitTangentTimeSlab (I := I) (M := M) G K =>
        |quad02 (I := I) (M := M)
          (A (MetricUnitTangentTimeSlab.time (I := I) (M := M) p)
            (MetricUnitTangentTimeSlab.base (I := I) (M := M) p))
          (MetricUnitTangentTimeSlab.vec (I := I) (M := M) p)|) := by
  let P := MetricUnitTangentTimeSlab (I := I) (M := M) G K
  let b : P -> M := fun p => MetricUnitTangentTimeSlab.base (I := I) (M := M) p
  let T : (p : P) -> Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 (b p) :=
    fun p => A (MetricUnitTangentTimeSlab.time (I := I) (M := M) p) (b p)
  let v : Fin 2 -> (p : P) -> TangentSpace I (b p) :=
    fun _ p => MetricUnitTangentTimeSlab.vec (I := I) (M := M) p
  have hb : Continuous b := by
    dsimp [b, MetricUnitTangentTimeSlab.base, MetricUnitTangentTimeSlab.bundlePoint]
    exact (FiberBundle.continuous_proj E (TangentSpace I)).comp
      (continuous_snd.comp continuous_subtype_val)
  have hT : Continuous (fun p : P =>
      TotalSpace.mk' (Tensor0SModel 2 Real E)
        (E := fun x : M => Tensor0SSpace 2 I x) (b p) (T p)) := by
    change Continuous
      ((fun q : {t : Real // t ∈ K} × TangentBundle I M ↦
        TotalSpace.mk' (Tensor0SModel 2 Real E)
          (E := fun x : M ↦ Tensor0SSpace 2 I x) q.2.proj
            (A q.1 q.2.proj)) ∘ Subtype.val)
    exact hA.comp continuous_subtype_val
  have hv : ∀ i : Fin 2, Continuous (fun p : P =>
      TotalSpace.mk' E (E := fun x : M => TangentSpace I x) (b p) (v i p)) := by
    intro i
    change Continuous (Prod.snd ∘ Subtype.val : P → TangentBundle I M)
    exact continuous_snd.comp continuous_subtype_val
  have hEval := TensorMultilinear.continuous_section_apply_base
    (𝕜 := Real) (I := I) (M := M) (P := P) (n := 2)
    b hb T hT v hv
  change Continuous (fun p : P ↦
    |Tensor0SSpace.toModel (T p) (fun i : Fin 2 ↦ v i p)|)
  exact hEval.abs

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.timeSlabAbsQuadCont then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.timeSlabAbsQuadCont"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.timeSlabAbsQuadCont ``Submission.DifferentialGeometry.timeSlabAbsQuadCont

theorem metric_lower_icc
    [CompactSpace M] [T2Space M]
    (G : Real → SmoothRiemannianMetric I M) (t0 t1 : Real)
    (gRef : SmoothRiemannianMetric I M)
    (hquad :
      Continuous
        (metricTimeBundleQuad (I := I) (M := M) G (Set.Icc t0 t1))) :
    ∃ c : Real, 0 < c ∧
      ∀ t, t ∈ Set.Icc t0 t1 →
        ∀ x (v : TangentSpace I x),
          c * gRef.inner x v v ≤ (G t).inner x v v := by
  classical
  let K : Set Real := Set.Icc t0 t1
  have hcompact :
      IsCompact
        (Set.univ :
          Set (MetricUnitTangentTimeSlab (I := I) (M := M) G K)) := by
    simpa only [K] using
      metricUnitTimeSlab_icc_compact_of_bundle
        (I := I) (M := M) G t0 t1 gRef hquad
  have hcont :
      Continuous
        (fun p : MetricUnitTangentTimeSlab (I := I) (M := M) G K =>
          |quad02 (I := I) (M := M)
            (Tensor0SBundle.metricTensorField (I := I) gRef
              (MetricUnitTangentTimeSlab.base (I := I) (M := M) p))
            (MetricUnitTangentTimeSlab.vec (I := I) (M := M) p)|) := by
    change Continuous (fun p : MetricUnitTangentTimeSlab (I := I) (M := M) G K =>
      |gRef.inner p.val.2.proj p.val.2.2 p.val.2.2|)
    exact ((metricQuad_cont (I := I) (M := M) gRef).comp
      (continuous_snd.comp continuous_subtype_val)).abs
  obtain ⟨C, hC, hbound⟩ :=
    compactUnitTimeSlab_absBound (I := I) (M := M) G
      (fun _ x => Tensor0SBundle.metricTensorField (I := I) gRef x)
      K hcompact hcont
  have hC1 : 0 < C + 1 := by linarith
  refine ⟨(C + 1)⁻¹, inv_pos.mpr hC1, ?_⟩
  intro t ht x v
  have href : 0 ≤ gRef.inner x v v := by
    by_cases hv : v = 0
    · subst v
      simp
    · exact (gRef.pos x v hv).le
  have hGt : 0 ≤ (G t).inner x v v := by
    by_cases hv : v = 0
    · subst v
      simp
    · exact ((G t).pos x v hv).le
  have hraw := hbound t (by simpa only [K] using ht) x v
  have href_le : gRef.inner x v v ≤ C * (G t).inner x v v := by
    simpa [quad02, Tensor0SBundle.metricTensorField_apply,
      abs_of_nonneg href] using hraw
  have hratio : (C + 1)⁻¹ * C ≤ 1 :=
    (inv_mul_le_one₀ hC1).2 (by linarith)
  calc
    (C + 1)⁻¹ * gRef.inner x v v
        ≤ (C + 1)⁻¹ * (C * (G t).inner x v v) :=
      mul_le_mul_of_nonneg_left href_le (inv_pos.mpr hC1).le
    _ = ((C + 1)⁻¹ * C) * (G t).inner x v v := by ring
    _ ≤ 1 * (G t).inner x v v :=
      mul_le_mul_of_nonneg_right hratio hGt
    _ = (G t).inner x v v := one_mul _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.metric_lower_icc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.metric_lower_icc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.metric_lower_icc ``Submission.DifferentialGeometry.metric_lower_icc

end DifferentialGeometry
