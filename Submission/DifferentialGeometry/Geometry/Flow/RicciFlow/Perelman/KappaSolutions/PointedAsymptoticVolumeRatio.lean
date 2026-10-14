import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AsymptoticVolumeRatio
import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.InverseDistanceControl
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.LocalVolumeOrder
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.OpenRestrictionVolume
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.VolumeNaturality
import Submission.DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens
import Submission.DifferentialGeometry.Topology.SigmaCompactOpen
import Mathlib.Analysis.SpecificLimits.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Filter _root_.Set _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.TopologicalSpace
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal _root_.Topology _root_.Submission.Topology

universe u uE uH

section LocalVolume

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [T2Space N] [SigmaCompactSpace N]

private local instance pointedAvrLocalMMeasurable : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedAvrLocalMMeasurable
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedAvrLocalMMeasurable target :: scope.openDecls } }
private local instance pointedAvrLocalMBorel : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedAvrLocalMBorel
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedAvrLocalMBorel target :: scope.openDecls } }
private local instance pointedAvrLocalNMeasurable : MeasurableSpace N := borel N

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedAvrLocalNMeasurable
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedAvrLocalNMeasurable target :: scope.openDecls } }
private local instance pointedAvrLocalNBorel : BorelSpace N := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedAvrLocalNBorel
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedAvrLocalNBorel target :: scope.openDecls } }

omit [CompleteSpace E] in
private theorem pointedAvr_image_volume_le
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric I N)
    (F : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞))
    {A : Set M} (hA : MeasurableSet A) (hsource : A ⊆ F.source)
    {Q : ℝ} (hQ : 0 < Q)
    (hmetric : ∀ x ∈ A, ∀ v : TangentSpace I x,
      h.inner (F x) (mfderiv I I (F : M → N) x v)
        (mfderiv I I (F : M → N) x v) ≤ Q * g.inner x v v) :
    riemannianVolumeMeasure (I := I) (M := N) h ((F : M → N) '' A) ≤
      ENNReal.ofReal (Real.sqrt (Q ^ Module.finrank ℝ E)) *
        riemannianVolumeMeasure (I := I) (M := M) g A := by
  let U : _root_.TopologicalSpace.Opens M := ⟨F.source, F.open_source⟩
  have hU : (U : Set M) ⊆ F.source := subset_rfl
  let V : _root_.TopologicalSpace.Opens N := ⟨(F : M → N) '' (U : Set M), image_opens_isOpen F hU⟩
  let _ : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
  let _ : SigmaCompactSpace V := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I V.isOpen)
  let _ : MeasurableSpace U := borel U
  let _ : BorelSpace U := ⟨rfl⟩
  let _ : MeasurableSpace V := borel V
  let _ : BorelSpace V := ⟨rfl⟩
  let e : U ≃ₘ⟮I, I⟯ V := PartialDiffeomorph.toOpensDiffeo F hU
  let B : Set U := (Subtype.val : U → M) ⁻¹' A
  let gU := g.restrictOpen U
  let hV := h.restrictOpen V
  let gP := Diffeomorph.pullbackMetric hV e
  have hB : MeasurableSet B := hA.preimage continuous_subtype_val.measurable
  have hvalB : (Subtype.val : U → M) '' B = A := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hx
      exact ⟨⟨x, hsource hx⟩, hx, rfl⟩
  have himage : (Subtype.val : V → N) '' ((e : U → V) '' B) =
      (F : M → N) '' A := by
    rw [Set.image_image]
    change (fun x : U => F (x : M)) '' B = (F : M → N) '' A
    rw [← Set.image_image, hvalB]
  have he : MeasurableEmbedding (e : U → V) :=
    e.toHomeomorph.toMeasurableEquiv.measurableEmbedding
  have hpres := (volumeMeasurePreserving_pullbackMetric hV e).measure_preimage_emb he
    ((e : U → V) '' B)
  rw [he.injective.preimage_image] at hpres
  have hcomp : ∀ x ∈ B, ∀ v : TangentSpace I x,
      gP.inner x v v ≤ Q * gU.inner x v v := by
    intro x hx v
    dsimp only [gP, gU, hV]
    rw [Diffeomorph.pullbackMetric_inner, SmoothRiemannianMetric.restrictOpen_inner,
      SmoothRiemannianMetric.restrictOpen_inner]
    dsimp only [e]
    rw [PartialDiffeomorph.mfderiv_toOpensDiffeo]
    exact hmetric (x : M) hx v
  calc
    riemannianVolumeMeasure (I := I) (M := N) h ((F : M → N) '' A) =
        riemannianVolumeMeasure (I := I) (M := V) hV ((e : U → V) '' B) := by
      rw [riemannianVolumeMeasure_restrictOpen_apply, himage]
    _ = riemannianVolumeMeasure (I := I) (M := U) gP B := hpres.symm
    _ ≤ ENNReal.ofReal (Real.sqrt (Q ^ Module.finrank ℝ E)) *
        riemannianVolumeMeasure (I := I) (M := U) gU B :=
      riemannianVolumeMeasure_le_on gU gP hB hQ hcomp
    _ = ENNReal.ofReal (Real.sqrt (Q ^ Module.finrank ℝ E)) *
        riemannianVolumeMeasure (I := I) (M := M) g A := by
      rw [riemannianVolumeMeasure_restrictOpen_apply, hvalB]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedAvr_image_volume_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedAvr_image_volume_le target :: scope.openDecls } }

end LocalVolume

section Pointed

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
  {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
  {subseq : ℕ → ℕ} {Phi : PointedRiemannianConvergenceMaps (I := I) X L subseq}

private local instance pointedAvrTopology : TopologicalSpace L.M := L.topology

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedAvrTopology
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedAvrTopology target :: scope.openDecls } }
private local instance pointedAvrCharted : ChartedSpace H L.M := L.charted

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedAvrCharted
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedAvrCharted target :: scope.openDecls } }
private local instance pointedAvrSmooth : IsManifold I ∞ L.M := L.smooth

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedAvrSmooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedAvrSmooth target :: scope.openDecls } }
private local instance pointedAvrT2 : T2Space L.M := L.t2

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedAvrT2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedAvrT2 target :: scope.openDecls } }
private local instance pointedAvrSigmaCompact : SigmaCompactSpace L.M := L.sigmaCompact

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedAvrSigmaCompact
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedAvrSigmaCompact target :: scope.openDecls } }
private local instance pointedAvrTangentT2 : T2Space (TangentBundle I L.M) := L.t2TangentBundle

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedAvrTangentT2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedAvrTangentT2 target :: scope.openDecls } }
private local instance pointedAvrMeasurable : MeasurableSpace L.M := borel L.M

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedAvrMeasurable
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedAvrMeasurable target :: scope.openDecls } }
private local instance pointedAvrBorel : BorelSpace L.M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedAvrBorel
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedAvrBorel target :: scope.openDecls } }

theorem exists_pointed_buffered_ball_volume_le
    (C : MetricConvergenceData (I := I) Phi)
    (hreference : ∀ k, (C.domain k).referenceMetric = (C.domain k).limitMetric)
    (hcomplete : MetricComplete (I := I) L)
    {s r epsilon delta : ℝ} (hs : 0 < s) (hepsilon : 0 < epsilon)
    (hbuffer : (1 + epsilon) * s < r) (hdelta : 0 < delta) :
    ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
      (let _ : TopologicalSpace (X.obj (subseq k)).M := (X.obj (subseq k)).topology
       let _ : ChartedSpace H (X.obj (subseq k)).M := (X.obj (subseq k)).charted
       let _ : IsManifold I ∞ (X.obj (subseq k)).M := (X.obj (subseq k)).smooth
       let _ : T2Space (X.obj (subseq k)).M := (X.obj (subseq k)).t2
       let _ : SigmaCompactSpace (X.obj (subseq k)).M := (X.obj (subseq k)).sigmaCompact
       riemannianVolumeMeasure (I := I) (M := (X.obj (subseq k)).M) (X.obj (subseq k)).metric
           (riemannianBallOf (X.obj (subseq k)).metric (X.obj (subseq k)).basepoint s) ≤
         ENNReal.ofReal (Real.sqrt ((1 + delta) ^ Module.finrank ℝ E)) *
           riemannianVolumeMeasure (I := I) (M := L.M) L.metric
             (riemannianBallOf L.metric L.basepoint r)) := by
  obtain ⟨hKcompact, kcap, hkcap⟩ := exists_pointed_inverse_distance_control
    C hreference hcomplete s hs.le epsilon hepsilon
  let K := riemannianClosedBallOf L.metric L.basepoint ((1 + epsilon) * s)
  obtain ⟨kmetric, hkmetric⟩ :=
    exists_pointed_full_ambient_quadratic_control C hreference K hKcompact delta hdelta
  refine ⟨max kcap kmetric, ?_⟩
  intro k hk
  let _ : TopologicalSpace (X.obj (subseq k)).M := (X.obj (subseq k)).topology
  let _ : ChartedSpace H (X.obj (subseq k)).M := (X.obj (subseq k)).charted
  let _ : IsManifold I ∞ (X.obj (subseq k)).M := (X.obj (subseq k)).smooth
  let _ : T2Space (X.obj (subseq k)).M := (X.obj (subseq k)).t2
  let _ : SigmaCompactSpace (X.obj (subseq k)).M := (X.obj (subseq k)).sigmaCompact
  let _ : MeasurableSpace (X.obj (subseq k)).M := borel (X.obj (subseq k)).M
  let _ : BorelSpace (X.obj (subseq k)).M := ⟨rfl⟩
  let F := Phi.partialDiffeomorph k
  let B := riemannianBallOf (X.obj (subseq k)).metric (X.obj (subseq k)).basepoint s
  let A : Set L.M := F.source ∩ (F : L.M → (X.obj (subseq k)).M) ⁻¹' B
  have hcap := (hkcap k ((Nat.le_max_left _ _).trans hk)).1
  have hmetric := (hkmetric k ((Nat.le_max_right _ _).trans hk)).2
  have hBopen : IsOpen B :=
    isOpen_lt (DifferentialGeometry.Geometry.Riemannian.continuous_riemannianEDist
      (I := I) (X.obj (subseq k)).metric (X.obj (subseq k)).basepoint) continuous_const
  have hA : MeasurableSet A :=
    (F.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage F.open_source hBopen).measurableSet
  have hAsource : A ⊆ F.source := _root_.Set.inter_subset_left
  have hAK : A ⊆ K := by
    intro x hx
    have hopen : riemannianEDistOf (I := I) (X.obj (subseq k)).metric
        (X.obj (subseq k)).basepoint (F x) < ENNReal.ofReal s := hx.2
    have hclosed : F x ∈ riemannianClosedBallOf (X.obj (subseq k)).metric
        (X.obj (subseq k)).basepoint s := by
      change riemannianEDistOf (I := I) (X.obj (subseq k)).metric
        (X.obj (subseq k)).basepoint (F x) ≤ ENNReal.ofReal s
      exact hopen.le
    have hc := (hcap (F x) hclosed).2
    have hi : F.symm (F x) = x := F.left_inv' hx.1
    rwa [hi] at hc
  have hr : 0 < r := (mul_pos (by linarith : 0 < 1 + epsilon) hs).trans hbuffer
  have hAr : A ⊆ riemannianBallOf L.metric L.basepoint r := by
    intro x hx
    exact (hAK hx).trans_lt ((ENNReal.ofReal_lt_ofReal_iff hr).2 hbuffer)
  have himage : (F : L.M → (X.obj (subseq k)).M) '' A = B := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx.2
    · intro hy
      have hopen : riemannianEDistOf (I := I) (X.obj (subseq k)).metric
          (X.obj (subseq k)).basepoint y < ENNReal.ofReal s := hy
      have hclosed : y ∈ riemannianClosedBallOf (X.obj (subseq k)).metric
          (X.obj (subseq k)).basepoint s := by
        change riemannianEDistOf (I := I) (X.obj (subseq k)).metric
          (X.obj (subseq k)).basepoint y ≤ ENNReal.ofReal s
        exact hopen.le
      have hyt : y ∈ F.target := (hcap y hclosed).1
      have hright : F (F.symm y) = y := F.right_inv' hyt
      refine ⟨F.symm y, ⟨F.toPartialEquiv.map_target hyt, ?_⟩, hright⟩
      change F (F.symm y) ∈ B
      rw [hright]
      exact hy
  have hquad : ∀ x ∈ A, ∀ v : TangentSpace I x,
      (X.obj (subseq k)).metric.inner (F x)
          (mfderiv I I (F : L.M → (X.obj (subseq k)).M) x v)
          (mfderiv I I (F : L.M → (X.obj (subseq k)).M) x v) ≤
        (1 + delta) * L.metric.inner x v v := by
    intro x hx v
    have herr := (abs_le.mp (hmetric x (hAK hx) v)).2
    change (X.obj (subseq k)).metric.inner (F x)
        (mfderiv I I (F : L.M → (X.obj (subseq k)).M) x v)
        (mfderiv I I (F : L.M → (X.obj (subseq k)).M) x v) -
      L.metric.inner x v v ≤ delta * L.metric.inner x v v at herr
    linarith
  have hv := pointedAvr_image_volume_le L.metric (X.obj (subseq k)).metric F
    hA hAsource (by linarith : 0 < 1 + delta) hquad
  rw [himage] at hv
  exact hv.trans (mul_le_mul_right (_root_.MeasureTheory.measure_mono hAr) _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_pointed_buffered_ball_volume_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_pointed_buffered_ball_volume_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_pointed_buffered_ball_volume_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_pointed_buffered_ball_volume_le

theorem asymptoticVolumeRatio_lower_of_pointed_metric_convergence
    (C : MetricConvergenceData (I := I) Phi)
    (hreference : ∀ k, (C.domain k).referenceMetric = (C.domain k).limitMetric)
    (hcomplete : MetricComplete (I := I) L) (v : ℝ≥0∞)
    (hsource : ∀ i : ℕ,
      let _ : TopologicalSpace (X.obj i).M := (X.obj i).topology
      let _ : ChartedSpace H (X.obj i).M := (X.obj i).charted
      let _ : IsManifold I ∞ (X.obj i).M := (X.obj i).smooth
      let _ : T2Space (X.obj i).M := (X.obj i).t2
      let _ : SigmaCompactSpace (X.obj i).M := (X.obj i).sigmaCompact
      v ≤ asymptoticVolumeRatio (I := I) (X.obj i).metric (X.obj i).basepoint) :
    v ≤ asymptoticVolumeRatio (I := I) L.metric L.basepoint := by
  let n := Module.finrank ℝ E
  let omega := euclideanUnitBallVolume n
  have hden0 (r : ℝ) (hr : 0 < r) : omega * ENNReal.ofReal (r ^ n) ≠ 0 :=
    mul_ne_zero (euclideanUnitBallVolume_pos n).ne'
      (ENNReal.ofReal_pos.mpr (pow_pos hr n)).ne'
  have hdentop (r : ℝ) : omega * ENNReal.ofReal (r ^ n) ≠ ⊤ :=
    ENNReal.mul_ne_top (euclideanUnitBallVolume_ne_top n) ENNReal.ofReal_ne_top
  change v ≤ ⨅ (r : ℝ) (_ : 0 < r), normalizedBallVolumeRatio L.metric L.basepoint r
  refine le_iInf fun r => le_iInf fun hr => ?_
  change v ≤ riemannianVolumeMeasure (I := I) (M := L.M) L.metric
    (riemannianBallOf L.metric L.basepoint r) / (omega * ENNReal.ofReal (r ^ n))
  apply (ENNReal.le_div_iff_mul_le (Or.inl (hden0 r hr)) (Or.inl (hdentop r))).2
  let epsilon : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  let s : ℕ → ℝ := fun j => r / (1 + epsilon j) ^ 2
  have hepsilon : _root_.Filter.Tendsto epsilon _root_.Filter.atTop (𝓝 (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hone : _root_.Filter.Tendsto (fun j => 1 + epsilon j) _root_.Filter.atTop (𝓝 (1 : ℝ)) := by
    simpa only [add_zero] using
      (tendsto_const_nhds : _root_.Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) _root_.Filter.atTop (𝓝 1)).add hepsilon
  have hs : _root_.Filter.Tendsto s _root_.Filter.atTop (𝓝 r) := by
    simpa only [s, Pi.div_def, one_pow, div_one] using
      (tendsto_const_nhds : _root_.Filter.Tendsto (fun _ : ℕ => r) _root_.Filter.atTop (𝓝 r)).div
        (hone.pow 2) (by norm_num : (1 : ℝ) ^ 2 ≠ 0)
  have hpow : _root_.Filter.Tendsto (fun j => ENNReal.ofReal ((s j) ^ n)) _root_.Filter.atTop
      (𝓝 (ENNReal.ofReal (r ^ n))) := by
    simpa only [Function.comp_def] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hs.pow n)
  have hden := ENNReal.Tendsto.const_mul (a := omega) hpow
    (Or.inr (euclideanUnitBallVolume_ne_top n))
  have hleft := ENNReal.Tendsto.const_mul (a := v) hden (Or.inl (hden0 r hr))
  have hsqrt : _root_.Filter.Tendsto (fun j => Real.sqrt ((1 + epsilon j) ^ n)) _root_.Filter.atTop
      (𝓝 (1 : ℝ)) := by
    simpa only [one_pow, Real.sqrt_one, Function.comp_def] using
      Real.continuous_sqrt.continuousAt.tendsto.comp (hone.pow n)
  have hcoef : _root_.Filter.Tendsto (fun j => ENNReal.ofReal (Real.sqrt ((1 + epsilon j) ^ n)))
      atTop (𝓝 (1 : ℝ≥0∞)) := by
    simpa only [ENNReal.ofReal_one, Function.comp_def] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hsqrt
  have hright : _root_.Filter.Tendsto (fun j =>
      ENNReal.ofReal (Real.sqrt ((1 + epsilon j) ^ n)) *
        riemannianVolumeMeasure (I := I) (M := L.M) L.metric
          (riemannianBallOf L.metric L.basepoint r))
      atTop (𝓝 (riemannianVolumeMeasure (I := I) (M := L.M) L.metric
        (riemannianBallOf L.metric L.basepoint r))) := by
    simpa only [one_mul] using ENNReal.Tendsto.mul_const hcoef (Or.inl one_ne_zero)
  apply le_of_tendsto_of_tendsto' hleft hright
  intro j
  have he : 0 < epsilon j := by dsimp only [epsilon]; positivity
  have h1 : 0 < 1 + epsilon j := by linarith
  have hsj : 0 < s j := div_pos hr (sq_pos_of_pos h1)
  have hbuffer : (1 + epsilon j) * s j < r := by
    calc
      (1 + epsilon j) * s j = r / (1 + epsilon j) := by
        dsimp only [s]
        field_simp [ne_of_gt h1]
      _ < r := (div_lt_iff₀ h1).2 (by nlinarith)
  obtain ⟨k0, hk0⟩ := exists_pointed_buffered_ball_volume_le C hreference hcomplete
    hsj he hbuffer he
  let _ : TopologicalSpace (X.obj (subseq k0)).M := (X.obj (subseq k0)).topology
  let _ : ChartedSpace H (X.obj (subseq k0)).M := (X.obj (subseq k0)).charted
  let _ : IsManifold I ∞ (X.obj (subseq k0)).M := (X.obj (subseq k0)).smooth
  let _ : T2Space (X.obj (subseq k0)).M := (X.obj (subseq k0)).t2
  let _ : SigmaCompactSpace (X.obj (subseq k0)).M := (X.obj (subseq k0)).sigmaCompact
  have hratio : v ≤ normalizedBallVolumeRatio (X.obj (subseq k0)).metric
      (X.obj (subseq k0)).basepoint (s j) :=
    (hsource (subseq k0)).trans
      (asymptoticVolumeRatio_le_ratio (X.obj (subseq k0)).metric
        (X.obj (subseq k0)).basepoint hsj)
  have hraw : v * (omega * ENNReal.ofReal ((s j) ^ n)) ≤
      riemannianVolumeMeasure (I := I) (M := (X.obj (subseq k0)).M) (X.obj (subseq k0)).metric
        (riemannianBallOf (X.obj (subseq k0)).metric (X.obj (subseq k0)).basepoint (s j)) :=
    (ENNReal.le_div_iff_mul_le (Or.inl (hden0 (s j) hsj))
      (Or.inl (hdentop (s j)))).1 hratio
  exact hraw.trans (hk0 k0 le_rfl)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.asymptoticVolumeRatio_lower_of_pointed_metric_convergence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.asymptoticVolumeRatio_lower_of_pointed_metric_convergence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.asymptoticVolumeRatio_lower_of_pointed_metric_convergence ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.asymptoticVolumeRatio_lower_of_pointed_metric_convergence

end Pointed

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
