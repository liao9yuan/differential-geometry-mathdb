import Submission.DifferentialGeometry.Analysis.Integration.Measure.Polar.Evaluation
import Submission.DifferentialGeometry.Geometry.Comparison.Volume.Segment.Domain.NoConjugatePoints
import Submission.DifferentialGeometry.Geometry.Exponential.NormalCoordinates.Frame

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Function _root_.Filter _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.Topology _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Exponential
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M]
variable [RiemannianBundle (fun x : M => TangentSpace I x)]

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
private local instance instMeasTangent (x : M) :
    MeasurableSpace (TangentSpace I x) := borel _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.instMeasTangent
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.instMeasTangent target :: scope.openDecls } }
private local instance instBorelTangent (x : M) :
    BorelSpace (TangentSpace I x) := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.instBorelTangent
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.instBorelTangent target :: scope.openDecls } }

omit [T2Space (TangentBundle I M)] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
def SegmentInt [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
  (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (x : M) : Set (TangentSpace I x) :=
  {v | ∃ c : ℝ, 1 < c ∧ c • v ∈ SegmentDom (I := I) g hEnorm x}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.SegmentInt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.VolumeComparison.SegmentInt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.SegmentInt ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.SegmentInt

omit [T2Space (TangentBundle I M)] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem mem_segmentInt [PseudoEMetricSpace M] [IsRiemannianManifold I M]
    [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w))}
    {x : M} {v : TangentSpace I x} :
    v ∈ SegmentInt (I := I) g hEnorm x ↔
      ∃ c : ℝ, 1 < c ∧ c • v ∈ SegmentDom (I := I) g hEnorm x :=
  Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.mem_segmentInt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.VolumeComparison.mem_segmentInt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.mem_segmentInt ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.mem_segmentInt

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem segmentInt_subset [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (x : M) :
    SegmentInt (I := I) g hEnorm x ⊆ SegmentDom (I := I) g hEnorm x := by
  rintro v ⟨c, hc, hcv⟩
  have hc0 : 0 < c := one_pos.trans hc
  have hs0 : 0 ≤ c⁻¹ := inv_nonneg.mpr hc0.le
  have hs1 : c⁻¹ ≤ 1 := (inv_le_one₀ hc0).2 hc.le
  have h := segmentDom_smul (I := I) g hEnorm hcv hs0 hs1
  simpa only [smul_smul, inv_mul_cancel₀ hc0.ne', one_smul] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.segmentInt_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.VolumeComparison.segmentInt_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.segmentInt_subset ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.segmentInt_subset

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem segmentInt_smul [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    {x : M} {v : TangentSpace I x}
    (hv : v ∈ SegmentInt (I := I) g hEnorm x)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    s • v ∈ SegmentInt (I := I) g hEnorm x := by
  obtain ⟨c, hc, hcv⟩ := hv
  refine ⟨c, hc, ?_⟩
  simpa only [smul_smul, mul_comm] using
    (segmentDom_smul (I := I) g hEnorm hcv hs0 hs1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.segmentInt_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.VolumeComparison.segmentInt_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.segmentInt_smul ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.segmentInt_smul

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem measurableSet_segmentInt [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (x : M) :
    MeasurableSet (SegmentInt (I := I) g hEnorm x) := by
  let Q : Set ℚ := {q | (1 : ℝ) < (q : ℝ)}
  let A : ℚ → Set (TangentSpace I x) := fun q =>
    (fun v => (q : ℝ) • v) ⁻¹' SegmentDom (I := I) g hEnorm x
  have hA (q : ℚ) : MeasurableSet (A q) := by
    exact (isClosed_segmentDom (I := I) g hEnorm x).preimage
      (_root_.ContinuousConstSMul.continuous_const_smul (q : ℝ)) |>.measurableSet
  have hEq : SegmentInt (I := I) g hEnorm x = ⋃ q ∈ Q, A q := by
    ext v
    constructor
    · rintro ⟨c, hc, hcv⟩
      obtain ⟨q : ℚ, hq1, hqc⟩ := exists_rat_btwn hc
      have hc0 : 0 < c := one_pos.trans hc
      have hq0 : 0 ≤ (q : ℝ) := (zero_lt_one.trans hq1).le
      have hs0 : 0 ≤ (q : ℝ) / c := div_nonneg hq0 hc0.le
      have hs1 : (q : ℝ) / c ≤ 1 := (div_le_one hc0).mpr hqc.le
      have hqv : (q : ℝ) • v ∈ SegmentDom (I := I) g hEnorm x := by
        have h := segmentDom_smul (I := I) g hEnorm hcv hs0 hs1
        have hcne : c ≠ 0 := hc0.ne'
        simpa only [smul_smul, div_mul_cancel₀ _ hcne] using h
      exact mem_iUnion₂.mpr ⟨q, hq1, hqv⟩
    · rintro hv
      obtain ⟨q, hqQ, hqv⟩ := mem_iUnion₂.mp hv
      exact ⟨(q : ℝ), hqQ, hqv⟩
  rw [hEq]
  exact MeasurableSet.biUnion (Set.to_countable Q) fun q _ => hA q

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.measurableSet_segmentInt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.VolumeComparison.measurableSet_segmentInt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.measurableSet_segmentInt ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.measurableSet_segmentInt

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem exp_inj_segmentInt [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (x : M) :
    Set.InjOn (expMapIntrinsic (I := I) g hEnorm x)
      (SegmentInt (I := I) g hEnorm x) := by
  classical
  intro v hv w hw heq
  have hvD : v ∈ SegmentDom (I := I) g hEnorm x :=
    segmentInt_subset (I := I) g hEnorm x hv
  have hwD : w ∈ SegmentDom (I := I) g hEnorm x :=
    segmentInt_subset (I := I) g hEnorm x hw
  let L : ℝ := Real.sqrt (g.inner x v v)
  have hlen :
      Real.sqrt (g.inner x w w) = L := by
    calc
      Real.sqrt (g.inner x w w) =
          (_root_.Manifold.riemannianEDist I x
            (expMapIntrinsic (I := I) g hEnorm x w)).toReal :=
        (mem_segmentDom (I := I)).mp hwD
      _ = (_root_.Manifold.riemannianEDist I x
            (expMapIntrinsic (I := I) g hEnorm x v)).toReal := by
        rw [heq]
      _ = L := ((mem_segmentDom (I := I)).mp hvD).symm
  by_cases hv0 : v = 0
  · subst v
    have hL0 : L = 0 := by
      simp only [L, map_zero, Real.sqrt_zero]
    have hwlen0 : Real.sqrt (g.inner x w w) = 0 := hlen.trans hL0
    have hw0 : w = 0 := by
      by_contra hne
      have hpos : 0 < Real.sqrt (g.inner x w w) :=
        Real.sqrt_pos.mpr (g.pos x w hne)
      linarith
    exact hw0.symm
  have hw0 : w ≠ 0 := by
    intro hwz
    subst w
    have hwlen0 : Real.sqrt (g.inner x (0 : TangentSpace I x) 0) = 0 := by
      simp
    have hL0 : L = 0 := hlen.symm.trans hwlen0
    have hLpos : 0 < L := Real.sqrt_pos.mpr (g.pos x v hv0)
    linarith
  have hLpos : 0 < L := Real.sqrt_pos.mpr (g.pos x v hv0)
  have hLne : L ≠ 0 := hLpos.ne'
  let u : TangentSpace I x := L⁻¹ • v
  let z : TangentSpace I x := L⁻¹ • w
  have hvinner : g.inner x v v = L ^ 2 := by
    have hsq := Real.sq_sqrt (gInner_self_nonneg (I := I) g x v)
    simpa only [L] using hsq.symm
  have hwinner : g.inner x w w = L ^ 2 := by
    have hsq := Real.sq_sqrt (gInner_self_nonneg (I := I) g x w)
    rw [hlen] at hsq
    exact hsq.symm
  have hu_unit : g.inner x u u = 1 := by
    dsimp only [u]
    rw [gInner_smul_self (I := I) g x, hvinner]
    field_simp [hLne]
  have hz_unit : g.inner x z z = 1 := by
    dsimp only [z]
    rw [gInner_smul_self (I := I) g x, hwinner]
    field_simp [hLne]
  have hLu : L • u = v := by
    dsimp only [u]
    rw [smul_smul]
    field_simp [hLne]
    simp
  have hLz : L • z = w := by
    dsimp only [z]
    rw [smul_smul]
    field_simp [hLne]
    simp
  obtain ⟨c, hc, hcv⟩ := hv
  have hc0 : 0 < c := one_pos.trans hc
  let ell : ℝ := (c - 1) * L
  have hell : 0 < ell := mul_pos (sub_pos.mpr hc) hLpos
  have hLell : L + ell = c * L := by
    dsimp only [ell]
    ring
  let γv : ℝ → M := intrinsicGeodesic (I := I) g hEnorm x u
  let γw : ℝ → M := intrinsicGeodesic (I := I) g hEnorm x z
  have hγv_geo : Geodesic.IsGeodesic (I := I) g γv :=
    intrinsicGeodesic_isGeodesic (I := I) g hEnorm x u
  have hγw_geo : Geodesic.IsGeodesic (I := I) g γw :=
    intrinsicGeodesic_isGeodesic (I := I) g hEnorm x z
  have hγv_cont : Continuous γv :=
    intrinsicGeodesic_continuous (I := I) g hEnorm x u
  have hγw_cont : Continuous γw :=
    intrinsicGeodesic_continuous (I := I) g hEnorm x z
  have hγv_smooth : ContMDiff 𝓘(ℝ, ℝ) I ∞ γv :=
    isGeodesic_contMDiff (I := I) g hγv_geo hγv_cont
  have hγw_smooth : ContMDiff 𝓘(ℝ, ℝ) I ∞ γw :=
    isGeodesic_contMDiff (I := I) g hγw_geo hγw_cont
  have hγv_unit (t : ℝ) :
      g.inner (γv t)
          (mfderiv 𝓘(ℝ, ℝ) I γv t 1)
          (mfderiv 𝓘(ℝ, ℝ) I γv t 1) = 1 := by
    simpa only [γv, hu_unit] using
      (intrinsicGeodesic_speedSq_eq (I := I) g hEnorm x u t)
  have hγw_unit (t : ℝ) :
      g.inner (γw t)
          (mfderiv 𝓘(ℝ, ℝ) I γw t 1)
          (mfderiv 𝓘(ℝ, ℝ) I γw t 1) = 1 := by
    simpa only [γw, hz_unit] using
      (intrinsicGeodesic_speedSq_eq (I := I) g hEnorm x z t)
  have hγvL :
      γv L = expMapIntrinsic (I := I) g hEnorm x v := by
    calc
      γv L = intrinsicGeodesic (I := I) g hEnorm x (L • u) 1 :=
        (intrinsicGeodesic_smul (I := I) g hEnorm x u L).symm
      _ = expMapIntrinsic (I := I) g hEnorm x v := by
        rw [hLu]
        rfl
  have hγwL :
      γw L = expMapIntrinsic (I := I) g hEnorm x w := by
    calc
      γw L = intrinsicGeodesic (I := I) g hEnorm x (L • z) 1 :=
        (intrinsicGeodesic_smul (I := I) g hEnorm x z L).symm
      _ = expMapIntrinsic (I := I) g hEnorm x w := by
        rw [hLz]
        rfl
  let a : TangentSpace I (γv L) :=
    mfderiv 𝓘(ℝ, ℝ) I γv L (1 : ℝ)
  let σ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm (γv L) a
  have hσ_geo : Geodesic.IsGeodesic (I := I) g σ :=
    intrinsicGeodesic_isGeodesic (I := I) g hEnorm (γv L) a
  have hσ_cont : Continuous σ :=
    intrinsicGeodesic_continuous (I := I) g hEnorm (γv L) a
  have hσ_smooth : ContMDiff 𝓘(ℝ, ℝ) I ∞ σ :=
    isGeodesic_contMDiff (I := I) g hσ_geo hσ_cont
  have ha_unit : g.inner (γv L) a a = 1 := by
    convert hγv_unit L using 1
    all_goals rfl
  have hσ_unit (t : ℝ) :
      g.inner (σ t)
          (mfderiv 𝓘(ℝ, ℝ) I σ t 1)
          (mfderiv 𝓘(ℝ, ℝ) I σ t 1) = 1 := by
    simpa only [σ, ha_unit] using
      (intrinsicGeodesic_speedSq_eq (I := I) g hEnorm (γv L) a t)
  have hcontv :
      (fun s => γv (s + L)) = σ := by
    simpa only [γv, a, σ] using
      (intrinsicGeodesic_continuation (I := I) g hEnorm x u L)
  have hcvscale : (c * L) • u = c • v := by
    rw [_root_.SemigroupAction.mul_smul, hLu]
  have hσell :
      σ ell = expMapIntrinsic (I := I) g hEnorm x (c • v) := by
    calc
      σ ell = γv (ell + L) := by
        rw [← congrFun hcontv ell]
      _ = γv (c * L) := by rw [add_comm ell L, hLell]
      _ = intrinsicGeodesic (I := I) g hEnorm x ((c * L) • u) 1 :=
        (intrinsicGeodesic_smul (I := I) g hEnorm x u (c * L)).symm
      _ = expMapIntrinsic (I := I) g hEnorm x (c • v) := by
        rw [hcvscale]
        rfl
  have hdistc :
      _root_.Manifold.riemannianEDist I x
          (expMapIntrinsic (I := I) g hEnorm x (c • v)) =
        ENNReal.ofReal (c * L) := by
    have hreal :
        c * L =
          (_root_.Manifold.riemannianEDist I x
            (expMapIntrinsic (I := I) g hEnorm x (c • v))).toReal := by
      calc
        c * L = Real.sqrt (g.inner x (c • v) (c • v)) := by
          rw [sqrt_gInner_smul_self (I := I) g x hc0.le v]
        _ = (_root_.Manifold.riemannianEDist I x
            (expMapIntrinsic (I := I) g hEnorm x (c • v))).toReal :=
          (mem_segmentDom (I := I)).mp hcv
    rw [← ENNReal.ofReal_toReal
      (riemannianEDist_ne_top (I := I) x
        (expMapIntrinsic (I := I) g hEnorm x (c • v)))]
    congr 1
    exact hreal.symm
  have hγw0 : γw 0 = x :=
    intrinsicGeodesic_zero (I := I) g hEnorm x z
  have hσ0 : σ 0 = γv L :=
    intrinsicGeodesic_zero (I := I) g hEnorm (γv L) a
  have hjunc : γw L = σ 0 := by
    rw [hγwL, hσ0, hγvL, ← heq]
  have hmin :
      _root_.Manifold.riemannianEDist I (γw 0) (σ ell) =
        ENNReal.ofReal (L + ell) := by
    rw [hγw0, hσell, hdistc, hLell]
  have hmatch :
      mfderiv 𝓘(ℝ, ℝ) I γw L (1 : ℝ) =
        mfderiv 𝓘(ℝ, ℝ) I σ 0 (1 : ℝ) :=
    broken_minimizer_velocity_match (I := I) g hEnorm hLpos hell
      (hγw_geo.isGeodesicOn (_root_.Set.Icc 0 L))
      (hσ_geo.isGeodesicOn (_root_.Set.Icc 0 ell))
      hγw_smooth hσ_smooth
      (fun t _ => hγw_unit t) (fun t _ => hσ_unit t) hjunc hmin
  have hσvelocity :
      (mfderiv 𝓘(ℝ, ℝ) I σ 0 (1 : ℝ) : E) = (a : E) := by
    simpa only [σ] using
      (intrinsicGeodesic_mfderiv_zero (I := I) g hEnorm (γv L) a)
  have hvel :
      (mfderiv 𝓘(ℝ, ℝ) I γw L (1 : ℝ) : E) =
        (mfderiv 𝓘(ℝ, ℝ) I γv L (1 : ℝ) : E) := by
    rw [hmatch, hσvelocity]
  have hcontw :=
    intrinsicGeodesic_continuation (I := I) g hEnorm x z L
  have hfoot : γw L = γv L :=
    hγwL.trans (heq.symm.trans hγvL.symm)
  have hcontw' :
      (fun s => γw (s + L)) = σ := by
    calc
      (fun s => γw (s + L)) =
          intrinsicGeodesic (I := I) g hEnorm (γw L)
            (mfderiv 𝓘(ℝ, ℝ) I γw L (1 : ℝ)) := by
        simpa only [γw] using hcontw
      _ = σ := by
        rw [hfoot]
        change intrinsicGeodesic (I := I) g hEnorm (γv L)
            (mfderiv 𝓘(ℝ, ℝ) I γw L (1 : ℝ)) =
          intrinsicGeodesic (I := I) g hEnorm (γv L) a
        rw [show (mfderiv 𝓘(ℝ, ℝ) I γw L (1 : ℝ) :
              TangentSpace I (γv L)) = a by
          exact hvel]
  have hshift :
      (fun s => γw (s + L)) = fun s => γv (s + L) := by
    exact hcontw'.trans hcontv.symm
  have hcurves : γw = γv := by
    funext t
    have ht := congrFun hshift (t - L)
    simpa only [sub_add_cancel] using ht
  have huz : (z : E) = (u : E) := by
    have hderiv := congrArg
      (fun γ : ℝ → M => (mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ) : E)) hcurves
    have hγw0 :
        (mfderiv 𝓘(ℝ, ℝ) I γw 0 (1 : ℝ) : E) = (z : E) := by
      change (mfderiv 𝓘(ℝ, ℝ) I
        (intrinsicGeodesic (I := I) g hEnorm x z) 0 (1 : ℝ) : E) = (z : E)
      exact intrinsicGeodesic_mfderiv_zero (I := I) g hEnorm x z
    have hγv0 :
        (mfderiv 𝓘(ℝ, ℝ) I γv 0 (1 : ℝ) : E) = (u : E) := by
      change (mfderiv 𝓘(ℝ, ℝ) I
        (intrinsicGeodesic (I := I) g hEnorm x u) 0 (1 : ℝ) : E) = (u : E)
      exact intrinsicGeodesic_mfderiv_zero (I := I) g hEnorm x u
    exact hγw0.symm.trans (hderiv.trans hγv0)
  calc
    v = L • u := hLu.symm
    _ = L • z := congrArg (fun y : E => L • y) huz.symm
    _ = w := hLz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.exp_inj_segmentInt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.VolumeComparison.exp_inj_segmentInt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.exp_inj_segmentInt ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.exp_inj_segmentInt

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem segmentInt_no_conj [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    {x : M} {v : TangentSpace I x}
    (hv : v ∈ SegmentInt (I := I) g hEnorm x) :
    ¬ IsConjVec (I := I) g hEnorm x (v : E) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  by_cases hv0 : v = 0
  · subst v
    simp only [IsConjVec, _root_.Classical.not_not]
    change Function.Injective fun w : E =>
      mfderiv 𝓘(ℝ, E) I
        (fun b : E => expMapIntrinsic (I := I) g hEnorm x
          (show TangentSpace I x from b))
        (0 : E) w
    rw [mfderiv_expMapIntrinsic_at_zero (I := I) g hEnorm x]
    exact Function.injective_id
  obtain ⟨c, hc, hcv⟩ := hv
  have hc0 : 0 < c := one_pos.trans hc
  have hcv0 : c • v ≠ 0 := smul_ne_zero hc0.ne' hv0
  have ht : c⁻¹ ∈ _root_.Set.Ioo (0 : ℝ) 1 :=
    ⟨inv_pos.mpr hc0, (inv_lt_one₀ hc0).2 hc⟩
  have hno :=
    segmentDom_no_conj (I := I) g hEnorm hcv hcv0 c⁻¹ ht
  simpa only [smul_smul, inv_mul_cancel₀ hc0.ne', one_smul] using hno

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.segmentInt_no_conj then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.VolumeComparison.segmentInt_no_conj"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.segmentInt_no_conj ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.segmentInt_no_conj

omit [T2Space (TangentBundle I M)] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem segmentEnd_ray_sub [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (x : M) (u : TangentSpace I x) :
    ({r : _root_.Set.Ioi (0 : ℝ) |
      r.1 • u ∈
        SegmentDom (I := I) g hEnorm x \ SegmentInt (I := I) g hEnorm x} :
      Set (_root_.Set.Ioi (0 : ℝ))).Subsingleton := by
  rintro ⟨a, ha0⟩ ⟨haD, haI⟩ ⟨b, hb0⟩ ⟨hbD, hbI⟩
  have ha_pos : 0 < a := ha0
  have hb_pos : 0 < b := hb0
  apply Subtype.ext
  rcases lt_trichotomy a b with hab | hab | hab
  · exfalso
    apply haI
    refine ⟨b / a, (one_lt_div ha_pos).2 hab, ?_⟩
    rw [smul_smul, div_mul_cancel₀ b ha_pos.ne']
    exact hbD
  · exact hab
  · exfalso
    apply hbI
    refine ⟨a / b, (one_lt_div hb_pos).2 hab, ?_⟩
    rw [smul_smul, div_mul_cancel₀ a hb_pos.ne']
    exact haD

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.segmentEnd_ray_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.VolumeComparison.segmentEnd_ray_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.segmentEnd_ray_sub ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.segmentEnd_ray_sub

omit [T2Space (TangentBundle I M)] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem segmentEnd_zero [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (x : M) :
    (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)
        ((normalFrame (I := I) (E := E) g x) ⁻¹'
          (SegmentDom (I := I) g hEnorm x \ SegmentInt (I := I) g hEnorm x)) = 0 := by
  classical
  let : Nontrivial E :=
    Module.nontrivial_of_finrank_pos
      (show 0 < Module.finrank ℝ E from NeZero.pos _)
  let L := normalFrame (I := I) (E := E) g x
  let B : Set E :=
    L ⁻¹' (SegmentDom (I := I) g hEnorm x \ SegmentInt (I := I) g hEnorm x)
  let f : E → ℝ≥0∞ := B.indicator fun _ => 1
  have hB : MeasurableSet B := by
    exact ((measurableSet_segmentDom (I := I) g hEnorm x).diff
      (measurableSet_segmentInt (I := I) g hEnorm x)).preimage
        L.continuous.measurable
  have hf : Measurable f :=
    measurable_const.indicator hB
  change (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) B = 0
  calc
    (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) B = ∫⁻ z : E, f z ∂volume :=
      (_root_.MeasureTheory.lintegral_indicator_one hB).symm
    _ = ∫⁻ u : Metric.sphere (0 : E) 1,
          ∫⁻ r : _root_.Set.Ioi (0 : ℝ), f (r.1 • u.1)
            ∂(Measure.volumeIoiPow (Module.finrank ℝ E - 1))
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E).toSphere :=
      lintegral_polar (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) f hf.aemeasurable
    _ = 0 := by
      apply _root_.MeasureTheory.lintegral_eq_zero_of_ae_eq_zero
      filter_upwards with u
      let A : Set (_root_.Set.Ioi (0 : ℝ)) := {r | r.1 • u.1 ∈ B}
      have hA : MeasurableSet A := by
        exact hB.preimage (continuous_subtype_val.smul continuous_const).measurable
      have hAsub : A.Subsingleton := by
        intro r hr s hs
        change L (r.1 • u.1) ∈
          SegmentDom (I := I) g hEnorm x \ SegmentInt (I := I) g hEnorm x at hr
        change L (s.1 • u.1) ∈
          SegmentDom (I := I) g hEnorm x \ SegmentInt (I := I) g hEnorm x at hs
        have hr' : (r : ℝ) • L (u : E) ∈
            SegmentDom (I := I) g hEnorm x \ SegmentInt (I := I) g hEnorm x := by
          rw [← map_smul]
          exact hr
        have hs' : (s : ℝ) • L (u : E) ∈
            SegmentDom (I := I) g hEnorm x \ SegmentInt (I := I) g hEnorm x := by
          rw [← map_smul]
          exact hs
        exact (segmentEnd_ray_sub (I := I) g hEnorm x (L u.1)) hr' hs'
      have hbase :
          (Measure.comap ((↑) : _root_.Set.Ioi (0 : ℝ) → ℝ) _root_.MeasureTheory.MeasureSpace.volume) A = 0 := by
        rw [comap_subtype_coe_apply measurableSet_Ioi]
        exact (hAsub.image ((↑) : _root_.Set.Ioi (0 : ℝ) → ℝ)).measure_zero _root_.MeasureTheory.MeasureSpace.volume
      have hAzero :
          (Measure.volumeIoiPow (Module.finrank ℝ E - 1)) A = 0 := by
        rw [Measure.volumeIoiPow]
        exact _root_.MeasureTheory.withDensity_absolutelyContinuous _ _ hbase
      calc
        ∫⁻ r : _root_.Set.Ioi (0 : ℝ), f (r.1 • u.1)
              ∂(Measure.volumeIoiPow (Module.finrank ℝ E - 1)) =
            ∫⁻ r : _root_.Set.Ioi (0 : ℝ), A.indicator (fun _ => 1) r
              ∂(Measure.volumeIoiPow (Module.finrank ℝ E - 1)) := by
          apply _root_.MeasureTheory.lintegral_congr
          intro r
          by_cases hr : r.1 • u.1 ∈ B
          · have hrA : r ∈ A := hr
            simp only [f, Set.indicator_of_mem hr, Set.indicator_of_mem hrA]
          · have hrA : r ∉ A := hr
            simp only [f, Set.indicator_of_notMem hr, Set.indicator_of_notMem hrA]
        _ = (Measure.volumeIoiPow (Module.finrank ℝ E - 1)) A :=
          _root_.MeasureTheory.lintegral_indicator_one hA
        _ = 0 := hAzero

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.segmentEnd_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.VolumeComparison.segmentEnd_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.segmentEnd_zero ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.segmentEnd_zero

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison

end
