import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CurvatureNormalization
import Submission.DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic
import Submission.DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling
import Mathlib.Topology.Instances.ENNReal.Lemmas

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Filter _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Exponential
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal _root_.Topology _root_.Submission.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance ascrIsManifoldOne : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ascrIsManifoldOne
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ascrIsManifoldOne target :: scope.openDecls } }

def scalarCurvatureDistanceTail (g : SmoothRiemannianMetric I M) (p : M)
    (rho : ℝ) : ℝ≥0∞ :=
  ⨆ (x : M) (_ : rho ≤ (riemannianEDistOf g p x).toReal),
    ENNReal.ofReal (metricScalarAt (I := I) g x *
      ((riemannianEDistOf g p x).toReal) ^ 2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarCurvatureDistanceTail then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarCurvatureDistanceTail"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarCurvatureDistanceTail ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarCurvatureDistanceTail

def asymptoticScalarCurvatureRatio (g : SmoothRiemannianMetric I M) (p : M) : ℝ≥0∞ :=
  ⨅ (rho : ℝ) (_ : 0 < rho), scalarCurvatureDistanceTail g p rho

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.asymptoticScalarCurvatureRatio then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.asymptoticScalarCurvatureRatio"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.asymptoticScalarCurvatureRatio ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.asymptoticScalarCurvatureRatio


theorem asymptoticScalarCurvatureRatio_le_tail
    (g : SmoothRiemannianMetric I M) (p : M) {rho : ℝ} (hrho : 0 < rho) :
    asymptoticScalarCurvatureRatio g p ≤ scalarCurvatureDistanceTail g p rho :=
  iInf_le_of_le rho (iInf_le _ hrho)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.asymptoticScalarCurvatureRatio_le_tail then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.asymptoticScalarCurvatureRatio_le_tail"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.asymptoticScalarCurvatureRatio_le_tail ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.asymptoticScalarCurvatureRatio_le_tail

theorem asymptoticScalarCurvatureRatio_eq_top_iff
    (g : SmoothRiemannianMetric I M) (p : M) :
    asymptoticScalarCurvatureRatio g p = ⊤ ↔
      ∀ A D : ℝ, 0 < A → 0 < D → ∃ x : M,
        D ≤ (riemannianEDistOf g p x).toReal ∧
          A < metricScalarAt (I := I) g x *
            ((riemannianEDistOf g p x).toReal) ^ 2 := by
  constructor
  · intro htop A D hA hD
    have htail : scalarCurvatureDistanceTail g p D = ⊤ := by
      apply top_unique
      rw [← htop]
      exact asymptoticScalarCurvatureRatio_le_tail g p hD
    have hlt : ENNReal.ofReal A < scalarCurvatureDistanceTail g p D := by
      rw [htail]
      exact ENNReal.ofReal_lt_top
    obtain ⟨x, hx⟩ := lt_iSup_iff.mp hlt
    obtain ⟨hxD, hxA⟩ := lt_iSup_iff.mp hx
    exact ⟨x, hxD, (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hA.le).mp hxA⟩
  · intro hfar
    simp only [asymptoticScalarCurvatureRatio, iInf_eq_top]
    intro D hD
    apply iSup_eq_top.mpr
    intro b hb
    obtain ⟨x, hxD, hxA⟩ := hfar (b.toReal + 1) D (by positivity) hD
    have hbA : b < ENNReal.ofReal (b.toReal + 1) := by
      conv_lhs => rw [← ENNReal.ofReal_toReal hb.ne]
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg).mpr
        (by linarith)
    have hAx : ENNReal.ofReal (b.toReal + 1) <
        ENNReal.ofReal (metricScalarAt (I := I) g x *
          ((riemannianEDistOf g p x).toReal) ^ 2) :=
      (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).mpr hxA
    refine ⟨x, ?_⟩
    exact lt_iSup_iff.mpr ⟨hxD, hbA.trans hAx⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.asymptoticScalarCurvatureRatio_eq_top_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.asymptoticScalarCurvatureRatio_eq_top_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.asymptoticScalarCurvatureRatio_eq_top_iff ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.asymptoticScalarCurvatureRatio_eq_top_iff

private theorem ascr_scalar_scale
    (g : SmoothRiemannianMetric I M) (c : ℝ) (hc : 0 < c) (x : M) :
    metricScalarAt (I := I) (scaleMetric c hc g) x =
      c⁻¹ * metricScalarAt (I := I) g x := by
  let S : SolutionOn (I := I) (M := M) ancientTimeInterval := ⟨⟨fun _ => g⟩⟩
  have h := congrFun (congrFun (parabolicSolution_scalar (I := I) S 0 c hc
    (by change (0 : ℝ) ≤ 0; exact le_rfl)) 0) x
  change metricScalarAt (I := I) (scaleMetric c hc g) x =
    c⁻¹ * metricScalarAt (I := I) g x at h
  exact h

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ascr_scalar_scale
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ascr_scalar_scale target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
private theorem ascr_distance_scale
    (g : SmoothRiemannianMetric I M) (c : ℝ) (hc : 0 < c) (p x : M) :
    (riemannianEDistOf (scaleMetric c hc g) p x).toReal =
      Real.sqrt c * (riemannianEDistOf g p x).toReal := by
  rw [edistOf_scale, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg c)]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ascr_distance_scale
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ascr_distance_scale target :: scope.openDecls } }

theorem scalarCurvature_mul_sq_distance_scaleMetric
    (g : SmoothRiemannianMetric I M) (c : ℝ) (hc : 0 < c) (p x : M) :
    metricScalarAt (I := I) (scaleMetric c hc g) x *
        ((riemannianEDistOf (scaleMetric c hc g) p x).toReal) ^ 2 =
      metricScalarAt (I := I) g x * ((riemannianEDistOf g p x).toReal) ^ 2 := by
  rw [ascr_scalar_scale, ascr_distance_scale, mul_pow, Real.sq_sqrt hc.le]
  calc
    c⁻¹ * metricScalarAt (I := I) g x *
        (c * ((riemannianEDistOf g p x).toReal) ^ 2) =
      (c⁻¹ * c) * (metricScalarAt (I := I) g x *
        ((riemannianEDistOf g p x).toReal) ^ 2) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hc.ne', one_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarCurvature_mul_sq_distance_scaleMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarCurvature_mul_sq_distance_scaleMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarCurvature_mul_sq_distance_scaleMetric ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarCurvature_mul_sq_distance_scaleMetric


theorem scalarCurvatureDistanceTail_scaleMetric
    (g : SmoothRiemannianMetric I M) (c : ℝ) (hc : 0 < c) (p : M) (rho : ℝ) :
    scalarCurvatureDistanceTail (scaleMetric c hc g) p (Real.sqrt c * rho) =
      scalarCurvatureDistanceTail g p rho := by
  have hsqrt : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  unfold scalarCurvatureDistanceTail
  simp_rw [scalarCurvature_mul_sq_distance_scaleMetric,
    ascr_distance_scale, mul_le_mul_iff_right₀ hsqrt]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarCurvatureDistanceTail_scaleMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarCurvatureDistanceTail_scaleMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarCurvatureDistanceTail_scaleMetric ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarCurvatureDistanceTail_scaleMetric

theorem asymptoticScalarCurvatureRatio_scaleMetric
    (g : SmoothRiemannianMetric I M) (c : ℝ) (hc : 0 < c) (p : M) :
    asymptoticScalarCurvatureRatio (scaleMetric c hc g) p =
      asymptoticScalarCurvatureRatio g p := by
  have hsqrt : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  apply le_antisymm
  · refine le_iInf fun rho => le_iInf fun hrho => ?_
    calc
      asymptoticScalarCurvatureRatio (scaleMetric c hc g) p ≤
          scalarCurvatureDistanceTail (scaleMetric c hc g) p (Real.sqrt c * rho) :=
        asymptoticScalarCurvatureRatio_le_tail _ _ (mul_pos hsqrt hrho)
      _ = scalarCurvatureDistanceTail g p rho :=
        scalarCurvatureDistanceTail_scaleMetric g c hc p rho
  · refine le_iInf fun rho => le_iInf fun hrho => ?_
    calc
      asymptoticScalarCurvatureRatio g p ≤
          scalarCurvatureDistanceTail g p (rho / Real.sqrt c) :=
        asymptoticScalarCurvatureRatio_le_tail _ _ (div_pos hrho hsqrt)
      _ = scalarCurvatureDistanceTail (scaleMetric c hc g) p
          (Real.sqrt c * (rho / Real.sqrt c)) :=
        (scalarCurvatureDistanceTail_scaleMetric g c hc p _).symm
      _ = scalarCurvatureDistanceTail (scaleMetric c hc g) p rho := by
        rw [mul_div_cancel₀ rho hsqrt.ne']

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.asymptoticScalarCurvatureRatio_scaleMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.asymptoticScalarCurvatureRatio_scaleMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.asymptoticScalarCurvatureRatio_scaleMetric ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.asymptoticScalarCurvatureRatio_scaleMetric

section Basepoint

variable [ConnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [FiniteDimensional ℝ E] [CompleteSpace E] in
private theorem ascr_real_distance_triangle
    (g : SmoothRiemannianMetric I M) (p q x : M) :
    (riemannianEDistOf g p x).toReal ≤
      (riemannianEDistOf g p q).toReal + (riemannianEDistOf g q x).toReal := by
  let _ : _root_.Bundle.RiemannianBundle (fun y : M => TangentSpace I y) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro y v w; rfl⟩⟩
  change (_root_.Manifold.riemannianEDist I p x).toReal ≤
    (_root_.Manifold.riemannianEDist I p q).toReal + (_root_.Manifold.riemannianEDist I q x).toReal
  have h := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨riemannianEDist_ne_top (I := I) p q,
      riemannianEDist_ne_top (I := I) q x⟩)
    (_root_.Manifold.riemannianEDist_triangle (I := I) (x := p) (y := q) (z := x))
  simpa only [ENNReal.toReal_add (riemannianEDist_ne_top (I := I) p q)
    (riemannianEDist_ne_top (I := I) q x)] using h

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ascr_real_distance_triangle
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ascr_real_distance_triangle target :: scope.openDecls } }

theorem asymptoticScalarCurvatureRatio_basepoint_le_mul
    (g : SmoothRiemannianMetric I M)
    (hscalar : ∀ x : M, 0 ≤ metricScalarAt (I := I) g x)
    (p q : M) (delta : ℝ) (hdelta : 0 < delta) :
    asymptoticScalarCurvatureRatio g q ≤
      ENNReal.ofReal ((1 + delta) ^ 2) * asymptoticScalarCurvatureRatio g p := by
  let k : ℝ≥0∞ := ENNReal.ofReal ((1 + delta) ^ 2)
  have hk0 : k ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))
  have hktop : k ≠ ⊤ := ENNReal.ofReal_ne_top
  let d : ℝ := (riemannianEDistOf g q p).toReal
  have hd : 0 ≤ d := ENNReal.toReal_nonneg
  have hddelta : 0 ≤ d / delta := div_nonneg hd hdelta.le
  calc
    asymptoticScalarCurvatureRatio g q ≤
        ⨅ (rho : ℝ) (_ : 0 < rho), k * scalarCurvatureDistanceTail g p rho := by
      refine le_iInf fun rho => le_iInf fun hrho => ?_
      calc
        asymptoticScalarCurvatureRatio g q ≤
            scalarCurvatureDistanceTail g q (rho + d + d / delta + 1) :=
          asymptoticScalarCurvatureRatio_le_tail _ _ (by linarith)
        _ ≤ k * scalarCurvatureDistanceTail g p rho := by
          refine iSup_le fun x => iSup_le fun hx => ?_
          have htriangle := ascr_real_distance_triangle g q p x
          change (riemannianEDistOf g q x).toReal ≤
            d + (riemannianEDistOf g p x).toReal at htriangle
          have hxp : rho ≤ (riemannianEDistOf g p x).toReal := by linarith
          have hdsmall : d / delta ≤ (riemannianEDistOf g p x).toReal := by linarith
          have hdmul : d ≤ delta * (riemannianEDistOf g p x).toReal := by
            simpa only [mul_comm] using (div_le_iff₀ hdelta).mp hdsmall
          have hdist : (riemannianEDistOf g q x).toReal ≤
              (1 + delta) * (riemannianEDistOf g p x).toReal := by nlinarith
          have hsquare : ((riemannianEDistOf g q x).toReal) ^ 2 ≤
              ((1 + delta) * (riemannianEDistOf g p x).toReal) ^ 2 :=
            (sq_le_sq₀ ENNReal.toReal_nonneg (by positivity)).mpr hdist
          have hproduct : metricScalarAt (I := I) g x *
              ((riemannianEDistOf g q x).toReal) ^ 2 ≤
              (1 + delta) ^ 2 * (metricScalarAt (I := I) g x *
                ((riemannianEDistOf g p x).toReal) ^ 2) := by
            calc
              _ ≤ metricScalarAt (I := I) g x *
                  ((1 + delta) * (riemannianEDistOf g p x).toReal) ^ 2 :=
                mul_le_mul_of_nonneg_left hsquare (hscalar x)
              _ = _ := by ring
          calc
            _ ≤ ENNReal.ofReal ((1 + delta) ^ 2 *
                (metricScalarAt (I := I) g x *
                  ((riemannianEDistOf g p x).toReal) ^ 2)) :=
              ENNReal.ofReal_le_ofReal hproduct
            _ = k * ENNReal.ofReal (metricScalarAt (I := I) g x *
                ((riemannianEDistOf g p x).toReal) ^ 2) :=
              ENNReal.ofReal_mul (sq_nonneg _)
            _ ≤ k * scalarCurvatureDistanceTail g p rho := by
              have htail : ENNReal.ofReal (metricScalarAt (I := I) g x *
                  ((riemannianEDistOf g p x).toReal) ^ 2) ≤
                  scalarCurvatureDistanceTail g p rho := by
                unfold scalarCurvatureDistanceTail
                exact le_iSup₂ (f := fun (y : M)
                  (_ : rho ≤ (riemannianEDistOf g p y).toReal) =>
                    ENNReal.ofReal (metricScalarAt (I := I) g y *
                      ((riemannianEDistOf g p y).toReal) ^ 2)) x hxp
              exact mul_le_mul_right htail k
    _ = k * asymptoticScalarCurvatureRatio g p := by
      simp only [asymptoticScalarCurvatureRatio, ENNReal.mul_iInf_of_ne hk0 hktop]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.asymptoticScalarCurvatureRatio_basepoint_le_mul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.asymptoticScalarCurvatureRatio_basepoint_le_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.asymptoticScalarCurvatureRatio_basepoint_le_mul ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.asymptoticScalarCurvatureRatio_basepoint_le_mul

private theorem ascr_basepoint_le
    (g : SmoothRiemannianMetric I M)
    (hscalar : ∀ x : M, 0 ≤ metricScalarAt (I := I) g x) (p q : M) :
    asymptoticScalarCurvatureRatio g q ≤ asymptoticScalarCurvatureRatio g p := by
  by_cases hp : asymptoticScalarCurvatureRatio g p = ⊤
  · rw [hp]
    exact le_top
  · let b : ℝ := (asymptoticScalarCurvatureRatio g p).toReal
    have hcontinuous : Continuous (fun delta : ℝ =>
        ENNReal.ofReal ((1 + delta) ^ 2 * b)) :=
      ENNReal.continuous_ofReal.comp (by fun_prop)
    have hlim : _root_.Filter.Tendsto (fun delta : ℝ => ENNReal.ofReal ((1 + delta) ^ 2 * b))
        (𝓝[>] (0 : ℝ)) (𝓝 (asymptoticScalarCurvatureRatio g p)) := by
      have hwithin : _root_.Filter.Tendsto (fun delta : ℝ => ENNReal.ofReal ((1 + delta) ^ 2 * b))
          (𝓝[>] (0 : ℝ)) (𝓝 (ENNReal.ofReal ((1 + (0 : ℝ)) ^ 2 * b))) :=
        (hcontinuous.tendsto 0).mono_left nhdsWithin_le_nhds
      simpa only [add_zero, one_pow, one_mul, b, ENNReal.ofReal_toReal hp] using
        hwithin
    apply ge_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin] with delta (hdelta : 0 < delta)
    have h := asymptoticScalarCurvatureRatio_basepoint_le_mul g hscalar p q delta hdelta
    rw [ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_toReal hp]
    exact h

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ascr_basepoint_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ascr_basepoint_le target :: scope.openDecls } }

theorem asymptoticScalarCurvatureRatio_basepoint_eq
    (g : SmoothRiemannianMetric I M)
    (hscalar : ∀ x : M, 0 ≤ metricScalarAt (I := I) g x) (p q : M) :
    asymptoticScalarCurvatureRatio g p = asymptoticScalarCurvatureRatio g q :=
  le_antisymm (ascr_basepoint_le g hscalar q p) (ascr_basepoint_le g hscalar p q)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.asymptoticScalarCurvatureRatio_basepoint_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.asymptoticScalarCurvatureRatio_basepoint_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.asymptoticScalarCurvatureRatio_basepoint_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.asymptoticScalarCurvatureRatio_basepoint_eq

end Basepoint

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
