import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.MetricComparison
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.Defs
import Submission.DifferentialGeometry.Geometry.Measure.MetricComparison
import Submission.DifferentialGeometry.Geometry.Metric.Distance.Ball

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Integral.Measure
open scoped _root_.Manifold _root_.ContDiff _root_.ENNReal

namespace DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem riemannianBallOf_subset_of_inner_le_mul
    (g h : SmoothRiemannianMetric I M) (p : M) {r Q : ℝ} (hQ : 0 < Q)
    (hlocal : ∀ q ∈ riemannianBallOf g p r, ∀ v : TangentSpace I q,
      h.inner q v v ≤ Q * g.inner q v v) :
    riemannianBallOf g p r ⊆ riemannianBallOf h p (Real.sqrt Q * r) := by
  intro z hz
  have hlen : ∀ (k : SmoothRiemannianMetric I M) (γ : ℝ → M) (a b : ℝ),
      (letI : _root_.Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨k.toRiemannianMetric⟩;
        _root_.Manifold.pathELength I γ a b) =
        ∫⁻ s in _root_.Set.Ioo a b, ENNReal.ofReal (Real.sqrt (k.inner (γ s)
          (mfderiv (modelWithCornersSelf ℝ ℝ) I γ s 1)
          (mfderiv (modelWithCornersSelf ℝ ℝ) I γ s 1))) := by
    intro k γ a b
    let : _root_.Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨k.toRiemannianMetric⟩
    rw [_root_.Manifold.pathELength_eq_lintegral_mfderiv_Ioo]
    apply _root_.MeasureTheory.lintegral_congr
    intro s
    exact Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm k (γ s) _
  obtain ⟨γ, h0, h1, hγ, hγlen⟩ : ∃ γ : ℝ → M, γ 0 = p ∧ γ 1 = z ∧
      ContMDiffOn (modelWithCornersSelf ℝ ℝ) I 1 γ (_root_.Set.Icc 0 1) ∧
      (letI : _root_.Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩;
        pathELength I γ 0 1) < ENNReal.ofReal r := by
    let : _root_.Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    change _root_.Manifold.riemannianEDist I p z < ENNReal.ofReal r at hz
    exact _root_.Manifold.exists_lt_of_riemannianEDist_lt hz
  have hstay : ∀ s ∈ _root_.Set.Ioo (0 : ℝ) 1, γ s ∈ riemannianBallOf g p r := by
    intro s hs
    let : _root_.Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    change _root_.Manifold.riemannianEDist I p (γ s) < ENNReal.ofReal r
    calc
      riemannianEDist I p (γ s) ≤ _root_.Manifold.pathELength I γ 0 s :=
        _root_.Manifold.riemannianEDist_le_pathELength (hγ.mono (_root_.Set.Icc_subset_Icc le_rfl hs.2.le)) h0 rfl
          hs.1.le
      _ ≤ _root_.Manifold.pathELength I γ 0 1 := _root_.Manifold.pathELength_mono le_rfl hs.2.le
      _ < ENNReal.ofReal r := hγlen
  have hcomp :
      (letI : _root_.Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨h.toRiemannianMetric⟩;
        _root_.Manifold.pathELength I γ 0 1) ≤ ENNReal.ofReal (Real.sqrt Q) *
      (letI : _root_.Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩;
        pathELength I γ 0 1) := by
    rw [hlen h, hlen g, ← _root_.MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply _root_.MeasureTheory.setLIntegral_mono' measurableSet_Ioo
    intro s hs
    have hroot := Real.sqrt_le_sqrt
      (hlocal (γ s) (hstay s hs) (mfderiv (modelWithCornersSelf ℝ ℝ) I γ s 1))
    rw [Real.sqrt_mul hQ.le] at hroot
    simpa only [ENNReal.ofReal_mul (Real.sqrt_nonneg Q)] using ENNReal.ofReal_le_ofReal hroot
  let : _root_.Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨h.toRiemannianMetric⟩
  change _root_.Manifold.riemannianEDist I p z < ENNReal.ofReal (Real.sqrt Q * r)
  calc
    riemannianEDist I p z ≤ _root_.Manifold.pathELength I γ 0 1 :=
      _root_.Manifold.riemannianEDist_le_pathELength hγ h0 h1 zero_le_one
    _ ≤ ENNReal.ofReal (Real.sqrt Q) *
        (letI : _root_.Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩;
          pathELength I γ 0 1) := hcomp
    _ < ENNReal.ofReal (Real.sqrt Q) * ENNReal.ofReal r :=
      ENNReal.mul_lt_mul_right (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr hQ)).ne'
        ENNReal.ofReal_ne_top hγlen
    _ = ENNReal.ofReal (Real.sqrt Q * r) := (ENNReal.ofReal_mul (Real.sqrt_nonneg Q)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.riemannianBallOf_subset_of_inner_le_mul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.riemannianBallOf_subset_of_inner_le_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.riemannianBallOf_subset_of_inner_le_mul ``Submission.DifferentialGeometry.riemannianBallOf_subset_of_inner_le_mul

end DifferentialGeometry

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
variable {D : RealTimeInterval}

theorem inner_le_exp_mul_inner_of_rmNormSq_le
    {S : SolutionOn (I := I) (M := M) D} (hS : IsSolutionOn (I := I) S)
    {T t ρ : ℝ} (hρ : 0 < ρ) (hslab : _root_.Set.Icc T t ⊆ D.carrier) (hreg : _root_.Set.Ioo T t ⊆ D.regular)
    {y : M} (hcurv : ∀ u ∈ _root_.Set.Icc T t, ρ ^ 4 * FlowMetricBall.rmNormSq S u y ≤ 1)
    {s₁ s₂ : ℝ} (hs₁ : s₁ ∈ _root_.Set.Icc T t) (hs₂ : s₂ ∈ _root_.Set.Icc T t) (v : TangentSpace I y) :
    (S.base.metric s₁).inner y v v ≤
      Real.exp (2 * ((Module.finrank ℝ E : ℝ) ^ 2 / ρ ^ 2 * |s₁ - s₂|)) *
        (S.base.metric s₂).inner y v v := by
  have hsqrt : Real.sqrt (1 / ρ ^ 4) = 1 / ρ ^ 2 := by
    have hr : 0 < ρ ^ 2 := sq_pos_of_pos hρ
    rw [show ρ ^ 4 = (ρ ^ 2) ^ 2 by ring]
    rw [show 1 / (ρ ^ 2) ^ 2 = (1 / ρ ^ 2) ^ 2 by field_simp]
    rw [Real.sqrt_sq_eq_abs, abs_of_pos (one_div_pos.mpr hr)]
  have hexp := inner_le_exp_mul_inner_of_abs_deriv_le S.base.metric
    (K := 2 * ((Module.finrank ℝ E : ℝ) ^ 2 / ρ ^ 2)) y v (fun q hq => by
      have hnorm : Tensor0SBundle.normSq0S (I := I) (S.base.metric q) y 4
          (S.base.rm04 q y) ≤ 1 / ρ ^ 4 := by
        apply (le_div_iff₀ (pow_pos hρ 4)).2
        simpa only [mul_comm, FlowMetricBall.rmNormSq] using hcurv q hq
      have hr := ricci_quadratic_form_bound_of_solution_curvature_bound (I := I) S y v hnorm
      rw [hsqrt] at hr
      have hr' : |ricciTensor (I := I) (S.base.metric q) y v v| ≤
          (Module.finrank ℝ E : ℝ) ^ 2 / ρ ^ 2 * (S.base.metric q).inner y v v := by
        simpa only [div_eq_mul_inv, one_mul] using hr
      refine ⟨_, metricPDE_Icc S hS hslab hreg q hq y v v, ?_⟩
      rw [abs_mul]
      norm_num
      nlinarith [hr']) hs₁ hs₂
  simpa only [mul_assoc] using hexp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.inner_le_exp_mul_inner_of_rmNormSq_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.inner_le_exp_mul_inner_of_rmNormSq_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.inner_le_exp_mul_inner_of_rmNormSq_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.inner_le_exp_mul_inner_of_rmNormSq_le

variable [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.instMeasurableSpace_differentialGeometry : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.instBorelSpace_differentialGeometry : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.instBorelSpace_differentialGeometry target :: scope.openDecls } }

theorem volume_riemannianBallOf_le_exp_mul_of_rmNormSq_le
    {S : SolutionOn (I := I) (M := M) D} (hS : IsSolutionOn (I := I) S)
    {T t ρ : ℝ} (hρ : 0 < ρ) (hTt : T ≤ t) (hslab : _root_.Set.Icc T t ⊆ D.carrier)
    (hreg : _root_.Set.Ioo T t ⊆ D.regular) (x : M)
    (hcurv : ∀ u ∈ _root_.Set.Icc T t, ∀ y ∈ riemannianBallOf (S.base.metric T) x ρ,
      ρ ^ 4 * FlowMetricBall.rmNormSq S u y ≤ 1) :
    riemannianVolumeMeasure (I := I) (M := M) (S.base.metric T)
        (riemannianBallOf (S.base.metric T) x ρ) ≤
      ENNReal.ofReal (Real.exp ((Module.finrank ℝ E : ℝ) *
          ((Module.finrank ℝ E : ℝ) ^ 2 / ρ ^ 2 * (t - T)))) *
        riemannianVolumeMeasure (I := I) (M := M) (S.base.metric t)
          (riemannianBallOf (S.base.metric t) x
            (Real.exp ((Module.finrank ℝ E : ℝ) ^ 2 / ρ ^ 2 * (t - T)) * ρ)) := by
  set A : ℝ := (Module.finrank ℝ E : ℝ) ^ 2 / ρ ^ 2 * (t - T) with hA
  have hT : T ∈ _root_.Set.Icc T t := left_mem_Icc.mpr hTt
  have ht : t ∈ _root_.Set.Icc T t := right_mem_Icc.mpr hTt
  have habs₁ : |t - T| = t - T := abs_of_nonneg (sub_nonneg.mpr hTt)
  have habs₂ : |T - t| = t - T := by rw [abs_sub_comm, habs₁]
  have hup : ∀ y ∈ riemannianBallOf (S.base.metric T) x ρ, ∀ v : TangentSpace I y,
      (S.base.metric t).inner y v v ≤ Real.exp (2 * A) * (S.base.metric T).inner y v v := by
    intro y hy v
    simpa only [habs₁] using
      inner_le_exp_mul_inner_of_rmNormSq_le hS hρ hslab hreg (hcurv · · y hy) ht hT v
  have hdown : ∀ y ∈ riemannianBallOf (S.base.metric T) x ρ, ∀ v : TangentSpace I y,
      (S.base.metric T).inner y v v ≤ Real.exp (2 * A) * (S.base.metric t).inner y v v := by
    intro y hy v
    simpa only [habs₂] using
      inner_le_exp_mul_inner_of_rmNormSq_le hS hρ hslab hreg (hcurv · · y hy) hT ht v
  have hsqrt : Real.sqrt (Real.exp (2 * A)) = Real.exp A := by
    rw [show 2 * A = A + A by ring, Real.exp_add, Real.sqrt_mul_self (Real.exp_pos A).le]
  have hsqrtPow : Real.sqrt (Real.exp (2 * A) ^ Module.finrank ℝ E) =
      Real.exp ((Module.finrank ℝ E : ℝ) * A) := by
    rw [← Real.exp_nat_mul, show (Module.finrank ℝ E : ℝ) * (2 * A) =
      (Module.finrank ℝ E : ℝ) * A + (Module.finrank ℝ E : ℝ) * A by ring, Real.exp_add,
      Real.sqrt_mul_self (Real.exp_pos _).le]
  have hsub : riemannianBallOf (S.base.metric T) x ρ ⊆
      riemannianBallOf (S.base.metric t) x (Real.exp A * ρ) := by
    simpa only [hsqrt] using
      riemannianBallOf_subset_of_inner_le_mul (S.base.metric T) (S.base.metric t) x
        (Real.exp_pos (2 * A)) hup
  have hmeas : MeasurableSet (riemannianBallOf (S.base.metric T) x ρ) :=
    (isOpen_lt (Geometry.Riemannian.continuous_riemannianEDist (S.base.metric T) x)
      continuous_const).measurableSet
  have hvol := Geometry.Measure.riemannianVolumeMeasure_apply_le_of_inner_le
    (I := I) (M := M) (S.base.metric t) (S.base.metric T) (Real.exp_pos (2 * A)) hmeas hdown
  rw [hsqrtPow] at hvol
  exact hvol.trans (mul_le_mul' le_rfl (_root_.MeasureTheory.measure_mono hsub))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.volume_riemannianBallOf_le_exp_mul_of_rmNormSq_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.volume_riemannianBallOf_le_exp_mul_of_rmNormSq_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.volume_riemannianBallOf_le_exp_mul_of_rmNormSq_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.volume_riemannianBallOf_le_exp_mul_of_rmNormSq_le

theorem FlowMetricBall.isKappaNoncollapsed_of_earlier_ball_of_rmNormSq_le
    {S : SolutionOn (I := I) (M := M) D} (hS : IsSolutionOn (I := I) S)
    {T t : RealTimeInterval.FlowTime D} (B₀ : FlowMetricBall S T) (B : FlowMetricBall S t)
    (hcenter : B.center = B₀.center) {θ L κ : ℝ} (hTt : (T : ℝ) ≤ t)
    (hθ : (t : ℝ) - T ≤ θ * B₀.radius ^ 2)
    (hL : Real.exp ((Module.finrank ℝ E : ℝ) ^ 2 * θ) ≤ L)
    (hradius : B.radius = L * B₀.radius)
    (hslab : _root_.Set.Icc (T : ℝ) t ⊆ D.carrier) (hreg : _root_.Set.Ioo (T : ℝ) t ⊆ D.regular)
    (hcurv : ∀ u ∈ _root_.Set.Icc (T : ℝ) t, ∀ y ∈ B₀.set,
      B₀.radius ^ 4 * FlowMetricBall.rmNormSq S u y ≤ 1)
    (hB₀ : B₀.IsKappaNoncollapsed κ) :
    B.IsKappaNoncollapsed
      (κ / (L ^ Module.finrank ℝ E * Real.exp ((Module.finrank ℝ E : ℝ) ^ 3 * θ))) := by
  set n : ℕ := Module.finrank ℝ E with hn
  set ρ : ℝ := B₀.radius with hρdef
  have hρ : 0 < ρ := B₀.radius_pos
  have hLpos : 0 < L := (Real.exp_pos _).trans_le hL
  set A : ℝ := (n : ℝ) ^ 2 / ρ ^ 2 * ((t : ℝ) - T) with hA
  have hAθ : A ≤ (n : ℝ) ^ 2 * θ := by
    have hq : ((t : ℝ) - T) / ρ ^ 2 ≤ θ := (div_le_iff₀ (by positivity)).mpr hθ
    calc
      A = (n : ℝ) ^ 2 * (((t : ℝ) - T) / ρ ^ 2) := by rw [hA]; ring
      _ ≤ (n : ℝ) ^ 2 * θ := mul_le_mul_of_nonneg_left hq (by positivity)
  have hvol := volume_riemannianBallOf_le_exp_mul_of_rmNormSq_le hS hρ hTt hslab hreg
    B₀.center hcurv
  have hsub :
      riemannianBallOf (S.base.metric (t : ℝ)) B₀.center (Real.exp A * ρ) ⊆ B.set := by
    intro y hy
    change riemannianEDistOf (S.base.metric (t : ℝ)) B.center y < ENNReal.ofReal B.radius
    rw [hcenter, hradius]
    refine hy.trans_le (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right ((Real.exp_le_exp.mpr hAθ).trans hL) hρ.le
  have hexp : Real.exp ((n : ℝ) * A) ≤ Real.exp ((n : ℝ) ^ 3 * θ) := by
    apply Real.exp_le_exp.mpr
    calc
      (n : ℝ) * A ≤ (n : ℝ) * ((n : ℝ) ^ 2 * θ) :=
        mul_le_mul_of_nonneg_left hAθ (Nat.cast_nonneg n)
      _ = (n : ℝ) ^ 3 * θ := by ring
  set e : ℝ := Real.exp ((n : ℝ) ^ 3 * θ) with he
  have hepos : 0 < e := Real.exp_pos _
  have hbound : ENNReal.ofReal κ * ENNReal.ofReal ρ ^ n ≤ ENNReal.ofReal e * B.volume := by
    calc
      ENNReal.ofReal κ * ENNReal.ofReal ρ ^ n ≤ B₀.volume := hB₀.2
      _ = riemannianVolumeMeasure (I := I) (M := M) (S.base.metric (T : ℝ))
          (riemannianBallOf (S.base.metric (T : ℝ)) B₀.center ρ) := rfl
      _ ≤ _ := hvol
      _ ≤ ENNReal.ofReal e * B.volume :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal hexp) (_root_.MeasureTheory.measure_mono hsub)
  refine ⟨div_pos hB₀.1 (mul_pos (pow_pos hLpos n) hepos), ?_⟩
  have hkey : ENNReal.ofReal e *
      (ENNReal.ofReal (κ / (L ^ n * e)) * ENNReal.ofReal B.radius ^ n) =
        ENNReal.ofReal κ * ENNReal.ofReal ρ ^ n := by
    rw [← ENNReal.ofReal_pow (B.radius_pos.le), ← ENNReal.ofReal_pow hρ.le,
      ← ENNReal.ofReal_mul (div_nonneg hB₀.1.le (mul_pos (pow_pos hLpos n) hepos).le),
      ← ENNReal.ofReal_mul hepos.le, ← ENNReal.ofReal_mul hB₀.1.le, hradius]
    congr 1
    field_simp
    ring
  rw [← hkey] at hbound
  exact (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.mpr hepos).ne' ENNReal.ofReal_ne_top).mp
    hbound

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.isKappaNoncollapsed_of_earlier_ball_of_rmNormSq_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.isKappaNoncollapsed_of_earlier_ball_of_rmNormSq_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.isKappaNoncollapsed_of_earlier_ball_of_rmNormSq_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.isKappaNoncollapsed_of_earlier_ball_of_rmNormSq_le

end DifferentialGeometry.PDE.RicciFlow.Perelman
