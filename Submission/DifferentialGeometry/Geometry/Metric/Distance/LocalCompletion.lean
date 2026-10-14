import Submission.DifferentialGeometry.Geometry.Comparison.DistanceHessianLocal
import Submission.DifferentialGeometry.Geometry.Metric.Distance.Ball

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Manifold _root_.Submission.Manifold _root_.Set
open scoped _root_.Topology _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M]

theorem exists_riemannianMetricComplete_eqOn_ball
    (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ x y : M, _root_.EDist.edist x y = riemannianEDistOf g x y) (p : M) :
    ∃ (g' : SmoothRiemannianMetric I M) (r : ℝ) (U : Set M),
      0 < r ∧ RiemannianMetricComplete g' ∧ IsOpen U ∧
      Metric.closedBall p (4 * r) ⊆ U ∧
      (∀ z ∈ U, g'.inner z = g.inner z) ∧
      (∀ z (v : TangentSpace I z), g.inner z v v ≤ g'.inner z v v) ∧
      ∀ x ∈ Metric.ball p r, ∀ y ∈ Metric.ball p r,
        riemannianEDistOf g' x y = ENNReal.ofReal (_root_.Dist.dist x y) := by
  obtain ⟨g', U, hcomplete, hU, hpU, heq, hle⟩ :=
    exists_riemannianMetricComplete_eqOn_of_isCompact g (isCompact_singleton (x := p))
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds (hpU (_root_.Set.mem_singleton p)))
  let r := R / 8
  have hr : 0 < r := by positivity
  have hKU : Metric.closedBall p (4 * r) ⊆ U := by
    intro z hz
    apply hball
    change _root_.Dist.dist z p < R
    have hd : _root_.Dist.dist z p ≤ 4 * r := hz
    dsimp only [r] at hd
    linarith only [hd, hR]
  have hdist (x y : M) : riemannianEDistOf g x y = ENNReal.ofReal (_root_.Dist.dist x y) :=
    (hmetric x y).symm.trans (edist_dist x y)
  refine ⟨g', r, U, hr, hcomplete, hU, hKU, heq, hle, ?_⟩
  intro x hx y hy
  have hxp : _root_.Dist.dist x p < r := hx
  have hyp : _root_.Dist.dist y p < r := hy
  have hxy : _root_.Dist.dist x y < 2 * r := by
    have htri := dist_triangle x p y
    rw [dist_comm p y] at htri
    linarith only [htri, hxp, hyp]
  have hbuffer : {z : M | riemannianEDistOf g x z ≤ ENNReal.ofReal (2 * r)} ⊆ U := by
    intro z hz
    apply hKU
    change _root_.Dist.dist z p ≤ 4 * r
    change riemannianEDistOf g x z ≤ ENNReal.ofReal (2 * r) at hz
    rw [hdist] at hz
    have hxz : _root_.Dist.dist x z ≤ 2 * r :=
      (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hz
    have htri := dist_triangle z x p
    rw [dist_comm z x] at htri
    linarith only [htri, hxz, hxp, hr]
  have hyshort : riemannianEDistOf g x y < ENNReal.ofReal (2 * r) := by
    rw [hdist]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hxy
  exact (riemannianEDistOf_eq_of_eqOn_ball g g' hbuffer heq hle hyshort).trans (hdist x y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_riemannianMetricComplete_eqOn_ball then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_riemannianMetricComplete_eqOn_ball"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_riemannianMetricComplete_eqOn_ball ``Submission.DifferentialGeometry.Geometry.exists_riemannianMetricComplete_eqOn_ball

end DifferentialGeometry.Geometry

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Geometry.instIsManifoldRealOfNatWithTopENat_differentialGeometry : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.instIsManifoldRealOfNatWithTopENat_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.instIsManifoldRealOfNatWithTopENat_differentialGeometry target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M] in
private theorem riemannianEDistOf_eq_on_inner_ball
    (g g' : SmoothRiemannianMetric I M) {p : M} {R r : ℝ} {U : Set M}
    (hr : 0 < r) (hR : 3 * r ≤ R)
    (hKU : riemannianClosedBallOf g p R ⊆ U)
    (heq : ∀ z ∈ U, g'.inner z = g.inner z)
    (hle : ∀ z (v : TangentSpace I z), g.inner z v v ≤ g'.inner z v v)
    {x y : M} (hx : x ∈ riemannianBallOf g p r) (hy : y ∈ riemannianBallOf g p r) :
    riemannianEDistOf g' x y = riemannianEDistOf g x y := by
  have hxp : riemannianEDistOf g p x < ENNReal.ofReal r := hx
  have hyp : riemannianEDistOf g p y < ENNReal.ofReal r := hy
  have hxy : riemannianEDistOf g x y < ENNReal.ofReal (2 * r) := by
    calc
      _ ≤ riemannianEDistOf g x p + riemannianEDistOf g p y :=
        riemannianEDistOf_triangle _ _ _ _
      _ < ENNReal.ofReal r + ENNReal.ofReal r :=
        ENNReal.add_lt_add (by rwa [riemannianEDistOf_comm]) hyp
      _ = ENNReal.ofReal (2 * r) := by rw [← ENNReal.ofReal_add hr.le hr.le]; congr 1; ring
  have hbuffer : {z : M | riemannianEDistOf g x z ≤ ENNReal.ofReal (2 * r)} ⊆ U := by
    intro z hz
    apply hKU
    change riemannianEDistOf g p z ≤ ENNReal.ofReal R
    calc
      _ ≤ riemannianEDistOf g p x + riemannianEDistOf g x z :=
        riemannianEDistOf_triangle _ _ _ _
      _ ≤ ENNReal.ofReal r + ENNReal.ofReal (2 * r) := add_le_add hxp.le hz
      _ = ENNReal.ofReal (3 * r) := by rw [← ENNReal.ofReal_add hr.le (by positivity : (0 : ℝ) ≤ 2 * r)]; congr 1; ring
      _ ≤ ENNReal.ofReal R := ENNReal.ofReal_le_ofReal hR
  exact riemannianEDistOf_eq_of_eqOn_ball g g' hbuffer heq hle hxy

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.riemannianEDistOf_eq_on_inner_ball
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.riemannianEDistOf_eq_on_inner_ball target :: scope.openDecls } }

theorem exists_complete_metric_extension_of_riemannianClosedBall
    (g : SmoothRiemannianMetric I M) (p : M) {R : ℝ}
    (hK : IsCompact (riemannianClosedBallOf g p R)) :
    ∃ (g' : SmoothRiemannianMetric I M) (U : Set M),
      RiemannianMetricComplete g' ∧ IsOpen U ∧
      riemannianClosedBallOf g p R ⊆ U ∧
      (∀ z ∈ U, g'.inner z = g.inner z) ∧
      (∀ z (v : TangentSpace I z), g.inner z v v ≤ g'.inner z v v) ∧
      (∀ y ∈ riemannianBallOf g p R, riemannianEDistOf g' p y = riemannianEDistOf g p y) ∧
      (∀ r : ℝ, r ≤ R → riemannianBallOf g' p r = riemannianBallOf g p r) ∧
      (∀ r : ℝ, 0 ≤ r → r < R →
        riemannianClosedBallOf g' p r = riemannianClosedBallOf g p r) ∧
      ∀ r : ℝ, 0 < r → 3 * r ≤ R →
        ∀ x ∈ riemannianBallOf g p r, ∀ y ∈ riemannianBallOf g p r,
          riemannianEDistOf g' x y = riemannianEDistOf g x y := by
  obtain ⟨g', U, hcomplete, hU, hKU, heq, hle⟩ :=
    exists_riemannianMetricComplete_eqOn_of_isCompact g hK
  have hd : ∀ y ∈ riemannianBallOf g p R,
      riemannianEDistOf g' p y = riemannianEDistOf g p y :=
    fun y hy => riemannianEDistOf_eq_of_eqOn_ball g g' hKU heq hle hy
  have hmono (y : M) : riemannianEDistOf g p y ≤ riemannianEDistOf g' p y :=
    edistOf_mono g g' hle p y
  refine ⟨g', U, hcomplete, hU, hKU, heq, hle, hd, ?_, ?_, ?_⟩
  · intro r hr
    ext y
    constructor
    · intro hy
      exact (hmono y).trans_lt hy
    · intro hy
      have hyR : y ∈ riemannianBallOf g p R :=
        lt_of_lt_of_le hy (ENNReal.ofReal_le_ofReal hr)
      change riemannianEDistOf g' p y < ENNReal.ofReal r
      rw [hd y hyR]
      exact hy
  · intro r hr hrR
    ext y
    constructor
    · intro hy
      exact (hmono y).trans hy
    · intro hy
      have hyR : y ∈ riemannianBallOf g p R :=
        lt_of_le_of_lt hy ((ENNReal.ofReal_lt_ofReal_iff (hr.trans_lt hrR)).mpr hrR)
      change riemannianEDistOf g' p y ≤ ENNReal.ofReal r
      rw [hd y hyR]
      exact hy
  · intro r hr hR x hx y hy
    exact riemannianEDistOf_eq_on_inner_ball g g' hr hR hKU heq hle hx hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_complete_metric_extension_of_riemannianClosedBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_complete_metric_extension_of_riemannianClosedBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_complete_metric_extension_of_riemannianClosedBall ``Submission.DifferentialGeometry.Geometry.exists_complete_metric_extension_of_riemannianClosedBall

end DifferentialGeometry.Geometry
