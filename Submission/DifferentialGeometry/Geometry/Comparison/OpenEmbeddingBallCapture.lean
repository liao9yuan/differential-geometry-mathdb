import Submission.DifferentialGeometry.Geometry.Comparison.BallCapture
import Submission.DifferentialGeometry.Geometry.Metric.Comparison.PartialDiffeomorphDistance
import Submission.DifferentialGeometry.Topology.Manifold.LocalDiffeomorphRange
import Submission.DifferentialGeometry.Topology.Manifold.OpenSubtypeDiffeomorph

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Manifold _root_.Submission.Manifold _root_.Function
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal

namespace DifferentialGeometry.Geometry.Metric

variable {E F H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N]

omit [FiniteDimensional ℝ F] [T2Space M] [T2Space N]
  [IsManifold I ∞ M] [IsManifold J ∞ N] in
private theorem exists_partialDiffeomorph_of_injective_localDiffeomorph_on_opens
    (U : TopologicalSpace.Opens N) (f : U → M)
    (hf : IsLocalDiffeomorph J I ∞ f) (hinj : _root_.Function.Injective f) (p : U) :
    ∃ Φ : PartialDiffeomorph J I N M ∞, Φ.source = (U : Set N) ∧
      (∀ x : U, Φ x.val = f x) ∧
      ∀ x : U, mfderiv J I f x = mfderiv J I (Φ : N → M) x.val := by
  let V := hf.image
  let e : Diffeomorph J I U V ∞ := Topology.diffeomorphRangeOfInjective hf hinj
  let iU := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph J U ⟨p⟩
  let iV := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph I V ⟨e p⟩
  let Φ := (iU.symm.trans e.toPartialDiffeomorph).trans iV
  have hsrc : Φ.source = (U : Set N) := by
    ext x
    change ((x ∈ iU.target ∧ iU.symm x ∈ (_root_.Set.univ : Set U)) ∧
      e (iU.symm x) ∈ (_root_.Set.univ : Set V)) ↔ x ∈ U
    simp only [_root_.Set.mem_univ, and_true, iU,
      DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_target]
    rfl
  have hmap (x : U) : Φ x.val = f x := by
    change (e (iU.symm x.val) : M) = f x
    rw [show iU.symm x.val = x from
      DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_symm_apply J U ⟨p⟩ x.property]
    rfl
  have hder (x : U) : mfderiv J I f x = mfderiv J I (Φ : N → M) x.val := by
    have hfun : (fun x : U => Φ x.val) = f := funext hmap
    rw [← hfun]
    exact mfderiv_restrict_open (Φ : N → M) U x
  exact ⟨Φ, hsrc, hmap, hder⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Metric.exists_partialDiffeomorph_of_injective_localDiffeomorph_on_opens
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Metric.exists_partialDiffeomorph_of_injective_localDiffeomorph_on_opens target :: scope.openDecls } }

theorem ball_subset_image_of_metric_lower_on_opens
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (U : TopologicalSpace.Opens N) (f : U → M)
    (hf : IsLocalDiffeomorph J I ∞ f) (hinj : _root_.Function.Injective f)
    (p : U) {R L : ℝ} (hR : 0 < R) (hL : 0 < L)
    (hcompact : IsCompact (riemannianClosedBallOf h p.val R))
    (hsource : riemannianClosedBallOf h p.val R ⊆ U)
    (hlower : ∀ x : U, x.val ∈ riemannianClosedBallOf h p.val R →
      ∀ v : TangentSpace J x, h.inner x.val v v ≤ L ^ 2 *
        g.inner (f x) (mfderiv J I f x v) (mfderiv J I f x v)) :
    riemannianBallOf g (f p) (R / L) ⊆
      f '' {x : U | x.val ∈ riemannianClosedBallOf h p.val R} := by
  obtain ⟨Φ, hsrc, hmap, hder⟩ :=
    exists_partialDiffeomorph_of_injective_localDiffeomorph_on_opens U f hf hinj p
  have hlow : ∀ x ∈ riemannianClosedBallOf h p.val R, ∀ v : TangentSpace J x,
      h.inner x v v ≤ L ^ 2 * g.inner (Φ x)
        (mfderiv J I (Φ : N → M) x v) (mfderiv J I (Φ : N → M) x v) := by
    intro x hx v
    let q : U := ⟨x, hsource hx⟩
    have hb := hlower q hx v
    rw [hder, ← hmap q] at hb
    exact hb
  have hcap := PartialDiffeomorph.ball_subset_image_closedBall_of_metric_lower
    h g Φ p.val hR hL hcompact (hsource.trans (by rw [hsrc])) hlow
  rw [hmap p] at hcap
  intro x hx
  obtain ⟨q, hq, hΦq⟩ := hcap hx
  exact ⟨⟨q, hsource hq⟩, hq, (hmap ⟨q, hsource hq⟩).symm.trans hΦq⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.ball_subset_image_of_metric_lower_on_opens then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.ball_subset_image_of_metric_lower_on_opens"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.ball_subset_image_of_metric_lower_on_opens ``Submission.DifferentialGeometry.Geometry.Metric.ball_subset_image_of_metric_lower_on_opens

omit [FiniteDimensional ℝ F] [T2Space M] [T2Space N] in
theorem edistOf_map_le_of_metric_upper_on_opens
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (U : TopologicalSpace.Opens N) (f : U → M)
    (hf : IsLocalDiffeomorph J I ∞ f) (hinj : _root_.Function.Injective f)
    (p y : U) {R L : ℝ} (hR : 0 < R) (hL : 0 < L)
    (hsource : riemannianClosedBallOf h p.val R ⊆ U)
    (hupper : ∀ x : U, x.val ∈ riemannianClosedBallOf h p.val R →
      ∀ v : TangentSpace J x,
        g.inner (f x) (mfderiv J I f x v) (mfderiv J I f x v) ≤
          L ^ 2 * h.inner x.val v v)
    (hy : riemannianEDistOf h p.val y.val < ENNReal.ofReal R) :
    riemannianEDistOf g (f p) (f y) ≤ ENNReal.ofReal L * riemannianEDistOf h p.val y.val := by
  obtain ⟨Φ, hsrc, hmap, hder⟩ :=
    exists_partialDiffeomorph_of_injective_localDiffeomorph_on_opens U f hf hinj p
  have hup : ∀ x ∈ riemannianClosedBallOf h p.val R, ∀ v : TangentSpace J x,
      g.inner (Φ x) (mfderiv J I (Φ : N → M) x v) (mfderiv J I (Φ : N → M) x v) ≤
        L ^ 2 * h.inner x v v := by
    intro x hx v
    let q : U := ⟨x, hsource hx⟩
    have hb := hupper q hx v
    rw [hder, ← hmap q] at hb
    exact hb
  have hd := PDE.RicciFlow.Perelman.KappaSolutions.edistOf_map_le_of_metric_upper_on_ball
    h g Φ p.val y.val hR hL (hsource.trans (by rw [hsrc])) hup hy
  rwa [hmap p, hmap y] at hd

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.edistOf_map_le_of_metric_upper_on_opens then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.edistOf_map_le_of_metric_upper_on_opens"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.edistOf_map_le_of_metric_upper_on_opens ``Submission.DifferentialGeometry.Geometry.Metric.edistOf_map_le_of_metric_upper_on_opens

omit [FiniteDimensional ℝ F] [T2Space M] [T2Space N] in
theorem image_closedBall_subset_ball_of_metric_upper_on_opens
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (U : TopologicalSpace.Opens N) (f : U → M)
    (hf : IsLocalDiffeomorph J I ∞ f) (hinj : _root_.Function.Injective f)
    (p : U) {r R L c : ℝ} (hr : 0 < r) (hrR : r < R)
    (hL : 0 < L) (hLc : L < c)
    (hsource : riemannianClosedBallOf h p.val R ⊆ U)
    (hupper : ∀ x : U, x.val ∈ riemannianClosedBallOf h p.val R →
      ∀ v : TangentSpace J x,
        g.inner (f x) (mfderiv J I f x v) (mfderiv J I f x v) ≤
          L ^ 2 * h.inner x.val v v) :
    f '' {x : U | x.val ∈ riemannianClosedBallOf h p.val r} ⊆
      riemannianBallOf g (f p) (c * r) := by
  rintro _ ⟨x, hx, rfl⟩
  have hxR : riemannianEDistOf h p.val x.val < ENNReal.ofReal R :=
    hx.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (hr.trans hrR)).mpr hrR)
  have hd := edistOf_map_le_of_metric_upper_on_opens g h U f hf hinj p x
    (hr.trans hrR) hL hsource hupper hxR
  change riemannianEDistOf g (f p) (f x) < ENNReal.ofReal (c * r)
  calc
    _ ≤ ENNReal.ofReal L * ENNReal.ofReal r := hd.trans (mul_le_mul' le_rfl hx)
    _ = ENNReal.ofReal (L * r) := (ENNReal.ofReal_mul hL.le).symm
    _ < _ := (ENNReal.ofReal_lt_ofReal_iff (mul_pos (hL.trans hLc) hr)).mpr
      (mul_lt_mul_of_pos_right hLc hr)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.image_closedBall_subset_ball_of_metric_upper_on_opens then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.image_closedBall_subset_ball_of_metric_upper_on_opens"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.image_closedBall_subset_ball_of_metric_upper_on_opens ``Submission.DifferentialGeometry.Geometry.Metric.image_closedBall_subset_ball_of_metric_upper_on_opens

end DifferentialGeometry.Geometry.Metric
