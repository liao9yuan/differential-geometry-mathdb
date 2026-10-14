import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.BallImage
import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.QuadraticBounds
import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.MetricExtension

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Filter _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.ENNReal

namespace DifferentialGeometry.CheegerGromovCompactness

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

private def changeSourceMetric
    (X : PointedRiemannianSeq.{u, uE, uH} I)
    (g : ∀ n, SmoothRiemannianMetric I (X.obj n).M) : PointedRiemannianSeq.{u, uE, uH} I :=
  { obj := fun n => { X.obj n with metric := g n } }

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.changeSourceMetric
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.changeSourceMetric target :: scope.openDecls } }

private def PointedRiemannianConvergenceMaps.changeSourceMetric
    {X : PointedRiemannianSeq.{u, uE, uH} I}
    {L : PointedRiemannianManifold.{u, uE, uH} I} {f : ℕ → ℕ}
    (F : PointedRiemannianConvergenceMaps X L f)
    (g : ∀ n, SmoothRiemannianMetric I (X.obj n).M) :
    PointedRiemannianConvergenceMaps (CheegerGromovCompactness.changeSourceMetric X g) L f where
  partialDiffeomorph := F.partialDiffeomorph
  source_exhausts := F.source_exhausts
  base_mem := F.base_mem
  basepoint_map := F.basepoint_map

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps.changeSourceMetric
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps.changeSourceMetric target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private theorem canonicalSourceData_derivNormSupOn_eq_of_source_metric_eqOn
    {X : PointedRiemannianSeq.{u, uE, uH} I}
    {L : PointedRiemannianManifold.{u, uE, uH} I} {f : ℕ → ℕ}
    (F : PointedRiemannianConvergenceMaps X L f)
    (g : ∀ n, SmoothRiemannianMetric I (X.obj n).M) (k : ℕ)
    (U : TopologicalSpace.Opens L.M) (hUsrc : (U : Set L.M) ⊆ F.source k)
    (K : Set L.M) (hKU : K ⊆ U) (p : ℕ)
    (heq : ∀ x ∈ U, (g (f k)).inner (F.map k x) = (X.obj (f k)).metric.inner (F.map k x)) :
    (CanonicalMetricCompactness.canonicalSourceData (F.changeSourceMetric g) k).derivNormSupOn K p =
      (CanonicalMetricCompactness.canonicalSourceData F k).derivNormSupOn K p := by
  let D := CanonicalMetricCompactness.canonicalSourceData F k
  let V : TopologicalSpace.Opens L.M := metricSourceOpenSubset F k
  let A := D.pullbackMetric.restrictOpenOfSubset hUsrc
  have hA : ∀ (x : U) (v w : TangentSpace I x),
      A.inner x v w = (X.obj (f k)).metric.inner (F.map k x)
        (mfderiv I I (F.map k) x v) (mfderiv I I (F.map k) x w) := by
    intro x v w
    have hpull := D.pullback_inner (⟨x, hUsrc x.property⟩ : V) v w
    have hval := (hasMFDerivAt_subtype_val (I := I) V (⟨x, hUsrc x.property⟩ : V)).mdifferentiableAt
    have hF := (F.partialDiffeomorph k).mdifferentiableAt (by simp) (hUsrc x.property)
    have hderiv (v : TangentSpace I x) :
        mfderiv I I (fun y : V => F.map k (y : L.M)) (⟨x, hUsrc x.property⟩ : V) v =
          mfderiv I I (F.map k) (x : L.M) v := by
      exact (mfderiv_comp_apply (⟨x, hUsrc x.property⟩ : V) hF hval v).trans
        (congrArg (mfderiv I I (F.map k) (x : L.M)) (mfderiv_subtype_val_apply V _ v))
    exact hpull.trans (congrArg₂ (fun a b => (X.obj (f k)).metric.inner (F.map k x) a b)
      (hderiv v) (hderiv w))
  rw [canonicalSourceData_derivNormSupOn_eq_of_open_pullback (F.changeSourceMetric g) k U hUsrc A K hKU p
    (fun x v w => by
      change A.inner x v w = (g (f k)).inner (F.map k x)
        (mfderiv I I (F.map k) x v) (mfderiv I I (F.map k) x w)
      rw [heq x x.property]
      exact hA x v w),
    canonicalSourceData_derivNormSupOn_eq_of_open_pullback F k U hUsrc A K hKU p hA]

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.canonicalSourceData_derivNormSupOn_eq_of_source_metric_eqOn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.canonicalSourceData_derivNormSupOn_eq_of_source_metric_eqOn target :: scope.openDecls } }


omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem PointedRiemannianConvergenceMaps.exists_canonical_convergence_of_inner_ball_metric_agreement
    {X : PointedRiemannianSeq.{u, uE, uH} I}
    {L : PointedRiemannianManifold.{u, uE, uH} I} {f : ℕ → ℕ}
    (F : PointedRiemannianConvergenceMaps X L f)
    (C : MetricConvergenceData F)
    (hcanonical : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData F k)
    (g : ∀ n, SmoothRiemannianMetric I (X.obj n).M)
    {rho : ℝ} (hrho : 0 < rho)
    (hradial : ∀ x : L.M, riemannianEDistOf L.metric L.basepoint x < ENNReal.ofReal rho)
    (hcompact : ∀ R : ℝ, 0 ≤ R → R < rho → IsCompact (riemannianClosedBallOf L.metric L.basepoint R))
    (hagree : ∀ R : ℝ, 0 < R → R < rho → ∀ᶠ k in _root_.Filter.atTop,
      ∀ y ∈ riemannianBallOf (X.obj (f k)).metric (X.obj (f k)).basepoint R,
        (g (f k)).inner y = (X.obj (f k)).metric.inner y) :
    ∃ F' : PointedRiemannianConvergenceMaps
      ({ obj := fun n => { X.obj n with metric := g n } } : PointedRiemannianSeq I) L f,
      (∀ k, F'.partialDiffeomorph k = F.partialDiffeomorph k) ∧
      ∃ C' : MetricConvergenceData F',
        ∀ k, C'.domain k = CanonicalMetricCompactness.canonicalSourceData F' k := by
  have hupper : ∀ K : Set L.M, IsCompact K → ∀ B : ℝ, 1 < B → ∀ᶠ i in _root_.Filter.atTop,
      ∀ x ∈ K, ∀ v : TangentSpace I x,
        (X.obj (f i)).metric.inner (F.map i x)
          (mfderiv I I (F.map i) x v) (mfderiv I I (F.map i) x v) ≤
            B ^ 2 * L.metric.inner x v v := by
    intro K hK B hB
    have hconv : metricSourceConvergesOn F (CanonicalMetricCompactness.canonicalSourceData F) K 0 := by
      have heq : C.domain = CanonicalMetricCompactness.canonicalSourceData F := funext hcanonical
      rw [← heq]
      exact C.converges K hK 0
    filter_upwards [pointed_metric_eventually_quadratic_bounds hK hconv (by nlinarith : 0 < B ^ 2 - 1)] with i hi
    intro x hx v
    simpa only [add_sub_cancel] using (hi.2 x hx v).2
  let F' := F.changeSourceMetric g
  refine ⟨F', fun _ => rfl, ?_⟩
  obtain ⟨C', hC', _⟩ := exists_metricConvergenceData_canonicalSourceData F' (by
    intro K hK p eps heps
    obtain ⟨R, hR, hRrho, himage⟩ :=
      F.exists_eventually_image_compact_subset_inner_ball hrho hradial hcompact hupper hK
    obtain ⟨N, hN⟩ := C.converges K hK p eps heps
    obtain ⟨J, hJ⟩ := eventually_atTop.mp (himage.and (hagree R hR hRrho))
    refine ⟨max N J, fun k hk => ?_⟩
    have hkN := hN k ((le_max_left N J).trans hk)
    have hkJ := hJ k ((le_max_right N J).trans hk)
    let V : Set (X.obj (f k)).M := riemannianBallOf (X.obj (f k)).metric (X.obj (f k)).basepoint R
    have hV : IsOpen V := isOpen_lt (by
      unfold riemannianEDistOf
      exact Geometry.Riemannian.continuous_riemannianEDist _ _) continuous_const
    let U : TopologicalSpace.Opens L.M := ⟨F.source k ∩ F.map k ⁻¹' V,
      (F.partialDiffeomorph k).contMDiffOn_toFun.continuousOn.isOpen_inter_preimage
        (F.partialDiffeomorph k).open_source hV⟩
    have hUsrc : (U : Set L.M) ⊆ F.source k := _root_.Set.inter_subset_left
    have hKU : K ⊆ U := fun x hx => ⟨hkJ.1.1 hx, hkJ.1.2 ⟨x, hx, rfl⟩⟩
    rw [canonicalSourceData_derivNormSupOn_eq_of_source_metric_eqOn F g k U hUsrc K hKU p
      (fun x hx => hkJ.2 _ hx.2)]
    simpa only [hcanonical k] using hkN.2)
  exact ⟨C', hC'⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps.exists_canonical_convergence_of_inner_ball_metric_agreement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps.exists_canonical_convergence_of_inner_ball_metric_agreement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps.exists_canonical_convergence_of_inner_ball_metric_agreement ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps.exists_canonical_convergence_of_inner_ball_metric_agreement


end DifferentialGeometry.CheegerGromovCompactness
