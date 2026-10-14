import Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.RadialConeApproximation
import Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.Completion

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Filter _root_.Set
open scoped _root_.Topology _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.Toponogov
open _root_.Submission.DifferentialGeometry.Geometry

universe u

structure PuncturedConeApproximation {M : Type u} [MetricSpace M]
    (q : UniformSpace.Completion M) (r : ℝ) where
  radius_pos : 0 < r
  ray : {x : M // _root_.Dist.dist (x : UniformSpace.Completion M) q ∈ _root_.Set.Ioo 0 (r / 3)} → C(ℝ, UniformSpace.Completion M)
  ray_start : ∀ i, ray i 0 = q
  ray_end : ∀ i, ray i (_root_.Dist.dist (i.val : UniformSpace.Completion M) q) = (i.val : UniformSpace.Completion M)
  ray_minimizing : ∀ i, ∀ s ∈ _root_.Set.Icc 0 (_root_.Dist.dist (i.val : UniformSpace.Completion M) q),
    ∀ t ∈ _root_.Set.Icc 0 (_root_.Dist.dist (i.val : UniformSpace.Completion M) q), _root_.Dist.dist (ray i s) (ray i t) = |s - t|
  angles : AngleKernel {x : M // _root_.Dist.dist (x : UniformSpace.Completion M) q ∈ _root_.Set.Ioo 0 (r / 3)}
  angle_eq : ∀ i j, angles.angle i j = limitingRadialAngle
    (fun x => _root_.Dist.dist (x.val : UniformSpace.Completion M) q) (fun i => ray i) i j
  directions_totallyBounded : let _ := angles.metricSpace
    TotallyBounded (_root_.Set.univ : Set (Quotient angles.setoid))
  approximation : let _ := angles.metricSpace
    ∀ a b eps : ℝ, 0 < a → a ≤ b → 0 < eps →
      ∀ F : Finset ({x : M // _root_.Dist.dist (x : UniformSpace.Completion M) q ∈ _root_.Set.Ioo 0 (r / 3)} × ℝ),
      (∀ p ∈ F, p.2 ∈ _root_.Set.Icc a b) →
      ∃ S : Finset ({x : M // _root_.Dist.dist (x : UniformSpace.Completion M) q ∈ _root_.Set.Ioo 0 (r / 3)} × ℝ),
        F ⊆ S ∧ (∀ p ∈ S, p.2 ∈ _root_.Set.Icc a b) ∧
        (∀ t ∈ _root_.Set.Icc a b, ∀ z : UniformSpace.Completion (Quotient angles.setoid),
          ∃ p ∈ S, Metric.coneDistance (t, z)
            (p.2, (angles.classOf p.1 : UniformSpace.Completion (Quotient angles.setoid))) < eps) ∧
        ∀ᶠ rho in 𝓝[>] (0 : ℝ),
          (∀ p ∈ S, rho * p.2 ∈ _root_.Set.Ioc 0 (_root_.Dist.dist (p.1.val : UniformSpace.Completion M) q)) ∧
          (∀ p ∈ S, ray p.1 (rho * p.2) ∈ _root_.Set.range (fun x : M => (x : UniformSpace.Completion M)) ∧
            _root_.Dist.dist q (ray p.1 (rho * p.2)) / rho = p.2) ∧
          (∀ x : M, _root_.Dist.dist (x : UniformSpace.Completion M) q / rho ∈ _root_.Set.Icc a b →
            ∃ p ∈ S, _root_.Dist.dist (x : UniformSpace.Completion M) (ray p.1 (rho * p.2)) / rho < eps) ∧
          ∀ p ∈ S, ∀ z ∈ S,
            |Metric.coneDistance (p.2, (angles.classOf p.1 : UniformSpace.Completion (Quotient angles.setoid)))
              (z.2, (angles.classOf z.1 : UniformSpace.Completion (Quotient angles.setoid))) -
              _root_.Dist.dist (ray p.1 (rho * p.2)) (ray z.1 (rho * z.2)) / rho| < eps

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.PuncturedConeApproximation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.PuncturedConeApproximation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.PuncturedConeApproximation ``Submission.DifferentialGeometry.Toponogov.PuncturedConeApproximation

theorem PuncturedConeApproximation.compact_directions {M : Type u} [MetricSpace M]
    {q : UniformSpace.Completion M} {r : ℝ} (C : PuncturedConeApproximation q r) :
    let _ := C.angles.metricSpace
    CompactSpace (UniformSpace.Completion (Quotient C.angles.setoid)) := by
  let _ := C.angles.metricSpace
  exact Metric.compactSpace_completion_of_totallyBounded C.directions_totallyBounded

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Toponogov.PuncturedConeApproximation
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.PuncturedConeApproximation.compact_directions then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.PuncturedConeApproximation.compact_directions"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.PuncturedConeApproximation.compact_directions ``Submission.DifferentialGeometry.Toponogov.PuncturedConeApproximation.compact_directions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type u} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]

private theorem exists_punctured_annulus_cone_approximation_data
    (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ x y : M, _root_.EDist.edist x y = riemannianEDistOf g x y)
    (hsec : HasNonnegativeSectionalCurvature g)
    {q : UniformSpace.Completion M}
    (hq : q ∉ _root_.Set.range (fun x : M => (x : UniformSpace.Completion M)))
    {r : ℝ} (hr : 0 < r) (hcompact : IsCompact (Metric.closedBall q r))
    (hcover : Metric.closedBall q r ⊆ _root_.Insert.insert q (_root_.Set.range (fun x : M => (x : UniformSpace.Completion M))))
    (havoid : ∀ (beta : ℝ → UniformSpace.Completion M) (u v w : ℝ), u < v → v < w →
      (∀ s ∈ _root_.Set.Icc u w, ∀ t ∈ _root_.Set.Icc u w, _root_.Dist.dist (beta s) (beta t) = |s - t|) → beta v ≠ q)
    (hdir : ∀ {ι : Type u} (L : ι → ℝ) (gamma : ι → C(ℝ, UniformSpace.Completion M)),
      (∀ i, 0 < L i) → (∀ i, L i < r / 3) → (∀ i, gamma i 0 = q) →
      (∀ i, ∀ s ∈ _root_.Set.Icc 0 (L i), ∀ t ∈ _root_.Set.Icc 0 (L i), _root_.Dist.dist (gamma i s) (gamma i t) = |s - t|) →
      ∃ K : AngleKernel ι, (∀ i j, K.angle i j = limitingRadialAngle L (fun i => gamma i) i j) ∧
        let _ := K.metricSpace
        TotallyBounded (_root_.Set.univ : Set (Quotient K.setoid))) :
    let P := {x : M // _root_.Dist.dist (x : UniformSpace.Completion M) q ∈ _root_.Set.Ioo 0 (r / 3)}
    let L (x : P) := _root_.Dist.dist (x.val : UniformSpace.Completion M) q
    ∃ gamma : P → C(ℝ, UniformSpace.Completion M),
      (∀ i, gamma i 0 = q) ∧ (∀ i, gamma i (L i) = (i.val : UniformSpace.Completion M)) ∧
      (∀ i, ∀ s ∈ _root_.Set.Icc 0 (L i), ∀ t ∈ _root_.Set.Icc 0 (L i), _root_.Dist.dist (gamma i s) (gamma i t) = |s - t|) ∧
      ∃ K : AngleKernel P,
        (∀ i j, K.angle i j = limitingRadialAngle L (fun i => gamma i) i j) ∧
        let _ := K.metricSpace
        TotallyBounded (_root_.Set.univ : Set (Quotient K.setoid)) ∧
        CompactSpace (UniformSpace.Completion (Quotient K.setoid)) ∧
        ∀ a b eps : ℝ, 0 < a → a ≤ b → 0 < eps →
          ∀ F : Finset (P × ℝ), (∀ p ∈ F, p.2 ∈ _root_.Set.Icc a b) →
          ∃ S : Finset (P × ℝ), F ⊆ S ∧ (∀ p ∈ S, p.2 ∈ _root_.Set.Icc a b) ∧
            (∀ t ∈ _root_.Set.Icc a b, ∀ z : UniformSpace.Completion (Quotient K.setoid),
              ∃ p ∈ S, Metric.coneDistance (t, z)
                (p.2, (K.classOf p.1 : UniformSpace.Completion (Quotient K.setoid))) < eps) ∧
            ∀ᶠ rho in 𝓝[>] (0 : ℝ),
              (∀ p ∈ S, rho * p.2 ∈ _root_.Set.Ioc 0 (L p.1)) ∧
              (∀ p ∈ S, gamma p.1 (rho * p.2) ∈ _root_.Set.range (fun x : M => (x : UniformSpace.Completion M)) ∧
                _root_.Dist.dist q (gamma p.1 (rho * p.2)) / rho = p.2) ∧
              (∀ x : M, _root_.Dist.dist (x : UniformSpace.Completion M) q / rho ∈ _root_.Set.Icc a b →
                ∃ p ∈ S, _root_.Dist.dist (x : UniformSpace.Completion M) (gamma p.1 (rho * p.2)) / rho < eps) ∧
              ∀ p ∈ S, ∀ z ∈ S,
                |Metric.coneDistance (p.2, (K.classOf p.1 : UniformSpace.Completion (Quotient K.setoid)))
                  (z.2, (K.classOf z.1 : UniformSpace.Completion (Quotient K.setoid))) -
                  dist (gamma p.1 (rho * p.2)) (gamma z.1 (rho * z.2)) / rho| < eps := by
  classical
  let P := {x : M // _root_.Dist.dist (x : UniformSpace.Completion M) q ∈ _root_.Set.Ioo 0 (r / 3)}
  let L (x : P) := _root_.Dist.dist (x.val : UniformSpace.Completion M) q
  change ∃ gamma : P → C(ℝ, UniformSpace.Completion M), _
  have hseg (x : P) := exists_radial_segment_of_punctured_compact_ball g hmetric hcompact hcover
    x.val (x.property.2.trans (by linarith))
  choose gamma hzero hend hmin using hseg
  have hL (x : P) : 0 < L x := x.property.1
  have hLr (x : P) : L x < r / 3 := x.property.2
  have hrad : IsRadialFamily q L (fun i => gamma i) := by
    intro i s hs
    simpa only [hzero, sub_zero, abs_of_pos hs.1, dist_comm q] using
      hmin i s ⟨hs.1.le, hs.2⟩ 0 ⟨le_rfl, (hL i).le⟩
  obtain ⟨K, hK, htb⟩ := hdir L gamma hL hLr hzero hmin
  let _ := K.metricSpace
  have hmono (i j : P) := radialComparisonAngle_nonincreasing_of_completion_segments
    g hmetric hsec hq hcompact hcover havoid hL hLr hzero hmin i j
  refine ⟨gamma, hzero, hend, hmin, K, hK, htb,
    Metric.compactSpace_completion_of_totallyBounded htb, ?_⟩
  intro a b eps ha hab heps F hF
  have hb : 0 < b := ha.trans_le hab
  obtain ⟨S, hFS, hS, hcone, happrox⟩ := exists_finset_radial_cone_approximation hrad hL
    (fun i s hs t ht => hmin i s ⟨hs.1.le, hs.2⟩ t ⟨ht.1.le, ht.2⟩)
    hmono K hK htb ha hab heps F hF
  refine ⟨S, hFS, hS, hcone, ?_⟩
  filter_upwards [happrox, Ioc_mem_nhdsGT (show 0 < r / (6 * b) by positivity)] with rho happ hrho
  obtain ⟨hdom, hsource, hradial, hpair⟩ := happ
  refine ⟨hdom, ?_, ?_, hpair⟩
  · intro p hp
    refine ⟨?_, hradial p hp⟩
    have hs := hdom p hp
    have hdist : _root_.Dist.dist (gamma p.1 (rho * p.2)) q = rho * p.2 := by
      rw [dist_comm]
      exact hrad p.1 _ hs
    have hball : gamma p.1 (rho * p.2) ∈ Metric.closedBall q r := by
      rw [Metric.mem_closedBall, hdist]
      exact hs.2.trans ((hLr p.1).le.trans (by linarith))
    rcases mem_insert_iff.mp (hcover hball) with hz | hz
    · rw [hz, dist_self] at hdist
      exact False.elim (hs.1.ne hdist)
    · exact hz
  · intro x hx
    have hxpos : 0 < _root_.Dist.dist (x : UniformSpace.Completion M) q :=
      dist_pos.mpr (fun h => hq ⟨x, h⟩)
    have hxr : _root_.Dist.dist (x : UniformSpace.Completion M) q < r / 3 := by
      have hle := (div_le_iff₀ hrho.1).mp hx.2
      have hscale := mul_le_mul_of_nonneg_right hrho.2 hb.le
      have heq : r / (6 * b) * b = r / 6 := by field_simp
      rw [heq] at hscale
      linarith only [hle, hscale, hr]
    let i : P := ⟨x, hxpos, hxr⟩
    have hparam : rho * (_root_.Dist.dist (x : UniformSpace.Completion M) q / rho) = L i := by
      dsimp only [L, i]
      field_simp [hrho.1.ne']
    obtain ⟨p, hp, hnear⟩ := hsource i (_root_.Dist.dist (x : UniformSpace.Completion M) q / rho) hx hparam.le
    refine ⟨p, hp, ?_⟩
    rw [hparam, hend] at hnear
    exact hnear

run_cmd do
  let target := ``Submission.DifferentialGeometry.Toponogov.exists_punctured_annulus_cone_approximation_data
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Toponogov.exists_punctured_annulus_cone_approximation_data target :: scope.openDecls } }

theorem exists_punctured_annulus_cone_approximation
    (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ x y : M, _root_.EDist.edist x y = riemannianEDistOf g x y)
    (hsec : HasNonnegativeSectionalCurvature g)
    {q : UniformSpace.Completion M}
    (hq : q ∉ _root_.Set.range (fun x : M => (x : UniformSpace.Completion M)))
    {r : ℝ} (hr : 0 < r) (hcompact : IsCompact (Metric.closedBall q r))
    (hcover : Metric.closedBall q r ⊆ _root_.Insert.insert q (_root_.Set.range (fun x : M => (x : UniformSpace.Completion M))))
    (havoid : ∀ (beta : ℝ → UniformSpace.Completion M) (u v w : ℝ), u < v → v < w →
      (∀ s ∈ _root_.Set.Icc u w, ∀ t ∈ _root_.Set.Icc u w, _root_.Dist.dist (beta s) (beta t) = |s - t|) → beta v ≠ q)
    (hdir : ∀ {ι : Type u} (L : ι → ℝ) (gamma : ι → C(ℝ, UniformSpace.Completion M)),
      (∀ i, 0 < L i) → (∀ i, L i < r / 3) → (∀ i, gamma i 0 = q) →
      (∀ i, ∀ s ∈ _root_.Set.Icc 0 (L i), ∀ t ∈ _root_.Set.Icc 0 (L i), _root_.Dist.dist (gamma i s) (gamma i t) = |s - t|) →
      ∃ K : AngleKernel ι, (∀ i j, K.angle i j = limitingRadialAngle L (fun i => gamma i) i j) ∧
        let _ := K.metricSpace
        TotallyBounded (_root_.Set.univ : Set (Quotient K.setoid))) :
    Nonempty (PuncturedConeApproximation q r) := by
  obtain ⟨gamma, hzero, hend, hmin, K, hK, htb, _, happrox⟩ :=
    exists_punctured_annulus_cone_approximation_data g hmetric hsec hq hr hcompact hcover havoid hdir
  exact ⟨{ radius_pos := hr
           ray := gamma
           ray_start := hzero
           ray_end := hend
           ray_minimizing := hmin
           angles := K
           angle_eq := hK
           directions_totallyBounded := htb
           approximation := happrox }⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.exists_punctured_annulus_cone_approximation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.exists_punctured_annulus_cone_approximation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.exists_punctured_annulus_cone_approximation ``Submission.DifferentialGeometry.Toponogov.exists_punctured_annulus_cone_approximation

end DifferentialGeometry.Toponogov
