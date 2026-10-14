import Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.RadialNets
import Submission.DifferentialGeometry.Geometry.Metric.Distance.Completion

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

universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type u} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]

theorem exists_radial_sphere_nets_of_totallyBounded_limiting_directions
    (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ x y : M, _root_.EDist.edist x y = riemannianEDistOf g x y)
    {q : UniformSpace.Completion M} {r : ℝ} (hr : 0 < r)
    (hcompact : IsCompact (Metric.closedBall q r))
    (hcover : Metric.closedBall q r ⊆ _root_.Insert.insert q (_root_.Set.range (fun x : M => (x : UniformSpace.Completion M))))
    (hdir : ∀ {ι : Type u} (L : ι → ℝ) (gamma : ι → C(ℝ, UniformSpace.Completion M)),
      (∀ i, 0 < L i) → (∀ i, L i < r / 3) → (∀ i, gamma i 0 = q) →
      (∀ i, ∀ s ∈ _root_.Set.Icc 0 (L i), ∀ t ∈ _root_.Set.Icc 0 (L i), _root_.Dist.dist (gamma i s) (gamma i t) = |s - t|) →
      ∃ K : AngleKernel ι, (∀ i j, K.angle i j = limitingRadialAngle L (fun i => gamma i) i j) ∧
        let _ := K.metricSpace
        TotallyBounded (_root_.Set.univ : Set (Quotient K.setoid)))
    {eps : ℝ} (heps : 0 < eps) :
    ∃ d ∈ _root_.Set.Ioo 0 (r / 3), ∃ A : Finset C(ℝ, UniformSpace.Completion M),
      (∀ gamma ∈ A, gamma 0 = q ∧
        ∀ s ∈ _root_.Set.Icc 0 d, ∀ t ∈ _root_.Set.Icc 0 d, _root_.Dist.dist (gamma s) (gamma t) = |s - t|) ∧
      ∀ s ∈ _root_.Set.Ioc 0 d, ∀ x : M, _root_.Dist.dist (x : UniformSpace.Completion M) q = s →
        ∃ gamma ∈ A, _root_.Dist.dist (x : UniformSpace.Completion M) (gamma s) < eps * s := by
  classical
  let Seg := {p : ℝ × C(ℝ, UniformSpace.Completion M) |
    0 < p.1 ∧ p.1 < r / 3 ∧ p.2 0 = q ∧
      ∀ s ∈ _root_.Set.Icc 0 p.1, ∀ t ∈ _root_.Set.Icc 0 p.1, _root_.Dist.dist (p.2 s) (p.2 t) = |s - t|}
  let L (i : Seg) := i.val.1
  let gamma (i : Seg) := i.val.2
  have hL (i : Seg) : 0 < L i := i.property.1
  have hLr (i : Seg) : L i < r / 3 := i.property.2.1
  have hzero (i : Seg) : gamma i 0 = q := i.property.2.2.1
  have hmin (i : Seg) : ∀ s ∈ _root_.Set.Icc 0 (L i), ∀ t ∈ _root_.Set.Icc 0 (L i),
      dist (gamma i s) (gamma i t) = |s - t| := i.property.2.2.2
  have hrad : IsRadialFamily q L (fun i => gamma i) := by
    intro i s hs
    simpa only [hzero, sub_zero, abs_of_pos hs.1, dist_comm q] using
      hmin i s ⟨hs.1.le, hs.2⟩ 0 ⟨le_rfl, (hL i).le⟩
  obtain ⟨K, hK, htb⟩ := hdir L gamma hL hLr hzero hmin
  obtain ⟨B, d0, hd0, hBd, hB, _⟩ := exists_finset_radial_net hrad hL K hK htb heps
  let d := _root_.Min.min d0 (r / 6)
  have hd : 0 < d := lt_min hd0 (by positivity)
  have hdr : d < r / 3 := (min_le_right _ _).trans_lt (by linarith)
  refine ⟨d, ⟨hd, hdr⟩, B.image gamma, ?_, ?_⟩
  · intro c hc
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hc
    refine ⟨hzero i, fun s hs t ht => hmin i s ?_ t ?_⟩
    · exact ⟨hs.1, hs.2.trans ((min_le_left _ _).trans (hBd i hi))⟩
    · exact ⟨ht.1, ht.2.trans ((min_le_left _ _).trans (hBd i hi))⟩
  · intro s hs x hx
    have hxr : _root_.Dist.dist (x : UniformSpace.Completion M) q < r / 3 :=
      hx ▸ hs.2.trans_lt hdr
    obtain ⟨c, hc0, hcx, hcmin⟩ := Geometry.exists_radial_segment_of_punctured_compact_ball
      g hmetric hcompact hcover x (hxr.trans (by linarith))
    let i : Seg := ⟨(_root_.Dist.dist (x : UniformSpace.Completion M) q, c),
      ⟨by change 0 < _root_.Dist.dist (x : UniformSpace.Completion M) q; rw [hx]; exact hs.1, hxr, hc0, hcmin⟩⟩
    have hsi : s ≤ L i := by change s ≤ _root_.Dist.dist (x : UniformSpace.Completion M) q; exact hx.ge
    obtain ⟨j, hj, hdist⟩ := hB s ⟨hs.1, hs.2.trans (min_le_left _ _)⟩ i hsi
    refine ⟨gamma j, Finset.mem_image.mpr ⟨j, hj, rfl⟩, ?_⟩
    have hi : gamma i s = (x : UniformSpace.Completion M) := by
      change c s = x
      simpa only [hx] using hcx
    rwa [hi] at hdist

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.exists_radial_sphere_nets_of_totallyBounded_limiting_directions then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.exists_radial_sphere_nets_of_totallyBounded_limiting_directions"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.exists_radial_sphere_nets_of_totallyBounded_limiting_directions ``Submission.DifferentialGeometry.Toponogov.exists_radial_sphere_nets_of_totallyBounded_limiting_directions

end DifferentialGeometry.Toponogov
