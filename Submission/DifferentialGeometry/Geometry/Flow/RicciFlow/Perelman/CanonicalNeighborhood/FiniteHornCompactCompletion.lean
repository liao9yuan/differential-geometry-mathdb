import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornCompactHull

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Submission.Set
open scoped _root_.Topology _root_.Submission.Topology _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Tensor0SBundle

universe u
variable {W : Type u} [MetricSpace W] [ChartedSpace ThreeSpace W]
  [IsManifold I3 ∞ W] [SigmaCompactSpace W]

theorem exists_finiteHorn_compact_complete_metric_depth :
    ∃ H₀ : ℝ, 0 < H₀ ∧ ∀ (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g),
      H₀ ≤ H.collar_depth → ∀ outer : ℕ, ∃ inner : ℕ,
        closure (H.subend inner) ⊆ H.subend outer ∧
        ∀ A B : Set W, IsCompact A → IsCompact B →
          A ⊆ H.subend inner → B ⊆ H.subend inner →
          ∃ (g' : SmoothRiemannianMetric I3 W) (U K : Set W) (eta : ℝ),
            RiemannianMetricComplete g' ∧ IsOpen U ∧ IsCompact K ∧ 0 < eta ∧
            K ⊆ U ∧ A ∪ B ⊆ U ∧
            (∀ z ∈ U, g'.inner z = g.inner z) ∧
            (∀ z (v : TangentSpace I3 z), g.inner z v v ≤ g'.inner z v v) ∧
            ∀ x ∈ A, ∀ y ∈ B,
              riemannianEDistOf g' x y = ENNReal.ofReal (_root_.Dist.dist x y) ∧
              (∀ z : W, _root_.Dist.dist x z + _root_.Dist.dist z y ≤ _root_.Dist.dist x y + eta →
                z ∈ H.subend outer ∩ K) ∧
              ∀ gamma : ℝ → W,
                ContMDiffOn 𝓘(ℝ, ℝ) I3 1 gamma (_root_.Set.Icc (0 : ℝ) 1) →
                gamma 0 = x → gamma 1 = y →
                metricPathELength g gamma 0 1 ≤
                  ENNReal.ofReal (_root_.Dist.dist x y) + ENNReal.ofReal eta →
                ∀ s ∈ _root_.Set.Icc (0 : ℝ) 1, gamma s ∈ H.subend outer ∩ K := by
  obtain ⟨Hsave, hHsave, hsave⟩ := exists_finiteHorn_no_endpoint_shortcut_depth (W := W)
  obtain ⟨Hmin, _hHmin, hmin⟩ := exists_finiteHorn_deep_minimizer_depth (W := W)
  refine ⟨max Hsave Hmin, hHsave.trans_le (le_max_left _ _), ?_⟩
  intro g H hdepth outer
  obtain ⟨j, hj, _hconnect⟩ := hmin g H ((le_max_right _ _).trans hdepth) outer
  obtain ⟨d, hd, hrays⟩ := finiteHorn_exists_intrinsic_endRay_near_endpoint g H
  obtain ⟨delta, hdelta, hball⟩ := finiteHorn_ball_subset_subend g H outer
  obtain ⟨k, hk⟩ := finiteHorn_subend_radial_small g H
    (lt_min hd (by positivity : 0 < delta / 8))
  have hmono : Antitone H.subend := antitone_nat_of_succ_le H.nested
  refine ⟨max j k, (closure_mono (hmono (le_max_left j k))).trans hj, ?_⟩
  intro A B hA hB hAin hBin
  have hsmall (z : W) (hz : z ∈ H.subend (_root_.Max.max j k)) :
      dist (z : UniformSpace.Completion W) H.endpoint < _root_.Min.min d (delta / 8) :=
    hk z (hmono (le_max_right j k) hz)
  have hgap : ∀ x ∈ A, ∀ y ∈ B,
      _root_.Dist.dist x y < _root_.Dist.dist (x : UniformSpace.Completion W) H.endpoint +
        dist (y : UniformSpace.Completion W) H.endpoint := by
    intro x hx y hy
    obtain ⟨a, ha⟩ := hrays x ((hsmall x (hAin hx)).trans_le (min_le_left _ _))
    obtain ⟨b, hb⟩ := hrays y ((hsmall y (hBin hy)).trans_le (min_le_left _ _))
    have haRad := a.radial a.length ⟨a.length_pos, le_rfl⟩
    have hbRad := b.radial b.length ⟨b.length_pos, le_rfl⟩
    rw [ha] at haRad
    rw [hb] at hbRad
    have h := hsave g H ((le_max_left _ _).trans hdepth) a b
    rwa [ha, hb, ← haRad, ← hbRad] at h
  obtain ⟨eps, heps, K₀, hK₀, hcapture⟩ :=
    finiteHorn_exists_compact_near_minimizing_hull g H outer hA hB hgap
  let eta : ℝ := _root_.Min.min eps (delta / 4)
  have heta : 0 < eta := lt_min heps (by positivity)
  let K : Set W := K₀ ∪ (A ∪ B)
  have hK : IsCompact K := hK₀.union (hA.union hB)
  have hpointTrap : ∀ x ∈ A, ∀ y ∈ B, ∀ z : W,
      dist x z + _root_.Dist.dist z y ≤ _root_.Dist.dist x y + eta → z ∈ H.subend outer ∩ K := by
    intro x hx y hy z hlength
    have hxrad := (hsmall x (hAin hx)).trans_le (min_le_right _ _)
    have hyrad := (hsmall y (hBin hy)).trans_le (min_le_right _ _)
    have hxy := hgap x hx y hy
    have htri := dist_triangle (z : UniformSpace.Completion W)
      (x : UniformSpace.Completion W) H.endpoint
    rw [UniformSpace.Completion.dist_eq, dist_comm z x] at htri
    have hetadelta : eta ≤ delta / 4 := min_le_right _ _
    have hrad : _root_.Dist.dist (z : UniformSpace.Completion W) H.endpoint < delta := by
      linarith [dist_nonneg (x := z) (y := y)]
    have houter : z ∈ H.subend outer := hball _ hrad
    refine ⟨houter, Or.inl (hcapture x hx y hy z houter ?_)⟩
    exact hlength.trans (by
      dsimp only [eta]
      gcongr
      exact min_le_left _ _)
  have htrap : ∀ x ∈ A, ∀ y ∈ B, ∀ gamma : ℝ → W,
      ContMDiffOn 𝓘(ℝ, ℝ) I3 1 gamma (_root_.Set.Icc (0 : ℝ) 1) → gamma 0 = x → gamma 1 = y →
      metricPathELength g gamma 0 1 ≤ riemannianEDistOf g x y + ENNReal.ofReal eta →
      ∀ s ∈ _root_.Set.Icc (0 : ℝ) 1, gamma s ∈ H.subend outer ∩ K := by
    intro x hx y hy gamma hsmooth hstart hend hnear s hs
    have hleft := edistOf_le_metricPathELength g hs.1
      (hsmooth.mono (_root_.Set.Icc_subset_Icc le_rfl hs.2))
    have hright := edistOf_le_metricPathELength g hs.2
      (hsmooth.mono (_root_.Set.Icc_subset_Icc hs.1 le_rfl))
    rw [hstart, H.edist_eq_ofReal_dist] at hleft
    rw [hend, H.edist_eq_ofReal_dist] at hright
    have hsum := ((add_le_add hleft hright).trans_eq
      (metricPathELength_add g gamma hs.1 hs.2)).trans hnear
    rw [← ENNReal.ofReal_add dist_nonneg dist_nonneg, H.edist_eq_ofReal_dist,
      ← ENNReal.ofReal_add dist_nonneg heta.le] at hsum
    have hlength : _root_.Dist.dist x (gamma s) + _root_.Dist.dist (gamma s) y ≤ _root_.Dist.dist x y + eta :=
      (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hsum
    exact hpointTrap x hx y hy (gamma s) hlength
  obtain ⟨g', U, hcomplete, hU, hKU, heq, hle⟩ :=
    exists_riemannianMetricComplete_eqOn_of_isCompact g hK
  refine ⟨g', U, K, eta, hcomplete, hU, hK, heta, hKU,
    fun z hz => hKU (Or.inr hz), heq, hle, ?_⟩
  intro x hx y hy
  have hfinite : riemannianEDistOf g x y ≠ ⊤ := by
    rw [H.edist_eq_ofReal_dist]
    exact ENNReal.ofReal_ne_top
  have hdist := Geometry.riemannianEDistOf_eq_of_near_minimizer_trapping g g' heta hfinite
    (fun z hz => heq z (hKU hz)) hle
    (fun gamma hsmooth hstart hend hnear s hs =>
      (htrap x hx y hy gamma hsmooth hstart hend hnear s hs).2)
  refine ⟨hdist.trans (edist_eq_ofReal_dist g H x y), hpointTrap x hx y hy, ?_⟩
  simpa only [H.edist_eq_ofReal_dist] using htrap x hx y hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_finiteHorn_compact_complete_metric_depth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_finiteHorn_compact_complete_metric_depth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_finiteHorn_compact_complete_metric_depth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_finiteHorn_compact_complete_metric_depth

theorem auxiliary_sectional_nonnegative_of_distance_add
    (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g)
    (g' : SmoothRiemannianMetric I3 W) {U : Set W}
    (hU : IsOpen U) (heq : ∀ z ∈ U, g'.inner z = g.inner z)
    (hle : ∀ z (v : TangentSpace I3 z), g.inner z v v ≤ g'.inner z v v)
    {x y : W} (hdist : riemannianEDistOf g' x y = ENNReal.ofReal (_root_.Dist.dist x y))
    {eta : ℝ} (heta : 0 ≤ eta)
    (hcapture : ∀ z : W, _root_.Dist.dist x z + _root_.Dist.dist z y ≤ _root_.Dist.dist x y + eta → z ∈ U)
    {z : W} (hz : riemannianEDistOf g' x z + riemannianEDistOf g' z y =
      riemannianEDistOf g' x y) :
    metricRm04At (I := I3) g' z ∈ tensor04SectionalNonnegativeCone (I := I3) (M := W) := by
  have hsum := (add_le_add (edistOf_mono g g' hle x z)
    (edistOf_mono g g' hle z y)).trans_eq (hz.trans hdist)
  rw [H.edist_eq_ofReal_dist, H.edist_eq_ofReal_dist,
    ← ENNReal.ofReal_add dist_nonneg dist_nonneg] at hsum
  have hmetric : _root_.Dist.dist x z + _root_.Dist.dist z y ≤ _root_.Dist.dist x y :=
    (ENNReal.ofReal_le_ofReal_iff dist_nonneg).mp hsum
  have hzU : z ∈ U := hcapture z (hmetric.trans (le_add_of_nonneg_right heta))
  apply (metricRm04At_mem_tensor04SectionalNonnegativeCone_iff g' z).mpr
  intro v w
  rw [metricRm04StandardAt_congr_metric g g' hU heq hzU v w w v]
  have hslots : (fun i => ![v, w, w, v] i) = vec4 v w w v := by
    funext i
    fin_cases i <;> rfl
  simpa only [_root_.MulZeroClass.zero_mul, metricRm04StandardAt_apply, hslots] using H.nonnegative z (_root_.Set.mem_univ z) v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.auxiliary_sectional_nonnegative_of_distance_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.auxiliary_sectional_nonnegative_of_distance_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.auxiliary_sectional_nonnegative_of_distance_add ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.auxiliary_sectional_nonnegative_of_distance_add


theorem finiteHorn_compact_complete_metric_of_endRay_dist_lt_sum
    (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g)
    (hsave : ∀ a b : EndRay H.endpoint,
      _root_.Dist.dist (a.point a.length) (b.point b.length) < a.length + b.length) :
    ∀ outer : ℕ, ∃ inner : ℕ,
        closure (H.subend inner) ⊆ H.subend outer ∧
        ∀ A B : Set W, IsCompact A → IsCompact B →
          A ⊆ H.subend inner → B ⊆ H.subend inner →
          ∃ (g' : SmoothRiemannianMetric I3 W) (U K : Set W) (eta : ℝ),
            RiemannianMetricComplete g' ∧ IsOpen U ∧ IsCompact K ∧ 0 < eta ∧
            K ⊆ U ∧ A ∪ B ⊆ U ∧
            (∀ z ∈ U, g'.inner z = g.inner z) ∧
            (∀ z (v : TangentSpace I3 z), g.inner z v v ≤ g'.inner z v v) ∧
            ∀ x ∈ A, ∀ y ∈ B,
              riemannianEDistOf g' x y = ENNReal.ofReal (_root_.Dist.dist x y) ∧
              (∀ z : W, _root_.Dist.dist x z + _root_.Dist.dist z y ≤ _root_.Dist.dist x y + eta →
                z ∈ H.subend outer ∩ K) ∧
              ∀ gamma : ℝ → W,
                ContMDiffOn 𝓘(ℝ, ℝ) I3 1 gamma (_root_.Set.Icc (0 : ℝ) 1) →
                gamma 0 = x → gamma 1 = y →
                metricPathELength g gamma 0 1 ≤
                  ENNReal.ofReal (_root_.Dist.dist x y) + ENNReal.ofReal eta →
                ∀ s ∈ _root_.Set.Icc (0 : ℝ) 1, gamma s ∈ H.subend outer ∩ K := by
  intro outer
  obtain ⟨j, hjheight⟩ :=
    ((tendsto_order.1 H.cut_height_zero).2 _ (H.cut_height_mem outer).1).exists
  have hj : closure (H.subend j) ⊆ H.subend outer := by
    have hclosed : IsClosed {z : W | H.tube.height z ≤ H.cut_height j} :=
      isClosed_le H.tube.continuous_height continuous_const
    have hsub : H.subend j ⊆ {z : W | H.tube.height z ≤ H.cut_height j} := by
      intro z hz
      rw [H.subend_eq j] at hz
      change H.tube.height z < H.cut_height j at hz
      exact hz.le
    intro z hz
    rw [H.subend_eq outer]
    exact (closure_minimal hsub hclosed hz).trans_lt hjheight
  obtain ⟨d, hd, hrays⟩ := finiteHorn_exists_intrinsic_endRay_near_endpoint g H
  obtain ⟨delta, hdelta, hball⟩ := finiteHorn_ball_subset_subend g H outer
  obtain ⟨k, hk⟩ := finiteHorn_subend_radial_small g H
    (lt_min hd (by positivity : 0 < delta / 8))
  have hmono : Antitone H.subend := antitone_nat_of_succ_le H.nested
  refine ⟨max j k, (closure_mono (hmono (le_max_left j k))).trans hj, ?_⟩
  intro A B hA hB hAin hBin
  have hsmall (z : W) (hz : z ∈ H.subend (_root_.Max.max j k)) :
      dist (z : UniformSpace.Completion W) H.endpoint < _root_.Min.min d (delta / 8) :=
    hk z (hmono (le_max_right j k) hz)
  have hgap : ∀ x ∈ A, ∀ y ∈ B,
      _root_.Dist.dist x y < _root_.Dist.dist (x : UniformSpace.Completion W) H.endpoint +
        dist (y : UniformSpace.Completion W) H.endpoint := by
    intro x hx y hy
    obtain ⟨a, ha⟩ := hrays x ((hsmall x (hAin hx)).trans_le (min_le_left _ _))
    obtain ⟨b, hb⟩ := hrays y ((hsmall y (hBin hy)).trans_le (min_le_left _ _))
    have haRad := a.radial a.length ⟨a.length_pos, le_rfl⟩
    have hbRad := b.radial b.length ⟨b.length_pos, le_rfl⟩
    rw [ha] at haRad
    rw [hb] at hbRad
    have h := hsave a b
    rwa [ha, hb, ← haRad, ← hbRad] at h
  obtain ⟨eps, heps, K₀, hK₀, hcapture⟩ :=
    finiteHorn_exists_compact_near_minimizing_hull g H outer hA hB hgap
  let eta : ℝ := _root_.Min.min eps (delta / 4)
  have heta : 0 < eta := lt_min heps (by positivity)
  let K : Set W := K₀ ∪ (A ∪ B)
  have hK : IsCompact K := hK₀.union (hA.union hB)
  have hpointTrap : ∀ x ∈ A, ∀ y ∈ B, ∀ z : W,
      dist x z + _root_.Dist.dist z y ≤ _root_.Dist.dist x y + eta → z ∈ H.subend outer ∩ K := by
    intro x hx y hy z hlength
    have hxrad := (hsmall x (hAin hx)).trans_le (min_le_right _ _)
    have hyrad := (hsmall y (hBin hy)).trans_le (min_le_right _ _)
    have hxy := hgap x hx y hy
    have htri := dist_triangle (z : UniformSpace.Completion W)
      (x : UniformSpace.Completion W) H.endpoint
    rw [UniformSpace.Completion.dist_eq, dist_comm z x] at htri
    have hetadelta : eta ≤ delta / 4 := min_le_right _ _
    have hrad : _root_.Dist.dist (z : UniformSpace.Completion W) H.endpoint < delta := by
      linarith [dist_nonneg (x := z) (y := y)]
    have houter : z ∈ H.subend outer := hball _ hrad
    refine ⟨houter, Or.inl (hcapture x hx y hy z houter ?_)⟩
    exact hlength.trans (by
      dsimp only [eta]
      gcongr
      exact min_le_left _ _)
  have htrap : ∀ x ∈ A, ∀ y ∈ B, ∀ gamma : ℝ → W,
      ContMDiffOn 𝓘(ℝ, ℝ) I3 1 gamma (_root_.Set.Icc (0 : ℝ) 1) → gamma 0 = x → gamma 1 = y →
      metricPathELength g gamma 0 1 ≤ riemannianEDistOf g x y + ENNReal.ofReal eta →
      ∀ s ∈ _root_.Set.Icc (0 : ℝ) 1, gamma s ∈ H.subend outer ∩ K := by
    intro x hx y hy gamma hsmooth hstart hend hnear s hs
    have hleft := edistOf_le_metricPathELength g hs.1
      (hsmooth.mono (_root_.Set.Icc_subset_Icc le_rfl hs.2))
    have hright := edistOf_le_metricPathELength g hs.2
      (hsmooth.mono (_root_.Set.Icc_subset_Icc hs.1 le_rfl))
    rw [hstart, H.edist_eq_ofReal_dist] at hleft
    rw [hend, H.edist_eq_ofReal_dist] at hright
    have hsum := ((add_le_add hleft hright).trans_eq
      (metricPathELength_add g gamma hs.1 hs.2)).trans hnear
    rw [← ENNReal.ofReal_add dist_nonneg dist_nonneg, H.edist_eq_ofReal_dist,
      ← ENNReal.ofReal_add dist_nonneg heta.le] at hsum
    have hlength : _root_.Dist.dist x (gamma s) + _root_.Dist.dist (gamma s) y ≤ _root_.Dist.dist x y + eta :=
      (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hsum
    exact hpointTrap x hx y hy (gamma s) hlength
  obtain ⟨g', U, hcomplete, hU, hKU, heq, hle⟩ :=
    exists_riemannianMetricComplete_eqOn_of_isCompact g hK
  refine ⟨g', U, K, eta, hcomplete, hU, hK, heta, hKU,
    fun z hz => hKU (Or.inr hz), heq, hle, ?_⟩
  intro x hx y hy
  have hfinite : riemannianEDistOf g x y ≠ ⊤ := by
    rw [H.edist_eq_ofReal_dist]
    exact ENNReal.ofReal_ne_top
  have hdist := Geometry.riemannianEDistOf_eq_of_near_minimizer_trapping g g' heta hfinite
    (fun z hz => heq z (hKU hz)) hle
    (fun gamma hsmooth hstart hend hnear s hs =>
      (htrap x hx y hy gamma hsmooth hstart hend hnear s hs).2)
  refine ⟨hdist.trans (edist_eq_ofReal_dist g H x y), hpointTrap x hx y hy, ?_⟩
  simpa only [H.edist_eq_ofReal_dist] using htrap x hx y hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finiteHorn_compact_complete_metric_of_endRay_dist_lt_sum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finiteHorn_compact_complete_metric_of_endRay_dist_lt_sum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finiteHorn_compact_complete_metric_of_endRay_dist_lt_sum ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finiteHorn_compact_complete_metric_of_endRay_dist_lt_sum


end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
