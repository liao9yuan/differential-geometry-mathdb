import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornEndpoint

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Submission.Set
open scoped _root_.Topology _root_.Submission.Topology _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {W : Type u} [MetricSpace W] [ChartedSpace ThreeSpace W]
  [IsManifold I3 ∞ W]

local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.instFactEqNatFinrankRealThreeSpaceHAddOfNat_1 : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp [ThreeSpace]⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.instFactEqNatFinrankRealThreeSpaceHAddOfNat_1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.instFactEqNatFinrankRealThreeSpaceHAddOfNat_1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.instFactEqNatFinrankRealThreeSpaceHAddOfNat_1 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.instFactEqNatFinrankRealThreeSpaceHAddOfNat_1

omit [IsManifold I3 ∞ W] in
theorem GlobalNeckTube.isConnected_univ (T : GlobalNeckTube W) :
    IsConnected (_root_.Set.univ : Set W) := by
  let : ConnectedSpace (Sphere 2) := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank
      (by simp [ThreeSpace] : 1 < Module.finrank ℝ ThreeSpace)) (0 : ThreeSpace)
      (by norm_num : (0 : ℝ) ≤ 1))
  have hsource : IsConnected T.map.source := by
    rw [T.source_eq]
    exact (_root_.isConnected_univ : IsConnected (_root_.Set.univ : Set (Sphere 2))).prod
      (isConnected_Ioo (by norm_num : (0 : ℝ) < 1))
  have himage := hsource.image T.map T.map.contMDiffOn_toFun.continuousOn
  simpa only [T.map.toPartialEquiv.image_source_eq_target, T.target_eq] using himage

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.GlobalNeckTube.isConnected_univ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.GlobalNeckTube.isConnected_univ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.GlobalNeckTube.isConnected_univ ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.GlobalNeckTube.isConnected_univ

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem edist_eq_ofReal_dist (g : SmoothRiemannianMetric I3 W)
    (H : FiniteHorn g) (x y : W) :
    riemannianEDistOf g x y = ENNReal.ofReal (_root_.Dist.dist x y) := by
  let : ConnectedSpace W := connectedSpace_iff_univ.mpr H.tube.isConnected_univ
  let : _root_.Bundle.RiemannianBundle (fun z : W => TangentSpace I3 z) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle ThreeSpace (fun z : W => TangentSpace I3 z) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro z v w; rfl⟩⟩
  have hfinite : riemannianEDistOf g x y ≠ ⊤ :=
    Geometry.Riemannian.Exponential.riemannianEDist_ne_top (I := I3) x y
  rw [H.intrinsic, metricDistance, ENNReal.ofReal_toReal hfinite]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.edist_eq_ofReal_dist then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.edist_eq_ofReal_dist"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.edist_eq_ofReal_dist ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.edist_eq_ofReal_dist

theorem finiteHorn_ball_subset_subend (g : SmoothRiemannianMetric I3 W)
    (H : FiniteHorn g) (i : ℕ) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ x : W,
      dist (x : UniformSpace.Completion W) H.endpoint < delta → x ∈ H.subend i := by
  let q := H.cut_height i
  have hq : q ∈ _root_.Set.Ioo (0 : ℝ) 1 := H.cut_height_mem i
  let S := H.tube.sectionSet q
  have hS : IsCompact S := by
    simpa only [S, GlobalNeckTube.sectionSet, _root_.Set.Icc_self] using
      H.tube.isCompact_slab hq.1 hq.2
  have hne : S.Nonempty := by
    let p := (H.tube.map.symm (H.axial.point H.axial.length)).1
    exact ⟨H.tube.map (p, q), ⟨(p, q), ⟨mem_univ _, rfl⟩, rfl⟩⟩
  have hc : Continuous (fun z : W => _root_.Dist.dist (z : UniformSpace.Completion W) H.endpoint) :=
    (UniformSpace.Completion.continuous_coe W).dist continuous_const
  obtain ⟨z₀, _hz₀, hmin⟩ := hS.exists_isMinOn hne hc.continuousOn
  let m := _root_.Dist.dist (z₀ : UniformSpace.Completion W) H.endpoint
  have hm : 0 < m := dist_pos.mpr (H.endpoint_missing z₀)
  obtain ⟨d, hd, hdL, htail⟩ := H.cofinal_axial i
  let s : ℝ := _root_.Min.min d (m / 4) / 2
  have hs : 0 < s := half_pos (lt_min hd (by positivity))
  have hsd : s ≤ d := by
    have h := min_le_left d (m / 4)
    dsimp [s]
    linarith
  have hsm : s < m / 4 := by
    have h := min_le_right d (m / 4)
    dsimp [s]
    linarith
  have hsL : s ∈ _root_.Set.Ioc (0 : ℝ) H.axial.length := ⟨hs, hsd.trans hdL⟩
  have hstart : H.tube.height (H.axial.point s) < q := by
    have h := htail s ⟨hs, hsd⟩
    rwa [H.subend_eq i] at h
  refine ⟨m / 4, by positivity, ?_⟩
  intro x hx
  by_contra hnot
  have hend : q ≤ H.tube.height x := by
    apply le_of_not_gt
    intro hlt
    apply hnot
    rw [H.subend_eq i]
    exact hlt
  have hax : _root_.Dist.dist (H.axial.point s) x < m / 2 := by
    calc
      _ = _root_.Dist.dist (H.axial.point s : UniformSpace.Completion W)
          (x : UniformSpace.Completion W) := by rw [UniformSpace.Completion.dist_eq]
      _ ≤ _root_.Dist.dist (H.axial.point s : UniformSpace.Completion W) H.endpoint +
          dist H.endpoint (x : UniformSpace.Completion W) := dist_triangle _ _ _
      _ = s + _root_.Dist.dist (x : UniformSpace.Completion W) H.endpoint := by
        rw [H.axial.radial s hsL, dist_comm H.endpoint]
      _ < m / 2 := by linarith
  have hedist : riemannianEDistOf g (H.axial.point s) x < ENNReal.ofReal (m / 2) := by
    rw [H.edist_eq_ofReal_dist]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hax
  obtain ⟨gamma, hg0, hg1, hgsmooth, hlength⟩ := exists_lt_of_edistOf_lt g hedist
  have hh : ContinuousOn (H.tube.height ∘ gamma) (_root_.Set.Icc (0 : ℝ) 1) :=
    H.tube.continuous_height.comp_continuousOn hgsmooth.continuousOn
  obtain ⟨t, ht, hheight⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hh
    (show q ∈ _root_.Set.Icc ((H.tube.height ∘ gamma) 0) ((H.tube.height ∘ gamma) 1) by
      simpa only [Function.comp_apply, hg0, hg1, _root_.Set.mem_Icc] using And.intro hstart.le hend)
  have hsection : gamma t ∈ S := (H.tube.mem_sectionSet_iff hq (gamma t)).mpr hheight
  have hprefix := edistOf_le_metricPathELength g ht.1
    (hgsmooth.mono (_root_.Set.Icc_subset_Icc le_rfl ht.2))
  have hlenprefix := metricPathELength_mono g gamma (a := 0) (b := t)
    (a' := 0) (b' := 1) le_rfl ht.2
  have hshort := (hprefix.trans hlenprefix).trans_lt hlength
  rw [hg0, H.edist_eq_ofReal_dist] at hshort
  have hreal : _root_.Dist.dist (H.axial.point s) (gamma t) < m / 2 :=
    (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp hshort
  have hlower : m ≤ _root_.Dist.dist (gamma t : UniformSpace.Completion W) H.endpoint := hmin hsection
  have hupper : _root_.Dist.dist (gamma t : UniformSpace.Completion W) H.endpoint < m := by
    calc
      _ ≤ _root_.Dist.dist (gamma t : UniformSpace.Completion W)
            (H.axial.point s : UniformSpace.Completion W) +
          dist (H.axial.point s : UniformSpace.Completion W) H.endpoint := dist_triangle _ _ _
      _ = _root_.Dist.dist (H.axial.point s) (gamma t) + s := by
        rw [UniformSpace.Completion.dist_eq, H.axial.radial s hsL, dist_comm (gamma t)]
      _ < m := by linarith
  exact (not_lt_of_ge hlower) hupper

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finiteHorn_ball_subset_subend then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finiteHorn_ball_subset_subend"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finiteHorn_ball_subset_subend ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finiteHorn_ball_subset_subend

theorem finiteHorn_eventually_mem_subend (g : SmoothRiemannianMetric I3 W)
    (H : FiniteHorn g) {w : ℕ → W}
    (hw : _root_.Filter.Tendsto (fun n => (w n : UniformSpace.Completion W)) _root_.Filter.atTop (𝓝 H.endpoint))
    (i : ℕ) : ∀ᶠ n in _root_.Filter.atTop, w n ∈ H.subend i := by
  obtain ⟨delta, hdelta, hball⟩ := finiteHorn_ball_subset_subend g H i
  have hnear := hw.eventually (Metric.ball_mem_nhds H.endpoint hdelta)
  exact hnear.mono (fun n hn => hball (w n) hn)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finiteHorn_eventually_mem_subend then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finiteHorn_eventually_mem_subend"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finiteHorn_eventually_mem_subend ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finiteHorn_eventually_mem_subend

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
