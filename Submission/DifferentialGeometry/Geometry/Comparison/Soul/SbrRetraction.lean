import Submission.DifferentialGeometry.Geometry.Comparison.Soul.SbrMaximalFlow

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Manifold _root_.Submission.Manifold _root_.Set
open scoped _root_.Topology _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.NNReal
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Exponential

namespace DifferentialGeometry.Geometry.Topology

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)]

variable (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
  (F : M → ℝ) (L : ℝ≥0) (hF : LipschitzWith L F)
  (hconc : ∀ (p : M) (v : TangentSpace I p),
    ConcaveOn ℝ univ (fun t => F (intrinsicGeodesic g hEnorm p v t)))
  (hC : IsCompact {z : M | 0 ≤ F z}) {m : ℝ}
  (hmax : ∃ q : M, F q = m ∧ ∀ z : M, F z ≤ m)

def selectedMaximalAscent (x : M) : ℝ → M :=
  if hx : 0 ≤ F x ∧ F x < m then
    (exists_maximal_normalized_ascent_curve g hEnorm F L hF hconc hC
      hx.1 hx.2 hmax x rfl).choose
  else fun _ => x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.selectedMaximalAscent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.selectedMaximalAscent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.selectedMaximalAscent ``Submission.DifferentialGeometry.Geometry.Topology.selectedMaximalAscent

local notation "c" => selectedMaximalAscent g hEnorm F L hF hconc hC hmax


theorem selectedMaximalAscent_spec (x : M) (hx : 0 ≤ F x ∧ F x < m) :
    ContinuousOn (c x) (_root_.Set.Icc (F x) m) ∧ c x (F x) = x ∧
      _root_.Set.MapsTo (c x) (_root_.Set.Icc (F x) m) {z : M | 0 ≤ F z} ∧
      (∀ t ∈ _root_.Set.Icc (F x) m, F (c x t) = t) ∧
      (∀ t ∈ _root_.Set.Ico (F x) m,
        let G := intrinsicGeneralizedGradient g hEnorm hF hconc (c x t)
        G ≠ 0 ∧ HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (c x) (_root_.Set.Ici t) t
          (ContinuousLinearMap.toSpanSingleton ℝ ((g.inner (c x t) G G)⁻¹ • G))) ∧
      ∀ T ∈ _root_.Set.Ioo (F x) m,
        LipschitzOnWith (Real.toNNReal (Metric.diam {z : M | 0 ≤ F z} / (m - T)))
          (c x) (_root_.Set.Icc (F x) T) := by
  unfold selectedMaximalAscent
  rw [dif_pos hx]
  exact (exists_maximal_normalized_ascent_curve g hEnorm F L hF hconc hC
    hx.1 hx.2 hmax x rfl).choose_spec

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.selectedMaximalAscent_spec then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.selectedMaximalAscent_spec"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.selectedMaximalAscent_spec ``Submission.DifferentialGeometry.Geometry.Topology.selectedMaximalAscent_spec

def sharafutdinovLevelMap (s : ℝ) (x : M) : M :=
  if s ≤ F x then x else c x s

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.sharafutdinovLevelMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.sharafutdinovLevelMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.sharafutdinovLevelMap ``Submission.DifferentialGeometry.Geometry.Topology.sharafutdinovLevelMap

local notation "R" => sharafutdinovLevelMap g hEnorm F L hF hconc hC hmax

theorem sharafutdinovLevelMap_of_le (s : ℝ) (x : M) (hs : s ≤ F x) : R s x = x := by
  simp only [sharafutdinovLevelMap, if_pos hs]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.sharafutdinovLevelMap_of_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.sharafutdinovLevelMap_of_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.sharafutdinovLevelMap_of_le ``Submission.DifferentialGeometry.Geometry.Topology.sharafutdinovLevelMap_of_le

theorem sharafutdinovLevelMap_eq_ascent (x : M) (hx : 0 ≤ F x ∧ F x < m)
    {s : ℝ} (hs : F x ≤ s) : R s x = c x s := by
  by_cases h : s ≤ F x
  · have heq : s = F x := le_antisymm h hs
    subst s
    rw [sharafutdinovLevelMap_of_le g hEnorm F L hF hconc hC hmax _ _ le_rfl]
    exact (selectedMaximalAscent_spec g hEnorm F L hF hconc hC hmax x hx).2.1.symm
  · simp only [sharafutdinovLevelMap, if_neg h]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.sharafutdinovLevelMap_eq_ascent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.sharafutdinovLevelMap_eq_ascent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.sharafutdinovLevelMap_eq_ascent ``Submission.DifferentialGeometry.Geometry.Topology.sharafutdinovLevelMap_eq_ascent

theorem sharafutdinovLevelMap_level {s : ℝ} (hs : s ∈ _root_.Set.Icc 0 m)
    {x : M} (hx : 0 ≤ F x) : F (R s x) = _root_.Max.max (F x) s := by
  by_cases h : s ≤ F x
  · rw [sharafutdinovLevelMap_of_le g hEnorm F L hF hconc hC hmax s x h,
      max_eq_left h]
  · have hxs : F x < s := lt_of_not_ge h
    have hx' : 0 ≤ F x ∧ F x < m := ⟨hx, hxs.trans_le hs.2⟩
    rw [sharafutdinovLevelMap_eq_ascent g hEnorm F L hF hconc hC hmax x hx' hxs.le,
      (selectedMaximalAscent_spec g hEnorm F L hF hconc hC hmax x hx').2.2.2.1
        s ⟨hxs.le, hs.2⟩, max_eq_right hxs.le]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.sharafutdinovLevelMap_level then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.sharafutdinovLevelMap_level"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.sharafutdinovLevelMap_level ``Submission.DifferentialGeometry.Geometry.Topology.sharafutdinovLevelMap_level

theorem sharafutdinovLevelMap_image {s : ℝ} (hs : s ∈ _root_.Set.Icc 0 m) :
    R s '' {z : M | 0 ≤ F z} = {z : M | s ≤ F z} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change s ≤ F (R s x)
    rw [sharafutdinovLevelMap_level g hEnorm F L hF hconc hC hmax hs hx]
    exact le_max_right _ _
  · intro hy
    exact ⟨y, hs.1.trans hy,
      sharafutdinovLevelMap_of_le g hEnorm F L hF hconc hC hmax s y hy⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.sharafutdinovLevelMap_image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.sharafutdinovLevelMap_image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.sharafutdinovLevelMap_image ``Submission.DifferentialGeometry.Geometry.Topology.sharafutdinovLevelMap_image


theorem sharafutdinovLevelMap_mapsTo {s : ℝ} (hs : s ∈ _root_.Set.Icc 0 m) :
    MapsTo (R s) {z : M | 0 ≤ F z} {z : M | 0 ≤ F z} := by
  intro x hx
  change 0 ≤ F (R s x)
  rw [sharafutdinovLevelMap_level g hEnorm F L hF hconc hC hmax hs hx]
  exact hx.trans (le_max_left _ _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.sharafutdinovLevelMap_mapsTo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.sharafutdinovLevelMap_mapsTo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.sharafutdinovLevelMap_mapsTo ``Submission.DifferentialGeometry.Geometry.Topology.sharafutdinovLevelMap_mapsTo

private theorem selectedMaximalAscent_dist_fixed
    (x y : M) (hx : 0 ≤ F x ∧ F x < m) {t : ℝ}
    (ht : t ∈ _root_.Set.Icc (F x) m) (hty : t ≤ F y) : _root_.Dist.dist (c x t) y ≤ _root_.Dist.dist x y := by
  obtain ⟨hcont, hstart, _hmaps, hlevel, hder, _hlip⟩ :=
    selectedMaximalAscent_spec g hEnorm F L hF hconc hC hmax x hx
  have hanti := antitoneOn_dist_fixed_normalized_intrinsicGeneralizedGradient
    g hEnorm hF hconc (c x) (a := F x) (b := t)
    (hcont.mono (fun u hu => ⟨hu.1, hu.2.trans ht.2⟩))
    (fun u hu => (hder u ⟨hu.1, hu.2.trans_le ht.2⟩).2) y (by
      intro u hu
      rw [hlevel u ⟨hu.1, hu.2.le.trans ht.2⟩]
      exact hu.2.le.trans hty)
  have hd := hanti (show F x ∈ _root_.Set.Icc (F x) t from ⟨le_rfl, ht.1⟩)
    (show t ∈ _root_.Set.Icc (F x) t from ⟨ht.1, le_rfl⟩) ht.1
  simpa only [hstart] using hd

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Topology.selectedMaximalAscent_dist_fixed
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Topology.selectedMaximalAscent_dist_fixed target :: scope.openDecls } }

private theorem sharafutdinovLevelMap_dist_le_of_level_le
    {s : ℝ} (hs : s ∈ _root_.Set.Icc 0 m) (x y : M)
    (hx : 0 ≤ F x) (hy : 0 ≤ F y) (hxy : F x ≤ F y) :
    dist (R s x) (R s y) ≤ _root_.Dist.dist x y := by
  by_cases hsx : s ≤ F x
  · rw [sharafutdinovLevelMap_of_le g hEnorm F L hF hconc hC hmax s x hsx,
      sharafutdinovLevelMap_of_le g hEnorm F L hF hconc hC hmax s y (hsx.trans hxy)]
  · have hxs : F x < s := lt_of_not_ge hsx
    have hx' : 0 ≤ F x ∧ F x < m := ⟨hx, hxs.trans_le hs.2⟩
    rw [sharafutdinovLevelMap_eq_ascent g hEnorm F L hF hconc hC hmax x hx' hxs.le]
    by_cases hsy : s ≤ F y
    · rw [sharafutdinovLevelMap_of_le g hEnorm F L hF hconc hC hmax s y hsy]
      exact selectedMaximalAscent_dist_fixed g hEnorm F L hF hconc hC hmax
        x y hx' ⟨hxs.le, hs.2⟩ hsy
    · have hys : F y < s := lt_of_not_ge hsy
      have hy' : 0 ≤ F y ∧ F y < m := ⟨hy, hys.trans_le hs.2⟩
      rw [sharafutdinovLevelMap_eq_ascent g hEnorm F L hF hconc hC hmax y hy' hys.le]
      obtain ⟨hxcont, _hxstart, _hxmaps, hxlevel, hxder, _hxlip⟩ :=
        selectedMaximalAscent_spec g hEnorm F L hF hconc hC hmax x hx'
      obtain ⟨hycont, hystart, _hymaps, hylevel, hyder, _hylip⟩ :=
        selectedMaximalAscent_spec g hEnorm F L hF hconc hC hmax y hy'
      have hanti := antitoneOn_dist_normalized_intrinsicGeneralizedGradient
        g hEnorm hF hconc (c x) (c y) (a := F y) (b := s)
        (hxcont.mono (fun u hu => ⟨hxy.trans hu.1, hu.2.trans hs.2⟩))
        (hycont.mono (fun u hu => ⟨hu.1, hu.2.trans hs.2⟩))
        (fun u hu => (hxder u ⟨hxy.trans hu.1, hu.2.trans_le hs.2⟩).2)
        (fun u hu => (hyder u ⟨hu.1, hu.2.trans_le hs.2⟩).2) (by
          intro u hu
          rw [hxlevel u ⟨hxy.trans hu.1, hu.2.le.trans hs.2⟩,
            hylevel u ⟨hu.1, hu.2.le.trans hs.2⟩])
      have hd := hanti (show F y ∈ _root_.Set.Icc (F y) s from ⟨le_rfl, hys.le⟩)
        (show s ∈ _root_.Set.Icc (F y) s from ⟨hys.le, le_rfl⟩) hys.le
      change _root_.Dist.dist (c x s) (c y s) ≤ _root_.Dist.dist (c x (F y)) (c y (F y)) at hd
      rw [hystart] at hd
      exact hd.trans (selectedMaximalAscent_dist_fixed g hEnorm F L hF hconc hC hmax
        x y hx' ⟨hxy, hy'.2.le⟩ le_rfl)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Topology.sharafutdinovLevelMap_dist_le_of_level_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Topology.sharafutdinovLevelMap_dist_le_of_level_le target :: scope.openDecls } }

theorem sharafutdinovLevelMap_lipschitzOnWith {s : ℝ} (hs : s ∈ _root_.Set.Icc 0 m) :
    LipschitzOnWith 1 (R s) {z : M | 0 ≤ F z} := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  simp only [NNReal.coe_one, one_mul]
  rcases le_total (F x) (F y) with hxy | hyx
  · exact sharafutdinovLevelMap_dist_le_of_level_le g hEnorm F L hF hconc hC hmax
      hs x y hx hy hxy
  · simpa only [dist_comm] using
      sharafutdinovLevelMap_dist_le_of_level_le g hEnorm F L hF hconc hC hmax
        hs y x hy hx hyx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.sharafutdinovLevelMap_lipschitzOnWith then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.sharafutdinovLevelMap_lipschitzOnWith"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.sharafutdinovLevelMap_lipschitzOnWith ``Submission.DifferentialGeometry.Geometry.Topology.sharafutdinovLevelMap_lipschitzOnWith

theorem sharafutdinovLevelMap_continuousOn_orbit {x : M} (hx : 0 ≤ F x) :
    ContinuousOn (fun s => R s x) (_root_.Set.Icc 0 m) := by
  have hxm : F x ≤ m := hmax.choose_spec.2 x
  by_cases hlt : F x < m
  · have hx' : 0 ≤ F x ∧ F x < m := ⟨hx, hlt⟩
    obtain ⟨hcont, hstart, _hmaps, _hlevel, _hder, _hlip⟩ :=
      selectedMaximalAscent_spec g hEnorm F L hF hconc hC hmax x hx'
    have hmaxcont : Continuous (fun s : ℝ => _root_.Max.max (F x) s) := continuous_const.max continuous_id
    have hc : ContinuousOn (fun s => c x (_root_.Max.max (F x) s)) (_root_.Set.Icc 0 m) :=
      hcont.comp hmaxcont.continuousOn (fun s hs =>
        ⟨le_max_left _ _, max_le hxm hs.2⟩)
    apply hc.congr
    intro s _hs
    change R s x = c x (_root_.Max.max (F x) s)
    by_cases h : s ≤ F x
    · rw [sharafutdinovLevelMap_of_le g hEnorm F L hF hconc hC hmax s x h,
        max_eq_left h, hstart]
    · rw [max_eq_right (le_of_not_ge h)]
      exact sharafutdinovLevelMap_eq_ascent g hEnorm F L hF hconc hC hmax x hx'
        (le_of_not_ge h)
  · have heq : F x = m := le_antisymm hxm (le_of_not_gt hlt)
    apply (continuousOn_const : ContinuousOn (fun _ : ℝ => x) (_root_.Set.Icc (0 : ℝ) m)).congr
    intro s hs
    exact sharafutdinovLevelMap_of_le g hEnorm F L hF hconc hC hmax s x (by
      simpa only [heq] using hs.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.sharafutdinovLevelMap_continuousOn_orbit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.sharafutdinovLevelMap_continuousOn_orbit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.sharafutdinovLevelMap_continuousOn_orbit ``Submission.DifferentialGeometry.Geometry.Topology.sharafutdinovLevelMap_continuousOn_orbit

theorem sharafutdinovLevelMap_hasMFDerivWithinAt_orbit {x : M} (hx : 0 ≤ F x)
    {t : ℝ} (hxt : F x ≤ t) (htm : t < m) :
    let G := intrinsicGeneralizedGradient g hEnorm hF hconc (R t x)
    G ≠ 0 ∧ HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s => R s x) (_root_.Set.Ici t) t
      (ContinuousLinearMap.toSpanSingleton ℝ ((g.inner (R t x) G G)⁻¹ • G)) := by
  have hx' : 0 ≤ F x ∧ F x < m := ⟨hx, hxt.trans_lt htm⟩
  have hdata := (selectedMaximalAscent_spec g hEnorm F L hF hconc hC hmax x hx').2.2.2.2.1
    t ⟨hxt, htm⟩
  have hbase : R t x = c x t :=
    sharafutdinovLevelMap_eq_ascent g hEnorm F L hF hconc hC hmax x hx' hxt
  have hevent : (fun s => R s x) =ᶠ[𝓝[_root_.Set.Ici t] t] c x := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact sharafutdinovLevelMap_eq_ascent g hEnorm F L hF hconc hC hmax x hx' (hxt.trans hs)
  refine ⟨?_, ?_⟩
  · rw [hbase]
    exact hdata.1
  · have hder := hdata.2.congr_of_eventuallyEq hevent hbase
    rw [← hbase] at hder
    exact hder

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.sharafutdinovLevelMap_hasMFDerivWithinAt_orbit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.sharafutdinovLevelMap_hasMFDerivWithinAt_orbit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.sharafutdinovLevelMap_hasMFDerivWithinAt_orbit ``Submission.DifferentialGeometry.Geometry.Topology.sharafutdinovLevelMap_hasMFDerivWithinAt_orbit

end DifferentialGeometry.Geometry.Topology

end
