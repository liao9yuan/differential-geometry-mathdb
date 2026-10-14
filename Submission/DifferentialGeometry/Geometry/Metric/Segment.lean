import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.UniformSpace.UniformEmbedding
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.MetricSpace.Completion
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Geometry

variable {M : Type*} [PseudoMetricSpace M]

theorem isometry_Icc_of_lipschitzOnWith_of_dist_eq
    {γ : ℝ → M} {a b : ℝ} (hγ : LipschitzOnWith 1 γ (_root_.Set.Icc a b))
    (hend : _root_.Dist.dist (γ a) (γ b) = b - a) :
    Isometry (fun t : _root_.Set.Icc a b ↦ γ t) := by
  apply Isometry.of_dist_eq
  intro s t
  suffices h : ∀ s t : _root_.Set.Icc a b, (s : ℝ) ≤ t → _root_.Dist.dist (γ s) (γ t) = (t : ℝ) - s by
    rcases le_total (s : ℝ) t with hst | hts
    · simpa [Subtype.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hst)] using h s t hst
    · rw [dist_comm, h t s hts]
      simp [Subtype.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hts)]
  intro s t hst
  have hab : a ≤ b := s.2.1.trans s.2.2
  have hstUpper := hγ.dist_le_mul (s : ℝ) s.2 t t.2
  have haUpper := hγ.dist_le_mul a ⟨le_rfl, hab⟩ (s : ℝ) s.2
  have hbUpper := hγ.dist_le_mul (t : ℝ) t.2 b ⟨hab, le_rfl⟩
  simp only [NNReal.coe_one, one_mul, Real.dist_eq,
    abs_of_nonpos (sub_nonpos.mpr hst), abs_of_nonpos (sub_nonpos.mpr s.2.1),
    abs_of_nonpos (sub_nonpos.mpr t.2.2)] at hstUpper haUpper hbUpper
  have htri := dist_triangle4 (γ a) (γ s) (γ t) (γ b)
  rw [hend] at htri
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.isometry_Icc_of_lipschitzOnWith_of_dist_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.isometry_Icc_of_lipschitzOnWith_of_dist_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.isometry_Icc_of_lipschitzOnWith_of_dist_eq ``Submission.DifferentialGeometry.Geometry.isometry_Icc_of_lipschitzOnWith_of_dist_eq

end DifferentialGeometry.Geometry

open _root_.Filter
open scoped _root_.Topology

namespace Isometry
open _root_.Isometry

variable {X : Type*} [MetricSpace X] [CompleteSpace X]

open _root_.Isometry in
theorem exists_endpoint_Ico {a b : ℝ} (hab : a < b) {γ : ℝ → X}
    (hγ : Isometry (fun s : _root_.Set.Ico a b => γ s)) :
    ∃! E : X, _root_.Filter.Tendsto γ (𝓝[<] b) (𝓝 E) ∧
      ∀ s ∈ _root_.Set.Ico a b, _root_.Dist.dist (γ s) E = b - s := by
  have hlip : LipschitzOnWith 1 γ (_root_.Set.Ico a b) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro s hs t ht
    rw [NNReal.coe_one, one_mul]
    exact (hγ.dist_eq ⟨s, hs⟩ ⟨t, ht⟩).le
  have hc : Cauchy (𝓝[<] b) := cauchy_nhds.mono nhdsWithin_le_nhds
  obtain ⟨E, hE⟩ := cauchy_map_iff_exists_tendsto.mp
    (hc.map_of_le hlip.uniformContinuousOn (le_principal_iff.mpr (Ico_mem_nhdsLT hab)))
  refine ⟨E, ⟨hE, ?_⟩, fun E' hE' => tendsto_nhds_unique hE'.1 hE⟩
  intro s hs
  have hdist : _root_.Filter.Tendsto (fun t => _root_.Dist.dist (γ s) (γ t)) (𝓝[<] b) (𝓝 (_root_.Dist.dist (γ s) E)) :=
    tendsto_const_nhds.dist hE
  have hreal : _root_.Filter.Tendsto (fun t : ℝ => _root_.Dist.dist s t) (𝓝[<] b) (𝓝 (_root_.Dist.dist s b)) :=
    tendsto_const_nhds.dist nhdsWithin_le_nhds
  have heq : (fun t => _root_.Dist.dist (γ s) (γ t)) =ᶠ[𝓝[<] b] (fun t : ℝ => _root_.Dist.dist s t) := by
    filter_upwards [Ico_mem_nhdsLT hab] with t ht
    exact hγ.dist_eq ⟨s, hs⟩ ⟨t, ht⟩
  have hlim := tendsto_nhds_unique hdist (hreal.congr' heq.symm)
  simpa only [Real.dist_eq, abs_of_neg (sub_neg.mpr hs.2), neg_sub] using hlim

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Isometry.exists_endpoint_Ico then
    throwError "Refusing to shadow existing declaration Isometry.exists_endpoint_Ico"
  Lean.modifyEnv fun env => Lean.addAlias env `Isometry.exists_endpoint_Ico ``Submission.Isometry.exists_endpoint_Ico

end Isometry

namespace UniformSpace.Completion
open _root_.UniformSpace _root_.UniformSpace.Completion

variable {W : Type*} [MetricSpace W]

open _root_.UniformSpace _root_.UniformSpace.Completion in
theorem ne_coe_of_tendsto_atTop {ι : Type*} {l : Filter ι} [l.NeBot]
    {γ : ι → W} {E : _root_.UniformSpace.Completion W}
    (hE : _root_.Filter.Tendsto (fun s => (γ s : _root_.UniformSpace.Completion W)) l (𝓝 E))
    {f : W → ℝ} (hdiv : _root_.Filter.Tendsto (f ∘ γ) l _root_.Filter.atTop)
    (x : W) (hf : ContinuousAt f x) : E ≠ (x : _root_.UniformSpace.Completion W) := by
  intro hEq
  rw [hEq] at hE
  have hγ : _root_.Filter.Tendsto γ l (𝓝 x) := _root_.UniformSpace.Completion.coe_isometry.isEmbedding.tendsto_nhds_iff.mpr hE
  exact not_tendsto_atTop_of_tendsto_nhds (hf.tendsto.comp hγ) hdiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `UniformSpace.Completion.ne_coe_of_tendsto_atTop then
    throwError "Refusing to shadow existing declaration UniformSpace.Completion.ne_coe_of_tendsto_atTop"
  Lean.modifyEnv fun env => Lean.addAlias env `UniformSpace.Completion.ne_coe_of_tendsto_atTop ``Submission.UniformSpace.Completion.ne_coe_of_tendsto_atTop

end UniformSpace.Completion

namespace DifferentialGeometry.Geometry

variable {M : Type*} [PseudoMetricSpace M]

open _root_.Filter _root_.UniformSpace _root_.Submission.UniformSpace in
open scoped _root_.Topology in
theorem exists_completion_endpoint_of_isometry
    {a b : ℝ} (hab : a < b)
    {g : _root_.Set.Ico a b → M} (hg : Isometry g) :
    ∃ q : _root_.UniformSpace.Completion M,
      _root_.Filter.Tendsto (fun t => (g t : _root_.UniformSpace.Completion M))
        (_root_.Filter.comap (Subtype.val : _root_.Set.Ico a b → ℝ) (𝓝 b)) (𝓝 q) ∧
      ∀ t : _root_.Set.Ico a b, _root_.Dist.dist q (g t : _root_.UniformSpace.Completion M) = b - t := by
  let l : Filter (_root_.Set.Ico a b) := _root_.Filter.comap Subtype.val (𝓝 b)
  have hmap : _root_.Filter.NeBot (_root_.Filter.map (Subtype.val : _root_.Set.Ico a b → ℝ) l) := by
    rw [_root_.Filter.map_comap_setCoe_val]
    exact right_nhdsWithin_Ico_neBot hab
  let _ : _root_.Filter.NeBot l := hmap.of_map
  have hl : Cauchy l := cauchy_nhds.comap'
    (le_of_eq isUniformEmbedding_subtype_val.isUniformInducing.comap_uniformity) inferInstance
  let G : _root_.Set.Ico a b → _root_.UniformSpace.Completion M := fun t => (g t : _root_.UniformSpace.Completion M)
  have hG : Isometry G := Completion.coe_isometry.comp hg
  obtain ⟨q, hq⟩ := CompleteSpace.complete (hl.map hG.uniformContinuous)
  have hqT : _root_.Filter.Tendsto G l (𝓝 q) := hq
  refine ⟨q, hqT, ?_⟩
  intro t
  have hdist := hqT.dist (tendsto_const_nhds (x := G t))
  have hparam : _root_.Filter.Tendsto (Subtype.val : _root_.Set.Ico a b → ℝ) l (𝓝 b) := _root_.Filter.tendsto_comap
  have hdist' := hparam.dist (tendsto_const_nhds (x := (t : ℝ)))
  have hdist'' : _root_.Filter.Tendsto (fun s : _root_.Set.Ico a b => _root_.Dist.dist (s : ℝ) (t : ℝ)) l (𝓝 (_root_.Dist.dist q (G t))) :=
    hdist.congr' (Eventually.of_forall fun s => hG.dist_eq s t)
  rw [tendsto_nhds_unique hdist'' hdist', Real.dist_eq,
    abs_of_nonneg (sub_nonneg.mpr t.property.2.le)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_completion_endpoint_of_isometry then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_completion_endpoint_of_isometry"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_completion_endpoint_of_isometry ``Submission.DifferentialGeometry.Geometry.exists_completion_endpoint_of_isometry


variable {X : Type*} [PseudoMetricSpace X]

private theorem dist_rescaled_segment
    {r : ℝ} (hr : 0 < r) (a : _root_.Set.Icc (0 : ℝ) 1 → X)
    (ha : ∀ s t, _root_.Dist.dist (a s) (a t) = r * _root_.Dist.dist s t)
    {s t : ℝ} (hs : s ∈ _root_.Set.Icc 0 r) (ht : t ∈ _root_.Set.Icc 0 r) :
    _root_.Dist.dist (a (_root_.Set.projIcc 0 1 zero_le_one (s / r)))
      (a (_root_.Set.projIcc 0 1 zero_le_one (t / r))) = |s - t| := by
  have hs' : s / r ∈ _root_.Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hs.1 hr.le, (div_le_one hr).mpr hs.2⟩
  have ht' : t / r ∈ _root_.Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg ht.1 hr.le, (div_le_one hr).mpr ht.2⟩
  rw [ha, Subtype.dist_eq, Real.dist_eq, _root_.Set.projIcc_of_mem zero_le_one hs', _root_.Set.projIcc_of_mem zero_le_one ht']
  rw [← sub_div, abs_div, abs_of_pos hr, mul_div_cancel₀ _ hr.ne']

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.dist_rescaled_segment
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.dist_rescaled_segment target :: scope.openDecls } }

theorem dist_lt_dist_add_dist_of_geodesic_avoidance
    {p x y : X} (hx : 0 < _root_.Dist.dist x p) (hy : 0 < _root_.Dist.dist y p)
    (a b : _root_.Set.Icc (0 : ℝ) 1 → X)
    (ha0 : a ⟨0, by norm_num⟩ = x) (ha1 : a ⟨1, by norm_num⟩ = p)
    (hb0 : b ⟨0, by norm_num⟩ = y) (hb1 : b ⟨1, by norm_num⟩ = p)
    (ha : ∀ s t, _root_.Dist.dist (a s) (a t) = _root_.Dist.dist x p * _root_.Dist.dist s t)
    (hb : ∀ s t, _root_.Dist.dist (b s) (b t) = _root_.Dist.dist y p * _root_.Dist.dist s t)
    (havoid : ∀ (gamma : ℝ → X) (u v w : ℝ), u < v → v < w →
      (∀ s ∈ _root_.Set.Icc u w, ∀ t ∈ _root_.Set.Icc u w, _root_.Dist.dist (gamma s) (gamma t) = |s - t|) →
      gamma v ≠ p) :
    dist x y < _root_.Dist.dist x p + _root_.Dist.dist p y := by
  classical
  by_contra hnot
  have heq : _root_.Dist.dist x y = _root_.Dist.dist x p + _root_.Dist.dist y p := by
    rw [dist_comm y p]
    exact le_antisymm (dist_triangle x p y) (not_lt.mp hnot)
  let r := _root_.Dist.dist x p
  let s := _root_.Dist.dist y p
  change 0 < r at hx
  change 0 < s at hy
  let A (t : ℝ) := a (_root_.Set.projIcc 0 1 zero_le_one (t / r))
  let B (t : ℝ) := b (_root_.Set.projIcc 0 1 zero_le_one (t / s))
  have hA0 : A 0 = x := by simpa only [A, zero_div, _root_.Set.projIcc_left] using ha0
  have hAr : A r = p := by simpa only [A, div_self hx.ne', _root_.Set.projIcc_right] using ha1
  have hB0 : B 0 = y := by simpa only [B, zero_div, _root_.Set.projIcc_left] using hb0
  have hBs : B s = p := by simpa only [B, div_self hy.ne', _root_.Set.projIcc_right] using hb1
  have hA (t : ℝ) (ht : t ∈ _root_.Set.Icc 0 r) (u : ℝ) (hu : u ∈ _root_.Set.Icc 0 r) :
      dist (A t) (A u) = |t - u| := dist_rescaled_segment hx a ha ht hu
  have hB (t : ℝ) (ht : t ∈ _root_.Set.Icc 0 s) (u : ℝ) (hu : u ∈ _root_.Set.Icc 0 s) :
      dist (B t) (B u) = |t - u| := dist_rescaled_segment hy b hb ht hu
  let gamma (t : ℝ) := if t ≤ r then A t else B (r + s - t)
  have hg0 : gamma 0 = x := by simpa only [gamma, if_pos hx.le] using hA0
  have hgend : gamma (r + s) = y := by
    have hgt : ¬ r + s ≤ r := by linarith only [hy]
    simpa only [gamma, if_neg hgt, sub_self] using hB0
  have hgr : gamma r = p := by simpa only [gamma, if_pos le_rfl] using hAr
  have hordered (t : ℝ) (ht : t ∈ _root_.Set.Icc 0 (r + s))
      (u : ℝ) (hu : u ∈ _root_.Set.Icc 0 (r + s)) (htu : t ≤ u) :
      dist (gamma t) (gamma u) ≤ u - t := by
    by_cases htr : t ≤ r
    · by_cases hur : u ≤ r
      · rw [show gamma t = A t from if_pos htr, show gamma u = A u from if_pos hur,
          hA t ⟨ht.1, htr⟩ u ⟨hu.1, hur⟩, abs_of_nonpos (sub_nonpos.mpr htu)]
        linarith only []
      · have hru : r ≤ u := (not_le.mp hur).le
        have harg : r + s - u ∈ _root_.Set.Icc (0 : ℝ) s :=
          ⟨sub_nonneg.mpr hu.2, by linarith only [hru]⟩
        have hleft := hA t ⟨ht.1, htr⟩ r ⟨hx.le, le_rfl⟩
        have hright := hB s ⟨hy.le, le_rfl⟩ (r + s - u) harg
        rw [hAr, abs_of_nonpos (sub_nonpos.mpr htr)] at hleft
        rw [hBs, abs_of_nonneg (by linarith only [hru] : 0 ≤ s - (r + s - u))] at hright
        have htri := dist_triangle (A t) p (B (r + s - u))
        rw [hleft, hright] at htri
        rw [show gamma t = A t from if_pos htr, show gamma u = B (r + s - u) from if_neg hur]
        linarith only [htri]
    · have hur : ¬ u ≤ r := fun h => htr (htu.trans h)
      have hrt : r ≤ t := (not_le.mp htr).le
      have hru : r ≤ u := (not_le.mp hur).le
      rw [show gamma t = B (r + s - t) from if_neg htr,
        show gamma u = B (r + s - u) from if_neg hur,
        hB (r + s - t) ⟨sub_nonneg.mpr ht.2, by linarith only [hrt]⟩
          (r + s - u) ⟨sub_nonneg.mpr hu.2, by linarith only [hru]⟩,
        abs_of_nonneg (by linarith only [htu] : 0 ≤ r + s - t - (r + s - u))]
      linarith only []
  have hLip : LipschitzOnWith 1 gamma (_root_.Set.Icc 0 (r + s)) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro t ht u hu
    simp only [NNReal.coe_one, one_mul, Real.dist_eq]
    rcases le_total t u with htu | hut
    · rw [abs_of_nonpos (sub_nonpos.mpr htu)]
      linarith only [hordered t ht u hu htu]
    · rw [dist_comm (gamma t), abs_of_nonneg (sub_nonneg.mpr hut)]
      exact hordered u hu t ht hut
  have hiso := isometry_Icc_of_lipschitzOnWith_of_dist_eq hLip
    (show _root_.Dist.dist (gamma 0) (gamma (r + s)) = r + s - 0 by rw [hg0, hgend, sub_zero]; exact heq)
  apply havoid gamma 0 r (r + s) hx (by linarith only [hy]) _ hgr
  intro t ht u hu
  exact hiso.dist_eq ⟨t, ht⟩ ⟨u, hu⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.dist_lt_dist_add_dist_of_geodesic_avoidance then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.dist_lt_dist_add_dist_of_geodesic_avoidance"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.dist_lt_dist_add_dist_of_geodesic_avoidance ``Submission.DifferentialGeometry.Geometry.dist_lt_dist_add_dist_of_geodesic_avoidance



end DifferentialGeometry.Geometry

open scoped _root_.ENNReal

namespace Isometry
open _root_.Isometry

variable {X : Type*} [PseudoEMetricSpace X] {a b : ℝ} (hab : a < b)
  {f : Ico a b → X}

open _root_.Isometry in
theorem not_tendsto_right_endpoint_of_edist_lt (hf : Isometry f) (x : X)
    (hbound : _root_.EDist.edist (f ⟨a, le_rfl, hab⟩) x < ENNReal.ofReal (b - a)) : ¬ _root_.Filter.Tendsto f (_root_.Filter.comap (Subtype.val : _root_.Set.Ico a b → ℝ) (𝓝 b)) (𝓝 x) := by
  let l := _root_.Filter.comap (Subtype.val : _root_.Set.Ico a b → ℝ) (𝓝 b)
  have hmap : _root_.Filter.NeBot (_root_.Filter.map (Subtype.val : _root_.Set.Ico a b → ℝ) l) := by
    change _root_.Filter.NeBot (_root_.Filter.map (Subtype.val : _root_.Set.Ico a b → ℝ)
      (_root_.Filter.comap (Subtype.val : _root_.Set.Ico a b → ℝ) (𝓝 b)))
    rw [_root_.Filter.map_comap_setCoe_val]
    exact right_nhdsWithin_Ico_neBot hab
  let _ : _root_.Filter.NeBot l := hmap.of_map
  intro ht
  have hdist : _root_.Filter.Tendsto (fun t : _root_.Set.Ico a b => _root_.EDist.edist (f ⟨a, le_rfl, hab⟩) (f t)) l
      (𝓝 (_root_.EDist.edist (f ⟨a, le_rfl, hab⟩) x)) :=
    tendsto_const_nhds.edist ht
  have hreal : _root_.Filter.Tendsto (fun t : _root_.Set.Ico a b => (t : ℝ) - a) l (𝓝 (b - a)) :=
    tendsto_comap.sub_const a
  have hdist' : _root_.Filter.Tendsto (fun t : _root_.Set.Ico a b => _root_.EDist.edist (f ⟨a, le_rfl, hab⟩) (f t)) l
      (𝓝 (ENNReal.ofReal (b - a))) := by
    have h := ENNReal.tendsto_ofReal hreal
    convert h using 1
    funext t
    rw [hf.edist_eq]
    change _root_.EDist.edist a (t : ℝ) = ENNReal.ofReal ((t : ℝ) - a)
    rw [edist_dist, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr t.property.1), neg_sub]
  exact hbound.ne (tendsto_nhds_unique hdist hdist')

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Isometry.not_tendsto_right_endpoint_of_edist_lt then
    throwError "Refusing to shadow existing declaration Isometry.not_tendsto_right_endpoint_of_edist_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `Isometry.not_tendsto_right_endpoint_of_edist_lt ``Submission.Isometry.not_tendsto_right_endpoint_of_edist_lt

end Isometry

namespace Isometry
open _root_.Isometry

variable {X : Type*} [PseudoEMetricSpace X] {a b : ℝ} (hab : a < b)
  {f : Ico a b → X}

open _root_.Isometry in
theorem tendsto_cocompact_right_endpoint_of_edist_lt (hf : Isometry f)
    (hbound : ∀ x : X, _root_.EDist.edist (f ⟨a, le_rfl, hab⟩) x < ENNReal.ofReal (b - a)) :
    Tendsto f (_root_.Filter.comap (Subtype.val : _root_.Set.Ico a b → ℝ) (𝓝 b)) (_root_.Filter.cocompact X) := by
  let l := _root_.Filter.comap (Subtype.val : _root_.Set.Ico a b → ℝ) (𝓝 b)
  have hdist : _root_.Filter.Tendsto (fun t : _root_.Set.Ico a b => _root_.EDist.edist (f ⟨a, le_rfl, hab⟩) (f t)) l
      (𝓝 (ENNReal.ofReal (b - a))) := by
    have h := ENNReal.tendsto_ofReal (tendsto_comap.sub_const a :
      _root_.Filter.Tendsto (fun t : _root_.Set.Ico a b => (t : ℝ) - a) l (𝓝 (b - a)))
    convert h using 1
    funext t
    rw [hf.edist_eq]
    change _root_.EDist.edist a (t : ℝ) = ENNReal.ofReal ((t : ℝ) - a)
    rw [edist_dist, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr t.property.1), neg_sub]
  intro S hS
  change ∀ᶠ t in l, f t ∈ S
  obtain ⟨K, hK, hKS⟩ := mem_cocompact.mp hS
  by_cases hne : K.Nonempty
  · obtain ⟨x, hx, hmax⟩ := hK.exists_isMaxOn hne
      ((continuous_const.edist continuous_id).continuousOn)
    filter_upwards [hdist.eventually (Ioi_mem_nhds (hbound x))] with t ht
    apply hKS
    intro hmem
    exact ht.not_ge (hmax hmem)
  · have hKempty : K = ∅ := not_nonempty_iff_eq_empty.mp hne
    exact Filter.Eventually.of_forall fun t => hKS (by simp [hKempty])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Isometry.tendsto_cocompact_right_endpoint_of_edist_lt then
    throwError "Refusing to shadow existing declaration Isometry.tendsto_cocompact_right_endpoint_of_edist_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `Isometry.tendsto_cocompact_right_endpoint_of_edist_lt ``Submission.Isometry.tendsto_cocompact_right_endpoint_of_edist_lt

end Isometry


namespace Isometry
open _root_.Isometry

variable {X : Type*} [PseudoMetricSpace X] {a b : ℝ} (hab : a < b)
  {f : Ico a b → X}

open _root_.Isometry in
theorem exists_completion_right_endpoint_not_mem_range (hf : Isometry f)
    (hbound : ∀ x : X, _root_.EDist.edist (f ⟨a, le_rfl, hab⟩) x < ENNReal.ofReal (b - a)) :
    ∃ q : UniformSpace.Completion X,
      _root_.Filter.Tendsto (fun t => (f t : UniformSpace.Completion X))
        (_root_.Filter.comap (Subtype.val : _root_.Set.Ico a b → ℝ) (𝓝 b)) (𝓝 q) ∧
      (∀ t : _root_.Set.Ico a b, _root_.Dist.dist q (f t : UniformSpace.Completion X) = b - t) ∧
      q ∉ _root_.Set.range (fun x : X => (x : UniformSpace.Completion X)) := by
  obtain ⟨q, hq, hd⟩ := DifferentialGeometry.Geometry.exists_completion_endpoint_of_isometry hab hf
  refine ⟨q, hq, hd, ?_⟩
  rintro ⟨x, hx⟩
  change (x : UniformSpace.Completion X) = q at hx
  have hfend : _root_.Filter.Tendsto f (_root_.Filter.comap (Subtype.val : _root_.Set.Ico a b → ℝ) (𝓝 b)) (𝓝 x) := by
    apply (UniformSpace.Completion.isUniformInducing_coe X).isInducing.tendsto_nhds_iff.mpr
    change _root_.Filter.Tendsto (fun t => (f t : UniformSpace.Completion X)) _ (𝓝 (x : UniformSpace.Completion X))
    rw [hx]
    exact hq
  exact hf.not_tendsto_right_endpoint_of_edist_lt hab x (hbound x) hfend

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Isometry.exists_completion_right_endpoint_not_mem_range then
    throwError "Refusing to shadow existing declaration Isometry.exists_completion_right_endpoint_not_mem_range"
  Lean.modifyEnv fun env => Lean.addAlias env `Isometry.exists_completion_right_endpoint_not_mem_range ``Submission.Isometry.exists_completion_right_endpoint_not_mem_range

end Isometry
