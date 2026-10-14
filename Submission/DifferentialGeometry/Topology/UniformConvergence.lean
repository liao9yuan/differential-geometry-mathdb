import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.UniformSpace.Compact
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Topology.UniformSpace.Pi

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.Filter _root_.Set

namespace TendstoUniformlyOn
open _root_.TendstoUniformlyOn

variable {A E N : Type*} [UniformSpace E]
  {K : Set A} {X : N → A → E} {v : A → E} {l : Filter N}

open _root_.TendstoUniformlyOn in
theorem eventually_mapsTo_of_isCompact_image
    (hX : TendstoUniformlyOn X v l K) (hK : IsCompact (v '' K))
    {U : Set E} (hU : IsOpen U) (hv : _root_.Set.MapsTo v K U) :
    ∀ᶠ n in l, _root_.Set.MapsTo (X n) K U := by
  obtain ⟨V, hV, _, hball⟩ := lebesgue_number_of_compact_open
    hK hU (mapsTo_iff_image_subset.mp hv)
  filter_upwards [hX V hV] with n hn z hz
  exact hball (v z) (_root_.Set.mem_image_of_mem v hz) (hn z hz)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `TendstoUniformlyOn.eventually_mapsTo_of_isCompact_image then
    throwError "Refusing to shadow existing declaration TendstoUniformlyOn.eventually_mapsTo_of_isCompact_image"
  Lean.modifyEnv fun env => Lean.addAlias env `TendstoUniformlyOn.eventually_mapsTo_of_isCompact_image ``Submission.TendstoUniformlyOn.eventually_mapsTo_of_isCompact_image

open _root_.TendstoUniformlyOn in
theorem eventually_mapsTo_of_isCompact [TopologicalSpace A]
    (hX : TendstoUniformlyOn X v l K) (hK : IsCompact K)
    (hv : ContinuousOn v K) {U : Set E} (hU : IsOpen U) (hmap : _root_.Set.MapsTo v K U) :
    ∀ᶠ n in l, _root_.Set.MapsTo (X n) K U :=
  hX.eventually_mapsTo_of_isCompact_image (hK.image_of_continuousOn hv) hU hmap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `TendstoUniformlyOn.eventually_mapsTo_of_isCompact then
    throwError "Refusing to shadow existing declaration TendstoUniformlyOn.eventually_mapsTo_of_isCompact"
  Lean.modifyEnv fun env => Lean.addAlias env `TendstoUniformlyOn.eventually_mapsTo_of_isCompact ``Submission.TendstoUniformlyOn.eventually_mapsTo_of_isCompact

open _root_.TendstoUniformlyOn in
theorem eventually_forall_mapsTo_of_isCompact_image
    {J : Type*} [Finite J] {xi : N → A → J → E} {f : A → J → E}
    (hxi : TendstoUniformlyOn xi f l K)
    (hK : ∀ j, IsCompact ((fun z => f z j) '' K))
    {U : J → Set E} (hU : ∀ j, IsOpen (U j))
    (hf : ∀ j, _root_.Set.MapsTo (fun z => f z j) K (U j)) :
    ∀ᶠ n in l, ∀ j, _root_.Set.MapsTo (fun z => xi n z j) K (U j) := by
  apply Filter.eventually_all.mpr
  intro j
  have hj : TendstoUniformlyOn (fun n z => xi n z j) (fun z => f z j) l K :=
    (Pi.uniformContinuous_proj (fun _ : J => E) j).comp_tendstoUniformlyOn hxi
  exact hj.eventually_mapsTo_of_isCompact_image (hK j) (hU j) (hf j)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `TendstoUniformlyOn.eventually_forall_mapsTo_of_isCompact_image then
    throwError "Refusing to shadow existing declaration TendstoUniformlyOn.eventually_forall_mapsTo_of_isCompact_image"
  Lean.modifyEnv fun env => Lean.addAlias env `TendstoUniformlyOn.eventually_forall_mapsTo_of_isCompact_image ``Submission.TendstoUniformlyOn.eventually_forall_mapsTo_of_isCompact_image

end TendstoUniformlyOn

namespace TendstoUniformlyOn
open _root_.TendstoUniformlyOn

variable {A E N J : Type*} [PseudoMetricSpace E] [Finite J]
  {K : Set A} {X : N → A → E} {v : A → E}
  {xi : N → A → J → E} {l : Filter N}

open _root_.TendstoUniformlyOn in
theorem eventually_forall_pair_mem_ball_of_isCompact_image
    (hX : TendstoUniformlyOn X v l K)
    (hxi : TendstoUniformlyOn xi (fun z _ => v z) l K)
    (hK : IsCompact (v '' K)) {a : E} {eps : ℝ}
    (hv : _root_.Set.MapsTo v K (Metric.ball a eps)) :
    ∀ᶠ n in l, ∀ z ∈ K, ∀ j,
      (X n z, xi n z j) ∈ Metric.ball (a, a) eps := by
  have hXmem := hX.eventually_mapsTo_of_isCompact_image hK Metric.isOpen_ball hv
  have hximem := hxi.eventually_forall_mapsTo_of_isCompact_image
    (fun _ => hK) (fun _ => Metric.isOpen_ball) (fun _ => hv)
  filter_upwards [hXmem, hximem] with n hn hxn z hz j
  rw [← ball_prod_same]
  exact ⟨hn hz, hxn j hz⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `TendstoUniformlyOn.eventually_forall_pair_mem_ball_of_isCompact_image then
    throwError "Refusing to shadow existing declaration TendstoUniformlyOn.eventually_forall_pair_mem_ball_of_isCompact_image"
  Lean.modifyEnv fun env => Lean.addAlias env `TendstoUniformlyOn.eventually_forall_pair_mem_ball_of_isCompact_image ``Submission.TendstoUniformlyOn.eventually_forall_pair_mem_ball_of_isCompact_image

open _root_.TendstoUniformlyOn in
theorem eventually_forall_pair_mem_ball_of_isCompact [TopologicalSpace A]
    (hX : TendstoUniformlyOn X v l K)
    (hxi : TendstoUniformlyOn xi (fun z _ => v z) l K)
    (hK : IsCompact K) (hvc : ContinuousOn v K) {a : E} {eps : ℝ}
    (hv : _root_.Set.MapsTo v K (Metric.ball a eps)) :
    ∀ᶠ n in l, ∀ z ∈ K, ∀ j,
      (X n z, xi n z j) ∈ Metric.ball (a, a) eps :=
  hX.eventually_forall_pair_mem_ball_of_isCompact_image hxi
    (hK.image_of_continuousOn hvc) hv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `TendstoUniformlyOn.eventually_forall_pair_mem_ball_of_isCompact then
    throwError "Refusing to shadow existing declaration TendstoUniformlyOn.eventually_forall_pair_mem_ball_of_isCompact"
  Lean.modifyEnv fun env => Lean.addAlias env `TendstoUniformlyOn.eventually_forall_pair_mem_ball_of_isCompact ``Submission.TendstoUniformlyOn.eventually_forall_pair_mem_ball_of_isCompact

end TendstoUniformlyOn

namespace DifferentialGeometry

theorem eventually_mapsTo_of_tendstoUniformly
    {X Y ι : Type*} [TopologicalSpace X] [UniformSpace Y]
    {A : Set X} {f : X → Y} {U : Set Y} {F : ι → X → Y} {p : Filter ι}
    (hconv : TendstoUniformly F f p) (hA : IsCompact A)
    (hf : ContinuousOn f A) (hU : IsOpen U) (hmap : _root_.Set.MapsTo f A U) :
    ∀ᶠ n in p, _root_.Set.MapsTo (F n) A U :=
  hconv.tendstoUniformlyOn.eventually_mapsTo_of_isCompact hA hf hU hmap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.eventually_mapsTo_of_tendstoUniformly then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.eventually_mapsTo_of_tendstoUniformly"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.eventually_mapsTo_of_tendstoUniformly ``Submission.DifferentialGeometry.eventually_mapsTo_of_tendstoUniformly

end DifferentialGeometry

open _root_.TendstoUniformlyOn in
theorem TendstoUniformlyOn.comp_tendstoUniformly
    {α β γ ι : Type*} [UniformSpace β] [UniformSpace γ]
    {l : Filter ι} {s : Set β} {F : ι → β → γ} {f : β → γ}
    {u : ι → α → β} {v : α → β}
    (hF : TendstoUniformlyOn F f l s) (hf : UniformContinuousOn f s)
    (hu : TendstoUniformly u v l)
    (hus : ∀ᶠ i in l, ∀ x, u i x ∈ s) (hvs : ∀ x, v x ∈ s) :
    TendstoUniformly (fun i x => F i (u i x)) (fun x => f (v x)) l := by
  have hcomp := hf.comp_tendstoUniformly_eventually hus hvs hu
  intro V hV
  obtain ⟨W, hW, hWV⟩ := comp_mem_uniformity_sets hV
  filter_upwards [hF W hW, hcomp W hW, hus] with i hi hci hsi
  intro x
  exact hWV (SetRel.prodMk_mem_comp (hci x) (hi _ (hsi x)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `TendstoUniformlyOn.comp_tendstoUniformly then
    throwError "Refusing to shadow existing declaration TendstoUniformlyOn.comp_tendstoUniformly"
  Lean.modifyEnv fun env => Lean.addAlias env `TendstoUniformlyOn.comp_tendstoUniformly ``Submission.TendstoUniformlyOn.comp_tendstoUniformly

noncomputable section
open scoped _root_.Topology

open _root_.Topology _root_.Topology.IsClosedEmbedding in
theorem Topology.IsClosedEmbedding.exists_continuousMap_of_tendstoUniformly
    {X M F ι : Type*} [TopologicalSpace X] [TopologicalSpace M]
    [UniformSpace F] {f : M → F} (hf : _root_.Topology.IsClosedEmbedding f)
    {Y : ι → X → M} {YT : X → F} {l : Filter ι}
    (hlim : TendstoUniformly (fun i x => f (Y i x)) YT l)
    (hcont : ∃ᶠ i in l, Continuous (Y i)) :
    ∃ yT : C(X, M), (∀ x, f (yT x) = YT x) ∧
      ∀ x, _root_.Filter.Tendsto (fun i => Y i x) l (𝓝 (yT x)) := by
  let _ : _root_.Filter.NeBot l := (_root_.Filter.frequently_true_iff_neBot l).mp
    (hcont.mono fun _ _ => trivial)
  have hrange : ∀ x, YT x ∈ _root_.Set.range f := by
    intro x
    exact hf.isClosed_range.mem_of_tendsto (hlim.tendsto_at x)
      (Eventually.of_forall fun i => _root_.Set.mem_range_self (Y i x))
  choose yT hyT using hrange
  have hcontinuous : Continuous YT :=
    hlim.continuous (hcont.mono fun i hi => hf.continuous.comp hi)
  have hycontinuous : Continuous yT := hf.isEmbedding.continuous_iff.mpr
    (hcontinuous.congr fun x => (hyT x).symm)
  refine ⟨⟨yT, hycontinuous⟩, hyT, ?_⟩
  intro x
  apply hf.isEmbedding.isInducing.tendsto_nhds_iff.mpr
  change _root_.Filter.Tendsto (fun i => f (Y i x)) l (𝓝 (f (yT x)))
  rw [hyT x]
  exact hlim.tendsto_at x

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.Topology
  Lean.modifyEnv fun env => env.registerNamespace `Submission.Topology.IsClosedEmbedding
  let env ← Lean.getEnv
  if env.contains `Topology.IsClosedEmbedding.exists_continuousMap_of_tendstoUniformly then
    throwError "Refusing to shadow existing declaration Topology.IsClosedEmbedding.exists_continuousMap_of_tendstoUniformly"
  Lean.modifyEnv fun env => Lean.addAlias env `Topology.IsClosedEmbedding.exists_continuousMap_of_tendstoUniformly ``Submission.Topology.IsClosedEmbedding.exists_continuousMap_of_tendstoUniformly

end

open _root_.TendstoUniformlyOn in
theorem TendstoUniformlyOn.comp_of_eventually_mapsTo
    {α β γ ι : Type*} [UniformSpace β] [UniformSpace γ]
    {l : Filter ι} {K : Set α} {L : Set β}
    {A : ι → β → γ} {Ainf : β → γ} {B : ι → α → β} {Binf : α → β}
    (hA : TendstoUniformlyOn A Ainf l L)
    (hAinf : UniformContinuousOn Ainf L)
    (hB : TendstoUniformlyOn B Binf l K)
    (hmap : ∀ᶠ k in l, _root_.Set.MapsTo (B k) K L)
    (hmapInf : _root_.Set.MapsTo Binf K L) :
    TendstoUniformlyOn (fun k x => A k (B k x)) (fun x => Ainf (Binf x)) l K := by
  rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe] at hB ⊢
  apply hA.comp_tendstoUniformly hAinf hB
  · filter_upwards [hmap] with k hk x
    exact hk x.property
  · intro x
    exact hmapInf x.property

run_cmd do
  let env ← Lean.getEnv
  if env.contains `TendstoUniformlyOn.comp_of_eventually_mapsTo then
    throwError "Refusing to shadow existing declaration TendstoUniformlyOn.comp_of_eventually_mapsTo"
  Lean.modifyEnv fun env => Lean.addAlias env `TendstoUniformlyOn.comp_of_eventually_mapsTo ``Submission.TendstoUniformlyOn.comp_of_eventually_mapsTo

namespace TendstoUniformlyOn
open _root_.TendstoUniformlyOn

variable {A E N : Type*} [UniformSpace E] [LocallyCompactSpace E]
  {K : Set A} {X : N → A → E} {v : A → E} {l : Filter N}

open _root_.TendstoUniformlyOn in
theorem exists_isCompact_eventually_mapsTo_of_isCompact_image
    (hX : TendstoUniformlyOn X v l K) (hK : IsCompact (v '' K))
    {U : Set E} (hU : IsOpen U) (hv : _root_.Set.MapsTo v K U) :
    ∃ L : Set E, IsCompact L ∧ L ⊆ U ∧ _root_.Set.MapsTo v K (interior L) ∧
      ∀ᶠ n in l, _root_.Set.MapsTo (X n) K L := by
  obtain ⟨L, hL, hKL, hLU⟩ :=
    exists_compact_between hK hU (mapsTo_iff_image_subset.mp hv)
  have hvL : _root_.Set.MapsTo v K (interior L) := mapsTo_iff_image_subset.mpr hKL
  refine ⟨L, hL, hLU, hvL, ?_⟩
  exact (hX.eventually_mapsTo_of_isCompact_image hK isOpen_interior hvL).mono
    fun n hn x hx => interior_subset (hn hx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `TendstoUniformlyOn.exists_isCompact_eventually_mapsTo_of_isCompact_image then
    throwError "Refusing to shadow existing declaration TendstoUniformlyOn.exists_isCompact_eventually_mapsTo_of_isCompact_image"
  Lean.modifyEnv fun env => Lean.addAlias env `TendstoUniformlyOn.exists_isCompact_eventually_mapsTo_of_isCompact_image ``Submission.TendstoUniformlyOn.exists_isCompact_eventually_mapsTo_of_isCompact_image

open _root_.TendstoUniformlyOn in
theorem exists_isCompact_eventually_mapsTo_of_isCompact [TopologicalSpace A]
    (hX : TendstoUniformlyOn X v l K) (hK : IsCompact K)
    (hv : ContinuousOn v K) {U : Set E} (hU : IsOpen U) (hmap : _root_.Set.MapsTo v K U) :
    ∃ L : Set E, IsCompact L ∧ L ⊆ U ∧ _root_.Set.MapsTo v K (interior L) ∧
      ∀ᶠ n in l, _root_.Set.MapsTo (X n) K L :=
  hX.exists_isCompact_eventually_mapsTo_of_isCompact_image
    (hK.image_of_continuousOn hv) hU hmap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `TendstoUniformlyOn.exists_isCompact_eventually_mapsTo_of_isCompact then
    throwError "Refusing to shadow existing declaration TendstoUniformlyOn.exists_isCompact_eventually_mapsTo_of_isCompact"
  Lean.modifyEnv fun env => Lean.addAlias env `TendstoUniformlyOn.exists_isCompact_eventually_mapsTo_of_isCompact ``Submission.TendstoUniformlyOn.exists_isCompact_eventually_mapsTo_of_isCompact

end TendstoUniformlyOn

namespace TendstoUniformly
open _root_.TendstoUniformly

variable {A E N : Type*} [TopologicalSpace A] [CompactSpace A]
  [UniformSpace E] [LocallyCompactSpace E]
  {X : N → A → E} {v : A → E} {l : Filter N}

open _root_.TendstoUniformly in
theorem exists_isCompact_eventually_range_subset
    (hX : TendstoUniformly X v l) (hv : Continuous v)
    {U : Set E} (hU : IsOpen U) (hmap : _root_.Set.range v ⊆ U) :
    ∃ L : Set E, IsCompact L ∧ L ⊆ U ∧ _root_.Set.range v ⊆ interior L ∧
      ∀ᶠ n in l, _root_.Set.range (X n) ⊆ L := by
  have hvU : _root_.Set.MapsTo v _root_.Set.univ U := fun x _ => hmap (_root_.Set.mem_range_self x)
  obtain ⟨L, hL, hLU, hvL, hXL⟩ :=
    hX.tendstoUniformlyOn.exists_isCompact_eventually_mapsTo_of_isCompact
      isCompact_univ hv.continuousOn hU hvU
  refine ⟨L, hL, hLU, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact hvL (_root_.Set.mem_univ x)
  · filter_upwards [hXL] with n hn
    rintro _ ⟨x, rfl⟩
    exact hn (_root_.Set.mem_univ x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `TendstoUniformly.exists_isCompact_eventually_range_subset then
    throwError "Refusing to shadow existing declaration TendstoUniformly.exists_isCompact_eventually_range_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `TendstoUniformly.exists_isCompact_eventually_range_subset ``Submission.TendstoUniformly.exists_isCompact_eventually_range_subset

end TendstoUniformly

namespace DifferentialGeometry.Analysis

open scoped _root_.Topology _root_.Submission.Topology

theorem exists_tendstoUniformlyOn_of_dist_le_dist
    {J X F Y : Type*} [PseudoMetricSpace F] [CompleteSpace F] [PseudoMetricSpace Y]
    {l : Filter J} [_root_.Filter.NeBot l] {U : Set X} (f : J → X → F) (m : J → Y)
    {y : Y} (hm : _root_.Filter.Tendsto m l (𝓝 y))
    (hbound : ∀ᶠ st : J × J in l ×ˢ l, ∀ x ∈ U,
      _root_.Dist.dist (f st.1 x) (f st.2 x) ≤ _root_.Dist.dist (m st.1) (m st.2)) :
    ∃ g : X → F, TendstoUniformlyOn f g l U := by
  classical
  have hmod : _root_.Filter.Tendsto (fun st : J × J => _root_.Dist.dist (m st.1) (m st.2))
      (l ×ˢ l) (𝓝 0) := by
    simpa only [dist_self, Function.comp_def] using (hm.comp _root_.Filter.tendsto_fst).dist (hm.comp _root_.Filter.tendsto_snd)
  have huc : UniformCauchySeqOn f l U := by
    intro V hV
    obtain ⟨ε, hε, hεV⟩ := Metric.mem_uniformity_dist.mp hV
    filter_upwards [hbound, hmod.eventually_lt_const hε] with st hst hsmall x hx
    exact hεV ((hst x hx).trans_lt hsmall)
  have hex : ∀ x : X, ∃ z : F, x ∈ U → _root_.Filter.Tendsto (fun t => f t x) l (𝓝 z) := by
    intro x
    by_cases hx : x ∈ U
    · obtain ⟨z, hz⟩ := cauchy_map_iff_exists_tendsto.mp (huc.cauchy_map hx)
      exact ⟨z, fun _ => hz⟩
    · obtain ⟨i⟩ := _root_.Filter.nonempty_of_neBot l
      exact ⟨f i x, fun hx' => False.elim (hx hx')⟩
  choose g hg using hex
  exact ⟨g, huc.tendstoUniformlyOn_of_tendsto hg⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.exists_tendstoUniformlyOn_of_dist_le_dist then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.exists_tendstoUniformlyOn_of_dist_le_dist"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.exists_tendstoUniformlyOn_of_dist_le_dist ``Submission.DifferentialGeometry.Analysis.exists_tendstoUniformlyOn_of_dist_le_dist

theorem exists_tendstoUniformlyOn_left_endpoint_of_time_modulus
    {X F : Type*} [PseudoMetricSpace F] [CompleteSpace F]
    {a b : ℝ} (hab : a < b) {U : Set X} (f : ℝ → X → F) (m : ℝ → ℝ)
    {c : ℝ} (hm : _root_.Filter.Tendsto m (𝓝[_root_.Set.Ioo a b] a) (𝓝 c))
    (hbound : ∀ s ∈ _root_.Set.Ioo a b, ∀ t ∈ _root_.Set.Ioo a b, ∀ x ∈ U,
      _root_.Dist.dist (f s x) (f t x) ≤ |m s - m t|) :
    ∃ g : X → F, TendstoUniformlyOn f g (𝓝[_root_.Set.Ioo a b] a) U := by
  let : _root_.Filter.NeBot (𝓝[_root_.Set.Ioo a b] a) := left_nhdsWithin_Ioo_neBot hab
  apply exists_tendstoUniformlyOn_of_dist_le_dist f m hm
  have hmem : ∀ᶠ st : ℝ × ℝ in (𝓝[_root_.Set.Ioo a b] a) ×ˢ (𝓝[_root_.Set.Ioo a b] a),
      st.1 ∈ _root_.Set.Ioo a b ∧ st.2 ∈ _root_.Set.Ioo a b :=
    (tendsto_fst.eventually eventually_mem_nhdsWithin).and
      (tendsto_snd.eventually eventually_mem_nhdsWithin)
  filter_upwards [hmem] with st hst x hx
  simpa only [Real.dist_eq] using hbound st.1 hst.1 st.2 hst.2 x hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.exists_tendstoUniformlyOn_left_endpoint_of_time_modulus then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.exists_tendstoUniformlyOn_left_endpoint_of_time_modulus"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.exists_tendstoUniformlyOn_left_endpoint_of_time_modulus ``Submission.DifferentialGeometry.Analysis.exists_tendstoUniformlyOn_left_endpoint_of_time_modulus

end DifferentialGeometry.Analysis
