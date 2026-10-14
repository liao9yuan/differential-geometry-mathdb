import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.SpecificCodomains.Pi

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.Filter _root_.MeasureTheory _root_.Set
open scoped _root_.Interval _root_.Topology

namespace AbsolutelyContinuousOnInterval
open _root_.AbsolutelyContinuousOnInterval

variable {X : Type*} [PseudoMetricSpace X]

theorem _root_.Submission.uniformContinuousOn_of_absolutelyContinuousOnInterval
    {f : ℝ → X} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b) :
    UniformContinuousOn f (_root_.Set.uIcc a b) := by
  simp only [UniformContinuousOn, Filter.tendsto_iff_comap, _root_.AbsolutelyContinuousOnInterval.uniformity_eq_comap_totalLengthFilter]
  simp only [AbsolutelyContinuousOnInterval, Filter.tendsto_iff_comap] at hf
  convert! Filter.comap_mono hf
  · simp only [_root_.Filter.comap_inf, _root_.Filter.comap_principal]
    congr
    ext p
    simp only [_root_.AbsolutelyContinuousOnInterval.disjWithin, Finset.mem_range, _root_.Set.preimage_ofPred_eq, Nat.lt_one_iff,
      forall_eq, _root_.Set.mem_ofPred_eq, _root_.Set.mem_prod]
    simp
  · simp [_root_.AbsolutelyContinuousOnInterval.totalLengthFilter, _root_.Filter.comap_comap, Function.comp_def]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `uniformContinuousOn_of_absolutelyContinuousOnInterval then
    throwError "Refusing to shadow existing declaration uniformContinuousOn_of_absolutelyContinuousOnInterval"
  Lean.modifyEnv fun env => Lean.addAlias env `uniformContinuousOn_of_absolutelyContinuousOnInterval ``Submission.uniformContinuousOn_of_absolutelyContinuousOnInterval

open _root_.AbsolutelyContinuousOnInterval in
theorem piecewise_Iic {f g : ℝ → X} {a b c : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c)
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : AbsolutelyContinuousOnInterval g b c)
    (hfg : f b = g b) :
    AbsolutelyContinuousOnInterval (Set.piecewise (Set.Iic b) f g) a c := by
  classical
  rw [absolutelyContinuousOnInterval_iff] at hf hg ⊢
  intro ε hε
  obtain ⟨δf, hδf, hf⟩ := hf (ε / 2) (half_pos hε)
  obtain ⟨δg, hδg, hg⟩ := hg (ε / 2) (half_pos hε)
  refine ⟨min δf δg, lt_min hδf hδg, ?_⟩
  rintro ⟨n, p⟩ hp hpLen
  change
    (∀ i ∈ Finset.range n, (p i).1 ∈ _root_.Set.uIcc a c ∧ (p i).2 ∈ _root_.Set.uIcc a c) ∧
      Set.PairwiseDisjoint (Finset.range n) (fun i ↦ _root_.Set.uIoc (p i).1 (p i).2) at hp
  rcases hp with ⟨hpEnds, hpDisj⟩
  have hleft_subset (x y : ℝ) :
      uIoc (_root_.Min.min x b) (_root_.Min.min y b) ⊆ _root_.Set.uIoc x y := by
    simp only [_root_.Set.uIoc]
    grind
  have hright_subset (x y : ℝ) :
      uIoc (_root_.Max.max x b) (_root_.Max.max y b) ⊆ _root_.Set.uIoc x y := by
    simp only [_root_.Set.uIoc]
    grind
  have hpLeft :
      (n, fun i ↦ (_root_.Min.min (p i).1 b, _root_.Min.min (p i).2 b)) ∈ _root_.AbsolutelyContinuousOnInterval.disjWithin a b := by
    refine ⟨?_, hpDisj.mono (fun i ↦ hleft_subset (p i).1 (p i).2)⟩
    intro i hi
    have hiEnds := hpEnds i hi
    rw [_root_.Set.uIcc_of_le (hab.trans hbc)] at hiEnds
    rw [_root_.Set.uIcc_of_le hab]
    exact ⟨⟨le_min hiEnds.1.1 hab, min_le_right _ _⟩,
      ⟨le_min hiEnds.2.1 hab, min_le_right _ _⟩⟩
  have hpRight :
      (n, fun i ↦ (_root_.Max.max (p i).1 b, _root_.Max.max (p i).2 b)) ∈ _root_.AbsolutelyContinuousOnInterval.disjWithin b c := by
    refine ⟨?_, hpDisj.mono (fun i ↦ hright_subset (p i).1 (p i).2)⟩
    intro i hi
    have hiEnds := hpEnds i hi
    rw [_root_.Set.uIcc_of_le (hab.trans hbc)] at hiEnds
    rw [_root_.Set.uIcc_of_le hbc]
    exact ⟨⟨le_max_right _ _, max_le hiEnds.1.2 hbc⟩,
      ⟨le_max_right _ _, max_le hiEnds.2.2 hbc⟩⟩
  have hleftLen :
      ∑ i ∈ Finset.range n, _root_.Dist.dist (_root_.Min.min (p i).1 b) (_root_.Min.min (p i).2 b) < δf := by
    refine lt_of_le_of_lt (Finset.sum_le_sum fun i _ ↦ ?_) (hpLen.trans_le (min_le_left _ _))
    simpa using (LipschitzWith.id.min_const b).dist_le_mul (p i).1 (p i).2
  have hrightLen :
      ∑ i ∈ Finset.range n, _root_.Dist.dist (_root_.Max.max (p i).1 b) (_root_.Max.max (p i).2 b) < δg := by
    refine lt_of_le_of_lt (Finset.sum_le_sum fun i _ ↦ ?_) (hpLen.trans_le (min_le_right _ _))
    simpa using (LipschitzWith.id.max_const b).dist_le_mul (p i).1 (p i).2
  have hfSum := hf (n, fun i ↦ (_root_.Min.min (p i).1 b, _root_.Min.min (p i).2 b)) hpLeft hleftLen
  have hgSum := hg (n, fun i ↦ (_root_.Max.max (p i).1 b, _root_.Max.max (p i).2 b)) hpRight hrightLen
  have hdist (x y : ℝ) :
      _root_.Dist.dist (Set.piecewise (Set.Iic b) f g x)
          (Set.piecewise (Set.Iic b) f g y) ≤
        _root_.Dist.dist (f (_root_.Min.min x b)) (f (_root_.Min.min y b)) +
          dist (g (_root_.Max.max x b)) (g (_root_.Max.max y b)) := by
    by_cases hx : x ≤ b <;> by_cases hy : y ≤ b
    · simp [Set.piecewise, hx, hy]
    · have hby : b ≤ y := le_of_not_ge hy
      simpa [Set.piecewise, hx, hy, min_eq_left, min_eq_right hby,
        max_eq_right, max_eq_left hby, hfg] using dist_triangle (f x) (f b) (g y)
    · have hbx : b ≤ x := le_of_not_ge hx
      simpa [Set.piecewise, hx, hy, min_eq_right hbx, min_eq_left,
        max_eq_left hbx, max_eq_right, hfg, add_comm] using
        dist_triangle (g x) (g b) (f y)
    · have hbx : b ≤ x := le_of_not_ge hx
      have hby : b ≤ y := le_of_not_ge hy
      simp [Set.piecewise, hx, hy, min_eq_right hbx, min_eq_right hby,
        max_eq_left hbx, max_eq_left hby]
  calc
    ∑ i ∈ Finset.range n,
        _root_.Dist.dist (Set.piecewise (Set.Iic b) f g (p i).1)
          (Set.piecewise (Set.Iic b) f g (p i).2) ≤
        ∑ i ∈ Finset.range n,
          (_root_.Dist.dist (f (_root_.Min.min (p i).1 b)) (f (_root_.Min.min (p i).2 b)) +
            dist (g (_root_.Max.max (p i).1 b)) (g (_root_.Max.max (p i).2 b))) :=
      Finset.sum_le_sum fun i _ ↦ hdist (p i).1 (p i).2
    _ =
        (∑ i ∈ Finset.range n,
          _root_.Dist.dist (f (_root_.Min.min (p i).1 b)) (f (_root_.Min.min (p i).2 b))) +
        ∑ i ∈ Finset.range n,
          dist (g (_root_.Max.max (p i).1 b)) (g (_root_.Max.max (p i).2 b)) := by
      rw [Finset.sum_add_distrib]
    _ < ε / 2 + ε / 2 := add_lt_add hfSum hgSum
    _ = ε := by ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AbsolutelyContinuousOnInterval.piecewise_Iic then
    throwError "Refusing to shadow existing declaration AbsolutelyContinuousOnInterval.piecewise_Iic"
  Lean.modifyEnv fun env => Lean.addAlias env `AbsolutelyContinuousOnInterval.piecewise_Iic ``Submission.AbsolutelyContinuousOnInterval.piecewise_Iic

open _root_.AbsolutelyContinuousOnInterval in
theorem congr {f g : ℝ → X} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hfg : _root_.Set.EqOn f g (_root_.Set.uIcc a b)) :
    AbsolutelyContinuousOnInterval g a b := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro ε hε
  obtain ⟨δ, hδ, hf⟩ := hf ε hε
  refine ⟨δ, hδ, ?_⟩
  intro p hp hpLen
  have hpEnds := hp.1
  convert hf p hp hpLen using 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [← hfg (hpEnds i hi).1, ← hfg (hpEnds i hi).2]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AbsolutelyContinuousOnInterval.congr then
    throwError "Refusing to shadow existing declaration AbsolutelyContinuousOnInterval.congr"
  Lean.modifyEnv fun env => Lean.addAlias env `AbsolutelyContinuousOnInterval.congr ``Submission.AbsolutelyContinuousOnInterval.congr

open _root_.LipschitzOnWith in
theorem _root_.Submission.LipschitzOnWith.comp_absolutelyContinuousOnInterval
    {Y : Type*} [PseudoMetricSpace Y]
    {f : X → Y} {g : ℝ → X} {s : Set X} {K : NNReal} {a b : ℝ}
    (hf : LipschitzOnWith K f s)
    (hg : AbsolutelyContinuousOnInterval g a b)
    (hgs : _root_.Set.MapsTo g (_root_.Set.uIcc a b) s) :
    AbsolutelyContinuousOnInterval (f ∘ g) a b := by
  rw [absolutelyContinuousOnInterval_iff] at hg ⊢
  intro ε hε
  obtain ⟨δ, hδ, hg⟩ := hg (ε / (K + 1)) (by positivity)
  refine ⟨δ, hδ, ?_⟩
  intro p hp hpLen
  have hgSum := hg p hp hpLen
  have hpEnds := hp.1
  calc
    ∑ i ∈ Finset.range p.1,
        _root_.Dist.dist ((f ∘ g) (p.2 i).1) ((f ∘ g) (p.2 i).2) ≤
        ∑ i ∈ Finset.range p.1,
          K * _root_.Dist.dist (g (p.2 i).1) (g (p.2 i).2) := by
      apply Finset.sum_le_sum
      intro i hi
      have hle := hf
        (hgs (hpEnds i hi).1) (hgs (hpEnds i hi).2)
      apply ENNReal.toReal_mono
        (ENNReal.mul_ne_top ENNReal.coe_ne_top (edist_ne_top _ _)) at hle
      simpa only [Function.comp_apply, ENNReal.toReal_mul, ENNReal.coe_toReal,
        ← dist_edist] using hle
    _ = K * ∑ i ∈ Finset.range p.1,
        dist (g (p.2 i).1) (g (p.2 i).2) := by
      rw [Finset.mul_sum]
    _ ≤ K * (ε / (K + 1)) := by
      gcongr
    _ < (K + 1) * (ε / (K + 1)) := by
      gcongr
      linarith
    _ = ε := by field

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.LipschitzOnWith
  let env ← Lean.getEnv
  if env.contains `LipschitzOnWith.comp_absolutelyContinuousOnInterval then
    throwError "Refusing to shadow existing declaration LipschitzOnWith.comp_absolutelyContinuousOnInterval"
  Lean.modifyEnv fun env => Lean.addAlias env `LipschitzOnWith.comp_absolutelyContinuousOnInterval ``Submission.LipschitzOnWith.comp_absolutelyContinuousOnInterval

open _root_.AbsolutelyContinuousOnInterval in
theorem comp_monotone_lipschitzOn
    {f : ℝ → X} {g : ℝ → ℝ} {a b c d : ℝ} {K : NNReal}
    (hf : AbsolutelyContinuousOnInterval f c d)
    (hg : LipschitzOnWith K g (_root_.Set.uIcc a b))
    (hmono : MonotoneOn g (_root_.Set.uIcc a b))
    (hmap : _root_.Set.MapsTo g (_root_.Set.uIcc a b) (_root_.Set.uIcc c d)) :
    AbsolutelyContinuousOnInterval (f ∘ g) a b := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro ε hε
  obtain ⟨δ, hδ, hf⟩ := hf ε hε
  refine ⟨δ / (K + 1), by positivity, ?_⟩
  rintro ⟨n, p⟩ hp hpLen
  let q : ℕ → ℝ × ℝ := fun i ↦ (g (p i).1, g (p i).2)
  have hmin_mem {x y : ℝ} (hx : x ∈ _root_.Set.uIcc a b) (hy : y ∈ _root_.Set.uIcc a b) :
      min x y ∈ _root_.Set.uIcc a b := by
    rw [_root_.Set.uIcc] at hx hy ⊢
    exact ⟨le_min hx.1 hy.1, (min_le_left x y).trans hx.2⟩
  have hmax_mem {x y : ℝ} (hx : x ∈ _root_.Set.uIcc a b) (hy : y ∈ _root_.Set.uIcc a b) :
      max x y ∈ _root_.Set.uIcc a b := by
    rw [_root_.Set.uIcc] at hx hy ⊢
    exact ⟨hx.1.trans (le_max_left x y), max_le hx.2 hy.2⟩
  have hmin_map {x y : ℝ} (hx : x ∈ _root_.Set.uIcc a b) (hy : y ∈ _root_.Set.uIcc a b) :
      g (_root_.Min.min x y) = _root_.Min.min (g x) (g y) := by
    rcases le_total x y with hxy | hyx
    · rw [min_eq_left hxy, min_eq_left (hmono hx hy hxy)]
    · rw [min_eq_right hyx, min_eq_right (hmono hy hx hyx)]
  have hmax_map {x y : ℝ} (hx : x ∈ _root_.Set.uIcc a b) (hy : y ∈ _root_.Set.uIcc a b) :
      g (_root_.Max.max x y) = _root_.Max.max (g x) (g y) := by
    rcases le_total x y with hxy | hyx
    · rw [max_eq_right hxy, max_eq_right (hmono hx hy hxy)]
    · rw [max_eq_left hyx, max_eq_left (hmono hy hx hyx)]
  have hq : (n, q) ∈ _root_.AbsolutelyContinuousOnInterval.disjWithin c d := by
    refine ⟨?_, ?_⟩
    · intro i hi
      exact ⟨hmap (hp.1 i hi).1, hmap (hp.1 i hi).2⟩
    · intro i hi j hj hij
      have hdisj := hp.2 hi hj hij
      simp only [_root_.Set.uIoc, Set.Ioc_disjoint_Ioc] at hdisj ⊢
      have hiMin := hmin_mem (hp.1 i hi).1 (hp.1 i hi).2
      have hiMax := hmax_mem (hp.1 i hi).1 (hp.1 i hi).2
      have hjMin := hmin_mem (hp.1 j hj).1 (hp.1 j hj).2
      have hjMax := hmax_mem (hp.1 j hj).1 (hp.1 j hj).2
      have hleft := hmin_mem hiMax hjMax
      have hright := hmax_mem hiMin hjMin
      have horder := hmono hleft hright hdisj
      rw [hmin_map hiMax hjMax, hmax_map hiMin hjMin,
        hmax_map (hp.1 i hi).1 (hp.1 i hi).2,
        hmax_map (hp.1 j hj).1 (hp.1 j hj).2,
        hmin_map (hp.1 i hi).1 (hp.1 i hi).2,
        hmin_map (hp.1 j hj).1 (hp.1 j hj).2] at horder
      exact horder
  apply hf (n, q) hq
  calc
    ∑ i ∈ Finset.range n, _root_.Dist.dist (q i).1 (q i).2 ≤
        ∑ i ∈ Finset.range n, K * _root_.Dist.dist (p i).1 (p i).2 := by
      apply Finset.sum_le_sum
      intro i hi
      have hle := hg (hp.1 i hi).1 (hp.1 i hi).2
      apply ENNReal.toReal_mono
        (ENNReal.mul_ne_top ENNReal.coe_ne_top (edist_ne_top _ _)) at hle
      simpa only [q, ENNReal.toReal_mul, ENNReal.coe_toReal, ← dist_edist] using hle
    _ = K * ∑ i ∈ Finset.range n, _root_.Dist.dist (p i).1 (p i).2 := by
      rw [Finset.mul_sum]
    _ ≤ K * (δ / (K + 1)) := by
      gcongr
    _ < (K + 1) * (δ / (K + 1)) := by
      gcongr
      linarith
    _ = δ := by field

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AbsolutelyContinuousOnInterval.comp_monotone_lipschitzOn then
    throwError "Refusing to shadow existing declaration AbsolutelyContinuousOnInterval.comp_monotone_lipschitzOn"
  Lean.modifyEnv fun env => Lean.addAlias env `AbsolutelyContinuousOnInterval.comp_monotone_lipschitzOn ``Submission.AbsolutelyContinuousOnInterval.comp_monotone_lipschitzOn

open _root_.AbsolutelyContinuousOnInterval in
theorem comp_sq
    {f : ℝ → X} {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hf : AbsolutelyContinuousOnInterval f (a ^ 2) (b ^ 2)) :
    AbsolutelyContinuousOnInterval (f ∘ fun s : ℝ ↦ s ^ 2) a b := by
  obtain ⟨K, hK⟩ :=
    (contDiff_id.pow 2).contDiffOn.exists_lipschitzOnWith
      one_ne_zero (convex_Icc a b) _root_.CompactIccSpace.isCompact_Icc
  apply comp_monotone_lipschitzOn hf (by simpa only [_root_.Set.uIcc_of_le hab, id_eq] using hK)
  · intro x hx y hy hxy
    rw [_root_.Set.uIcc_of_le hab] at hx hy
    exact (sq_le_sq₀ (ha.trans hx.1) (ha.trans hy.1)).2 hxy
  · intro s hs
    rw [_root_.Set.uIcc_of_le hab] at hs
    have hs0 : 0 ≤ s := ha.trans hs.1
    rw [_root_.Set.uIcc_of_le ((sq_le_sq₀ ha (ha.trans hab)).2 hab)]
    exact ⟨(sq_le_sq₀ ha hs0).2 hs.1,
      (sq_le_sq₀ hs0 (ha.trans hab)).2 hs.2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AbsolutelyContinuousOnInterval.comp_sq then
    throwError "Refusing to shadow existing declaration AbsolutelyContinuousOnInterval.comp_sq"
  Lean.modifyEnv fun env => Lean.addAlias env `AbsolutelyContinuousOnInterval.comp_sq ``Submission.AbsolutelyContinuousOnInterval.comp_sq

section Vector

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {f : ℝ → E} {a b : ℝ}

open _root_.AbsolutelyContinuousOnInterval in
private theorem ae_deriv_comp_continuousLinearMap
    (hf : AbsolutelyContinuousOnInterval f a b) (L : E →L[ℝ] ℝ) :
    deriv (L ∘ f) =ᵐ[volume.restrict (Ι a b)] fun t ↦ L (deriv f t) := by
  change ∀ᵐ t ∂volume.restrict (Ι a b), deriv (L ∘ f) t = L (deriv f t)
  rw [_root_.MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
  filter_upwards [hf.boundedVariationOn.ae_differentiableAt_of_mem_uIcc] with t ht htab
  simpa only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, one_smul] using
    ((L.hasFDerivAt.comp t
      (ht (_root_.Set.uIoc_subset_uIcc htab)).hasDerivAt.hasFDerivAt).hasDerivAt).deriv

run_cmd do
  let target := ``Submission.AbsolutelyContinuousOnInterval.ae_deriv_comp_continuousLinearMap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `AbsolutelyContinuousOnInterval.ae_deriv_comp_continuousLinearMap target :: scope.openDecls } }

open _root_.AbsolutelyContinuousOnInterval in
theorem intervalIntegrable_deriv_vector (hf : AbsolutelyContinuousOnInterval f a b) :
    IntervalIntegrable (deriv f) _root_.MeasureTheory.MeasureSpace.volume a b := by
  classical
  let A := (Module.Basis.ofVectorSpace ℝ E).equivFun.toContinuousLinearEquiv
  rw [intervalIntegrable_iff, _root_.MeasureTheory.IntegrableOn, ← A.integrable_comp_iff, _root_.MeasureTheory.integrable_pi_iff]
  intro i
  let L : E →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap ((LinearMap.proj i).comp A.toLinearMap)
  have hLac : AbsolutelyContinuousOnInterval (L ∘ f) a b :=
    L.lipschitz.lipschitzOnWith.comp_absolutelyContinuousOnInterval hf
      (_root_.Set.mapsTo_univ f (_root_.Set.uIcc a b))
  exact hLac.intervalIntegrable_deriv.def'.congr (ae_deriv_comp_continuousLinearMap hf L)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AbsolutelyContinuousOnInterval.intervalIntegrable_deriv_vector then
    throwError "Refusing to shadow existing declaration AbsolutelyContinuousOnInterval.intervalIntegrable_deriv_vector"
  Lean.modifyEnv fun env => Lean.addAlias env `AbsolutelyContinuousOnInterval.intervalIntegrable_deriv_vector ``Submission.AbsolutelyContinuousOnInterval.intervalIntegrable_deriv_vector

open _root_.AbsolutelyContinuousOnInterval in
theorem integral_deriv_eq_sub_vector (hf : AbsolutelyContinuousOnInterval f a b) :
    ∫ t in a..b, deriv f t = f b - f a := by
  let A := (Module.Basis.ofVectorSpace ℝ E).equivFun.toContinuousLinearEquiv
  apply A.injective
  ext i
  let L : E →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap ((LinearMap.proj i).comp A.toLinearMap)
  have hLac : AbsolutelyContinuousOnInterval (L ∘ f) a b :=
    L.lipschitz.lipschitzOnWith.comp_absolutelyContinuousOnInterval hf
      (_root_.Set.mapsTo_univ f (_root_.Set.uIcc a b))
  change L (∫ t in a..b, deriv f t) = L (f b - f a)
  calc
    L (∫ t in a..b, deriv f t) = ∫ t in a..b, L (deriv f t) :=
      (L.intervalIntegral_comp_comm hf.intervalIntegrable_deriv_vector).symm
    _ = ∫ t in a..b, deriv (L ∘ f) t :=
      intervalIntegral.integral_congr_ae_restrict
        (ae_deriv_comp_continuousLinearMap hf L).symm
    _ = L (f b) - L (f a) := by
      simpa only [Function.comp_apply] using hLac.integral_deriv_eq_sub
    _ = L (f b - f a) := (L.map_sub _ _).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AbsolutelyContinuousOnInterval.integral_deriv_eq_sub_vector then
    throwError "Refusing to shadow existing declaration AbsolutelyContinuousOnInterval.integral_deriv_eq_sub_vector"
  Lean.modifyEnv fun env => Lean.addAlias env `AbsolutelyContinuousOnInterval.integral_deriv_eq_sub_vector ``Submission.AbsolutelyContinuousOnInterval.integral_deriv_eq_sub_vector

end Vector

end AbsolutelyContinuousOnInterval

namespace Real
open _root_.Real

open _root_.Real in
theorem absolutelyContinuousOnInterval_sqrt (a b : ℝ) :
    AbsolutelyContinuousOnInterval _root_.Real.sqrt a b := by
  let q : ℝ := -(1 / 2 : ℝ)
  let v : ℝ → ℝ := fun t ↦ (1 / 2 : ℝ) * t ^ q
  have hvInt : IntervalIntegrable v _root_.MeasureTheory.MeasureSpace.volume a b := by
    exact (intervalIntegral.intervalIntegrable_rpow'
      (a := a) (b := b) (by norm_num [q])).const_mul (1 / 2 : ℝ)
  have hprim : AbsolutelyContinuousOnInterval
      (fun x ↦ ∫ t in a..x, v t) a b :=
    hvInt.absolutelyContinuousOnInterval_intervalIntegral _root_.Set.left_mem_uIcc
  have hconst : AbsolutelyContinuousOnInterval
      (fun _ : ℝ ↦ _root_.Real.sqrt a) a b :=
    (LipschitzWith.const (_root_.Real.sqrt a)).lipschitzOnWith.absolutelyContinuousOnInterval
  apply (hconst.add hprim).congr
  intro x _
  simp only [Pi.add_apply, v, q]
  rw [intervalIntegral.integral_const_mul,
    integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -(1 / 2 : ℝ)))]
  rw [show (-(1 / 2 : ℝ) + 1) = 1 / 2 by norm_num]
  simp only [← _root_.Real.sqrt_eq_rpow]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Real.absolutelyContinuousOnInterval_sqrt then
    throwError "Refusing to shadow existing declaration Real.absolutelyContinuousOnInterval_sqrt"
  Lean.modifyEnv fun env => Lean.addAlias env `Real.absolutelyContinuousOnInterval_sqrt ``Submission.Real.absolutelyContinuousOnInterval_sqrt

end Real

namespace AbsolutelyContinuousOnInterval
open _root_.AbsolutelyContinuousOnInterval

variable {f g : ℝ → ℝ} {a b : ℝ}

open _root_.AbsolutelyContinuousOnInterval in
theorem sub_le_integral_of_dini_le (hab : a ≤ b)
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : IntervalIntegrable g _root_.MeasureTheory.MeasureSpace.volume a b)
    (hD : ∀ t ∈ _root_.Set.Ioo a b, ∀ ε, 0 < ε →
      ∀ᶠ s in 𝓝[>] t, slope f t s ≤ g t + ε) :
    f b - f a ≤ ∫ t in a..b, g t := by
  have hdiff : ∀ᵐ t ∂volume.restrict (_root_.Set.Icc a b),
      DifferentiableAt ℝ f t := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    simpa only [_root_.Set.uIcc_of_le hab] using hf.ae_differentiableAt
  have hmem : ∀ᵐ t ∂volume.restrict (_root_.Set.Icc a b), t ∈ _root_.Set.Ioo a b := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    filter_upwards [_root_.MeasureTheory.Ioo_ae_eq_Icc (μ := _root_.MeasureTheory.MeasureSpace.volume)] with t ht htab
    exact ht.mpr htab
  have hle : ∀ᵐ t ∂volume.restrict (_root_.Set.Icc a b), deriv f t ≤ g t := by
    filter_upwards [hdiff, hmem] with t ht htab
    refine le_of_forall_pos_le_add fun ε hε ↦ ?_
    exact le_of_tendsto
      (ht.hasDerivAt.tendsto_slope.mono_left (nhdsGT_le_nhdsNE t))
      (hD t htab ε hε)
  rw [← hf.integral_deriv_eq_sub]
  exact intervalIntegral.integral_mono_ae_restrict hab
    hf.intervalIntegrable_deriv hg hle

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AbsolutelyContinuousOnInterval.sub_le_integral_of_dini_le then
    throwError "Refusing to shadow existing declaration AbsolutelyContinuousOnInterval.sub_le_integral_of_dini_le"
  Lean.modifyEnv fun env => Lean.addAlias env `AbsolutelyContinuousOnInterval.sub_le_integral_of_dini_le ``Submission.AbsolutelyContinuousOnInterval.sub_le_integral_of_dini_le

open _root_.ContinuousOn in
theorem _root_.Submission.ContinuousOn.sub_le_integral_of_dini_le (hab : a ≤ b)
    (hf : ContinuousOn f (_root_.Set.Icc a b))
    (hfac : ∀ c ∈ _root_.Set.Ioc a b, AbsolutelyContinuousOnInterval f c b)
    (hg : IntervalIntegrable g _root_.MeasureTheory.MeasureSpace.volume a b)
    (hD : ∀ t ∈ _root_.Set.Ioo a b, ∀ ε, 0 < ε →
      ∀ᶠ s in 𝓝[>] t, slope f t s ≤ g t + ε) :
    f b - f a ≤ ∫ t in a..b, g t := by
  obtain rfl | hab' := hab.eq_or_lt
  · simp
  let s := {c | f b - f c ≤ ∫ t in c..b, g t} ∩ _root_.Set.Icc a b
  have hs : IsClosed s := by
    have hgIcc : _root_.MeasureTheory.IntegrableOn g (_root_.Set.Icc a b) :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hab).1 hg
    have hgU : _root_.MeasureTheory.IntegrableOn g (_root_.Set.uIcc a b) := by
      simpa only [_root_.Set.uIcc_of_le hab] using hgIcc
    have hprim : ContinuousOn (fun c ↦ ∫ t in c..b, g t) (_root_.Set.Icc a b) := by
      simpa only [_root_.Set.uIcc_of_le hab] using
        (intervalIntegral.continuousOn_primitive_interval_left
          (f := g) (μ := _root_.MeasureTheory.MeasureSpace.volume) (a := a) (b := b) hgU)
    simpa only [s, _root_.Set.inter_comm, Pi.sub_apply, Set.inter_def, Set.mem_ofPred_eq] using
      isClosed_Icc.isClosed_le (continuousOn_const.sub hf) hprim
  have hclosure : closure (_root_.Set.Ioc a b) ⊆ s := by
    apply hs.closure_subset_iff.2
    intro c hc
    have hcb : c ≤ b := hc.2
    have hgcb : IntervalIntegrable g _root_.MeasureTheory.MeasureSpace.volume c b := by
      apply hg.mono_set
      rw [_root_.Set.uIcc_of_le hcb, _root_.Set.uIcc_of_le hab]
      exact _root_.Set.Icc_subset_Icc hc.1.le le_rfl
    refine ⟨AbsolutelyContinuousOnInterval.sub_le_integral_of_dini_le (f := f) (g := g) hcb
      (hfac c hc) hgcb ?_, ⟨hc.1.le, hc.2⟩⟩
    intro t ht
    exact hD t ⟨hc.1.trans ht.1, ht.2⟩
  rw [closure_Ioc hab'.ne] at hclosure
  exact (hclosure (left_mem_Icc.2 hab)).1

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.ContinuousOn
  let env ← Lean.getEnv
  if env.contains `ContinuousOn.sub_le_integral_of_dini_le then
    throwError "Refusing to shadow existing declaration ContinuousOn.sub_le_integral_of_dini_le"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousOn.sub_le_integral_of_dini_le ``Submission.ContinuousOn.sub_le_integral_of_dini_le

end AbsolutelyContinuousOnInterval
