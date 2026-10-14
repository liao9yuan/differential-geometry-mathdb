import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornArmComparison
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornEndAngle
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornRayApproximation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Filter _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Submission.Set
open scoped _root_.Topology _root_.Submission.Topology _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open _root_.Submission.DifferentialGeometry.Toponogov

universe u

variable {W : Type u} [MetricSpace W] [ChartedSpace ThreeSpace W]
  [IsManifold I3 ∞ W] [SigmaCompactSpace W]

omit [ChartedSpace ThreeSpace W] [IsManifold I3 ∞ W] [SigmaCompactSpace W] in
theorem endComparisonAngle_eq_comparisonAngle {E : UniformSpace.Completion W} (a b : EndRay E)
    (s t : ℝ) :
    endComparisonAngle a b s t = comparisonAngle s t (_root_.Dist.dist (a.point s) (b.point t)) :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endComparisonAngle_eq_comparisonAngle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endComparisonAngle_eq_comparisonAngle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endComparisonAngle_eq_comparisonAngle ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endComparisonAngle_eq_comparisonAngle

private theorem tendsto_comparisonAngle' {A : Type*} {l : Filter A} {a b c : A → ℝ}
    {a₀ b₀ c₀ : ℝ} (ha : _root_.Filter.Tendsto a l (𝓝 a₀)) (hb : _root_.Filter.Tendsto b l (𝓝 b₀))
    (hc : _root_.Filter.Tendsto c l (𝓝 c₀)) (ha₀ : 0 < a₀) (hb₀ : 0 < b₀) :
    Tendsto (fun i => comparisonAngle (a i) (b i) (c i)) l (𝓝 (comparisonAngle a₀ b₀ c₀)) := by
  simp only [comparisonAngle, comparisonCosine]
  exact Real.continuous_arccos.continuousAt.tendsto.comp
    (((ha.pow 2).add (hb.pow 2)).sub (hc.pow 2) |>.div
      ((tendsto_const_nhds.mul ha).mul hb) (by positivity))

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.tendsto_comparisonAngle'
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.tendsto_comparisonAngle' target :: scope.openDecls } }

omit [SigmaCompactSpace W] in
private theorem endComparisonAngle_mono_of_ray_approximation {g : SmoothRiemannianMetric I3 W}
    (H : FiniteHorn g) {inner : ℕ} {d : ℝ}
    (hcmp : ∀ (arm : Fin 2 → ℝ → W) (L : Fin 2 → ℝ), (∀ k, 0 < L k) →
      (∀ k, ContMDiffOn 𝓘(ℝ, ℝ) I3 ∞ (arm k) (_root_.Set.Icc 0 (L k))) →
      (∀ k s, s ∈ _root_.Set.Icc 0 (L k) → arm k s ∈ H.subend inner) →
      arm 0 0 = arm 1 0 →
      (∀ k s, s ∈ _root_.Set.Icc 0 (L k) → ∀ t ∈ _root_.Set.Icc 0 (L k), _root_.Dist.dist (arm k s) (arm k t) = |s - t|) →
      ∀ a1 a2 b1 b2 : ℝ, 0 < a1 → a1 ≤ a2 → a2 ≤ L 0 → 0 < b1 → b1 ≤ b2 → b2 ≤ L 1 →
        comparisonAngle a2 b2 (_root_.Dist.dist (arm 0 a2) (arm 1 b2)) ≤
          comparisonAngle a1 b1 (_root_.Dist.dist (arm 0 a1) (arm 1 b1)))
    (hrx : ∀ a b : EndRay H.endpoint, ∀ lo hi : Fin 2 → ℝ, (∀ k, 0 < lo k) →
      (∀ k, lo k ≤ hi k) → hi 0 ≤ a.length → hi 1 ≤ b.length → (∀ k, hi k ≤ d) →
      ∃ A : RayApproximation H a b lo hi, A.connector_index = inner)
    (a b : EndRay H.endpoint) {s₁ s₂ t₁ t₂ : ℝ}
    (hs₁ : 0 < s₁) (hs₁₂ : s₁ ≤ s₂) (hs₂ : s₂ ≤ _root_.Min.min a.length d)
    (ht₁ : 0 < t₁) (ht₁₂ : t₁ ≤ t₂) (ht₂ : t₂ ≤ _root_.Min.min b.length d) :
    endComparisonAngle a b s₂ t₂ ≤ endComparisonAngle a b s₁ t₁ := by
  let lo : Fin 2 → ℝ := ![s₁ / 2, t₁ / 2]
  let hi : Fin 2 → ℝ := ![_root_.Min.min a.length d, _root_.Min.min b.length d]
  have hlo : ∀ k, 0 < lo k := by
    intro k
    fin_cases k
    · change 0 < s₁ / 2
      linarith
    · change 0 < t₁ / 2
      linarith
  have hlohi : ∀ k, lo k ≤ hi k := by
    intro k
    fin_cases k
    · change s₁ / 2 ≤ _root_.Min.min a.length d
      linarith
    · change t₁ / 2 ≤ _root_.Min.min b.length d
      linarith
  have hia : hi 0 ≤ a.length := by
    change _root_.Min.min a.length d ≤ a.length
    exact min_le_left _ _
  have hib : hi 1 ≤ b.length := by
    change _root_.Min.min b.length d ≤ b.length
    exact min_le_left _ _
  have hid : ∀ k, hi k ≤ d := by
    intro k
    fin_cases k
    · change _root_.Min.min a.length d ≤ d
      exact min_le_right _ _
    · change _root_.Min.min b.length d ≤ d
      exact min_le_right _ _
  obtain ⟨A, hA⟩ := hrx a b lo hi hlo hlohi hia hib hid
  have hs₁I : s₁ ∈ _root_.Set.Icc (lo 0) (hi 0) := by
    constructor
    · change s₁ / 2 ≤ s₁
      linarith
    · change s₁ ≤ _root_.Min.min a.length d
      linarith
  have hs₂I : s₂ ∈ _root_.Set.Icc (lo 0) (hi 0) := by
    constructor
    · change s₁ / 2 ≤ s₂
      linarith
    · change s₂ ≤ _root_.Min.min a.length d
      linarith
  have ht₁I : t₁ ∈ _root_.Set.Icc (lo 1) (hi 1) := by
    constructor
    · change t₁ / 2 ≤ t₁
      linarith
    · change t₁ ≤ _root_.Min.min b.length d
      linarith
  have ht₂I : t₂ ∈ _root_.Set.Icc (lo 1) (hi 1) := by
    constructor
    · change t₁ / 2 ≤ t₂
      linarith
    · change t₂ ≤ _root_.Min.min b.length d
      linarith
  have heta_s : _root_.Min.min s₁ t₁ / 4 ≤ s₁ / 2 := by linarith [min_le_left s₁ t₁, hs₁]
  have heta_t : _root_.Min.min s₁ t₁ / 4 ≤ t₁ / 2 := by linarith [min_le_right s₁ t₁, ht₁]
  have hineq : ∀ᶠ i in _root_.Filter.atTop,
      comparisonAngle (A.parameter 0 i s₂) (A.parameter 1 i t₂)
          (_root_.Dist.dist (A.arm 0 i (A.parameter 0 i s₂)) (A.arm 1 i (A.parameter 1 i t₂))) ≤
        comparisonAngle (A.parameter 0 i s₁) (A.parameter 1 i t₁)
          (_root_.Dist.dist (A.arm 0 i (A.parameter 0 i s₁)) (A.arm 1 i (A.parameter 1 i t₁))) := by
    filter_upwards [A.uniform (_root_.Min.min s₁ t₁ / 4) (by positivity)] with i hi
    have h₁ := hi.2 s₁ hs₁I t₁ ht₁I
    have h₂ := hi.2 s₂ hs₂I t₂ ht₂I
    have hsub : ∀ k s, s ∈ _root_.Set.Icc 0 (A.length k i) → A.arm k i s ∈ H.subend inner := by
      intro k s hs
      have h := A.arm_buffer (subset_closure (A.arm_mem k i s hs))
      rwa [hA] at h
    have hσ₁ : 0 < A.parameter 0 i s₁ := by
      have h := (abs_lt.mp h₁.1).1
      linarith
    have hσ₁₂ : A.parameter 0 i s₁ ≤ A.parameter 0 i s₂ :=
      A.parameter_mono 0 i hs₁I hs₂I hs₁₂
    have hσ₂ : A.parameter 0 i s₂ ≤ A.length 0 i := (A.parameter_mem 0 i s₂ hs₂I).2
    have hτ₁ : 0 < A.parameter 1 i t₁ := by
      have h := (abs_lt.mp h₁.2.1).1
      linarith
    have hτ₁₂ : A.parameter 1 i t₁ ≤ A.parameter 1 i t₂ :=
      A.parameter_mono 1 i ht₁I ht₂I ht₁₂
    have hτ₂ : A.parameter 1 i t₂ ≤ A.length 1 i := (A.parameter_mem 1 i t₂ ht₂I).2
    exact hcmp (fun k => A.arm k i) (fun k => A.length k i) (fun k => A.length_pos k i)
      (fun k => A.arm_smooth k i) hsub
      (by rw [A.starts 0 i, A.starts 1 i])
      (fun k s hs t ht => A.minimizing k i s hs t ht)
      (A.parameter 0 i s₁) (A.parameter 0 i s₂) (A.parameter 1 i t₁) (A.parameter 1 i t₂)
      hσ₁ hσ₁₂ hσ₂ hτ₁ hτ₁₂ hτ₂
  have hlimσ : ∀ σ ∈ _root_.Set.Icc (lo 0) (hi 0), _root_.Filter.Tendsto (fun i => A.parameter 0 i σ) _root_.Filter.atTop (𝓝 σ) := by
    intro σ hσ
    rw [Metric.tendsto_nhds]
    intro eta heta
    filter_upwards [A.uniform eta heta] with i hi
    simpa only [Real.dist_eq] using (hi.2 σ hσ t₁ ht₁I).1
  have hlimτ : ∀ σ ∈ _root_.Set.Icc (lo 1) (hi 1), _root_.Filter.Tendsto (fun i => A.parameter 1 i σ) _root_.Filter.atTop (𝓝 σ) := by
    intro σ hσ
    rw [Metric.tendsto_nhds]
    intro eta heta
    filter_upwards [A.uniform eta heta] with i hi
    simpa only [Real.dist_eq] using (hi.2 s₁ hs₁I σ hσ).2.1
  have hlimΔ : _root_.Filter.Tendsto
      (fun i => _root_.Dist.dist (A.arm 0 i (A.parameter 0 i s₂)) (A.arm 1 i (A.parameter 1 i t₂)))
      atTop (𝓝 (_root_.Dist.dist (a.point s₂) (b.point t₂))) := by
    rw [Metric.tendsto_nhds]
    intro eta heta
    filter_upwards [A.uniform eta heta] with i hi
    simpa only [Real.dist_eq] using (hi.2 s₂ hs₂I t₂ ht₂I).2.2.2.2
  have hlim₂ := tendsto_comparisonAngle' (hlimσ s₂ hs₂I) (hlimτ t₂ ht₂I) hlimΔ
    (hs₁.trans_le hs₁₂) (ht₁.trans_le ht₁₂)
  have hlimΔ₁ : _root_.Filter.Tendsto
      (fun i => _root_.Dist.dist (A.arm 0 i (A.parameter 0 i s₁)) (A.arm 1 i (A.parameter 1 i t₁)))
      atTop (𝓝 (_root_.Dist.dist (a.point s₁) (b.point t₁))) := by
    rw [Metric.tendsto_nhds]
    intro eta heta
    filter_upwards [A.uniform eta heta] with i hi
    simpa only [Real.dist_eq] using (hi.2 s₁ hs₁I t₁ ht₁I).2.2.2.2
  have hlim₁ := tendsto_comparisonAngle' (hlimσ s₁ hs₁I) (hlimτ t₁ ht₁I) hlimΔ₁ hs₁ ht₁
  have hfinal : comparisonAngle s₂ t₂ (_root_.Dist.dist (a.point s₂) (b.point t₂)) ≤
      comparisonAngle s₁ t₁ (_root_.Dist.dist (a.point s₁) (b.point t₁)) :=
    le_of_tendsto_of_tendsto hlim₂ hlim₁ hineq
  rw [endComparisonAngle_eq_comparisonAngle a b s₂ t₂,
    endComparisonAngle_eq_comparisonAngle a b s₁ t₁]
  exact hfinal

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endComparisonAngle_mono_of_ray_approximation
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endComparisonAngle_mono_of_ray_approximation target :: scope.openDecls } }

theorem finite_horn_end_angle_monotone :
    ∃ H₀ : ℝ, 0 < H₀ ∧ ∀ (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g),
      H₀ ≤ H.collar_depth → ∃ d : ℝ, 0 < d ∧ ∀ a b : EndRay H.endpoint,
        CoordinatewiseNonincreasingOn (endRayLength H.endpoint d a) (endRayLength H.endpoint d b)
          (radialComparisonAngle (endRayFamily H.endpoint) a b) := by
  obtain ⟨H₁, hH₁, hcmp⟩ := exists_finiteHorn_arm_comparison_depth (W := W)
  obtain ⟨H₂, hH₂, happ⟩ := exists_finiteHorn_ray_approximation_in_subend_depth (W := W)
  refine ⟨max H₁ H₂, lt_max_of_lt_left hH₁, ?_⟩
  intro g H hdepth
  obtain ⟨inner, hinner⟩ := hcmp g H ((le_max_left H₁ H₂).trans hdepth)
  obtain ⟨d, hd, hlocal⟩ := happ g H ((le_max_right H₁ H₂).trans hdepth) inner
  have hfull : ∀ a b : EndRay H.endpoint,
      CoordinatewiseNonincreasingOn (_root_.Min.min a.length d) (_root_.Min.min b.length d) (endComparisonAngle a b) := by
    intro a b
    constructor
    · intro s₁ s₂ t hs₁ hs₂ ht hs₁₂
      exact endComparisonAngle_mono_of_ray_approximation H hinner hlocal a b
        hs₁.1 hs₁₂ hs₂.2 ht.1 le_rfl ht.2
    · intro s t₁ t₂ hs ht₁ ht₂ ht₁₂
      exact endComparisonAngle_mono_of_ray_approximation H hinner hlocal a b
        hs.1 le_rfl hs.2 ht₁.1 ht₁₂ ht₂.2
  refine ⟨d, hd, fun a b => ?_⟩
  have hfun : radialComparisonAngle (endRayFamily H.endpoint) a b = endComparisonAngle a b :=
    funext fun s => funext fun t => radialComparisonAngle_endRay a b s t
  rw [endRayLength, endRayLength, hfun]
  exact hfull a b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_end_angle_monotone then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_end_angle_monotone"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_end_angle_monotone ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_end_angle_monotone

theorem finite_horn_end_angle_of_depth :
    ∃ H₀ : ℝ, 0 < H₀ ∧ ∀ (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g),
      H₀ ≤ H.collar_depth → Nonempty (EndAngles H) := by
  obtain ⟨H₀, hH₀, hmono⟩ := finite_horn_end_angle_monotone (W := W)
  refine ⟨H₀, hH₀, ?_⟩
  intro g H hdepth
  obtain ⟨d, hd, hmono'⟩ := hmono g H hdepth
  exact finite_horn_end_angle_of_monotone H d hd hmono'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_end_angle_of_depth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_end_angle_of_depth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_end_angle_of_depth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_end_angle_of_depth


omit [SigmaCompactSpace W] in
theorem finiteHorn_end_angle_monotone_of_endRay_dist_lt_sum
    (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g)
    (hsave : ∀ a b : EndRay H.endpoint,
      _root_.Dist.dist (a.point a.length) (b.point b.length) < a.length + b.length) :
    ∃ d : ℝ, 0 < d ∧ ∀ a b : EndRay H.endpoint,
      CoordinatewiseNonincreasingOn (endRayLength H.endpoint d a) (endRayLength H.endpoint d b)
        (radialComparisonAngle (endRayFamily H.endpoint) a b) := by
  obtain ⟨inner, hcmp⟩ := finiteHorn_arm_comparison_of_endRay_dist_lt_sum g H hsave
  obtain ⟨d, hd, hlocal⟩ :=
    finiteHorn_ray_approximation_in_subend_of_endRay_dist_lt_sum g H hsave inner
  have hfull : ∀ a b : EndRay H.endpoint,
      CoordinatewiseNonincreasingOn (_root_.Min.min a.length d) (_root_.Min.min b.length d) (endComparisonAngle a b) := by
    intro a b
    constructor
    · intro s1 s2 t hs1 hs2 ht hs12
      exact endComparisonAngle_mono_of_ray_approximation H
        (fun arm L _hL _hsmooth hmem hstart hmetric => hcmp arm L hmem hstart hmetric)
        (fun a b lo hi hlo _hlohi hia hib hid => hlocal a b lo hi hlo hia hib hid) a b
        hs1.1 hs12 hs2.2 ht.1 le_rfl ht.2
    · intro s t1 t2 hs ht1 ht2 ht12
      exact endComparisonAngle_mono_of_ray_approximation H
        (fun arm L _hL _hsmooth hmem hstart hmetric => hcmp arm L hmem hstart hmetric)
        (fun a b lo hi hlo _hlohi hia hib hid => hlocal a b lo hi hlo hia hib hid) a b
        hs.1 le_rfl hs.2 ht1.1 ht12 ht2.2
  refine ⟨d, hd, fun a b => ?_⟩
  have hfun : radialComparisonAngle (endRayFamily H.endpoint) a b = endComparisonAngle a b :=
    funext fun s => funext fun t => radialComparisonAngle_endRay a b s t
  rw [endRayLength, endRayLength, hfun]
  exact hfull a b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finiteHorn_end_angle_monotone_of_endRay_dist_lt_sum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finiteHorn_end_angle_monotone_of_endRay_dist_lt_sum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finiteHorn_end_angle_monotone_of_endRay_dist_lt_sum ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finiteHorn_end_angle_monotone_of_endRay_dist_lt_sum


end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
