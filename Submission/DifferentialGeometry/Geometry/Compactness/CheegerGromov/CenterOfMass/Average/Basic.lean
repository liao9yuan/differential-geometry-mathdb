import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.CenterOfMass.Existence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Submission.DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

universe u uE uH uX uY

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open _root_.Set _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Topology _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  [ConnectedSpace M] [T3Space M]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
    [T2Space (TangentBundle I M)] [SigmaCompactSpace M] [ConnectedSpace M] [T3Space M] in
theorem metricEnorm (g : SmoothRiemannianMetric I M) :
    letI : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    ∀ x : M, ∀ v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)) := by
  let : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  intro x v
  exact (isMetricNorm_of_riemannianBundle (I := I) g) x v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.metricEnorm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.metricEnorm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.metricEnorm ``Submission.DifferentialGeometry.CheegerGromovCompactness.metricEnorm

noncomputable def centerAverage (g : SmoothRiemannianMetric I M)
    {X : Type uX} {ι : Type} [Fintype ι] (μ : X → ι → ℝ)
    (points : X → ι → M) (join : M → M → ℝ → M) (p : X → M) (r : X → ℝ)
    (h : ∀ x : X, CenterOfMassConditions (I := I) g (μ x) (points x) join (p x) (r x))
    (x : X) : M :=
  centerOfMass (I := I) g (μ x) (points x) join (p x) (r x) (h x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.centerAverage then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.centerAverage"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.centerAverage ``Submission.DifferentialGeometry.CheegerGromovCompactness.centerAverage

noncomputable def centerAverageOn (g : SmoothRiemannianMetric I M)
    {X : Type uX} {ι : Type} [Fintype ι] (s : Set X) (μ : X → ι → ℝ)
    (points : X → ι → M) (join : M → M → ℝ → M) (p : X → M) (r : X → ℝ)
    (qstar : X → M)
    (h : ∀ x : X, x ∈ s → CenterOfMassConditions (I := I) g (μ x) (points x) join (p x) (r x))
    (x : X) : M :=
  by
    classical
    exact
      if hx : x ∈ s then
        centerOfMass (I := I) g (μ x) (points x) join (p x) (r x) (h x hx)
      else qstar x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.centerAverageOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.centerAverageOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.centerAverageOn ``Submission.DifferentialGeometry.CheegerGromovCompactness.centerAverageOn

namespace centerAverage

variable {g : SmoothRiemannianMetric I M} {X : Type uX} {ι : Type}

noncomputable def activeFill (μ : X → ι → ℝ) (points : X → ι → M)
    (qstar : X → M) : X → ι → M := by
  classical
  exact fun x i => if μ x i = 0 then qstar x else points x i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.centerAverage.activeFill then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.centerAverage.activeFill"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.centerAverage.activeFill ``Submission.DifferentialGeometry.CheegerGromovCompactness.centerAverage.activeFill

omit [T3Space M] in
omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
    [T2Space (TangentBundle I M)] [SigmaCompactSpace M] [ConnectedSpace M] in
theorem energy_activeFill [Fintype ι] (g : SmoothRiemannianMetric I M)
    (μ : X → ι → ℝ) (points : X → ι → M) (qstar : X → M)
    (x : X) (q : M) :
    CenterOfMass.centerEnergy (I := I) g (μ x) (activeFill μ points qstar x) q =
      CenterOfMass.centerEnergy (I := I) g (μ x) (points x) q := by
  apply CenterOfMass.centerEnergy_congr
  intro i hi
  simp only [activeFill, hi, ↓reduceIte]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.centerAverage.energy_activeFill then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.centerAverage.energy_activeFill"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.centerAverage.energy_activeFill ``Submission.DifferentialGeometry.CheegerGromovCompactness.centerAverage.energy_activeFill

theorem uniqueMin_activeFill [Fintype ι] (g : SmoothRiemannianMetric I M)
    (μ : X → ι → ℝ) (points : X → ι → M) (qstar : X → M)
    (join : M → M → ℝ → M) (p : X → M) (r : X → ℝ)
    (x : X) (h : CenterOfMassConditions (I := I) g (μ x)
      (activeFill μ points qstar x) join (p x) (r x)) :
    ∃! y : M, ∀ z : M,
      CenterOfMass.centerEnergy (I := I) g (μ x) (points x) y ≤
        CenterOfMass.centerEnergy (I := I) g (μ x) (points x) z := by
  let : _root_.Bundle.RiemannianBundle (fun y : M => TangentSpace I y) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  obtain ⟨y, _hy, hmin, huniq⟩ := h.exists_unique_minimizer
  refine ⟨y, ?_, ?_⟩
  · intro z
    rw [← energy_activeFill g μ points qstar x y,
      ← energy_activeFill g μ points qstar x z]
    exact hmin z
  · intro y' hy'
    apply huniq y'
    intro z
    rw [energy_activeFill g μ points qstar x y',
      energy_activeFill g μ points qstar x z]
    exact hy' z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.centerAverage.uniqueMin_activeFill then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.centerAverage.uniqueMin_activeFill"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.centerAverage.uniqueMin_activeFill ``Submission.DifferentialGeometry.CheegerGromovCompactness.centerAverage.uniqueMin_activeFill

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
    [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
theorem activeFill_close {μ : X → ι → ℝ} {points : X → ι → M} {qstar : X → M}
    {x : X} {ε : ℝ} (hε : 0 < ε)
    (hactive :
      letI : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ∀ i : ι, μ x i ≠ 0 → _root_.Dist.dist (qstar x) (points x i) < ε) :
    letI : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    ∀ i : ι, _root_.Dist.dist (qstar x) (activeFill μ points qstar x i) < ε := by
  let : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  intro i
  by_cases hzero : μ x i = 0
  · simpa [activeFill, hzero] using hε
  · simpa [activeFill, hzero] using hactive i hzero

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.centerAverage.activeFill_close then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.centerAverage.activeFill_close"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.centerAverage.activeFill_close ``Submission.DifferentialGeometry.CheegerGromovCompactness.centerAverage.activeFill_close

variable [Fintype ι]

omit [Fintype ι] in
theorem exists_active_radius {Y : Type uY} [PseudoMetricSpace Y] {s : Set X}
    [Finite ι]
    {target : X → Y} {μSeq : ℕ → ℕ → X → ι → ℝ}
    {pointsSeq : ℕ → ℕ → X → ι → Y}
    (hpts : ∀ i : ι, ∀ ε > 0, ∃ N : ℕ, ∀ a ≥ N, ∀ b ≥ N, ∀ x ∈ s,
      μSeq a b x i ≠ 0 → _root_.Dist.dist (target x) (pointsSeq a b x i) < ε) :
    ∃ radSeq : ℕ → ℕ → X → ℝ,
      (∀ a b x, 0 < radSeq a b x) ∧
      (∀ a b x, x ∈ s → ∀ i : ι, μSeq a b x i ≠ 0 →
        _root_.Dist.dist (target x) (pointsSeq a b x i) < radSeq a b x) ∧
      ∀ ε > 0, ∃ N : ℕ, ∀ a ≥ N, ∀ b ≥ N, ∀ x ∈ s, radSeq a b x < ε := by
  classical
  let := Fintype.ofFinite ι
  let radSeq : ℕ → ℕ → X → ℝ := fun a b x =>
    (∑ i : ι, if μSeq a b x i = 0 then 0 else _root_.Dist.dist (target x) (pointsSeq a b x i)) +
      1 / ((a : ℝ) + 1)
  refine ⟨radSeq, ?_, ?_, ?_⟩
  · intro a b x
    have hsum : 0 ≤
        ∑ i : ι, if μSeq a b x i = 0 then 0 else _root_.Dist.dist (target x) (pointsSeq a b x i) := by
      exact Finset.sum_nonneg fun i _ => by
        split_ifs
        · exact le_rfl
        · exact dist_nonneg
    have htail : 0 < 1 / ((a : ℝ) + 1) := by positivity
    exact add_pos_of_nonneg_of_pos hsum htail
  · intro a b x hx i hi
    have hle : _root_.Dist.dist (target x) (pointsSeq a b x i) ≤
        ∑ j : ι, if μSeq a b x j = 0 then 0 else _root_.Dist.dist (target x) (pointsSeq a b x j) := by
      calc
        _root_.Dist.dist (target x) (pointsSeq a b x i) =
            (if μSeq a b x i = 0 then 0 else _root_.Dist.dist (target x) (pointsSeq a b x i)) := by
              simp [hi]
        _ ≤ ∑ j : ι,
            if μSeq a b x j = 0 then 0 else _root_.Dist.dist (target x) (pointsSeq a b x j) := by
              refine Finset.single_le_sum (s := Finset.univ)
                (f := fun j : ι =>
                  if μSeq a b x j = 0 then (0 : ℝ) else _root_.Dist.dist (target x) (pointsSeq a b x j))
                ?_ (Finset.mem_univ i)
              intro j _
              change 0 ≤ if μSeq a b x j = 0 then (0 : ℝ) else
                _root_.Dist.dist (target x) (pointsSeq a b x j)
              by_cases hj : μSeq a b x j = 0
              · simp [hj]
              · simp [hj, dist_nonneg]
    have htail : 0 < 1 / ((a : ℝ) + 1) := by positivity
    exact lt_of_le_of_lt hle (lt_add_of_pos_right _ htail)
  · intro ε hε
    let δ : ℝ := ε / (2 * ((Fintype.card ι : ℝ) + 1))
    have hδ : 0 < δ := by
      dsimp [δ]
      positivity
    choose N hN using fun i : ι => hpts i δ hδ
    let Nmax : ℕ := Finset.univ.sup N
    have htail : ∀ᶠ a : ℕ in Filter.atTop, 1 / ((a : ℝ) + 1) < ε / 2 :=
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
        (Iio_mem_nhds (by linarith))
    obtain ⟨Ntail, hNtail⟩ := Filter.eventually_atTop.mp htail
    refine ⟨max Nmax Ntail, fun a ha b hb x hx => ?_⟩
    have ha_max : Nmax ≤ a := le_trans (le_max_left _ _) ha
    have ha_tail : Ntail ≤ a := le_trans (le_max_right _ _) ha
    have hb_max : Nmax ≤ b := le_trans (le_max_left _ _) hb
    have hsum_le :
        (∑ i : ι,
          if μSeq a b x i = 0 then 0 else _root_.Dist.dist (target x) (pointsSeq a b x i)) ≤
          ∑ _i : ι, δ := by
      refine Finset.sum_le_sum fun i _ => ?_
      by_cases hi : μSeq a b x i = 0
      · simp [hi, hδ.le]
      · simp only [hi, ↓reduceIte]
        have hNi : N i ≤ Nmax :=
          Finset.le_sup (s := Finset.univ) (f := N) (Finset.mem_univ i)
        exact le_of_lt (hN i a (le_trans hNi ha_max) b (le_trans hNi hb_max) x hx hi)
    have hcard :
        (∑ _i : ι, δ) = (Fintype.card ι : ℝ) * δ := by simp
    have hcard_lt : (Fintype.card ι : ℝ) * δ < ε / 2 := by
      dsimp [δ]
      have hden : 0 < 2 * ((Fintype.card ι : ℝ) + 1) := by positivity
      rw [← mul_div_assoc]
      apply (div_lt_iff₀ hden).2
      have hcard_nonneg : 0 ≤ (Fintype.card ι : ℝ) := by positivity
      nlinarith
    have hsum_lt :
        (∑ i : ι,
          if μSeq a b x i = 0 then 0 else _root_.Dist.dist (target x) (pointsSeq a b x i)) <
          ε / 2 :=
      lt_of_le_of_lt hsum_le (hcard ▸ hcard_lt)
    simpa [radSeq] using add_lt_add_of_lt_of_lt hsum_lt (hNtail a ha_tail)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.centerAverage.exists_active_radius then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.centerAverage.exists_active_radius"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.centerAverage.exists_active_radius ``Submission.DifferentialGeometry.CheegerGromovCompactness.centerAverage.exists_active_radius

structure WeightDataOn (s : Set X) (U : ι → Set X) (μ : X → ι → ℝ) : Prop where
  nonneg : ∀ x ∈ s, ∀ i : ι, 0 ≤ μ x i
  pos : ∀ x ∈ s, ∃ i : ι, 0 < μ x i
  sum_one : ∀ x ∈ s, ∑ i : ι, μ x i = 1
  active_mem : ∀ x ∈ s, ∀ i : ι, μ x i ≠ 0 → x ∈ U i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.centerAverage.WeightDataOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.centerAverage.WeightDataOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.centerAverage.WeightDataOn ``Submission.DifferentialGeometry.CheegerGromovCompactness.centerAverage.WeightDataOn

theorem WeightDataOn.comp {Y : Type uY} {s : Set Y} {U : Set X}
    {R : ι → Set X} {μ : X → ι → ℝ} {f : Y → X}
    (h : WeightDataOn U R μ) (hf : Set.MapsTo f s U) :
    WeightDataOn s (fun i => f ⁻¹' R i) (fun y i => μ (f y) i) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro y hy i
    exact h.nonneg (f y) (hf hy) i
  · intro y hy
    exact h.pos (f y) (hf hy)
  · intro y hy
    exact h.sum_one (f y) (hf hy)
  · intro y hy i hne
    exact h.active_mem (f y) (hf hy) i hne

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.CheegerGromovCompactness.centerAverage.WeightDataOn
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.centerAverage.WeightDataOn.comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.centerAverage.WeightDataOn.comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.centerAverage.WeightDataOn.comp ``Submission.DifferentialGeometry.CheegerGromovCompactness.centerAverage.WeightDataOn.comp

variable {μ : X → ι → ℝ} {points : X → ι → M} {join : M → M → ℝ → M}
  {p : X → M} {r : X → ℝ}
  (h : ∀ x : X, CenterOfMassConditions (I := I) g (μ x) (points x) join (p x) (r x))

theorem on_eq {s : Set X} {qstar : X → M}
    (hOn : ∀ x : X, x ∈ s → CenterOfMassConditions (I := I) g (μ x) (points x) join (p x) (r x))
    {x : X} (hx : x ∈ s) :
    centerAverageOn (I := I) g s μ points join p r qstar hOn x =
      centerOfMass (I := I) g (μ x) (points x) join (p x) (r x) (hOn x hx) := by
  simp [centerAverageOn, hx]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.centerAverage.on_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.centerAverage.on_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.centerAverage.on_eq ``Submission.DifferentialGeometry.CheegerGromovCompactness.centerAverage.on_eq

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
    [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
theorem inputOfFill {qstar : X → M} (x : X)
    (hcomplete :
      letI : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
      CompleteSpace M)
    (hr : 0 < r x)
    (hqstar :
      letI : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      _root_.Dist.dist (p x) (qstar x) < r x)
    (hactive :
      letI : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ∀ i : ι, μ x i ≠ 0 → _root_.Dist.dist (p x) (points x i) < r x)
    (hμ_nonneg : ∀ i : ι, 0 ≤ μ x i)
    (hμ_pos : ∃ i : ι, 0 < μ x i)
    (hstrict :
      StrictDistanceConvexity (I := I) g (activeFill μ points qstar x) join (p x) (r x)) :
    CenterOfMassConditions (I := I) g (μ x) (activeFill μ points qstar x) join (p x) (r x) := by
  let : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  refine
    { complete := hcomplete
      enorm := metricEnorm (I := I) g
      r_pos := hr
      points_mem := ?_
      μ_nonneg := hμ_nonneg
      μ_pos := hμ_pos
      strict_distance := hstrict }
  intro i
  by_cases hzero : μ x i = 0
  · simpa [activeFill, hzero] using hqstar
  · simpa [activeFill, hzero] using hactive i hzero

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.centerAverage.inputOfFill then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.centerAverage.inputOfFill"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.centerAverage.inputOfFill ``Submission.DifferentialGeometry.CheegerGromovCompactness.centerAverage.inputOfFill

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
    [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
theorem inputOfFillSelf {qstar : X -> M} (x : X)
    (hcomplete :
      letI : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
      CompleteSpace M)
    (hr : 0 < r x)
    (hactive :
      letI : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      forall i : ι, μ x i ≠ 0 -> _root_.Dist.dist (qstar x) (points x i) < r x)
    (hμ_nonneg : forall i : ι, 0 ≤ μ x i)
    (hμ_pos : exists i : ι, 0 < μ x i)
    (hstrict :
      StrictDistanceConvexity (I := I) g (activeFill μ points qstar x) join (qstar x) (r x)) :
    CenterOfMassConditions (I := I) g (μ x) (activeFill μ points qstar x) join (qstar x)
      (r x) := by
  let : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  refine inputOfFill (I := I) (g := g) (μ := μ) (points := points) (join := join)
    (p := qstar) (r := r) (qstar := qstar) x hcomplete hr ?_ hactive
    hμ_nonneg hμ_pos hstrict
  simpa using hr

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.centerAverage.inputOfFillSelf then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.centerAverage.inputOfFillSelf"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.centerAverage.inputOfFillSelf ``Submission.DifferentialGeometry.CheegerGromovCompactness.centerAverage.inputOfFillSelf

theorem mem (x : X) :
    letI : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    centerAverage (I := I) g μ points join p r h x ∈ Metric.closedBall (p x) (2 * r x) := by
  simpa [centerAverage] using
    centerOfMass.mem (I := I) (g := g) (μ := μ x) (points := points x) (join := join)
      (p := p x) (r := r x) (h x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.centerAverage.mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.centerAverage.mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.centerAverage.mem ``Submission.DifferentialGeometry.CheegerGromovCompactness.centerAverage.mem

theorem mem_on {s : Set X} {qstar : X → M}
    (hOn : ∀ x : X, x ∈ s → CenterOfMassConditions (I := I) g (μ x) (points x) join (p x) (r x))
    {x : X} (hx : x ∈ s) :
    letI : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    centerAverageOn (I := I) g s μ points join p r qstar hOn x ∈
      Metric.closedBall (p x) (2 * r x) := by
  let : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  rw [on_eq (I := I) (g := g) (μ := μ) (points := points) (join := join) (p := p)
    (r := r) hOn hx]
  exact centerOfMass.mem (I := I) (g := g) (μ := μ x) (points := points x)
    (join := join) (p := p x) (r := r x) (hOn x hx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.centerAverage.mem_on then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.centerAverage.mem_on"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.centerAverage.mem_on ``Submission.DifferentialGeometry.CheegerGromovCompactness.centerAverage.mem_on

theorem eq_of_all_eq {qstar : X → M} (x : X)
    (hpts : ∀ i : ι, points x i = qstar x) :
    letI : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    centerAverage (I := I) g μ points join p r h x = qstar x := by
  let : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  have hnear : ∀ i : ι, _root_.Dist.dist (qstar x) (points x i) ≤ (0 : ℝ) := by
    intro i
    rw [hpts i, dist_self]
  have hdist :
      dist (centerAverage (I := I) g μ points join p r h x) (qstar x) ≤ 0 :=
    by
      simpa [centerAverage] using
        centerOfMass.dist_le (I := I) (g := g) (μ := μ x) (points := points x)
          (join := join) (p := p x) (r := r x) (h x) (qstar := qstar x)
          (by norm_num) hnear
  exact dist_eq_zero.mp (le_antisymm hdist dist_nonneg)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.centerAverage.eq_of_all_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.centerAverage.eq_of_all_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.centerAverage.eq_of_all_eq ``Submission.DifferentialGeometry.CheegerGromovCompactness.centerAverage.eq_of_all_eq

theorem dist_le {qstar : X → M} {ε : ℝ} (x : X) (hε : 0 ≤ ε)
    (hnear :
      letI : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ∀ i : ι, _root_.Dist.dist (qstar x) (points x i) ≤ ε) :
    letI : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    dist (centerAverage (I := I) g μ points join p r h x) (qstar x) ≤ 2 * ε := by
  simpa [centerAverage] using
    centerOfMass.dist_le (I := I) (g := g) (μ := μ x) (points := points x)
      (join := join) (p := p x) (r := r x) (h x) (qstar := qstar x) hε hnear

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.centerAverage.dist_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.centerAverage.dist_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.centerAverage.dist_le ``Submission.DifferentialGeometry.CheegerGromovCompactness.centerAverage.dist_le

theorem dist_le_on {s : Set X} {default target : X → M} {ε : ℝ}
    (hOn : ∀ x : X, x ∈ s → CenterOfMassConditions (I := I) g (μ x) (points x) join (p x) (r x))
    {x : X} (hx : x ∈ s) (hε : 0 ≤ ε)
    (hnear :
      letI : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ∀ i : ι, _root_.Dist.dist (target x) (points x i) ≤ ε) :
    letI : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    dist (centerAverageOn (I := I) g s μ points join p r default hOn x) (target x) ≤
      2 * ε := by
  let : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  rw [on_eq (I := I) (g := g) (μ := μ) (points := points) (join := join) (p := p)
    (r := r) hOn hx]
  exact centerOfMass.dist_le (I := I) (g := g) (μ := μ x) (points := points x)
    (join := join) (p := p x) (r := r x) (hOn x hx) (qstar := target x) hε hnear

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.centerAverage.dist_le_on then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.centerAverage.dist_le_on"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.centerAverage.dist_le_on ``Submission.DifferentialGeometry.CheegerGromovCompactness.centerAverage.dist_le_on

end centerAverage
end CheegerGromovCompactness
end DifferentialGeometry
