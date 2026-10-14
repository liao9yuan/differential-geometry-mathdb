import Submission.DifferentialGeometry.Geometry.Measure.Area.SpanningCompetitors

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission








noncomputable section

open _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T3Space M]



def lipschitzContractibleLoop (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) :=
  {γ : contractibleLoop M // ∃ L : ℝ≥0, ∀ s t,
    riemannianEDistOf g (γ.val s) (γ.val t) ≤ (L : ℝ≥0∞) * _root_.EDist.edist s t}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.lipschitzContractibleLoop then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.lipschitzContractibleLoop"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.lipschitzContractibleLoop ``Submission.DifferentialGeometry.Geometry.lipschitzContractibleLoop


def spanningDiskAreas (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ : lipschitzContractibleLoop g) : Set ℝ :=
  (fun u : C(closedDisk, M) => riemannianDiskArea g u) '' spanningDiskCompetitors g γ.val.val

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.spanningDiskAreas then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.spanningDiskAreas"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.spanningDiskAreas ``Submission.DifferentialGeometry.Geometry.spanningDiskAreas


theorem spanningDiskAreas_nonempty [Nonempty M] [PreconnectedSpace M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (γ : lipschitzContractibleLoop g) :
    (spanningDiskAreas g γ).Nonempty := by
  obtain ⟨L, hL⟩ := γ.property
  exact (spanningDiskCompetitors_nonempty g hL γ.val.property).image _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.spanningDiskAreas_nonempty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.spanningDiskAreas_nonempty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.spanningDiskAreas_nonempty ``Submission.DifferentialGeometry.Geometry.spanningDiskAreas_nonempty

omit [CompactSpace M] [T3Space M] [FiniteDimensional ℝ E] in
theorem spanningDiskAreas_bddBelow (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ : lipschitzContractibleLoop g) : BddBelow (spanningDiskAreas g γ) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨u, _, rfl⟩
  exact riemannianDiskArea_nonneg g u

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.spanningDiskAreas_bddBelow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.spanningDiskAreas_bddBelow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.spanningDiskAreas_bddBelow ``Submission.DifferentialGeometry.Geometry.spanningDiskAreas_bddBelow



def leastSpanningArea (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ : lipschitzContractibleLoop g) : ℝ := _root_.InfSet.sInf (spanningDiskAreas g γ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.leastSpanningArea then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.leastSpanningArea"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.leastSpanningArea ``Submission.DifferentialGeometry.Geometry.leastSpanningArea

theorem leastSpanningArea_isGLB [Nonempty M] [PreconnectedSpace M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (γ : lipschitzContractibleLoop g) :
    IsGLB (spanningDiskAreas g γ) (leastSpanningArea g γ) :=
  isGLB_csInf (spanningDiskAreas_nonempty g γ) (spanningDiskAreas_bddBelow g γ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.leastSpanningArea_isGLB then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.leastSpanningArea_isGLB"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.leastSpanningArea_isGLB ``Submission.DifferentialGeometry.Geometry.leastSpanningArea_isGLB

theorem leastSpanningArea_nonneg [Nonempty M] [PreconnectedSpace M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (γ : lipschitzContractibleLoop g) :
    0 ≤ leastSpanningArea g γ := by
  apply le_csInf (spanningDiskAreas_nonempty g γ)
  rintro _ ⟨u, _, rfl⟩
  exact riemannianDiskArea_nonneg g u

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.leastSpanningArea_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.leastSpanningArea_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.leastSpanningArea_nonneg ``Submission.DifferentialGeometry.Geometry.leastSpanningArea_nonneg

omit [CompactSpace M] [T3Space M] [FiniteDimensional ℝ E] in
theorem leastSpanningArea_le_competitor (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ : lipschitzContractibleLoop g) {u : C(closedDisk, M)}
    (hu : u ∈ spanningDiskCompetitors g γ.val.val) :
    leastSpanningArea g γ ≤ riemannianDiskArea g u :=
  csInf_le (spanningDiskAreas_bddBelow g γ) ⟨u, hu, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.leastSpanningArea_le_competitor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.leastSpanningArea_le_competitor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.leastSpanningArea_le_competitor ``Submission.DifferentialGeometry.Geometry.leastSpanningArea_le_competitor



theorem exists_spanningDisk_area_lt [Nonempty M] [PreconnectedSpace M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (γ : lipschitzContractibleLoop g)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ u ∈ spanningDiskCompetitors g γ.val.val,
      riemannianDiskArea g u < leastSpanningArea g γ + ε := by
  obtain ⟨a, ⟨u, hu, rfl⟩, ha⟩ := exists_lt_of_csInf_lt (spanningDiskAreas_nonempty g γ)
    (show leastSpanningArea g γ < leastSpanningArea g γ + ε by linarith)
  exact ⟨u, hu, ha⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_spanningDisk_area_lt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_spanningDisk_area_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_spanningDisk_area_lt ``Submission.DifferentialGeometry.Geometry.exists_spanningDisk_area_lt

theorem exists_spanningDiskCompetitors_area_tendsto_leastSpanningArea [Nonempty M]
    [PreconnectedSpace M] (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ : lipschitzContractibleLoop g) :
    ∃ uj : ℕ → C(closedDisk, M), (∀ j, uj j ∈ spanningDiskCompetitors g γ.val.val) ∧
      Filter.Tendsto (fun j => riemannianDiskArea g (uj j)) Filter.atTop
        (𝓝 (leastSpanningArea g γ)) := by
  choose u hu hlt using fun j : ℕ =>
    exists_spanningDisk_area_lt g γ (ε := 1 / ((j : ℝ) + 1)) (by positivity)
  refine ⟨u, hu, ?_⟩
  have hb (j : ℕ) : |riemannianDiskArea g (u j) - leastSpanningArea g γ| ≤ 1 / ((j : ℝ) + 1) := by
    have h1 : leastSpanningArea g γ ≤ riemannianDiskArea g (u j) :=
      leastSpanningArea_le_competitor g γ (hu j)
    have h2 : riemannianDiskArea g (u j) < leastSpanningArea g γ + 1 / ((j : ℝ) + 1) := hlt j
    rw [abs_le]
    constructor <;> linarith
  have hnorm : Filter.Tendsto
      (fun j : ℕ => ‖riemannianDiskArea g (u j) - leastSpanningArea g γ‖) Filter.atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun j => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    rw [norm_norm]
    simpa only [Real.norm_eq_abs] using hb j
  exact (tendsto_iff_norm_sub_tendsto_zero).mpr hnorm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_spanningDiskCompetitors_area_tendsto_leastSpanningArea then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_spanningDiskCompetitors_area_tendsto_leastSpanningArea"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_spanningDiskCompetitors_area_tendsto_leastSpanningArea ``Submission.DifferentialGeometry.Geometry.exists_spanningDiskCompetitors_area_tendsto_leastSpanningArea


def constantLipschitzContractibleLoop (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (q : M) :
    lipschitzContractibleLoop g :=
  ⟨ContractibleLoop.constants q, 0, fun _ _ => by
    simp only [ContractibleLoop.constants_apply, riemannianEDistOf_self, ENNReal.coe_zero, _root_.MulZeroClass.zero_mul, le_refl]⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.constantLipschitzContractibleLoop then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.constantLipschitzContractibleLoop"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.constantLipschitzContractibleLoop ``Submission.DifferentialGeometry.Geometry.constantLipschitzContractibleLoop


theorem leastSpanningArea_constant [Nonempty M] [PreconnectedSpace M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (q : M) :
    leastSpanningArea g (constantLipschitzContractibleLoop g q) = 0 := by
  apply le_antisymm _ (leastSpanningArea_nonneg g _)
  have hu : ContinuousMap.const closedDisk q ∈ spanningDiskCompetitors g
      (constantLipschitzContractibleLoop g q).val.val := by
    refine ⟨rfl, 0, fun z w => ?_⟩
    simp only [ContinuousMap.const_apply, riemannianEDistOf_self, ENNReal.coe_zero, _root_.MulZeroClass.zero_mul, le_refl]
  have h := leastSpanningArea_le_competitor g (constantLipschitzContractibleLoop g q) hu
  change leastSpanningArea g (constantLipschitzContractibleLoop g q) ≤
    riemannianDiskArea g (fun _ => q) at h
  rw [riemannianDiskArea_const] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.leastSpanningArea_constant then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.leastSpanningArea_constant"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.leastSpanningArea_constant ``Submission.DifferentialGeometry.Geometry.leastSpanningArea_constant

end DifferentialGeometry.Geometry
