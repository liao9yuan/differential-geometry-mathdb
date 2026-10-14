import Submission.DifferentialGeometry.Geometry.Exponential.NormalCoordinates.Framed
import Mathlib.Data.ENNReal.Real

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection

noncomputable section

open _root_.Set _root_.Function _root_.Filter _root_.Metric _root_.Bundle _root_.Submission.Bundle _root_.Manifold
open scoped _root_.Topology _root_.Manifold _root_.ContDiff _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian

open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Exponential
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open _root_.Submission.DifferentialGeometry.Integral.Measure

section RawExpMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

omit [NeZero (Module.finrank ℝ E)] in
lemma exists_metric_ball_subset_expMapDiffeo_source
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ r₀ : ℝ, 0 < r₀ ∧
      Metric.ball (0 : E) r₀ ⊆ (expMapDiffeo (I := I) g p).source := by
  classical
  have h_open : IsOpen (expMapDiffeo (I := I) g p).source :=
    (expMapDiffeo (I := I) g p).open_source
  have h_mem : (0 : E) ∈ (expMapDiffeo (I := I) g p).source :=
    zero_mem_expMapDiffeo_source (I := I) g p
  exact Metric.isOpen_iff.mp h_open (0 : E) h_mem

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.exists_metric_ball_subset_expMapDiffeo_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.exists_metric_ball_subset_expMapDiffeo_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.exists_metric_ball_subset_expMapDiffeo_source ``Submission.DifferentialGeometry.Geometry.Riemannian.exists_metric_ball_subset_expMapDiffeo_source

omit [NeZero (Module.finrank ℝ E)] in
lemma injOn_expMap_on_expMapDiffeo_source
    (g : SmoothRiemannianMetric I M) (p : M) :
    _root_.Set.InjOn (fun v : E =>
      (expMap (I := I) g p (show TangentSpace I p from v) : M))
      (expMapDiffeo (I := I) g p).source := by
  classical
  have h_inj_diffeo : _root_.Set.InjOn (expMapDiffeo (I := I) g p)
      (expMapDiffeo (I := I) g p).source :=
    (expMapDiffeo (I := I) g p).toPartialEquiv.injOn
  intro v hv w hw hvw
  apply h_inj_diffeo hv hw
  rw [expMapDiffeo_apply_eq (I := I) g p hv,
      expMapDiffeo_apply_eq (I := I) g p hw]
  exact hvw

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.injOn_expMap_on_expMapDiffeo_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.injOn_expMap_on_expMapDiffeo_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.injOn_expMap_on_expMapDiffeo_source ``Submission.DifferentialGeometry.Geometry.Riemannian.injOn_expMap_on_expMapDiffeo_source

end RawExpMap

section GeneralInjectivityRadius

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

def injRadiusSet (g : SmoothRiemannianMetric I M) (p : M) : Set ℝ≥0∞ :=
  { r : ℝ≥0∞ |
    InjOn (fun v : E => (expMap (I := I) g p (show TangentSpace I p from v) : M))
      (Metric.eball (0 : E) r) }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.injRadiusSet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.injRadiusSet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.injRadiusSet ``Submission.DifferentialGeometry.Geometry.Riemannian.injRadiusSet

def injRadius (g : SmoothRiemannianMetric I M) (p : M) : ℝ≥0∞ :=
  sSup (injRadiusSet (I := I) g p)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.injRadius then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.injRadius"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.injRadius ``Submission.DifferentialGeometry.Geometry.Riemannian.injRadius

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E]
  [T2Space (TangentBundle I M)] in
lemma mem_injRadiusSet_iff (g : SmoothRiemannianMetric I M) (p : M)
    {r : ℝ≥0∞} :
    r ∈ injRadiusSet (I := I) g p ↔
      InjOn (fun v : E => (expMap (I := I) g p (show TangentSpace I p from v) : M))
        (Metric.eball (0 : E) r) := Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.mem_injRadiusSet_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.mem_injRadiusSet_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.mem_injRadiusSet_iff ``Submission.DifferentialGeometry.Geometry.Riemannian.mem_injRadiusSet_iff

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E]
  [T2Space (TangentBundle I M)] in
lemma injRadiusSet_downward_closed (g : SmoothRiemannianMetric I M) (p : M)
    {r r' : ℝ≥0∞} (h : r' ≤ r) (hr : r ∈ injRadiusSet (I := I) g p) :
    r' ∈ injRadiusSet (I := I) g p := by
  refine InjOn.mono ?_ hr
  exact Metric.eball_subset_eball h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.injRadiusSet_downward_closed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.injRadiusSet_downward_closed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.injRadiusSet_downward_closed ``Submission.DifferentialGeometry.Geometry.Riemannian.injRadiusSet_downward_closed

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E]
  [T2Space (TangentBundle I M)] in
lemma zero_mem_injRadiusSet (g : SmoothRiemannianMetric I M) (p : M) :
    (0 : ℝ≥0∞) ∈ injRadiusSet (I := I) g p := by
  classical
  change _root_.Set.InjOn _ (Metric.eball (0 : E) (0 : ℝ≥0∞))
  rw [Metric.eball_zero]
  exact Set.injOn_empty _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.zero_mem_injRadiusSet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.zero_mem_injRadiusSet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.zero_mem_injRadiusSet ``Submission.DifferentialGeometry.Geometry.Riemannian.zero_mem_injRadiusSet

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E]
  [T2Space (TangentBundle I M)] in
lemma injRadiusSet_nonempty (g : SmoothRiemannianMetric I M) (p : M) :
    (injRadiusSet (I := I) g p).Nonempty :=
  ⟨0, zero_mem_injRadiusSet (I := I) g p⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.injRadiusSet_nonempty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.injRadiusSet_nonempty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.injRadiusSet_nonempty ``Submission.DifferentialGeometry.Geometry.Riemannian.injRadiusSet_nonempty

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E]
  [T2Space (TangentBundle I M)] in
lemma le_injRadius_of_mem (g : SmoothRiemannianMetric I M) (p : M)
    {r : ℝ≥0∞} (hr : r ∈ injRadiusSet (I := I) g p) :
    r ≤ injRadius (I := I) g p :=
  le_sSup hr

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.le_injRadius_of_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.le_injRadius_of_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.le_injRadius_of_mem ``Submission.DifferentialGeometry.Geometry.Riemannian.le_injRadius_of_mem

omit [NeZero (Module.finrank ℝ E)] in
lemma exists_pos_injOn_metric_ball
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ r₀ : ℝ, 0 < r₀ ∧
      InjOn (fun v : E => (expMap (I := I) g p (show TangentSpace I p from v) : M))
        (Metric.ball (0 : E) r₀) := by
  classical
  obtain ⟨r₀, hr₀_pos, hr₀_sub⟩ :=
    exists_metric_ball_subset_expMapDiffeo_source (I := I) g p
  refine ⟨r₀, hr₀_pos, ?_⟩
  exact (injOn_expMap_on_expMapDiffeo_source (I := I) g p).mono hr₀_sub

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.exists_pos_injOn_metric_ball then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.exists_pos_injOn_metric_ball"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.exists_pos_injOn_metric_ball ``Submission.DifferentialGeometry.Geometry.Riemannian.exists_pos_injOn_metric_ball

omit [NeZero (Module.finrank ℝ E)] in
lemma exists_pos_mem_injRadiusSet (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ r : ℝ≥0∞, 0 < r ∧ r ∈ injRadiusSet (I := I) g p := by
  classical
  obtain ⟨r₀, hr₀_pos, hr₀_inj⟩ :=
    exists_pos_injOn_metric_ball (I := I) g p
  refine ⟨ENNReal.ofReal r₀, ?_, ?_⟩
  · exact ENNReal.ofReal_pos.mpr hr₀_pos
  · change _root_.Set.InjOn _ (Metric.eball (0 : E) (ENNReal.ofReal r₀))
    rw [Metric.eball_ofReal]
    exact hr₀_inj

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.exists_pos_mem_injRadiusSet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.exists_pos_mem_injRadiusSet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.exists_pos_mem_injRadiusSet ``Submission.DifferentialGeometry.Geometry.Riemannian.exists_pos_mem_injRadiusSet

omit [NeZero (Module.finrank ℝ E)] in
theorem injRadius_pos (g : SmoothRiemannianMetric I M) (p : M) :
    0 < injRadius (I := I) g p := by
  classical
  obtain ⟨r, hr_pos, hr_mem⟩ := exists_pos_mem_injRadiusSet (I := I) g p
  exact lt_of_lt_of_le hr_pos (le_injRadius_of_mem (I := I) g p hr_mem)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.injRadius_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.injRadius_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.injRadius_pos ``Submission.DifferentialGeometry.Geometry.Riemannian.injRadius_pos

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E]
  [T2Space (TangentBundle I M)] in
@[simp] lemma injRadius_eq_sSup (g : SmoothRiemannianMetric I M) (p : M) :
    injRadius (I := I) g p = _root_.SupSet.sSup (injRadiusSet (I := I) g p) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.injRadius_eq_sSup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.injRadius_eq_sSup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.injRadius_eq_sSup ``Submission.DifferentialGeometry.Geometry.Riemannian.injRadius_eq_sSup

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E]
  [T2Space (TangentBundle I M)] in
theorem injOn_expMap_eball_of_lt_injRadius
    (g : SmoothRiemannianMetric I M) (p : M) {r : ℝ≥0∞}
    (hr : r < injRadius (I := I) g p) :
    InjOn (fun v : E => (expMap (I := I) g p (show TangentSpace I p from v) : M))
      (Metric.eball (0 : E) r) := by
  classical
  rcases lt_sSup_iff.mp hr with ⟨r', hr'_mem, hr_lt_r'⟩
  have hr_le_r' : r ≤ r' := le_of_lt hr_lt_r'
  exact (mem_injRadiusSet_iff (I := I) g p).mp hr'_mem |>.mono
    (Metric.eball_subset_eball hr_le_r')

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.injOn_expMap_eball_of_lt_injRadius then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.injOn_expMap_eball_of_lt_injRadius"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.injOn_expMap_eball_of_lt_injRadius ``Submission.DifferentialGeometry.Geometry.Riemannian.injOn_expMap_eball_of_lt_injRadius

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E]
  [T2Space (TangentBundle I M)] in
theorem injOn_expMap_ball_of_ofReal_lt_injRadius
    (g : SmoothRiemannianMetric I M) (p : M) {r₀ : ℝ}
    (hr : ENNReal.ofReal r₀ < injRadius (I := I) g p) :
    InjOn (fun v : E => (expMap (I := I) g p (show TangentSpace I p from v) : M))
      (Metric.ball (0 : E) r₀) := by
  classical
  have h := injOn_expMap_eball_of_lt_injRadius (I := I) g p hr
  rwa [Metric.eball_ofReal] at h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.injOn_expMap_ball_of_ofReal_lt_injRadius then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.injOn_expMap_ball_of_ofReal_lt_injRadius"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.injOn_expMap_ball_of_ofReal_lt_injRadius ``Submission.DifferentialGeometry.Geometry.Riemannian.injOn_expMap_ball_of_ofReal_lt_injRadius

omit [NeZero (Module.finrank ℝ E)] in
theorem injRadius_iInf_pos_of_compact_of_lowerSemicontinuous
    (g : SmoothRiemannianMetric I M) [CompactSpace M] [Nonempty M]
    (h_lsc : LowerSemicontinuous (fun p : M => injRadius (I := I) g p)) :
    0 < ⨅ p : M, injRadius (I := I) g p := by
  classical
  have h_lsc_on : LowerSemicontinuousOn (fun p : M => injRadius (I := I) g p)
      Set.univ := lowerSemicontinuousOn_univ_iff.mpr h_lsc
  obtain ⟨p₀, _hp₀_mem, h_min⟩ :=
    LowerSemicontinuousOn.exists_isMinOn (f := fun p : M => injRadius (I := I) g p)
      (s := (Set.univ : Set M)) Set.univ_nonempty isCompact_univ h_lsc_on
  have h_iInf_eq : ⨅ p : M, injRadius (I := I) g p = injRadius (I := I) g p₀ := by
    apply le_antisymm
    · exact iInf_le _ p₀
    · refine le_iInf fun p => ?_
      have := h_min (Set.mem_univ p)
      simpa using this
  rw [h_iInf_eq]
  exact injRadius_pos (I := I) g p₀

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.injRadius_iInf_pos_of_compact_of_lowerSemicontinuous then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.injRadius_iInf_pos_of_compact_of_lowerSemicontinuous"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.injRadius_iInf_pos_of_compact_of_lowerSemicontinuous ``Submission.DifferentialGeometry.Geometry.Riemannian.injRadius_iInf_pos_of_compact_of_lowerSemicontinuous

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_uniform_injectivity_radius_of_lowerSemicontinuous
    (g : SmoothRiemannianMetric I M) [CompactSpace M] [Nonempty M]
    (h_lsc : LowerSemicontinuous (fun p : M => injRadius (I := I) g p)) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ p : M,
      InjOn (fun v : E => (expMap (I := I) g p (show TangentSpace I p from v) : M))
        (Metric.ball (0 : E) r₀) := by
  classical
  have h_inf_pos := injRadius_iInf_pos_of_compact_of_lowerSemicontinuous
    (I := I) g h_lsc
  set R : ℝ≥0∞ := ⨅ p : M, injRadius (I := I) g p with hR_def
  by_cases hRtop : R = (⊤ : ℝ≥0∞)
  · refine ⟨1, one_pos, fun p => ?_⟩
    have h_le_inf : R ≤ injRadius (I := I) g p := by
      rw [hR_def]; exact iInf_le _ p
    have h_lt : ENNReal.ofReal 1 < injRadius (I := I) g p := by
      rw [hRtop] at h_le_inf
      have : ENNReal.ofReal 1 < (⊤ : ℝ≥0∞) := ENNReal.ofReal_lt_top
      exact lt_of_lt_of_le this h_le_inf
    exact injOn_expMap_ball_of_ofReal_lt_injRadius (I := I) g p h_lt
  · have hR_ne_top : R ≠ (⊤ : ℝ≥0∞) := hRtop
    have hR_pos : 0 < R := h_inf_pos
    have hR_toReal_pos : 0 < R.toReal := by
      rw [ENNReal.toReal_pos_iff]
      exact ⟨hR_pos, lt_top_iff_ne_top.mpr hR_ne_top⟩
    refine ⟨R.toReal / 2, by positivity, fun p => ?_⟩
    have h_le_inf : R ≤ injRadius (I := I) g p := by
      rw [hR_def]; exact iInf_le _ p
    have h_ofReal_lt_R : ENNReal.ofReal (R.toReal / 2) < R := by
      have hhalf_lt : R.toReal / 2 < R.toReal := by linarith
      calc ENNReal.ofReal (R.toReal / 2)
          < ENNReal.ofReal R.toReal := by
            exact (ENNReal.ofReal_lt_ofReal_iff hR_toReal_pos).mpr hhalf_lt
        _ = R := ENNReal.ofReal_toReal hR_ne_top
    have h_lt : ENNReal.ofReal (R.toReal / 2) < injRadius (I := I) g p :=
      lt_of_lt_of_le h_ofReal_lt_R h_le_inf
    exact injOn_expMap_ball_of_ofReal_lt_injRadius (I := I) g p h_lt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.exists_uniform_injectivity_radius_of_lowerSemicontinuous then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.exists_uniform_injectivity_radius_of_lowerSemicontinuous"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.exists_uniform_injectivity_radius_of_lowerSemicontinuous ``Submission.DifferentialGeometry.Geometry.Riemannian.exists_uniform_injectivity_radius_of_lowerSemicontinuous

end GeneralInjectivityRadius

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

section InjectivityRadius

variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

def framedInjRadiusSet (g : SmoothRiemannianMetric I M) (p : M) : Set ℝ≥0∞ :=
  { r : ℝ≥0∞ |
    InjOn (framedExpMap (I := I) g p) (Metric.eball (0 : E) r) }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.framedInjRadiusSet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.framedInjRadiusSet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.framedInjRadiusSet ``Submission.DifferentialGeometry.Geometry.Riemannian.framedInjRadiusSet

def framedInjRadius (g : SmoothRiemannianMetric I M) (p : M) : ℝ≥0∞ :=
  sSup (framedInjRadiusSet (I := I) g p)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.framedInjRadius then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.framedInjRadius"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.framedInjRadius ``Submission.DifferentialGeometry.Geometry.Riemannian.framedInjRadius

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E]
    [T2Space (TangentBundle I M)] in
lemma mem_framedInjRadiusSet_iff (g : SmoothRiemannianMetric I M) (p : M)
    {r : ℝ≥0∞} :
    r ∈ framedInjRadiusSet (I := I) g p ↔
      InjOn (framedExpMap (I := I) g p) (Metric.eball (0 : E) r) := Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.mem_framedInjRadiusSet_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.mem_framedInjRadiusSet_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.mem_framedInjRadiusSet_iff ``Submission.DifferentialGeometry.Geometry.Riemannian.mem_framedInjRadiusSet_iff

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E]
    [T2Space (TangentBundle I M)] in
lemma framedInjRadiusSet_downward_closed (g : SmoothRiemannianMetric I M) (p : M)
    {r r' : ℝ≥0∞} (h : r' ≤ r) (hr : r ∈ framedInjRadiusSet (I := I) g p) :
    r' ∈ framedInjRadiusSet (I := I) g p := by
  refine InjOn.mono ?_ hr
  exact Metric.eball_subset_eball h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.framedInjRadiusSet_downward_closed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.framedInjRadiusSet_downward_closed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.framedInjRadiusSet_downward_closed ``Submission.DifferentialGeometry.Geometry.Riemannian.framedInjRadiusSet_downward_closed

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E]
    [T2Space (TangentBundle I M)] in
lemma zero_mem_framedInjRadiusSet (g : SmoothRiemannianMetric I M) (p : M) :
    (0 : ℝ≥0∞) ∈ framedInjRadiusSet (I := I) g p := by
  classical
  change _root_.Set.InjOn (framedExpMap (I := I) g p)
    (Metric.eball (0 : E) (0 : ℝ≥0∞))
  rw [Metric.eball_zero]
  exact Set.injOn_empty _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.zero_mem_framedInjRadiusSet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.zero_mem_framedInjRadiusSet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.zero_mem_framedInjRadiusSet ``Submission.DifferentialGeometry.Geometry.Riemannian.zero_mem_framedInjRadiusSet

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E]
    [T2Space (TangentBundle I M)] in
lemma framedInjRadiusSet_nonempty (g : SmoothRiemannianMetric I M) (p : M) :
    (framedInjRadiusSet (I := I) g p).Nonempty :=
  ⟨0, zero_mem_framedInjRadiusSet (I := I) g p⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.framedInjRadiusSet_nonempty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.framedInjRadiusSet_nonempty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.framedInjRadiusSet_nonempty ``Submission.DifferentialGeometry.Geometry.Riemannian.framedInjRadiusSet_nonempty

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E]
    [T2Space (TangentBundle I M)] in
lemma le_framedInjRadius_of_mem (g : SmoothRiemannianMetric I M) (p : M)
    {r : ℝ≥0∞} (hr : r ∈ framedInjRadiusSet (I := I) g p) :
    r ≤ framedInjRadius (I := I) g p :=
  le_sSup hr

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.le_framedInjRadius_of_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.le_framedInjRadius_of_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.le_framedInjRadius_of_mem ``Submission.DifferentialGeometry.Geometry.Riemannian.le_framedInjRadius_of_mem

omit [NeZero (Module.finrank ℝ E)] in
lemma exists_framed_ball (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ r₀ : ℝ, 0 < r₀ ∧
      Metric.ball (0 : E) r₀ ⊆ (framedExpDiffeo (I := I) g p).source := by
  have h_open : IsOpen (framedExpDiffeo (I := I) g p).source :=
    (framedExpDiffeo (I := I) g p).open_source
  have h_mem : (0 : E) ∈ (framedExpDiffeo (I := I) g p).source :=
    zero_mem_framedExp_source (I := I) g p
  exact Metric.isOpen_iff.mp h_open (0 : E) h_mem

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.exists_framed_ball then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.exists_framed_ball"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.exists_framed_ball ``Submission.DifferentialGeometry.Geometry.Riemannian.exists_framed_ball

omit [NeZero (Module.finrank ℝ E)] in
lemma injOn_framed_source (g : SmoothRiemannianMetric I M) (p : M) :
    InjOn (framedExpMap (I := I) g p)
      (framedExpDiffeo (I := I) g p).source := by
  have h_inj : _root_.Set.InjOn (framedExpDiffeo (I := I) g p)
      (framedExpDiffeo (I := I) g p).source :=
    (framedExpDiffeo (I := I) g p).toPartialEquiv.injOn
  intro v hv w hw hvw
  apply h_inj hv hw
  rw [framedExp_eq_expMap (I := I) g p hv,
    framedExp_eq_expMap (I := I) g p hw]
  exact hvw

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.injOn_framed_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.injOn_framed_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.injOn_framed_source ``Submission.DifferentialGeometry.Geometry.Riemannian.injOn_framed_source

omit [NeZero (Module.finrank ℝ E)] in
lemma exists_pos_injOn_framedExpMap_metric_ball
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ r₀ : ℝ, 0 < r₀ ∧
      InjOn (framedExpMap (I := I) g p) (Metric.ball (0 : E) r₀) := by
  classical
  obtain ⟨r₀, hr₀_pos, hr₀_sub⟩ :=
    exists_framed_ball (I := I) g p
  refine ⟨r₀, hr₀_pos, ?_⟩
  exact (injOn_framed_source (I := I) g p).mono hr₀_sub

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.exists_pos_injOn_framedExpMap_metric_ball then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.exists_pos_injOn_framedExpMap_metric_ball"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.exists_pos_injOn_framedExpMap_metric_ball ``Submission.DifferentialGeometry.Geometry.Riemannian.exists_pos_injOn_framedExpMap_metric_ball

omit [NeZero (Module.finrank ℝ E)] in
lemma exists_pos_mem_framedInjRadiusSet (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ r : ℝ≥0∞, 0 < r ∧ r ∈ framedInjRadiusSet (I := I) g p := by
  classical
  obtain ⟨r₀, hr₀_pos, hr₀_inj⟩ :=
    exists_pos_injOn_framedExpMap_metric_ball (I := I) g p
  refine ⟨ENNReal.ofReal r₀, ?_, ?_⟩
  · exact ENNReal.ofReal_pos.mpr hr₀_pos
  · change _root_.Set.InjOn _ (Metric.eball (0 : E) (ENNReal.ofReal r₀))
    rw [Metric.eball_ofReal]
    exact hr₀_inj

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.exists_pos_mem_framedInjRadiusSet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.exists_pos_mem_framedInjRadiusSet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.exists_pos_mem_framedInjRadiusSet ``Submission.DifferentialGeometry.Geometry.Riemannian.exists_pos_mem_framedInjRadiusSet

omit [NeZero (Module.finrank ℝ E)] in
theorem framedInjRadius_pos (g : SmoothRiemannianMetric I M) (p : M) :
    0 < framedInjRadius (I := I) g p := by
  classical
  obtain ⟨r, hr_pos, hr_mem⟩ := exists_pos_mem_framedInjRadiusSet (I := I) g p
  exact lt_of_lt_of_le hr_pos (le_framedInjRadius_of_mem (I := I) g p hr_mem)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.framedInjRadius_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.framedInjRadius_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.framedInjRadius_pos ``Submission.DifferentialGeometry.Geometry.Riemannian.framedInjRadius_pos

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E]
  [T2Space (TangentBundle I M)] in
@[simp] lemma framedInjRadius_eq_sSup (g : SmoothRiemannianMetric I M) (p : M) :
    framedInjRadius (I := I) g p = _root_.SupSet.sSup (framedInjRadiusSet (I := I) g p) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.framedInjRadius_eq_sSup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.framedInjRadius_eq_sSup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.framedInjRadius_eq_sSup ``Submission.DifferentialGeometry.Geometry.Riemannian.framedInjRadius_eq_sSup
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E]
    [T2Space (TangentBundle I M)] in
theorem injOn_framedExpMap_eball_of_lt_framedInjRadius
    (g : SmoothRiemannianMetric I M) (p : M) {r : ℝ≥0∞}
    (hr : r < framedInjRadius (I := I) g p) :
    InjOn (framedExpMap (I := I) g p) (Metric.eball (0 : E) r) := by
  classical
  rcases lt_sSup_iff.mp hr with ⟨r', hr'_mem, hr_lt_r'⟩
  have hr_le_r' : r ≤ r' := le_of_lt hr_lt_r'
  exact (mem_framedInjRadiusSet_iff (I := I) g p).mp hr'_mem |>.mono
    (Metric.eball_subset_eball hr_le_r')

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.injOn_framedExpMap_eball_of_lt_framedInjRadius then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.injOn_framedExpMap_eball_of_lt_framedInjRadius"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.injOn_framedExpMap_eball_of_lt_framedInjRadius ``Submission.DifferentialGeometry.Geometry.Riemannian.injOn_framedExpMap_eball_of_lt_framedInjRadius
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E]
    [T2Space (TangentBundle I M)] in
theorem injOn_framedExpMap_ball_of_ofReal_lt_framedInjRadius
    (g : SmoothRiemannianMetric I M) (p : M) {r₀ : ℝ}
    (hr : ENNReal.ofReal r₀ < framedInjRadius (I := I) g p) :
    InjOn (framedExpMap (I := I) g p) (Metric.ball (0 : E) r₀) := by
  classical
  have h := injOn_framedExpMap_eball_of_lt_framedInjRadius (I := I) g p hr
  rwa [Metric.eball_ofReal] at h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.injOn_framedExpMap_ball_of_ofReal_lt_framedInjRadius then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.injOn_framedExpMap_ball_of_ofReal_lt_framedInjRadius"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.injOn_framedExpMap_ball_of_ofReal_lt_framedInjRadius ``Submission.DifferentialGeometry.Geometry.Riemannian.injOn_framedExpMap_ball_of_ofReal_lt_framedInjRadius

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
theorem exp_dom_of_inj
    (g : SmoothRiemannianMetric I M) (p : M) {r : ℝ}
    (hinj : _root_.Set.InjOn (framedExpMap (I := I) g p) (Metric.ball (0 : E) r))
    {z : E} (hz : z ∈ Metric.ball (0 : E) r) :
    normalFrame (I := I) g p z ∈ expDomain (I := I) g p := by
  classical
  by_cases hz0 : z = 0
  · subst z
    simpa using zero_mem_expDomain (I := I) g p
  · by_contra hdom
    have hr : 0 < r :=
      (dist_nonneg.trans_lt (Metric.mem_ball.mp hz))
    have hzero : (0 : E) ∈ Metric.ball (0 : E) r :=
      Metric.mem_ball_self hr
    apply hz0
    apply hinj hz hzero
    rw [framedExpMap_apply, framedExpMap_apply, map_zero,
      expMap_of_not_mem_expDomain (I := I) hdom, expMap_zero (I := I) g p]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.exp_dom_of_inj then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.exp_dom_of_inj"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.exp_dom_of_inj ``Submission.DifferentialGeometry.Geometry.Riemannian.exp_dom_of_inj

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
theorem exp_dom_of_framedInjRadius
    (g : SmoothRiemannianMetric I M) (p : M) {r : ℝ}
    (hr : ENNReal.ofReal r < framedInjRadius (I := I) g p)
    {z : E} (hz : z ∈ Metric.ball (0 : E) r) :
    normalFrame (I := I) g p z ∈ expDomain (I := I) g p :=
  exp_dom_of_inj (I := I) g p
    (injOn_framedExpMap_ball_of_ofReal_lt_framedInjRadius (I := I) g p hr) hz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.exp_dom_of_framedInjRadius then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.exp_dom_of_framedInjRadius"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.exp_dom_of_framedInjRadius ``Submission.DifferentialGeometry.Geometry.Riemannian.exp_dom_of_framedInjRadius

omit [NeZero (Module.finrank ℝ E)] in
theorem framedInjRadius_iInf_pos_of_compact_of_lowerSemicontinuous
    (g : SmoothRiemannianMetric I M) [CompactSpace M] [Nonempty M]
    (h_lsc : LowerSemicontinuous (fun p : M => framedInjRadius (I := I) g p)) :
    0 < ⨅ p : M, framedInjRadius (I := I) g p := by
  classical
  have h_lsc_on : LowerSemicontinuousOn (fun p : M => framedInjRadius (I := I) g p)
      Set.univ := lowerSemicontinuousOn_univ_iff.mpr h_lsc
  obtain ⟨p₀, _hp₀_mem, h_min⟩ :=
    LowerSemicontinuousOn.exists_isMinOn (f := fun p : M => framedInjRadius (I := I) g p)
      (s := (Set.univ : Set M)) Set.univ_nonempty isCompact_univ h_lsc_on
  have h_iInf_eq : ⨅ p : M, framedInjRadius (I := I) g p =
      framedInjRadius (I := I) g p₀ := by
    apply le_antisymm
    · exact iInf_le _ p₀
    · refine le_iInf fun p => ?_
      have := h_min (Set.mem_univ p)
      simpa using this
  rw [h_iInf_eq]
  exact framedInjRadius_pos (I := I) g p₀

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.framedInjRadius_iInf_pos_of_compact_of_lowerSemicontinuous then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.framedInjRadius_iInf_pos_of_compact_of_lowerSemicontinuous"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.framedInjRadius_iInf_pos_of_compact_of_lowerSemicontinuous ``Submission.DifferentialGeometry.Geometry.Riemannian.framedInjRadius_iInf_pos_of_compact_of_lowerSemicontinuous

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_uniform_framedInjRadius_of_lowerSemicontinuous
    (g : SmoothRiemannianMetric I M) [CompactSpace M] [Nonempty M]
    (h_lsc : LowerSemicontinuous (fun p : M => framedInjRadius (I := I) g p)) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ p : M,
      InjOn (framedExpMap (I := I) g p) (Metric.ball (0 : E) r₀) := by
  classical
  have h_inf_pos := framedInjRadius_iInf_pos_of_compact_of_lowerSemicontinuous
    (I := I) g h_lsc
  set R : ℝ≥0∞ := ⨅ p : M, framedInjRadius (I := I) g p with hR_def
  by_cases hRtop : R = (⊤ : ℝ≥0∞)
  · refine ⟨1, one_pos, fun p => ?_⟩
    have h_le_inf : R ≤ framedInjRadius (I := I) g p := by
      rw [hR_def]; exact iInf_le _ p
    have h_lt : ENNReal.ofReal 1 < framedInjRadius (I := I) g p := by
      rw [hRtop] at h_le_inf
      have : ENNReal.ofReal 1 < (⊤ : ℝ≥0∞) := ENNReal.ofReal_lt_top
      exact lt_of_lt_of_le this h_le_inf
    exact injOn_framedExpMap_ball_of_ofReal_lt_framedInjRadius (I := I) g p h_lt
  · have hR_ne_top : R ≠ (⊤ : ℝ≥0∞) := hRtop
    have hR_pos : 0 < R := h_inf_pos
    have hR_toReal_pos : 0 < R.toReal := by
      rw [ENNReal.toReal_pos_iff]
      exact ⟨hR_pos, lt_top_iff_ne_top.mpr hR_ne_top⟩
    refine ⟨R.toReal / 2, by positivity, fun p => ?_⟩
    have h_le_inf : R ≤ framedInjRadius (I := I) g p := by
      rw [hR_def]; exact iInf_le _ p
    have h_ofReal_lt_R : ENNReal.ofReal (R.toReal / 2) < R := by
      have hhalf_lt : R.toReal / 2 < R.toReal := by linarith
      calc ENNReal.ofReal (R.toReal / 2)
          < ENNReal.ofReal R.toReal := by
            exact (ENNReal.ofReal_lt_ofReal_iff hR_toReal_pos).mpr hhalf_lt
        _ = R := ENNReal.ofReal_toReal hR_ne_top
    have h_lt : ENNReal.ofReal (R.toReal / 2) < framedInjRadius (I := I) g p :=
      lt_of_lt_of_le h_ofReal_lt_R h_le_inf
    exact injOn_framedExpMap_ball_of_ofReal_lt_framedInjRadius (I := I) g p h_lt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.exists_uniform_framedInjRadius_of_lowerSemicontinuous then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.exists_uniform_framedInjRadius_of_lowerSemicontinuous"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.exists_uniform_framedInjRadius_of_lowerSemicontinuous ``Submission.DifferentialGeometry.Geometry.Riemannian.exists_uniform_framedInjRadius_of_lowerSemicontinuous

end InjectivityRadius

end Riemannian
end Geometry
end DifferentialGeometry

end
