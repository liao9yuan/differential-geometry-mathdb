import Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Tensor

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem tensorChartComp_eq_zero_of_notMem_finset
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) {α : M}
    (hα : α ∉ chartAtlasPOUFinset (I := I) (M := M))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComp (I := I) (M := M) g r s T α Idx Jdx = (fun _ => (0 : ℝ)) := by
  have hρ_zero : ∀ x : M, (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x = 0 :=
    fun x => chartAtlasPOU_weight_zero_of_notMem (I := I) (M := M) hα x
  funext y
  by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
  · rw [tensorChartComp_apply_of_mem (I := I) (M := M) g r s T α Idx Jdx hy]
    unfold tensorChartComponentPou
    rw [hρ_zero]
    ring
  · exact tensorChartComp_apply_of_notMem (I := I) (M := M) g r s T α Idx Jdx hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartComp_eq_zero_of_notMem_finset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartComp_eq_zero_of_notMem_finset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartComp_eq_zero_of_notMem_finset ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartComp_eq_zero_of_notMem_finset

omit [NeZero (Module.finrank ℝ E)] in
theorem wtwokTwoNorm_chartTerm_eq_zero_of_notMem_finset
    (g : SmoothRiemannianMetric I M) {r s : ℕ} (k : ℕ)
    (T : SmoothCcTensor g r s) {α : M}
    (hα : α ∉ chartAtlasPOUFinset (I := I) (M := M)) :
    (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
      ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (2 * k) 2
          (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
          (chartTargetEuclid (I := I) (M := M) α)) = 0 := by
  refine Finset.sum_eq_zero ?_
  intro Idx _
  refine Finset.sum_eq_zero ?_
  intro Jdx _
  rw [tensorChartComp_eq_zero_of_notMem_finset (I := I) (M := M) g r s T hα Idx Jdx]
  exact wkpNorm_zero_fun_zero (d := Module.finrank ℝ E) (by norm_num)
    (chartTargetEuclid_isOpen (I := I) (M := M) α)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoNorm_chartTerm_eq_zero_of_notMem_finset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoNorm_chartTerm_eq_zero_of_notMem_finset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoNorm_chartTerm_eq_zero_of_notMem_finset ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoNorm_chartTerm_eq_zero_of_notMem_finset

omit [NeZero (Module.finrank ℝ E)] in
theorem memWkp_tensorChartComp_of_notMem_finset
    (g : SmoothRiemannianMetric I M) {r s : ℕ} (k : ℕ)
    (T : SmoothCcTensor g r s) {α : M}
    (hα : α ∉ chartAtlasPOUFinset (I := I) (M := M))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    MemWkp (d := Module.finrank ℝ E) (2 * k) 2
      (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α) := by
  rw [tensorChartComp_eq_zero_of_notMem_finset (I := I) (M := M) g r s T hα Idx Jdx]
  exact MemWkp_zero_fun (d := Module.finrank ℝ E) (by norm_num)
    (chartTargetEuclid_isOpen (I := I) (M := M) α)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Tensor.memWkp_tensorChartComp_of_notMem_finset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Tensor.memWkp_tensorChartComp_of_notMem_finset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Tensor.memWkp_tensorChartComp_of_notMem_finset ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.memWkp_tensorChartComp_of_notMem_finset

omit [NeZero (Module.finrank ℝ E)] in
theorem MemWtwokTwo_iff_forall_finset
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (k : ℕ) (T : SmoothCcTensor g r s) :
    MemWtwokTwo (I := I) (M := M) g k T ↔
      ∀ α ∈ chartAtlasPOUFinset (I := I) (M := M),
        ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
          (Jdx : Fin s → Fin (Module.finrank ℝ E)),
          MemWkp (d := Module.finrank ℝ E) (2 * k) 2
            (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
            (chartTargetEuclid (I := I) (M := M) α) := by
  constructor
  · intro hT α _ Idx Jdx
    exact hT α Idx Jdx
  · intro hT α Idx Jdx
    by_cases hα : α ∈ chartAtlasPOUFinset (I := I) (M := M)
    · exact hT α hα Idx Jdx
    · exact memWkp_tensorChartComp_of_notMem_finset
        (I := I) (M := M) g k T hα Idx Jdx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Tensor.MemWtwokTwo_iff_forall_finset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Tensor.MemWtwokTwo_iff_forall_finset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Tensor.MemWtwokTwo_iff_forall_finset ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.MemWtwokTwo_iff_forall_finset

omit [NeZero (Module.finrank ℝ E)] in
theorem MemWtwokTwo_of_forall_finset_memWkp
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (k : ℕ) (T : SmoothCcTensor g r s)
    (hT : ∀ α ∈ chartAtlasPOUFinset (I := I) (M := M),
      ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        MemWkp (d := Module.finrank ℝ E) (2 * k) 2
          (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
          (chartTargetEuclid (I := I) (M := M) α)) :
    MemWtwokTwo (I := I) (M := M) g k T :=
  (MemWtwokTwo_iff_forall_finset (I := I) (M := M) g k T).mpr hT

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Tensor.MemWtwokTwo_of_forall_finset_memWkp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Tensor.MemWtwokTwo_of_forall_finset_memWkp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Tensor.MemWtwokTwo_of_forall_finset_memWkp ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.MemWtwokTwo_of_forall_finset_memWkp

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [CompactSpace M] in
theorem MemWtwokTwo.memWkp_chartComp_finset
    {g : SmoothRiemannianMetric I M} {r s : ℕ} {k : ℕ}
    {T : SmoothCcTensor g r s}
    (hT : MemWtwokTwo (I := I) (M := M) g k T)
    {α : M} (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    MemWkp (d := Module.finrank ℝ E) (2 * k) 2
      (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α) :=
  hT α Idx Jdx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Tensor.MemWtwokTwo.memWkp_chartComp_finset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Tensor.MemWtwokTwo.memWkp_chartComp_finset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Tensor.MemWtwokTwo.memWkp_chartComp_finset ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.MemWtwokTwo.memWkp_chartComp_finset

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem MemWtwokTwo.memWkp_chartComp
    {g : SmoothRiemannianMetric I M} {r s : ℕ} {k : ℕ}
    {T : SmoothCcTensor g r s}
    (hT : MemWtwokTwo (I := I) (M := M) g k T)
    (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    MemWkp (d := Module.finrank ℝ E) (2 * k) 2
      (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α) :=
  hT α Idx Jdx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Tensor.MemWtwokTwo.memWkp_chartComp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Tensor.MemWtwokTwo.memWkp_chartComp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Tensor.MemWtwokTwo.memWkp_chartComp ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.MemWtwokTwo.memWkp_chartComp

omit [NeZero (Module.finrank ℝ E)] in
theorem wtwokTwoNorm_eq_finset_sum
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (k : ℕ) (T : SmoothCcTensor g r s) :
    wtwokTwoNorm (I := I) (M := M) g k T =
      ∑ α ∈ chartAtlasPOUFinset (I := I) (M := M),
        ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (2 * k) 2
              (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
              (chartTargetEuclid (I := I) (M := M) α) := by
  unfold wtwokTwoNorm
  rw [tsum_eq_sum]
  intro α hα
  exact wtwokTwoNorm_chartTerm_eq_zero_of_notMem_finset
    (I := I) (M := M) g k T hα

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoNorm_eq_finset_sum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoNorm_eq_finset_sum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoNorm_eq_finset_sum ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoNorm_eq_finset_sum

def wtwokTwoChartTerm
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (k : ℕ) (T : SmoothCcTensor g r s) (α : M) : ℝ≥0∞ :=
  ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
    ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (2 * k) 2
        (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
        (chartTargetEuclid (I := I) (M := M) α)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoChartTerm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoChartTerm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoChartTerm ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoChartTerm

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
@[simp] lemma wtwokTwoChartTerm_def
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (k : ℕ) (T : SmoothCcTensor g r s) (α : M) :
    wtwokTwoChartTerm (I := I) (M := M) g k T α =
      ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
        ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (2 * k) 2
            (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
            (chartTargetEuclid (I := I) (M := M) α) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoChartTerm_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoChartTerm_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoChartTerm_def ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoChartTerm_def

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem wtwokTwoChartTerm_lt_top
    (g : SmoothRiemannianMetric I M) {r s : ℕ} {k : ℕ}
    {T : SmoothCcTensor g r s}
    (hT : MemWtwokTwo (I := I) (M := M) g k T) (α : M) :
    wtwokTwoChartTerm (I := I) (M := M) g k T α < ⊤ := by
  rw [wtwokTwoChartTerm_def]
  refine ENNReal.sum_lt_top.mpr ?_
  intro Idx _
  refine ENNReal.sum_lt_top.mpr ?_
  intro Jdx _
  exact wkpNorm_lt_top_of_memWkp (d := Module.finrank ℝ E) (hT α Idx Jdx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoChartTerm_lt_top then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoChartTerm_lt_top"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoChartTerm_lt_top ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoChartTerm_lt_top

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem wtwokTwoChartTerm_ne_top
    (g : SmoothRiemannianMetric I M) {r s : ℕ} {k : ℕ}
    {T : SmoothCcTensor g r s}
    (hT : MemWtwokTwo (I := I) (M := M) g k T) (α : M) :
    wtwokTwoChartTerm (I := I) (M := M) g k T α ≠ ⊤ :=
  (wtwokTwoChartTerm_lt_top (I := I) (M := M) g hT α).ne

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoChartTerm_ne_top then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoChartTerm_ne_top"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoChartTerm_ne_top ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoChartTerm_ne_top

omit [NeZero (Module.finrank ℝ E)] in
theorem wtwokTwoNorm_eq_finset_sum_chartTerm
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (k : ℕ) (T : SmoothCcTensor g r s) :
    wtwokTwoNorm (I := I) (M := M) g k T =
      ∑ α ∈ chartAtlasPOUFinset (I := I) (M := M),
        wtwokTwoChartTerm (I := I) (M := M) g k T α := by
  rw [wtwokTwoNorm_eq_finset_sum (I := I) (M := M) g k T]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoNorm_eq_finset_sum_chartTerm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoNorm_eq_finset_sum_chartTerm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoNorm_eq_finset_sum_chartTerm ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoNorm_eq_finset_sum_chartTerm

omit [NeZero (Module.finrank ℝ E)] in
theorem wtwokTwoChartTerm_le_wtwokTwoNorm
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (k : ℕ) (T : SmoothCcTensor g r s) {α : M}
    (hα : α ∈ chartAtlasPOUFinset (I := I) (M := M)) :
    wtwokTwoChartTerm (I := I) (M := M) g k T α ≤
      wtwokTwoNorm (I := I) (M := M) g k T := by
  rw [wtwokTwoNorm_eq_finset_sum_chartTerm (I := I) (M := M) g k T]
  exact Finset.single_le_sum
    (f := fun α => wtwokTwoChartTerm (I := I) (M := M) g k T α)
    (fun α _ => zero_le) hα

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoChartTerm_le_wtwokTwoNorm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoChartTerm_le_wtwokTwoNorm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoChartTerm_le_wtwokTwoNorm ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoChartTerm_le_wtwokTwoNorm

omit [NeZero (Module.finrank ℝ E)] in
theorem wkpNorm_tensorChartComp_le_wtwokTwoNorm
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (k : ℕ) (T : SmoothCcTensor g r s) {α : M}
    (hα : α ∈ chartAtlasPOUFinset (I := I) (M := M))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (2 * k) 2
        (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
        (chartTargetEuclid (I := I) (M := M) α) ≤
      wtwokTwoNorm (I := I) (M := M) g k T := by
  refine le_trans ?_ (wtwokTwoChartTerm_le_wtwokTwoNorm (I := I) (M := M) g k T hα)
  rw [wtwokTwoChartTerm_def]
  refine le_trans ?_ (Finset.single_le_sum
    (f := fun Idx => ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (2 * k) 2
        (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
        (chartTargetEuclid (I := I) (M := M) α))
    (fun Idx _ => zero_le) (Finset.mem_univ Idx))
  exact Finset.single_le_sum
    (f := fun Jdx => iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (2 * k) 2
      (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α))
    (fun Jdx _ => zero_le) (Finset.mem_univ Jdx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Tensor.wkpNorm_tensorChartComp_le_wtwokTwoNorm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Tensor.wkpNorm_tensorChartComp_le_wtwokTwoNorm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Tensor.wkpNorm_tensorChartComp_le_wtwokTwoNorm ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.wkpNorm_tensorChartComp_le_wtwokTwoNorm

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem tensorChartComp_reconstruct
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    tensorChartPushed (I := I) (M := M) g r s T α y =
      ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
        ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
          tensorChartComp (I := I) (M := M) g r s T α Idx Jdx y •
            tensorChartBasisElement (E := E) r s Idx Jdx :=
  tensorChartPushed_eq_sum_tensorChartComp (I := I) (M := M) g r s T α y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartComp_reconstruct then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartComp_reconstruct"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartComp_reconstruct ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartComp_reconstruct

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem tensorChartPushed_eqOn_zero_of_tensorChartComp_eqOn_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (h : ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
      Set.EqOn (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
        (fun _ => (0 : ℝ)) (chartTargetEuclid (I := I) (M := M) α)) :
    Set.EqOn (tensorChartPushed (I := I) (M := M) g r s T α)
      (fun _ => (0 : TensorRSModel r s ℝ E))
      (chartTargetEuclid (I := I) (M := M) α) := by
  intro y hy
  rw [tensorChartComp_reconstruct (I := I) (M := M) g r s T α y]
  refine Finset.sum_eq_zero ?_
  intro Idx _
  refine Finset.sum_eq_zero ?_
  intro Jdx _
  rw [h Idx Jdx hy, zero_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartPushed_eqOn_zero_of_tensorChartComp_eqOn_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartPushed_eqOn_zero_of_tensorChartComp_eqOn_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartPushed_eqOn_zero_of_tensorChartComp_eqOn_zero ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartPushed_eqOn_zero_of_tensorChartComp_eqOn_zero

omit [NeZero (Module.finrank ℝ E)] in
theorem wtwokTwoNormReal_eq_finset_sum_toReal
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (k : ℕ) (T : SmoothCcTensor g r s) :
    wtwokTwoNormReal (I := I) (M := M) g k T =
      (∑ α ∈ chartAtlasPOUFinset (I := I) (M := M),
        wtwokTwoChartTerm (I := I) (M := M) g k T α).toReal := by
  unfold wtwokTwoNormReal
  rw [wtwokTwoNorm_eq_finset_sum_chartTerm (I := I) (M := M) g k T]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoNormReal_eq_finset_sum_toReal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoNormReal_eq_finset_sum_toReal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoNormReal_eq_finset_sum_toReal ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoNormReal_eq_finset_sum_toReal

omit [NeZero (Module.finrank ℝ E)] in
theorem wtwokTwoNormReal_le_finset_sum
    (g : SmoothRiemannianMetric I M) {r s : ℕ} {k : ℕ}
    {T : SmoothCcTensor g r s}
    (hT : MemWtwokTwo (I := I) (M := M) g k T) :
    wtwokTwoNormReal (I := I) (M := M) g k T ≤
      ∑ α ∈ chartAtlasPOUFinset (I := I) (M := M),
        (wtwokTwoChartTerm (I := I) (M := M) g k T α).toReal := by
  rw [wtwokTwoNormReal_eq_finset_sum_toReal (I := I) (M := M) g k T]
  rw [ENNReal.toReal_sum]
  intro α _
  exact wtwokTwoChartTerm_ne_top (I := I) (M := M) g hT α

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoNormReal_le_finset_sum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoNormReal_le_finset_sum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoNormReal_le_finset_sum ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoNormReal_le_finset_sum

omit [NeZero (Module.finrank ℝ E)] in
theorem wtwokTwoNormReal_ge_finset_sum
    (g : SmoothRiemannianMetric I M) {r s : ℕ} {k : ℕ}
    {T : SmoothCcTensor g r s}
    (hT : MemWtwokTwo (I := I) (M := M) g k T) :
    ∑ α ∈ chartAtlasPOUFinset (I := I) (M := M),
        (wtwokTwoChartTerm (I := I) (M := M) g k T α).toReal ≤
      wtwokTwoNormReal (I := I) (M := M) g k T := by
  rw [wtwokTwoNormReal_eq_finset_sum_toReal (I := I) (M := M) g k T]
  rw [ENNReal.toReal_sum]
  intro α _
  exact wtwokTwoChartTerm_ne_top (I := I) (M := M) g hT α

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoNormReal_ge_finset_sum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoNormReal_ge_finset_sum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoNormReal_ge_finset_sum ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoNormReal_ge_finset_sum

omit [NeZero (Module.finrank ℝ E)] in
theorem wtwokTwoNormReal_eq_finset_sum
    (g : SmoothRiemannianMetric I M) {r s : ℕ} {k : ℕ}
    {T : SmoothCcTensor g r s}
    (hT : MemWtwokTwo (I := I) (M := M) g k T) :
    wtwokTwoNormReal (I := I) (M := M) g k T =
      ∑ α ∈ chartAtlasPOUFinset (I := I) (M := M),
        (wtwokTwoChartTerm (I := I) (M := M) g k T α).toReal :=
  le_antisymm
    (wtwokTwoNormReal_le_finset_sum (I := I) (M := M) g hT)
    (wtwokTwoNormReal_ge_finset_sum (I := I) (M := M) g hT)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoNormReal_eq_finset_sum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoNormReal_eq_finset_sum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoNormReal_eq_finset_sum ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoNormReal_eq_finset_sum

omit [NeZero (Module.finrank ℝ E)] in
theorem wtwokTwoChartTerm_toReal_le_wtwokTwoNormReal
    (g : SmoothRiemannianMetric I M) {r s : ℕ} {k : ℕ}
    {T : SmoothCcTensor g r s}
    (hT : MemWtwokTwo (I := I) (M := M) g k T) {α : M}
    (hα : α ∈ chartAtlasPOUFinset (I := I) (M := M)) :
    (wtwokTwoChartTerm (I := I) (M := M) g k T α).toReal ≤
      wtwokTwoNormReal (I := I) (M := M) g k T := by
  unfold wtwokTwoNormReal
  refine ENNReal.toReal_le_toReal
    (wtwokTwoChartTerm_ne_top (I := I) (M := M) g hT α)
    (wtwokTwoNorm_ne_top (I := I) (M := M) g hT) |>.mpr ?_
  exact wtwokTwoChartTerm_le_wtwokTwoNorm (I := I) (M := M) g k T hα

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoChartTerm_toReal_le_wtwokTwoNormReal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoChartTerm_toReal_le_wtwokTwoNormReal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoChartTerm_toReal_le_wtwokTwoNormReal ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoChartTerm_toReal_le_wtwokTwoNormReal

omit [NeZero (Module.finrank ℝ E)] in
theorem wtwokTwoNormReal_le_card_mul
    (g : SmoothRiemannianMetric I M) {r s : ℕ} {k : ℕ}
    {T : SmoothCcTensor g r s}
    (hT : MemWtwokTwo (I := I) (M := M) g k T)
    {C : ℝ}
    (hbound : ∀ α ∈ chartAtlasPOUFinset (I := I) (M := M),
      (wtwokTwoChartTerm (I := I) (M := M) g k T α).toReal ≤ C) :
    wtwokTwoNormReal (I := I) (M := M) g k T ≤
      (chartAtlasPOUFinset (I := I) (M := M)).card * C := by
  rw [wtwokTwoNormReal_eq_finset_sum (I := I) (M := M) g hT]
  refine le_trans (Finset.sum_le_sum hbound) ?_
  rw [Finset.sum_const, nsmul_eq_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoNormReal_le_card_mul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoNormReal_le_card_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoNormReal_le_card_mul ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.wtwokTwoNormReal_le_card_mul

end Tensor
end Sobolev
end Analysis
end DifferentialGeometry
