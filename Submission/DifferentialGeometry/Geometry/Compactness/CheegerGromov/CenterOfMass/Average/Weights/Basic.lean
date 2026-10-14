import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.CenterOfMass.Average.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


open _root_.Submission.DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

universe uX uι

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open scoped _root_.BigOperators

noncomputable def normWeights {E' : Type uX} {ι : Type uι} [Fintype ι]
    (num : ι → E' → ℝ) (i : ι) (z : E') : ℝ :=
  num i z / ∑ j, num j z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.normWeights then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.normWeights"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.normWeights ``Submission.DifferentialGeometry.CheegerGromovCompactness.normWeights

theorem normWeights_sum {E' : Type uX} {ι : Type uι} [Fintype ι]
    {num : ι → E' → ℝ} {z : E'} (hne : (∑ j, num j z) ≠ 0) :
    ∑ i, normWeights num i z = 1 := by
  simp only [normWeights, ← Finset.sum_div]
  exact div_self hne

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.normWeights_sum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.normWeights_sum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.normWeights_sum ``Submission.DifferentialGeometry.CheegerGromovCompactness.normWeights_sum

theorem normWeights_nonneg {E' : Type uX} {ι : Type uι} [Fintype ι]
    {num : ι → E' → ℝ} {z : E'} (hnn : ∀ j, 0 ≤ num j z) (i : ι) :
    0 ≤ normWeights num i z :=
  div_nonneg (hnn i) (Finset.sum_nonneg fun j _ => hnn j)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.normWeights_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.normWeights_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.normWeights_nonneg ``Submission.DifferentialGeometry.CheegerGromovCompactness.normWeights_nonneg

theorem normWeights_pos {E' : Type uX} {ι : Type uι} [Fintype ι]
    {num : ι → E' → ℝ} {z : E'} (hnn : ∀ j, 0 ≤ num j z)
    (hne : (∑ j, num j z) ≠ 0) : ∃ i, 0 < normWeights num i z := by
  have hsum : ∑ i, normWeights num i z = 1 := normWeights_sum hne
  have hpos : 0 < ∑ i, normWeights num i z := by rw [hsum]; exact zero_lt_one
  simpa only [Finset.mem_univ, true_and] using
    (Finset.sum_pos_iff_of_nonneg
      (fun i (_hi : i ∈ Finset.univ) => normWeights_nonneg hnn i)).mp hpos

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.normWeights_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.normWeights_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.normWeights_pos ``Submission.DifferentialGeometry.CheegerGromovCompactness.normWeights_pos

theorem num_ne_of_weight_ne {E' : Type uX} {ι : Type uι} [Fintype ι]
    {num : ι → E' → ℝ} {i : ι} {z : E'} (hweight : normWeights num i z ≠ 0) :
    num i z ≠ 0 := by
  intro hnum
  apply hweight
  simp [normWeights, hnum]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.num_ne_of_weight_ne then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.num_ne_of_weight_ne"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.num_ne_of_weight_ne ``Submission.DifferentialGeometry.CheegerGromovCompactness.num_ne_of_weight_ne

theorem normWeights_delta {E' : Type uX} {ι : Type uι} [Fintype ι]
    {num : ι → E' → ℝ} {z : E'} (i0 : ι)
    (hzero : ∀ j, j ≠ i0 → num j z = 0) (hne : num i0 z ≠ 0) :
    normWeights num i0 z = 1 ∧ ∀ j, j ≠ i0 → normWeights num j z = 0 := by
  have hsum : ∑ j, num j z = num i0 z :=
    Finset.sum_eq_single i0 (fun j _ hj => hzero j hj)
      (fun h => absurd (Finset.mem_univ i0) h)
  refine ⟨?_, fun j hj => ?_⟩
  · simp [normWeights, hsum, div_self hne]
  · simp [normWeights, hzero j hj]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.normWeights_delta then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.normWeights_delta"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.normWeights_delta ``Submission.DifferentialGeometry.CheegerGromovCompactness.normWeights_delta

theorem normWeights_weightDataOn {E' : Type uX} {ι : Type} [Fintype ι]
    {s : Set E'} {U : ι → Set E'} {num : ι → E' → ℝ}
    (hnn : ∀ z ∈ s, ∀ i, 0 ≤ num i z)
    (hne : ∀ z ∈ s, (∑ j, num j z) ≠ 0)
    (hactive : ∀ z ∈ s, ∀ i, num i z ≠ 0 → z ∈ U i) :
    centerAverage.WeightDataOn s U (fun z i => normWeights num i z) where
  nonneg z hz i := normWeights_nonneg (hnn z hz) i
  pos z hz := normWeights_pos (hnn z hz) (hne z hz)
  sum_one z hz := normWeights_sum (hne z hz)
  active_mem z hz i hi := hactive z hz i (num_ne_of_weight_ne hi)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.normWeights_weightDataOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.normWeights_weightDataOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.normWeights_weightDataOn ``Submission.DifferentialGeometry.CheegerGromovCompactness.normWeights_weightDataOn

noncomputable def cutRaw {X : Type uX} {ι : Type uι} [DecidableEq ι]
    (cut : X → ℝ) (a : ι → X → ℝ) (i0 i : ι) (x : X) : ℝ :=
  if i = i0 then a i0 x else (1 - cut x) * a i x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.cutRaw then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.cutRaw"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.cutRaw ``Submission.DifferentialGeometry.CheegerGromovCompactness.cutRaw

@[simp] theorem cutRaw_same {X : Type uX} {ι : Type uι} [DecidableEq ι]
    (cut : X → ℝ) (a : ι → X → ℝ) (i0 : ι) (x : X) :
    cutRaw cut a i0 i0 x = a i0 x := by
  rw [cutRaw, if_pos rfl]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.cutRaw_same then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.cutRaw_same"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.cutRaw_same ``Submission.DifferentialGeometry.CheegerGromovCompactness.cutRaw_same

theorem cutRaw_of_ne {X : Type uX} {ι : Type uι} [DecidableEq ι]
    (cut : X → ℝ) (a : ι → X → ℝ) (i0 i : ι) (x : X) (hi : i ≠ i0) :
    cutRaw cut a i0 i x = (1 - cut x) * a i x := by
  rw [cutRaw, if_neg hi]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.cutRaw_of_ne then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.cutRaw_of_ne"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.cutRaw_of_ne ``Submission.DifferentialGeometry.CheegerGromovCompactness.cutRaw_of_ne

theorem cutRaw_nonneg {X : Type uX} {ι : Type uι} [DecidableEq ι]
    {cut : X → ℝ} {a : ι → X → ℝ} {i0 : ι} {x : X}
    (hcut : cut x ∈ Set.Icc (0 : ℝ) 1) (hnn : ∀ i, 0 ≤ a i x) (i : ι) :
    0 ≤ cutRaw cut a i0 i x := by
  by_cases hi : i = i0
  · subst i
    rw [cutRaw_same]
    exact hnn i0
  · rw [cutRaw_of_ne cut a i0 i x hi]
    exact mul_nonneg (sub_nonneg.mpr hcut.2) (hnn i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.cutRaw_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.cutRaw_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.cutRaw_nonneg ``Submission.DifferentialGeometry.CheegerGromovCompactness.cutRaw_nonneg

theorem num_ne_of_cut_ne {X : Type uX} {ι : Type uι} [DecidableEq ι]
    {cut : X → ℝ} {a : ι → X → ℝ} {i0 i : ι} {x : X}
    (hraw : cutRaw cut a i0 i x ≠ 0) : a i x ≠ 0 := by
  intro ha
  by_cases hi : i = i0
  · subst i
    exact hraw (by rw [cutRaw_same, ha])
  · exact hraw (by rw [cutRaw_of_ne cut a i0 i x hi, ha, _root_.MulZeroClass.mul_zero])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.num_ne_of_cut_ne then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.num_ne_of_cut_ne"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.num_ne_of_cut_ne ``Submission.DifferentialGeometry.CheegerGromovCompactness.num_ne_of_cut_ne

theorem cutRaw_pos {X : Type uX} {ι : Type uι} [DecidableEq ι]
    {cut : X → ℝ} {a : ι → X → ℝ} {i0 : ι} {x : X}
    (hnn : ∀ i, 0 ≤ a i x)
    (hcover : ∃ i, 0 < a i x) (hbase : cut x ≠ 0 → 0 < a i0 x) :
    ∃ i, 0 < cutRaw cut a i0 i x := by
  by_cases hi0 : 0 < a i0 x
  · exact ⟨i0, by simpa only [cutRaw_same] using hi0⟩
  have hai0 : a i0 x = 0 := le_antisymm (not_lt.mp hi0) (hnn i0)
  have hcut0 : cut x = 0 := by
    by_contra hc
    exact hi0 (hbase hc)
  obtain ⟨i, hi⟩ := hcover
  have hine : i ≠ i0 := by
    intro h
    subst i
    rw [hai0] at hi
    exact (lt_irrefl 0) hi
  refine ⟨i, ?_⟩
  rw [cutRaw_of_ne cut a i0 i x hine, hcut0, sub_zero, one_mul]
  exact hi

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.cutRaw_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.cutRaw_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.cutRaw_pos ``Submission.DifferentialGeometry.CheegerGromovCompactness.cutRaw_pos

theorem cutRaw_sum_pos {X : Type uX} {ι : Type uι} [Fintype ι] [DecidableEq ι]
    {cut : X → ℝ} {a : ι → X → ℝ} {i0 : ι} {x : X}
    (hcut : cut x ∈ Set.Icc (0 : ℝ) 1) (hnn : ∀ i, 0 ≤ a i x)
    (hcover : ∃ i, 0 < a i x) (hbase : cut x ≠ 0 → 0 < a i0 x) :
    0 < ∑ i, cutRaw cut a i0 i x := by
  obtain ⟨i, hi⟩ := cutRaw_pos hnn hcover hbase
  exact (Finset.sum_pos_iff_of_nonneg
    (fun j (_hj : j ∈ Finset.univ) => cutRaw_nonneg hcut hnn j)).2
      ⟨i, Finset.mem_univ i, hi⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.cutRaw_sum_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.cutRaw_sum_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.cutRaw_sum_pos ``Submission.DifferentialGeometry.CheegerGromovCompactness.cutRaw_sum_pos

theorem cutRaw_delta {X : Type uX} {ι : Type uι} [DecidableEq ι]
    {cut : X → ℝ} {a : ι → X → ℝ} {i0 : ι} {x : X}
    (hcut : cut x = 1) :
    cutRaw cut a i0 i0 x = a i0 x ∧
      ∀ i, i ≠ i0 → cutRaw cut a i0 i x = 0 := by
  refine ⟨cutRaw_same cut a i0 x, fun i hi => ?_⟩
  rw [cutRaw_of_ne cut a i0 i x hi, hcut, sub_self, _root_.MulZeroClass.zero_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.cutRaw_delta then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.cutRaw_delta"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.cutRaw_delta ``Submission.DifferentialGeometry.CheegerGromovCompactness.cutRaw_delta

noncomputable def rawWeights {X : Type uX} {ι : Type uι} [Fintype ι]
    (a : ι → X → ℝ) (x : X) (i : ι) : ℝ :=
  a i x / ∑ j, a j x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.rawWeights then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.rawWeights"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.rawWeights ``Submission.DifferentialGeometry.CheegerGromovCompactness.rawWeights

theorem rawWeights_sum {X : Type uX} {ι : Type uι} [Fintype ι]
    {a : ι → X → ℝ} {x : X} (hne : (∑ j, a j x) ≠ 0) :
    ∑ i, rawWeights a x i = 1 := by
  simp only [rawWeights, ← Finset.sum_div]
  exact div_self hne

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.rawWeights_sum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.rawWeights_sum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.rawWeights_sum ``Submission.DifferentialGeometry.CheegerGromovCompactness.rawWeights_sum

theorem rawWeights_nonneg {X : Type uX} {ι : Type uι} [Fintype ι]
    {a : ι → X → ℝ} {x : X} (hnn : ∀ j, 0 ≤ a j x) (i : ι) :
    0 ≤ rawWeights a x i :=
  div_nonneg (hnn i) (Finset.sum_nonneg fun j _ => hnn j)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.rawWeights_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.rawWeights_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.rawWeights_nonneg ``Submission.DifferentialGeometry.CheegerGromovCompactness.rawWeights_nonneg

theorem rawWeights_pos {X : Type uX} {ι : Type uι} [Fintype ι]
    {a : ι → X → ℝ} {x : X} (hnn : ∀ j, 0 ≤ a j x)
    (hne : (∑ j, a j x) ≠ 0) : ∃ i, 0 < rawWeights a x i := by
  have hsum : ∑ i, rawWeights a x i = 1 := rawWeights_sum hne
  have hpos : 0 < ∑ i, rawWeights a x i := by rw [hsum]; exact zero_lt_one
  simpa only [Finset.mem_univ, true_and] using
    (Finset.sum_pos_iff_of_nonneg
      (fun i (_hi : i ∈ Finset.univ) => rawWeights_nonneg hnn i)).mp hpos

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.rawWeights_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.rawWeights_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.rawWeights_pos ``Submission.DifferentialGeometry.CheegerGromovCompactness.rawWeights_pos

theorem num_ne_of_raw_ne {X : Type uX} {ι : Type uι} [Fintype ι]
    {a : ι → X → ℝ} {x : X} {i : ι} (hweight : rawWeights a x i ≠ 0) :
    a i x ≠ 0 := by
  intro hnum
  apply hweight
  simp [rawWeights, hnum]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.num_ne_of_raw_ne then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.num_ne_of_raw_ne"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.num_ne_of_raw_ne ``Submission.DifferentialGeometry.CheegerGromovCompactness.num_ne_of_raw_ne

theorem rawWeights_delta {X : Type uX} {ι : Type uι} [Fintype ι]
    {a : ι → X → ℝ} {x : X} (i0 : ι)
    (hzero : ∀ j, j ≠ i0 → a j x = 0) (hne : a i0 x ≠ 0) :
    rawWeights a x i0 = 1 ∧ ∀ j, j ≠ i0 → rawWeights a x j = 0 := by
  have hsum : ∑ j, a j x = a i0 x :=
    Finset.sum_eq_single i0 (fun j _ hj => hzero j hj)
      (fun h => absurd (Finset.mem_univ i0) h)
  refine ⟨?_, fun j hj => ?_⟩
  · simp [rawWeights, hsum, div_self hne]
  · simp [rawWeights, hzero j hj]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.rawWeights_delta then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.rawWeights_delta"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.rawWeights_delta ``Submission.DifferentialGeometry.CheegerGromovCompactness.rawWeights_delta

theorem rawWeights_weightDataOn {X : Type uX} {ι : Type} [Fintype ι]
    {s : Set X} {U : ι → Set X} {a : ι → X → ℝ}
    (hnn : ∀ x ∈ s, ∀ i, 0 ≤ a i x)
    (hne : ∀ x ∈ s, (∑ j, a j x) ≠ 0)
    (hactive : ∀ x ∈ s, ∀ i, a i x ≠ 0 → x ∈ U i) :
    centerAverage.WeightDataOn s U (rawWeights a) where
  nonneg x hx i := rawWeights_nonneg (hnn x hx) i
  pos x hx := rawWeights_pos (hnn x hx) (hne x hx)
  sum_one x hx := rawWeights_sum (hne x hx)
  active_mem x hx i hi := hactive x hx i (num_ne_of_raw_ne hi)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.rawWeights_weightDataOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.rawWeights_weightDataOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.rawWeights_weightDataOn ``Submission.DifferentialGeometry.CheegerGromovCompactness.rawWeights_weightDataOn

theorem cutWeights_weightDataOn {X : Type uX} {ι : Type} [Fintype ι] [DecidableEq ι]
    {s : Set X} {U : ι → Set X} {cut : X → ℝ} {a : ι → X → ℝ} {i0 : ι}
    (hcut : ∀ x ∈ s, cut x ∈ Set.Icc (0 : ℝ) 1)
    (hnn : ∀ x ∈ s, ∀ i, 0 ≤ a i x)
    (hcover : ∀ x ∈ s, ∃ i, 0 < a i x)
    (hbase : ∀ x ∈ s, cut x ≠ 0 → 0 < a i0 x)
    (hactive : ∀ x ∈ s, ∀ i, a i x ≠ 0 → x ∈ U i) :
    centerAverage.WeightDataOn s U (rawWeights (cutRaw cut a i0)) := by
  apply rawWeights_weightDataOn
  · intro x hx i
    exact cutRaw_nonneg (hcut x hx) (hnn x hx) i
  · intro x hx
    exact ne_of_gt (cutRaw_sum_pos (hcut x hx) (hnn x hx) (hcover x hx) (hbase x hx))
  · intro x hx i hi
    exact hactive x hx i (num_ne_of_cut_ne hi)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.cutWeights_weightDataOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.cutWeights_weightDataOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.cutWeights_weightDataOn ``Submission.DifferentialGeometry.CheegerGromovCompactness.cutWeights_weightDataOn

end CheegerGromovCompactness
end DifferentialGeometry
