import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Iterated.Linear

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Manifold
open scoped _root_.BigOperators _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Analysis.Sobolev

open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Integral.L2

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

noncomputable abbrev covariantJetNormSq
    (g : SmoothRiemannianMetric I M) {r s : ℕ} (m : ℕ)
    (S : SmoothCcTensor g r s) : ℝ :=
  ∑ q ∈ Finset.range (m + 1),
    ‖iteratedCovGrad (I := I) g r s q S‖ ^ 2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.covariantJetNormSq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.covariantJetNormSq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.covariantJetNormSq ``Submission.DifferentialGeometry.Analysis.Sobolev.covariantJetNormSq

omit [BoundarylessManifold I M] [NeZero (Module.finrank ℝ E)] in
omit [CompactSpace M] in
theorem covariantJetNormSq_nonneg
    (g : SmoothRiemannianMetric I M) {r s m : ℕ}
    (S : SmoothCcTensor g r s) :
    0 ≤ covariantJetNormSq (I := I) (M := M) g m S :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.covariantJetNormSq_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.covariantJetNormSq_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.covariantJetNormSq_nonneg ``Submission.DifferentialGeometry.Analysis.Sobolev.covariantJetNormSq_nonneg

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem covariantJetNormSq_smul
    (g : SmoothRiemannianMetric I M) {r s : ℕ} (m : ℕ)
    (c : ℝ) (S : SmoothCcTensor g r s) :
    covariantJetNormSq (I := I) (M := M) g m (c • S) =
      c ^ 2 * covariantJetNormSq (I := I) (M := M) g m S := by
  unfold covariantJetNormSq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [iteratedCovGrad_smul, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.covariantJetNormSq_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.covariantJetNormSq_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.covariantJetNormSq_smul ``Submission.DifferentialGeometry.Analysis.Sobolev.covariantJetNormSq_smul

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem covariantJetNormSq_add_le
    (g : SmoothRiemannianMetric I M) {r s : ℕ} (m : ℕ)
    (S V : SmoothCcTensor g r s) :
    covariantJetNormSq (I := I) (M := M) g m (S + V) ≤
      2 * (covariantJetNormSq (I := I) (M := M) g m S +
        covariantJetNormSq (I := I) (M := M) g m V) := by
  unfold covariantJetNormSq
  calc
    ∑ q ∈ Finset.range (m + 1),
        ‖iteratedCovGrad (I := I) g r s q (S + V)‖ ^ 2 ≤
        ∑ q ∈ Finset.range (m + 1),
          2 * (‖iteratedCovGrad (I := I) g r s q S‖ ^ 2 +
            ‖iteratedCovGrad (I := I) g r s q V‖ ^ 2) := by
      refine Finset.sum_le_sum fun q _ => ?_
      rw [iteratedCovGrad_add]
      have htri := norm_add_le
        (iteratedCovGrad (I := I) g r s q S)
        (iteratedCovGrad (I := I) g r s q V)
      calc
        ‖iteratedCovGrad (I := I) g r s q S +
            iteratedCovGrad (I := I) g r s q V‖ ^ 2 ≤
            (‖iteratedCovGrad (I := I) g r s q S‖ +
              ‖iteratedCovGrad (I := I) g r s q V‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) htri 2
        _ ≤ 2 * (‖iteratedCovGrad (I := I) g r s q S‖ ^ 2 +
            ‖iteratedCovGrad (I := I) g r s q V‖ ^ 2) := by
          nlinarith [sq_nonneg
            (‖iteratedCovGrad (I := I) g r s q S‖ -
              ‖iteratedCovGrad (I := I) g r s q V‖)]
    _ = 2 * ((∑ q ∈ Finset.range (m + 1),
          ‖iteratedCovGrad (I := I) g r s q S‖ ^ 2) +
        ∑ q ∈ Finset.range (m + 1),
          ‖iteratedCovGrad (I := I) g r s q V‖ ^ 2) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.covariantJetNormSq_add_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.covariantJetNormSq_add_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.covariantJetNormSq_add_le ``Submission.DifferentialGeometry.Analysis.Sobolev.covariantJetNormSq_add_le

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem covariantJetNormSq_sub_le
    (g : SmoothRiemannianMetric I M) {r s : ℕ} (m : ℕ)
    (S V : SmoothCcTensor g r s) :
    covariantJetNormSq (I := I) (M := M) g m (S - V) ≤
      2 * (covariantJetNormSq (I := I) (M := M) g m S +
        covariantJetNormSq (I := I) (M := M) g m V) := by
  unfold covariantJetNormSq
  calc
    ∑ q ∈ Finset.range (m + 1),
        ‖iteratedCovGrad (I := I) g r s q (S - V)‖ ^ 2 ≤
        ∑ q ∈ Finset.range (m + 1),
          2 * (‖iteratedCovGrad (I := I) g r s q S‖ ^ 2 +
            ‖iteratedCovGrad (I := I) g r s q V‖ ^ 2) := by
      refine Finset.sum_le_sum fun q _ => ?_
      rw [iteratedCovGrad_sub]
      have htri := norm_sub_le
        (iteratedCovGrad (I := I) g r s q S)
        (iteratedCovGrad (I := I) g r s q V)
      have hstep :
          ‖iteratedCovGrad (I := I) g r s q S -
              iteratedCovGrad (I := I) g r s q V‖ ^ 2 ≤
            (‖iteratedCovGrad (I := I) g r s q S‖ +
              ‖iteratedCovGrad (I := I) g r s q V‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) htri 2
      nlinarith [hstep, sq_nonneg
        (‖iteratedCovGrad (I := I) g r s q S‖ -
          ‖iteratedCovGrad (I := I) g r s q V‖)]
    _ = 2 * ((∑ q ∈ Finset.range (m + 1),
          ‖iteratedCovGrad (I := I) g r s q S‖ ^ 2) +
        ∑ q ∈ Finset.range (m + 1),
          ‖iteratedCovGrad (I := I) g r s q V‖ ^ 2) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.covariantJetNormSq_sub_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.covariantJetNormSq_sub_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.covariantJetNormSq_sub_le ``Submission.DifferentialGeometry.Analysis.Sobolev.covariantJetNormSq_sub_le

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem covariantJetNormSq_neg
    (g : SmoothRiemannianMetric I M) {r s : ℕ} (m : ℕ)
    (S : SmoothCcTensor g r s) :
    covariantJetNormSq (I := I) (M := M) g m (-S) =
      covariantJetNormSq (I := I) (M := M) g m S := by
  unfold covariantJetNormSq
  apply Finset.sum_congr rfl
  intro q _
  rw [iteratedCovGrad_neg, norm_neg]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.covariantJetNormSq_neg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.covariantJetNormSq_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.covariantJetNormSq_neg ``Submission.DifferentialGeometry.Analysis.Sobolev.covariantJetNormSq_neg

omit [BoundarylessManifold I M] [NeZero (Module.finrank ℝ E)] in
omit [CompactSpace M] in
theorem covariantJetNormSq_mono
    (g : SmoothRiemannianMetric I M) {r s m n : ℕ}
    (hmn : m ≤ n) (S : SmoothCcTensor g r s) :
    covariantJetNormSq (I := I) (M := M) g m S ≤
      covariantJetNormSq (I := I) (M := M) g n S := by
  unfold covariantJetNormSq
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_subset_range.mpr (Nat.add_le_add_right hmn 1))
    (fun _ _ _ => sq_nonneg _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.covariantJetNormSq_mono then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.covariantJetNormSq_mono"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.covariantJetNormSq_mono ``Submission.DifferentialGeometry.Analysis.Sobolev.covariantJetNormSq_mono

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [CompactSpace M] [SigmaCompactSpace M] in
theorem iteratedCovGrad_zero_section
    (g : SmoothRiemannianMetric I M) (r s m : ℕ) :
    iteratedCovGrad (I := I) g r s m
        (0 : SmoothCcTensor g r s) = 0 := by
  induction m with
  | zero => rw [iteratedCovGrad_zero]
  | succ m ih => rw [iteratedCovGrad_succ, ih, covGrad_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.iteratedCovGrad_zero_section then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.iteratedCovGrad_zero_section"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.iteratedCovGrad_zero_section ``Submission.DifferentialGeometry.Analysis.Sobolev.iteratedCovGrad_zero_section

omit [BoundarylessManifold I M] [NeZero (Module.finrank ℝ E)] in
omit [CompactSpace M] in
theorem covariantJetNormSq_zero
    (g : SmoothRiemannianMetric I M) {r s m : ℕ} :
    covariantJetNormSq (I := I) (M := M) g m
        (0 : SmoothCcTensor g r s) = 0 := by
  unfold covariantJetNormSq
  apply Finset.sum_eq_zero
  intro q _
  rw [iteratedCovGrad_zero_section, norm_zero, zero_pow (by norm_num)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.covariantJetNormSq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.covariantJetNormSq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.covariantJetNormSq_zero ``Submission.DifferentialGeometry.Analysis.Sobolev.covariantJetNormSq_zero

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem covariantJetNormSq_sum_four_le
    (g : SmoothRiemannianMetric I M) {r s m : ℕ}
    (A B C D : SmoothCcTensor g r s) (X : ℝ)
    (hA : covariantJetNormSq (I := I) (M := M) g m A ≤ X ^ 2)
    (hB : covariantJetNormSq (I := I) (M := M) g m B ≤ X ^ 2)
    (hC : covariantJetNormSq (I := I) (M := M) g m C ≤ X ^ 2)
    (hD : covariantJetNormSq (I := I) (M := M) g m D ≤ X ^ 2) :
    covariantJetNormSq (I := I) (M := M) g m (A + B + C + D) ≤
      (8 * X) ^ 2 := by
  have hAB : covariantJetNormSq (I := I) (M := M) g m (A + B) ≤
      (2 * X) ^ 2 := by
    refine (covariantJetNormSq_add_le (I := I) (M := M) g m A B).trans ?_
    nlinarith [sq_nonneg X]
  have hABC : covariantJetNormSq (I := I) (M := M) g m (A + B + C) ≤
      (4 * X) ^ 2 := by
    refine (covariantJetNormSq_add_le (I := I) (M := M) g m (A + B) C).trans ?_
    nlinarith [sq_nonneg X]
  refine (covariantJetNormSq_add_le (I := I) (M := M) g m (A + B + C) D).trans ?_
  nlinarith [sq_nonneg X]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.covariantJetNormSq_sum_four_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.covariantJetNormSq_sum_four_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.covariantJetNormSq_sum_four_le ``Submission.DifferentialGeometry.Analysis.Sobolev.covariantJetNormSq_sum_four_le

omit [CompactSpace M] in
omit [BoundarylessManifold I M] [NeZero (Module.finrank ℝ E)] in
theorem covariantJetNormSq_sum_six_le
    (g : SmoothRiemannianMetric I M) {r s : ℕ} (m : ℕ)
    (t1 t2 t3 t4 t5 t6 : SmoothCcTensor g r s) {K : ℝ}
    (h1 : covariantJetNormSq (I := I) (M := M) g m t1 ≤ K)
    (h2 : covariantJetNormSq (I := I) (M := M) g m t2 ≤ K)
    (h3 : covariantJetNormSq (I := I) (M := M) g m t3 ≤ K)
    (h4 : covariantJetNormSq (I := I) (M := M) g m t4 ≤ K)
    (h5 : covariantJetNormSq (I := I) (M := M) g m t5 ≤ K)
    (h6 : covariantJetNormSq (I := I) (M := M) g m t6 ≤ K) :
    covariantJetNormSq (I := I) (M := M) g m
        (t1 + t2 + t3 + t4 + t5 + t6) ≤ 94 * K := by
  have a1 := covariantJetNormSq_add_le (I := I) (M := M) g m t1 t2
  have a2 := covariantJetNormSq_add_le (I := I) (M := M) g m (t1 + t2) t3
  have a3 := covariantJetNormSq_add_le
    (I := I) (M := M) g m (t1 + t2 + t3) t4
  have a4 := covariantJetNormSq_add_le
    (I := I) (M := M) g m (t1 + t2 + t3 + t4) t5
  have a5 := covariantJetNormSq_add_le
    (I := I) (M := M) g m (t1 + t2 + t3 + t4 + t5) t6
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.covariantJetNormSq_sum_six_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.covariantJetNormSq_sum_six_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.covariantJetNormSq_sum_six_le ``Submission.DifferentialGeometry.Analysis.Sobolev.covariantJetNormSq_sum_six_le

end DifferentialGeometry.Analysis.Sobolev
