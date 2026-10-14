import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.TimeLipschitz

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

theorem exists_metric_extension_covariant_derivative_bound_on_closed_interval
    {X : PointedFlowSeq (I := I)} {P : PointedRiemannianManifold (I := I)}
    {subseq : ℕ → ℕ} (Φ : PointedCGHMaps (I := I) X P subseq)
    (R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily Φ) (hsrc : SourceIsSigmaCompact Φ) (htgt : TargetIsSigmaCompact Φ)
    {a b : ℝ} (hslab : _root_.Set.Icc a b ⊆ X.D.carrier)
    (hregular : _root_.Set.Ico a b ⊆ X.D.regular) (i : ℕ)
    {K : Set P.M} (hK : letI : TopologicalSpace P.M := P.topology; IsCompact K)
    (p : ℕ) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    ∃ C : ℝ, 0 < C ∧ ∀ q ≤ p, ∀ t ∈ _root_.Set.Icc a b, ∀ x ∈ K,
      metricCovDerivNorm q (gSeqExt Φ R bf hsrc htgt i t) R x ≤ C := by
  classical
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  let : SigmaCompactSpace P.M := P.sigmaCompact
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hbase (q : ℕ) : ∃ C : ℝ, ∀ x ∈ K,
      metricCovDerivNorm q (gSeqExt Φ R bf hsrc htgt i a) R x ≤ C :=
    metricCovDerivNorm_bddOn hK q (gSeqExt Φ R bf hsrc htgt i a) R
  choose C hC using hbase
  let B : ℝ := ∑ q ∈ Finset.range (p + 1), _root_.Max.max (C q) 0
  have hB : 0 ≤ B := Finset.sum_nonneg fun q _ => le_max_right _ _
  have hbaseBound (q : ℕ) (hq : q ≤ p) (x : P.M) (hx : x ∈ K) :
      metricCovDerivNorm q (gSeqExt Φ R bf hsrc htgt i a) R x ≤ B := by
    have hqb : C q ≤ B := (le_max_left _ _).trans
      (Finset.single_le_sum (fun j _ => le_max_right (C j) 0)
        (Finset.mem_range.mpr (by omega)))
    exact (hC q x hx).trans hqb
  by_cases hab : a < b
  · obtain ⟨L, hL, hlip⟩ :=
      exists_metric_extension_time_lipschitz_constant_on_closed_interval
        Φ R bf hsrc htgt hab hslab hregular i K hK p
    refine ⟨B + L * |b - a| + 1, by positivity, ?_⟩
    intro q hq t ht x hx
    have htime : |t - a| ≤ |b - a| := by
      rw [abs_of_nonneg (sub_nonneg.mpr ht.1),
        abs_of_nonneg (sub_nonneg.mpr hab.le)]
      exact sub_le_sub_right ht.2 a
    have hd := hlip t ht a ⟨le_rfl, hab.le⟩ q hq x hx
    have he := hd.trans (mul_le_mul_of_nonneg_left htime hL)
    have hc := covNorm_le_add q (gSeqExt Φ R bf hsrc htgt i t)
      (gSeqExt Φ R bf hsrc htgt i a) R x
    have hb := hbaseBound q hq x hx
    linarith
  · refine ⟨B + 1, by positivity, ?_⟩
    intro q hq t ht x hx
    have htEq : t = a := by
      have hba : b ≤ a := le_of_not_gt hab
      exact le_antisymm (ht.2.trans hba) ht.1
    rw [htEq]
    exact (hbaseBound q hq x hx).trans (by linarith)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.exists_metric_extension_covariant_derivative_bound_on_closed_interval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.exists_metric_extension_covariant_derivative_bound_on_closed_interval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.exists_metric_extension_covariant_derivative_bound_on_closed_interval ``Submission.DifferentialGeometry.CheegerGromovCompactness.exists_metric_extension_covariant_derivative_bound_on_closed_interval

end DifferentialGeometry.CheegerGromovCompactness
