import Submission.DifferentialGeometry.Geometry.Metric.DirectLimit.Defs
import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Maps
import Submission.DifferentialGeometry.Topology.Exhaustion

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

abbrev pointedDirectLimit
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {A : ℕ → Type u} [∀ k, TopologicalSpace (A k)] [∀ k, ChartedSpace H (A k)]
    [∀ k, IsManifold I ∞ (A k)] [∀ k, Nonempty (A k)]
    [∀ k, SigmaCompactSpace (A k)] [∀ k, T2Space (A k)]
    (S : SmoothSeqSystem I A) (O₀ : A 0)
    (ginf : SmoothRiemannianMetric I S.toSeqSystem.Lim) :
    PointedRiemannianManifold.{u, uE, uH} (I := I) where
  M := S.toSeqSystem.Lim
  basepoint := S.toSeqSystem.incl 0 O₀
  metric := ginf

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.pointedDirectLimit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.pointedDirectLimit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.pointedDirectLimit ``Submission.DifferentialGeometry.CheegerGromovCompactness.pointedDirectLimit

abbrev pointedDirectLimitOfMetricCocycle
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {A : ℕ → Type u} [∀ k, TopologicalSpace (A k)] [∀ k, ChartedSpace H (A k)]
    [∀ k, IsManifold I ∞ (A k)] [∀ k, Nonempty (A k)]
    [∀ k, SigmaCompactSpace (A k)] [∀ k, T2Space (A k)]
    (S : SmoothSeqSystem I A) (O₀ : A 0)
    (g : ∀ k, SmoothRiemannianMetric I (A k)) (hg : S.MetricCocycle g) :
    PointedRiemannianManifold.{u, uE, uH} (I := I) :=
  pointedDirectLimit S O₀ (S.limitMetric g hg)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.pointedDirectLimitOfMetricCocycle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.pointedDirectLimitOfMetricCocycle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.pointedDirectLimitOfMetricCocycle ``Submission.DifferentialGeometry.CheegerGromovCompactness.pointedDirectLimitOfMetricCocycle

section

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {A : ℕ → Type u} [∀ k, TopologicalSpace (A k)] [∀ k, ChartedSpace H (A k)]
  [∀ k, IsManifold I ∞ (A k)] [∀ k, Nonempty (A k)]
  [∀ k, SigmaCompactSpace (A k)] [∀ k, T2Space (A k)]

abbrev factorPointed (S : SmoothSeqSystem I A) (O₀ : A 0)
    (g : ∀ k, SmoothRiemannianMetric I (A k)) (k : ℕ) :
    PointedRiemannianManifold.{u, uE, uH} (I := I) where
  M := A k
  basepoint := S.toSeqSystem.map (Nat.zero_le k) O₀
  metric := g k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.factorPointed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.factorPointed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.factorPointed ``Submission.DifferentialGeometry.CheegerGromovCompactness.factorPointed

abbrev factorSeq (S : SmoothSeqSystem I A) (O₀ : A 0)
    (g : ∀ k, SmoothRiemannianMetric I (A k)) :
    PointedRiemannianSeq.{u, uE, uH} (I := I) where
  obj := factorPointed S O₀ g

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.factorSeq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.factorSeq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.factorSeq ``Submission.DifferentialGeometry.CheegerGromovCompactness.factorSeq

omit [FiniteDimensional ℝ E] [CompleteSpace E] [∀ (k : ℕ), SigmaCompactSpace (A k)]
    [∀ (k : ℕ), T2Space (A k)] in
theorem range_exhausts (S : SmoothSeqSystem I A) :
    ExhaustsByOpen (fun k => Set.range (S.toSeqSystem.incl k)) where
  isOpen k := (S.toSeqSystem.incl_isOpenEmb k).isOpen_range
  mono_step k := S.toSeqSystem.range_incl_mono (Nat.le_succ k)
  subset K hK := by
    obtain ⟨k₀, Kk, _, hKeq⟩ := S.toSeqSystem.exists_compact_stage_representation hK
    refine ⟨k₀, fun k hk => ?_⟩
    rw [hKeq]
    exact (Set.image_subset_range _ _).trans (S.toSeqSystem.range_incl_mono hk)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.range_exhausts then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.range_exhausts"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.range_exhausts ``Submission.DifferentialGeometry.CheegerGromovCompactness.range_exhausts

noncomputable def limitConvergenceMapsOf (S : SmoothSeqSystem I A) (O₀ : A 0)
    (gSeq gLim : ∀ k, SmoothRiemannianMetric I (A k)) (hgLim : S.MetricCocycle gLim) :
    PointedRiemannianConvergenceMaps.{u, uE, uH} (I := I)
      (X := factorSeq S O₀ gSeq)
      (L := (pointedDirectLimitOfMetricCocycle S O₀ gLim hgLim :
        PointedRiemannianManifold.{u, uE, uH} (I := I)))
      (subseq := id) where
  partialDiffeomorph k := S.inclPartialDiffeo k
  source_exhausts := range_exhausts S
  base_mem k := ⟨S.toSeqSystem.map (Nat.zero_le k) O₀, S.toSeqSystem.incl_comp (Nat.zero_le k) O₀⟩
  basepoint_map k := S.invIncl_incl_le (Nat.zero_le k) O₀

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.limitConvergenceMapsOf then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.limitConvergenceMapsOf"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.limitConvergenceMapsOf ``Submission.DifferentialGeometry.CheegerGromovCompactness.limitConvergenceMapsOf

noncomputable def limitConvergenceMaps (S : SmoothSeqSystem I A) (O₀ : A 0)
    (g : ∀ k, SmoothRiemannianMetric I (A k)) (hg : S.MetricCocycle g) :
    PointedRiemannianConvergenceMaps.{u, uE, uH} (I := I)
      (X := factorSeq S O₀ g)
      (L := (pointedDirectLimitOfMetricCocycle S O₀ g hg : PointedRiemannianManifold.{u, uE, uH} (I := I)))
      (subseq := id) :=
  limitConvergenceMapsOf S O₀ g g hg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.limitConvergenceMaps then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.limitConvergenceMaps"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.limitConvergenceMaps ``Submission.DifferentialGeometry.CheegerGromovCompactness.limitConvergenceMaps

end

end CheegerGromovCompactness
end DifferentialGeometry
