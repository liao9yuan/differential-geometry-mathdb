import Submission.DifferentialGeometry.Geometry.Curvature.ContinuousEvaluation
import Submission.DifferentialGeometry.Geometry.Metric.UnitTangentPair

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set
open scoped _root_.Manifold _root_.ContDiff
open _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]


def orthonormalPairCurvature (g : SmoothRiemannianMetric I M) (p : OrthonormalTangentPair g) : ℝ :=
  metricRm04StandardAt g (SameBaseUnitTangentPair.base g p.val)
    (SameBaseUnitTangentPair.first g p.val) (SameBaseUnitTangentPair.second g p.val)
    (SameBaseUnitTangentPair.second g p.val) (SameBaseUnitTangentPair.first g p.val)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.orthonormalPairCurvature then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.orthonormalPairCurvature"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.orthonormalPairCurvature ``Submission.DifferentialGeometry.Geometry.orthonormalPairCurvature


theorem orthonormalPairCurvature_continuous (g : SmoothRiemannianMetric I M) :
    Continuous (orthonormalPairCurvature g) :=
  (continuous_sectional_contraction g (SameBaseUnitTangentPair.base g)
    (SameBaseUnitTangentPair.continuous_base g)
    (SameBaseUnitTangentPair.first g) (SameBaseUnitTangentPair.second g)
    (SameBaseUnitTangentPair.continuous_first g) (SameBaseUnitTangentPair.continuous_second g)).comp
      continuous_subtype_val

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.orthonormalPairCurvature_continuous then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.orthonormalPairCurvature_continuous"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.orthonormalPairCurvature_continuous ``Submission.DifferentialGeometry.Geometry.orthonormalPairCurvature_continuous

theorem HasPositiveSectionalCurvature.exists_uniform_orthonormal_bound [CompactSpace M]
    {g : SmoothRiemannianMetric I M} (hg : HasPositiveSectionalCurvature g) :
    ∃ k : ℝ, 0 < k ∧ ∀ (x : M) (v w : TangentSpace I x),
      g.inner x v v = 1 → g.inner x w w = 1 → g.inner x v w = 0 →
        k ≤ metricRm04StandardAt g x v w w v := by
  let := orthonormalTangentPair_compactSpace g
  have hpos (p : OrthonormalTangentPair g) : 0 < orthonormalPairCurvature g p :=
    hg _ _ _ (tangent_pair_linearIndependent_of_orthonormal g _ _ _
      (SameBaseUnitTangentPair.unit g p.val).1 (SameBaseUnitTangentPair.unit g p.val).2 p.property)
  by_cases hn : Nonempty (OrthonormalTangentPair g)
  · obtain ⟨p, _, hp⟩ := isCompact_univ.exists_isMinOn
      (Set.nonempty_iff_univ_nonempty.mp hn) (orthonormalPairCurvature_continuous g).continuousOn
    refine ⟨orthonormalPairCurvature g p, hpos p, ?_⟩
    intro x v w hv hw hvw
    let q : OrthonormalTangentPair g :=
      ⟨⟨(⟨⟨x, v⟩, hv⟩, ⟨⟨x, w⟩, hw⟩), rfl⟩, hvw⟩
    exact (isMinOn_iff.mp hp) q (_root_.Set.mem_univ q)
  · refine ⟨1, one_pos, ?_⟩
    intro x v w hv hw hvw
    exact False.elim (hn ⟨⟨⟨(⟨⟨x, v⟩, hv⟩, ⟨⟨x, w⟩, hw⟩), rfl⟩, hvw⟩⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.HasPositiveSectionalCurvature.exists_uniform_orthonormal_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.HasPositiveSectionalCurvature.exists_uniform_orthonormal_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.HasPositiveSectionalCurvature.exists_uniform_orthonormal_bound ``Submission.DifferentialGeometry.Geometry.HasPositiveSectionalCurvature.exists_uniform_orthonormal_bound

end DifferentialGeometry.Geometry
