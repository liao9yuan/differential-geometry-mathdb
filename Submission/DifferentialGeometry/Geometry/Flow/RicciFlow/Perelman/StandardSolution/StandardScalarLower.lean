import Submission.DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.Scalar.CompleteHeatComparison
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardCurvatureControl
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.Scalar
import Submission.DifferentialGeometry.Geometry.Curvature.Bounds.ScalarNorm
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.Cutoff.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow _root_.Submission.DifferentialGeometry.Analysis.Parabolic
open _root_.Submission.DifferentialGeometry.Integral.Measure _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ENNReal
namespace DifferentialGeometry.PDE.RicciFlow
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.E3 target :: scope.openDecls } }

private theorem scalar_lower_closed (S : PartialStandardSolution)
    (T : ℝ) (hT : 0 < T) (hTl : ENNReal.ofReal T < S.lifetime) :
    ∀ t ∈ _root_.Set.Icc 0 T, ∀ x : E3, 1 ≤ metricScalarAt (S.metric t) x := by
  let Q := S.toSolutionOn
  let G := flowG Q
  have hQ : IsSolutionOn Q := S.isSolutionOn
  have hQs := smoothOfSolution Q hQ
  have hslab := (Icc_subset_lifetimeInterval_iff S.lifetime S.lifetime_pos T hT.le).mpr hTl
  have hreg (t : ℝ) (ht : t ∈ _root_.Set.Icc 0 T) (hp : 0 < t) :
      t ∈ (lifetimeInterval S.lifetime S.lifetime_pos).regular :=
    (mem_lifetimeInterval_regular S.lifetime S.lifetime_pos t).mpr
      ⟨hp, (ENNReal.ofReal_le_ofReal ht.2).trans_lt hTl⟩
  obtain ⟨K, hK, hRm⟩ := S.curvature_bound T hT.le hTl
  have hnorm : ∀ t ∈ _root_.Set.Icc 0 T, ∀ x : E3,
      nablaKRm04NormSqIntrinsic Q 0 t x ≤ K ^ 2 := by
    intro t ht x
    exact (Real.sqrt_le_iff.mp (hRm t ht x)).2
  have hcut := nonempty_shi_barrier_cutoff_data_of_solution Q hQ hT hslab
    (fun t ht => hreg t ⟨ht.1.le, ht.2⟩ ht.1)
    (S.complete 0 (hslab ⟨le_rfl, hT.le⟩)) (sq_nonneg K) hnorm
  let q := fun t x => 1 - Q.scalar t x
  have hcont : ContinuousOn (fun p : ℝ × E3 => q p.1 p.2) (_root_.Set.Icc 0 T ×ˢ _root_.Set.univ) :=
    continuousOn_const.sub (hQ.scalarCont.mono (_root_.Set.prod_mono hslab subset_rfl))
  have htime (t : ℝ) (ht : t ∈ _root_.Set.Icc 0 T) (_hp : 0 < t) (x : E3) :
      DifferentiableWithinAt ℝ (fun r => q r x) (_root_.Set.Icc 0 T) t :=
    (hQ.scalarTime ht hslab x).const_sub 1
  have hspace (t : ℝ) (_ht : t ∈ _root_.Set.Icc 0 T) (_hp : 0 < t) :
      ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (q t) :=
    contMDiff_const.sub (scalarSmoothOfSolution Q t)
  have hinit (x : E3) : q 0 x ≤ 0 := by
    change 1 - metricScalarAt (S.metric 0) x ≤ 0
    rw [S.initial]
    exact sub_nonpos.mpr (DifferentialGeometry.PDE.RicciFlow.StandardCap.one_le_metricScalarAt x)
  have hbound : ∀ t ∈ _root_.Set.Icc 0 T, ∀ x : E3, q t x ≤ 1 + 9 * K := by
    intro t ht x
    have hs := scalar_abs_le_rm (S.metric t) x
    have hd : Module.finrank ℝ (TangentSpace (𝓡 3) x) = 3 := by
      change Module.finrank ℝ E3 = 3
      exact finrank_euclideanSpace_fin
    norm_num only [hd] at hs
    change |metricScalarAt (S.metric t) x| ≤
      9 * Real.sqrt (normSq0S (S.metric t) x 4 (metricRm04 (S.metric t) x)) at hs
    have hr := hRm t ht x
    have hneg := neg_le_abs (metricScalarAt (S.metric t) x)
    change 1 - metricScalarAt (S.metric t) x ≤ _
    nlinarith only [hs, hr, hneg]
  have hheat : ∀ t ∈ _root_.Set.Icc 0 T, 0 < t → ∀ x : E3,
      parabolicOperatorWithDrift G T (fun _ _ => 0) q t x ≤ 0 := by
    intro t ht hp x
    have hevolution := hQs.scalarEvolution G (fun _ => rfl) (fun _ => rfl)
      ⟨t, hreg t ht hp⟩ x
    have hd : derivWithin (fun r => Q.scalar r x) (_root_.Set.Icc 0 T) t =
        laplacianAt G t (Q.scalar t) x +
          2 * normSq0S (Q.family.metric t) x 2 (Q.ricci t x) :=
      (hevolution.hasDerivAt
        ((lifetimeInterval S.lifetime S.lifetime_pos).regular_mem_nhds (hreg t ht hp))).hasDerivWithinAt.derivWithin
          ((uniqueDiffOn_Icc hT) t ht)
    have hpq := parabolic_const_sub G T (fun _ _ => 0) Q.scalar 1 t x
      ((uniqueDiffOn_Icc hT) t ht) (hQ.scalarTime ht hslab x)
      (fun y => (scalarSmoothOfSolution Q t).mdifferentiableAt (by simp))
      (gradientFun_mdiffAt (G.metric t) (scalarSmoothOfSolution Q t) x)
    change parabolicOperatorWithDrift G T (fun _ _ => 0) (fun r y => 1 - Q.scalar r y) t x ≤ 0
    rw [hpq, parabolicOperatorWithDrift_eq, hd, heatOperatorWithDrift_zero_drift]
    have hn := normSq0S_nonneg (Q.family.metric t) x 2 (Q.ricci t x)
    change -(laplacianAt G t (Q.scalar t) x + 2 * _ - laplacianAt G t (Q.scalar t) x) ≤ 0
    linarith only [hn]
  have hb := DifferentialGeometry.Analysis.nonpositive_of_heat_subsolution_and_cutoffs G T hT q
    (1 + 9 * K) hcont htime hspace hinit hbound hheat hcut
  intro t ht x
  exact sub_nonpos.mp (hb t ht x)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.scalar_lower_closed
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.scalar_lower_closed target :: scope.openDecls } }

theorem PartialStandardSolution.one_le_scalar (S : PartialStandardSolution)
    (t : ℝ) (ht : t ∈ S.domain) (x : E3) : 1 ≤ metricScalarAt (S.metric t) x := by
  have htime := (mem_lifetimeInterval_carrier S.lifetime S.lifetime_pos t).mp ht
  by_cases hp : 0 < t
  · exact scalar_lower_closed S t hp htime.2 t ⟨hp.le, le_rfl⟩ x
  · have hz : t = 0 := le_antisymm (le_of_not_gt hp) htime.1
    rw [hz, S.initial]
    exact DifferentialGeometry.PDE.RicciFlow.StandardCap.one_le_metricScalarAt x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.one_le_scalar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.one_le_scalar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.one_le_scalar ``Submission.DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.one_le_scalar
end DifferentialGeometry.PDE.RicciFlow
