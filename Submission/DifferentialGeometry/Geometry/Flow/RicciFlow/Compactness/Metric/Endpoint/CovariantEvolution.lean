import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Shi.Restriction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]


theorem metricCovDeriv_hasDerivAt_of_local_solution
    (g : ℝ → SmoothRiemannianMetric I M) (gRef : SmoothRiemannianMetric I M)
    (U : TopologicalSpace.Opens M) [SigmaCompactSpace U]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := U) D)
    (hS : IsSolutionOn (I := I) S)
    (hmet : ∀ t : ℝ, S.family.metric t = (g t).restrictOpen (I := I) U)
    (p : ℕ) {t : ℝ} (ht : t ∈ D.regular) (x : U)
    (slots : Fin (p + 2) → TangentSpace I x) :
    HasDerivAt
      (fun r : ℝ => metricCovDeriv (I := I) (g r) gRef p (x : M) slots)
      (((-2 : ℝ) • nablaRicReal (I := I) (fun _ r => g r) gRef p 0 t (x : M))
        slots) t := by
  have hswap := solutionTowerSwap_regularity (I := I) (gRef.restrictOpen (I := I) U)
    S hS p (fun {_r} hr => D.regular_isOpen.mem_nhds hr)
  have h := solutionTower_hasDerivAt (I := I) (gRef.restrictOpen (I := I) U)
    S hS p hswap p le_rfl t ht x slots
  have hfun :
      (fun r : ℝ => covDerivOfField (I := I) (gRef.restrictOpen (I := I) U)
        (solutionMetricField (I := I) S r) p x slots) =
      (fun r : ℝ => metricCovDeriv (I := I) (g r) gRef p (x : M) slots) := by
    funext r
    simp only [solutionMetricField, hmet r]
    exact metricCovDeriv_restrictOpen_apply (I := I) (g r) gRef U p x slots
  have hsec :
      covDerivOfField (I := I) (gRef.restrictOpen (I := I) U)
        (solutionRicField (I := I) S t) p x slots =
      nablaRicReal (I := I) (fun _ r => g r) gRef p 0 t (x : M) slots := by
    simp only [solutionRicField, hmet t]
    have hr := covDerivOfField_restrictOpen (I := I) gRef U
      (CovariantDerivative.ricciSection (I := I)
        (leviCivitaConnectionOfMetric (I := I) ((g t).restrictOpen (I := I) U))
        (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally (I := I)
          ((g t).restrictOpen (I := I) U)))
      (CovariantDerivative.ricciSection (I := I)
        (leviCivitaConnectionOfMetric (I := I) (g t))
        (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally (I := I)
          (g t)))
      (ricciSection_restrictOpen (I := I) (g t) U) p x slots
    exact hr.trans (by rw [covDerivOfField_eq_iterCov]; rfl)
  have hval :
      covDerivOfField (I := I) (gRef.restrictOpen (I := I) U)
        (solutionEvolutionField (I := I) S t) p x slots =
      ((-2 : ℝ) • nablaRicReal (I := I) (fun _ r => g r) gRef p 0 t (x : M))
        slots := by
    simp only [solutionEvolutionField, covDerivOfField_smul, ContMDiffSection.coe_smul,
      Pi.smul_apply]
    exact congrArg (fun z : ℝ => (-2 : ℝ) * z) hsec
  rw [hfun, hval] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.metricCovDeriv_hasDerivAt_of_local_solution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.metricCovDeriv_hasDerivAt_of_local_solution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.metricCovDeriv_hasDerivAt_of_local_solution ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.metricCovDeriv_hasDerivAt_of_local_solution

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
