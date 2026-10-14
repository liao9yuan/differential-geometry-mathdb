import Submission.DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace.ChartOperator.ManifoldFlowOrbitReduction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Connection


noncomputable section

namespace DifferentialGeometry.Analysis.ODE

open _root_.Set _root_.Function _root_.Bundle _root_.Submission.Bundle _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.ContDiff

open _root_.Submission.DifferentialGeometry.Integral.Measure

section OrbitODE

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

def chartCloseTriv (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M) (α x : M) (s : ℝ) : E →L[ℝ] E :=
  trivFromE (I := I) α ((Φ_fam s : M → M) x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.chartCloseTriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.chartCloseTriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.chartCloseTriv ``Submission.DifferentialGeometry.Analysis.ODE.chartCloseTriv

def chartCloseFderiv (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M) (α x : M) (s : ℝ) : E →L[ℝ] E :=
  mfderiv I 𝓘(ℝ, E) (fun y => extChartAt I α ((Φ_fam s : M → M) y)) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.chartCloseFderiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.chartCloseFderiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.chartCloseFderiv ``Submission.DifferentialGeometry.Analysis.ODE.chartCloseFderiv

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M]
    [BoundarylessManifold I M] in
lemma chartCloseDop_eq_comp
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M) (α x : M) (s : ℝ) :
    flowOrbitChartTrivDerivOp (I := I) Φ_fam α x s
      = (chartCloseTriv (I := I) Φ_fam α x s).comp
          (chartCloseFderiv (I := I) Φ_fam α x s) :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.chartCloseDop_eq_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.chartCloseDop_eq_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.chartCloseDop_eq_comp ``Submission.DifferentialGeometry.Analysis.ODE.chartCloseDop_eq_comp

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M]
    [BoundarylessManifold I M] in
lemma chartCloseTriv_basepoint
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M) (t : ℝ) (x : M) (w : E) :
    chartCloseTriv (I := I) Φ_fam (Φ_fam t x) x t w = w := by
  classical
  unfold chartCloseTriv
  set α : M := Φ_fam t x with hα
  have hcore : trivFromE (I := I) α α
      = (tangentBundleCore I M).coordChange (achart H α) (achart H α) α :=
    TangentBundle.symmL_trivializationAt_eq_core (I := I) (M := M)
      (b₀ := α) (b := α) (mem_chart_source H α)
  rw [hcore]
  exact (tangentBundleCore I M).coordChange_self (achart H α) α
    (by rw [tangentBundleCore_baseSet]; exact mem_chart_source H α) w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.chartCloseTriv_basepoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.chartCloseTriv_basepoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.chartCloseTriv_basepoint ``Submission.DifferentialGeometry.Analysis.ODE.chartCloseTriv_basepoint

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M]
    [BoundarylessManifold I M] in
theorem chartCloseDop_hasDerivAt_clm_comp
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M) (α x : M) (t : ℝ)
    {T' P' : E →L[ℝ] E}
    (hT : HasDerivAt (chartCloseTriv (I := I) Φ_fam α x) T' t)
    (hP : HasDerivAt (chartCloseFderiv (I := I) Φ_fam α x) P' t) :
    HasDerivAt (flowOrbitChartTrivDerivOp (I := I) Φ_fam α x)
      (T'.comp (chartCloseFderiv (I := I) Φ_fam α x t)
        + (chartCloseTriv (I := I) Φ_fam α x t).comp P') t := by
  have hcomp : (fun s : ℝ =>
        (chartCloseTriv (I := I) Φ_fam α x s).comp
          (chartCloseFderiv (I := I) Φ_fam α x s))
      = flowOrbitChartTrivDerivOp (I := I) Φ_fam α x := by
    funext s
    exact (chartCloseDop_eq_comp (I := I) Φ_fam α x s).symm
  have := hT.clm_comp hP
  rwa [hcomp] at this

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.chartCloseDop_hasDerivAt_clm_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.chartCloseDop_hasDerivAt_clm_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.chartCloseDop_hasDerivAt_clm_comp ``Submission.DifferentialGeometry.Analysis.ODE.chartCloseDop_hasDerivAt_clm_comp

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M]
    [BoundarylessManifold I M] in
theorem chartCloseDop_deriv_basepoint_apply
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M) (t : ℝ) (x : M) (v : TangentSpace I x)
    (T' P' : E →L[ℝ] E) :
    (T'.comp (chartCloseFderiv (I := I) Φ_fam (Φ_fam t x) x t)
        + (chartCloseTriv (I := I) Φ_fam (Φ_fam t x) x t).comp P') v
      = T' (mfderiv I I (Φ_fam t : M → M) x v) + P' v := by
  classical
  let w : E := v
  let z : E := mfderiv I I (Φ_fam t : M → M) x v
  change (T'.comp (chartCloseFderiv (I := I) Φ_fam (Φ_fam t x) x t)
      + (chartCloseTriv (I := I) Φ_fam (Φ_fam t x) x t).comp P') w =
    T' z + P' w
  rw [add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply]
  rw [chartCloseTriv_basepoint (I := I) Φ_fam t x (P' w)]
  have hPv : chartCloseFderiv (I := I) Φ_fam (Φ_fam t x) x t w = z := by
    have hdop : flowOrbitChartTrivDerivOp (I := I) Φ_fam (Φ_fam t x) x t w
        = chartCloseFderiv (I := I) Φ_fam (Φ_fam t x) x t w := by
      rw [chartCloseDop_apply]
      exact chartCloseTriv_basepoint (I := I) Φ_fam t x
        (chartCloseFderiv (I := I) Φ_fam (Φ_fam t x) x t w)
    rw [← hdop]
    have hbase := chartCloseDop_basepoint_apply_eq_mfderiv (I := I) Φ_fam t x v
    change flowOrbitChartTrivDerivOp (I := I) Φ_fam (Φ_fam t x) x t w = z at hbase
    exact hbase
  rw [hPv]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.chartCloseDop_deriv_basepoint_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.chartCloseDop_deriv_basepoint_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.chartCloseDop_deriv_basepoint_apply ``Submission.DifferentialGeometry.Analysis.ODE.chartCloseDop_deriv_basepoint_apply

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem rawVariationalIdentity_of_orbitODE_factors
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v : TangentSpace I x)
    {T' P' : E →L[ℝ] E}
    (hT : HasDerivAt (chartCloseTriv (I := I) Φ_fam (Φ_fam t x) x) T' t)
    (hP : HasDerivAt (chartCloseFderiv (I := I) Φ_fam (Φ_fam t x) x) P' t)
    (hcont : Continuous (fun s : ℝ => (Φ_fam s : M → M) x))
    (hRdiff : DifferentiableAt ℝ
      (chartRawRepr (I := I) (Φ_fam t x) (X : ∀ y : M, TangentSpace I y))
      (extChartAt I (Φ_fam t x) (Φ_fam t x)))
    (hCdiff : DifferentiableAt ℝ
      (fun z => chartMovingTriv (I := I) (Φ_fam t x) z)
      (extChartAt I (Φ_fam t x) (Φ_fam t x)))
    (hsplit : (T'.comp (chartCloseFderiv (I := I) Φ_fam (Φ_fam t x) x t)
        + (chartCloseTriv (I := I) Φ_fam (Φ_fam t x) x t).comp P') v
      = -trivFromE (I := I) (Φ_fam t x) (Φ_fam t x)
            (fderiv ℝ (chartTrivRepr (I := I) (Φ_fam t x)
                (X : ∀ y : M, TangentSpace I y))
              (extChartAt I (Φ_fam t x) (Φ_fam t x))
              (mfderiv I I (Φ_fam t : M → M) x v))
        + (-trivFromE (I := I) (Φ_fam t x) (Φ_fam t x)
            (christoffelCorrection (I := I) g (Φ_fam t x) (Φ_fam t x)
              (chartESectionRepr (I := I) (Φ_fam t x)
                (X : ∀ y : M, TangentSpace I y) (Φ_fam t x))
              (mfderiv I I (Φ_fam t : M → M) x v)))) :
    RawVariationalIdentity (I := I) g X Φ_fam t x v := by
  have hDchart := chartCloseDop_hasDerivAt_clm_comp (I := I) Φ_fam (Φ_fam t x) x t hT hP
  exact rawVariationalIdentity_of_manifoldFlowFamily_chartClose (I := I) g X Φ_fam t x v
    hcont hDchart hRdiff hCdiff hsplit

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.rawVariationalIdentity_of_orbitODE_factors then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.rawVariationalIdentity_of_orbitODE_factors"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.rawVariationalIdentity_of_orbitODE_factors ``Submission.DifferentialGeometry.Analysis.ODE.rawVariationalIdentity_of_orbitODE_factors

end OrbitODE

end DifferentialGeometry.Analysis.ODE
