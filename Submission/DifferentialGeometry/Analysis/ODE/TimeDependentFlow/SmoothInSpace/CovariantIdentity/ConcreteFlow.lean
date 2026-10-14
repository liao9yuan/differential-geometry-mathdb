import Submission.DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace.CovariantIdentity.ManifoldFlow

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Connection


noncomputable section

namespace DifferentialGeometry.Analysis.ODE

open _root_.Set _root_.Function _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff

open _root_.Submission.DifferentialGeometry.Integral.Measure

section Close

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

def flowOrbitChartTrivDerivOp (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M) (α x : M) (s : ℝ) : E →L[ℝ] E :=
  (trivFromE (I := I) α ((Φ_fam s : M → M) x)).comp
    (mfderiv I 𝓘(ℝ, E)
      (fun y => extChartAt I α ((Φ_fam s : M → M) y)) x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.flowOrbitChartTrivDerivOp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.flowOrbitChartTrivDerivOp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.flowOrbitChartTrivDerivOp ``Submission.DifferentialGeometry.Analysis.ODE.flowOrbitChartTrivDerivOp

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M]
    [BoundarylessManifold I M] in
lemma chartCloseDop_apply
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M) (α x : M) (s : ℝ) (v : TangentSpace I x) :
    flowOrbitChartTrivDerivOp (I := I) Φ_fam α x s v
      = trivFromE (I := I) α ((Φ_fam s : M → M) x)
          (mfderiv I 𝓘(ℝ, E)
            (fun y => extChartAt I α ((Φ_fam s : M → M) y)) x v) := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.chartCloseDop_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.chartCloseDop_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.chartCloseDop_apply ``Submission.DifferentialGeometry.Analysis.ODE.chartCloseDop_apply

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M]
    [BoundarylessManifold I M] in
theorem mfderiv_flowOrbit_eventuallyEq_flowOrbitChartTrivDerivOp
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M) (t : ℝ) (x : M) (v : TangentSpace I x) :
    (fun s : ℝ =>
        trivFromE (I := I) (Φ_fam t x) ((Φ_fam s : M → M) x)
          (mfderiv I 𝓘(ℝ, E)
            (fun y => extChartAt I (Φ_fam t x) ((Φ_fam s : M → M) y)) x v))
      =ᶠ[𝓝 t] (fun s : ℝ =>
        (ContinuousLinearMap.id ℝ E)
          (flowOrbitChartTrivDerivOp (I := I) Φ_fam (Φ_fam t x) x s v)) := by
  refine Filter.Eventually.of_forall (fun s => ?_)
  simp only [ContinuousLinearMap.id_apply]
  exact (chartCloseDop_apply (I := I) Φ_fam (Φ_fam t x) x s v).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.mfderiv_flowOrbit_eventuallyEq_flowOrbitChartTrivDerivOp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.mfderiv_flowOrbit_eventuallyEq_flowOrbitChartTrivDerivOp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.mfderiv_flowOrbit_eventuallyEq_flowOrbitChartTrivDerivOp ``Submission.DifferentialGeometry.Analysis.ODE.mfderiv_flowOrbit_eventuallyEq_flowOrbitChartTrivDerivOp

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem rawVariationalIdentity_of_manifoldFlowFamily_chartClose
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v : TangentSpace I x)
    {Dchart' : E →L[ℝ] E}
    (hcont : Continuous (fun s : ℝ => (Φ_fam s : M → M) x))
    (hDchart : HasDerivAt (flowOrbitChartTrivDerivOp (I := I) Φ_fam (Φ_fam t x) x) Dchart' t)
    (hRdiff : DifferentiableAt ℝ
      (chartRawRepr (I := I) (Φ_fam t x) (X : ∀ y : M, TangentSpace I y))
      (extChartAt I (Φ_fam t x) (Φ_fam t x)))
    (hCdiff : DifferentiableAt ℝ
      (fun z => chartMovingTriv (I := I) (Φ_fam t x) z)
      (extChartAt I (Φ_fam t x) (Φ_fam t x)))
    (hsplit : (ContinuousLinearMap.id ℝ E) (Dchart' v)
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
    RawVariationalIdentity (I := I) g X Φ_fam t x v :=
  rawVariationalIdentity_of_manifoldFlowFamily (I := I) g X Φ_fam t x v
    (ContinuousLinearMap.id ℝ E) v hcont hDchart
    (mfderiv_flowOrbit_eventuallyEq_flowOrbitChartTrivDerivOp (I := I) Φ_fam t x v) hRdiff hCdiff
      hsplit

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.rawVariationalIdentity_of_manifoldFlowFamily_chartClose then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.rawVariationalIdentity_of_manifoldFlowFamily_chartClose"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.rawVariationalIdentity_of_manifoldFlowFamily_chartClose ``Submission.DifferentialGeometry.Analysis.ODE.rawVariationalIdentity_of_manifoldFlowFamily_chartClose

end Close

end DifferentialGeometry.Analysis.ODE
