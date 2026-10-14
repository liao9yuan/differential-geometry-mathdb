import Submission.DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace.CovariantIdentity.ConcreteFlow

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

section OrbitReduction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M]
    [BoundarylessManifold I M] in
theorem chartCloseDop_apply_eq_mfderiv
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M) (α x : M) (s : ℝ) (v : TangentSpace I x)
    (hsrc : (Φ_fam s : M → M) x ∈ (chartAt H α).source) :
    flowOrbitChartTrivDerivOp (I := I) Φ_fam α x s v = mfderiv I I (Φ_fam s : M → M) x v := by
  have hF : MDifferentiableAt I I (Φ_fam s : M → M) x :=
    flowFamily_mdifferentiableAt_fixed_time (I := I) Φ_fam s x
  rw [chartCloseDop_apply]
  exact (mfderiv_flow_eq_chartFderiv_apply (I := I) (Φ_fam s : M → M) α v hF hsrc).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.chartCloseDop_apply_eq_mfderiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.chartCloseDop_apply_eq_mfderiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.chartCloseDop_apply_eq_mfderiv ``Submission.DifferentialGeometry.Analysis.ODE.chartCloseDop_apply_eq_mfderiv

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M]
    [BoundarylessManifold I M] in
theorem chartCloseDop_basepoint_apply_eq_mfderiv
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M) (t : ℝ) (x : M) (v : TangentSpace I x) :
    flowOrbitChartTrivDerivOp (I := I) Φ_fam (Φ_fam t x) x t v
      = mfderiv I I (Φ_fam t : M → M) x v :=
  chartCloseDop_apply_eq_mfderiv (I := I) Φ_fam (Φ_fam t x) x t v (mem_chart_source H _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.chartCloseDop_basepoint_apply_eq_mfderiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.chartCloseDop_basepoint_apply_eq_mfderiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.chartCloseDop_basepoint_apply_eq_mfderiv ``Submission.DifferentialGeometry.Analysis.ODE.chartCloseDop_basepoint_apply_eq_mfderiv

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M]
    [BoundarylessManifold I M] in
theorem chartCloseDop_eventuallyEq_mfderiv_orbit
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M) (t : ℝ) (x : M) (v : TangentSpace I x)
    (hcontAt : ContinuousAt (fun s : ℝ => (Φ_fam s : M → M) x) t) :
    (fun s : ℝ => flowOrbitChartTrivDerivOp (I := I) Φ_fam (Φ_fam t x) x s v)
      =ᶠ[𝓝 t] (fun s : ℝ => mfderiv I I (Φ_fam s : M → M) x v) := by
  have hmem : ∀ᶠ s : ℝ in 𝓝 t,
      (Φ_fam s : M → M) x ∈ (chartAt H (Φ_fam t x)).source :=
    flow_orbit_eventually_mem_chartAt_source (I := I) Φ_fam t x hcontAt
  filter_upwards [hmem] with s hs
  exact chartCloseDop_apply_eq_mfderiv (I := I) Φ_fam (Φ_fam t x) x s v hs

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.chartCloseDop_eventuallyEq_mfderiv_orbit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.chartCloseDop_eventuallyEq_mfderiv_orbit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.chartCloseDop_eventuallyEq_mfderiv_orbit ``Submission.DifferentialGeometry.Analysis.ODE.chartCloseDop_eventuallyEq_mfderiv_orbit

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] [T2Space M] in
theorem rawVariationalIdentity_iff_hasDerivAt_chartCloseDop
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v : TangentSpace I x)
    (hcontAt : ContinuousAt (fun s : ℝ => (Φ_fam s : M → M) x) t) :
    RawVariationalIdentity (I := I) g X Φ_fam t x v
      ↔ HasDerivAt (fun s : ℝ => flowOrbitChartTrivDerivOp (I := I) Φ_fam (Φ_fam t x) x s v)
          (-(LeviCivita (I := I) g) (X : ∀ x : M, TangentSpace I x) (Φ_fam t x)
            (mfderiv I I (Φ_fam t : M → M) x v)) t := by
  unfold RawVariationalIdentity
  exact (Filter.EventuallyEq.hasDerivAt_iff
    (chartCloseDop_eventuallyEq_mfderiv_orbit (I := I) Φ_fam t x v hcontAt)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.rawVariationalIdentity_iff_hasDerivAt_chartCloseDop then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.rawVariationalIdentity_iff_hasDerivAt_chartCloseDop"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.rawVariationalIdentity_iff_hasDerivAt_chartCloseDop ``Submission.DifferentialGeometry.Analysis.ODE.rawVariationalIdentity_iff_hasDerivAt_chartCloseDop

end OrbitReduction

end DifferentialGeometry.Analysis.ODE
