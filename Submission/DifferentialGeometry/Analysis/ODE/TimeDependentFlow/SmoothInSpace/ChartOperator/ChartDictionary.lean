import Submission.DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace.CovariantIdentity.Covariant
import Submission.DifferentialGeometry.Analysis.ODE.TimeDependentFlow.Regularity.PushforwardSmooth

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

section Dictionary

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem trivToE_mfderiv_eq_chartFderiv_apply
    (F : M → M) (α : M) {x : M} (v : TangentSpace I x)
    (hF : MDifferentiableAt I I F x)
    (hFx : F x ∈ (chartAt H α).source) :
    trivToE (I := I) α (F x) (mfderiv I I F x v)
      = mfderiv I 𝓘(ℝ, E) (fun y => extChartAt I α (F y)) x v := by
  have htriv : trivToE (I := I) α (F x)
      = mfderiv I 𝓘(ℝ, E) (extChartAt I α) (F x) :=
    TangentBundle.continuousLinearMapAt_trivializationAt (I := I) hFx
  have hext : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I α) (F x) :=
    mdifferentiableAt_extChartAt (I := I) hFx
  have hchain :
      mfderiv I 𝓘(ℝ, E) (extChartAt I α ∘ F) x
        = (mfderiv I 𝓘(ℝ, E) (extChartAt I α) (F x)).comp (mfderiv I I F x) :=
    mfderiv_comp x hext hF
  rw [htriv]
  have hchainApply := mfderiv_comp_apply x hext hF v
  have hfun : (fun y => extChartAt I α (F y)) = extChartAt I α ∘ F := rfl
  rw [hfun]
  exact hchainApply.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.trivToE_mfderiv_eq_chartFderiv_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.trivToE_mfderiv_eq_chartFderiv_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.trivToE_mfderiv_eq_chartFderiv_apply ``Submission.DifferentialGeometry.Analysis.ODE.trivToE_mfderiv_eq_chartFderiv_apply

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem mfderiv_flow_eq_chartFderiv_apply
    (F : M → M) (α : M) {x : M} (v : TangentSpace I x)
    (hF : MDifferentiableAt I I F x)
    (hFx : F x ∈ (chartAt H α).source) :
    mfderiv I I F x v
      = trivFromE (I := I) α (F x)
          (mfderiv I 𝓘(ℝ, E) (fun y => extChartAt I α (F y)) x v) := by
  have hbase : F x ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact hFx
  have hdict := trivToE_mfderiv_eq_chartFderiv_apply (I := I) F α v hF hFx
  calc
    mfderiv I I F x v
        = trivFromE (I := I) α (F x)
            (trivToE (I := I) α (F x) (mfderiv I I F x v)) :=
          (trivFromE_trivToE (I := I) α hbase (mfderiv I I F x v)).symm
    _ = trivFromE (I := I) α (F x)
            (mfderiv I 𝓘(ℝ, E) (fun y => extChartAt I α (F y)) x v) := by
          rw [hdict]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.mfderiv_flow_eq_chartFderiv_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.mfderiv_flow_eq_chartFderiv_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.mfderiv_flow_eq_chartFderiv_apply ``Submission.DifferentialGeometry.Analysis.ODE.mfderiv_flow_eq_chartFderiv_apply

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem orbit_continuousAt_of_jointContinuous
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M) (t : ℝ) (x : M)
    (hcont : Continuous (fun s : ℝ => (Φ_fam s : M → M) x)) :
    ContinuousAt (fun s : ℝ => (Φ_fam s : M → M) x) t :=
  hcont.continuousAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.orbit_continuousAt_of_jointContinuous then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.orbit_continuousAt_of_jointContinuous"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.orbit_continuousAt_of_jointContinuous ``Submission.DifferentialGeometry.Analysis.ODE.orbit_continuousAt_of_jointContinuous

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem flow_orbit_eventually_mem_chartAt_source
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M) (t : ℝ) (x : M)
    (hcontAt : ContinuousAt (fun s : ℝ => (Φ_fam s : M → M) x) t) :
    ∀ᶠ s : ℝ in 𝓝 t, (Φ_fam s : M → M) x ∈ (chartAt H (Φ_fam t x)).source := by
  have hsrc_mem : (chartAt H (Φ_fam t x)).source ∈ 𝓝 (Φ_fam t x) :=
    (chartAt H (Φ_fam t x)).open_source.mem_nhds (mem_chart_source H (Φ_fam t x))
  exact hcontAt.eventually_mem hsrc_mem

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.flow_orbit_eventually_mem_chartAt_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.flow_orbit_eventually_mem_chartAt_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.flow_orbit_eventually_mem_chartAt_source ``Submission.DifferentialGeometry.Analysis.ODE.flow_orbit_eventually_mem_chartAt_source

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem chartFderiv_eventuallyEq
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M) (t : ℝ) (x : M) (v : TangentSpace I x)
    (Q : E →L[ℝ] E) (d : E) (Dchart : ℝ → (E →L[ℝ] E))
    (hcontAt : ContinuousAt (fun s : ℝ => (Φ_fam s : M → M) x) t)
    (hwitness : (fun s : ℝ =>
        trivFromE (I := I) (Φ_fam t x) ((Φ_fam s : M → M) x)
          (mfderiv I 𝓘(ℝ, E)
            (fun y => extChartAt I (Φ_fam t x) ((Φ_fam s : M → M) y)) x v))
      =ᶠ[𝓝 t] (fun s : ℝ => Q (Dchart s d))) :
    (fun s : ℝ => (mfderiv I I (Φ_fam s : M → M) x v : E))
      =ᶠ[𝓝 t] (fun s : ℝ => Q (Dchart s d)) := by
  have hmem := flow_orbit_eventually_mem_chartAt_source (I := I) Φ_fam t x hcontAt
  have hinfty : (∞ : WithTop ℕ∞) ≠ 0 := by decide
  have hstep : (fun s : ℝ => (mfderiv I I (Φ_fam s : M → M) x v : E))
      =ᶠ[𝓝 t] (fun s : ℝ =>
        trivFromE (I := I) (Φ_fam t x) ((Φ_fam s : M → M) x)
          (mfderiv I 𝓘(ℝ, E)
            (fun y => extChartAt I (Φ_fam t x) ((Φ_fam s : M → M) y)) x v)) := by
    filter_upwards [hmem] with s hs
    exact mfderiv_flow_eq_chartFderiv_apply (I := I) (Φ_fam s : M → M) (Φ_fam t x) v
      ((Φ_fam s).mdifferentiable hinfty x) hs
  exact hstep.trans hwitness

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.chartFderiv_eventuallyEq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.chartFderiv_eventuallyEq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.chartFderiv_eventuallyEq ``Submission.DifferentialGeometry.Analysis.ODE.chartFderiv_eventuallyEq

end Dictionary

section Producer

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem rawVariationalIdentity_of_chartFderiv_eventuallyEq
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v : TangentSpace I x)
    (Q : E →L[ℝ] E) (d : E)
    {Dchart : ℝ → (E →L[ℝ] E)} {Dchart' : E →L[ℝ] E}
    (hDchart : HasDerivAt Dchart Dchart' t)
    (hcontAt : ContinuousAt (fun s : ℝ => (Φ_fam s : M → M) x) t)
    (hwitness : (fun s : ℝ =>
        trivFromE (I := I) (Φ_fam t x) ((Φ_fam s : M → M) x)
          (mfderiv I 𝓘(ℝ, E)
            (fun y => extChartAt I (Φ_fam t x) ((Φ_fam s : M → M) y)) x v))
      =ᶠ[𝓝 t] (fun s : ℝ => Q (Dchart s d)))
    (hQinner : Q (Dchart' d)
      = -trivFromE (I := I) (Φ_fam t x) (Φ_fam t x)
          (chartLeviCivitaInnerCLM (I := I) g (Φ_fam t x)
            (X : ∀ x : M, TangentSpace I x) (Φ_fam t x)
            (mfderiv I I (Φ_fam t : M → M) x v))) :
    RawVariationalIdentity (I := I) g X Φ_fam t x v := by
  have hagree :=
    chartFderiv_eventuallyEq (I := I) Φ_fam t x v Q d Dchart hcontAt hwitness
  exact rawVariationalIdentity_of_chartFlow_innerCLM (I := I) g X Φ_fam t x v Q d
    hDchart hagree hQinner

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.rawVariationalIdentity_of_chartFderiv_eventuallyEq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.rawVariationalIdentity_of_chartFderiv_eventuallyEq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.rawVariationalIdentity_of_chartFderiv_eventuallyEq ``Submission.DifferentialGeometry.Analysis.ODE.rawVariationalIdentity_of_chartFderiv_eventuallyEq

end Producer

end DifferentialGeometry.Analysis.ODE
