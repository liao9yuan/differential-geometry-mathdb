import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.Basic
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Parametric.Evaluation
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.ExpDensity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.MinNonconjugacy

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Function _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.Submission.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
  {D : RealTimeInterval}

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

section VolumeDefinition

variable [T2Space M] [SigmaCompactSpace M]

noncomputable def redVolume
    (S : SolutionOn (I := I) (M := M) D)
    (T : ℝ) (x : M) (tau : ℝ) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal
    (DifferentialGeometry.PDE.RicciFlow.Perelman.redDensity S T x y tau)
    ∂riemannianVolumeMeasure (I := I) (M := M)
      (S.base.metric (T - tau))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.redVolume then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.redVolume"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.redVolume ``Submission.DifferentialGeometry.PDE.RicciFlow.redVolume

theorem redVolume_eq_upstream [CompactSpace M]
    (S : SolutionOn (I := I) (M := M) D)
    (T : ℝ) (x : M) (tau : ℝ) :
    DifferentialGeometry.PDE.RicciFlow.redVolume S T x tau =
      DifferentialGeometry.PDE.RicciFlow.Perelman.redVolume S T x tau := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.redVolume_eq_upstream then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.redVolume_eq_upstream"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.redVolume_eq_upstream ``Submission.DifferentialGeometry.PDE.RicciFlow.redVolume_eq_upstream

end VolumeDefinition

theorem paramDensity_eq_lExpDensity_of_eqOn [I.Boundaryless] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (T : ℝ) (x : M) (tau : ℝ)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    (hEq : Set.EqOn Ψ (fun W : E ↦ lExp S T x W tau) Ψ.source)
    (Z : E) (hZ : Z ∈ Ψ.source) :
    paramDensity (I := I) (S.base.metric (T - tau)) Ψ Z =
      lExpDensity S T x Z tau := by
  have hev : (Ψ : E → M) =ᶠ[𝓝 Z] (fun W : E ↦ lExp S T x W tau) := by
    refine Filter.eventuallyEq_of_mem (Ψ.open_source.mem_nhds hZ) ?_
    intro W hW
    exact hEq hW
  unfold paramDensity paramGramMatrix lExpDensity lExpGram lGram lExpField
  rw [hev.eq_of_nhds,
    hev.mfderiv_eq (I := modelWithCornersSelf ℝ E) (I' := I)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.paramDensity_eq_lExpDensity_of_eqOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.paramDensity_eq_lExpDensity_of_eqOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.paramDensity_eq_lExpDensity_of_eqOn ``Submission.DifferentialGeometry.PDE.RicciFlow.paramDensity_eq_lExpDensity_of_eqOn

section NonconjugateNormalization

variable [I.Boundaryless] [T2Space M]

theorem lRedJac_mul_src_of_nonconj
    (S : SolutionOn (I := I) (M := M) D)
    (T : ℝ) (x : M) (Z : TangentSpace I x) (tau : ℝ)
    (hdom : (Z, tau) ∈ lExpPosDom S T x)
    (hnconj : ¬ IsLConjugate S T x Z tau) :
    lReducedJacobian S T x Z tau * lSourceDensity S T x =
      lExpDensity S T x Z tau *
        DifferentialGeometry.PDE.RicciFlow.Perelman.redDensity
          S T x (lExp S T x Z tau) tau := by
  have hJ : 0 < lExpJacobian S T x Z tau :=
    lExpJac_pos_of_nonconj S T x Z tau hdom hnconj
  have hred : lReducedJacobian S T x Z tau =
      lExpJacobian S T x Z tau *
        DifferentialGeometry.PDE.RicciFlow.Perelman.redDensity
          S T x (lExp S T x Z tau) tau := by
    rw [lReducedJacobian, lRedLog,
      DifferentialGeometry.PDE.RicciFlow.Perelman.redDensity]
    have hexp :
        Real.log (lExpJacobian S T x Z tau) -
            redLength S T x (lExp S T x Z tau) tau -
            ((Module.finrank ℝ E : ℝ) / 2) * Real.log tau -
            ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi) =
          Real.log (lExpJacobian S T x Z tau) +
            (-redLength S T x (lExp S T x Z tau) tau -
              ((Module.finrank ℝ E : ℝ) / 2) * Real.log tau -
              ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi)) := by
      ring
    rw [hexp, Real.exp_add, Real.exp_log hJ]
  rw [hred, lExpJacobian]
  field_simp [ne_of_gt (lSourceDensity_pos S T x)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.lRedJac_mul_src_of_nonconj then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.lRedJac_mul_src_of_nonconj"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.lRedJac_mul_src_of_nonconj ``Submission.DifferentialGeometry.PDE.RicciFlow.lRedJac_mul_src_of_nonconj

private theorem original_inj_domain_nonconj
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : ℝ) (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → _root_.Set.Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ _root_.Set.Icc (T - sigma) T, ∀ y : M,
        normSq0S (I := I) (S.base.metric t) y 4
          (S.base.rm04 t y) ≤ K)
    (tau : ℝ) (htau : 0 < tau) {Z : E}
    (hZ : Z ∈ lInjDomain S T x tau) :
    (Z, tau) ∈ lExpPosDom S T x ∧ ¬ IsLConjugate S T x Z tau := by
  obtain ⟨sigma, hlt, hmin⟩ := hZ
  have hsigma : 0 < sigma := lMinDomain_pos S T x Z sigma hmin
  have hdomSigma : (Z, sigma) ∈ lExpPosDom S T x :=
    ((mem_lMinDomain S T x Z sigma).mp hmin).1
  have hreg : _root_.Set.Icc (T - sigma) T ⊆ D.regular := by
    intro t ht
    have hnonneg : 0 ≤ T - t := sub_nonneg.mpr ht.2
    have hback : T - t ≤ sigma := by linarith only [ht.1]
    have hsqrt : Real.sqrt (T - t) ∈ _root_.Set.Icc (0 : ℝ) (Real.sqrt sigma) :=
      ⟨Real.sqrt_nonneg _, Real.sqrt_le_sqrt hback⟩
    have hclock := lExpPosDom_regularity S T x Z hdomSigma hsqrt
    have heq : T - (Real.sqrt (T - t)) ^ 2 = t := by
      rw [Real.sq_sqrt hnonneg]
      ring
    simpa only [heq] using hclock
  obtain ⟨K, hK⟩ := hRm sigma hsigma hreg
  exact ⟨lExpPosDom_down S T x Z hdomSigma htau hlt.le,
    lMinVec_nconj_lt_of_rm S hS K T x hmin hlt hK⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.original_inj_domain_nonconj
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.original_inj_domain_nonconj target :: scope.openDecls } }

end NonconjugateNormalization

section ChangeOfVariables

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

theorem redVolume_lint_of_param
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : ℝ) (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → _root_.Set.Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ _root_.Set.Icc (T - sigma) T, ∀ y : M,
        normSq0S (I := I) (S.base.metric t) y 4
          (S.base.rm04 t y) ≤ K)
    (tau : ℝ) (htau : 0 < tau)
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞)
    (hsource : Φ.source = lInjDomain S T x tau)
    (hmap : Set.EqOn Φ (fun Z : E ↦ lExp S T x Z tau)
      (lInjDomain S T x tau))
    (hnull : riemannianVolumeMeasure (I := I) (M := M)
      (S.base.metric (T - tau)) Φ.targetᶜ = 0) :
    DifferentialGeometry.PDE.RicciFlow.redVolume S T x tau =
      ∫⁻ Z in lInjDomain S T x tau,
        ENNReal.ofReal (lReducedJacobian S T x Z tau * lSourceDensity S T x)
        ∂modelHaar (E := E) := by
  let U : Set E := lInjDomain S T x tau
  let Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1 :=
    { toPartialEquiv := Φ.toPartialEquiv
      open_source := Φ.open_source
      open_target := Φ.open_target
      contMDiffOn_toFun := Φ.contMDiffOn_toFun.of_le (by norm_num)
      contMDiffOn_invFun := Φ.contMDiffOn_invFun.of_le (by norm_num) }
  have hUeq : U = Ψ.source := hsource.symm
  have hUmeas : MeasurableSet U := by
    rw [hUeq]
    exact Ψ.open_source.measurableSet
  have hUsource : U ⊆ Ψ.source := by
    rw [hUeq]
  have hΨmap : Set.EqOn Ψ (fun Z : E ↦ lExp S T x Z tau) Ψ.source := by
    intro Z hZ
    apply hmap
    change Z ∈ U
    rw [hUeq]
    exact hZ
  have himage : Ψ '' U = Φ.target := by
    rw [hUeq]
    exact Ψ.toPartialEquiv.image_source_eq_target
  have htarget : Φ.target ∈ _root_.MeasureTheory.ae
      (riemannianVolumeMeasure (I := I) (M := M)
        (S.base.metric (T - tau))) :=
    mem_ae_iff.mpr hnull
  calc
    DifferentialGeometry.PDE.RicciFlow.redVolume S T x tau =
        ∫⁻ y in Ψ '' U, ENNReal.ofReal
          (DifferentialGeometry.PDE.RicciFlow.Perelman.redDensity S T x y tau)
          ∂riemannianVolumeMeasure (I := I) (M := M)
            (S.base.metric (T - tau)) := by
      unfold DifferentialGeometry.PDE.RicciFlow.redVolume
      rw [himage]
      exact congrArg
        (fun μ : _root_.MeasureTheory.Measure M ↦ ∫⁻ y, ENNReal.ofReal
          (DifferentialGeometry.PDE.RicciFlow.Perelman.redDensity S T x y tau) ∂μ)
        (Measure.restrict_eq_self_of_ae_mem htarget).symm
    _ = ∫⁻ Z in U,
        ENNReal.ofReal (paramDensity (I := I) (S.base.metric (T - tau)) Ψ Z) *
          ENNReal.ofReal
            (DifferentialGeometry.PDE.RicciFlow.Perelman.redDensity
              S T x (Ψ Z) tau)
        ∂modelHaar (E := E) :=
      riemVol_param_lint (I := I) (S.base.metric (T - tau)) Ψ
        (fun y ↦ ENNReal.ofReal
          (DifferentialGeometry.PDE.RicciFlow.Perelman.redDensity S T x y tau))
        hUmeas hUsource
    _ = ∫⁻ Z in U,
        ENNReal.ofReal (lReducedJacobian S T x Z tau * lSourceDensity S T x)
        ∂modelHaar (E := E) := by
      refine MeasureTheory.setLIntegral_congr_fun hUmeas ?_
      intro Z hZ
      dsimp only
      have hZsrc : Z ∈ Ψ.source := hUsource hZ
      have hΨZ : Ψ Z = lExp S T x Z tau := hΨmap hZsrc
      obtain ⟨hdom, hnconj⟩ :=
        original_inj_domain_nonconj S hS T x hRm tau htau hZ
      rw [paramDensity_eq_lExpDensity_of_eqOn S T x tau Ψ hΨmap Z hZsrc,
        hΨZ]
      rw [← ENNReal.ofReal_mul
        (lExpDensity_pos_of_nonconj S T x Z tau hdom hnconj).le]
      exact congrArg ENNReal.ofReal
        (lRedJac_mul_src_of_nonconj S T x Z tau hdom hnconj).symm
    _ = ∫⁻ Z in lInjDomain S T x tau,
        ENNReal.ofReal (lReducedJacobian S T x Z tau * lSourceDensity S T x)
        ∂modelHaar (E := E) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.redVolume_lint_of_param then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.redVolume_lint_of_param"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.redVolume_lint_of_param ``Submission.DifferentialGeometry.PDE.RicciFlow.redVolume_lint_of_param

end ChangeOfVariables

end DifferentialGeometry.PDE.RicciFlow

end
