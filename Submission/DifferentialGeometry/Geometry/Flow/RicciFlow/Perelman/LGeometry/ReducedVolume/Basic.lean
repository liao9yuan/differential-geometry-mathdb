import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.Measure
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Parametric.Evaluation
import Submission.DifferentialGeometry.Geometry.Metric.Path.Length
import Submission.DifferentialGeometry.Geometry.Comparison.NormalCoordinates.ExponentialBallPartialDiffeomorph
import Submission.DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.CutLocus.MeasureZero
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Jacobian.Monotonicity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

section DensityBound

open scoped _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}

theorem redDensity_le_of_redLength_ge
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (x y : M) (tau C : ℝ)
    (hlen : -C ≤ redLength S T x y tau) :
    redDensity S T x y tau ≤ Real.exp
      (C - ((Module.finrank ℝ E : ℝ) / 2) * Real.log tau -
        ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi)) := by
  unfold redDensity
  apply Real.exp_le_exp.mpr
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.redDensity_le_of_redLength_ge then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.redDensity_le_of_redLength_ge"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.redDensity_le_of_redLength_ge ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.redDensity_le_of_redLength_ge

end DensityBound

open _root_.Bundle _root_.Submission.Bundle _root_.Set
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.Submission.Topology

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.MeasureTheory _root_.Submission.MeasureTheory

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
variable {D : RealTimeInterval}

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [T2Space M]
  [CompactSpace M] in
theorem redDensity_pos
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (x y : M)
    (tau : Real) : 0 < redDensity S T x y tau :=
  Real.exp_pos _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.redDensity_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.redDensity_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.redDensity_pos ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.redDensity_pos

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] in
private theorem exists_lExpPartial
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    (tau : Real) (htau : 0 < tau) :
    ∃ Φ : PartialDiffeomorph (modelWithCornersSelf Real E) I E M 1,
      Φ.source = lInjDomain S T x tau ∧
      Φ.target =
        (fun Z : E ↦ lExp S T x Z tau) '' lInjDomain S T x tau ∧
      Set.EqOn Φ (fun Z : E ↦ lExp S T x Z tau)
        (lInjDomain S T x tau) := by
  let f : E → M := fun Z ↦ lExp S T x Z tau
  let U : Set E := lInjDomain S T x tau
  have hdomain : IsOpen U ∧ _root_.Set.InjOn f U := by
    by_cases hdim : Module.finrank ℝ E = 0
    · let : Subsingleton E := Module.finrank_zero_iff.mp hdim
      exact ⟨isOpen_discrete _, fun _ _ _ _ _ => Subsingleton.elim _ _⟩
    · let : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
      exact ⟨lInj_isOpen S hS T x tau, lInj_inj S hS T x tau htau⟩
  have hlocal : IsLocalDiffeomorphOn (modelWithCornersSelf Real E) I ∞ f U := by
    rintro ⟨Z, hZ⟩
    exact lInj_local S hS T x tau htau hZ
  obtain ⟨Φ, hsource, htarget, hEq⟩ :=
    DifferentialGeometry.Geometry.Riemannian.exists_partial_diffeomorph_of_is_local_diffeomorph_on_inj_on
      hlocal hdomain.1 hdomain.2
  let Ψ : PartialDiffeomorph (modelWithCornersSelf Real E) I E M 1 :=
    { toPartialEquiv := Φ.toPartialEquiv
      open_source := Φ.open_source
      open_target := Φ.open_target
      contMDiffOn_toFun := Φ.contMDiffOn_toFun.of_le (by norm_num)
      contMDiffOn_invFun := Φ.contMDiffOn_invFun.of_le (by norm_num) }
  refine ⟨Ψ, ?_, ?_, ?_⟩
  · simpa only [Ψ, U] using hsource
  · simpa only [Ψ, f, U] using htarget
  · simpa only [Ψ, f, U] using hEq

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.exists_lExpPartial
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.exists_lExpPartial target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
noncomputable def lExpPartial
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    (tau : Real) (htau : 0 < tau) :
    PartialDiffeomorph (modelWithCornersSelf Real E) I E M 1 :=
  Classical.choose (exists_lExpPartial S hS T x tau htau)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lExpPartial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lExpPartial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lExpPartial ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lExpPartial

omit [NeZero (Module.finrank ℝ E)] in
theorem lExpPartial_source
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    (tau : Real) (htau : 0 < tau) :
    (lExpPartial S hS T x tau htau).source = lInjDomain S T x tau :=
  (Classical.choose_spec (exists_lExpPartial S hS T x tau htau)).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lExpPartial_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lExpPartial_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lExpPartial_source ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lExpPartial_source

omit [NeZero (Module.finrank ℝ E)] in
theorem lExpPartial_target
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    (tau : Real) (htau : 0 < tau) :
    (lExpPartial S hS T x tau htau).target =
      (fun Z : E ↦ lExp S T x Z tau) '' lInjDomain S T x tau :=
  (Classical.choose_spec (exists_lExpPartial S hS T x tau htau)).2.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lExpPartial_target then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lExpPartial_target"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lExpPartial_target ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lExpPartial_target

omit [NeZero (Module.finrank ℝ E)] in
theorem lExpPartial_apply
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    (tau : Real) (htau : 0 < tau) {Z : E}
    (hZ : Z ∈ lInjDomain S T x tau) :
    lExpPartial S hS T x tau htau Z = lExp S T x Z tau :=
  (Classical.choose_spec (exists_lExpPartial S hS T x tau htau)).2.2 hZ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lExpPartial_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lExpPartial_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lExpPartial_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lExpPartial_apply

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] in
theorem lExpPartial_density
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    (tau : Real) (htau : 0 < tau) {Z : E}
    (hZ : Z ∈ lInjDomain S T x tau) :
    paramDensity (S.base.metric (T - tau))
        (lExpPartial S hS T x tau htau) Z =
      lExpDensity S T x Z tau := by
  have hsource : Z ∈ (lExpPartial S hS T x tau htau).source := by
    rw [lExpPartial_source S hS T x tau htau]
    exact hZ
  have hev :
      (lExpPartial S hS T x tau htau : E → M) =ᶠ[nhds Z]
        (fun W : E ↦ lExp S T x W tau) := by
    refine Filter.eventuallyEq_of_mem
      ((lExpPartial S hS T x tau htau).open_source.mem_nhds hsource) ?_
    intro W hW
    apply lExpPartial_apply S hS T x tau htau
    rw [← lExpPartial_source S hS T x tau htau]
    exact hW
  unfold paramDensity paramGramMatrix lExpDensity lExpGram lGram lExpField
  rw [hev.eq_of_nhds,
    hev.mfderiv_eq (I := modelWithCornersSelf Real E) (I' := I)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lExpPartial_density then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lExpPartial_density"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lExpPartial_density ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lExpPartial_density

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] in
theorem lReducedJacobian_eq
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    {Z : TangentSpace I x} {tau : Real}
    (htau : 0 < tau)
    (hZ : Z ∈ lInjDomain (E := E) (I := I) S T x tau) :
    lReducedJacobian S T x Z tau =
      lExpJacobian S T x Z tau *
        redDensity S T x (lExp S T x Z tau) tau := by
  have hJ : 0 < lExpJacobian S T x Z tau :=
    lExpJacobian_pos S hS T x htau hZ
  rw [lReducedJacobian, lRedLog, redDensity]
  have hexp :
      Real.log (lExpJacobian S T x Z tau) -
          redLength S T x (lExp S T x Z tau) tau -
          ((Module.finrank Real E : Real) / 2) * Real.log tau -
          ((Module.finrank Real E : Real) / 2) * Real.log (4 * Real.pi) =
        Real.log (lExpJacobian S T x Z tau) +
          (-redLength S T x (lExp S T x Z tau) tau -
            ((Module.finrank Real E : Real) / 2) * Real.log tau -
            ((Module.finrank Real E : Real) / 2) * Real.log (4 * Real.pi)) := by
    ring
  rw [hexp, Real.exp_add, Real.exp_log hJ]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lReducedJacobian_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lReducedJacobian_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lReducedJacobian_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lReducedJacobian_eq

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] in
theorem lReducedJacobian_mul_source
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    {Z : TangentSpace I x} {tau : Real}
    (htau : 0 < tau)
    (hZ : Z ∈ lInjDomain (E := E) (I := I) S T x tau) :
    lReducedJacobian S T x Z tau * lSourceDensity S T x =
      lExpDensity S T x Z tau *
        redDensity S T x (lExp S T x Z tau) tau := by
  rw [lReducedJacobian_eq S hS T x htau hZ, lExpJacobian]
  field_simp [ne_of_gt (lSourceDensity_pos S T x)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lReducedJacobian_mul_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lReducedJacobian_mul_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lReducedJacobian_mul_source ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lReducedJacobian_mul_source

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] in
theorem lintegral_lReducedJacobian_mul_source
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (x : M) {tau : ℝ} (htau : 0 < tau)
    {A : Set E} (hAmeas : MeasurableSet A) (hAinj : A ⊆ lInjDomain S T x tau) :
    (∫⁻ Z in A, ENNReal.ofReal (lReducedJacobian S T x Z tau * lSourceDensity S T x)
      ∂modelHaar (E := E)) =
      ∫⁻ y in (fun Z : E => lExp S T x Z tau) '' A,
        ENNReal.ofReal (redDensity S T x y tau)
        ∂riemannianVolumeMeasure (I := I) (M := M) (S.base.metric (T - tau)) := by
  let Ψ := lExpPartial S hS T x tau htau
  have hAsource : A ⊆ Ψ.source := by
    rw [lExpPartial_source S hS T x tau htau]
    exact hAinj
  have himage : Ψ '' A = (fun Z : E => lExp S T x Z tau) '' A :=
    Set.image_congr fun Z hZ => lExpPartial_apply S hS T x tau htau (hAinj hZ)
  rw [← himage, riemVol_param_lint (S.base.metric (T - tau)) Ψ
    (fun y => ENNReal.ofReal (redDensity S T x y tau)) hAmeas hAsource]
  apply _root_.MeasureTheory.setLIntegral_congr_fun hAmeas
  intro Z hZ
  dsimp only [Ψ]
  rw [lExpPartial_density S hS T x tau htau (hAinj hZ),
    lExpPartial_apply S hS T x tau htau (hAinj hZ),
    ← ENNReal.ofReal_mul (lExpDensity_pos S hS T x htau (hAinj hZ)).le]
  exact congrArg ENNReal.ofReal (lReducedJacobian_mul_source S hS T x htau (hAinj hZ))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lintegral_lReducedJacobian_mul_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lintegral_lReducedJacobian_mul_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lintegral_lReducedJacobian_mul_source ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lintegral_lReducedJacobian_mul_source

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] in
theorem lintegral_lReducedJacobian_mul_source_le
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (x : M) {tau : ℝ} (htau : 0 < tau)
    (A : Set E) (K : Set M) (hAmeas : MeasurableSet A)
    (hAinj : A ⊆ lInjDomain S T x tau) (c : ℝ)
    (hImage : ∀ Z ∈ A, lExp S T x Z tau ∈ K)
    (hden : ∀ Z ∈ A, redDensity S T x (lExp S T x Z tau) tau ≤ c) :
    (∫⁻ Z in A, ENNReal.ofReal (lReducedJacobian S T x Z tau * lSourceDensity S T x)
      ∂modelHaar (E := E)) ≤
      ENNReal.ofReal c *
        riemannianVolumeMeasure (I := I) (M := M) (S.base.metric (T - tau)) K := by
  rw [lintegral_lReducedJacobian_mul_source S hS T x htau hAmeas hAinj]
  have hmeas : MeasurableSet ((fun Z : E => lExp S T x Z tau) '' A) := by
    let Ψ := lExpPartial S hS T x tau htau
    have hAsource : A ⊆ Ψ.source := by
      rw [lExpPartial_source S hS T x tau htau]
      exact hAinj
    have himage : Ψ '' A = (fun Z : E => lExp S T x Z tau) '' A :=
      Set.image_congr fun Z hZ => lExpPartial_apply S hS T x tau htau (hAinj hZ)
    rw [← himage]
    exact measurableSet_image_param_global Ψ hAmeas hAsource
  calc
    _ ≤ ∫⁻ _y in (fun Z : E => lExp S T x Z tau) '' A, ENNReal.ofReal c
        ∂riemannianVolumeMeasure (I := I) (M := M) (S.base.metric (T - tau)) := by
      apply _root_.MeasureTheory.setLIntegral_mono' hmeas
      rintro y ⟨Z, hZ, rfl⟩
      exact ENNReal.ofReal_le_ofReal (hden Z hZ)
    _ ≤ ∫⁻ _y in K, ENNReal.ofReal c
        ∂riemannianVolumeMeasure (I := I) (M := M) (S.base.metric (T - tau)) :=
      _root_.MeasureTheory.lintegral_mono_set (by rintro y ⟨Z, hZ, rfl⟩; exact hImage Z hZ)
    _ = _ := _root_.MeasureTheory.setLIntegral_const _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lintegral_lReducedJacobian_mul_source_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lintegral_lReducedJacobian_mul_source_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lintegral_lReducedJacobian_mul_source_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lintegral_lReducedJacobian_mul_source_le

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem exists_lMin_slab
    [ConnectedSpace M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x y : M)
    (tau : Real) (htau : 0 < tau)
    (hslab : Set.Icc (T - tau) T ⊆ D.regular) :
    ∃ Z : TangentSpace I x,
      (Z, tau) ∈ lMinDomain S T x ∧ lExp S T x Z tau = y := by
  let g := S.base.metric T
  let : _root_.Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E
      (TangentSpace I : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩
  have hxy : Manifold.riemannianEDist I x y < (⊤ : ENNReal) :=
    lt_of_le_of_ne le_top
      (DifferentialGeometry.Geometry.Riemannian.Exponential.riemannianEDist_ne_top
        (I := I) x y)
  obtain ⟨p, hp, _hlen⟩ :=
    Manifold.exists_path_isContMDiffWithSittingInstants_of_riemannianEDist_lt
      (I := I) hxy
  let b : Real := Real.sqrt tau
  have hb : 0 < b := by
    simpa only [b] using Real.sqrt_pos.2 htau
  let alpha : Real → M := fun s ↦ p.extend (s / b)
  have halpha : ContMDiff (modelWithCornersSelf Real Real) I 1 alpha := by
    apply hp.contMDiff.comp
    rw [contMDiff_iff_contDiff]
    fun_prop
  have ha0 : alpha 0 = x := by
    simp only [alpha, zero_div, Path.extend_zero]
  have hab : alpha b = y := by
    simp only [alpha, div_self hb.ne', Path.extend_one]
  have hback : ∀ s ∈ Set.Icc (0 : Real) b,
      T - s ^ 2 ∈ Set.Icc (T - tau) T := by
    intro s hs
    have hsSq : s ^ 2 ≤ tau := by
      calc
        s ^ 2 ≤ (Real.sqrt tau) ^ 2 :=
          (sq_le_sq₀ hs.1 (Real.sqrt_nonneg tau)).2 (by
            simpa only [b] using hs.2)
        _ = tau := Real.sq_sqrt htau.le
    exact ⟨by linarith, by nlinarith [sq_nonneg s]⟩
  exact exists_lMinimizingVector (I := I) S hS T (T - tau) T tau htau
    (fun r hr ↦ D.regular_subset (hslab hr))
    hback x y alpha halpha ha0 hab (fun s hs ↦ hslab (hback s hs))

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.exists_lMin_slab
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.exists_lMin_slab target :: scope.openDecls } }

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lExp_inj_cover
    [ConnectedSpace M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    (tau : Real) (htau : 0 < tau)
    (hslab : Set.Icc (T - tau) T ⊆ D.regular) :
    ((fun Z : E ↦ lExp S T x Z tau) '' lInjDomain S T x tau)ᶜ ⊆
      lCutImage S T x tau := by
  intro y hy
  obtain ⟨Z, hmin, hend⟩ :=
    exists_lMin_slab S hS T x y tau htau hslab
  have hnot : (Z : E) ∉ lInjDomain S T x tau := by
    intro hZ
    exact hy ⟨(Z : E), hZ, hend⟩
  exact ⟨(Z : E),
    (mem_lCutDomain S T x tau (Z : E)).2 ⟨hmin, hnot⟩, hend⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lExp_inj_cover then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lExp_inj_cover"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lExp_inj_cover ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lExp_inj_cover

theorem lExp_inj_ae
    [ConnectedSpace M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    (tau : Real) (htau : 0 < tau)
    (hslab : Set.Icc (T - tau) T ⊆ D.regular) :
    (fun Z : E ↦ lExp S T x Z tau) '' lInjDomain S T x tau ∈
      ae (riemannianVolumeMeasure (I := I) (M := M)
        (S.base.metric (T - tau))) := by
  apply mem_ae_iff.mpr
  exact _root_.MeasureTheory.measure_mono_null (lExp_inj_cover S hS T x tau htau hslab)
    (lCut_null S hS T x tau (S.base.metric (T - tau)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lExp_inj_ae then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lExp_inj_ae"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lExp_inj_ae ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lExp_inj_ae

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem redVolume_lint
    [ConnectedSpace M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    (tau : Real) (htau : 0 < tau)
    (hslab : Set.Icc (T - tau) T ⊆ D.regular) :
    redVolume S T x tau =
      ∫⁻ Z in lInjDomain S T x tau,
        ENNReal.ofReal (lReducedJacobian S T x Z tau * lSourceDensity S T x)
        ∂modelHaar (E := E) := by
  let U : Set E := lInjDomain S T x tau
  have hUmeas : MeasurableSet U := (lInj_isOpen S hS T x tau).measurableSet
  calc
    redVolume S T x tau =
        ∫⁻ y in (fun Z : E ↦ lExp S T x Z tau) '' U,
          ENNReal.ofReal (redDensity S T x y tau)
          ∂riemannianVolumeMeasure (I := I) (M := M)
            (S.base.metric (T - tau)) := by
      unfold redVolume
      exact congrArg
        (fun μ : _root_.MeasureTheory.Measure M ↦
          ∫⁻ y, ENNReal.ofReal (redDensity S T x y tau) ∂μ)
        (Measure.restrict_eq_self_of_ae_mem
          (lExp_inj_ae S hS T x tau htau hslab)).symm
    _ = ∫⁻ Z in lInjDomain S T x tau,
        ENNReal.ofReal (lReducedJacobian S T x Z tau * lSourceDensity S T x)
        ∂modelHaar (E := E) :=
      (lintegral_lReducedJacobian_mul_source S hS T x htau hUmeas Subset.rfl).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.redVolume_lint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.redVolume_lint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.redVolume_lint ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.redVolume_lint

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem redVolume_anti
    [ConnectedSpace M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    {tau₁ tau₂ : Real} (htau₁ : 0 < tau₁) (h12 : tau₁ ≤ tau₂)
    (hslab : Set.Icc (T - tau₂) T ⊆ D.regular) :
    redVolume S T x tau₂ ≤ redVolume S T x tau₁ := by
  have htau₂ : 0 < tau₂ := htau₁.trans_le h12
  have hslab₁ : Set.Icc (T - tau₁) T ⊆ D.regular := by
    intro r hr
    exact hslab ⟨(sub_le_sub_left h12 T).trans hr.1, hr.2⟩
  have hdomain :
      lInjDomain S T x tau₂ ⊆ lInjDomain S T x tau₁ := by
    rintro Z ⟨sigma, hsigma, hmin⟩
    exact ⟨sigma, lt_of_le_of_lt h12 hsigma, hmin⟩
  rw [redVolume_lint S hS T x tau₂ htau₂ hslab,
    redVolume_lint S hS T x tau₁ htau₁ hslab₁]
  calc
    (∫⁻ Z in lInjDomain S T x tau₂,
        ENNReal.ofReal (lReducedJacobian S T x Z tau₂ * lSourceDensity S T x)
        ∂modelHaar (E := E)) ≤
        ∫⁻ Z in lInjDomain S T x tau₂,
          ENNReal.ofReal (lReducedJacobian S T x Z tau₁ * lSourceDensity S T x)
          ∂modelHaar (E := E) := by
      refine MeasureTheory.setLIntegral_mono'
        (lInj_isOpen S hS T x tau₂).measurableSet ?_
      intro Z hZ
      exact ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right
          (lReducedJacobian_anti S hS T x htau₁ h12 hZ)
          (lSourceDensity_pos S T x).le)
    _ ≤ ∫⁻ Z in lInjDomain S T x tau₁,
        ENNReal.ofReal (lReducedJacobian S T x Z tau₁ * lSourceDensity S T x)
        ∂modelHaar (E := E) :=
      MeasureTheory.lintegral_mono_set hdomain

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.redVolume_anti then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.redVolume_anti"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.redVolume_anti ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.redVolume_anti

end DifferentialGeometry.PDE.RicciFlow.Perelman
