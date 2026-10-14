import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.InjGeometryComplete
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.ReducedVolumeComplete
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.RedJacobian

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped _root_.ContDiff _root_.ENNReal _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.Submission.Topology _root_.Submission.DifferentialGeometry.Topology

namespace DifferentialGeometry.PDE.RicciFlow

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  [ConnectedSpace M]
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

theorem redVolume_lint_of_rm
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : ℝ)
    (hg : RiemannianMetricComplete (I := I) (S.base.metric T))
    (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → _root_.Set.Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ _root_.Set.Icc (T - sigma) T, ∀ z : M,
        normSq0S (I := I) (S.base.metric t) z 4
          (S.base.rm04 t z) ≤ K)
    (tau : ℝ) (htau : 0 < tau)
    (hslab : _root_.Set.Icc (T - tau) T ⊆ D.regular) :
    DifferentialGeometry.PDE.RicciFlow.redVolume S T x tau =
      ∫⁻ Z in lInjDomain S T x tau,
        ENNReal.ofReal (lReducedJacobian S T x Z tau * lSourceDensity S T x)
        ∂modelHaar (E := E) := by
  obtain ⟨Φ, hsource, _himage, hmap, _hcut, hnull⟩ :=
    exists_lExpPartial_full_of_rm S hS T hg x hRm tau htau hslab
  exact redVolume_lint_of_param S hS T x hRm tau htau
    Φ hsource hmap hnull

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.redVolume_lint_of_rm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.redVolume_lint_of_rm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.redVolume_lint_of_rm ``Submission.DifferentialGeometry.PDE.RicciFlow.redVolume_lint_of_rm

theorem redVolume_anti_of_rm
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : ℝ)
    (hg : RiemannianMetricComplete (I := I) (S.base.metric T))
    (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → _root_.Set.Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ _root_.Set.Icc (T - sigma) T, ∀ z : M,
        normSq0S (I := I) (S.base.metric t) z 4
          (S.base.rm04 t z) ≤ K)
    {tau₁ tau₂ : ℝ} (htau₁ : 0 < tau₁) (h12 : tau₁ ≤ tau₂)
    (hslab : _root_.Set.Icc (T - tau₂) T ⊆ D.regular) :
    DifferentialGeometry.PDE.RicciFlow.redVolume S T x tau₂ ≤
      DifferentialGeometry.PDE.RicciFlow.redVolume S T x tau₁ := by
  have htau₂ : 0 < tau₂ := htau₁.trans_le h12
  have hslab₁ : _root_.Set.Icc (T - tau₁) T ⊆ D.regular := by
    intro t ht
    exact hslab ⟨(sub_le_sub_left h12 T).trans ht.1, ht.2⟩
  have hdomain : lInjDomain S T x tau₂ ⊆ lInjDomain S T x tau₁ := by
    rintro Z ⟨sigma, hsigma, hmin⟩
    exact ⟨sigma, lt_of_le_of_lt h12 hsigma, hmin⟩
  have hpoint : ∀ Z ∈ lInjDomain S T x tau₂,
      lReducedJacobian S T x Z tau₂ ≤ lReducedJacobian S T x Z tau₁ := by
    rintro Z ⟨sigma, hsigma, hmin⟩
    have hsigmapos : 0 < sigma := htau₂.trans hsigma
    have hdom : (Z, sigma) ∈ lExpPosDom S T x :=
      ((mem_lMinDomain S T x Z sigma).mp hmin).1
    have hregSigma : _root_.Set.Icc (T - sigma) T ⊆ D.regular := by
      intro t ht
      have hnonneg : 0 ≤ T - t := sub_nonneg.mpr ht.2
      have hback : T - t ≤ sigma := by linarith only [ht.1]
      have hsqrt : Real.sqrt (T - t) ∈ _root_.Set.Icc (0 : ℝ) (Real.sqrt sigma) :=
        ⟨Real.sqrt_nonneg _, Real.sqrt_le_sqrt hback⟩
      have hclock := lExpPosDom_regularity S T x Z hdom hsqrt
      have heq : T - (Real.sqrt (T - t)) ^ 2 = t := by
        rw [Real.sq_sqrt hnonneg]
        ring
      simpa only [heq] using hclock
    obtain ⟨K, hK⟩ := hRm sigma hsigmapos hregSigma
    exact (lRedJac_antitoneOn_of_rm S hS K T x hmin hK)
      ⟨htau₁, lt_of_le_of_lt h12 hsigma⟩ ⟨htau₂, hsigma⟩ h12
  rw [redVolume_lint_of_rm S hS T hg x hRm tau₂ htau₂ hslab,
    redVolume_lint_of_rm S hS T hg x hRm tau₁ htau₁ hslab₁]
  calc
    (∫⁻ Z in lInjDomain S T x tau₂,
        ENNReal.ofReal (lReducedJacobian S T x Z tau₂ * lSourceDensity S T x)
        ∂modelHaar (E := E)) ≤
        ∫⁻ Z in lInjDomain S T x tau₂,
          ENNReal.ofReal (lReducedJacobian S T x Z tau₁ * lSourceDensity S T x)
          ∂modelHaar (E := E) := by
      refine MeasureTheory.setLIntegral_mono'
        (lInj_isOpen_of_rm S hS T hg x hRm tau₂).measurableSet ?_
      intro Z hZ
      exact ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (hpoint Z hZ)
          (lSourceDensity_pos S T x).le)
    _ ≤ ∫⁻ Z in lInjDomain S T x tau₁,
        ENNReal.ofReal (lReducedJacobian S T x Z tau₁ * lSourceDensity S T x)
        ∂modelHaar (E := E) :=
      MeasureTheory.lintegral_mono_set hdomain

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.redVolume_anti_of_rm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.redVolume_anti_of_rm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.redVolume_anti_of_rm ``Submission.DifferentialGeometry.PDE.RicciFlow.redVolume_anti_of_rm

namespace Perelman

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space (TangentBundle I M)]
  [ConnectedSpace M] in
theorem redVolume_congr_base {D D' : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (S' : SolutionOn (I := I) (M := M) D')
    (h : S'.base = S.base) (T : ℝ) (x : M) (tau : ℝ) :
    redVolume S' T x tau = redVolume S T x tau := by
  simp only [redVolume, redDensity, redLength, lCost, lLength, lDensity, lSpeedSq,
    SolutionOn.scalar, SolutionFamily.scalar]
  rw [h]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.redVolume_congr_base then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.redVolume_congr_base"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.redVolume_congr_base ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.redVolume_congr_base

omit [T2Space (TangentBundle I M)] in
theorem redVolume_anti_Ico_of_base_eq
    [CompactSpace M]
    {D D' : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (S' : SolutionOn (I := I) (M := M) D')
    (hbase : S'.base = S.base) (hS' : IsSolutionOn (I := I) S')
    (T : ℝ) (x : M) {tau₁ tau₂ : ℝ}
    (htau₁ : 0 < tau₁) (h12 : tau₁ ≤ tau₂)
    (hslab : Set.Icc (T - tau₂) T ⊆ D'.regular) :
    redVolume (I := I) (M := M) S T x tau₂ ≤ redVolume (I := I) (M := M) S T x tau₁ := by
  have h := redVolume_anti (I := I) (M := M) (D := D') S' hS' T x htau₁ h12 hslab
  rw [redVolume_congr_base (I := I) (M := M) (D := D) (D' := D') S S' hbase T x tau₂,
    redVolume_congr_base (I := I) (M := M) (D := D) (D' := D') S S' hbase T x tau₁] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.redVolume_anti_Ico_of_base_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.redVolume_anti_Ico_of_base_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.redVolume_anti_Ico_of_base_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.redVolume_anti_Ico_of_base_eq

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space (TangentBundle I M)]
  [ConnectedSpace M] in
set_option backward.isDefEq.respectTransparency false in
theorem redVolume_standard_eq {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (x : M) (tau : ℝ) :
    DifferentialGeometry.PDE.RicciFlow.redVolume S T x tau = redVolume S T x tau := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.redVolume_standard_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.redVolume_standard_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.redVolume_standard_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.redVolume_standard_eq

theorem redVolume_anti_of_rm_Ico_of_base_eq
    {D D' : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (S' : SolutionOn (I := I) (M := M) D')
    (hbase : S'.base = S.base) (hS' : IsSolutionOn (I := I) S')
    (T : ℝ) (x : M)
    (hg : RiemannianMetricComplete (I := I) (S.base.metric T))
    (hRm : ∀ sigma : ℝ, 0 < sigma → Set.Icc (T - sigma) T ⊆ D'.regular →
      ∃ K : ℝ, ∀ t ∈ Set.Icc (T - sigma) T, ∀ z : M,
        normSq0S (I := I) (S.base.metric t) z 4 (S.base.rm04 t z) ≤ K)
    {tau₁ tau₂ : ℝ} (htau₁ : 0 < tau₁) (h12 : tau₁ ≤ tau₂)
    (hslab : Set.Icc (T - tau₂) T ⊆ D'.regular) :
    redVolume (I := I) (M := M) S T x tau₂ ≤ redVolume (I := I) (M := M) S T x tau₁ := by
  have hg' : RiemannianMetricComplete (I := I) (S'.base.metric T) := by
    rw [hbase]; exact hg
  have hRm' : ∀ sigma : ℝ, 0 < sigma → Set.Icc (T - sigma) T ⊆ D'.regular →
      ∃ K : ℝ, ∀ t ∈ Set.Icc (T - sigma) T, ∀ z : M,
        normSq0S (I := I) (S'.base.metric t) z 4 (S'.base.rm04 t z) ≤ K := by
    intro sigma hsigma hsub
    obtain ⟨K, hK⟩ := hRm sigma hsigma hsub
    exact ⟨K, fun t ht z => by rw [hbase]; exact hK t ht z⟩
  have h := DifferentialGeometry.PDE.RicciFlow.redVolume_anti_of_rm (I := I) (M := M)
    (D := D') S' hS' T hg' x hRm' htau₁ h12 hslab
  rw [redVolume_standard_eq (I := I) (M := M) (D := D') S' T x tau₂,
    redVolume_standard_eq (I := I) (M := M) (D := D') S' T x tau₁] at h
  rw [redVolume_congr_base (I := I) (M := M) (D := D) (D' := D') S S' hbase T x tau₂,
    redVolume_congr_base (I := I) (M := M) (D := D) (D' := D') S S' hbase T x tau₁] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.redVolume_anti_of_rm_Ico_of_base_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.redVolume_anti_of_rm_Ico_of_base_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.redVolume_anti_of_rm_Ico_of_base_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.redVolume_anti_of_rm_Ico_of_base_eq

end Perelman

end DifferentialGeometry.PDE.RicciFlow

end
