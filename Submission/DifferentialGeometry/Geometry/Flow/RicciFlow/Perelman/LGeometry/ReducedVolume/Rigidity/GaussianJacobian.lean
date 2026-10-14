import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.SmallVolumeComplete
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.OpenPos

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Set _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.ContDiff _root_.ENNReal _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.Submission.Topology

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  [ConnectedSpace M] {D : RealTimeInterval}

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

theorem ae_lReducedJacobian_indicator_eq_gaussian_of_redVolume_eq_one
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (hg : RiemannianMetricComplete (S.base.metric T)) (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → _root_.Set.Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ _root_.Set.Icc (T - sigma) T, ∀ z : M,
        normSq0S (S.base.metric t) z 4 (S.base.rm04 t z) ≤ K)
    {tau : ℝ} (htau : 0 < tau) (hslab : _root_.Set.Icc (T - tau) T ⊆ D.regular)
    (hvol : redVolume S T x tau = 1) :
    (lInjDomain S T x tau).indicator
        (fun Z : E => ENNReal.ofReal
          (lReducedJacobian S T x Z tau * lSourceDensity S T x)) =ᵐ[modelHaar]
      fun Z : E => ENNReal.ofReal (lSourceGaussian S T x Z) := by
  let J : E → ℝ≥0∞ := (lInjDomain S T x tau).indicator
    (fun Z => ENNReal.ofReal
      (lReducedJacobian S T x Z tau * lSourceDensity S T x))
  let G : E → ℝ≥0∞ := fun Z => ENNReal.ofReal (lSourceGaussian S T x Z)
  have hU := (lInj_isOpen_of_rm S hS T hg x hRm tau).measurableSet
  have hmass : (∫⁻ Z, J Z ∂modelHaar) = 1 := by
    rw [show (∫⁻ Z, J Z ∂modelHaar) =
      ∫⁻ Z in lInjDomain S T x tau, ENNReal.ofReal
        (lReducedJacobian S T x Z tau * lSourceDensity S T x) ∂modelHaar from
      _root_.MeasureTheory.lintegral_indicator hU _]
    exact (redVolume_lint_of_rm S hS T hg x hRm tau htau hslab).symm.trans hvol
  have hJG : J ≤ᵐ[modelHaar] G := by
    apply _root_.MeasureTheory.ae_of_all
    intro Z
    by_cases hZ : Z ∈ lInjDomain S T x tau
    · simpa only [J, G, Set.indicator_of_mem hZ] using
        lRedJac_src_le_of_rm S hS T x hRm tau htau hZ
    · simp only [J, Set.indicator_of_notMem hZ, zero_le]
  have hG : Measurable G := by
    dsimp only [G]
    unfold lSourceGaussian
    fun_prop
  exact _root_.MeasureTheory.ae_eq_of_ae_le_of_lintegral_le hJG (by rw [hmass]; exact ENNReal.one_ne_top)
    hG.aemeasurable (by rw [hmass]; exact (lSourceGaussian_mass S T x).le)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.ae_lReducedJacobian_indicator_eq_gaussian_of_redVolume_eq_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.ae_lReducedJacobian_indicator_eq_gaussian_of_redVolume_eq_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.ae_lReducedJacobian_indicator_eq_gaussian_of_redVolume_eq_one ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.ae_lReducedJacobian_indicator_eq_gaussian_of_redVolume_eq_one

theorem ae_mem_lInjDomain_of_redVolume_eq_one
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (hg : RiemannianMetricComplete (S.base.metric T)) (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → _root_.Set.Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ _root_.Set.Icc (T - sigma) T, ∀ z : M,
        normSq0S (S.base.metric t) z 4 (S.base.rm04 t z) ≤ K)
    {tau : ℝ} (htau : 0 < tau) (hslab : _root_.Set.Icc (T - tau) T ⊆ D.regular)
    (hvol : redVolume S T x tau = 1) :
    ∀ᵐ Z : E ∂modelHaar, Z ∈ lInjDomain S T x tau := by
  filter_upwards [ae_lReducedJacobian_indicator_eq_gaussian_of_redVolume_eq_one
    S hS T hg x hRm htau hslab hvol] with Z hZ
  by_contra hnot
  have hpos : 0 < lSourceGaussian S T x Z := by
    rw [lSourceGaussian_eq_metric_norm]
    exact mul_pos (mul_pos (inv_pos.mpr (Real.rpow_pos_of_pos Real.pi_pos _))
      (lSourceDensity_pos S T x)) (Real.exp_pos _)
  rw [Set.indicator_of_notMem hnot] at hZ
  exact (ENNReal.ofReal_pos.mpr hpos).ne' hZ.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.ae_mem_lInjDomain_of_redVolume_eq_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.ae_mem_lInjDomain_of_redVolume_eq_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.ae_mem_lInjDomain_of_redVolume_eq_one ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.ae_mem_lInjDomain_of_redVolume_eq_one

theorem lReducedJacobian_mul_source_eq_gaussian_of_redVolume_eq_one
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (hg : RiemannianMetricComplete (S.base.metric T)) (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → _root_.Set.Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ _root_.Set.Icc (T - sigma) T, ∀ z : M,
        normSq0S (S.base.metric t) z 4 (S.base.rm04 t z) ≤ K)
    {tau : ℝ} (htau : 0 < tau) (hslab : _root_.Set.Icc (T - tau) T ⊆ D.regular)
    (hvol : redVolume S T x tau = 1) {Z : E}
    (hZ : Z ∈ lInjDomain S T x tau) :
    lReducedJacobian S T x Z tau * lSourceDensity S T x =
      lSourceGaussian S T x Z := by
  have hU := lInj_isOpen_of_rm S hS T hg x hRm tau
  have hae : (fun W : E => lReducedJacobian S T x W tau * lSourceDensity S T x)
      =ᵐ[(modelHaar (E := E)).restrict (lInjDomain S T x tau)]
      lSourceGaussian S T x := by
    filter_upwards [_root_.MeasureTheory.ae_restrict_of_ae
      (ae_lReducedJacobian_indicator_eq_gaussian_of_redVolume_eq_one
        S hS T hg x hRm htau hslab hvol), _root_.MeasureTheory.ae_restrict_mem hU.measurableSet]
      with W hW hWU
    rw [Set.indicator_of_mem hWU] at hW
    have hnonneg : 0 ≤ lReducedJacobian S T x W tau * lSourceDensity S T x :=
      mul_nonneg (Real.exp_pos _).le (lSourceDensity_pos S T x).le
    have hgauss : 0 ≤ lSourceGaussian S T x W := by
      rw [lSourceGaussian_eq_metric_norm]
      exact mul_nonneg (mul_nonneg (inv_nonneg.mpr (Real.rpow_pos_of_pos Real.pi_pos _).le)
        (lSourceDensity_pos S T x).le) (Real.exp_pos _).le
    exact (ENNReal.ofReal_eq_ofReal_iff hnonneg hgauss).mp hW
  have hcont : Continuous (lSourceGaussian S T x) := by
    unfold lSourceGaussian
    fun_prop
  exact MeasureTheory.Measure.eqOn_open_of_ae_eq hae hU
    (lRedJac_mul_src_contOn_of_rm S hS T hg x hRm tau htau)
    hcont.continuousOn hZ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lReducedJacobian_mul_source_eq_gaussian_of_redVolume_eq_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lReducedJacobian_mul_source_eq_gaussian_of_redVolume_eq_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lReducedJacobian_mul_source_eq_gaussian_of_redVolume_eq_one ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lReducedJacobian_mul_source_eq_gaussian_of_redVolume_eq_one

theorem hasDerivAt_lReducedJacobian_zero_of_redVolume_eq_one
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (hg : RiemannianMetricComplete (S.base.metric T)) (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → _root_.Set.Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ _root_.Set.Icc (T - sigma) T, ∀ z : M,
        normSq0S (S.base.metric t) z 4 (S.base.rm04 t z) ≤ K)
    {tau s : ℝ} (hs : 0 < s) (hstau : s < tau)
    (hslab : _root_.Set.Icc (T - tau) T ⊆ D.regular)
    (hvol : redVolume S T x tau = 1) {Z : E}
    (hZ : Z ∈ lInjDomain S T x tau) :
    HasDerivAt (lReducedJacobian S T x Z) 0 s := by
  have hlocal : lReducedJacobian S T x Z =ᶠ[𝓝 s]
      fun _ => lSourceGaussian S T x Z / lSourceDensity S T x := by
    filter_upwards [isOpen_Ioo.mem_nhds (show s ∈ _root_.Set.Ioo (0 : ℝ) tau from ⟨hs, hstau⟩)]
      with r hr
    have hslabr : _root_.Set.Icc (T - r) T ⊆ D.regular :=
      (_root_.Set.Icc_subset_Icc (sub_le_sub_left hr.2.le T) le_rfl).trans hslab
    have hvolr : redVolume S T x r = 1 := by
      apply le_antisymm
      · exact DifferentialGeometry.PDE.RicciFlow.redVolume_le_one_of_rm
          S hS T hg x hRm r hr.1 hslabr
      · have hmono := DifferentialGeometry.PDE.RicciFlow.redVolume_anti_of_rm
          S hS T hg x hRm hr.1 hr.2.le hslab
        change redVolume S T x tau ≤ redVolume S T x r at hmono
        rwa [hvol] at hmono
    have hZr : Z ∈ lInjDomain S T x r := by
      obtain ⟨sigma, hsigma, hmin⟩ := hZ
      exact ⟨sigma, hr.2.trans hsigma, hmin⟩
    exact (eq_div_iff (lSourceDensity_pos S T x).ne').mpr
      (lReducedJacobian_mul_source_eq_gaussian_of_redVolume_eq_one
        S hS T hg x hRm hr.1 hslabr hvolr hZr)
  exact (hasDerivAt_const s (lSourceGaussian S T x Z / lSourceDensity S T x)).congr_of_eventuallyEq
    hlocal

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.hasDerivAt_lReducedJacobian_zero_of_redVolume_eq_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.hasDerivAt_lReducedJacobian_zero_of_redVolume_eq_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.hasDerivAt_lReducedJacobian_zero_of_redVolume_eq_one ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.hasDerivAt_lReducedJacobian_zero_of_redVolume_eq_one

end DifferentialGeometry.PDE.RicciFlow.Perelman
