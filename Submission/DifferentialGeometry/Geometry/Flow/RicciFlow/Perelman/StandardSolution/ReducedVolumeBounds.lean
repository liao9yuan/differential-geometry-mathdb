import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Jacobian.SourceGaussian
import Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatKernel.PositiveDefinite.GaussianTail
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.SmallReducedComplete
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.ReducedVolumeMonotonicity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CutTime

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Set _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean
open scoped _root_.ContDiff _root_.ENNReal _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.Submission.Topology _root_.Submission.DifferentialGeometry.Topology

namespace DifferentialGeometry.PDE.RicciFlow

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

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

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] in
theorem lSourceGaussian_tail_eq_spd
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (x : M) (R : ℝ) :
    (∫⁻ Z : E in {Z | R < Real.sqrt ((S.base.metric T).inner x Z Z)},
      ENNReal.ofReal (lSourceGaussian S T x Z) ∂modelHaar (E := E)) =
      ∫⁻ y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) in
        {y | R < Real.sqrt (_root_.Inner.inner ℝ y
          (Matrix.toEuclideanCLM (n := Fin (Module.finrank ℝ E))
            (𝕜 := ℝ) (lSourceGram S T x) y))},
        ENNReal.ofReal
          (((Real.pi : ℝ) ^ ((Module.finrank ℝ E : ℝ) / 2))⁻¹ *
            Real.sqrt (lSourceGram S T x).det *
            Real.exp (-_root_.Inner.inner ℝ y
              (Matrix.toEuclideanCLM (n := Fin (Module.finrank ℝ E))
                (𝕜 := ℝ) (lSourceGram S T x) y))) ∂volume := by
  classical
  let A := lSourceGram S T x
  let e := toEuclidean (E := E)
  let sE : Set E := {Z | R < Real.sqrt ((S.base.metric T).inner x Z Z)}
  let sU : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
    {y | R < Real.sqrt (_root_.Inner.inner ℝ y
      (Matrix.toEuclideanCLM (n := Fin (Module.finrank ℝ E)) (𝕜 := ℝ) A y))}
  let G : E → ℝ≥0∞ := sE.indicator (fun Z ↦ ENNReal.ofReal (lSourceGaussian S T x Z))
  have hsE : MeasurableSet sE := by
    dsimp only [sE]
    apply measurableSet_lt measurable_const
    fun_prop
  have hsU : MeasurableSet sU := by
    dsimp only [sU]
    apply measurableSet_lt measurable_const
    fun_prop
  have hmem : ∀ y, e.symm y ∈ sE ↔ y ∈ sU := by
    intro y
    simp only [sE, sU, Set.mem_ofPred_eq]
    have hquad := lSourceGram_quadraticForm S T x (e.symm y)
    simp only [e, ContinuousLinearEquiv.apply_symm_apply] at hquad
    rw [← hquad]
  have hpoint : ∀ y,
      G (e.symm y) =
        sU.indicator
          (fun z ↦ ENNReal.ofReal
            (((Real.pi : ℝ) ^ ((Module.finrank ℝ E : ℝ) / 2))⁻¹ *
              Real.sqrt A.det * Real.exp (-_root_.Inner.inner ℝ z
                (Matrix.toEuclideanCLM (n := Fin (Module.finrank ℝ E))
                  (𝕜 := ℝ) A z)))) y := by
    intro y
    by_cases hy : y ∈ sU
    · have hEy : e.symm y ∈ sE := (hmem y).mpr hy
      simp only [G, Set.indicator_of_mem hEy, Set.indicator_of_mem hy]
      rw [lSourceGaussian_eq_metric_norm]
      have hquad := lSourceGram_quadraticForm S T x (e.symm y)
      simp only [e, ContinuousLinearEquiv.apply_symm_apply] at hquad
      rw [← hquad]
      rfl
    · have hEy : e.symm y ∉ sE := fun h ↦ hy ((hmem y).mp h)
      simp only [G, Set.indicator_of_notMem hEy,
        Set.indicator_of_notMem hy]
  calc
    (∫⁻ Z : E in sE, ENNReal.ofReal (lSourceGaussian S T x Z)
        ∂modelHaar (E := E)) =
        ∫⁻ Z : E, G Z ∂modelHaar (E := E) := by
      rw [← _root_.MeasureTheory.lintegral_indicator hsE]
    _ = ∫⁻ y, G ((toEuclidean (E := E)).symm y)
        ∂Measure.map (toEuclidean (E := E)) (modelHaar (E := E)) := by
      symm
      calc
        (∫⁻ y, G ((toEuclidean (E := E)).symm y)
            ∂Measure.map (toEuclidean (E := E)) (modelHaar (E := E))) =
            ∫⁻ Z, G ((toEuclidean (E := E)).symm (toEuclidean Z))
              ∂modelHaar (E := E) :=
          (toEuclidean (E := E)).toHomeomorph.measurableEmbedding.lintegral_map _
        _ = ∫⁻ Z, G Z ∂modelHaar (E := E) := by
          refine _root_.MeasureTheory.lintegral_congr fun Z ↦ ?_
          rw [ContinuousLinearEquiv.symm_apply_apply]
    _ = ∫⁻ y, G ((toEuclidean (E := E)).symm y)
        ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) := by
      rw [map_toEuclidean_modelHaar_eq_volume (E := E)]
    _ = ∫⁻ y in sU, ENNReal.ofReal
        (((Real.pi : ℝ) ^ ((Module.finrank ℝ E : ℝ) / 2))⁻¹ *
          Real.sqrt A.det * Real.exp (-_root_.Inner.inner ℝ y
            (Matrix.toEuclideanCLM (n := Fin (Module.finrank ℝ E))
              (𝕜 := ℝ) A y))) ∂volume := by
      rw [← _root_.MeasureTheory.lintegral_indicator hsU]
      exact _root_.MeasureTheory.lintegral_congr fun y ↦ by
        simpa only [e] using hpoint y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.lSourceGaussian_tail_eq_spd then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.lSourceGaussian_tail_eq_spd"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.lSourceGaussian_tail_eq_spd ``Submission.DifferentialGeometry.PDE.RicciFlow.lSourceGaussian_tail_eq_spd

theorem lRedJac_src_le_of_rm
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : ℝ) (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → _root_.Set.Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ _root_.Set.Icc (T - sigma) T, ∀ y : M,
        normSq0S (I := I) (S.base.metric t) y 4 (S.base.rm04 t y) ≤ K)
    (tau : ℝ) (htau : 0 < tau) {Z : E}
    (hZ : Z ∈ lInjDomain S T x tau) :
    ENNReal.ofReal (lReducedJacobian S T x Z tau * lSourceDensity S T x) ≤
      ENNReal.ofReal (lSourceGaussian S T x Z) := by
  obtain ⟨sigma, hsigma, hmin⟩ := hZ
  have hsigmapos : 0 < sigma := htau.trans hsigma
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
  apply ENNReal.ofReal_le_ofReal
  rw [lSourceGaussian_eq_metric_norm]
  calc
    lReducedJacobian S T x Z tau * lSourceDensity S T x ≤
        (((Real.pi : ℝ) ^ ((Module.finrank ℝ E : ℝ) / 2))⁻¹ *
          Real.exp (-(S.base.metric T).inner x Z Z)) * lSourceDensity S T x :=
      mul_le_mul_of_nonneg_right
        (lRedJac_le_gauss_of_rm S hS K T x hmin htau hsigma hK)
        (lSourceDensity_pos S T x).le
    _ = ((Real.pi : ℝ) ^ ((Module.finrank ℝ E : ℝ) / 2))⁻¹ *
        lSourceDensity S T x * Real.exp (-(S.base.metric T).inner x Z Z) := by
      ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.lRedJac_src_le_of_rm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.lRedJac_src_le_of_rm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.lRedJac_src_le_of_rm ``Submission.DifferentialGeometry.PDE.RicciFlow.lRedJac_src_le_of_rm

theorem lRedJac_tail_le_of_rm
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : ℝ) (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → _root_.Set.Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ _root_.Set.Icc (T - sigma) T, ∀ y : M,
        normSq0S (I := I) (S.base.metric t) y 4 (S.base.rm04 t y) ≤ K)
    (tau R : ℝ) (htau : 0 < tau) :
    (∫⁻ Z : E in lInjDomain S T x tau ∩
        {Z | R < Real.sqrt ((S.base.metric T).inner x Z Z)},
      ENNReal.ofReal (lReducedJacobian S T x Z tau * lSourceDensity S T x)
        ∂modelHaar (E := E)) ≤
      ∫⁻ Z : E in {Z | R < Real.sqrt ((S.base.metric T).inner x Z Z)},
        ENNReal.ofReal (lSourceGaussian S T x Z) ∂modelHaar (E := E) := by
  have hgauss : Measurable (fun Z : E ↦ ENNReal.ofReal (lSourceGaussian S T x Z)) := by
    unfold lSourceGaussian
    fun_prop
  calc
    (∫⁻ Z : E in lInjDomain S T x tau ∩
        {Z | R < Real.sqrt ((S.base.metric T).inner x Z Z)},
      ENNReal.ofReal (lReducedJacobian S T x Z tau * lSourceDensity S T x)
        ∂modelHaar (E := E)) ≤
        ∫⁻ Z : E in lInjDomain S T x tau ∩
          {Z | R < Real.sqrt ((S.base.metric T).inner x Z Z)},
          ENNReal.ofReal (lSourceGaussian S T x Z) ∂modelHaar (E := E) :=
      _root_.MeasureTheory.setLIntegral_mono hgauss fun Z hZ ↦
        lRedJac_src_le_of_rm S hS T x hRm tau htau hZ.1
    _ ≤ ∫⁻ Z : E in {Z | R < Real.sqrt ((S.base.metric T).inner x Z Z)},
        ENNReal.ofReal (lSourceGaussian S T x Z) ∂modelHaar (E := E) :=
      _root_.MeasureTheory.lintegral_mono_set _root_.Set.inter_subset_right

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.lRedJac_tail_le_of_rm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.lRedJac_tail_le_of_rm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.lRedJac_tail_le_of_rm ``Submission.DifferentialGeometry.PDE.RicciFlow.lRedJac_tail_le_of_rm

theorem lRedJac_tail_unif_of_rm (eps : ℝ≥0∞) (heps : 0 < eps) :
    ∃ R : ℝ, 0 ≤ R ∧
      ∀ (D : RealTimeInterval) (S : SolutionOn (I := I) (M := M) D),
        IsSolutionOn (I := I) S → ∀ (T : ℝ) (x : M),
        (∀ sigma : ℝ, 0 < sigma → _root_.Set.Icc (T - sigma) T ⊆ D.regular →
          ∃ K : ℝ, ∀ t ∈ _root_.Set.Icc (T - sigma) T, ∀ y : M,
            normSq0S (I := I) (S.base.metric t) y 4 (S.base.rm04 t y) ≤ K) →
        ∀ tau : ℝ, 0 < tau →
        (∫⁻ Z : E in lInjDomain S T x tau ∩
            {Z | R < Real.sqrt ((S.base.metric T).inner x Z Z)},
          ENNReal.ofReal (lReducedJacobian S T x Z tau * lSourceDensity S T x)
            ∂modelHaar (E := E)) ≤ eps := by
  let : Nonempty (Fin (Module.finrank ℝ E)) :=
    ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))⟩⟩
  obtain ⟨R, hR, htail⟩ :=
    gaussianPosDef_uniform_tail (n := Fin (Module.finrank ℝ E)) eps heps
  refine ⟨R, hR, ?_⟩
  intro D S hS T x hRm tau htau
  refine (lRedJac_tail_le_of_rm S hS T x hRm tau R htau).trans ?_
  rw [lSourceGaussian_tail_eq_spd S T x R]
  simpa only [Fintype.card_fin] using htail (lSourceGram S T x) (lSourceGram_posDef S T x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.lRedJac_tail_unif_of_rm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.lRedJac_tail_unif_of_rm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.lRedJac_tail_unif_of_rm ``Submission.DifferentialGeometry.PDE.RicciFlow.lRedJac_tail_unif_of_rm

variable [T2Space (TangentBundle I M)] [SigmaCompactSpace M] [ConnectedSpace M]

theorem redVolume_le_one_of_rm
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : ℝ) (hg : RiemannianMetricComplete (I := I) (S.base.metric T)) (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → _root_.Set.Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ _root_.Set.Icc (T - sigma) T, ∀ y : M,
        normSq0S (I := I) (S.base.metric t) y 4 (S.base.rm04 t y) ≤ K)
    (tau : ℝ) (htau : 0 < tau) (hslab : _root_.Set.Icc (T - tau) T ⊆ D.regular) :
    DifferentialGeometry.PDE.RicciFlow.redVolume S T x tau ≤ 1 := by
  rw [redVolume_lint_of_rm S hS T hg x hRm tau htau hslab]
  calc
    (∫⁻ Z in lInjDomain S T x tau,
        ENNReal.ofReal (lReducedJacobian S T x Z tau * lSourceDensity S T x)
        ∂modelHaar (E := E)) ≤
        ∫⁻ Z in lInjDomain S T x tau,
          ENNReal.ofReal (lSourceGaussian S T x Z) ∂modelHaar (E := E) := by
      refine _root_.MeasureTheory.setLIntegral_mono'
        (measurableSet_lInjDomain_of_rm S hS T x hRm tau) ?_
      intro Z hZ
      exact lRedJac_src_le_of_rm S hS T x hRm tau htau hZ
    _ ≤ ∫⁻ Z : E, ENNReal.ofReal (lSourceGaussian S T x Z)
        ∂modelHaar (E := E) := _root_.MeasureTheory.setLIntegral_le_lintegral _ _
    _ = 1 := lSourceGaussian_mass S T x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.redVolume_le_one_of_rm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.redVolume_le_one_of_rm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.redVolume_le_one_of_rm ``Submission.DifferentialGeometry.PDE.RicciFlow.redVolume_le_one_of_rm

end DifferentialGeometry.PDE.RicciFlow

end
