import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientReducedDensityGaussian
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientVolumeComparison
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Riemannian.GaussianTail

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.BonnetMyers
open _root_.Submission.DifferentialGeometry.Analysis.Measure
open _root_.Submission.DifferentialGeometry.Integral.Measure
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance terminalFiniteTopology : TopologicalSpace F.M := F.topology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalFiniteTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalFiniteTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalFiniteTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalFiniteTopology
local instance terminalFiniteCharted : ChartedSpace H F.M := F.charted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalFiniteCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalFiniteCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalFiniteCharted ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalFiniteCharted
local instance terminalFiniteSmooth : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalFiniteSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalFiniteSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalFiniteSmooth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalFiniteSmooth
local instance terminalFiniteT2 : T2Space F.M := F.t2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalFiniteT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalFiniteT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalFiniteT2 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalFiniteT2
local instance terminalFiniteSigma : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalFiniteSigma then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalFiniteSigma"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalFiniteSigma ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalFiniteSigma
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instMeasurableSpaceM : MeasurableSpace F.M := borel F.M

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instMeasurableSpaceM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instMeasurableSpaceM target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instBorelSpaceM : BorelSpace F.M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instBorelSpaceM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instBorelSpaceM target :: scope.openDecls } }

theorem ancient_lintegral_terminal_gaussian_ne_top
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p : F.M)
    {s decay A : ℝ} (hs : s ≤ 0) (hdecay : 0 < decay) (hA : 0 ≤ A) :
    (∫⁻ q, ENNReal.ofReal (A * Real.exp
      (-decay * (riemannianEDistOf (I := I) (F.S.base.metric 0) p q).toReal ^ 2))
      ∂riemannianVolumeMeasure (I := I) (M := F.M) (F.S.base.metric s)) ≠ (⊤ : ENNReal) := by
  let : ConnectedSpace F.M := hF.connected
  let : TopologicalSpace.MetrizableSpace F.M := Manifold.metrizableSpace I F.M
  let : PseudoMetricSpace F.M := TopologicalSpace.pseudoMetrizableSpacePseudoMetric F.M
  have hdim' : Module.finrank ℝ E ≠ 0 := by
    intro hzero
    obtain ⟨t, ht, x, hx⟩ := hF.notFlat
    have hb := ancientKappa_rmNormLeScalar_finrank F hF t ht x
    rw [hzero, Nat.cast_zero] at hb
    norm_num at hb
    have hn : 0 ≤ F.rmNormSq (I := I) t x := by
      simpa only [PointedFlowData.rmNormSq, SolutionOn.family] using
        DifferentialGeometry.Tensor0SBundle.normSq0S_nonneg
          (I := I) (F.S.base.metric t) x 4 (F.S.base.rm04 t x)
    have hz : Real.sqrt (F.rmNormSq (I := I) t x) = 0 :=
      le_antisymm hb (Real.sqrt_nonneg _)
    exact hx ((Real.sqrt_eq_zero hn).mp hz)
  let : NeZero (Module.finrank ℝ E) := ⟨hdim'⟩
  obtain ⟨K, hK, hvol⟩ := exists_ancientKappa_volumeMeasure_le_exp F hF
  have hmeasure := hvol s 0 hs le_rfl
  let f : F.M → ENNReal := fun q => ENNReal.ofReal (A * Real.exp
    (-decay * (riemannianEDistOf (I := I) (F.S.base.metric 0) p q).toReal ^ 2))
  have hmono := MeasureTheory.lintegral_mono' hmeasure (le_refl f)
  rw [MeasureTheory.lintegral_smul_measure] at hmono
  have hcomplete : RiemannianMetricComplete (I := I) (F.S.base.metric 0) :=
    ⟨hF.complete 0 (by simp [ancientTimeInterval_carrier])⟩
  have hRic : RicciBoundedBelow (I := I) (F.S.base.metric 0) 0 := by
    intro x v
    rw [_root_.MulZeroClass.zero_mul, ← metricRicciAt_apply_eq_ricciTensor]
    apply metricRicciAt_nonnegative_of_curvatureOperator_nonnegative
    apply (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff
      (F.S.base.metric 0) x).mpr
    intro n c a b
    simpa only [SolutionFamily.rm04, metricRm04StandardAt_apply, metricRm04_apply] using
      hF.nonnegativeCurvatureOperator 0 (by simp [ancientTimeInterval_carrier]) x n c a b
  have hgauss := lintegral_gaussian_riemannianEDistOf_le
    (F.S.base.metric 0) hcomplete p hdecay hRic 0
  have hgauss' : (∫⁻ q, ENNReal.ofReal (Real.exp
      (-decay * (riemannianEDistOf (I := I) (F.S.base.metric 0) p q).toReal ^ 2))
      ∂riemannianVolumeMeasure (I := I) (M := F.M) (F.S.base.metric 0)) ≤
      (((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).toSphere _root_.Set.univ *
        ENNReal.ofReal ((Module.finrank ℝ E : ℝ)⁻¹)) * gaussianTail
          (Module.finrank ℝ E) decay 0) := by
    have htailset : {q : F.M | (0 : ℝ) ≤
        (riemannianEDistOf (I := I) (F.S.base.metric 0) p q).toReal} = Set.univ := by
      ext q
      simp only [_root_.Set.mem_ofPred_eq, _root_.Set.mem_univ, iff_true]
      exact ENNReal.toReal_nonneg
    rw [← MeasureTheory.setLIntegral_univ, ← htailset]
    simpa only [Nat.cast_zero] using hgauss
  have hAint : (∫⁻ q, f q ∂riemannianVolumeMeasure (I := I) (M := F.M)
      (F.S.base.metric 0)) ≤ ENNReal.ofReal A *
      ((((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).toSphere _root_.Set.univ *
        ENNReal.ofReal ((Module.finrank ℝ E : ℝ)⁻¹)) * gaussianTail
          (Module.finrank ℝ E) decay 0)) := by
    have hf : (fun q => f q) = (fun q => ENNReal.ofReal A * ENNReal.ofReal
        (Real.exp (-decay * (riemannianEDistOf (I := I) (F.S.base.metric 0) p q).toReal ^ 2))) := by
      funext q
      dsimp only [f]
      rw [ENNReal.ofReal_mul hA]
    rw [hf]
    rw [_root_.MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact mul_le_mul_of_nonneg_left hgauss' (by positivity)
  have htail : gaussianTail (Module.finrank ℝ E) decay 0 ≠ (⊤ : ENNReal) := by
    dsimp [gaussianTail]
    exact (summable_gaussianShell (Module.finrank ℝ E) hdecay).tsum_ofReal_ne_top
  have hfinite : ENNReal.ofReal A *
      (((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).toSphere _root_.Set.univ *
        ENNReal.ofReal ((Module.finrank ℝ E : ℝ)⁻¹)) * gaussianTail
          (Module.finrank ℝ E) decay 0 ) ≠ (⊤ : ENNReal) := by
    apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (_root_.MeasureTheory.measure_ne_top (volume.toSphere) _root_.Set.univ) ENNReal.ofReal_ne_top) htail
  have hc : ENNReal.ofReal (Real.sqrt (Real.exp (2 * K * (0 - s)) ^ Module.finrank ℝ E)) ≠ (⊤ : ENNReal) := ENNReal.ofReal_ne_top
  have hfinite' := ENNReal.mul_ne_top hc hfinite
  apply ne_top_of_le_ne_top hfinite'
  calc
    _ ≤ ENNReal.ofReal (Real.sqrt (Real.exp (2 * K * (0 - s)) ^ Module.finrank ℝ E)) •
        (∫⁻ q, f q ∂riemannianVolumeMeasure (I := I) (M := F.M) (F.S.base.metric 0)) := hmono
    _ ≤ ENNReal.ofReal (Real.sqrt (Real.exp (2 * K * (0 - s)) ^ Module.finrank ℝ E)) •
        (ENNReal.ofReal A *
          (((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).toSphere _root_.Set.univ *
            ENNReal.ofReal ((Module.finrank ℝ E : ℝ)⁻¹)) * gaussianTail
              (Module.finrank ℝ E) decay 0)) := by
      exact smul_le_smul_left _ hAint
    _ = _ := by simp only [smul_eq_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_lintegral_terminal_gaussian_ne_top then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_lintegral_terminal_gaussian_ne_top"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_lintegral_terminal_gaussian_ne_top ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_lintegral_terminal_gaussian_ne_top


end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
