import Submission.DifferentialGeometry.Analysis.Calculus.TimeJet.Seam
import Submission.DifferentialGeometry.Geometry.Metric.Family.JointSmoothness
import Submission.DifferentialGeometry.Geometry.Curvature.Coordinates.MetricJet.ChartBridge

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Set
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Submission.DifferentialGeometry.Analysis
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Operator _root_.Submission.DifferentialGeometry.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instCompleteSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instIsManifoldRealOfNatWithTopENat_differentialGeometry : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instIsManifoldRealOfNatWithTopENat_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instIsManifoldRealOfNatWithTopENat_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instIsManifoldRealOfNatWithTopENat_differentialGeometry_1 : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instIsManifoldRealOfNatWithTopENat_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instIsManifoldRealOfNatWithTopENat_differentialGeometry_1 target :: scope.openDecls } }

private theorem chartGramPi_hasDerivAt_of_metricPDE
    (g : ℝ → SmoothRiemannianMetric I M) (p : M) {t : ℝ}
    (hpde : ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivAt (fun s => (g s).inner x v w) (-2 * ricciTensor (I := I) (g t) x v w) t)
    {y : E} (hy : y ∈ (extChartAt I p).target) :
    HasDerivAt (fun s => chartGramPi (I := I) (g s) p y)
      (jetRicciFlow (chartModelBasis E) (jet2 (chartGramPi (I := I) (g t) p) y)) t := by
  have hstatic : ContDiffOn ℝ ∞ (chartGramPi (I := I) (g t) p) (extChartAt I p).target :=
    contDiffOn_pi.mpr fun i => contDiffOn_pi.mpr fun j =>
      chartGramOnE_contDiffOn (I := I) (g t) p i j
  have hopen := isOpen_extChartAt_target (I := I) p
  have hyint : y ∈ interior (extChartAt I p).target := hopen.interior_eq.symm ▸ hy
  have hsrc := (extChartAt I p).map_target hy
  have hxy := (extChartAt I p).right_inv hy
  have hbase : (extChartAt I p).symm y ∈
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) p).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source, ← extChartAt_source_eq_chartAt_source (I := I)]
    exact hsrc
  have hgood : (extChartAt I p).symm y ∈ chartLeviCivitaGoodSet (I := I) p :=
    mem_chartLeviCivitaGoodSet_iff.mpr ⟨hsrc, hbase, by simpa only [hxy] using hyint⟩
  have hAt := hstatic.contDiffAt (hopen.mem_nhds hy)
  have hG1 : ∀ᶠ z in 𝓝 y, DifferentiableAt ℝ (chartGramPi (I := I) (g t) p) z := by
    filter_upwards [hopen.mem_nhds hy] with z hz
    exact (hstatic.contDiffAt (hopen.mem_nhds hz)).differentiableAt (by simp)
  have hG2 : DifferentiableAt ℝ (fun z => fderiv ℝ (chartGramPi (I := I) (g t) p) z) y :=
    (hAt.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  refine hasDerivAt_pi.mpr fun i => hasDerivAt_pi.mpr fun j => ?_
  have hmetric := hpde ((extChartAt I p).symm y)
    (chartBasisVecFiber (I := I) p i ((extChartAt I p).symm y))
    (chartBasisVecFiber (I := I) p j ((extChartAt I p).symm y))
  have hentry := chartGramEntryPDE_of_metricPDE (I := I) g p hgood hxy i j
    (sL := _root_.Set.univ) hmetric.hasDerivWithinAt
  have hflow := jetRicciFlow_chartGram (I := I) (g t) p hyint
    (hAt.differentiableAt (by simp)) hG1 hG2 i j
  exact (hentry.hasDerivAt (_root_.Filter.univ_mem : _root_.Set.univ ∈ 𝓝 t)).congr_deriv hflow.symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.chartGramPi_hasDerivAt_of_metricPDE
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.chartGramPi_hasDerivAt_of_metricPDE target :: scope.openDecls } }

omit [I.Boundaryless] [T2Space M] in
private theorem chartGramPi_det_ne_zero
    (g : SmoothRiemannianMetric I M) (p : M) {y : E}
    (hy : y ∈ (extChartAt I p).target) :
    (Matrix.of (jet2 (chartGramPi (I := I) g p) y).1).det ≠ 0 := by
  have hbase : (extChartAt I p).symm y ∈
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) p).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]
    have hs := (extChartAt I p).map_target hy
    rwa [extChartAt_source_eq_chartAt_source (I := I)] at hs
  have heq : Matrix.of (jet2 (chartGramPi (I := I) g p) y).1 =
      chartGramMatrix (I := I) g p ((extChartAt I p).symm y) := by
    ext i j
    rfl
  rw [heq]
  exact (chartGramMatrix_det_pos (I := I) g p hbase).ne'

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.chartGramPi_det_ne_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.chartGramPi_det_ne_zero target :: scope.openDecls } }

theorem metricCLMSection_jointContMDiffOn_ite_of_ricciFlow
    (gL gR : ℝ → SmoothRiemannianMetric I M) {a c b : ℝ} (ha : a < c) (hb : c < b)
    (hL : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun q : ℝ × M => (⟨q.2, (gL q.1).inner q.2⟩ :
        _root_.Bundle.TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (_root_.Set.Icc a c ×ˢ (_root_.Set.univ : Set M)))
    (hR : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun q : ℝ × M => (⟨q.2, (gR q.1).inner q.2⟩ :
        _root_.Bundle.TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (_root_.Set.Icc c b ×ˢ (_root_.Set.univ : Set M)))
    (hpdeL : ∀ t ∈ _root_.Set.Ioo a c, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivAt (fun s => (gL s).inner x v w) (-2 * ricciTensor (I := I) (gL t) x v w) t)
    (hpdeR : ∀ t ∈ _root_.Set.Ioo c b, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivAt (fun s => (gR s).inner x v w) (-2 * ricciTensor (I := I) (gR t) x v w) t)
    (hmatch : gL c = gR c) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun q : ℝ × M => (⟨q.2, ((if q.1 ≤ c then gL q.1 else gR q.1)).inner q.2⟩ :
        _root_.Bundle.TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (_root_.Set.Icc a b ×ˢ (_root_.Set.univ : Set M)) := by
  apply metricCLMSection_jointContMDiffOn_of_chartGram_on
    (fun t => if t ≤ c then gL t else gR t) (_root_.Set.Icc a b)
  intro p i j
  let Ω : Set (MatJet E (Module.finrank ℝ E)) := {z | (Matrix.of z.1).det ≠ 0}
  have hdet : Continuous (fun z : MatJet E (Module.finrank ℝ E) => (Matrix.of z.1).det) :=
    (contDiff_det_of_entries (fun z : MatJet E (Module.finrank ℝ E) => Matrix.of z.1)
      (fun i j => contDiff_jetVal i j)).continuous
  have hΩ : IsOpen Ω := by
    simpa only [Ω, Set.mem_ofPred_eq] using
      (isOpen_ne_fun hdet (continuous_const : Continuous
        (fun _ : MatJet E (Module.finrank ℝ E) => (0 : ℝ))))
  have hΦ : ContDiffOn ℝ ∞ (jetRicciFlow (chartModelBasis E)) Ω :=
    fun z hz => (contDiffAt_jetRicciFlow (chartModelBasis E) hz).contDiffWithinAt
  have hGL : ContDiffOn ℝ ∞ (Function.uncurry (fun t => chartGramPi (I := I) (gL t) p))
      (_root_.Set.Icc a c ×ˢ (extChartAt I p).target) :=
    contDiffOn_pi.mpr fun i => contDiffOn_pi.mpr fun j =>
      chartGramOnE_joint_contDiffOn gL (_root_.Set.Icc a c) hL p i j
  have hGR : ContDiffOn ℝ ∞ (Function.uncurry (fun t => chartGramPi (I := I) (gR t) p))
      (_root_.Set.Icc c b ×ˢ (extChartAt I p).target) :=
    contDiffOn_pi.mpr fun i => contDiffOn_pi.mpr fun j =>
      chartGramOnE_joint_contDiffOn gR (_root_.Set.Icc c b) hR p i j
  have hG := contDiffOn_ite_of_jet_pde ha hb (isOpen_extChartAt_target p) hΩ hGL hGR hΦ
    (fun q hq => chartGramPi_det_ne_zero (gL q.1) p hq.2)
    (fun q hq => chartGramPi_det_ne_zero (gR q.1) p hq.2)
    (fun t ht y hy => chartGramPi_hasDerivAt_of_metricPDE gL p (hpdeL t ht) hy)
    (fun t ht y hy => chartGramPi_hasDerivAt_of_metricPDE gR p (hpdeR t ht) hy)
    (fun y _ => congrArg (fun g => chartGramPi (I := I) g p y) hmatch)
  have hentry := contDiffOn_pi.mp (contDiffOn_pi.mp hG i) j
  have hsource {y : M} (hy : y ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) p).baseSet) :
      y ∈ (extChartAt I p).source := by
    rwa [extChartAt_source_eq_chartAt_source, ← trivializationAt_baseSet_eq_chartAt_source (I := I)]
  have harg : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ × E) ∞
      (fun q : ℝ × M => (q.1, extChartAt I p q.2))
      (_root_.Set.Icc a b ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) p).baseSet) := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact contMDiffOn_fst.prodMk ((contMDiffOn_extChartAt (I := I) (x := p)).comp contMDiffOn_snd
      (fun q hq => by
        simpa only [Set.mem_preimage, trivializationAt_baseSet_eq_chartAt_source] using hq.2))
  have hh := hentry.contMDiffOn.comp harg (fun q hq => ⟨hq.1,
    (extChartAt I p).map_source (hsource hq.2)⟩)
  apply hh.congr
  intro q hq
  dsimp only [Function.comp_apply]
  split_ifs with hqc
  · change chartGramMatrix (gL q.1) p q.2 i j =
      chartGramMatrix (gL q.1) p ((extChartAt I p).symm (extChartAt I p q.2)) i j
    rw [(extChartAt I p).left_inv (hsource hq.2)]
  · change chartGramMatrix (gR q.1) p q.2 i j =
      chartGramMatrix (gR q.1) p ((extChartAt I p).symm (extChartAt I p q.2)) i j
    rw [(extChartAt I p).left_inv (hsource hq.2)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.metricCLMSection_jointContMDiffOn_ite_of_ricciFlow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.metricCLMSection_jointContMDiffOn_ite_of_ricciFlow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.metricCLMSection_jointContMDiffOn_ite_of_ricciFlow ``Submission.DifferentialGeometry.PDE.RicciFlow.metricCLMSection_jointContMDiffOn_ite_of_ricciFlow

theorem metricTensorField_iteratedDerivWithin_eq_of_ricciFlow
    (gL gR : ℝ → SmoothRiemannianMetric I M) {a c b : ℝ} (ha : a < c) (hb : c < b)
    (hL : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun q : ℝ × M => (⟨q.2, (gL q.1).inner q.2⟩ :
        _root_.Bundle.TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (_root_.Set.Icc a c ×ˢ (_root_.Set.univ : Set M)))
    (hR : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun q : ℝ × M => (⟨q.2, (gR q.1).inner q.2⟩ :
        _root_.Bundle.TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (_root_.Set.Icc c b ×ˢ (_root_.Set.univ : Set M)))
    (hpdeL : ∀ t ∈ _root_.Set.Ioo a c, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivAt (fun s => (gL s).inner x v w) (-2 * ricciTensor (I := I) (gL t) x v w) t)
    (hpdeR : ∀ t ∈ _root_.Set.Ioo c b, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivAt (fun s => (gR s).inner x v w) (-2 * ricciTensor (I := I) (gR t) x v w) t)
    (hmatch : gL c = gR c) (m : ℕ) (x : M) :
    iteratedDerivWithin m (fun t => Tensor0SBundle.metricTensorField (gL t) x) (_root_.Set.Icc a c) c =
      iteratedDerivWithin m (fun t => Tensor0SBundle.metricTensorField (gR t) x) (_root_.Set.Icc c b) c := by
  let g := fun t => if t ≤ c then gL t else gR t
  have hg := metricCLMSection_jointContMDiffOn_ite_of_ricciFlow gL gR ha hb hL hR hpdeL hpdeR hmatch
  have htime := metricTensorField_contDiffOn_time g (_root_.Set.Icc a b) hg x
  have htc : ContDiffAt ℝ ∞ (fun t => Tensor0SBundle.metricTensorField (g t) x) c :=
    htime.contDiffAt (Icc_mem_nhds ha hb)
  have heqL : _root_.Set.EqOn (fun t => Tensor0SBundle.metricTensorField (g t) x)
      (fun t => Tensor0SBundle.metricTensorField (gL t) x) (_root_.Set.Icc a c) := by
    intro t ht
    simp only [g, if_pos ht.2]
  have heqR : _root_.Set.EqOn (fun t => Tensor0SBundle.metricTensorField (g t) x)
      (fun t => Tensor0SBundle.metricTensorField (gR t) x) (_root_.Set.Icc c b) := by
    intro t ht
    by_cases htc : t ≤ c
    · have he : t = c := le_antisymm htc ht.1
      subst t
      simp only [g, if_pos le_rfl, hmatch]
    · simp only [g, if_neg htc]
  rw [← iteratedDerivWithin_congr heqL ⟨ha.le, le_rfl⟩,
    ← iteratedDerivWithin_congr heqR ⟨le_rfl, hb.le⟩,
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc ha)
      (htc.of_le (by exact_mod_cast le_top)) ⟨ha.le, le_rfl⟩,
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hb)
      (htc.of_le (by exact_mod_cast le_top)) ⟨le_rfl, hb.le⟩]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.metricTensorField_iteratedDerivWithin_eq_of_ricciFlow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.metricTensorField_iteratedDerivWithin_eq_of_ricciFlow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.metricTensorField_iteratedDerivWithin_eq_of_ricciFlow ``Submission.DifferentialGeometry.PDE.RicciFlow.metricTensorField_iteratedDerivWithin_eq_of_ricciFlow

end DifferentialGeometry.PDE.RicciFlow
