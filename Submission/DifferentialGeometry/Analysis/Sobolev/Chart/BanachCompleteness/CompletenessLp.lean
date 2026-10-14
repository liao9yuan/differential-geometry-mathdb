import Submission.DifferentialGeometry.Analysis.Sobolev.Chart.BanachCompleteness.Banach
import Submission.DifferentialGeometry.Analysis.Sobolev.Chart.BanachCompleteness.Completeness
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Chart.MeasureComparison
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Chart.Rellich
import Submission.DifferentialGeometry.Analysis.Sobolev.Chart.AtlasNorm.Atlas
import Submission.DifferentialGeometry.Analysis.Sobolev.Manifold.Embedding.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Topology.UniformSpace.UniformEmbedding

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.MeasureTheory _root_.Set _root_.Filter _root_.Topology _root_.Bundle _root_.Submission.Bundle _root_.Manifold
open scoped _root_.Manifold _root_.ContDiff _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Chart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Chart.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Chart.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Chart.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Chart.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

omit [IsManifold I ∞ M] in
lemma chartPushed_eq_chartPushedRaw_pou_mul_on_target
    (ρ : SmoothPartitionOfUnity M I M Set.univ) (α : M) (u : M → ℝ)
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    chartPushed (I := I) (M := M) ρ α u y =
      chartPushedRaw I α (fun x => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) y := by
  classical
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α
    (fun x => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) hy]
  unfold chartPushed
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed_eq_chartPushedRaw_pou_mul_on_target then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed_eq_chartPushedRaw_pou_mul_on_target"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed_eq_chartPushedRaw_pou_mul_on_target ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed_eq_chartPushedRaw_pou_mul_on_target

omit [IsManifold I ∞ M] in
lemma chartPushedRaw_pou_mul_ae_eq_chartPushed_on_target
    (ρ : SmoothPartitionOfUnity M I M Set.univ) (α : M) (u : M → ℝ) :
    (fun y => chartPushedRaw I α
        (fun x => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) y)
      =ᵐ[(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      chartPushed (I := I) (M := M) ρ α u := by
  refine (_root_.MeasureTheory.ae_restrict_iff'
    (chartTargetEuclid_measurableSet (I := I) (M := M) α)).mpr ?_
  refine Filter.Eventually.of_forall (fun y hy => ?_)
  exact (chartPushed_eq_chartPushedRaw_pou_mul_on_target
    (I := I) (M := M) ρ α u hy).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_pou_mul_ae_eq_chartPushed_on_target then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_pou_mul_ae_eq_chartPushed_on_target"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_pou_mul_ae_eq_chartPushed_on_target ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_pou_mul_ae_eq_chartPushed_on_target

omit [IsManifold I ∞ M] in
omit [FiniteDimensional ℝ E] in
lemma support_pou_mul_fun_subset
    (ρ : SmoothPartitionOfUnity M I M Set.univ) (α : M) (u : M → ℝ) :
    Function.support (fun x => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) ⊆
      Function.support ((ρ α : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
  intro x hx
  simp only [Function.mem_support] at hx ⊢
  intro h
  apply hx
  rw [h]; ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.support_pou_mul_fun_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.support_pou_mul_fun_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.support_pou_mul_fun_subset ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.support_pou_mul_fun_subset

omit [IsManifold I ∞ M] in
omit [FiniteDimensional ℝ E] in
lemma tsupport_pou_mul_fun_subset
    (ρ : SmoothPartitionOfUnity M I M Set.univ) (α : M) (u : M → ℝ) :
    tsupport (fun x => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) ⊆
      tsupport ((ρ α : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
  closure_mono (support_pou_mul_fun_subset (I := I) (M := M) ρ α u)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.tsupport_pou_mul_fun_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.tsupport_pou_mul_fun_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.tsupport_pou_mul_fun_subset ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.tsupport_pou_mul_fun_subset

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
lemma tsupport_pou_mul_fun_subset_chartAt_source
    (ρ : SmoothPartitionOfUnity M I M Set.univ)
    (hρ : ρ.IsSubordinate (fun α : M => (chartAt H α).source))
    (α : M) (u : M → ℝ) :
    tsupport (fun x => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) ⊆ (chartAt H α).source :=
  (tsupport_pou_mul_fun_subset (I := I) (M := M) ρ α u).trans (hρ α)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.tsupport_pou_mul_fun_subset_chartAt_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.tsupport_pou_mul_fun_subset_chartAt_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.tsupport_pou_mul_fun_subset_chartAt_source ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.tsupport_pou_mul_fun_subset_chartAt_source

omit [IsManifold I ∞ M] in
omit [FiniteDimensional ℝ E] in
lemma pou_continuous (ρ : SmoothPartitionOfUnity M I M Set.univ) (α : M) :
    Continuous ((ρ α : C^∞⟮I, M; ℝ⟯) : M → ℝ) := (ρ α).contMDiff.continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.pou_continuous then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.pou_continuous"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.pou_continuous ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.pou_continuous

omit [IsManifold I ∞ M] in
omit [FiniteDimensional ℝ E] in
lemma pou_measurable (ρ : SmoothPartitionOfUnity M I M Set.univ) (α : M) :
    Measurable ((ρ α : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
  (pou_continuous (I := I) (M := M) ρ α).measurable

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.pou_measurable then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.pou_measurable"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.pou_measurable ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.pou_measurable

omit [IsManifold I ∞ M] in
lemma eLpNorm_chartPushed_eq_eLpNorm_chartPushedRaw_pou_mul
    (ρ : SmoothPartitionOfUnity M I M Set.univ) (α : M) (u : M → ℝ)
    (p : ℝ≥0∞) :
    eLpNorm (chartPushed (I := I) (M := M) ρ α u) p
        ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
          (chartTargetEuclid (I := I) (M := M) α)) =
      _root_.MeasureTheory.eLpNorm (chartPushedRaw I α
            (fun x => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x)) p
        ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
  _root_.MeasureTheory.eLpNorm_congr_ae
    (chartPushedRaw_pou_mul_ae_eq_chartPushed_on_target
      (I := I) (M := M) ρ α u).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.eLpNorm_chartPushed_eq_eLpNorm_chartPushedRaw_pou_mul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.eLpNorm_chartPushed_eq_eLpNorm_chartPushedRaw_pou_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.eLpNorm_chartPushed_eq_eLpNorm_chartPushedRaw_pou_mul ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.eLpNorm_chartPushed_eq_eLpNorm_chartPushedRaw_pou_mul

lemma fun_eq_finset_sum_pou_mul
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (u : M → ℝ) :
    u = fun x =>
      ∑ α ∈ DifferentialGeometry.Integral.Measure.chartAtlasPOUFinset (I := I) (M := M),
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x := by
  classical
  funext x
  have hsum := chartAtlasPOU_finset_sum_eq_one (I := I) (M := M) x
  have h_eq : ∑ α ∈ DifferentialGeometry.Integral.Measure.chartAtlasPOUFinset (I := I) (M := M),
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) x * u x =
      (∑ α ∈ DifferentialGeometry.Integral.Measure.chartAtlasPOUFinset (I := I) (M := M),
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α : M → ℝ) x) * u x := by
    rw [Finset.sum_mul]
  rw [h_eq, hsum, one_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.fun_eq_finset_sum_pou_mul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.fun_eq_finset_sum_pou_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.fun_eq_finset_sum_pou_mul ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.fun_eq_finset_sum_pou_mul

omit [IsManifold I ∞ M] in
lemma eLpNorm_chartPushed_le_wkpNorm_chartPushed
    {k : ℕ} {p : ℝ≥0∞} (ρ : SmoothPartitionOfUnity M I M Set.univ) (α : M)
    (u : M → ℝ) :
    eLpNorm (chartPushed (I := I) (M := M) ρ α u) p
        ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
          (chartTargetEuclid (I := I) (M := M) α)) ≤
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) k p
        (chartPushed (I := I) (M := M) ρ α u)
        (chartTargetEuclid (I := I) (M := M) α) :=
  Euclidean.wkpNorm_zero_le_wkpNorm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.eLpNorm_chartPushed_le_wkpNorm_chartPushed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.eLpNorm_chartPushed_le_wkpNorm_chartPushed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.eLpNorm_chartPushed_le_wkpNorm_chartPushed ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.eLpNorm_chartPushed_le_wkpNorm_chartPushed

lemma exists_sup_chartDensity_on_pou_tsupport_image
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (α : M)
    (h_support_ne : (tsupport
        ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) : M → ℝ)).Nonempty) :
    ∃ M_sup : ℝ, 0 < M_sup ∧
      ∀ y ∈ (extChartAt I α) '' (tsupport
          ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) : M → ℝ)),
        DifferentialGeometry.Integral.Measure.chartDensity g α
          ((extChartAt I α).symm y) ≤ M_sup := by
  classical
  have hsub :
      tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ) ⊆ (chartAt H α).source :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M α
  have hK_decomp :=
    image_extChartAt_tsupport_compact_subset_target
      (I := I) (M := M)
      (u := ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ)) (α := α) hsub
  obtain ⟨hK_compact, hK_sub_target⟩ := hK_decomp
  have hK_ne : ((extChartAt I α) '' (tsupport
      ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ))).Nonempty := h_support_ne.image _
  exact exists_sup_chartDensity_on_compact_pos (I := I) (M := M)
    g α hK_compact hK_ne hK_sub_target

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.exists_sup_chartDensity_on_pou_tsupport_image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.exists_sup_chartDensity_on_pou_tsupport_image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.exists_sup_chartDensity_on_pou_tsupport_image ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.exists_sup_chartDensity_on_pou_tsupport_image

lemma eLpNorm_pou_mul_riemannianMeasure_le_const_mul_eLpNorm_chartPushed_per_u
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (α : M)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞))
    {u : M → ℝ} (hu_meas : Measurable u) :
    ∃ C : ℝ, 0 < C ∧
      _root_.MeasureTheory.eLpNorm
          (fun x => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
              : C^∞⟮I, M; ℝ⟯) x * u x) p
          (DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M))
        ≤ ENNReal.ofReal C *
            _root_.MeasureTheory.eLpNorm
              (chartPushed (I := I) (M := M)
                (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u) p
              ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
                (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  set ρα : M → ℝ := ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
    : C^∞⟮I, M; ℝ⟯) : M → ℝ) with hρα_def
  set ρu : M → ℝ := fun x => ρα x * u x with hρu_def
  have hρα_meas : Measurable ρα :=
    pou_measurable (I := I) (M := M)
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
  have hρu_meas : Measurable ρu := hρα_meas.mul hu_meas
  have hρu_support : tsupport ρu ⊆ (chartAt H α).source :=
    tsupport_pou_mul_fun_subset_chartAt_source (I := I) (M := M)
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M) α u
  obtain ⟨C, hC_pos, hbnd⟩ :=
    eLpNorm_riemannianMeasure_le_const_mul_eLpNorm_chartPushedRaw
      (I := I) (M := M) g α hp_one hp_top hρu_meas hρu_support
  refine ⟨C, hC_pos, ?_⟩
  refine hbnd.trans ?_
  have h_eq :=
    eLpNorm_chartPushed_eq_eLpNorm_chartPushedRaw_pou_mul (I := I) (M := M)
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u p
  rw [hρu_def, ← h_eq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.eLpNorm_pou_mul_riemannianMeasure_le_const_mul_eLpNorm_chartPushed_per_u then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.eLpNorm_pou_mul_riemannianMeasure_le_const_mul_eLpNorm_chartPushed_per_u"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.eLpNorm_pou_mul_riemannianMeasure_le_const_mul_eLpNorm_chartPushed_per_u ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.eLpNorm_pou_mul_riemannianMeasure_le_const_mul_eLpNorm_chartPushed_per_u

private noncomputable def chartLocalIntegralPouTsupport
    [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (α : M) : ℝ≥0∞ :=
  ∫⁻ x, (tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ)).indicator (fun _ : M => (1 : ℝ≥0∞)) x
      ∂(DifferentialGeometry.Integral.Measure.chartLocalMeasure (I := I) g α)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.chartLocalIntegralPouTsupport
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Chart.chartLocalIntegralPouTsupport target :: scope.openDecls } }

private noncomputable def euclideanDensityIntegralPouTsupport
    [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (α : M) : ℝ≥0∞ :=
  ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
    ENNReal.ofReal
        (DifferentialGeometry.Integral.Measure.chartDensity g α
          ((extChartAt I α).symm
            ((toEuclidean (E := E)).symm y))) *
      (tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) : M → ℝ)).indicator (fun _ : M => (1 : ℝ≥0∞))
        ((extChartAt I α).symm
          ((toEuclidean (E := E)).symm y))
      ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.euclideanDensityIntegralPouTsupport
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Chart.euclideanDensityIntegralPouTsupport target :: scope.openDecls } }

private noncomputable def chartHaarFactor
    [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (α : M) : ℝ≥0∞ :=
  chartLocalIntegralPouTsupport (I := I) (M := M) g α /
    euclideanDensityIntegralPouTsupport (I := I) (M := M) g α

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.chartHaarFactor
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Chart.chartHaarFactor target :: scope.openDecls } }

end Chart
end Sobolev
end Analysis
end DifferentialGeometry
