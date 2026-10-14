import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.RecenteredStaticPreparation
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.StaticWitnessVolume

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.TopologicalSpace _root_.Manifold _root_.Submission.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Neck _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Topology.Manifold.Attachment
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
universe u v w z
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.E3 target :: scope.openDecls } }

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instMeasurableSpaceE3 : MeasurableSpace E3 := borel E3

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instMeasurableSpaceE3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instMeasurableSpaceE3 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instBorelSpaceE3 : BorelSpace E3 := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instBorelSpaceE3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instBorelSpaceE3 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instChartedSpaceE3InsertionQuotient {B : ℝ} {hB : 0 < B} : ChartedSpace E3 (InsertionQuotient hB) :=
  radialCapAttachmentChartedSpace transitionEnd_pos hB

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instChartedSpaceE3InsertionQuotient
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instChartedSpaceE3InsertionQuotient target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopInsertionQuotient {B : ℝ} {hB : 0 < B} : IsManifold (𝓡 3) ∞ (InsertionQuotient hB) :=
  radialCapAttachment_isManifold transitionEnd_pos hB

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopInsertionQuotient
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopInsertionQuotient target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instT2SpaceInsertionQuotient {B : ℝ} {hB : 0 < B} : T2Space (InsertionQuotient hB) :=
  radialCapAttachment_t2Space transitionEnd_pos hB

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instT2SpaceInsertionQuotient
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instT2SpaceInsertionQuotient target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instSecondCountableTopologyInsertionQuotient {B : ℝ} {hB : 0 < B} : SecondCountableTopology (InsertionQuotient hB) :=
  radialCapAttachment_secondCountableTopology transitionEnd_pos hB

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instSecondCountableTopologyInsertionQuotient
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instSecondCountableTopologyInsertionQuotient target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instLocallyCompactSpaceInsertionQuotient {B : ℝ} {hB : 0 < B} : LocallyCompactSpace (InsertionQuotient hB) := by
  let : LocallyCompactSpace {x : E3 // ‖x‖ < transitionEnd + B} :=
    (isOpen_lt continuous_norm continuous_const).locallyCompactSpace
  exact (radialCapAttachmentHomeomorph transitionEnd_pos hB :
    InsertionQuotient hB ≃ₜ insertionBall B).isClosedEmbedding.locallyCompactSpace

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instLocallyCompactSpaceInsertionQuotient
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instLocallyCompactSpaceInsertionQuotient target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instMeasurableSpaceInsertionQuotient {B : ℝ} {hB : 0 < B} : MeasurableSpace (InsertionQuotient hB) :=
  borel (InsertionQuotient hB)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instMeasurableSpaceInsertionQuotient
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instMeasurableSpaceInsertionQuotient target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instBorelSpaceInsertionQuotient {B : ℝ} {hB : 0 < B} : BorelSpace (InsertionQuotient hB) := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instBorelSpaceInsertionQuotient
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instBorelSpaceInsertionQuotient target :: scope.openDecls } }


theorem exists_uniform_recentered_static_family_volume_bound :
    ∃ c : ℝ, 4 ≤ c ∧ ∃ C : ℕ → ℝ, (∀ j, 0 < C j) ∧
      ∃ (A : ℝ) (hA : 0 < A), 2 * A < 1 / 2 ∧
      ∀ (D : ℝ), 0 < D → ∀ (m : ℕ) (ε : ℝ), 0 < ε →
      ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < 1 / 4 ∧
      ∀ {E : Type u} {H : Type v} {M : Type w}
        [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
        [Fact (Module.finrank ℝ E = 3)] [TopologicalSpace H]
        {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
        (g : SmoothRiemannianMetric I M) {ι : Type z}
        (x₀ : ι → M) (δ : ι → ℝ)
        (d₀ : ∀ i, normalizedDatum g (x₀ i) (δ i) (m + 6)),
        (∀ i, δ i ≤ δ₀) → ∀ (σ : ι → ℝ) (hσ : ∀ i, σ i ^ 2 = 1),
        ∃ hfit : ∀ i, (c * δ i)⁻¹ + 1 ≤ (δ i)⁻¹,
        ∃ d : ∀ i, normalizedDatum g ((d₀ i).offsetPoint (hσ i)) (c * δ i) (m + 4),
        ∃ w : ∀ i, CanonicalStaticInsertionWitness (d i) A hA D m ε,
          (∀ i, (d i).map = (d₀ i).recenteringMap (hσ i) (hfit i)) ∧
          (∀ i, (d i).retainedSide = _root_.Bool.true) ∧
          (∀ i, |metricScalarAt g ((d₀ i).offsetPoint (hσ i)) / metricScalarAt g (x₀ i) - 1| ≤ c * δ i) ∧
          (∀ i, metricScalarAt g (x₀ i) / 2 ≤ metricScalarAt g ((d₀ i).offsetPoint (hσ i))) ∧
          (∀ i, metricScalarAt g ((d₀ i).offsetPoint (hσ i)) ≤ (3 / 2 : ℝ) * metricScalarAt g (x₀ i)) ∧
          (∀ i, StaticInsertionAdditionalProperties C (w i)) ∧
          (∀ i, riemannianVolumeMeasure (𝓡 3) (InsertionQuotient (inv_pos.mpr (d i).precision_pos))
            (w i).data.outMetric (_root_.Set.range (w i).data.capMap) ≤
              ENNReal.ofReal (8 * (metricScalarAt g (x₀ i)) ^ (-3 / 2 : ℝ)) *
                riemannianVolumeMeasure (𝓡 3) E3 metric {x | ‖x‖ ≤ transitionEnd}) := by
  obtain ⟨c, hc, C, hC, A, hA, hsmall, hfactory⟩ := exists_uniform_recentered_static_preparation.{u, v, w}
  obtain ⟨δv, hδv, _, hvolume⟩ := exists_canonicalStaticInsertionWitness_cap_volume_bound_of_scalar_lower A hA
  have hcpos : 0 < c := lt_of_lt_of_le (by norm_num) hc
  refine ⟨c, hc, C, hC, A, hA, hsmall, ?_⟩
  intro D hD m ε hε
  obtain ⟨δr, hδr, hquarter, hprep⟩ := hfactory D hD m ε hε
  let δ₀ := _root_.Min.min δr (_root_.Min.min (δv / c) (1 / 8646))
  refine ⟨δ₀, lt_min hδr (lt_min (div_pos hδv hcpos) (by norm_num)),
    (min_le_left _ _).trans_lt hquarter, ?_⟩
  intro E H M _ _ _ _ _ I _ _ _ _ _ g ι x₀ δ d₀ hδ σ hσ
  have hrec (i : ι) := hprep (δ i) (d₀ i).precision_pos
    ((hδ i).trans (min_le_left _ _)) g (x₀ i) (d₀ i) (σ i) (hσ i)
  choose hfit d hmap hside hratio w hw using hrec
  have hb (i : ι) : metricScalarAt g (x₀ i) / 2 ≤ metricScalarAt g ((d₀ i).offsetPoint (hσ i)) ∧
      metricScalarAt g ((d₀ i).offsetPoint (hσ i)) ≤ (3 / 2 : ℝ) * metricScalarAt g (x₀ i) := by
    have hdsmall : δ i ≤ 1 / 8646 := (hδ i).trans ((min_le_right _ _).trans (min_le_right _ _))
    let q : bufferedCylinder (δ i) := ⟨(spherePoint, σ i), offset_mem_bufferedCylinder (d₀ i).precision_pos (hσ i) spherePoint⟩
    have hq : q ∈ controlledCylinder (δ i) := by
      change -(δ i)⁻¹ ≤ σ i ∧ σ i ≤ (δ i)⁻¹
      have hi := (one_le_inv₀ (d₀ i).precision_pos).mpr (d₀ i).precision_lt_one.le
      rcases sq_eq_one_iff.mp (hσ i) with h | h <;> rw [h] <;> constructor <;> linarith
    have hr := (d₀ i).abs_scalar_ratio_sub_one_le (by omega) (by linarith) q hq
    have hlo : (1 / 2 : ℝ) ≤ metricScalarAt g ((d₀ i).map q) / metricScalarAt g (x₀ i) := by
      have hh := (abs_le.mp hr).1
      linarith
    have hhi : metricScalarAt g ((d₀ i).map q) / metricScalarAt g (x₀ i) ≤ (3 / 2 : ℝ) := by
      have hh := (abs_le.mp hr).2
      linarith
    change metricScalarAt g (x₀ i) / 2 ≤ metricScalarAt g ((d₀ i).map q) ∧
      metricScalarAt g ((d₀ i).map q) ≤ (3 / 2 : ℝ) * metricScalarAt g (x₀ i)
    exact ⟨by linarith [(le_div_iff₀ (d₀ i).scalar_pos).mp hlo],
      (div_le_iff₀ (d₀ i).scalar_pos).mp hhi⟩
  refine ⟨hfit, d, w, hmap, hside, hratio, fun i => (hb i).1, fun i => (hb i).2, hw, ?_⟩
  intro i
  have hvsmall : c * δ i ≤ δv := by
    have h := (hδ i).trans ((min_le_right _ _).trans (min_le_left _ _))
    exact (mul_comm c (δ i)) ▸ (le_div_iff₀ hcpos).mp h
  exact hvolume (c * δ i) (d i).precision_pos hvsmall (m + 4) g ((d₀ i).offsetPoint (hσ i))
    (d i) D m ε (w i) (metricScalarAt g (x₀ i)) (d₀ i).scalar_pos (hb i).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_uniform_recentered_static_family_volume_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_uniform_recentered_static_family_volume_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_uniform_recentered_static_family_volume_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_uniform_recentered_static_family_volume_bound

end DifferentialGeometry.PDE.RicciFlow.StandardCap
