import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.StaticWitness
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.NormalizedInsertionVolume

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Submission.Set _root_.TopologicalSpace _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry.Integral.Measure _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Neck _root_.Submission.DifferentialGeometry.Topology.Manifold.Attachment
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

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

private theorem cap_volume_scale_factor (Q : ℝ) (hQ : 0 < Q) :
    ENNReal.ofReal (Real.sqrt Q⁻¹) ^ 3 = ENNReal.ofReal (Q ^ (-3 / 2 : ℝ)) := by
  rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _) 3]
  congr 1
  calc
    (Real.sqrt Q⁻¹) ^ 3 = (Q⁻¹ ^ (1 / 2 : ℝ)) ^ (3 : ℕ) := by rw [Real.sqrt_eq_rpow]
    _ = Q⁻¹ ^ ((1 / 2 : ℝ) * 3) :=
      (Real.rpow_mul_natCast (inv_nonneg.mpr hQ.le) _ 3).symm
    _ = Q ^ (-((1 / 2 : ℝ) * 3)) := (Real.rpow_neg_eq_inv_rpow Q _).symm
    _ = Q ^ (-3 / 2 : ℝ) := by congr 1; ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.cap_volume_scale_factor
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.cap_volume_scale_factor target :: scope.openDecls } }

private theorem cap_volume_coefficient_le {Q Qloc : ℝ}
    (hQ : 0 < Q) (hlocal : Q / 2 ≤ Qloc) :
    2 * Qloc ^ (-3 / 2 : ℝ) ≤ 8 * Q ^ (-3 / 2 : ℝ) := by
  have hpower : Qloc ^ (-3 / 2 : ℝ) ≤ (Q / 2) ^ (-3 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos (half_pos hQ) hlocal (by norm_num)
  have hinv : ((2 : ℝ) ^ (-3 / 2 : ℝ))⁻¹ = (2 : ℝ) ^ (3 / 2 : ℝ) := by
    rw [show (-3 / 2 : ℝ) = -(3 / 2 : ℝ) by ring,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), inv_inv]
  have hscale : (Q / 2) ^ (-3 / 2 : ℝ) =
      Q ^ (-3 / 2 : ℝ) * (2 : ℝ) ^ (3 / 2 : ℝ) := by
    rw [Real.div_rpow hQ.le (by norm_num), div_eq_mul_inv, hinv]
  have htwo : (2 : ℝ) ^ (3 / 2 : ℝ) ≤ 4 := by
    calc
      _ ≤ (2 : ℝ) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 4 := by norm_num
  rw [hscale] at hpower
  calc
    _ ≤ 2 * (Q ^ (-3 / 2 : ℝ) * (2 : ℝ) ^ (3 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hpower (by norm_num)
    _ ≤ 2 * (Q ^ (-3 / 2 : ℝ) * 4) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left htwo (Real.rpow_nonneg hQ.le _)) (by norm_num)
    _ = _ := by ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.cap_volume_coefficient_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.cap_volume_coefficient_le target :: scope.openDecls } }

theorem exists_canonicalStaticInsertionWitness_cap_volume_bound (A : ℝ) (hA : 0 < A) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < 1 / 2 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ k : ℕ, ∀ {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M],
      ∀ (g : SmoothRiemannianMetric I M) (x₀ : M) (d : normalizedDatum g x₀ δ k)
        (D : ℝ) (m : ℕ) (ε : ℝ) (w : CanonicalStaticInsertionWitness d A hA D m ε),
        riemannianVolumeMeasure (𝓡 3) (InsertionQuotient (inv_pos.mpr d.precision_pos))
          w.data.outMetric (_root_.Set.range w.data.capMap) ≤
          ENNReal.ofReal (2 * (metricScalarAt g x₀) ^ (-3 / 2 : ℝ)) *
            riemannianVolumeMeasure (𝓡 3) E3 metric {x | ‖x‖ ≤ transitionEnd} := by
  obtain ⟨δ₀, hδ₀, hhalf, hvolume⟩ :=
    exists_normalizedDatum_positiveSideInsertionMetric_cap_volume_bound A hA
  refine ⟨δ₀, hδ₀, hhalf, ?_⟩
  intro δ hδ hle k E H M _ _ _ _ _ I _ _ _ _ _ g x₀ d D m ε w
  obtain ⟨hAB, hv⟩ := hvolume δ hδ hle
  have hvol := hv k g x₀ d.oriented
  rw [cap_volume_scale_factor _ d.scalar_pos] at hvol
  rw [w.properties.outMetric_eq, w.properties.capMap_eq, w.properties.capInclusion_eq]
  have hfactor :
      ENNReal.ofReal ((metricScalarAt g x₀) ^ (-3 / 2 : ℝ)) *
          (2 * riemannianVolumeMeasure (𝓡 3) E3 metric {x | ‖x‖ ≤ transitionEnd}) =
        ENNReal.ofReal (2 * (metricScalarAt g x₀) ^ (-3 / 2 : ℝ)) *
          riemannianVolumeMeasure (𝓡 3) E3 metric {x | ‖x‖ ≤ transitionEnd} := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
    rw [← mul_assoc, mul_comm _ (2 : ℝ≥0∞)]
  exact hvol.trans_eq hfactor

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_canonicalStaticInsertionWitness_cap_volume_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_canonicalStaticInsertionWitness_cap_volume_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_canonicalStaticInsertionWitness_cap_volume_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_canonicalStaticInsertionWitness_cap_volume_bound

theorem exists_canonicalStaticInsertionWitness_cap_volume_bound_of_scalar_lower
    (A : ℝ) (hA : 0 < A) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < 1 / 2 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ k : ℕ, ∀ {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M],
      ∀ (g : SmoothRiemannianMetric I M) (x₀ : M) (d : normalizedDatum g x₀ δ k)
        (D : ℝ) (m : ℕ) (ε : ℝ) (w : CanonicalStaticInsertionWitness d A hA D m ε)
        (Q : ℝ), 0 < Q → Q / 2 ≤ metricScalarAt g x₀ →
        riemannianVolumeMeasure (𝓡 3) (InsertionQuotient (inv_pos.mpr d.precision_pos))
          w.data.outMetric (_root_.Set.range w.data.capMap) ≤
          ENNReal.ofReal (8 * Q ^ (-3 / 2 : ℝ)) *
            riemannianVolumeMeasure (𝓡 3) E3 metric {x | ‖x‖ ≤ transitionEnd} := by
  obtain ⟨δ₀, hδ₀, hhalf, hvolume⟩ :=
    exists_canonicalStaticInsertionWitness_cap_volume_bound A hA
  refine ⟨δ₀, hδ₀, hhalf, ?_⟩
  intro δ hδ hle k E H M _ _ _ _ _ I _ _ _ _ _ g x₀ d D m ε w Q hQ hlocal
  exact (hvolume δ hδ hle k g x₀ d D m ε w).trans
    (mul_le_mul' (ENNReal.ofReal_le_ofReal (cap_volume_coefficient_le hQ hlocal)) le_rfl)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_canonicalStaticInsertionWitness_cap_volume_bound_of_scalar_lower then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_canonicalStaticInsertionWitness_cap_volume_bound_of_scalar_lower"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_canonicalStaticInsertionWitness_cap_volume_bound_of_scalar_lower ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_canonicalStaticInsertionWitness_cap_volume_bound_of_scalar_lower

end DifferentialGeometry.PDE.RicciFlow.StandardCap
