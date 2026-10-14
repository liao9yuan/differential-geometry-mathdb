import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.HalfBandSeparation
import Submission.DifferentialGeometry.Geometry.Neck.HalfBandVolume
import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.RetainedCoreMaps
import Submission.DifferentialGeometry.Topology.SigmaCompactOpen
import Submission.DifferentialGeometry.Topology.Manifold.LocallyPathConnected

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Submission.Set _root_.Function _root_.TopologicalSpace _root_.Manifold _root_.Submission.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Geometry.Neck
open _root_.Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.ENNReal _root_.Topology _root_.Submission.DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry.Neck

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M] {ι : Type*} [Finite ι] {δ : ι → ℝ}
  (U : Opens M) (g : SmoothRiemannianMetric I U)
  (x₀ : ι → U) (order : ι → ℕ) (d : ∀ i, normalizedDatum g (x₀ i) (δ i) (order i))
  (f : ∀ i, bufferedCylinder (δ i) → M)
  (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
  (hdisj : Pairwise fun i j => Disjoint (range (f i)) (range (f j)))
  (hOriginal : ∀ i, f i = neckAmbientMap U (d i))
  (R : Set (ConnectedComponents (cutCore f)))
  (hRet : MapsTo (Subtype.val : cutCore f → M) (retainedCore f R) U)

private local instance _root_.Submission.DifferentialGeometry.Geometry.Neck.instMeasurableSpaceSubtypeMemOpens_differentialGeometry : MeasurableSpace U := borel U

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.instMeasurableSpaceSubtypeMemOpens_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.instMeasurableSpaceSubtypeMemOpens_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Geometry.Neck.instBorelSpaceSubtypeMemOpens_differentialGeometry : BorelSpace U := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.instBorelSpaceSubtypeMemOpens_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.instBorelSpaceSubtypeMemOpens_differentialGeometry target :: scope.openDecls } }

include hf hdisj hOriginal in
theorem retained_core_add_negative_bands_volume_le
    (hδ : ∀ i, δ i ≤ 1 / 4)
    (hneg : ∀ i, cuttingSphereComponent (fun j => (d j).precision_pos) f hf hdisj (i, _root_.Bool.false) ∉ R) :
    let : SecondCountableTopology H := I.secondCountableTopology
    let : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
    let : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
      (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I U.isOpen)
    let : LocallyPathConnectedSpace M :=
      DifferentialGeometry.Topology.Manifold.locallyPathConnectedSpace_of_modelWithCorners I
    riemannianVolumeMeasure I U g (_root_.Set.range (retainedCoreDomainMap f R U hRet)) +
      ∑' i : ι, ENNReal.ofReal (2 * Real.pi / δ i) *
        ENNReal.ofReal ((metricScalarAt g (x₀ i)) ^ (-3 / 2 : ℝ)) ≤
      riemannianVolumeMeasure I U g
        (_root_.Set.range (retainedCoreDomainMap f R U hRet) ∪
          ⋃ i : ι, (d i).map '' {q | q.val.2 ∈ _root_.Set.Icc (-(δ i)⁻¹) (-1 : ℝ)}) := by
  let : SecondCountableTopology H := I.secondCountableTopology
  let : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  let : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I U.isOpen)
  let : LocallyPathConnectedSpace M :=
    DifferentialGeometry.Topology.Manifold.locallyPathConnectedSpace_of_modelWithCorners I
  dsimp only
  let C := _root_.Set.range (retainedCoreDomainMap f R U hRet)
  let B := fun i : ι => (d i).map '' {q : bufferedCylinder (δ i) |
    q.val.2 ∈ _root_.Set.Icc (-(δ i)⁻¹) (-1 : ℝ)}
  let μ := riemannianVolumeMeasure I U g
  have hcompact (i : ι) : IsCompact (B i) :=
    isCompact_negative_closed_half_band_image (d i).precision_pos (d i).map (d i).smooth.continuous
  have hd : Pairwise fun i j => Disjoint (B i) (B j) := by
    intro i j hij
    apply disjoint_left.mpr
    rintro x ⟨q, _, hq⟩ ⟨r, _, hr⟩
    apply disjoint_left.mp (hdisj hij) (_root_.Set.mem_range_self q)
    refine ⟨r, ?_⟩
    rw [hOriginal i, hOriginal j]
    exact congrArg Subtype.val (hr.trans hq.symm)
  have hc (i : ι) : Disjoint C (B i) := by
    apply disjoint_left.mpr
    rintro x ⟨p, hp⟩ ⟨q, hq, heq⟩
    have hsep := negative_closed_half_band_image_disjoint_retainedCore
      (fun j => (d j).precision_pos) f hf hdisj R i (hneg i)
    apply disjoint_left.mp hsep ⟨q, hq, rfl⟩
    refine ⟨p.val, p.property, ?_⟩
    rw [hOriginal i]
    exact congrArg Subtype.val (hp.trans heq.symm)
  have hcu : Disjoint C (⋃ i, B i) := disjoint_iUnion_right.mpr hc
  have hbmeas : MeasurableSet (⋃ i, B i) := MeasurableSet.iUnion fun i => (hcompact i).measurableSet
  have hadd : μ (C ∪ ⋃ i, B i) = μ C + ∑' i, μ (B i) := by
    rw [_root_.MeasureTheory.measure_union hcu hbmeas, _root_.MeasureTheory.measure_iUnion hd (fun i => (hcompact i).measurableSet)]
  change μ C + _ ≤ μ (C ∪ ⋃ i, B i)
  rw [hadd]
  apply add_le_add_right
  apply ENNReal.tsum_le_tsum
  intro i
  exact (d i).negative_closed_band_volume_ge (hδ i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.retained_core_add_negative_bands_volume_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.retained_core_add_negative_bands_volume_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.retained_core_add_negative_bands_volume_le ``Submission.DifferentialGeometry.Geometry.Neck.retained_core_add_negative_bands_volume_le

include hf hdisj in
omit [SigmaCompactSpace M] in
theorem isCompact_retained_core_union_negative_bands [CompactSpace M] :
    let : LocallyPathConnectedSpace M :=
      DifferentialGeometry.Topology.Manifold.locallyPathConnectedSpace_of_modelWithCorners I
    IsCompact (_root_.Set.range (retainedCoreDomainMap f R U hRet) ∪
      ⋃ i : ι, (d i).map '' {q | q.val.2 ∈ _root_.Set.Icc (-(δ i)⁻¹) (-1 : ℝ)}) := by
  let : LocallyPathConnectedSpace M :=
    DifferentialGeometry.Topology.Manifold.locallyPathConnectedSpace_of_modelWithCorners I
  let : CompactSpace (retainedCore f R) := isCompact_iff_compactSpace.mp
    (isCompact_retained_discardedCore (fun i => (d i).precision_pos) f hf hdisj R).1
  have hc : Continuous (retainedCoreDomainMap f R U hRet) :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  apply (isCompact_range hc).union
  apply isCompact_iUnion
  intro i
  exact isCompact_negative_closed_half_band_image (d i).precision_pos (d i).map (d i).smooth.continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.isCompact_retained_core_union_negative_bands then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.isCompact_retained_core_union_negative_bands"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.isCompact_retained_core_union_negative_bands ``Submission.DifferentialGeometry.Geometry.Neck.isCompact_retained_core_union_negative_bands

end DifferentialGeometry.Geometry.Neck
