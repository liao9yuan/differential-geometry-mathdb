import Submission.DifferentialGeometry.Geometry.Exponential.MinimizingDomain.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set
open scoped _root_.ContDiff _root_.ENNReal _root_.Manifold _root_.Submission.Manifold _root_.Topology

namespace DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space (TangentBundle I M)]
  [RiemannianBundle (fun x : M => TangentSpace I x)]

private local instance tangentSpaceNormedAddCommGroup
    (x : M) : NormedAddCommGroup (TangentSpace I x) :=
  Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
    (E := fun y : M => TangentSpace I y) x

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.Exponential.tangentSpaceNormedAddCommGroup
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.Exponential.tangentSpaceNormedAddCommGroup target :: scope.openDecls } }

private local instance tangentSpaceInnerProductSpace
    (x : M) : InnerProductSpace ℝ (TangentSpace I x) :=
  Bundle.instInnerProductSpaceReal (E := fun y : M => TangentSpace I y) x

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.Exponential.tangentSpaceInnerProductSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.Exponential.tangentSpaceInnerProductSpace target :: scope.openDecls } }

private local instance tangentSpaceNormedSpace
    (x : M) : NormedSpace ℝ (TangentSpace I x) := inferInstance

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.Exponential.tangentSpaceNormedSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.Exponential.tangentSpaceNormedSpace target :: scope.openDecls } }

variable [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

theorem isClosed_preimage_minimizingDomain
    (g : SmoothRiemannianMetric I M) (p : M) :
    IsClosed (Subtype.val ⁻¹' minimizingDomain (I := I) g p :
      Set (show Set E from expDomain (I := I) g p)) := by
  let : T2Space M := gauss_t2Space_base I
  have hleft : Continuous (fun v : E => ENNReal.ofReal
      (Real.sqrt (g.inner p (show TangentSpace I p from v)
        (show TangentSpace I p from v)))) := by
    apply ENNReal.continuous_ofReal.comp
    apply Real.continuous_sqrt.comp
    with_unfolding_all exact continuous_gInner_self (I := I) g p
  have hexp : Continuous (fun v : (show Set E from expDomain (I := I) g p) =>
      expMap (I := I) g p (show TangentSpace I p from (v : E))) :=
    (contMDiffOn_expMap (I := I) g p).continuousOn.domRestrict
  have hdist : Continuous (fun q : M => _root_.Manifold.riemannianEDist I p q) :=
    (continuous_riemannianEDist_to (I := I) p).congr
      (fun _ => Manifold.riemannianEDist_comm)
  exact isClosed_eq (hleft.comp continuous_subtype_val) (hdist.comp hexp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Exponential.isClosed_preimage_minimizingDomain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Exponential.isClosed_preimage_minimizingDomain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Exponential.isClosed_preimage_minimizingDomain ``Submission.DifferentialGeometry.Geometry.Riemannian.Exponential.isClosed_preimage_minimizingDomain

theorem isCompact_minimizingDomain_inter
    (g : SmoothRiemannianMetric I M) (p : M) {K : Set E}
    (hK : IsCompact K) (hKdom : K ⊆ expDomain (I := I) g p) :
    IsCompact (minimizingDomain (I := I) g p ∩ K) := by
  let f : K → (show Set E from expDomain (I := I) g p) :=
    fun v => ⟨(v : E), hKdom v.property⟩
  have hf : Continuous f := continuous_subtype_val.subtype_mk _
  have hclosed : IsClosed {v : K | (v : E) ∈ minimizingDomain (I := I) g p} :=
    (isClosed_preimage_minimizingDomain (I := I) g p).preimage hf
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hcpt := hclosed.isCompact.image continuous_subtype_val
  convert hcpt using 1
  ext v
  constructor
  · intro hv
    exact ⟨⟨v, hv.2⟩, hv.1, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨hw, w.property⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Exponential.isCompact_minimizingDomain_inter then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Exponential.isCompact_minimizingDomain_inter"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Exponential.isCompact_minimizingDomain_inter ``Submission.DifferentialGeometry.Geometry.Riemannian.Exponential.isCompact_minimizingDomain_inter

theorem isSigmaCompact_minimizingDomain
    (g : SmoothRiemannianMetric I M) (p : M) :
    IsSigmaCompact (minimizingDomain (I := I) g p) := by
  have hopen : IsOpen (show Set E from expDomain (I := I) g p) :=
    isOpen_expDomain (I := I) g p
  let : LocallyCompactSpace (show Set E from expDomain (I := I) g p) :=
    hopen.locallyCompactSpace
  have hsig : IsSigmaCompact (Subtype.val ⁻¹' minimizingDomain (I := I) g p :
      Set (show Set E from expDomain (I := I) g p)) :=
    isSigmaCompact_univ.of_isClosed_subset
      (isClosed_preimage_minimizingDomain (I := I) g p) (_root_.Set.subset_univ _)
  have himage := hsig.image continuous_subtype_val
  convert himage using 1
  ext v
  constructor
  · intro hv
    exact ⟨⟨v, minimizingDomain_subset_expDomain (I := I) g p hv⟩, hv, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact hw

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Exponential.isSigmaCompact_minimizingDomain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Exponential.isSigmaCompact_minimizingDomain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Exponential.isSigmaCompact_minimizingDomain ``Submission.DifferentialGeometry.Geometry.Riemannian.Exponential.isSigmaCompact_minimizingDomain

variable [MeasurableSpace E] [BorelSpace E]

theorem measurableSet_minimizingDomain
    (g : SmoothRiemannianMetric I M) (p : M) :
    MeasurableSet (minimizingDomain (I := I) g p) := by
  have hmeas := (isClosed_preimage_minimizingDomain (I := I) g p).measurableSet
  have hUopen : IsOpen (show Set E from expDomain (I := I) g p) :=
    isOpen_expDomain (I := I) g p
  have hU : MeasurableSet (show Set E from expDomain (I := I) g p) :=
    hUopen.measurableSet
  have himage : MeasurableSet (((↑) : (show Set E from expDomain (I := I) g p) → E) ''
      (Subtype.val ⁻¹' minimizingDomain (I := I) g p)) := hU.subtype_image hmeas
  convert himage using 1
  ext v
  constructor
  · intro hv
    exact ⟨⟨v, minimizingDomain_subset_expDomain (I := I) g p hv⟩, hv, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact hw

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Exponential.measurableSet_minimizingDomain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Exponential.measurableSet_minimizingDomain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Exponential.measurableSet_minimizingDomain ``Submission.DifferentialGeometry.Geometry.Riemannian.Exponential.measurableSet_minimizingDomain

theorem measurableSet_extendibleMinimizingDomain
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) :
    MeasurableSet (extendibleMinimizingDomain (I := I) g p) := by
  let Q : Set ℚ := {q | (1 : ℝ) < (q : ℝ)}
  let A : ℚ → Set E := fun q =>
    (fun v : E => (q : ℝ) • v) ⁻¹' minimizingDomain (I := I) g p
  have hA (q : ℚ) : MeasurableSet (A q) :=
    (measurableSet_minimizingDomain (I := I) g p).preimage
      (_root_.ContinuousConstSMul.continuous_const_smul (q : ℝ)).measurable
  have heq : extendibleMinimizingDomain (I := I) g p = ⋃ q ∈ Q, A q := by
    ext v
    constructor
    · rintro ⟨c, hc, hcv⟩
      obtain ⟨q : ℚ, hq1, hqc⟩ := exists_rat_btwn hc
      have hqpos : 0 < (q : ℝ) := zero_lt_one.trans hq1
      refine mem_iUnion₂.mpr ⟨q, hq1, ?_⟩
      apply extendibleMinimizingDomain_subset_minimizingDomain (I := I) g hEnorm p
      refine ⟨c / (q : ℝ), (one_lt_div hqpos).mpr hqc, ?_⟩
      simpa only [smul_smul, div_mul_cancel₀ _ hqpos.ne'] using hcv
    · intro hv
      obtain ⟨q, hq, hqv⟩ := mem_iUnion₂.mp hv
      exact ⟨(q : ℝ), hq, hqv⟩
  rw [heq]
  exact MeasurableSet.biUnion (Set.to_countable Q) fun q _ => hA q

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Exponential.measurableSet_extendibleMinimizingDomain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Exponential.measurableSet_extendibleMinimizingDomain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Exponential.measurableSet_extendibleMinimizingDomain ``Submission.DifferentialGeometry.Geometry.Riemannian.Exponential.measurableSet_extendibleMinimizingDomain

end DifferentialGeometry.Geometry.Riemannian.Exponential
