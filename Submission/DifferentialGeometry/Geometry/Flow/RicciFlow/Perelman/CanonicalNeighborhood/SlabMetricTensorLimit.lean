import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SlabMetricCoefficientLimit
import Submission.DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Tangent
import Submission.DifferentialGeometry.Geometry.Metric.Family.Continuity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open scoped _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Set _root_.Submission.Set _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Tensor.Coordinates
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology (ThreeSpace)
open _root_.Submission.DifferentialGeometry.Integral.Measure
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

variable {X : FlowSequence.{u}} {depthBound : ℝ}

private def mappedMetricQuadraticField (L : StaticTerminalLimit X depthBound) (k : ℕ → ℕ)
    (V : ∀ x : L.space.M, TangentSpace I3 x) (i : ℕ) (p : ℝ × L.space.M) : ℝ :=
  ((X.term (L.subseq (k i))).S.base.metric p.1).inner
    (L.maps.partialDiffeomorph (k i) p.2)
    (mfderiv I3 I3 (L.maps.partialDiffeomorph (k i)) p.2 (V p.2))
    (mfderiv I3 I3 (L.maps.partialDiffeomorph (k i)) p.2 (V p.2))

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.mappedMetricQuadraticField
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.mappedMetricQuadraticField target :: scope.openDecls } }

private theorem mappedMetricQuadraticField_continuousOn
    (L : StaticTerminalLimit X depthBound) {delta a b : ℝ}
    (hle : delta ≤ depthBound) (hsub : Set.Icc a b ⊆ Set.Icc (-delta) 0)
    (k : ℕ → ℕ) (i : ℕ) {K : Set L.space.M}
    (hsource : K ⊆ (L.maps.partialDiffeomorph (k i)).source)
    (V : ∀ x : L.space.M, TangentSpace I3 x)
    (hV : ContinuousOn (fun x => (TotalSpace.mk' ThreeSpace x (V x) : TangentBundle I3 L.space.M)) K) :
    ContinuousOn (mappedMetricQuadraticField L k V i) (Set.Icc a b ×ˢ K) := by
  rw [continuousOn_iff_continuous_domRestrict]
  let P := ↥(Set.Icc a b ×ˢ K)
  let F := L.maps.partialDiffeomorph (k i)
  have ht : Continuous (fun q : P => (q : ℝ × L.space.M).1) :=
    continuous_fst.comp continuous_subtype_val
  have hx : Continuous (fun q : P => (q : ℝ × L.space.M).2) :=
    continuous_snd.comp continuous_subtype_val
  have hb : Continuous (fun q : P => F (q : ℝ × L.space.M).2) :=
    F.contMDiffOn_toFun.continuousOn.comp_continuous hx (fun q => hsource q.2.2)
  have hv := DifferentialGeometry.PartialDiffeomorph.continuous_mfderiv_apply F (by simp)
    (fun q : P => (TotalSpace.mk' ThreeSpace (q : ℝ × L.space.M).2
      (V (q : ℝ × L.space.M).2) : TangentBundle I3 L.space.M))
    (hV.comp_continuous hx (fun q => q.2.2)) (fun q => hsource q.2.2)
  have hev := (X.term (L.subseq (k i))).isSolution.smoothMetric.metricTensor_cont.eval_continuous
    (P := P) (τ := fun q => (q : ℝ × L.space.M).1)
    (b := fun q => F (q : ℝ × L.space.M).2) ht
    (fun q => L.window_subset_carrier hle _ (hsub q.2.1)) hb
    (v := fun _ q => mfderiv I3 I3 F (q : ℝ × L.space.M).2 (V (q : ℝ × L.space.M).2))
    (fun _ => hv)
  refine hev.congr (fun q => ?_)
  exact metricTensorField_apply (I := I3)
    ((X.term (L.subseq (k i))).S.base.metric (q : ℝ × L.space.M).1)
    (F (q : ℝ × L.space.M).2)
    (fun _ => mfderiv I3 I3 F (q : ℝ × L.space.M).2 (V (q : ℝ × L.space.M).2))

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.mappedMetricQuadraticField_continuousOn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.mappedMetricQuadraticField_continuousOn target :: scope.openDecls } }

private theorem slabComparison_quadraticField_uniform
    (L : StaticTerminalLimit X depthBound) {delta a b : ℝ}
    (hle : delta ≤ depthBound) {k : ℕ → ℕ} (hk : StrictMono k)
    {g : ℝ → SmoothRiemannianMetric I3 L.space.M}
    (hcomp : SlabComparison L delta k g) (hab : a ≤ b)
    (hsub : Set.Icc a b ⊆ Set.Icc (-delta) 0)
    {K : Set L.space.M} (hK : IsCompact K)
    (V : ∀ x : L.space.M, TangentSpace I3 x)
    (hV : ContinuousOn (fun x => (TotalSpace.mk' ThreeSpace x (V x) : TangentBundle I3 L.space.M)) K) :
    TendstoUniformlyOn (mappedMetricQuadraticField L k V)
      (fun p => (g p.1).inner p.2 (V p.2) (V p.2)) _root_.Filter.atTop (Set.Icc a b ×ˢ K) := by
  obtain ⟨m, hm⟩ := L.maps.source_subset hK
  have hsrc : ∀ᶠ i in _root_.Filter.atTop, K ⊆ (L.maps.partialDiffeomorph (k i)).source := by
    filter_upwards [Filter.eventually_ge_atTop m] with i hi
    exact hm (k i) (hi.trans (StrictMono.le_apply hk))
  obtain ⟨i, ⟨hi, ⟨P⟩⟩⟩ :=
    (hsrc.and (hcomp K hK a b hab hsub 0 (1 / 2) (by norm_num))).exists
  obtain ⟨C0, hC0⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn
    (mappedMetricQuadraticField_continuousOn L hle hsub k i hi V hV)
  let C : ℝ := 2 * (|C0| + 1)
  have hCpos : 0 < C := by dsimp only [C]; positivity
  have hC (p : ℝ × L.space.M) (hp : p ∈ Set.Icc a b ×ˢ K) :
      (g p.1).inner p.2 (V p.2) (V p.2) ≤ C := by
    have heq := P.pullback_eq p.1 p.2 hp.2 (fun _ => V p.2)
    change P.pullback p.1 p.2 (fun _ => V p.2) = mappedMetricQuadraticField L k V i p at heq
    have hlo := (P.equivalence p.1 hp.1 p.2 hp.2 (V p.2)).1
    rw [heq] at hlo
    have hupper : mappedMetricQuadraticField L k V i p ≤ C0 :=
      (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hC0 p hp)
    dsimp only [C]
    nlinarith [le_abs_self C0]
  rw [Metric.tendstoUniformlyOn_iff]
  intro eta heta
  let eps : ℝ := eta / (2 * C)
  have heps : 0 < eps := by dsimp only [eps]; positivity
  have hmul : eps * (2 * C) = eta := div_mul_cancel₀ _ (by positivity)
  filter_upwards [hcomp K hK a b hab hsub 0 eps heps] with j hj
  obtain ⟨Q⟩ := hj
  intro p hp
  have heq := Q.pullback_eq p.1 p.2 hp.2 (fun _ => V p.2)
  change Q.pullback p.1 p.2 (fun _ => V p.2) = mappedMetricQuadraticField L k V j p at heq
  obtain ⟨hlo, hhi⟩ := Q.equivalence p.1 hp.1 p.2 hp.2 (V p.2)
  rw [heq] at hlo hhi
  have hbound := mul_le_mul_of_nonneg_left (hC p hp) heps.le
  rw [Real.dist_eq]
  apply abs_lt.mpr
  constructor <;> nlinarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.slabComparison_quadraticField_uniform
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.slabComparison_quadraticField_uniform target :: scope.openDecls } }

private theorem slabMetricTensor_polarization
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : ∀ v w, B v w = B w v) (v w : V) :
    B v w = (B (v + w) (v + w) - B v v - B w w) / 2 := by
  simp only [map_add, add_apply, hB w v]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.slabMetricTensor_polarization
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.slabMetricTensor_polarization target :: scope.openDecls } }

theorem slabComparison_metricPair_continuousOn
    (L : StaticTerminalLimit X depthBound) {delta a b : ℝ}
    (hle : delta ≤ depthBound) {k : ℕ → ℕ} (hk : StrictMono k)
    {g : ℝ → SmoothRiemannianMetric I3 L.space.M}
    (hcomp : SlabComparison L delta k g) (hab : a ≤ b)
    (hsub : Set.Icc a b ⊆ Set.Icc (-delta) 0)
    {K : Set L.space.M} (hK : IsCompact K)
    (V W : ∀ x : L.space.M, TangentSpace I3 x)
    (hV : ContMDiffOn I3 (I3.prod 𝓘(ℝ, ThreeSpace)) ∞
      (fun x => (TotalSpace.mk' ThreeSpace x (V x) : TangentBundle I3 L.space.M)) K)
    (hW : ContMDiffOn I3 (I3.prod 𝓘(ℝ, ThreeSpace)) ∞
      (fun x => (TotalSpace.mk' ThreeSpace x (W x) : TangentBundle I3 L.space.M)) K) :
    ContinuousOn (fun p : ℝ × L.space.M => (g p.1).inner p.2 (V p.2) (W p.2))
      (Set.Icc a b ×ˢ K) := by
  obtain ⟨m, hm⟩ := L.maps.source_subset hK
  have hquad (Y : ∀ x : L.space.M, TangentSpace I3 x)
      (hY : ContinuousOn
        (fun x => (TotalSpace.mk' ThreeSpace x (Y x) : TangentBundle I3 L.space.M)) K) :
      ContinuousOn (fun p : ℝ × L.space.M => (g p.1).inner p.2 (Y p.2) (Y p.2))
        (Set.Icc a b ×ˢ K) := by
    have hcont : ∀ᶠ i in _root_.Filter.atTop,
        ContinuousOn (mappedMetricQuadraticField L k Y i) (Set.Icc a b ×ˢ K) := by
      filter_upwards [Filter.eventually_ge_atTop m] with i hi
      exact mappedMetricQuadraticField_continuousOn L hle hsub k i
        (hm (k i) (hi.trans (StrictMono.le_apply hk))) Y hY
    exact (slabComparison_quadraticField_uniform L hle hk hcomp hab hsub hK Y hY).continuousOn
      hcont.frequently
  have hsum := hquad (fun x => V x + W x) (hV.add_section hW).continuousOn
  exact ((hsum.sub (hquad V hV.continuousOn)).sub (hquad W hW.continuousOn)).div_const 2 |>.congr
    (fun p _ => slabMetricTensor_polarization ((g p.1).inner p.2) ((g p.1).symm p.2)
      (V p.2) (W p.2))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.slabComparison_metricPair_continuousOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.slabComparison_metricPair_continuousOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.slabComparison_metricPair_continuousOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.slabComparison_metricPair_continuousOn

theorem slabComparison_metricTensor_cont
    (L : StaticTerminalLimit X depthBound) {delta a b : ℝ}
    (hle : delta ≤ depthBound) {k : ℕ → ℕ} (hk : StrictMono k)
    {g : ℝ → SmoothRiemannianMetric I3 L.space.M}
    (hcomp : SlabComparison L delta k g) (hab : a ≤ b)
    (hsub : Set.Icc a b ⊆ Set.Icc (-delta) 0) :
    tensor0SFamilyContinuousOnSet (I := I3) 2 (Set.Icc a b)
      (fun t x => metricTensorField (I := I3) (g t) x) := by
  let : LocallyCompactSpace L.space.M := Manifold.locallyCompact_of_finiteDimensional I3
  apply metricTensorCont_of_chartGram (I := I3) g
  intro x0 i j
  let B := (_root_.FiberBundle.trivializationAt ThreeSpace (TangentSpace I3) x0).baseSet
  have hB : IsOpen B := (_root_.FiberBundle.trivializationAt ThreeSpace (TangentSpace I3) x0).open_baseSet
  have hgram : ContinuousOn
      (fun p : ℝ × L.space.M => chartGramMatrix (I := I3) (g p.1) x0 p.2 i j)
      (Set.Icc a b ×ˢ B) := by
    intro p hp
    obtain ⟨K, hK, hpK, hKB⟩ := exists_compact_subset hB hp.2
    have hi := (chartBasisVec_contMDiffOn (I := I3) x0 i).mono hKB
    have hj := (chartBasisVec_contMDiffOn (I := I3) x0 j).mono hKB
    have hc := slabComparison_metricPair_continuousOn L hle hk hcomp hab hsub hK
      (chartBasisVecFiber (I := I3) x0 i) (chartBasisVecFiber (I := I3) x0 j) hi hj
    have hcGram : ContinuousOn
        (fun q : ℝ × L.space.M => chartGramMatrix (I := I3) (g q.1) x0 q.2 i j)
        (Set.Icc a b ×ˢ K) := by
      exact hc
    have hmem : Set.Icc a b ×ˢ K ∈ 𝓝[Set.Icc a b ×ˢ B] p := by
      have hn : (Set.univ ×ˢ interior K : Set (ℝ × L.space.M)) ∈ 𝓝 p :=
        prod_mem_nhds Filter.univ_mem (isOpen_interior.mem_nhds hpK)
      refine Filter.mem_of_superset (inter_mem_nhdsWithin _ hn) ?_
      rintro ⟨t, x⟩ ⟨⟨ht, _⟩, _, hx⟩
      exact ⟨ht, interior_subset hx⟩
    exact (hcGram.continuousWithinAt ⟨hp.1, interior_subset hpK⟩).mono_of_mem_nhdsWithin hmem
  let restrictTime : ↥(Set.Icc a b) × L.space.M → ℝ × L.space.M := fun q => (q.1, q.2)
  have hrestrict : Continuous restrictTime :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  have hrestrictOn : ContinuousOn restrictTime
      {q : ↥(Set.Icc a b) × L.space.M | q.2 ∈ B} := hrestrict.continuousOn
  have hmap : _root_.Set.MapsTo restrictTime
      {q : ↥(Set.Icc a b) × L.space.M | q.2 ∈ B} (Set.Icc a b ×ˢ B) :=
    fun q hq => ⟨q.1.2, hq⟩
  have hfinal := hgram.comp hrestrictOn hmap
  exact hfinal

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.slabComparison_metricTensor_cont then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.slabComparison_metricTensor_cont"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.slabComparison_metricTensor_cont ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.slabComparison_metricTensor_cont

theorem IsSlabLimit.metricTensor_cont
    (L : StaticTerminalLimit X depthBound) {delta : ℝ} {hd : 0 < delta}
    (hle : delta ≤ depthBound) {g : ℝ → SmoothRiemannianMetric I3 L.space.M}
    (hlim : IsSlabLimit L delta hd g) :
    tensor0SFamilyContinuousOnSet (I := I3) 2 (Set.Icc (-delta) 0)
      (fun t x => metricTensorField (I := I3) (g t) x) := by
  obtain ⟨_, k, hk, hconv⟩ := hlim
  have hcomp : SlabComparison L delta k g := by
    intro K hK a b hab hsub order eps heps
    filter_upwards [hconv K hK a b hab hsub order eps heps] with i hi
    exact hi.2.2
  exact slabComparison_metricTensor_cont L hle hk hcomp (by linarith) Set.Subset.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.IsSlabLimit.metricTensor_cont then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.IsSlabLimit.metricTensor_cont"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.IsSlabLimit.metricTensor_cont ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.IsSlabLimit.metricTensor_cont

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
