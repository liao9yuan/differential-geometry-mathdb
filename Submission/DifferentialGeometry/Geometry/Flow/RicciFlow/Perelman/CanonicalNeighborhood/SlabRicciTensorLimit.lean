import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SlabMetricTensorLimit
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SlabRicciCoefficientLimit

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

private def mappedRicciQuadraticField (L : StaticTerminalLimit X depthBound) (k : ℕ → ℕ)
    (V : ∀ x : L.space.M, TangentSpace I3 x) (i : ℕ) (p : ℝ × L.space.M) : ℝ :=
  mappedRicciCoefficient L k p.2 (V p.2) (V p.2) i p.1

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.mappedRicciQuadraticField
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.mappedRicciQuadraticField target :: scope.openDecls } }

private theorem slabRicciTensor_eval_slots
    {N : Type*} [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold I3 ∞ N]
    [T2Space N] (g : SmoothRiemannianMetric I3 N) (x : N)
    (slots : Fin 2 → TangentSpace I3 x) :
    metricRicciAt (I := I3) g x slots = ricciTensor (I := I3) g x (slots 0) (slots 1) := by
  have hv : slots = vec2 (slots 0) (slots 1) := by funext i; fin_cases i <;> rfl
  rw [hv, metricRicciAt_apply_eq_ricciTensor]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.slabRicciTensor_eval_slots
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.slabRicciTensor_eval_slots target :: scope.openDecls } }

private theorem mappedRicciQuadraticField_continuousOn
    (L : StaticTerminalLimit X depthBound) {delta a b : ℝ}
    (hle : delta ≤ depthBound) (hsub : Set.Icc a b ⊆ Set.Icc (-delta) 0)
    (k : ℕ → ℕ) (i : ℕ) {K : Set L.space.M}
    (hsource : K ⊆ (L.maps.partialDiffeomorph (k i)).source)
    (V : ∀ x : L.space.M, TangentSpace I3 x)
    (hV : ContinuousOn (fun x => (TotalSpace.mk' ThreeSpace x (V x) : TangentBundle I3 L.space.M)) K) :
    ContinuousOn (mappedRicciQuadraticField L k V i) (Set.Icc a b ×ˢ K) := by
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
  have hev := (X.term (L.subseq (k i))).isSolution.ricciCont.eval_continuous
    (P := P) (τ := fun q => (q : ℝ × L.space.M).1)
    (b := fun q => F (q : ℝ × L.space.M).2) ht
    (fun q => L.window_subset_carrier hle _ (hsub q.2.1)) hb
    (v := fun _ q => mfderiv I3 I3 F (q : ℝ × L.space.M).2 (V (q : ℝ × L.space.M).2))
    (fun _ => hv)
  refine hev.congr (fun q => ?_)
  simp only [SolutionOn.ricci]
  exact slabRicciTensor_eval_slots _ _ _

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.mappedRicciQuadraticField_continuousOn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.mappedRicciQuadraticField_continuousOn target :: scope.openDecls } }

private theorem slabComparison_ricciQuadraticField_uniform
    (L : StaticTerminalLimit X depthBound) {delta a b : ℝ}
    (hle : delta ≤ depthBound) {k : ℕ → ℕ} (hk : StrictMono k)
    {g : ℝ → SmoothRiemannianMetric I3 L.space.M}
    (hcomp : SlabComparison L delta k g) (hab : a ≤ b)
    (hsub : Set.Icc a b ⊆ Set.Icc (-delta) 0)
    {K : Set L.space.M} (hK : IsCompact K)
    (V : ∀ x : L.space.M, TangentSpace I3 x)
    (hV : ContMDiffOn I3 (I3.prod 𝓘(ℝ, ThreeSpace)) ∞
      (fun x => (TotalSpace.mk' ThreeSpace x (V x) : TangentBundle I3 L.space.M)) K) :
    TendstoUniformlyOn (mappedRicciQuadraticField L k V)
      (fun p => ricciTensor (I := I3) (g p.1) p.2 (V p.2) (V p.2))
      atTop (Set.Icc a b ×ˢ K) := by
  obtain ⟨C0, hC0⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn
    (slabComparison_metricPair_continuousOn L hle hk hcomp hab hsub hK V V hV hV)
  let C : ℝ := |C0| + 1
  have hCpos : 0 < C := by dsimp only [C]; positivity
  have hC (p : ℝ × L.space.M) (hp : p ∈ Set.Icc a b ×ˢ K) :
      (g p.1).inner p.2 (V p.2) (V p.2) ≤ C := by
    have hc := hC0 p hp
    rw [Real.norm_eq_abs] at hc
    exact (le_abs_self _).trans (hc.trans (by dsimp only [C]; linarith [le_abs_self C0]))
  obtain ⟨n, hn⟩ := L.maps.source_subset hK
  let U := sourceOpen (L.maps.partialDiffeomorph n)
  have hKU : K ⊆ (U : Set L.space.M) := hn n le_rfl
  let K0 : Set L.space.M := closure (L.maps.partialDiffeomorph n).source
  have hK0 : IsCompact K0 := L.precompact n
  have hUK0 : (U : Set L.space.M) ⊆ K0 := subset_closure
  obtain ⟨m, hm⟩ := L.maps.source_subset hK0
  let d : ℝ := Module.finrank ℝ ThreeSpace
  let A : ℝ := d * 432 * C
  have hd : 0 ≤ d := Nat.cast_nonneg _
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  rw [Metric.tendstoUniformlyOn_iff]
  intro eta heta
  let eps : ℝ := _root_.Min.min 1 (_root_.Min.min (1 / (2 * (d + 1))) (eta / (A + 1)))
  have heps : 0 < eps := by dsimp only [eps]; positivity
  have heps1 : eps ≤ 1 := min_le_left _ _
  have hsmall : d * eps ≤ 1 / 2 := by
    have ht : eps ≤ 1 / (2 * (d + 1)) :=
      (min_le_right _ _).trans (min_le_left _ _)
    have hm := (le_div_iff₀ (by positivity : 0 < 2 * (d + 1))).mp ht
    nlinarith [heps.le]
  have hAe : A * eps < eta := by
    have ht : eps ≤ eta / (A + 1) :=
      (min_le_right _ _).trans (min_le_right _ _)
    have hm := (le_div_iff₀ (by positivity : 0 < A + 1)).mp ht
    nlinarith
  filter_upwards [hcomp K0 hK0 a b hab hsub 2 eps heps,
    Filter.eventually_ge_atTop m] with i hi hmi
  obtain ⟨P⟩ := hi
  have hU : (U : Set L.space.M) ⊆ (L.maps.partialDiffeomorph (k i)).source :=
    hUK0.trans (hm (k i) (hmi.trans (StrictMono.le_apply hk)))
  intro p hp
  have hb := P.ricciQuadratic_sub_le U hU hUK0 le_rfl heps.le heps1 hsmall hp.1
    ⟨p.2, hKU hp.2⟩ (V p.2)
  change |mappedRicciQuadraticField L k V i p -
      ricciTensor (I := I3) (g p.1) p.2 (V p.2) (V p.2)| ≤
    d * (432 * eps) * (g p.1).inner p.2 (V p.2) (V p.2) at hb
  have hscale : d * (432 * eps) * (g p.1).inner p.2 (V p.2) (V p.2) ≤ A * eps := by
    calc
      _ ≤ d * (432 * eps) * C := mul_le_mul_of_nonneg_left (hC p hp) (by positivity)
      _ = _ := by dsimp only [A]; ring
  rw [dist_comm, Real.dist_eq]
  exact hb.trans_lt (hscale.trans_lt hAe)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.slabComparison_ricciQuadraticField_uniform
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.slabComparison_ricciQuadraticField_uniform target :: scope.openDecls } }

private theorem slabRicciTensor_polarization
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : ∀ v w, B v w = B w v) (v w : V) :
    B v w = (B (v + w) (v + w) - B v v - B w w) / 2 := by
  simp only [map_add, add_apply, hB w v]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.slabRicciTensor_polarization
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.slabRicciTensor_polarization target :: scope.openDecls } }

theorem slabComparison_ricciPair_continuousOn
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
    ContinuousOn (fun p : ℝ × L.space.M => ricciTensor (I := I3) (g p.1) p.2 (V p.2) (W p.2))
      (Set.Icc a b ×ˢ K) := by
  obtain ⟨m, hm⟩ := L.maps.source_subset hK
  have hquad (Y : ∀ x : L.space.M, TangentSpace I3 x)
      (hY : ContMDiffOn I3 (I3.prod 𝓘(ℝ, ThreeSpace)) ∞
        (fun x => (TotalSpace.mk' ThreeSpace x (Y x) : TangentBundle I3 L.space.M)) K) :
      ContinuousOn (fun p : ℝ × L.space.M => ricciTensor (I := I3) (g p.1) p.2 (Y p.2) (Y p.2))
        (Set.Icc a b ×ˢ K) := by
    have hcont : ∀ᶠ i in _root_.Filter.atTop,
        ContinuousOn (mappedRicciQuadraticField L k Y i) (Set.Icc a b ×ˢ K) := by
      filter_upwards [Filter.eventually_ge_atTop m] with i hi
      exact mappedRicciQuadraticField_continuousOn L hle hsub k i
        (hm (k i) (hi.trans (StrictMono.le_apply hk))) Y hY.continuousOn
    exact (slabComparison_ricciQuadraticField_uniform L hle hk hcomp hab hsub hK Y hY).continuousOn
      hcont.frequently
  have hsum := hquad (fun x => V x + W x) (hV.add_section hW)
  exact ((hsum.sub (hquad V hV)).sub (hquad W hW)).div_const 2 |>.congr
    (fun p _ => slabRicciTensor_polarization (ricciTensor (I := I3) (g p.1) p.2)
      (ricciTensor_symm _ _) (V p.2) (W p.2))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.slabComparison_ricciPair_continuousOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.slabComparison_ricciPair_continuousOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.slabComparison_ricciPair_continuousOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.slabComparison_ricciPair_continuousOn

theorem slabComparison_ricciTensor_cont
    (L : StaticTerminalLimit X depthBound) {delta a b : ℝ}
    (hle : delta ≤ depthBound) {k : ℕ → ℕ} (hk : StrictMono k)
    {g : ℝ → SmoothRiemannianMetric I3 L.space.M}
    (hcomp : SlabComparison L delta k g) (hab : a ≤ b)
    (hsub : Set.Icc a b ⊆ Set.Icc (-delta) 0) :
    tensor0SFamilyContinuousOnSet (I := I3) 2 (Set.Icc a b)
      (fun t x => metricRicciAt (I := I3) (g t) x) := by
  let : LocallyCompactSpace L.space.M := Manifold.locallyCompact_of_finiteDimensional I3
  apply tensor0SFamilyContinuousOnSet_of_chartBasisComp
    (N := fun x0 => (_root_.FiberBundle.trivializationAt ThreeSpace (TangentSpace I3) x0).baseSet)
    (hN := fun x0 => (Trivialization.open_baseSet _).mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt ThreeSpace (TangentSpace I3) x0))
  intro x0 idx
  let B := (_root_.FiberBundle.trivializationAt ThreeSpace (TangentSpace I3) x0).baseSet
  have hB : IsOpen B := (_root_.FiberBundle.trivializationAt ThreeSpace (TangentSpace I3) x0).open_baseSet
  let f : ℝ × L.space.M → ℝ := fun p => metricRicciAt (I := I3) (g p.1) p.2
    (fun q => chartBasisVecFiber (I := I3) x0 (idx q) p.2)
  have hcompOn : ContinuousOn f (Set.Icc a b ×ˢ B) := by
    intro p hp
    obtain ⟨K, hK, hpK, hKB⟩ := exists_compact_subset hB hp.2
    have hi := (chartBasisVec_contMDiffOn (I := I3) x0 (idx 0)).mono hKB
    have hj := (chartBasisVec_contMDiffOn (I := I3) x0 (idx 1)).mono hKB
    have hc := slabComparison_ricciPair_continuousOn L hle hk hcomp hab hsub hK
      (chartBasisVecFiber (I := I3) x0 (idx 0)) (chartBasisVecFiber (I := I3) x0 (idx 1)) hi hj
    have hcRic : ContinuousOn f (Set.Icc a b ×ˢ K) := by
      refine hc.congr (fun q _ => ?_)
      exact slabRicciTensor_eval_slots _ _ _
    have hmem : Set.Icc a b ×ˢ K ∈ 𝓝[Set.Icc a b ×ˢ B] p := by
      have hn : (Set.univ ×ˢ interior K : Set (ℝ × L.space.M)) ∈ 𝓝 p :=
        prod_mem_nhds Filter.univ_mem (isOpen_interior.mem_nhds hpK)
      refine Filter.mem_of_superset (inter_mem_nhdsWithin _ hn) ?_
      rintro ⟨t, x⟩ ⟨⟨ht, _⟩, _, hx⟩
      exact ⟨ht, interior_subset hx⟩
    exact (hcRic.continuousWithinAt ⟨hp.1, interior_subset hpK⟩).mono_of_mem_nhdsWithin hmem
  let restrictTime : ↥(Set.Icc a b) × L.space.M → ℝ × L.space.M := fun q => (q.1, q.2)
  have hrestrict : Continuous restrictTime :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  have hrestrictOn : ContinuousOn restrictTime
      {q : ↥(Set.Icc a b) × L.space.M | q.2 ∈ B} := hrestrict.continuousOn
  have hmap : _root_.Set.MapsTo restrictTime
      {q : ↥(Set.Icc a b) × L.space.M | q.2 ∈ B} (Set.Icc a b ×ˢ B) :=
    fun q hq => ⟨q.1.2, hq⟩
  have hfinal := hcompOn.comp hrestrictOn hmap
  exact hfinal

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.slabComparison_ricciTensor_cont then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.slabComparison_ricciTensor_cont"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.slabComparison_ricciTensor_cont ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.slabComparison_ricciTensor_cont

theorem IsSlabLimit.ricciTensor_cont
    (L : StaticTerminalLimit X depthBound) {delta : ℝ} {hd : 0 < delta}
    (hle : delta ≤ depthBound) {g : ℝ → SmoothRiemannianMetric I3 L.space.M}
    (hlim : IsSlabLimit L delta hd g) :
    tensor0SFamilyContinuousOnSet (I := I3) 2 (Set.Icc (-delta) 0)
      (fun t x => metricRicciAt (I := I3) (g t) x) := by
  obtain ⟨_, k, hk, hconv⟩ := hlim
  have hcomp : SlabComparison L delta k g := by
    intro K hK a b hab hsub order eps heps
    filter_upwards [hconv K hK a b hab hsub order eps heps] with i hi
    exact hi.2.2
  exact slabComparison_ricciTensor_cont L hle hk hcomp (by linarith) Set.Subset.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.IsSlabLimit.ricciTensor_cont then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.IsSlabLimit.ricciTensor_cont"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.IsSlabLimit.ricciTensor_cont ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.IsSlabLimit.ricciTensor_cont

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
