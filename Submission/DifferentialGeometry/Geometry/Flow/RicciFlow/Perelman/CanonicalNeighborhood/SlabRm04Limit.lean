import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SlabScalarLimit
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Preservation.Pinching.Evolution.Solution

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

private theorem slabRm04_formula
    (L : StaticTerminalLimit X depthBound)
    (g : ℝ → SmoothRiemannianMetric I3 L.space.M) (t : ℝ) (x : L.space.M)
    (V W Y Z : TangentSpace I3 x) :
    metricRm04At (I := I3) (g t) x (vec4 V W Y Z) =
      -ricciTensor (I := I3) (g t) x V Y * (g t).inner x W Z
        + ricciTensor (I := I3) (g t) x W Y * (g t).inner x V Z
        + ricciTensor (I := I3) (g t) x V Z * (g t).inner x W Y
        - ricciTensor (I := I3) (g t) x W Z * (g t).inner x V Y
        + (metricScalarAt (I := I3) (g t) x / 2) *
          ((g t).inner x V Y * (g t).inner x W Z -
            (g t).inner x W Y * (g t).inner x V Z) := by
  classical
  have hdim : Module.finrank ℝ (TangentSpace I3 x) = 3 := by
    change Module.finrank ℝ ThreeSpace = 3
    simp [ThreeSpace]
  have hb := exists_orthonormal_basis (I := I3) (g t) x
  rw [hdim] at hb
  obtain ⟨basis, hON⟩ := hb
  have horth : OrthonormalBasisAt (I := I3) (g t) x basis := hON
  have hdata := riemann_from_ricci_trace (I := I3)
    (flowOn (X.interval 0) g) (t := t) horth
  have h := rm04_kn_gform hdata V W Y Z
  dsimp only [flowOn, SolutionOn.ricciAt, SolutionFamily.ricciAt,
    SolutionOn.scalar, SolutionFamily.scalar, SolutionFamily.rm04] at h
  simp only [neg_apply, metricRm04_apply, metricRicciAt_apply_eq_ricciTensor] at h
  linear_combination h

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.slabRm04_formula
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.slabRm04_formula target :: scope.openDecls } }

private theorem slabRm04_slots
    (L : StaticTerminalLimit X depthBound)
    (g : ℝ → SmoothRiemannianMetric I3 L.space.M) (t : ℝ) (x : L.space.M)
    (v : Fin 4 → TangentSpace I3 x) :
    metricRm04At (I := I3) (g t) x v =
      metricRm04At (I := I3) (g t) x (vec4 (v 0) (v 1) (v 2) (v 3)) := by
  congr 1
  funext i
  fin_cases i <;> rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.slabRm04_slots
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.slabRm04_slots target :: scope.openDecls } }

theorem slabComparison_rm04Tensor_cont
    (L : StaticTerminalLimit X depthBound) {delta a b : ℝ}
    (hle : delta ≤ depthBound) {k : ℕ → ℕ} (hk : StrictMono k)
    {g : ℝ → SmoothRiemannianMetric I3 L.space.M}
    (hcomp : SlabComparison L delta k g) (hab : a ≤ b)
    (hsub : Set.Icc a b ⊆ Set.Icc (-delta) 0) :
    tensor0SFamilyContinuousOnSet (I := I3) 4 (Set.Icc a b)
      (fun t x => metricRm04At (I := I3) (g t) x) := by
  let : LocallyCompactSpace L.space.M := Manifold.locallyCompact_of_finiteDimensional I3
  apply tensor0SFamilyContinuousOnSet_of_chartBasisComp
    (N := fun x0 => (_root_.FiberBundle.trivializationAt ThreeSpace (TangentSpace I3) x0).baseSet)
    (hN := fun x0 => (Trivialization.open_baseSet _).mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt ThreeSpace (TangentSpace I3) x0))
  intro x0 idx
  let B := (_root_.FiberBundle.trivializationAt ThreeSpace (TangentSpace I3) x0).baseSet
  have hB : IsOpen B := (_root_.FiberBundle.trivializationAt ThreeSpace (TangentSpace I3) x0).open_baseSet
  let f : ℝ × L.space.M → ℝ := fun p => metricRm04At (I := I3) (g p.1) p.2
    (fun q => chartBasisVecFiber (I := I3) x0 (idx q) p.2)
  have hcompOn : ContinuousOn f (Set.Icc a b ×ˢ B) := by
    intro p hp
    obtain ⟨K, hK, hpK, hKB⟩ := exists_compact_subset hB hp.2
    let V (i : Fin 4) := chartBasisVecFiber (I := I3) x0 (idx i)
    have hV (i : Fin 4) := (chartBasisVec_contMDiffOn (I := I3) x0 (idx i)).mono hKB
    have hm (i j : Fin 4) :=
      slabComparison_metricPair_continuousOn L hle hk hcomp hab hsub hK (V i) (V j) (hV i) (hV j)
    have hr (i j : Fin 4) :=
      slabComparison_ricciPair_continuousOn L hle hk hcomp hab hsub hK (V i) (V j) (hV i) (hV j)
    have hs : ContinuousOn
        (fun q : ℝ × L.space.M => metricScalarAt (I := I3) (g q.1) q.2)
        (Set.Icc a b ×ˢ K) :=
      (slabComparison_scalar_continuousOn L hle hk hcomp hab hsub).mono
        (Set.prod_mono Set.Subset.rfl (Set.subset_univ K))
    have hc := (((((hr 0 2).neg.mul (hm 1 3)).add ((hr 1 2).mul (hm 0 3))).add
      ((hr 0 3).mul (hm 1 2))).sub ((hr 1 3).mul (hm 0 2))).add
      ((hs.div_const 2).mul (((hm 0 2).mul (hm 1 3)).sub ((hm 1 2).mul (hm 0 3))))
    have hcRm : ContinuousOn f (Set.Icc a b ×ˢ K) := by
      refine hc.congr (fun q _ => ?_)
      exact (slabRm04_slots L g q.1 q.2 _).trans
        (slabRm04_formula L g q.1 q.2 (V 0 q.2) (V 1 q.2) (V 2 q.2) (V 3 q.2))
    have hmem : Set.Icc a b ×ˢ K ∈ 𝓝[Set.Icc a b ×ˢ B] p := by
      have hn : (Set.univ ×ˢ interior K : Set (ℝ × L.space.M)) ∈ 𝓝 p :=
        prod_mem_nhds Filter.univ_mem (isOpen_interior.mem_nhds hpK)
      refine Filter.mem_of_superset (inter_mem_nhdsWithin _ hn) ?_
      rintro ⟨t, x⟩ ⟨⟨ht, _⟩, _, hx⟩
      exact ⟨ht, interior_subset hx⟩
    exact (hcRm.continuousWithinAt ⟨hp.1, interior_subset hpK⟩).mono_of_mem_nhdsWithin hmem
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
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.slabComparison_rm04Tensor_cont then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.slabComparison_rm04Tensor_cont"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.slabComparison_rm04Tensor_cont ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.slabComparison_rm04Tensor_cont

theorem IsSlabLimit.rm04Tensor_cont
    (L : StaticTerminalLimit X depthBound) {delta : ℝ} {hd : 0 < delta}
    (hle : delta ≤ depthBound) {g : ℝ → SmoothRiemannianMetric I3 L.space.M}
    (hlim : IsSlabLimit L delta hd g) :
    tensor0SFamilyContinuousOnSet (I := I3) 4 (Set.Icc (-delta) 0)
      (fun t x => metricRm04At (I := I3) (g t) x) := by
  obtain ⟨_, k, hk, hconv⟩ := hlim
  have hcomp : SlabComparison L delta k g := by
    intro K hK a b hab hsub order eps heps
    filter_upwards [hconv K hK a b hab hsub order eps heps] with i hi
    exact hi.2.2
  exact slabComparison_rm04Tensor_cont L hle hk hcomp (by linarith) Set.Subset.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.IsSlabLimit.rm04Tensor_cont then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.IsSlabLimit.rm04Tensor_cont"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.IsSlabLimit.rm04Tensor_cont ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.IsSlabLimit.rm04Tensor_cont

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
