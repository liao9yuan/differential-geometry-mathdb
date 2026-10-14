import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SlabRicciTensorLimit
import Submission.DifferentialGeometry.Geometry.Connection.ChartBridge.Metric.InverseGram

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
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Tensor.Coordinates
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology (ThreeSpace)
open _root_.Submission.DifferentialGeometry.Integral.Measure
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.BigOperators

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

variable {X : FlowSequence.{u}} {depthBound : ℝ}

theorem slabComparison_scalar_continuousOn
    (L : StaticTerminalLimit X depthBound) {delta a b : ℝ}
    (hle : delta ≤ depthBound) {k : ℕ → ℕ} (hk : StrictMono k)
    {g : ℝ → SmoothRiemannianMetric I3 L.space.M}
    (hcomp : SlabComparison L delta k g) (hab : a ≤ b)
    (hsub : Set.Icc a b ⊆ Set.Icc (-delta) 0) :
    ContinuousOn (fun p : ℝ × L.space.M => metricScalarAt (I := I3) (g p.1) p.2)
      (Set.Icc a b ×ˢ Set.univ) := by
  classical
  let : LocallyCompactSpace L.space.M := Manifold.locallyCompact_of_finiteDimensional I3
  intro p hp
  let B := (_root_.FiberBundle.trivializationAt ThreeSpace (TangentSpace I3) p.2).baseSet
  have hB : IsOpen B := (_root_.FiberBundle.trivializationAt ThreeSpace (TangentSpace I3) p.2).open_baseSet
  have hpB : p.2 ∈ B := _root_.FiberBundle.mem_baseSet_trivializationAt ThreeSpace (TangentSpace I3) p.2
  obtain ⟨K, hK, hpK, hKB⟩ := exists_compact_subset hB hpB
  let G (q : ℝ × L.space.M) := chartGramMatrix (I := I3) (g q.1) p.2 q.2
  have hGij (i j : Fin (Module.finrank ℝ ThreeSpace)) :
      ContinuousOn (fun q => G q i j) (Set.Icc a b ×ˢ K) := by
    exact slabComparison_metricPair_continuousOn L hle hk hcomp hab hsub hK
      (chartBasisVecFiber (I := I3) p.2 i) (chartBasisVecFiber (I := I3) p.2 j)
      ((chartBasisVec_contMDiffOn (I := I3) p.2 i).mono hKB)
      ((chartBasisVec_contMDiffOn (I := I3) p.2 j).mono hKB)
  have hG : ContinuousOn G (Set.Icc a b ×ˢ K) :=
    continuousOn_pi.mpr fun i => continuousOn_pi.mpr fun j => hGij i j
  have hGinv : ContinuousOn (fun q => (G q)⁻¹) (Set.Icc a b ×ˢ K) := by
    intro q hq
    have hdet : (G q).det ≠ 0 :=
      (chartGramMatrix_det_pos (I := I3) (g q.1) p.2 (hKB hq.2)).ne'
    have hRinv : ContinuousAt (Ring.inverse : ℝ → ℝ) (G q).det := by
      rw [Ring.inverse_eq_inv']
      exact _root_.ContinuousInv₀.continuousAt_inv₀ hdet
    exact Filter.Tendsto.comp (continuousAt_matrix_inv _ hRinv) (hG q hq)
  have hGinvij (i j : Fin (Module.finrank ℝ ThreeSpace)) :
      ContinuousOn (fun q => (G q)⁻¹ i j) (Set.Icc a b ×ˢ K) :=
    continuousOn_pi.mp (continuousOn_pi.mp hGinv i) j
  have hRicij (i j : Fin (Module.finrank ℝ ThreeSpace)) :
      ContinuousOn (fun q : ℝ × L.space.M => ricciTensor (I := I3) (g q.1) q.2
        (chartBasisVecFiber (I := I3) p.2 i q.2)
        (chartBasisVecFiber (I := I3) p.2 j q.2)) (Set.Icc a b ×ˢ K) :=
    slabComparison_ricciPair_continuousOn L hle hk hcomp hab hsub hK
      (chartBasisVecFiber (I := I3) p.2 i) (chartBasisVecFiber (I := I3) p.2 j)
      ((chartBasisVec_contMDiffOn (I := I3) p.2 i).mono hKB)
      ((chartBasisVec_contMDiffOn (I := I3) p.2 j).mono hKB)
  have hscalar : ContinuousOn
      (fun q : ℝ × L.space.M => metricScalarAt (I := I3) (g q.1) q.2)
      (Set.Icc a b ×ˢ K) := by
    have hsum : ContinuousOn
        (fun q : ℝ × L.space.M =>
          ∑ i : Fin (Module.finrank ℝ ThreeSpace),
            ∑ j : Fin (Module.finrank ℝ ThreeSpace),
              (G q)⁻¹ i j * ricciTensor (I := I3) (g q.1) q.2
                (chartBasisVecFiber (I := I3) p.2 i q.2)
                (chartBasisVecFiber (I := I3) p.2 j q.2)) (Set.Icc a b ×ˢ K) :=
      continuousOn_finsetSum Finset.univ fun i _ =>
        continuousOn_finsetSum Finset.univ fun j _ =>
        (hGinvij i j).mul (hRicij i j)
    refine hsum.congr (fun q hq => ?_)
    let β := chartBasisFamily (I := I3) p.2 (hKB hq.2)
    have hinv : MetricInverseInBasis (I := I3) (g q.1) q.2 β
        (fun i j => (G q)⁻¹ i j) := by
      simpa only [G, β, chartInvGramMatrix] using
        DifferentialGeometry.Geometry.Connection.chartInvGram_inverse
          (I := I3) (g q.1) p.2 (hKB hq.2)
    rw [metricScalarAt_def, metricTracePair0SAt_eq_sum_basis (I := I3) (g q.1)
      β (fun i j => (G q)⁻¹ i j) hinv]
    simp only [metricRicciAt_apply_eq_ricciTensor, β, chartBasisFamily_apply]
  have hmem : Set.Icc a b ×ˢ K ∈ 𝓝[Set.Icc a b ×ˢ Set.univ] p := by
    have hn : (Set.univ ×ˢ interior K : Set (ℝ × L.space.M)) ∈ 𝓝 p :=
      prod_mem_nhds Filter.univ_mem (isOpen_interior.mem_nhds hpK)
    refine Filter.mem_of_superset (inter_mem_nhdsWithin _ hn) ?_
    rintro ⟨t, x⟩ ⟨⟨ht, _⟩, _, hx⟩
    exact ⟨ht, interior_subset hx⟩
  exact (hscalar.continuousWithinAt ⟨hp.1, interior_subset hpK⟩).mono_of_mem_nhdsWithin hmem

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.slabComparison_scalar_continuousOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.slabComparison_scalar_continuousOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.slabComparison_scalar_continuousOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.slabComparison_scalar_continuousOn

theorem IsSlabLimit.scalar_continuousOn
    (L : StaticTerminalLimit X depthBound) {delta : ℝ} {hd : 0 < delta}
    (hle : delta ≤ depthBound) {g : ℝ → SmoothRiemannianMetric I3 L.space.M}
    (hlim : IsSlabLimit L delta hd g) :
    ContinuousOn (fun p : ℝ × L.space.M => metricScalarAt (I := I3) (g p.1) p.2)
      (Set.Icc (-delta) 0 ×ˢ Set.univ) := by
  obtain ⟨_, k, hk, hconv⟩ := hlim
  have hcomp : SlabComparison L delta k g := by
    intro K hK a b hab hsub order eps heps
    filter_upwards [hconv K hK a b hab hsub order eps heps] with i hi
    exact hi.2.2
  exact slabComparison_scalar_continuousOn L hle hk hcomp (by linarith) Set.Subset.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.IsSlabLimit.scalar_continuousOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.IsSlabLimit.scalar_continuousOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.IsSlabLimit.scalar_continuousOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.IsSlabLimit.scalar_continuousOn

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
