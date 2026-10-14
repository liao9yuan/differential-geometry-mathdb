import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homotopy.PlaneTriangle
import Mathlib.Topology.Algebra.Module.FiniteDimension

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-! # The actual three edges of the original planar triangle -/

noncomputable section

open _root_.Set _root_.Function
open scoped _root_.Topology

namespace DifferentialGeometry.Topology

/-- A point in the triangle is on its frontier precisely when one of its
three affine defining inequalities is an equality. -/
theorem planeTriangle_mem_frontier_iff (z : ℂ) :
    z ∈ frontier planeTriangle ↔ z ∈ planeTriangle ∧
      (z.re = 0 ∨ z.im = 0 ∨ z.re + z.im = 1) := by
  constructor
  · intro hz
    exact ⟨isClosed_planeTriangle.frontier_subset hz, planeTriangle_frontier_edges hz⟩
  · rintro ⟨hz, he⟩
    rw [frontier, isClosed_planeTriangle.closure_eq]
    refine ⟨hz, ?_⟩
    intro hi
    rcases he with hr | hi0 | hsum
    · have ho : IsOpenMap Complex.re := Complex.reLm.isOpenMap_of_finiteDimensional
        (fun r => ⟨(r : ℂ), by simp⟩)
      have hm : z ∈ interior (Complex.re ⁻¹' _root_.Set.Ici 0) := interior_mono (fun _ h => h.1) hi
      have hc := ho.interior_preimage_subset_preimage_interior hm
      simp only [_root_.Set.mem_preimage, interior_Ici, _root_.Set.mem_Ioi, hr, lt_self_iff_false] at hc
    · have ho : IsOpenMap Complex.im := Complex.imLm.isOpenMap_of_finiteDimensional
        (fun r => ⟨(r : ℂ) * Complex.I, by simp⟩)
      have hm : z ∈ interior (Complex.im ⁻¹' _root_.Set.Ici 0) := interior_mono (fun _ h => h.2.1) hi
      have hc := ho.interior_preimage_subset_preimage_interior hm
      simp only [_root_.Set.mem_preimage, interior_Ici, _root_.Set.mem_Ioi, hi0, lt_self_iff_false] at hc
    · have ho : IsOpenMap (fun z : ℂ => z.re + z.im) :=
        (Complex.reLm + Complex.imLm).isOpenMap_of_finiteDimensional
          (fun r => ⟨(r : ℂ), by simp⟩)
      have hm : z ∈ interior ((fun z : ℂ => z.re + z.im) ⁻¹' _root_.Set.Iic 1) :=
        interior_mono (fun _ h => h.2.2) hi
      have hc := ho.interior_preimage_subset_preimage_interior hm
      simp only [_root_.Set.mem_preimage, interior_Iic, _root_.Set.mem_Iio, hsum, lt_self_iff_false] at hc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.planeTriangle_mem_frontier_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.planeTriangle_mem_frontier_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.planeTriangle_mem_frontier_iff ``Submission.DifferentialGeometry.Topology.planeTriangle_mem_frontier_iff

/-- The edge coordinates are ordered by their missing barycentric vertex:
edge 12, edge 02, and edge 01. -/
def planeTriangleEdgeValue (i : Fin 3) (s : unitInterval) : ℂ :=
  ![((1 - s.val : ℝ) : ℂ) + (s.val : ℂ) * Complex.I,
    (s.val : ℂ) * Complex.I, (s.val : ℂ)] i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.planeTriangleEdgeValue then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.planeTriangleEdgeValue"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.planeTriangleEdgeValue ``Submission.DifferentialGeometry.Topology.planeTriangleEdgeValue

/-- Each original edge parametrization lies on the same actual frontier. -/
theorem planeTriangleEdgeValue_mem (i : Fin 3) (s : unitInterval) :
    planeTriangleEdgeValue i s ∈ frontier planeTriangle := by
  rw [planeTriangle_mem_frontier_iff]
  fin_cases i
  · simpa [planeTriangleEdgeValue, planeTriangle] using And.intro s.property.2 s.property.1
  · simpa [planeTriangleEdgeValue, planeTriangle] using And.intro s.property.1 s.property.2
  · simpa [planeTriangleEdgeValue, planeTriangle] using And.intro s.property.1 s.property.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.planeTriangleEdgeValue_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.planeTriangleEdgeValue_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.planeTriangleEdgeValue_mem ``Submission.DifferentialGeometry.Topology.planeTriangleEdgeValue_mem

/-- The actual closed-interval parametrizations of the three edges. -/
def planeTriangleEdge (i : Fin 3) : C(unitInterval, frontier planeTriangle) :=
  ⟨fun s => ⟨planeTriangleEdgeValue i s, planeTriangleEdgeValue_mem i s⟩, by
    apply Continuous.subtype_mk
    fin_cases i
    · exact (Complex.continuous_ofReal.comp (continuous_const.sub continuous_subtype_val)).add
        ((Complex.continuous_ofReal.comp continuous_subtype_val).mul continuous_const)
    · exact (Complex.continuous_ofReal.comp continuous_subtype_val).mul continuous_const
    · exact Complex.continuous_ofReal.comp continuous_subtype_val⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.planeTriangleEdge then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.planeTriangleEdge"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.planeTriangleEdge ``Submission.DifferentialGeometry.Topology.planeTriangleEdge

end DifferentialGeometry.Topology
