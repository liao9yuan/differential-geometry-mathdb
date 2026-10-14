import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SpherePuncture
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-! # The actual unit sphere of a one-dimensional real inner product space -/

noncomputable section

open _root_.Set _root_.Metric _root_.Module

universe u

namespace DifferentialGeometry.Topology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- In dimension one, the actual unit sphere consists precisely of the
specified unit vector and its antipode. -/
theorem oneDimUnitSphere_eq_or_antipode (hd : _root_.Module.finrank ℝ E = 1)
    (v x : _root_.Metric.sphere (0 : E) 1) : x = v ∨ x = -v := by
  let : FiniteDimensional ℝ E := Module.finite_of_finrank_eq_succ hd
  have hv : (v : E) ≠ 0 := by
    intro h
    have hn := norm_eq_of_mem_sphere v
    rw [h, norm_zero] at hn
    norm_num at hn
  have hspan : ℝ ∙ (v : E) = ⊤ := Submodule.eq_top_of_finrank_eq
    ((finrank_span_singleton hv).trans hd.symm)
  have hx : (x : E) ∈ ℝ ∙ (v : E) := hspan.symm ▸ Submodule.mem_top
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hx
  have hn : |r| = 1 := by
    have h := congrArg _root_.Norm.norm hr
    simpa [norm_smul, norm_eq_of_mem_sphere v, norm_eq_of_mem_sphere x, Real.norm_eq_abs] using h
  rcases abs_eq (by norm_num : (0 : ℝ) ≤ 1) |>.mp hn with h | h
  · left
    apply Subtype.ext
    simpa [h] using hr.symm
  · right
    apply Subtype.ext
    simpa [h] using hr.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.oneDimUnitSphere_eq_or_antipode then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.oneDimUnitSphere_eq_or_antipode"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.oneDimUnitSphere_eq_or_antipode ``Submission.DifferentialGeometry.Topology.oneDimUnitSphere_eq_or_antipode

/-- A concrete two-point parametrization of that original sphere. -/
def oneDimUnitSphereEquivBool (hd : _root_.Module.finrank ℝ E = 1) (v : _root_.Metric.sphere (0 : E) 1) :
    sphere (0 : E) 1 ≃ Bool := (Equiv.ofBijective (fun b : Bool => if b then -v else v) (by
  constructor
  · intro a b h
    cases a <;> cases b <;> simp_all [unitSphere_ne_antipode v, (unitSphere_ne_antipode v).symm]
  · intro x
    rcases oneDimUnitSphere_eq_or_antipode hd v x with h | h
    · exact ⟨false, h.symm⟩
    · exact ⟨true, h.symm⟩)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.oneDimUnitSphereEquivBool then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.oneDimUnitSphereEquivBool"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.oneDimUnitSphereEquivBool ``Submission.DifferentialGeometry.Topology.oneDimUnitSphereEquivBool

/-- This actual sphere is finite; its inherited Hausdorff topology is therefore discrete. -/
theorem oneDimUnitSphere_finite (hd : _root_.Module.finrank ℝ E = 1) (v : _root_.Metric.sphere (0 : E) 1) :
    Finite (_root_.Metric.sphere (0 : E) 1) := Finite.of_equiv Bool (oneDimUnitSphereEquivBool hd v).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.oneDimUnitSphere_finite then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.oneDimUnitSphere_finite"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.oneDimUnitSphere_finite ``Submission.DifferentialGeometry.Topology.oneDimUnitSphere_finite

end DifferentialGeometry.Topology
