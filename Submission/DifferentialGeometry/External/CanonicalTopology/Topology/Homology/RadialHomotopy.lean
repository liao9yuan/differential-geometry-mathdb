import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.Homotopy
import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
import Mathlib.Analysis.Convex.Contractible

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-! # The original punctured normed space and its same unit sphere -/

noncomputable section

open _root_.CategoryTheory _root_.ContinuousMap _root_.Set _root_.Metric
open scoped _root_.Topology

universe u

namespace DifferentialGeometry.Topology

/-- Projection from a positive-radius product is a homotopy equivalence
whose section uses radius EXACTLY one. The same radius is interpolated
linearly, remaining positive throughout the homotopy. -/
def positiveRadiusProdHomotopyEquiv (X : Type u) [TopologicalSpace X] :
    (X × _root_.Set.Ioi (0 : ℝ)) ≃ₕ X where
  toFun := ⟨Prod.fst, continuous_fst⟩
  invFun := ⟨fun x => (x, (⟨1, by norm_num⟩ : _root_.Set.Ioi (0 : ℝ))), by fun_prop⟩
  left_inv := by
    refine ⟨⟨⟨fun p => (p.2.1, ⟨(1 - p.1.val) • (1 : ℝ) + p.1.val • p.2.2.val, ?_⟩), ?_⟩, ?_, ?_⟩⟩
    · exact (show Convex ℝ (_root_.Set.Ioi (0 : ℝ)) from convex_Ioi 0) (by norm_num) p.2.2.property
        (sub_nonneg.mpr p.1.property.2) p.1.property.1 (sub_add_cancel 1 _)
    · fun_prop
    · intro x
      refine Prod.ext ?_ ?_
      · rfl
      · apply Subtype.ext
        simp
    · intro x
      refine Prod.ext ?_ ?_
      · rfl
      · apply Subtype.ext
        simp
  right_inv := Homotopic.refl _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.positiveRadiusProdHomotopyEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.positiveRadiusProdHomotopyEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.positiveRadiusProdHomotopyEquiv ``Submission.DifferentialGeometry.Topology.positiveRadiusProdHomotopyEquiv

variable (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The SAME actual radial normalization retracts the original punctured
space onto its unit sphere, with the unit-radius inclusion as inverse. -/
def puncturedSpaceSphereHomotopyEquiv : ({0}ᶜ : Set E) ≃ₕ _root_.Metric.sphere (0 : E) 1 :=
  (homeomorphUnitSphereProd E).toHomotopyEquiv.trans
    (positiveRadiusProdHomotopyEquiv (_root_.Metric.sphere (0 : E) 1))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.puncturedSpaceSphereHomotopyEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.puncturedSpaceSphereHomotopyEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.puncturedSpaceSphereHomotopyEquiv ``Submission.DifferentialGeometry.Topology.puncturedSpaceSphereHomotopyEquiv

/-- The forward map is the actual radial normalization of the original point. -/
theorem puncturedSpaceSphereHomotopyEquiv_apply (x : ({0}ᶜ : Set E)) :
    ((puncturedSpaceSphereHomotopyEquiv E).toFun x : E) = ‖x.val‖⁻¹ • x.val :=
  homeomorphUnitSphereProd_apply_fst_coe E x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.puncturedSpaceSphereHomotopyEquiv_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.puncturedSpaceSphereHomotopyEquiv_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.puncturedSpaceSphereHomotopyEquiv_apply ``Submission.DifferentialGeometry.Topology.puncturedSpaceSphereHomotopyEquiv_apply

/-- The inverse is the SAME original sphere inclusion into the punctured space. -/
theorem puncturedSpaceSphereHomotopyEquiv_inv_apply (x : _root_.Metric.sphere (0 : E) 1) :
    ((puncturedSpaceSphereHomotopyEquiv E).invFun x : E) = x.val := by
  change (1 : ℝ) • x.val = x.val
  exact one_smul ℝ x.val

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.puncturedSpaceSphereHomotopyEquiv_inv_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.puncturedSpaceSphereHomotopyEquiv_inv_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.puncturedSpaceSphereHomotopyEquiv_inv_apply ``Submission.DifferentialGeometry.Topology.puncturedSpaceSphereHomotopyEquiv_inv_apply

/-- The resulting isomorphism concerns the ORIGINAL singular homology
groups, and is induced by the same radial normalization. -/
def integralPuncturedSpaceSphereHomologyEquiv (n : ℕ) :
    integralSingularHomology n ({0}ᶜ : Set E) ≃ₗ[ℤ] integralSingularHomology n (_root_.Metric.sphere (0 : E) 1) :=
  integralSingularHomologyHomotopyEquiv n (puncturedSpaceSphereHomotopyEquiv E)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralPuncturedSpaceSphereHomologyEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralPuncturedSpaceSphereHomologyEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralPuncturedSpaceSphereHomologyEquiv ``Submission.DifferentialGeometry.Topology.integralPuncturedSpaceSphereHomologyEquiv

end DifferentialGeometry.Topology
