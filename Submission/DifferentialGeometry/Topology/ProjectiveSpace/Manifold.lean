import Submission.DifferentialGeometry.Topology.ProjectiveSpace.Real
import Submission.DifferentialGeometry.Topology.Manifold.Quotient
import Submission.DifferentialGeometry.Topology.Covering.SimplyConnected
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Analysis.Normed.Module.Connected

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {n : Nat} [Fact (Module.finrank Real E = n + 1)]

instance realProjectiveSpaceAntipodalGroupContMDiffConstSMul :
    ContMDiffConstSMul (𝓡 n) ∞ (realProjectiveSpaceAntipodalGroup E)
      (Metric.sphere (0 : E) 1) where
  contMDiff_const_smul gamma := by
    change ContMDiff (𝓡 n) (𝓡 n) ∞
      (gamma.1 : Metric.sphere (0 : E) 1 → Metric.sphere (0 : E) 1)
    rcases realProjectiveSpaceAntipodalGroup_eq_one_or_generator gamma with h | h
    · rw [h]
      exact contMDiff_id
    · rw [h]
      exact contMDiff_neg_sphere

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.realProjectiveSpaceAntipodalGroupContMDiffConstSMul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.realProjectiveSpaceAntipodalGroupContMDiffConstSMul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.realProjectiveSpaceAntipodalGroupContMDiffConstSMul ``Submission.DifferentialGeometry.realProjectiveSpaceAntipodalGroupContMDiffConstSMul

theorem realProjectiveSpaceQuotientMap_isLocalDiffeomorph :
    IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞
      (realProjectiveSpaceQuotientMap (E := E)) :=
  MulAction.isLocalDiffeomorph_quotientMk_of_properlyDiscontinuousSMul (𝓡 n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.realProjectiveSpaceQuotientMap_isLocalDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.realProjectiveSpaceQuotientMap_isLocalDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.realProjectiveSpaceQuotientMap_isLocalDiffeomorph ``Submission.DifferentialGeometry.realProjectiveSpaceQuotientMap_isLocalDiffeomorph

theorem not_simplyConnectedSpace_realProjectiveSpace (hn : 1 ≤ n) :
    ¬ SimplyConnectedSpace (RealProjectiveSpace E) := by
  intro h
  let _ : SimplyConnectedSpace (RealProjectiveSpace E) := h
  have hdim : 1 < Module.finrank Real E := by
    rw [show Module.finrank Real E = n + 1 from Fact.out]
    omega
  let _ : Nontrivial E :=
    Module.nontrivial_of_finrank_pos (lt_trans Nat.zero_lt_one hdim)
  let _ : LocallyPathConnectedSpace (RealProjectiveSpace E) :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace Real (Fin n)) _
  let _ : PreconnectedSpace (Metric.sphere (0 : E) 1) :=
    Subtype.preconnectedSpace
      (isPreconnected_sphere (Module.one_lt_rank_of_one_lt_finrank hdim) 0 1)
  obtain ⟨x, hx⟩ := NormedSpace.sphere_nonempty (E := E).2 zero_le_one
  let y : Metric.sphere (0 : E) 1 := ⟨x, hx⟩
  let _ : Nonempty (Metric.sphere (0 : E) 1) := ⟨y⟩
  have hinj := (realProjectiveSpaceQuotientMap_isCoveringMap (E := E)).bijective_sc.1
  have heq : realProjectiveSpaceQuotientMap
      (realProjectiveSpaceAntipodalHomeomorph E y) =
        realProjectiveSpaceQuotientMap y := by
    apply realProjectiveSpaceQuotientMap_eq_iff.mpr
    exact Or.inr (realProjectiveSpaceAntipodalHomeomorph_coe y)
  exact realProjectiveSpaceAntipodalHomeomorph_fixed_point_free y (hinj heq)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.not_simplyConnectedSpace_realProjectiveSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.not_simplyConnectedSpace_realProjectiveSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.not_simplyConnectedSpace_realProjectiveSpace ``Submission.DifferentialGeometry.not_simplyConnectedSpace_realProjectiveSpace

theorem not_simplyConnectedSpace_realProjectivePlane :
    ¬ SimplyConnectedSpace RealProjectivePlane := by
  let _ : Fact (Module.finrank Real (EuclideanSpace Real (Fin 3)) = 2 + 1) :=
    ⟨by simp⟩
  exact not_simplyConnectedSpace_realProjectiveSpace (E := EuclideanSpace Real (Fin 3))
    (n := 2) (by decide)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.not_simplyConnectedSpace_realProjectivePlane then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.not_simplyConnectedSpace_realProjectivePlane"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.not_simplyConnectedSpace_realProjectivePlane ``Submission.DifferentialGeometry.not_simplyConnectedSpace_realProjectivePlane

end DifferentialGeometry
