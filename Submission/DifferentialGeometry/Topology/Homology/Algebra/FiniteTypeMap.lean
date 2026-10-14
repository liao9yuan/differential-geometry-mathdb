import Submission.DifferentialGeometry.Topology.Homology.Algebra.FiniteType
import Mathlib.Algebra.Homology.QuasiIso

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
open _root_.CategoryTheory _root_.CategoryTheory.Limits
noncomputable section
universe u v
namespace DifferentialGeometry.HomologicalComplex
variable {k : Type u} [Field k]
  {K L : ChainComplex (ModuleCat.{v} k) ℕ} (φ : K ⟶ L) [QuasiIso φ]

include φ

theorem finiteHomologyType_iff_of_quasiIso : finiteHomologyType K ↔ finiteHomologyType L := by
  have transport {A B : ChainComplex (ModuleCat.{v} k) ℕ}
      (e : ∀ n, A.homology n ≅ B.homology n) (h : finiteHomologyType A) :
      finiteHomologyType B := by
    constructor
    · intro n
      have := h.1 n
      exact (e n).toLinearEquiv.finiteDimensional
    · obtain ⟨N, hN⟩ := h.2
      exact ⟨N, fun n hn => (hN n hn).of_iso (e n).symm⟩
  exact ⟨transport (fun n => isoOfQuasiIsoAt φ n), transport (fun n => (isoOfQuasiIsoAt φ n).symm)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.HomologicalComplex.finiteHomologyType_iff_of_quasiIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.HomologicalComplex.finiteHomologyType_iff_of_quasiIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.HomologicalComplex.finiteHomologyType_iff_of_quasiIso ``Submission.DifferentialGeometry.HomologicalComplex.finiteHomologyType_iff_of_quasiIso

theorem homologyEulerChar_eq_of_quasiIso : K.homologyEulerChar = L.homologyEulerChar := by
  apply finsum_congr
  intro n
  rw [(isoOfQuasiIsoAt φ n).toLinearEquiv.finrank_eq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.HomologicalComplex.homologyEulerChar_eq_of_quasiIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.HomologicalComplex.homologyEulerChar_eq_of_quasiIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.HomologicalComplex.homologyEulerChar_eq_of_quasiIso ``Submission.DifferentialGeometry.HomologicalComplex.homologyEulerChar_eq_of_quasiIso

end DifferentialGeometry.HomologicalComplex
