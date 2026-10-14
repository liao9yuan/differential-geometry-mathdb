import Submission.DifferentialGeometry.Topology.Simplex.AttachmentRelativeHomology
import Submission.DifferentialGeometry.Topology.Simplex.BoundaryEuler
import Submission.DifferentialGeometry.Topology.Homology.Algebra.FiniteTypeMap

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.CategoryTheory _root_.CategoryTheory.Limits
namespace DifferentialGeometry.Simplex.Attachment
variable (k : Type) [Field k] {n : ℕ} {X P : TopCat.{0}}
  {g : TopCat.of (boundary (Fin (n + 1))) ⟶ X}
  {r : TopCat.of (stdSimplex ℝ (Fin (n + 1))) ⟶ P} {b : X ⟶ P}
  (h : IsPushout boundaryι g r b)
include h

private theorem finite_euler_of_attachment
    (hX : DifferentialGeometry.Homology.finiteHomologyType k X) :
    DifferentialGeometry.Homology.finiteHomologyType k P ∧
      DifferentialGeometry.Homology.eulerChar k P = DifferentialGeometry.Homology.eulerChar k X + (-1 : ℤ)^n := by
  let D := TopCat.of (stdSimplex ℝ (Fin (n + 1)))
  let B := boundary (Fin (n + 1))
  let s : Set P := Set.range b
  let R := ModuleCat.of k k
  have hB := finiteHomologyType_boundary k n
  let : ContractibleSpace D := (convex_stdSimplex ℝ (Fin (n + 1))).contractibleSpace
    ⟨stdSimplex.barycenter, stdSimplex.barycenter.prop⟩
  have hD : DifferentialGeometry.Homology.finiteHomologyType k D :=
    DifferentialGeometry.Homology.finiteHomologyType_of_contractible k
  let e : X ≃ₜ TopCat.of s := (DifferentialGeometry.TopCat.Pushout.isClosedEmbedding_inr h
    isClosedEmbedding_boundaryι).isEmbedding.toHomeomorph
  have hs : DifferentialGeometry.Homology.finiteHomologyType k (TopCat.of s) := (DifferentialGeometry.Homology.finiteHomologyType_iff_of_homeomorph k e).mp hX
  have hCell := DifferentialGeometry.Homology.finiteHomologyType_relativeChainComplex D B k hB hD
  let q := cellRelativeChainMap R h
  have : QuasiIso q := quasiIso_cellRelativeChainMap R h
  have hRel : DifferentialGeometry.HomologicalComplex.finiteHomologyType
      (DifferentialGeometry.Homology.relativeChainComplex P s R) :=
    (DifferentialGeometry.HomologicalComplex.finiteHomologyType_iff_of_quasiIso q).mp hCell
  have hP : DifferentialGeometry.Homology.finiteHomologyType k P :=
    DifferentialGeometry.HomologicalComplex.finiteHomologyType_middle
      (DifferentialGeometry.Homology.relativeShortComplex P s R)
      (DifferentialGeometry.Homology.relativeShortExact P s R) hs hRel
  have he := DifferentialGeometry.HomologicalComplex.homologyEulerChar_eq_of_quasiIso q
  change DifferentialGeometry.Homology.relativeEulerChar D B k = DifferentialGeometry.Homology.relativeEulerChar P s k at he
  rw [DifferentialGeometry.Homology.relativeEulerChar_eq_sub D B k hB hD,
    DifferentialGeometry.Homology.relativeEulerChar_eq_sub P s k hs hP] at he
  have hDχ : DifferentialGeometry.Homology.eulerChar k D = 1 := DifferentialGeometry.Homology.eulerChar_of_contractible k
  have hsχ := DifferentialGeometry.Homology.eulerChar_eq_of_homeomorph k e
  have hBχ := eulerChar_boundary k n
  exact ⟨hP, by change DifferentialGeometry.Homology.eulerChar k (TopCat.of B) = _ at hBχ; omega⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Simplex.Attachment.finite_euler_of_attachment
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Simplex.Attachment.finite_euler_of_attachment target :: scope.openDecls } }


theorem finiteHomologyType_of_attachment (hX : DifferentialGeometry.Homology.finiteHomologyType k X) :
    DifferentialGeometry.Homology.finiteHomologyType k P :=
  (finite_euler_of_attachment k h hX).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.Attachment.finiteHomologyType_of_attachment then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.Attachment.finiteHomologyType_of_attachment"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.Attachment.finiteHomologyType_of_attachment ``Submission.DifferentialGeometry.Simplex.Attachment.finiteHomologyType_of_attachment


theorem eulerChar_attachment (hX : DifferentialGeometry.Homology.finiteHomologyType k X) :
    DifferentialGeometry.Homology.eulerChar k P = DifferentialGeometry.Homology.eulerChar k X + (-1 : ℤ)^n :=
  (finite_euler_of_attachment k h hX).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.Attachment.eulerChar_attachment then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.Attachment.eulerChar_attachment"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.Attachment.eulerChar_attachment ``Submission.DifferentialGeometry.Simplex.Attachment.eulerChar_attachment

end DifferentialGeometry.Simplex.Attachment
