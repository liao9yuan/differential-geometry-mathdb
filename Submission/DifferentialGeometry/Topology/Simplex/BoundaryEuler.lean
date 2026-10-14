import Submission.DifferentialGeometry.Topology.SimplicialSet.RealizationEulerCharacteristic
import Submission.DifferentialGeometry.Topology.SimplicialSet.BoundaryHomeomorphism
import Submission.DifferentialGeometry.Topology.SimplicialComplex.Simplex

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Simplicial
namespace DifferentialGeometry.Simplex
open _root_.Submission.DifferentialGeometry.Topology.SimplicialComplex

private def boundaryRealizationCoordinates (n : ℕ) :
    _root_.SSet.toTop.obj (_root_.SSet.boundary n : _root_.SSet) ≃ₜ boundary (Fin (n + 1)) :=
  (DifferentialGeometry.SSet.boundaryRealizationHomeomorph n).trans (Homeomorph.ulift.sets rfl)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Simplex.boundaryRealizationCoordinates
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Simplex.boundaryRealizationCoordinates target :: scope.openDecls } }


theorem finiteHomologyType_boundary (k : Type) [Field k] (n : ℕ) :
    DifferentialGeometry.Homology.finiteHomologyType k (TopCat.of (boundary (Fin (n + 1)))) :=
  (DifferentialGeometry.Homology.finiteHomologyType_iff_of_homeomorph k (boundaryRealizationCoordinates n)).mp
    (DifferentialGeometry.SSet.finiteHomologyType_realization k (_root_.SSet.boundary n : _root_.SSet))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.finiteHomologyType_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.finiteHomologyType_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.finiteHomologyType_boundary ``Submission.DifferentialGeometry.Simplex.finiteHomologyType_boundary

private def boundaryNondegenerateEquiv {n d : ℕ} (hd : d < n) :
    (_root_.SSet.boundary n : _root_.SSet).nonDegenerate d ≃
      (Δ[n] : _root_.SSet).nonDegenerate d where
  toFun x := ⟨x.val.val, ((_root_.SSet.boundary n).mem_nonDegenerate_iff x.val).mp x.prop⟩
  invFun x := ⟨⟨x.val, by rw [_root_.SSet.boundary_obj_eq_univ d n hd]; trivial⟩,
    ((_root_.SSet.boundary n).mem_nonDegenerate_iff _).mpr x.prop⟩
  left_inv _ := rfl
  right_inv _ := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Simplex.boundaryNondegenerateEquiv
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Simplex.boundaryNondegenerateEquiv target :: scope.openDecls } }

private theorem boundary_count {n d : ℕ} (hd : d < n) :
    Nat.card ((_root_.SSet.boundary n : _root_.SSet).nonDegenerate d) =
      (facesOfCard (boundarySimplex (Finset.univ : Finset (Fin (n + 1)))) (d + 1)).card := by
  rw [Nat.card_congr (boundaryNondegenerateEquiv hd),
    Nat.card_congr _root_.SSet.stdSimplex.nonDegenerateEquiv', Nat.card_eq_fintype_card]
  rw [card_facesOfCard_boundarySimplex_of_lt _ (d + 1) (by omega) (by simpa)]
  simp only [Finset.card_univ, Fintype.card_fin]
  simp

run_cmd do
  let target := ``Submission.DifferentialGeometry.Simplex.boundary_count
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Simplex.boundary_count target :: scope.openDecls } }


theorem eulerChar_boundary (k : Type) [Field k] (n : ℕ) :
    DifferentialGeometry.Homology.eulerChar k (TopCat.of (boundary (Fin (n + 1)))) = 1 - (-1 : ℤ)^n := by
  rw [← DifferentialGeometry.Homology.eulerChar_eq_of_homeomorph k (boundaryRealizationCoordinates n),
    DifferentialGeometry.SSet.eulerChar_realization_eq_sum_card_nonDegenerate k _ n]
  have hd : ∀ s ∈ boundarySimplex (Finset.univ : Finset (Fin (n + 1))), s.card ≤ n := by
    intro s hs
    have := Finset.card_lt_card hs.2
    simp only [Finset.card_univ, Fintype.card_fin] at this
    omega
  have he := faceEulerChar_eq_sum (boundarySimplex (Finset.univ : Finset (Fin (n + 1)))) n hd
  have hχ := faceEulerChar_boundarySimplex (Finset.univ_nonempty (α := Fin (n + 1)))
  rw [he] at hχ
  simp only [Finset.card_univ, Fintype.card_fin, pow_succ] at hχ
  rw [Finset.sum_range_succ', facesOfCard_zero, Finset.card_empty, Nat.cast_zero, _root_.MulZeroClass.mul_zero, add_zero] at hχ
  convert hχ using 1
  · apply Finset.sum_congr rfl
    intro d hd
    rw [boundary_count (Finset.mem_range.mp hd), pow_succ]
    ring
  · ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.eulerChar_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.eulerChar_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.eulerChar_boundary ``Submission.DifferentialGeometry.Simplex.eulerChar_boundary

end DifferentialGeometry.Simplex
