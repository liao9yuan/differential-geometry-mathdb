import Submission.DifferentialGeometry.Topology.Simplex.SupportFace
import Submission.DifferentialGeometry.Topology.Simplex.Reindex
import Submission.DifferentialGeometry.Topology.Simplex.MapInjectivity
import Mathlib.Data.Finset.Sort

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.Simplex

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem reindexHomeomorph_eq_map (e : ι ≃ κ) (p : stdSimplex ℝ ι) :
    reindexHomeomorph e p = stdSimplex.map e p := by
  ext j
  change p.val (e.symm j) = (stdSimplex.map e p).val j
  have h := stdSimplex.map_apply_of_injective e.injective p (e.symm j)
  change p (e.symm j) = (stdSimplex.map e p) j
  rw [e.apply_symm_apply] at h
  exact h.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.reindexHomeomorph_eq_map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.reindexHomeomorph_eq_map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.reindexHomeomorph_eq_map ``Submission.DifferentialGeometry.Simplex.reindexHomeomorph_eq_map

variable [LinearOrder ι]

def orderedSupportFaceHomeomorph (s : Finset ι) {m : ℕ} (hs : s.card = m) :
    stdSimplex ℝ (Fin m) ≃ₜ supportFace s :=
  (reindexHomeomorph (s.orderIsoOfFin hs).toEquiv).trans (supportFaceHomeomorph s)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.orderedSupportFaceHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.orderedSupportFaceHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.orderedSupportFaceHomeomorph ``Submission.DifferentialGeometry.Simplex.orderedSupportFaceHomeomorph

@[simp]
theorem orderedSupportFaceHomeomorph_apply_val (s : Finset ι) {m : ℕ} (hs : s.card = m)
    (p : stdSimplex ℝ (Fin m)) :
    (orderedSupportFaceHomeomorph s hs p).val = stdSimplex.map (s.orderEmbOfFin hs) p := by
  change stdSimplex.map Subtype.val (reindexHomeomorph (s.orderIsoOfFin hs).toEquiv p) = _
  rw [reindexHomeomorph_eq_map, stdSimplex.map_comp_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.orderedSupportFaceHomeomorph_apply_val then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.orderedSupportFaceHomeomorph_apply_val"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.orderedSupportFaceHomeomorph_apply_val ``Submission.DifferentialGeometry.Simplex.orderedSupportFaceHomeomorph_apply_val

@[simp]
theorem orderedSupportFaceHomeomorph_symm_apply (s : Finset ι) {m : ℕ} (hs : s.card = m)
    (p : supportFace s) (i : Fin m) :
    (orderedSupportFaceHomeomorph s hs).symm p i = p.val (s.orderEmbOfFin hs i) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.orderedSupportFaceHomeomorph_symm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.orderedSupportFaceHomeomorph_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.orderedSupportFaceHomeomorph_symm_apply ``Submission.DifferentialGeometry.Simplex.orderedSupportFaceHomeomorph_symm_apply

omit [Fintype ι] in
private theorem orderEmbOfFin_erase (s : Finset ι) {m : ℕ} (hs : s.card = m + 1)
    (i : Fin (m + 1))
    (he : (s.erase (s.orderEmbOfFin hs i)).card = m) :
    (s.erase (s.orderEmbOfFin hs i)).orderEmbOfFin he =
      (Fin.succAboveOrderEmb i).trans (s.orderEmbOfFin hs) := by
  symm
  apply Finset.orderEmbOfFin_unique'
  intro j
  exact Finset.mem_erase.mpr ⟨by
    intro h
    exact Fin.succAbove_ne i j ((s.orderEmbOfFin hs).injective h),
    s.orderEmbOfFin_mem hs _⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Simplex.orderEmbOfFin_erase
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Simplex.orderEmbOfFin_erase target :: scope.openDecls } }

theorem orderedSupportFaceHomeomorph_erase_apply_val (s : Finset ι) {m : ℕ}
    (hs : s.card = m + 1) (i : Fin (m + 1))
    (he : (s.erase (s.orderEmbOfFin hs i)).card = m) (p : stdSimplex ℝ (Fin m)) :
    (orderedSupportFaceHomeomorph (s.erase (s.orderEmbOfFin hs i)) he p).val =
      (orderedSupportFaceHomeomorph s hs (stdSimplex.map i.succAbove p)).val := by
  rw [orderedSupportFaceHomeomorph_apply_val, orderedSupportFaceHomeomorph_apply_val,
    stdSimplex.map_comp_apply, orderEmbOfFin_erase s hs i he]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.orderedSupportFaceHomeomorph_erase_apply_val then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.orderedSupportFaceHomeomorph_erase_apply_val"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.orderedSupportFaceHomeomorph_erase_apply_val ``Submission.DifferentialGeometry.Simplex.orderedSupportFaceHomeomorph_erase_apply_val

end DifferentialGeometry.Simplex
