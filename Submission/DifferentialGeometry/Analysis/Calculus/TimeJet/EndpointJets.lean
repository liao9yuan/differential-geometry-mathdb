import Submission.DifferentialGeometry.Analysis.Calculus.TimeJet.Commutation
import Submission.DifferentialGeometry.Analysis.Calculus.PartialDerivative.Parameter

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set
open scoped _root_.ContDiff
namespace DifferentialGeometry.Analysis
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem time_derivWithin_contDiffOn {G : ℝ → E → F} {J : Set ℝ} {V : Set E}
    (hJ : UniqueDiffOn ℝ J) (hV : IsOpen V)
    (hG : ContDiffOn ℝ ∞ (Function.uncurry G) (J ×ˢ V)) :
    ContDiffOn ℝ ∞ (fun p : ℝ × E => derivWithin (fun t => G t p.2) J p.1) (J ×ˢ V) := by
  have hfd : ContDiffOn ℝ ∞ (fderivWithin ℝ (Function.uncurry G) (J ×ˢ V)) (J ×ˢ V) :=
    hG.fderivWithin (hJ.prod hV.uniqueDiffOn) (by simp)
  have hd := hfd.clm_apply (contDiffOn_const (c := ((1, 0) : ℝ × E)))
  apply hd.congr
  intro p hp
  have hh : HasDerivWithinAt (fun t : ℝ => (t, p.2)) ((1, 0) : ℝ × E) J p.1 :=
    (hasDerivWithinAt_id p.1 J).prodMk (hasDerivWithinAt_const p.1 J p.2)
  have hm : _root_.Set.MapsTo (fun t : ℝ => (t, p.2)) J (J ×ˢ V) := fun t ht => ⟨ht, hp.2⟩
  exact ((hG.differentiableOn (by simp) p hp).hasFDerivWithinAt.comp_hasDerivWithinAt
    p.1 hh hm).derivWithin (hJ p.1 hp.1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.time_derivWithin_contDiffOn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.time_derivWithin_contDiffOn target :: scope.openDecls } }

theorem time_iteratedDerivWithin_contDiffOn {G : ℝ → E → F} {J : Set ℝ} {V : Set E}
    (hJ : UniqueDiffOn ℝ J) (hV : IsOpen V)
    (hG : ContDiffOn ℝ ∞ (Function.uncurry G) (J ×ˢ V)) (b : ℕ) :
    ContDiffOn ℝ ∞
      (fun p : ℝ × E => iteratedDerivWithin b (fun t => G t p.2) J p.1) (J ×ˢ V) := by
  induction b generalizing G with
  | zero => exact hG
  | succ b ih =>
    have hh := ih (G := fun t x => derivWithin (fun s => G s x) J t)
      (time_derivWithin_contDiffOn hJ hV hG)
    simpa only [iteratedDerivWithin_succ'] using hh

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.time_iteratedDerivWithin_contDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.time_iteratedDerivWithin_contDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.time_iteratedDerivWithin_contDiffOn ``Submission.DifferentialGeometry.Analysis.time_iteratedDerivWithin_contDiffOn

theorem mixed_endpoint_jets_contDiffOn {G : ℝ → E → F} {J : Set ℝ} {V : Set E}
    (hJ : UniqueDiffOn ℝ J) (hV : IsOpen V)
    (hG : ContDiffOn ℝ ∞ (Function.uncurry G) (J ×ˢ V)) (a b : ℕ) :
    ContDiffOn ℝ ∞
      (fun p : ℝ × E => iteratedDerivWithin b
        (fun t => iteratedFDeriv ℝ a (G t) p.2) J p.1) (J ×ˢ V) :=
  time_iteratedDerivWithin_contDiffOn (G := fun t x => iteratedFDeriv ℝ a (G t) x) hJ hV
    (spatial_iteratedFDeriv_contDiffOn hV hG a) b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.mixed_endpoint_jets_contDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.mixed_endpoint_jets_contDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.mixed_endpoint_jets_contDiffOn ``Submission.DifferentialGeometry.Analysis.mixed_endpoint_jets_contDiffOn

end DifferentialGeometry.Analysis
