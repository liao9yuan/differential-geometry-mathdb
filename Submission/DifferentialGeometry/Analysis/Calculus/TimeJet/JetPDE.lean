import Submission.DifferentialGeometry.Analysis.Calculus.IteratedDerivative.SpaceJets
import Submission.DifferentialGeometry.Analysis.Calculus.TimeJet.SliceSwap
import Submission.DifferentialGeometry.Analysis.Calculus.TimeJet.SliceBootstrap

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set
open scoped _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Analysis

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem contDiffOn_of_closed_jet_pde
    {G : ℝ → E → F} {a b : ℝ} {V : Set E}
    {Ω : Set (F × (E →L[ℝ] F) × (E →L[ℝ] E →L[ℝ] F))}
    {Φ : (F × (E →L[ℝ] F) × (E →L[ℝ] E →L[ℝ] F)) → F}
    (hab : a < b) (hV : IsOpen V) (hΩ : IsOpen Ω)
    (hGs : ∀ t ∈ _root_.Set.Icc a b, ContDiffOn ℝ ∞ (G t) V)
    (hΦ : ContDiffOn ℝ ∞ Φ Ω)
    (hmap : _root_.Set.MapsTo (fun p : ℝ × E => jet2 (G p.1) p.2) (_root_.Set.Icc a b ×ˢ V) Ω)
    (hjets : ∀ r : ℕ, ContinuousOn
      (fun p : ℝ × E => iteratedFDeriv ℝ r (G p.1) p.2) (_root_.Set.Icc a b ×ˢ V))
    (hpde : ∀ t ∈ _root_.Set.Ioo a b, ∀ x ∈ V,
      HasDerivAt (fun s => G s x) (Φ (jet2 (G t) x)) t) :
    ContDiffOn ℝ ∞ (Function.uncurry G) (_root_.Set.Icc a b ×ˢ V) := by
  let RHS : ℝ → E → F := fun t x => Φ (jet2 (G t) x)
  have hJetSlices : ∀ t ∈ _root_.Set.Icc a b, ContDiffOn ℝ ∞ (jet2 (G t)) V := by
    intro t ht
    have hfirst := (hGs t ht).fderiv_of_isOpen hV (m := ∞) (by simp)
    have hsecond := hfirst.fderiv_of_isOpen hV (m := ∞) (by simp)
    exact (hGs t ht).prodMk (hfirst.prodMk hsecond)
  have hRhsSlices : ∀ t ∈ _root_.Set.Icc a b, ContDiffOn ℝ ∞ (RHS t) V := by
    intro t ht
    exact hΦ.comp (hJetSlices t ht)
      (fun x hx => hmap (show (t, x) ∈ _root_.Set.Icc a b ×ˢ V from ⟨ht, hx⟩))
  have hbase : SpaceJetDiff 0 G (_root_.Set.Icc a b) V :=
    fun r => contDiffOn_zero.mpr (hjets r)
  have hRhs0 : SpaceJetDiff 0 RHS (_root_.Set.Icc a b) V :=
    spaceJet_comp_Icc hV hΩ hmap hΦ hJetSlices (hbase.jet2 hV hGs)
  have hClosed : ∀ t ∈ _root_.Set.Icc a b, ∀ x ∈ V,
      HasDerivWithinAt (fun s => G s x) (RHS t x) (_root_.Set.Icc a b) t := by
    intro t ht x hx
    have hGtime : ContinuousOn (fun s => G s x) (_root_.Set.Icc a b) := by
      have hraw := (continuousMultilinearCurryFin0 ℝ E F).continuous.comp_continuousOn
        ((hjets 0).comp (continuousOn_id.prodMk continuousOn_const)
          (fun s hs => ⟨hs, hx⟩))
      exact hraw.congr fun _ _ => rfl
    have hRtime : ContinuousOn (fun s => RHS s x) (_root_.Set.Icc a b) := by
      have hraw := (continuousMultilinearCurryFin0 ℝ E F).continuous.comp_continuousOn
        ((hRhs0 0).continuousOn.comp (continuousOn_id.prodMk continuousOn_const)
          (fun s hs => ⟨hs, hx⟩))
      exact hraw.congr fun _ _ => rfl
    exact hasDerivIcc_of_int hab hGtime hRtime (fun s hs => hpde s hs x hx) ht
  have hAll : ∀ q : ℕ, SpaceJetDiff q G (_root_.Set.Icc a b) V := by
    intro q
    induction q with
    | zero => exact hbase
    | succ q ih =>
      have hJetQ : SpaceJetDiff q (fun t x => jet2 (G t) x) (_root_.Set.Icc a b) V :=
        ih.jet2 hV hGs
      have hRhsQ : SpaceJetDiff q RHS (_root_.Set.Icc a b) V :=
        spaceJet_comp_Icc hV hΩ hmap hΦ hJetSlices hJetQ
      intro r
      have hpdeR : ∀ p ∈ _root_.Set.Icc a b ×ˢ V,
          HasDerivWithinAt (fun s => iteratedFDeriv ℝ r (G s) p.2)
            (iteratedFDeriv ℝ r (RHS p.1) p.2) (_root_.Set.Icc a b) p.1 := by
        intro p hp
        exact hasDerivWithin_iterF hV r hGs hRhsSlices hClosed
          (fun m _ => (hRhsQ m).continuousOn) hp.1 hp.2
      have hslice : ∀ p ∈ _root_.Set.Icc a b ×ˢ V,
          HasFDerivAt (iteratedFDeriv ℝ r (G p.1))
            (fderiv ℝ (iteratedFDeriv ℝ r (G p.1)) p.2) p.2 := by
        intro p hp
        have hAt := (hGs p.1 hp.1).contDiffAt (hV.mem_nhds hp.2)
        have hJetAt : ContDiffAt ℝ 1 (iteratedFDeriv ℝ r (G p.1)) p.2 :=
          hAt.iteratedFDeriv_right (m := 1) (i := r) (by exact_mod_cast le_top)
        exact (hJetAt.differentiableAt (by norm_num)).hasFDerivAt
      have hstep := contDiffIcc_succ (q := q) hab hV hpdeR hslice
        (hRhsQ r) (ih.jet_fderiv r)
      simpa only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] using hstep
  rw [contDiffOn_infty]
  intro q
  have hraw := (continuousMultilinearCurryFin0 ℝ E F).contDiff.comp_contDiffOn (hAll q 0)
  exact hraw.congr fun p _ => by
    rcases p with ⟨t, x⟩
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.contDiffOn_of_closed_jet_pde then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.contDiffOn_of_closed_jet_pde"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.contDiffOn_of_closed_jet_pde ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.contDiffOn_of_closed_jet_pde

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
