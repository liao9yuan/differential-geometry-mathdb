import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.W.Functional
import Submission.DifferentialGeometry.Geometry.Metric.ChartLipschitz.Spacetime
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Manifold _root_.Submission.Manifold _root_.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Entropy

private theorem locallyLipschitzOn_density_core (n : ℕ) :
    LocallyLipschitzOn (_root_.Set.Ioi (0 : ℝ) ×ˢ (_root_.Set.univ : Set ℝ))
      (fun q : ℝ × ℝ => perelmanDensityPrefactor n q.1 * Real.exp (-q.2)) := by
  apply ContDiffOn.locallyLipschitzOn ((convex_Ioi 0).prod convex_univ)
  intro q hq
  apply ContDiffAt.contDiffWithinAt
  apply ContDiffAt.mul
  · exact (contDiffAt_const.mul contDiffAt_fst).rpow_const_of_ne
      (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) (ne_of_gt hq.1))
  · exact contDiffAt_snd.neg.exp

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.locallyLipschitzOn_density_core
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Entropy.locallyLipschitzOn_density_core target :: scope.openDecls } }

theorem locallyLipschitzOn_perelmanDensity
    {X : Type*} [PseudoEMetricSpace X] {s : Set X} {t f : X → ℝ}
    (ht : LocallyLipschitzOn s t) (hf : LocallyLipschitzOn s f)
    (hpos : ∀ x ∈ s, 0 < t x) (n : ℕ) :
    LocallyLipschitzOn s (fun x => perelmanDensity n (t x) f x) :=
  (locallyLipschitzOn_density_core n).comp (ht.prodMk hf) (fun x hx => ⟨hpos x hx, _root_.Set.mem_univ _⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.locallyLipschitzOn_perelmanDensity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.locallyLipschitzOn_perelmanDensity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.locallyLipschitzOn_perelmanDensity ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.locallyLipschitzOn_perelmanDensity

theorem locallyLipschitzOn_perelmanDensity_in_chart_of_spacetime_bounds
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RegularSpace M] [PreconnectedSpace M]
    (g : SmoothRiemannianMetric I M) (p : M) {a b : ℝ} (hab : a ≤ b)
    (ell : M × _root_.Set.Icc a b → ℝ)
    (hell : ∀ R : ℝ, 0 ≤ R → ∃ K : ℝ≥0,
      ∀ x ∈ riemannianClosedBallOf g p R, ∀ y ∈ riemannianClosedBallOf g p R,
      ∀ s t : _root_.Set.Icc a b, |ell (x, s) - ell (y, t)| ≤
        (K : ℝ) * ((riemannianEDistOf g x y).toReal + |(s : ℝ) - t|))
    (α : M) (n : ℕ) :
    LocallyLipschitzOn (_root_.Set.Ioi (0 : ℝ) ×ˢ (extChartAt I α).target)
      (fun q : ℝ × E => perelmanDensity n q.1
        (fun x => ell (x, _root_.Set.projIcc a b hab q.1)) ((extChartAt I α).symm q.2)) := by
  have h := Geometry.Riemannian.locallyLipschitzOn_comp_extChartAt_symm_of_spacetime_bounds g p hab ell hell α
  exact locallyLipschitzOn_perelmanDensity LipschitzWith.prod_fst.locallyLipschitz.locallyLipschitzOn
    (h.mono (Set.prod_mono (_root_.Set.subset_univ _) Subset.rfl)) (fun _ hx => hx.1) n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.locallyLipschitzOn_perelmanDensity_in_chart_of_spacetime_bounds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.locallyLipschitzOn_perelmanDensity_in_chart_of_spacetime_bounds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.locallyLipschitzOn_perelmanDensity_in_chart_of_spacetime_bounds ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.locallyLipschitzOn_perelmanDensity_in_chart_of_spacetime_bounds

end DifferentialGeometry.PDE.RicciFlow.Entropy
