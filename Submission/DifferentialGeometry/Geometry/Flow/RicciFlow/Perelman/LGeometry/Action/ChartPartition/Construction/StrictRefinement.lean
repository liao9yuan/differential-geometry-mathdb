import Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Chart.H1
import Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Curve.Partition
import Submission.DifferentialGeometry.Topology.FiniteSubdivision

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open _root_.Set

open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]

omit [CompleteSpace E] in
private theorem toFun_cast {a b : Real} (h : a = b) (v : timeH1 E b) :
    ((h.symm ▸ v : timeH1 E a).toFun) = v.toFun := by
  subst b
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.toFun_cast
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.toFun_cast target :: scope.openDecls } }

omit [CompleteSpace E] in
theorem exists_strict_chart_partition
    {m : Nat} (t : Fin (m + 1) → Real) (htmono : Monotone t)
    (p : Fin m → M) (u : (i : Fin m) → timeH1 E (partitionIntervalLength t i))
    (gamma : Real → M)
    (hsrc : ∀ i, _root_.Set.MapsTo gamma (_root_.Set.Icc (t i.castSucc) (t i.succ))
      (chartAt H (p i)).source)
    (hrep : ∀ i, _root_.Set.EqOn (u i).toFun
      (fun r ↦ extChartAt I (p i) (gamma (t i.castSucc + r)))
      (_root_.Set.Icc (0 : Real) (partitionIntervalLength t i))) :
    ∃ (k : Nat) (s : Fin (k + 1) → Real) (q : Fin k → Fin m)
      (p' : Fin k → M) (u' : (i : Fin k) → timeH1 E (partitionIntervalLength s i)),
      StrictMono s ∧ StrictMono q ∧
        s 0 = t 0 ∧ s (Fin.last k) = t (Fin.last m) ∧
        (∀ i, s i.castSucc = t (q i).castSucc ∧
          s i.succ = t (q i).succ) ∧
        (∀ i, p' i = p (q i)) ∧
        (∀ i, _root_.Set.MapsTo gamma (_root_.Set.Icc (s i.castSucc) (s i.succ))
          (chartAt H (p' i)).source) ∧
        (∀ i, _root_.Set.EqOn (u' i).toFun
          (fun r ↦ extChartAt I (p' i) (gamma (s i.castSucc + r)))
          (_root_.Set.Icc (0 : Real) (partitionIntervalLength s i))) := by
  classical
  obtain ⟨k, s, q, hs, hq, hfirst, hlast, hseg⟩ :=
    DifferentialGeometry.Geometry.exists_strict_subdiv t htmono
  let p' : Fin k → M := fun i ↦ p (q i)
  have hlen (i : Fin k) : partitionIntervalLength s i = partitionIntervalLength t (q i) := by
    simp only [partitionIntervalLength, (hseg i).1, (hseg i).2]
  let u' : (i : Fin k) → timeH1 E (partitionIntervalLength s i) := fun i ↦
    (hlen i).symm ▸ u (q i)
  have hsrc' (i : Fin k) : _root_.Set.MapsTo gamma
      (_root_.Set.Icc (s i.castSucc) (s i.succ)) (chartAt H (p' i)).source := by
    simpa only [p', (hseg i).1, (hseg i).2] using hsrc (q i)
  have hrep' (i : Fin k) : _root_.Set.EqOn (u' i).toFun
      (fun r ↦ extChartAt I (p' i) (gamma (s i.castSucc + r)))
      (_root_.Set.Icc (0 : Real) (partitionIntervalLength s i)) := by
    have hu : (u' i).toFun = (u (q i)).toFun := by
      dsimp only [u']
      exact toFun_cast (hlen i) (u (q i))
    rw [hu]
    simpa only [p', (hseg i).1, hlen i] using hrep (q i)
  exact ⟨k, s, q, p', u', hs, hq, hfirst, hlast, hseg,
    fun i ↦ rfl, hsrc', hrep'⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.exists_strict_chart_partition then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.exists_strict_chart_partition"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.exists_strict_chart_partition ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.exists_strict_chart_partition

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
