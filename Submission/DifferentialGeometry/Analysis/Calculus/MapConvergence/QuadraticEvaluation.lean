import Submission.DifferentialGeometry.Analysis.Calculus.MapConvergence.Composition

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set
open scoped _root_.ContDiff _root_.Topology

namespace DifferentialGeometry
namespace CheegerGromovCompactness

universe uX uV

variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace Real X]
variable {V : Type uV} [NormedAddCommGroup V] [NormedSpace Real V]

def quadRead (B : X -> (V →L[Real] V →L[Real] Real))
    (v : X -> V) (x : X) : Real :=
  B x (v x) (v x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.quadRead then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.quadRead"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.quadRead ``Submission.DifferentialGeometry.CheegerGromovCompactness.quadRead

theorem quadRead_contDiff {B : X -> (V →L[Real] V →L[Real] Real)}
    {v : X -> V} {n : WithTop ℕ∞}
    (hB : ContDiff Real n B) (hv : ContDiff Real n v) :
    ContDiff Real n (quadRead B v) := by
  exact (hB.clm_apply hv).clm_apply hv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.quadRead_contDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.quadRead_contDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.quadRead_contDiff ``Submission.DifferentialGeometry.CheegerGromovCompactness.quadRead_contDiff

theorem quadRead_convergence
    [FiniteDimensional Real V]
    {U : Set X} (hU : IsOpen U)
    {B : Nat -> X -> (V →L[Real] V →L[Real] Real)}
    {Binf : X -> (V →L[Real] V →L[Real] Real)}
    {v : Nat -> X -> V} {vinf : X -> V}
    (hB : MapCInfConvergenceOnCompacts U B Binf)
    (hv : MapCInfConvergenceOnCompacts U v vinf)
    (hBc : forall k, ContDiffOn Real (∞ : WithTop ℕ∞) (B k) U)
    (hBinfc : ContDiffOn Real (∞ : WithTop ℕ∞) Binf U)
    (hvc : forall k, ContDiffOn Real (∞ : WithTop ℕ∞) (v k) U)
    (hvinfc : ContDiffOn Real (∞ : WithTop ℕ∞) vinf U) :
    MapCInfConvergenceOnCompacts U (fun k => quadRead (B k) (v k))
      (quadRead Binf vinf) := by
  let evalQuad : ((V →L[Real] V →L[Real] Real) × V) -> Real :=
    fun q => q.1 q.2 q.2
  have heval : ContDiff Real (∞ : WithTop ℕ∞) evalQuad := by
    exact (contDiff_fst.clm_apply contDiff_snd).clm_apply contDiff_snd
  have hpair := mapCInfConvergence_prodMk hU hB hv hBc hBinfc hvc hvinfc
  have hcomp := MapCInfConvergenceOnCompacts.comp_of_finiteDimensional
    hU isOpen_univ hpair
    (mapCInfConvergence_const (U := (Set.univ : Set ((V →L[Real] V →L[Real] Real) × V)))
      evalQuad)
    (fun k => (hBc k).prodMk (hvc k)) (hBinfc.prodMk hvinfc)
    (fun _ => heval.contDiffOn) heval.contDiffOn
    (Set.mapsTo_univ _ _) (fun _ => Set.mapsTo_univ _ _)
  exact hcomp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.quadRead_convergence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.quadRead_convergence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.quadRead_convergence ``Submission.DifferentialGeometry.CheegerGromovCompactness.quadRead_convergence

theorem quadBump_convergence
    [FiniteDimensional Real V]
    {U : Set X} (hU : IsOpen U)
    {B : Nat -> X -> (V →L[Real] V →L[Real] Real)}
    {Binf : X -> (V →L[Real] V →L[Real] Real)}
    {v : Nat -> X -> V} {vinf : X -> V}
    (hB : MapCInfConvergenceOnCompacts U B Binf)
    (hv : MapCInfConvergenceOnCompacts U v vinf)
    (hBc : forall k, ContDiffOn Real (∞ : WithTop ℕ∞) (B k) U)
    (hBinfc : ContDiffOn Real (∞ : WithTop ℕ∞) Binf U)
    (hvc : forall k, ContDiffOn Real (∞ : WithTop ℕ∞) (v k) U)
    (hvinfc : ContDiffOn Real (∞ : WithTop ℕ∞) vinf U)
    (f : Real -> Real) (hf : ContDiff Real (∞ : WithTop ℕ∞) f) :
    MapCInfConvergenceOnCompacts U
      (fun k x => f (quadRead (B k) (v k) x))
      (fun x => f (quadRead Binf vinf x)) := by
  have hquad := quadRead_convergence hU hB hv hBc hBinfc hvc hvinfc
  have hqc : forall k, ContDiffOn Real (∞ : WithTop ℕ∞)
      (quadRead (B k) (v k)) U :=
    fun k => (hBc k).clm_apply (hvc k) |>.clm_apply (hvc k)
  have hqinfc : ContDiffOn Real (∞ : WithTop ℕ∞)
      (quadRead Binf vinf) U :=
    hBinfc.clm_apply hvinfc |>.clm_apply hvinfc
  exact MapCInfConvergenceOnCompacts.comp hU isOpen_univ hquad
    (mapCInfConvergence_const (U := (Set.univ : Set Real)) f)
    hqc hqinfc (fun _ => hf.contDiffOn) hf.contDiffOn
    (Set.mapsTo_univ _ _) (fun _ => Set.mapsTo_univ _ _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.quadBump_convergence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.quadBump_convergence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.quadBump_convergence ``Submission.DifferentialGeometry.CheegerGromovCompactness.quadBump_convergence

theorem quadPiBump_convergence {ι : Type*} [Fintype ι]
    [FiniteDimensional Real V]
    {U : Set X} (hU : IsOpen U)
    {B : Nat -> X -> (ι -> (V →L[Real] V →L[Real] Real))}
    {Binf : X -> (ι -> (V →L[Real] V →L[Real] Real))}
    {v : Nat -> X -> V} {vinf : X -> V}
    (hB : MapCInfConvergenceOnCompacts U B Binf)
    (hv : MapCInfConvergenceOnCompacts U v vinf)
    (hBc : forall k, ContDiffOn Real (∞ : WithTop ℕ∞) (B k) U)
    (hBinfc : ContDiffOn Real (∞ : WithTop ℕ∞) Binf U)
    (hvc : forall k, ContDiffOn Real (∞ : WithTop ℕ∞) (v k) U)
    (hvinfc : ContDiffOn Real (∞ : WithTop ℕ∞) vinf U)
    (i : ι) (f : Real -> Real) (hf : ContDiff Real (∞ : WithTop ℕ∞) f) :
    MapCInfConvergenceOnCompacts U
      (fun k x => f (B k x i (v k x) (v k x)))
      (fun x => f (Binf x i (vinf x) (vinf x))) := by
  exact quadBump_convergence hU (mapCInf_apply hU hB hBc hBinfc i) hv
    (fun k => contDiffOn_pi.mp (hBc k) i) (contDiffOn_pi.mp hBinfc i)
    hvc hvinfc f hf

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.quadPiBump_convergence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.quadPiBump_convergence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.quadPiBump_convergence ``Submission.DifferentialGeometry.CheegerGromovCompactness.quadPiBump_convergence


end CheegerGromovCompactness
end DifferentialGeometry
