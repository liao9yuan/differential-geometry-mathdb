import Submission.DifferentialGeometry.Analysis.Calculus.Inverse.MatrixSmoothness

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open scoped _root_.ContDiff

namespace DifferentialGeometry
namespace Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

abbrev MatJet (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ) : Type _ :=
  (Fin n → Fin n → ℝ) ×
    (E →L[ℝ] (Fin n → Fin n → ℝ)) × (E →L[ℝ] (E →L[ℝ] (Fin n → Fin n → ℝ)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.MatJet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.MatJet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.MatJet ``Submission.DifferentialGeometry.Analysis.MatJet

theorem contDiff_jetVal (a b : Fin n) :
    ContDiff ℝ ∞ (fun p : MatJet E n => p.1 a b) :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) b).contDiff.comp
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => Fin n → ℝ) a).contDiff.comp
      contDiff_fst)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.contDiff_jetVal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.contDiff_jetVal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.contDiff_jetVal ``Submission.DifferentialGeometry.Analysis.contDiff_jetVal


theorem contDiff_jetD1 (d : E) (a b : Fin n) :
    ContDiff ℝ ∞ (fun p : MatJet E n => (p.2.1 d) a b) :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) b).contDiff.comp
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => Fin n → ℝ) a).contDiff.comp
      ((ContinuousLinearMap.apply ℝ (Fin n → Fin n → ℝ) d).contDiff.comp
        (contDiff_fst.comp contDiff_snd)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.contDiff_jetD1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.contDiff_jetD1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.contDiff_jetD1 ``Submission.DifferentialGeometry.Analysis.contDiff_jetD1


theorem contDiff_jetD2 (d e : E) (a b : Fin n) :
    ContDiff ℝ ∞ (fun p : MatJet E n => (p.2.2 d e) a b) :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) b).contDiff.comp
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => Fin n → ℝ) a).contDiff.comp
      (((contDiff_snd.comp contDiff_snd).clm_apply (contDiff_const (c := d))).clm_apply
        (contDiff_const (c := e))))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.contDiff_jetD2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.contDiff_jetD2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.contDiff_jetD2 ``Submission.DifferentialGeometry.Analysis.contDiff_jetD2

theorem contDiffAt_jetInvGram {p₀ : MatJet E n} (hp₀ : (Matrix.of p₀.1).det ≠ 0) (k l : Fin n) :
    ContDiffAt ℝ ∞ (fun p : MatJet E n => (Matrix.of p.1)⁻¹ k l) p₀ :=
  contDiffAt_inv_of_entries (fun p : MatJet E n => Matrix.of p.1)
    (fun a b => contDiff_jetVal a b) hp₀ k l

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.contDiffAt_jetInvGram then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.contDiffAt_jetInvGram"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.contDiffAt_jetInvGram ``Submission.DifferentialGeometry.Analysis.contDiffAt_jetInvGram

theorem contDiffAt_jetInvGramDeriv (b : Fin n → E) {p₀ : MatJet E n}
    (hp₀ : (Matrix.of p₀.1).det ≠ 0) (m k l : Fin n) :
    ContDiffAt ℝ ∞ (fun p : MatJet E n =>
      -∑ a : Fin n, ∑ c : Fin n,
        (Matrix.of p.1)⁻¹ k a * (Matrix.of p.1)⁻¹ c l * (p.2.1 (b m)) a c) p₀ := by
  refine ContDiffAt.neg (ContDiffAt.sum (fun a _ => ContDiffAt.sum (fun c _ => ?_)))
  exact ((contDiffAt_jetInvGram hp₀ k a).mul (contDiffAt_jetInvGram hp₀ c l)).mul
    (contDiff_jetD1 (b m) a c).contDiffAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.contDiffAt_jetInvGramDeriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.contDiffAt_jetInvGramDeriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.contDiffAt_jetInvGramDeriv ``Submission.DifferentialGeometry.Analysis.contDiffAt_jetInvGramDeriv

def jetChristoffel (b : Fin n → E) (p : MatJet E n) (i j k : Fin n) : ℝ :=
  (1 / 2 : ℝ) * ∑ l : Fin n, (Matrix.of p.1)⁻¹ k l *
    ((p.2.1 (b i)) l j + (p.2.1 (b j)) l i - (p.2.1 (b l)) i j)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.jetChristoffel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.jetChristoffel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.jetChristoffel ``Submission.DifferentialGeometry.Analysis.jetChristoffel

def jetChristoffelDeriv (b : Fin n → E) (p : MatJet E n) (m i j k : Fin n) : ℝ :=
  (1 / 2 : ℝ) * ∑ l : Fin n,
    ((-∑ a : Fin n, ∑ c : Fin n,
          (Matrix.of p.1)⁻¹ k a * (Matrix.of p.1)⁻¹ c l * (p.2.1 (b m)) a c)
        * ((p.2.1 (b i)) l j + (p.2.1 (b j)) l i - (p.2.1 (b l)) i j)
      + (Matrix.of p.1)⁻¹ k l
        * ((p.2.2 (b m) (b i)) l j + (p.2.2 (b m) (b j)) l i - (p.2.2 (b m) (b l)) i j))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.jetChristoffelDeriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.jetChristoffelDeriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.jetChristoffelDeriv ``Submission.DifferentialGeometry.Analysis.jetChristoffelDeriv


def jetRiemann (b : Fin n → E) (p : MatJet E n) (i j k l : Fin n) : ℝ :=
  jetChristoffelDeriv b p j i k l - jetChristoffelDeriv b p k i j l
    + ∑ m : Fin n, (jetChristoffel b p j m l * jetChristoffel b p i k m
        - jetChristoffel b p k m l * jetChristoffel b p i j m)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.jetRiemann then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.jetRiemann"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.jetRiemann ``Submission.DifferentialGeometry.Analysis.jetRiemann


def jetRicci (b : Fin n → E) (p : MatJet E n) (i k : Fin n) : ℝ :=
  ∑ j : Fin n, jetRiemann b p i j k j

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.jetRicci then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.jetRicci"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.jetRicci ``Submission.DifferentialGeometry.Analysis.jetRicci

def jetRicciFlow (b : Fin n → E) (p : MatJet E n) : Fin n → Fin n → ℝ :=
  fun i k => -2 * jetRicci b p i k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.jetRicciFlow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.jetRicciFlow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.jetRicciFlow ``Submission.DifferentialGeometry.Analysis.jetRicciFlow


theorem contDiffAt_jetChristoffel (b : Fin n → E) {p₀ : MatJet E n}
    (hp₀ : (Matrix.of p₀.1).det ≠ 0) (i j k : Fin n) :
    ContDiffAt ℝ ∞ (fun p : MatJet E n => jetChristoffel b p i j k) p₀ := by
  unfold jetChristoffel
  refine contDiffAt_const.mul (ContDiffAt.sum (fun l _ => ?_))
  refine (contDiffAt_jetInvGram hp₀ k l).mul ?_
  exact (((contDiff_jetD1 (b i) l j).contDiffAt).add (contDiff_jetD1 (b j) l i).contDiffAt).sub
    (contDiff_jetD1 (b l) i j).contDiffAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.contDiffAt_jetChristoffel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.contDiffAt_jetChristoffel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.contDiffAt_jetChristoffel ``Submission.DifferentialGeometry.Analysis.contDiffAt_jetChristoffel


theorem contDiffAt_jetChristoffelDeriv (b : Fin n → E) {p₀ : MatJet E n}
    (hp₀ : (Matrix.of p₀.1).det ≠ 0) (m i j k : Fin n) :
    ContDiffAt ℝ ∞ (fun p : MatJet E n => jetChristoffelDeriv b p m i j k) p₀ := by
  unfold jetChristoffelDeriv
  refine contDiffAt_const.mul (ContDiffAt.sum (fun l _ => ?_))
  refine ContDiffAt.add (ContDiffAt.mul ?_ ?_) (ContDiffAt.mul ?_ ?_)
  · exact contDiffAt_jetInvGramDeriv b hp₀ m k l
  · exact (((contDiff_jetD1 (b i) l j).contDiffAt).add (contDiff_jetD1 (b j) l i).contDiffAt).sub
      (contDiff_jetD1 (b l) i j).contDiffAt
  · exact contDiffAt_jetInvGram hp₀ k l
  · exact (((contDiff_jetD2 (b m) (b i) l j).contDiffAt).add
      (contDiff_jetD2 (b m) (b j) l i).contDiffAt).sub (contDiff_jetD2 (b m) (b l) i j).contDiffAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.contDiffAt_jetChristoffelDeriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.contDiffAt_jetChristoffelDeriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.contDiffAt_jetChristoffelDeriv ``Submission.DifferentialGeometry.Analysis.contDiffAt_jetChristoffelDeriv


theorem contDiffAt_jetRiemann (b : Fin n → E) {p₀ : MatJet E n}
    (hp₀ : (Matrix.of p₀.1).det ≠ 0) (i j k l : Fin n) :
    ContDiffAt ℝ ∞ (fun p : MatJet E n => jetRiemann b p i j k l) p₀ := by
  unfold jetRiemann
  refine ((contDiffAt_jetChristoffelDeriv b hp₀ j i k l).sub
    (contDiffAt_jetChristoffelDeriv b hp₀ k i j l)).add (ContDiffAt.sum (fun m _ => ?_))
  exact ((contDiffAt_jetChristoffel b hp₀ j m l).mul (contDiffAt_jetChristoffel b hp₀ i k m)).sub
    ((contDiffAt_jetChristoffel b hp₀ k m l).mul (contDiffAt_jetChristoffel b hp₀ i j m))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.contDiffAt_jetRiemann then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.contDiffAt_jetRiemann"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.contDiffAt_jetRiemann ``Submission.DifferentialGeometry.Analysis.contDiffAt_jetRiemann


theorem contDiffAt_jetRicci (b : Fin n → E) {p₀ : MatJet E n}
    (hp₀ : (Matrix.of p₀.1).det ≠ 0) (i k : Fin n) :
    ContDiffAt ℝ ∞ (fun p : MatJet E n => jetRicci b p i k) p₀ := by
  unfold jetRicci
  exact ContDiffAt.sum (fun j _ => contDiffAt_jetRiemann b hp₀ i j k j)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.contDiffAt_jetRicci then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.contDiffAt_jetRicci"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.contDiffAt_jetRicci ``Submission.DifferentialGeometry.Analysis.contDiffAt_jetRicci

theorem contDiffAt_jetRicciFlow (b : Fin n → E) {p₀ : MatJet E n}
    (hp₀ : (Matrix.of p₀.1).det ≠ 0) :
    ContDiffAt ℝ ∞ (fun p : MatJet E n => jetRicciFlow b p) p₀ := by
  refine contDiffAt_pi.mpr (fun i => contDiffAt_pi.mpr (fun k => ?_))
  exact contDiffAt_const.mul (contDiffAt_jetRicci b hp₀ i k)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.contDiffAt_jetRicciFlow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.contDiffAt_jetRicciFlow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.contDiffAt_jetRicciFlow ``Submission.DifferentialGeometry.Analysis.contDiffAt_jetRicciFlow

end Analysis
end DifferentialGeometry

end
