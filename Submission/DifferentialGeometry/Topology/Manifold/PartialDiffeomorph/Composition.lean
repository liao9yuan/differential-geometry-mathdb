import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Tactic.Order

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry

open scoped _root_.Manifold _root_.ContDiff

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}

noncomputable def PartialDiffeomorph.refl (M : Type u) [TopologicalSpace M]
    [ChartedSpace H M] :
    PartialDiffeomorph I I M M (∞ : WithTop ℕ∞) where
  toPartialEquiv := PartialEquiv.refl M
  open_source := isOpen_univ
  open_target := isOpen_univ
  contMDiffOn_toFun := contMDiff_id.contMDiffOn
  contMDiffOn_invFun := contMDiff_id.contMDiffOn

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.PartialDiffeomorph
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PartialDiffeomorph.refl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PartialDiffeomorph.refl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PartialDiffeomorph.refl ``Submission.DifferentialGeometry.PartialDiffeomorph.refl

namespace CheegerGromovCompactness

section Chain

noncomputable def chainComp {Mf : ℕ → Type u} [∀ j, TopologicalSpace (Mf j)]
    [∀ j, ChartedSpace H (Mf j)]
    (Ψ : ∀ j, PartialDiffeomorph I I (Mf j) (Mf (j + 1)) (∞ : WithTop ℕ∞)) (j l : ℕ) :
    PartialDiffeomorph I I (Mf j) (Mf (j + l)) (∞ : WithTop ℕ∞) :=
  Nat.rec
    (motive := fun l => PartialDiffeomorph I I (Mf j) (Mf (j + l)) (∞ : WithTop ℕ∞))
    (PartialDiffeomorph.refl (I := I) (Mf j))
    (fun l prev =>
      _root_.PartialDiffeomorph.trans (I := I) prev (Ψ (j + l)))
    l

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.chainComp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.chainComp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.chainComp ``Submission.DifferentialGeometry.CheegerGromovCompactness.chainComp

noncomputable def chainCompOfAddEq {Mf : ℕ → Type u} [∀ j, TopologicalSpace (Mf j)]
    [∀ j, ChartedSpace H (Mf j)]
    (Ψ : ∀ j, PartialDiffeomorph I I (Mf j) (Mf (j + 1)) (∞ : WithTop ℕ∞)) :
    ∀ (l j m : ℕ), j + l = m → PartialDiffeomorph I I (Mf j) (Mf m) (∞ : WithTop ℕ∞) :=
  Nat.rec
    (motive := fun l => ∀ j m : ℕ, j + l = m →
      PartialDiffeomorph I I (Mf j) (Mf m) (∞ : WithTop ℕ∞))
    (fun j m h => (Nat.add_zero j ▸ h : j = m) ▸ PartialDiffeomorph.refl (I := I) (Mf j))
    (fun l ih j m h =>
      _root_.PartialDiffeomorph.trans (I := I) (Ψ j) (ih (j + 1) m (by omega)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.chainCompOfAddEq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.chainCompOfAddEq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.chainCompOfAddEq ``Submission.DifferentialGeometry.CheegerGromovCompactness.chainCompOfAddEq

theorem chainComp_apply_succ {Mf : ℕ → Type u} [∀ j, TopologicalSpace (Mf j)]
    [∀ j, ChartedSpace H (Mf j)]
    (Ψ : ∀ j, PartialDiffeomorph I I (Mf j) (Mf (j + 1)) (∞ : WithTop ℕ∞))
    (j l : ℕ) (x : Mf j) :
    (chainComp (I := I) (Mf := Mf) Ψ j (l + 1) : Mf j → Mf (j + (l + 1))) x
      = (Ψ (j + l) : Mf (j + l) → Mf (j + l + 1))
          ((chainComp (I := I) (Mf := Mf) Ψ j l : Mf j → Mf (j + l)) x) :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.chainComp_apply_succ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.chainComp_apply_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.chainComp_apply_succ ``Submission.DifferentialGeometry.CheegerGromovCompactness.chainComp_apply_succ

theorem chainComp_shift_apply {Mf : ℕ → Type u} [∀ j, TopologicalSpace (Mf j)]
    [∀ j, ChartedSpace H (Mf j)]
    (Ψ : ∀ n, PartialDiffeomorph I I (Mf n) (Mf (n + 1)) (∞ : WithTop ℕ∞))
    (j₀ n k : ℕ) (x : Mf (j₀ + n)) :
    cast (congrArg Mf (Nat.add_assoc j₀ n k).symm)
      (chainComp (Mf := fun m => Mf (j₀ + m))
        (fun m => chainComp Ψ (j₀ + m) 1) n k x) =
      chainComp Ψ (j₀ + n) k x := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [chainComp_apply_succ, chainComp_apply_succ]
      conv_rhs => rw [chainComp_apply_succ]
      change cast (congrArg Mf (Nat.add_assoc j₀ n (k + 1)).symm)
        ((Ψ (j₀ + (n + k))) (chainComp (Mf := fun m => Mf (j₀ + m))
          (fun m => chainComp Ψ (j₀ + m) 1) n k x)) = _
      rw [← ih]
      have hcast : ∀ {a c : ℕ} (h : a = c) (y : Mf c),
          cast (congrArg Mf (congrArg Nat.succ h).symm) ((Ψ c) y) =
            (Ψ a) (cast (congrArg Mf h).symm y) := by
        intro a c h y
        cases h
        rfl
      exact hcast (Nat.add_assoc j₀ n k)
        (chainComp (Mf := fun m => Mf (j₀ + m))
          (fun m => chainComp Ψ (j₀ + m) 1) n k x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.chainComp_shift_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.chainComp_shift_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.chainComp_shift_apply ``Submission.DifferentialGeometry.CheegerGromovCompactness.chainComp_shift_apply

theorem chainComp_base {Mf : ℕ → Type u} [∀ j, TopologicalSpace (Mf j)]
    [∀ j, ChartedSpace H (Mf j)]
    (Ψ : ∀ j, PartialDiffeomorph I I (Mf j) (Mf (j + 1)) (∞ : WithTop ℕ∞))
    (b : ∀ j, Mf j)
    (hbase : ∀ j, (Ψ j : Mf j → Mf (j + 1)) (b j) = b (j + 1))
    (j l : ℕ) :
    (chainComp (I := I) (Mf := Mf) Ψ j l : Mf j → Mf (j + l)) (b j) = b (j + l) := by
  induction l with
  | zero =>
      rfl
  | succ l ih =>
      rw [chainComp_apply_succ, ih]
      change (Ψ (j + l) : Mf (j + l) → Mf ((j + l) + 1)) (b (j + l)) =
        b ((j + l) + 1)
      exact hbase (j + l)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.chainComp_base then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.chainComp_base"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.chainComp_base ``Submission.DifferentialGeometry.CheegerGromovCompactness.chainComp_base

theorem chainComp_add_apply {Mf : ℕ → Type u} [∀ j, TopologicalSpace (Mf j)]
    [∀ j, ChartedSpace H (Mf j)]
    (Ψ : ∀ j, PartialDiffeomorph I I (Mf j) (Mf (j + 1)) (∞ : WithTop ℕ∞))
    (j a b : ℕ) (x : Mf j) :
    cast (congrArg Mf (Nat.add_assoc j a b).symm)
        ((chainComp (I := I) (Mf := Mf) Ψ j (a + b) : Mf j → Mf (j + (a + b))) x) =
      (chainComp (I := I) (Mf := Mf) Ψ (j + a) b : Mf (j + a) → Mf ((j + a) + b))
        ((chainComp (I := I) (Mf := Mf) Ψ j a : Mf j → Mf (j + a)) x) := by
  have cast_step : ∀ (m n : ℕ) (h : m = n) (y : Mf m),
      cast (congrArg Mf (congrArg Nat.succ h))
          ((Ψ m : Mf m → Mf (m + 1)) y) =
        (Ψ n : Mf n → Mf (n + 1)) (cast (congrArg Mf h) y) := by
    intro m n h y
    subst h
    rfl
  induction b with
  | zero =>
      rfl
  | succ b ih =>
      change
        cast (congrArg Mf (Nat.add_assoc j a (b + 1)).symm)
            ((Ψ (j + (a + b)) : Mf (j + (a + b)) → Mf (j + (a + b) + 1))
              ((chainComp (I := I) (Mf := Mf) Ψ j (a + b) :
                Mf j → Mf (j + (a + b))) x)) =
          (Ψ ((j + a) + b) : Mf ((j + a) + b) → Mf ((j + a) + b + 1))
            ((chainComp (I := I) (Mf := Mf) Ψ (j + a) b :
              Mf (j + a) → Mf ((j + a) + b))
              ((chainComp (I := I) (Mf := Mf) Ψ j a : Mf j → Mf (j + a)) x))
      calc
        cast (congrArg Mf (Nat.add_assoc j a (b + 1)).symm)
            ((Ψ (j + (a + b)) : Mf (j + (a + b)) → Mf (j + (a + b) + 1))
              ((chainComp (I := I) (Mf := Mf) Ψ j (a + b) :
                Mf j → Mf (j + (a + b))) x)) =
            (Ψ ((j + a) + b) : Mf ((j + a) + b) → Mf ((j + a) + b + 1))
              (cast (congrArg Mf (Nat.add_assoc j a b).symm)
                ((chainComp (I := I) (Mf := Mf) Ψ j (a + b) :
                  Mf j → Mf (j + (a + b))) x)) := by
              simpa only [Nat.add_succ] using
                cast_step (j + (a + b)) ((j + a) + b) (Nat.add_assoc j a b).symm
                  ((chainComp (I := I) (Mf := Mf) Ψ j (a + b) :
                    Mf j → Mf (j + (a + b))) x)
        _ = (Ψ ((j + a) + b) : Mf ((j + a) + b) → Mf ((j + a) + b + 1))
              ((chainComp (I := I) (Mf := Mf) Ψ (j + a) b :
                Mf (j + a) → Mf ((j + a) + b))
                ((chainComp (I := I) (Mf := Mf) Ψ j a : Mf j → Mf (j + a)) x)) := by
              rw [ih]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.chainComp_add_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.chainComp_add_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.chainComp_add_apply ``Submission.DifferentialGeometry.CheegerGromovCompactness.chainComp_add_apply

noncomputable def chainCompAssoc {Mf : ℕ → Type u} [∀ j, TopologicalSpace (Mf j)]
    [∀ j, ChartedSpace H (Mf j)]
    (Ψ : ∀ j, PartialDiffeomorph I I (Mf j) (Mf (j + 1)) (∞ : WithTop ℕ∞))
    (j a b : ℕ) :
    PartialDiffeomorph I I (Mf j) (Mf ((j + a) + b)) (∞ : WithTop ℕ∞) :=
  (Nat.add_assoc j a b).symm ▸ chainComp (I := I) (Mf := Mf) Ψ j (a + b)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.chainCompAssoc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.chainCompAssoc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.chainCompAssoc ``Submission.DifferentialGeometry.CheegerGromovCompactness.chainCompAssoc

private theorem targetCast_source {Mf : ℕ → Type u} [∀ j, TopologicalSpace (Mf j)]
    [∀ j, ChartedSpace H (Mf j)]
    {j l m : ℕ} (h : l = m)
    (Φ : PartialDiffeomorph I I (Mf j) (Mf l) (∞ : WithTop ℕ∞)) :
    (h ▸ Φ).source = Φ.source := by
  subst h
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.targetCast_source
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.targetCast_source target :: scope.openDecls } }

theorem chainAssoc_source {Mf : ℕ → Type u} [∀ j, TopologicalSpace (Mf j)]
    [∀ j, ChartedSpace H (Mf j)]
    (Ψ : ∀ j, PartialDiffeomorph I I (Mf j) (Mf (j + 1)) (∞ : WithTop ℕ∞))
    (j a b : ℕ) :
    (chainCompAssoc (I := I) (Mf := Mf) Ψ j a b).source =
      (chainComp (I := I) (Mf := Mf) Ψ j (a + b)).source := by
  simpa only [chainCompAssoc] using
    targetCast_source (I := I) (Nat.add_assoc j a b).symm
      (chainComp (I := I) (Mf := Mf) Ψ j (a + b))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.chainAssoc_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.chainAssoc_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.chainAssoc_source ``Submission.DifferentialGeometry.CheegerGromovCompactness.chainAssoc_source

theorem chainCompAssoc_apply {Mf : ℕ → Type u} [∀ j, TopologicalSpace (Mf j)]
    [∀ j, ChartedSpace H (Mf j)]
    (Ψ : ∀ j, PartialDiffeomorph I I (Mf j) (Mf (j + 1)) (∞ : WithTop ℕ∞))
    (j a b : ℕ) (x : Mf j) :
    (chainCompAssoc (I := I) (Mf := Mf) Ψ j a b : Mf j → Mf ((j + a) + b)) x =
      (chainComp (I := I) (Mf := Mf) Ψ (j + a) b : Mf (j + a) → Mf ((j + a) + b))
        ((chainComp (I := I) (Mf := Mf) Ψ j a : Mf j → Mf (j + a)) x) := by
  have cast_apply : ∀ {m n : ℕ} (h : m = n)
      (F : PartialDiffeomorph I I (Mf j) (Mf m) (∞ : WithTop ℕ∞)) (y : Mf j),
      ((h ▸ F : PartialDiffeomorph I I (Mf j) (Mf n) (∞ : WithTop ℕ∞)) : Mf j → Mf n) y =
        cast (congrArg Mf h) ((F : Mf j → Mf m) y) := by
    intro m n h F y
    subst h
    rfl
  unfold chainCompAssoc
  rw [cast_apply]
  exact chainComp_add_apply (I := I) (Mf := Mf) Ψ j a b x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.chainCompAssoc_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.chainCompAssoc_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.chainCompAssoc_apply ``Submission.DifferentialGeometry.CheegerGromovCompactness.chainCompAssoc_apply

theorem chainCompAssoc_eq {Mf : ℕ → Type u} [∀ j, TopologicalSpace (Mf j)]
    [∀ j, ChartedSpace H (Mf j)]
    (Ψ : ∀ j, PartialDiffeomorph I I (Mf j) (Mf (j + 1)) (∞ : WithTop ℕ∞))
    (j a b : ℕ) :
    (chainCompAssoc (I := I) (Mf := Mf) Ψ j a b : Mf j → Mf ((j + a) + b)) =
      (_root_.PartialDiffeomorph.trans (I := I)
        (chainComp (I := I) (Mf := Mf) Ψ j a)
        (chainComp (I := I) (Mf := Mf) Ψ (j + a) b) : Mf j → Mf ((j + a) + b)) := by
  funext x
  exact chainCompAssoc_apply (I := I) (Mf := Mf) Ψ j a b x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.chainCompAssoc_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.chainCompAssoc_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.chainCompAssoc_eq ``Submission.DifferentialGeometry.CheegerGromovCompactness.chainCompAssoc_eq

theorem chainCompOfAddEq_apply_succ {Mf : ℕ → Type u} [∀ j, TopologicalSpace (Mf j)]
    [∀ j, ChartedSpace H (Mf j)]
    (Ψ : ∀ j, PartialDiffeomorph I I (Mf j) (Mf (j + 1)) (∞ : WithTop ℕ∞))
    (l j m : ℕ) (h : j + (l + 1) = m) (x : Mf j) :
    (chainCompOfAddEq (I := I) (Mf := Mf) Ψ (l + 1) j m h : Mf j → Mf m) x
      = (chainCompOfAddEq (I := I) (Mf := Mf) Ψ l (j + 1) m (by omega) : Mf (j + 1) → Mf m)
          ((Ψ j : Mf j → Mf (j + 1)) x) :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.chainCompOfAddEq_apply_succ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.chainCompOfAddEq_apply_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.chainCompOfAddEq_apply_succ ``Submission.DifferentialGeometry.CheegerGromovCompactness.chainCompOfAddEq_apply_succ

theorem chainCompOfAddEq_apply_zero {Mf : ℕ → Type u} [∀ j, TopologicalSpace (Mf j)]
    [∀ j, ChartedSpace H (Mf j)]
    (Ψ : ∀ j, PartialDiffeomorph I I (Mf j) (Mf (j + 1)) (∞ : WithTop ℕ∞))
    (j m : ℕ) (h : j + 0 = m) (x : Mf j) :
    (chainCompOfAddEq (I := I) (Mf := Mf) Ψ 0 j m h : Mf j → Mf m) x
      = (Nat.add_zero j ▸ h : j = m) ▸ x := by
  have hj : j = m := Nat.add_zero j ▸ h
  subst hj
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.chainCompOfAddEq_apply_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.chainCompOfAddEq_apply_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.chainCompOfAddEq_apply_zero ``Submission.DifferentialGeometry.CheegerGromovCompactness.chainCompOfAddEq_apply_zero

theorem chainCompOfAddEq_snoc {Mf : ℕ → Type u} [∀ j, TopologicalSpace (Mf j)]
    [∀ j, ChartedSpace H (Mf j)]
    (Ψ : ∀ j, PartialDiffeomorph I I (Mf j) (Mf (j + 1)) (∞ : WithTop ℕ∞)) :
    ∀ (l j m : ℕ) (h : j + (l + 1) = m) (x : Mf j),
      (chainCompOfAddEq (I := I) (Mf := Mf) Ψ (l + 1) j m h : Mf j → Mf m) x
        = (h ▸ ((Ψ (j + l) : Mf (j + l) → Mf (j + l + 1))
            ((chainCompOfAddEq (I := I) (Mf := Mf) Ψ l j (j + l) rfl :
              Mf j → Mf (j + l)) x)) : Mf m) := by
  intro l
  induction l with
  | zero =>
      intro j m h x
      subst h
      rw [chainCompOfAddEq_apply_succ, chainCompOfAddEq_apply_zero, chainCompOfAddEq_apply_zero]
      rfl
  | succ l ih =>
      intro j m h x
      subst h
      rw [chainCompOfAddEq_apply_succ,
        ih (j + 1) (j + (l + 1 + 1)) (by omega) ((Ψ j : Mf j → Mf (j + 1)) x)]
      conv_rhs => rw [chainCompOfAddEq_apply_succ]
      have hcast : ∀ (a : ℕ) (ha : (j + 1) + l = a),
          (Ψ a : Mf a → Mf (a + 1))
              ((chainCompOfAddEq (I := I) (Mf := Mf) Ψ l (j + 1) a ha : Mf (j + 1) → Mf a)
                ((Ψ j : Mf j → Mf (j + 1)) x))
            = ha ▸ ((Ψ ((j + 1) + l) : Mf ((j + 1) + l) → Mf ((j + 1) + l + 1))
                ((chainCompOfAddEq (I := I) (Mf := Mf) Ψ l (j + 1) ((j + 1) + l) rfl :
                    Mf (j + 1) → Mf ((j + 1) + l))
                  ((Ψ j : Mf j → Mf (j + 1)) x))) := by
        intro a ha; subst ha; rfl
      rw [hcast (j + (l + 1)) (by omega)]
      simp only [eqRec_eq_cast]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.chainCompOfAddEq_snoc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.chainCompOfAddEq_snoc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.chainCompOfAddEq_snoc ``Submission.DifferentialGeometry.CheegerGromovCompactness.chainCompOfAddEq_snoc

theorem chainComp_eq_right {Mf : ℕ → Type u} [∀ j, TopologicalSpace (Mf j)]
    [∀ j, ChartedSpace H (Mf j)]
    (Ψ : ∀ j, PartialDiffeomorph I I (Mf j) (Mf (j + 1)) (∞ : WithTop ℕ∞))
    (l j : ℕ) :
    (chainComp (I := I) (Mf := Mf) Ψ j l : Mf j → Mf (j + l))
      = (chainCompOfAddEq (I := I) (Mf := Mf) Ψ l j (j + l) rfl :
          Mf j → Mf (j + l)) := by
  funext x
  induction l generalizing j with
  | zero =>
      rw [chainCompOfAddEq_apply_zero]
      rfl
  | succ l ih =>
      rw [chainComp_apply_succ, ih j, chainCompOfAddEq_snoc]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.chainComp_eq_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.chainComp_eq_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.chainComp_eq_right ``Submission.DifferentialGeometry.CheegerGromovCompactness.chainComp_eq_right

theorem chainComp_coe_head {Mf : ℕ → Type u} [∀ j, TopologicalSpace (Mf j)]
    [∀ j, ChartedSpace H (Mf j)]
    (Ψ : ∀ j, PartialDiffeomorph I I (Mf j) (Mf (j + 1)) (∞ : WithTop ℕ∞)) :
    ∀ (l j : ℕ) (x : Mf j),
      (chainComp (I := I) (Mf := Mf) Ψ j (l + 1) : Mf j → Mf (j + (l + 1))) x
        = (chainCompOfAddEq (I := I) (Mf := Mf) Ψ l (j + 1) (j + (l + 1)) (by omega) :
            Mf (j + 1) → Mf (j + (l + 1)))
            ((Ψ j : Mf j → Mf (j + 1)) x) := by
  have lemmaA : ∀ (l j : ℕ) (x : Mf j),
      (chainComp (I := I) (Mf := Mf) Ψ j l : Mf j → Mf (j + l)) x
        = (chainCompOfAddEq (I := I) (Mf := Mf) Ψ l j (j + l) rfl :
            Mf j → Mf (j + l)) x := by
    intro l
    induction l with
    | zero =>
        intro j x
        rw [chainCompOfAddEq_apply_zero]
        rfl
    | succ l ih =>
        intro j x
        rw [chainComp_apply_succ, ih j x, chainCompOfAddEq_snoc]
  intro l j x
  rw [lemmaA (l + 1) j x]
  rw [chainCompOfAddEq_apply_succ]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.chainComp_coe_head then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.chainComp_coe_head"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.chainComp_coe_head ``Submission.DifferentialGeometry.CheegerGromovCompactness.chainComp_coe_head

end Chain

end CheegerGromovCompactness
end DifferentialGeometry
