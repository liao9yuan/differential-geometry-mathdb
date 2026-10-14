import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.Topology

open _root_.Path

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x : X}

noncomputable def loopPow (p : Path x x) : ℕ → Path x x
  | 0 => Path.refl x
  | k + 1 => p.trans (loopPow p k)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.loopPow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.loopPow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.loopPow ``Submission.DifferentialGeometry.Topology.loopPow

noncomputable def loopZPow (p : Path x x) : ℤ → Path x x
  | Int.ofNat k => loopPow p k
  | Int.negSucc k => loopPow p.symm (k + 1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.loopZPow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.loopZPow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.loopZPow ``Submission.DifferentialGeometry.Topology.loopZPow

theorem loopPow_zero (p : Path x x) : loopPow p 0 = Path.refl x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.loopPow_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.loopPow_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.loopPow_zero ``Submission.DifferentialGeometry.Topology.loopPow_zero

theorem loopPow_succ (p : Path x x) (k : ℕ) :
    loopPow p (k + 1) = p.trans (loopPow p k) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.loopPow_succ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.loopPow_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.loopPow_succ ``Submission.DifferentialGeometry.Topology.loopPow_succ

theorem loopZPow_natCast (p : Path x x) (k : ℕ) : loopZPow p (k : ℤ) = loopPow p k := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.loopZPow_natCast then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.loopZPow_natCast"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.loopZPow_natCast ``Submission.DifferentialGeometry.Topology.loopZPow_natCast

theorem loopZPow_negSucc (p : Path x x) (k : ℕ) :
    loopZPow p (Int.negSucc k) = loopPow p.symm (k + 1) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.loopZPow_negSucc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.loopZPow_negSucc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.loopZPow_negSucc ``Submission.DifferentialGeometry.Topology.loopZPow_negSucc

theorem refl_map {f : X → Y} (hf : Continuous f) (a : X) :
    (Path.refl a).map hf = Path.refl (f a) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.refl_map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.refl_map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.refl_map ``Submission.DifferentialGeometry.Topology.refl_map

theorem symm_map (p : Path x x) {f : X → Y} (hf : Continuous f) :
    p.symm.map hf = (p.map hf).symm := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.symm_map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.symm_map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.symm_map ``Submission.DifferentialGeometry.Topology.symm_map

theorem loopPow_map (p : Path x x) {f : X → Y} (hf : Continuous f) (k : ℕ) :
    (loopPow p k).map hf = loopPow (p.map hf) k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [loopPow_succ, Path.map_trans, ih, loopPow_succ]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.loopPow_map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.loopPow_map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.loopPow_map ``Submission.DifferentialGeometry.Topology.loopPow_map

theorem loopZPow_map (p : Path x x) {f : X → Y} (hf : Continuous f) (k : ℤ) :
    (loopZPow p k).map hf = loopZPow (p.map hf) k := by
  cases k with
  | ofNat k => exact loopPow_map p hf k
  | negSucc k => rw [loopZPow_negSucc, loopPow_map, symm_map, loopZPow_negSucc]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.loopZPow_map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.loopZPow_map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.loopZPow_map ``Submission.DifferentialGeometry.Topology.loopZPow_map

theorem loopPow_homotopic {p q : Path x x} (h : p.Homotopic q) (k : ℕ) :
    (loopPow p k).Homotopic (loopPow q k) := by
  induction k with
  | zero => exact Path.Homotopic.refl _
  | succ k ih => exact h.hcomp ih

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.loopPow_homotopic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.loopPow_homotopic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.loopPow_homotopic ``Submission.DifferentialGeometry.Topology.loopPow_homotopic

theorem loopZPow_homotopic {p q : Path x x} (h : p.Homotopic q) (k : ℤ) :
    (loopZPow p k).Homotopic (loopZPow q k) := by
  cases k with
  | ofNat k => exact loopPow_homotopic h k
  | negSucc k => exact loopPow_homotopic h.symm₂ (k + 1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.loopZPow_homotopic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.loopZPow_homotopic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.loopZPow_homotopic ``Submission.DifferentialGeometry.Topology.loopZPow_homotopic

theorem cast_rfl (p : Path x x) : p.cast rfl rfl = p := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.cast_rfl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.cast_rfl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.cast_rfl ``Submission.DifferentialGeometry.Topology.cast_rfl

theorem loopPow_cast {y : X} (p : Path x x) (hx : y = x) (k : ℕ) :
    (loopPow p k).cast hx hx = loopPow (p.cast hx hx) k := by
  cases hx
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.loopPow_cast then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.loopPow_cast"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.loopPow_cast ``Submission.DifferentialGeometry.Topology.loopPow_cast

theorem loopZPow_cast {y : X} (p : Path x x) (hx : y = x) (k : ℤ) :
    (loopZPow p k).cast hx hx = loopZPow (p.cast hx hx) k := by
  cases hx
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.loopZPow_cast then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.loopZPow_cast"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.loopZPow_cast ``Submission.DifferentialGeometry.Topology.loopZPow_cast

theorem fromPath_loopPow (p : Path x x) (k : ℕ) :
    (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (loopPow p k)) :
        FundamentalGroup X x) =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p) ^ k := by
  induction k with
  | zero => exact (FundamentalGroup.one_def (x := x)).symm
  | succ k ih =>
      change (Path.Homotopic.Quotient.mk (p.trans (loopPow p k)) : FundamentalGroup X x) = _
      rw [Path.Homotopic.Quotient.mk_trans, pow_succ, ← ih, FundamentalGroup.mul_def]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.fromPath_loopPow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.fromPath_loopPow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.fromPath_loopPow ``Submission.DifferentialGeometry.Topology.fromPath_loopPow

theorem fromPath_symm (p : Path x x) :
    (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p.symm) : FundamentalGroup X x) =
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p))⁻¹ :=
  (FundamentalGroup.inv_def (p := FundamentalGroup.fromPath
    (Path.Homotopic.Quotient.mk p))).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.fromPath_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.fromPath_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.fromPath_symm ``Submission.DifferentialGeometry.Topology.fromPath_symm

theorem fromPath_loopZPow (p : Path x x) (k : ℤ) :
    (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (loopZPow p k)) :
        FundamentalGroup X x) =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p) ^ k := by
  cases k with
  | ofNat k =>
      have hk : (Int.ofNat k) = (k : ℤ) := rfl
      rw [hk, loopZPow_natCast, fromPath_loopPow, zpow_natCast]
  | negSucc k =>
      rw [loopZPow_negSucc, fromPath_loopPow, fromPath_symm, zpow_negSucc, inv_pow]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.fromPath_loopZPow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.fromPath_loopZPow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.fromPath_loopZPow ``Submission.DifferentialGeometry.Topology.fromPath_loopZPow

theorem exists_homotopic_loopZPow_of_homeomorph (h : X ≃ₜ Y) {p : Path x x}
    (hgen : ∀ ℓ : Path x x, ∃ k : ℤ, ℓ.Homotopic (loopZPow p k))
    (m : Path (h x) (h x)) :
    ∃ k : ℤ, m.Homotopic (loopZPow (p.map h.continuous) k) := by
  have hx : x = h.symm (h x) := (h.symm_apply_apply x).symm
  obtain ⟨k, hk⟩ := hgen ((m.map h.symm.continuous).cast hx hx)
  refine ⟨k, ?_⟩
  have hmap := hk.map (h : C(X, Y))
  have hleft : (((m.map h.symm.continuous).cast hx hx).map (h : C(X, Y)).continuous) = m := by
    refine Path.ext (funext fun t => ?_)
    change h (h.symm (m t)) = m t
    exact h.apply_symm_apply _
  have hright : ((loopZPow p k).map (h : C(X, Y)).continuous) =
      loopZPow (p.map h.continuous) k := loopZPow_map p (h : C(X, Y)).continuous k
  rw [hleft, hright] at hmap
  exact hmap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_homotopic_loopZPow_of_homeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_homotopic_loopZPow_of_homeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_homotopic_loopZPow_of_homeomorph ``Submission.DifferentialGeometry.Topology.exists_homotopic_loopZPow_of_homeomorph

theorem exists_homotopic_loopZPow_of_forall_exists_zpow
    {p : Path x x}
    (h : ∀ a : FundamentalGroup X x,
      ∃ k : ℤ, a = FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p) ^ k)
    (m : Path x x) : ∃ k : ℤ, m.Homotopic (loopZPow p k) := by
  obtain ⟨k, hk⟩ := h (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk m))
  refine ⟨k, Path.Homotopic.Quotient.eq.mp ?_⟩
  rw [← fromPath_loopZPow] at hk
  exact hk

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_homotopic_loopZPow_of_forall_exists_zpow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_homotopic_loopZPow_of_forall_exists_zpow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_homotopic_loopZPow_of_forall_exists_zpow ``Submission.DifferentialGeometry.Topology.exists_homotopic_loopZPow_of_forall_exists_zpow

end DifferentialGeometry.Topology
