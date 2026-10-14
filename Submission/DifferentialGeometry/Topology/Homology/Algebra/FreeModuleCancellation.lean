/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Dimension.Constructions

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry

theorem nonempty_linearEquiv_of_prod_equiv_of_pid
    {R M N P : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P]
    [Module.Free R M] [Module.Finite R M] [Module.Free R P] [Module.Finite R P]
    (e : (M × N) ≃ₗ[R] (M × P)) : Nonempty (N ≃ₗ[R] P) := by
  let _ : Module.Free R (M × N) := Module.Free.of_equiv e.symm
  let _ : Module.Finite R (M × N) := Module.Finite.equiv e.symm
  let _ : Module.Finite R N := Module.Finite.of_surjective (LinearMap.snd R M N)
    (fun n => ⟨(0, n), rfl⟩)
  let _ : Module.IsTorsionFree R N :=
    Function.Injective.moduleIsTorsionFree (fun n : N => ((0 : M), n))
      (fun _ _ h => congrArg Prod.snd h) (fun r n => by simp)
  let _ : Module.Free R N := inferInstance
  exact ⟨LinearEquiv.ofFinrankEq N P (by simpa using e.finrank_eq)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.nonempty_linearEquiv_of_prod_equiv_of_pid then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.nonempty_linearEquiv_of_prod_equiv_of_pid"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.nonempty_linearEquiv_of_prod_equiv_of_pid ``Submission.DifferentialGeometry.nonempty_linearEquiv_of_prod_equiv_of_pid

end DifferentialGeometry
