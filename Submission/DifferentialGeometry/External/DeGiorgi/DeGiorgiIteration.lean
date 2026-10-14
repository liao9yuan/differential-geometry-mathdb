-- Modified 2026-04-28: updated internal import paths for project namespace
import Submission.DifferentialGeometry.External.DeGiorgi.DeGiorgiIteration.Linfty

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-!
# Chapter 05: De Giorgi Theory

This module re-exports the cutoff-admissibility, energy, pre-iteration,
recurrence, and `L^∞` layers of the De Giorgi iteration argument.
-/
