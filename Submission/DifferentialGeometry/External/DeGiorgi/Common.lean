-- Modified 2026-04-28: updated internal import paths for project namespace
import Mathlib

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-!
# Common Prelude

This module is the shared prelude for the De Giorgi development.

Policy:

- imports come directly from `Mathlib`;
- declarations in this directory live under `DeGiorgi`;
- shared opens and scoped notations live here so the theorem files stay small.
-/

noncomputable section

open _root_.MeasureTheory
open scoped _root_.NNReal

namespace DeGiorgi

end DeGiorgi
