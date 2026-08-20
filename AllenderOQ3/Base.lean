import AllenderOQ3.Model
import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.Cases
import Mathlib.Order.Atoms
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.LinearCombination
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Shared Mathlib base for the internal development

`AllenderOQ3/Model.lean` carries only the handful of Mathlib modules its
statements need, so that the trusted challenge file stays small.  The internal
development needs more of the library; instead of every file importing all of
Mathlib, the extra modules are listed once here and every internal file reaches
them through this module.  Adding a new library dependency is therefore a
one-line change in a single place, and a clean build compiles only the part of
Mathlib the project actually uses.
-/
