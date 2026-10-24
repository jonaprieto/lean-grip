/-
Copyright (c) 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Prieto-Cubides
-/
import Grip

/-! Checks for `Grip.Modality`, run at elaboration by `lake build Test`. -/

-- #guard truth-table checks for sup, inf, ite
#guard (Modality.sup never  always   == always)
#guard (Modality.sup always never    == always)
#guard (Modality.sup never  possibly == possibly)
#guard (Modality.sup possibly never  == possibly)
#guard (Modality.sup never  never    == never)
#guard (Modality.sup always always   == always)

#guard (Modality.inf never  always   == never)
#guard (Modality.inf always never    == never)
#guard (Modality.inf always always   == always)
#guard (Modality.inf possibly always == possibly)
#guard (Modality.inf always possibly == possibly)
#guard (Modality.inf never  never    == never)
#guard (Modality.inf possibly possibly == possibly)

#guard (Modality.ite always never  always == never)
#guard (Modality.ite never  never  always == always)
#guard (Modality.ite possibly never  always  == possibly)
#guard (Modality.ite possibly never  never   == never)
#guard (Modality.ite possibly always always  == always)
#guard (Modality.ite possibly possibly possibly == possibly)
