/-
Copyright (c) 2026 Claudiu G. Pop, George C. Rad, George C. Țurcaș. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claudiu G. Pop, George C. Rad, George C. Țurcaș
-/
module

public import DavenportProject.Bases.CubeThree.Masks

/-!
# Kernel check for Lemma 5.1(2)

The finite enumeration behind Lemma 5.1(2): `checkFrom` (defined in `Masks.lean`) is evaluated by
the kernel (`decide +kernel`), one declaration per first point `a` (26 declarations).
-/

public section

namespace DavenportProject.CubeThree.Support

/-! The kernel evaluates one first point per declaration. Declarations are checked one after
another (`Elab.async false`): in parallel, each kernel evaluation holds up to about 2 GB of
cache and the machine runs out of memory. -/

set_option Elab.async false

theorem checkFrom_1 : checkFrom 1 = true := by decide +kernel
theorem checkFrom_2 : checkFrom 2 = true := by decide +kernel
theorem checkFrom_3 : checkFrom 3 = true := by decide +kernel
theorem checkFrom_4 : checkFrom 4 = true := by decide +kernel
theorem checkFrom_5 : checkFrom 5 = true := by decide +kernel
theorem checkFrom_6 : checkFrom 6 = true := by decide +kernel
theorem checkFrom_7 : checkFrom 7 = true := by decide +kernel
theorem checkFrom_8 : checkFrom 8 = true := by decide +kernel
theorem checkFrom_9 : checkFrom 9 = true := by decide +kernel
theorem checkFrom_10 : checkFrom 10 = true := by decide +kernel
theorem checkFrom_11 : checkFrom 11 = true := by decide +kernel
theorem checkFrom_12 : checkFrom 12 = true := by decide +kernel
theorem checkFrom_13 : checkFrom 13 = true := by decide +kernel
theorem checkFrom_14 : checkFrom 14 = true := by decide +kernel
theorem checkFrom_15 : checkFrom 15 = true := by decide +kernel
theorem checkFrom_16 : checkFrom 16 = true := by decide +kernel
theorem checkFrom_17 : checkFrom 17 = true := by decide +kernel
theorem checkFrom_18 : checkFrom 18 = true := by decide +kernel
theorem checkFrom_19 : checkFrom 19 = true := by decide +kernel
theorem checkFrom_20 : checkFrom 20 = true := by decide +kernel
theorem checkFrom_21 : checkFrom 21 = true := by decide +kernel
theorem checkFrom_22 : checkFrom 22 = true := by decide +kernel
theorem checkFrom_23 : checkFrom 23 = true := by decide +kernel
theorem checkFrom_24 : checkFrom 24 = true := by decide +kernel
theorem checkFrom_25 : checkFrom 25 = true := by decide +kernel
theorem checkFrom_26 : checkFrom 26 = true := by decide +kernel

end DavenportProject.CubeThree.Support
