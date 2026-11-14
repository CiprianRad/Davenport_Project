/-
Copyright (c) 2026 Claudiu G. Pop, George C. Rad, George C. Țurcaș. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claudiu G. Pop, George C. Rad, George C. Țurcaș
-/
module

public import DavenportProject.Invariants
import DavenportProject.Transfer.Olson
import DavenportProject.Transfer.TheoremA

/-!
# The Davenport constants of the cubes

`D(C_2^3) = 4`, `D(C_3^3) = 7` and `D(C_4^3) = 10`. Each is the specialization of Olson's theorem
`davenport_pi_zmod_prime_pow` to `p ^ a` with `(p, a) = (2, 1), (3, 1), (2, 2)`, transported along
`ZMod (p ^ a) ≃ ZMod m` coordinatewise. The file also records the exponent of `C_m^3`.
-/

public section

namespace DavenportProject.Bases

open Transfer (davenport_congr)

/-- Olson's theorem for `C_m^3` with `m = p ^ a`. -/
theorem davenport_cube_prime_pow (p : ℕ) [Fact p.Prime] (a m : ℕ) [NeZero m] (hm : p ^ a = m) :
    davenport (Fin 3 → ZMod m) = 1 + 3 * (m - 1) := by
  have h := davenport_pi_zmod_prime_pow p (r := 3) (fun _ => a)
  rw [davenport_congr (AddEquiv.piCongrRight fun _ => (ZMod.ringEquivCongr hm).toAddEquiv)]
    at h
  rw [h, hm]
  simp

/-- `D(C_2^3) = 4` (Olson). -/
theorem davenport_cube_two : davenport (Fin 3 → ZMod 2) = 4 := by
  rw [davenport_cube_prime_pow 2 1 2 (by norm_num)]

/-- `D(C_3^3) = 7` (Olson). -/
theorem davenport_cube_three : davenport (Fin 3 → ZMod 3) = 7 := by
  rw [davenport_cube_prime_pow 3 1 3 (by norm_num)]

/-- `D(C_4^3) = 10` (Olson). -/
theorem davenport_cube_four : davenport (Fin 3 → ZMod 4) = 10 := by
  rw [davenport_cube_prime_pow 2 2 4 (by norm_num)]

/-! ## The exponent of `C_m^3` -/

/-- The exponent of `(ZMod m)^3` is `m` (no hypothesis on `m` is needed). -/
theorem exponent_fin_three_zmod (m : ℕ) : AddMonoid.exponent (Fin 3 → ZMod m) = m := by
  rw [AddMonoid.exponent_pi]
  simp only [ZMod.exponent]
  exact Nat.dvd_antisymm (Finset.lcm_dvd fun _ _ => dvd_rfl)
    (Finset.dvd_lcm (s := Finset.univ) (f := fun _ : Fin 3 => m) (Finset.mem_univ 0))

end DavenportProject.Bases
