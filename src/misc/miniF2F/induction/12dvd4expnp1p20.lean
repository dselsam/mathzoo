
-- #mathlib 2022-02-03 30a731ca565b92955e40274652f4c2b6f4db79f4
/-
Copyright (c) 2021 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kunhao Zheng, Stanislas Polu, David Renshaw, OpenAI GPT-f
-/
import imports.olympiad_core

open_locale big_operators
open_locale real
open_locale nat
open_locale topological_space

theorem induction_12dvd4expnp1p20
  (n : ℕ) :
  12 ∣ 4^(n+1) + 20 :=
begin
  have dvd_of_dvd_add_mul_left : ∀ (a b n : ℕ), a ∣ b + a * n → a ∣ b :=
  begin
    intros a b n,
    refine (nat.dvd_add_left _).mp,
    exact (dvd_mul_right a n),
  end,
  induction n with k IH,
  { dec_trivial },
  {
    rw pow_succ,
    -- If we add 60 to RHS, then we can factor the 4 to use IH
    apply dvd_of_dvd_add_mul_left 12 (4 * 4 ^ k.succ + 20) 5,
    exact dvd_mul_of_dvd_right IH 4,
  }
end