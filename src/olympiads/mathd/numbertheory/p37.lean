
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

theorem mathd_numbertheory_37 :
  (nat.lcm 9999 100001) = 90900909 :=
begin
 let e : empty → fin 1 → ℕ := λ _, 1,
  have : fintype.card (fin 1) = 1 := fintype.card_fin 1,
  unfold nat.lcm,
  have : fintype.card (fin 1) = 1 := fintype.card_fin 1,
  simp only [eq_comm] at this,
  rw this,
  simp [bit1],
  norm_num,
end