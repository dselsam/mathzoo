
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

theorem algebra_2rootspoly_apatapbeq2asqp2ab
  (a b : ℂ) :
  (a + a) * (a + b) = 2 * a^2 + 2 * (a * b) :=
begin
  ring,
end