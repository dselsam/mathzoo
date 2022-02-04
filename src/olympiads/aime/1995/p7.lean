
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

axiom aime_1995_p7
  (k m n : ℕ+)
  (t : ℝ)
  (h0 : nat.gcd m n = 1)
  (h1 : (1 + real.sin t) * (1 + real.cos t) = 5/4)
  (h2 : (1 - real.sin t) * (1- real.cos t) = m/n - real.sqrt k):
  k + m + n = 27 