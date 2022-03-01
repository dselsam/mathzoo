/-
Copyright (c) 2021 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kunhao Zheng and Stanislas Polu and David Renshaw and OpenAI GPT-f
-/
import mathzoo.imports.miniF2F

open_locale nat rat real big_operators topological_space

theorem algebra_2complexrootspoly_xsqp49eqxp7itxpn7i
  (x : ℂ) :
  x^2 + 49 = (x + (7 * complex.I)) * (x + (-7 * complex.I)) :=
begin
  ring_nf,
  ring_nf,
  rw [pow_two, pow_two, complex.I_mul_I],
  ring,
end