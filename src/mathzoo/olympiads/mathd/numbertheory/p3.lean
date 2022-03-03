/-
Copyright (c) 2021 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kunhao Zheng, Stanislas Polu, David Renshaw, OpenAI GPT-f
-/
import mathzoo.imports.miniF2F

open_locale nat rat real big_operators topological_space

theorem mathd_numbertheory_3 :
  (∑ x in finset.range 10, ((x + 1)^2)) % 10 = 5 :=
begin
  dec_trivial!,
end