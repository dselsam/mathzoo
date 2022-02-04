
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

theorem induction_sumkexp3eqsumksq
  (n : ℕ) :
  ∑ k in finset.range n, k^3 = (∑ k in finset.range n, k)^2 :=
begin
  symmetry,
  induction n with j IH,
  {
    refl,
  },
  {
    calc (∑ (k : ℕ) in finset.range j.succ, k)^2 = ((∑ (k : ℕ) in finset.range j, k) + j)^2 : by rw finset.sum_range_succ
   ... = (∑ (k : ℕ) in finset.range j, k)^2 + 2 * (∑ (k : ℕ) in finset.range j, k) * j + j^2 : by rw add_sq _ _
   ... = (∑ (k : ℕ) in finset.range j, k)^2 +  (∑ (k : ℕ) in finset.range j, k) * 2 * j + j^2 : by ring
   ... = (∑ (k : ℕ) in finset.range j, k)^2 + (j * (j-1)) * j + j^2 : by rw finset.sum_range_id_mul_two j
   ... = (∑ (k : ℕ) in finset.range j, k^3) + (j * (j-1)) * j + j^2 : by rw IH
   ... = (∑ (k : ℕ) in finset.range j, k^3) + j^2 * (j-1) + j^2 : by ring_nf
   ... = (∑ (k : ℕ) in finset.range j, k^3) + j^3 : by cases j ; [norm_num, ring_nf]
   ... = (∑ (k : ℕ) in finset.range j.succ, k^3) : by rw ← finset.sum_range_succ,
  }
end