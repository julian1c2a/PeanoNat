import PeanoNatLib.PeanoNatLib
import PeanoNatLib.PeanoNatAxioms
import PeanoNatLib.PeanoNatStrictOrder
import PeanoNatLib.PeanoNatOrder
import PeanoNatLib.PeanoNatMaxMin
import PeanoNatLib.PeanoNatAdd

namespace Peano
    open Peano
    open Peano.Axioms
    open Peano.StrictOrder
    open Peano.Order
    open Peano.MaxMin
    open Peano.Add

    namespace Sub
        open Peano.Sub

  def sub_chk (n m : ℕ₀) (h : Le m n) : ℕ₀ :=
    match n, m with
    | k, 𝟘 => k
    | 𝟘, σ m' =>
      False.elim (
        succ_neq_zero m' (le_zero_eq (σ m') h)
      )
    | σ n', σ m' =>
      sub_chk n' m' (succ_le_succ_then h)
  termination_by n

  def sub (n m : ℕ₀) : ℕ₀ :=
    if h: Le m n then
      sub_chk n m h
    else
      𝟘


  theorem sub_zero (n : ℕ₀) :
    sub_chk n 𝟘 (zero_le n) = n
      := by
    induction n with
    | zero =>
      calc
        sub_chk 𝟘 𝟘 (zero_le 𝟘) = 𝟘 := by rw [sub_chk]
        _ = 𝟘 := rfl
    | succ n' ih =>
      calc
        sub_chk (σ n') 𝟘 (zero_le (σ n')) = σ n'
            := by rw [sub_chk]
        _ = σ n' := rfl

  theorem sub_eq_zero (n m : ℕ₀) (h : m <= n) :
      sub_chk n m h = 𝟘 → n = m
          := by
      induction m generalizing n with
      | zero =>
        intro h_eq
        have h_n_eq_0 : n = 𝟘 := by
          calc
            n = sub_chk n 𝟘 (zero_le n) := by rw [sub_zero]
            _ = 𝟘 := h_eq
        simp [ h_n_eq_0 , h_eq ]
      | succ m' ih =>
        intro h_eq
        cases n with
        | zero =>
          exfalso
          have h_succ_le_zero : σ m' <= 𝟘 := h
          exact not_succ_le_zero  m' h_succ_le_zero
        | succ n' =>
          have h_le' : m' <= n' := succ_le_succ_then h
          have h_eq' : sub_chk n' m' h_le' = 𝟘 := by
            rw [← h_eq]
            simp [sub_chk]
          have h_n'_eq_m' : n' = m' := ih n' h_le' h_eq'
          rw [h_n'_eq_m']

--  theorem sub_succ (n k : ℕ₀) :
--     sub (σ n) k = σ (sub n k)
--      := by
--       match k with
--        | 𝟘 =>
--          calc
--            sub (σ n) 𝟘 = σ n := by rw [sub_zero]
--            _ = σ (sub n 𝟘) := rfl
--        | σ k' =>
--          calc
--            sub (σ n) k' = σ (sub n k') := by rw [sub_succ]
--            _ = σ (sub n (σ k')) := rfl
--        termination_by n k
--
--  k ≤ n → σ n - k = n + 1 - k
--

--  theorem substract_k_add_k (n: ℕ₀): ∀ (k : ℕ₀) (h_le : k <= n), add (substract n k h_le) k = n := by
--    sorry


end Sub
end Peano
