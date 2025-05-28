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

  def substract (n m : ℕ₀) (h : Le m n) : ℕ₀ :=
    match n, m with
    | k, 𝟘 => k
    | 𝟘, σ m' =>
      False.elim (
        succ_neq_zero m' (le_zero_eq (σ m') h)
      )
    | σ n_s, σ m_s =>
      substract n_s m_s (le_of_succ_le_succ h)
  termination_by n

  infix:50 "-" => substract

  theorem substract_zero (n : PeanoNat) : substract n zero (le_zero n) = n := by
    induction n with
    | zero => simp [substract, le_zero]
    | succ n' ih => simp [substract]

  theorem substract_eq_zero (n m : PeanoNat) (h : m <= n) : substract n m h = zero → n = m := by
    induction n generalizing m with
    | zero => intro h_sub_eq_zero; cases m with | zero => rfl | succ m' => have h_m_eq_zero := le_n_zero_eq_zero (succ m') h; exact False.elim (succ_neq_zero m' h_m_eq_zero)
    | succ n' ih_n' =>
      intro h_sub_eq_zero; cases m with
      | zero =>
        -- substract (succ n') zero (le_zero (succ n')) = succ n' by substract_zero
        have : substract (succ n') zero (le_zero (succ n')) = succ n' := substract_zero (succ n')
        have h_succ_n'_eq_zero : succ n' = zero := by
          rw [←h_sub_eq_zero]
          exact this.symm
        exact False.elim (succ_neq_zero n' h_succ_n'_eq_zero)
      | succ m' => have h' : m' <= n' := le_of_succ_le_succ h; unfold substract at h_sub_eq_zero; have h_n'_eq_m' := ih_n' m' h' h_sub_eq_zero; exact congrArg succ h_n'_eq_m'

  theorem substract_succ (n k : PeanoNat) (h_le : k <= succ n) : substract (succ n) k h_le = match k with | zero => succ n | succ k' => substract n k' (le_of_succ_le_succ h_le) := by
    cases k with
    | zero =>
      unfold substract
      rfl
    | succ k' =>
      simp [substract]

  theorem substract_k_add_k (n: PeanoNat): ∀ (k : PeanoNat) (h_le : k <= n), add (substract n k h_le) k = n := by
    intro k h_le
    induction n generalizing k with
    | zero =>
      have h_k_eq_zero : k = zero := le_n_zero_eq_zero k h_le
      subst h_k_eq_zero
      simp [substract, add]
    | succ n' ih =>
      cases k with
      | zero =>
        simp [substract, add]
      | succ k' =>
        simp only [substract_succ, add_succ]
        let h_le' := le_of_succ_le_succ h_le
        specialize ih k' h_le'
        rw [ih]


end Sub
end Peano

--export Peano.Sub (

--)
