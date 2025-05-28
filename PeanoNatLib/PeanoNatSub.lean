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
    | σ n', σ m' =>
      --substract n' m' (le_of_succ_le_succ n' m')
      sorry
  --termination_by n

  infix:50 "-" => substract

  theorem substract_zero (n : ℕ₀) :
    substract n 𝟘 (zero_le n) = n
      := by sorry

  theorem substract_eq_zero (n m : ℕ₀) (h : m <= n) :
      substract n m h = 𝟘 → n = m
          := by sorry

  theorem substract_succ (n k : ℕ₀) (h_le : k <= σ n) :
     substract (σ n) k h_le =
       match k with
       | zero => σ n
       | succ k' => substract n k' (le_of_succ_le_succ h_le)
       := by sorry

  theorem substract_k_add_k (n: ℕ₀): ∀ (k : ℕ₀) (h_le : k <= n), add (substract n k h_le) k = n := by
    sorry


end Sub
end Peano

--export Peano.Sub (

--)
