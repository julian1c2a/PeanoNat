import PeanoNatLib.PeanoNatAxioms
import PeanoNatLib.PeanoNatStrongOrder

open Peano
namespace Peano

    /--! def Λ(n : Nat) : ℕ₀  de_Nat_a_Pea
         def Ψ(n : ℕ₀) : Nat  de_Pea_a_Nat !--/
    def max (n m : ℕ₀) : ℕ₀ :=
        match n, m with
        | 𝟘 , _ => m
        | _ , 𝟘 => n
        | σ n' , σ m' =>
            if n' = m' then
                σ n'
            else if BLt n' m' then
                σ m'
            else
                σ n'

    /--! def Λ(n : Nat) : ℕ₀  de_Nat_a_Pea
         def Ψ(n : ℕ₀) : Nat  de_Pea_a_Nat !--/
    def min (n m : ℕ₀) : ℕ₀ :=
        match n, m with
        | 𝟘 , _ => 𝟘
        | _ , 𝟘 => 𝟘
        | σ n' , σ m' =>
            if n' = m' then
                σ n'
            else if BLt n' m' then
                σ n'
            else
                σ m'

    /--! def Λ(n : Nat) : ℕ₀  de_Nat_a_Pea
         def Ψ(n : ℕ₀) : Nat  de_Pea_a_Nat !--/
    def min_max (n m : ℕ₀) : ℕ₀×ℕ₀ :=
        match n, m with
        | 𝟘 , m => (𝟘 , m)
        | n , 𝟘 => (𝟘 , n)
        | σ n' , σ m' =>
            if n' = m' then
                (σ n' , σ n')
            else if BLt n' m' then
                (σ n' , σ m')
            else
                (σ m' , σ n')

    /--
        A PROBAR AÚN SOBRE MIN Y MAX:
        1,2) SON CONMUTATIVAS
        3,4) SON ASOCIATIVAS
        5,6) SON IDEMPOTENCIAS
        7) SON DISTRIBUTIVAS EL MIN RESPECTO EL MAX
        8) SON DISTRIBUTIVAS EL MAX RESPECTO EL MIN
        9) EL CERO ES ABSORBENTE DEL MIN
        10) EL CERO ES NEUTRO DEL MAX
        11,12,13,14) ISOMORFISMO CON NAT Y MAX Y MIN
        15,16) SON DECIDIBLES
    -/

    theorem max_comm(n m : ℕ₀) :
        max n m = max m n
            := by
                induction n generalizing m with
                | zero =>
                    cases m with
                    | zero =>
                        rfl
                    | succ m' =>
                        simp [max] -- Modificado para usar simp
                | succ n' ih_n' => -- ih_n' no se usa explícitamente en esta prueba particular
                    cases m with
                    | zero =>
                        simp [max] -- Modificado para usar simp
                    | succ m' =>
                        simp only [max, eq_comm] -- Expande max y normaliza n'=m' vs m'=n'
                        -- El objetivo se convierte en:
                        -- ite (n' = m') (σ n') (ite (BLt n' m' = true) (σ m') (σ n')) =
                        -- ite (n' = m') (σ m') (ite (BLt m' n' = true) (σ n') (σ m'))
                        -- Nota: si n' = m', entonces σ n' = σ m', por lo que la primera parte es consistente.

                        split_ifs with h_eq h_nm_lt_m h_mn_lt_n
                        -- Esto genera múltiples subobjetivos basados en las condiciones.
                        -- h_eq será (n' = m') o (n' ≠ m')
                        -- h_nm_lt_m será (BLt n' m' = true) o (BLt n' m' = false)
                        -- h_mn_lt_n será (BLt m' n' = true) o (BLt m' n' = false)

                        -- Subobjetivo 1: Asume h_eq : (n' = m')
                        · simp [h_eq] -- Ambos lados se simplifican a (σ n') o (σ m'). Con h_eq, son iguales.

                        -- Subobjetivo 2: Asume h_eq : (n' ≠ m'), h_nm_lt_m : (BLt n' m' = true)
                        · simp [h_eq, h_nm_lt_m] -- El lado izquierdo (LHS) se simplifica a (σ m').
                                                        -- El lado derecho (RHS) se simplifica a ite (BLt m' n' = true) (σ n') (σ m').
                          -- Necesitamos demostrar que BLt m' n' = false.
                          have h_lt_nm : Lt n' m' := (BLt_iff_Lt n' m').mp h_nm_lt_m
                          have h_not_lt_mn : ¬ Lt m' n' := lt_asymm n' m' h_lt_nm
                          have h_blt_mn_false : BLt m' n' = false := by rw [BLt_iff_Lt]; exact h_not_lt_mn
                          simp [h_blt_mn_false] -- Con esto, el RHS también se simplifica a (σ m').

                        -- Subobjetivo 3: Asume h_eq : (n' ≠ m'),
                        --                   h_nm_lt_m : (BLt n' m' = false),
                        --                   h_mn_lt_n : (BLt m' n' = true)
                        · simp [h_eq, h_nm_lt_m, h_mn_lt_n] -- LHS -> σ n'. RHS -> σ n'. Se resuelve por simp.

                        -- Subobjetivo 4: Asume h_eq : (n' ≠ m'),
                        --                   h_nm_lt_m : (BLt n' m' = false),
                        --                   h_mn_lt_n : (BLt m' n' = false)
                        · simp [h_eq, h_nm_lt_m, h_mn_lt_n] -- LHS -> σ n'. RHS -> σ m'. Objetivo: σ n' = σ m'.
                          -- Las hipótesis implican una contradicción:
                          -- h_eq significa n' ≠ m'.
                          -- h_nm_lt_m significa ¬ (Lt n' m').
                          -- h_mn_lt_n significa ¬ (Lt m' n').
                          -- Por lt_nor_gt_then_eq, esto implica n' = m', lo cual contradice h_eq.
                          have h_not_lt_nm : ¬ Lt n' m' := by rw [BLt_iff_Lt]; exact h_nm_lt_m
                          have h_not_lt_mn : ¬ Lt m' n' := by rw [BLt_iff_Lt]; exact h_mn_lt_n
                          have h_eq_from_trichotomy : n' = m' := lt_nor_gt_then_eq n' m' ⟨h_not_lt_nm, h_not_lt_mn⟩
                          exact (h_eq h_eq_from_trichotomy).elim -- Usa la contradicción para cerrar la meta.



end Peano
