import PeanoNatLib.PeanoNatAxioms

import PeanoNatLib.PeanoNatStrictOrder

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
        1) A != B => MAX(A,B) = A XOR MAX(A,B) = B
        2) A != B => MIN(A,B) = A XOR MIN(A,B) = B
        3) MAX(A,A) = A
        4) MIN(A,A) = A
        5) MAX(A,B) = A OR MAX(A,B) = B
        6) MIN(A,B) = A OR MIN(A,B) = B
        7,8) SON CONMUTATIVAS
        9,10) SON ASOCIATIVAS

        11) SON DISTRIBUTIVAS EL MIN RESPECTO EL MAX
        12) SON DISTRIBUTIVAS EL MAX RESPECTO EL MIN
        13) EL CERO ES ABSORBENTE DEL MIN
        14) EL CERO ES NEUTRO DEL MAX
        15,16,17,18) ISOMORFISMO CON NAT Y MAX Y MIN
        19,20) SON DECIDIBLES
    -/

theorem max_idem(n : ℕ₀) : max n n = n := by
  induction n with
  | zero =>
    simp [max]
  | succ n' n_ih =>
    simp [max]

theorem min_idem(n : ℕ₀) : min n n = n := by
  induction n with
  | zero =>
    simp [min]
  | succ n' n_ih =>
    simp [min]

theorem min_abs_0(n : ℕ₀) : min 𝟘 n = 𝟘 := by
  induction n with
  | zero =>
    simp [min]
  | succ n' n_ih =>
    simp [min]

theorem min_0_abs(n : ℕ₀) : min n 𝟘 = 𝟘 := by
  induction n with
  | zero =>
    simp [min]
  | succ n' n_ih =>
    simp [min]

theorem max_not_0(n : ℕ₀) : max 𝟘 n = n := by
  induction n with
  | zero =>
    simp [max]
  | succ n' n_ih =>
    simp [max]

theorem max_0_not(n : ℕ₀) : max n 𝟘 = n := by
  induction n with
  | zero =>
    simp [max]
  | succ n' n_ih =>
    simp [max]

theorem eq_max_min_then_eq(n m : ℕ₀) :
    (max n m = min n m) → (n = m)
        := by
    by_cases h_eq_or_neq : (n = m)
    · -- Caso n = m.
      intro h_hyp
      exact h_eq_or_neq
    · -- Caso n ≠ m.
      intro h_max_eq_min_hyp
      exfalso
      cases n with
      | zero =>
        cases m with
        | zero =>
            apply h_eq_or_neq
            rfl
        | succ m' =>
          simp [max, min] at h_max_eq_min_hyp
      | succ n' =>
          cases m with
        | zero =>
          simp [max, min] at h_max_eq_min_hyp
        | succ m' =>
          have h_neq_preds : n' ≠ m' := by
            intro h_preds_eq_contra
            apply h_eq_or_neq
            rw [h_preds_eq_contra]
          simp [max, min, if_neg h_neq_preds] at h_max_eq_min_hyp
          by_cases h_blt_eval : BLt n' m'
          · -- Caso BLt n' m' = true
            simp [h_blt_eval] at h_max_eq_min_hyp
            have h_preds_eq_from_hyp : m' = n' :=
              h_max_eq_min_hyp
            exact h_neq_preds (Eq.symm h_preds_eq_from_hyp)
          · -- Caso BLt n' m' = false
            simp [h_blt_eval] at h_max_eq_min_hyp
            have h_preds_eq_from_sigma_inj : n' = m' :=
              h_max_eq_min_hyp
            exact h_neq_preds h_preds_eq_from_sigma_inj

theorem eq_args_eq_max_min(n m : ℕ₀) :
    n = m ↔ (max n m = min n m)
        := by
    constructor
    · -- Dirección: n = m → max n m = min n m
      intro h_eq_args
      rw [h_eq_args]
      -- El objetivo ahora es: max m m = min m m
      -- Para demostrar max m m = min m m,
      --    hacemos un análisis por casos sobre m.
      cases m with
      | zero =>
      -- Caso m = 𝟘. El objetivo es max 𝟘 𝟘 = min 𝟘 𝟘.
        -- Por definición, max 𝟘 𝟘 se simplifica a 𝟘.
        -- Por definición, min 𝟘 𝟘 se simplifica a 𝟘.
        -- Entonces el objetivo se convierte en 𝟘 = 𝟘.
        simp [max, min]
      | succ m' =>
      -- Caso m = σ m'.
        -- El objetivo es max (σ m') (σ m') = min (σ m') (σ m').
        -- Por definición, max (σ m') (σ m') se simplifica a σ m'.
        -- (ya que if m' = m' then σ m' else ... se evalúa a σ m')
        -- Por definición, min (σ m') (σ m') se simplifica a σ m'.
        -- (ya que if m' = m' then σ m' else ... se evalúa a σ m')
        -- Entonces el objetivo se convierte en σ m' = σ m'.
        simp [max, min]
    · -- Dirección: max n m = min n m → n = m
      intro h_max_eq_min
      -- Hipótesis: max n m = min n m
      -- Objetivo: n = m
      -- Prueba por casos sobre n y m.
      cases n with
      | zero =>
      -- Caso n = 𝟘
        cases m with
        | zero =>
        -- Caso m = 𝟘. Objetivo: 𝟘 = 𝟘.
          rfl
        | succ m' =>
        -- Caso m = σ m'. Objetivo: 𝟘 = σ m'.
          -- h_max_eq_min es: max 𝟘 (σ m') = min 𝟘 (σ m')
          -- Simplificando con las definiciones de max y min: σ m' = 𝟘.
          -- Esto es una contradicción con Peano.no_succ_eq_zero.
          -- Desde una contradicción (False),
          --   podemos probar cualquier cosa.
          exfalso
          -- Indica que probaremos False.
          simp [max, min] at h_max_eq_min
          -- h_max_eq_min se convierte en σ m' = 𝟘
          -- y esto cierra el objetivo False.
      | succ n' =>
      -- Caso n = σ n'
        cases m with
        | zero =>
        -- Caso m = 𝟘. Objetivo: σ n' = 𝟘.
          -- h_max_eq_min es: max (σ n') 𝟘 = min (σ n') 𝟘
          -- Simplificando: σ n' = 𝟘.
          -- Contradicción.
          exfalso
          simp [max, min] at h_max_eq_min
          -- h_max_eq_min se convierte en σ n' = 𝟘
          -- y esto cierra el objetivo False.
        | succ m' => -- Caso n = σ n', m = σ m'. Objetivo: σ n' = σ m'.
          -- Por la inyectividad de σ (ℕ₀.succ.inj),
          --   esto es equivalente a n' = m'.
          -- Cambiamos el objetivo actual (σ n' = σ m') a (n' = m').
          -- Si podemos probar n' = m',
          --   entonces σ n' = σ m' se sigue por congrArg.
          suffices h_preds_eq_goal : n' = m' by
            exact congrArg ℕ₀.succ h_preds_eq_goal

          -- Nuevo objetivo: n' = m'.
          -- h_max_eq_min es: max (σ n') (σ m') = min (σ n') (σ m')
          -- Probaremos n' = m' por casos,
          --   buscando una contradicción si n' ≠ m'.
          by_cases h_eq_or_neq : (n' = m')
          · -- Caso n' = m'. El objetivo (n' = m')
            --   se cumple directamente.
            exact h_eq_or_neq
          · -- Caso n' ≠ m'.
            -- h_eq_or_neq es la prueba de n' ≠ m'.
            -- El objetivo actual es n' = m'. Como hemos asumido n' ≠ m',
            -- debemos derivar una contradicción (False) para cerrar esta rama.
            exfalso -- Cambia el objetivo a False.

            -- Ya no se necesita renombrar h_eq_or_neq. Usaremos h_eq_or_neq directamente.
            -- Con n' ≠ m', h_max_eq_min se simplifica.
            -- La parte `if n' = m' then ...` toma la rama `else`.
            have h_cond_eq :
               (if BLt n' m' then σ m' else σ n')
               =
               (if BLt n' m' then σ n' else σ m')
                  := by
                  -- Se hace la prueba más explícita para robustez.
                  dsimp [max, min] at h_max_eq_min
                  -- Cambiamos rw por simp only para aplicar la regla en ambos lados.
                  simp only [if_neg h_eq_or_neq] at h_max_eq_min -- Usamos h_eq_or_neq en lugar de h_neq_preds
                  exact h_max_eq_min

            -- Analizamos casos para el valor booleano de (BLt n' m').
            by_cases h_blt_eval : (BLt n' m')
            · -- Caso (BLt n' m') es true.
              -- h_blt_eval es (BLt n' m') = true.
              -- h_cond_eq simplificada con esto se convierte en σ m' = σ n'.
              simp only [h_blt_eval, if_true] at h_cond_eq
              have h_preds_eq : m' = n' := ℕ₀.succ.inj h_cond_eq -- Corregido AXIOM_succ_inj a ℕ₀.succ.inj
              -- Sustituimos m' por n' en h_blt_eval.
              rw [h_preds_eq] at h_blt_eval
              -- Ahora h_blt_eval es (BLt n' n') = true.
              -- Esto significa decide (Lt n' n') = true, lo que implica Lt n' n'.
              have h_lt_n_n_is_true : Lt n' n' := by {
                -- h_blt_eval tiene tipo BLt n' n' = true, que es decide (Lt n' n') = true.
                -- El objetivo es Lt n' n'.
                -- Usamos decide_eq_true_iff, que debe ser la equivalencia:
                --   decide (Lt n' n') = true ↔ Lt n' n'
                -- y aplicamos .mp a h_blt_eval.
                exact decide_eq_true_iff.mp h_blt_eval;
              }
              -- Probamos que Lt n' n' (∃k, n' = n' + σ k) es una contradicción.
              -- Esto asume que Peano.add_zero y Peano.add_left_cancel están disponibles.
              -- Si no lo están, esta parte necesitará importar lemas de adición.
              cases h_lt_n_n_is_true with
              | intro k h_sum_eq => {
                rw [← Peano.add_zero n'] at h_sum_eq;
                have h_zero_eq_sk : 𝟘 = σ k
                    := Peano.add_left_cancel _ _ _ h_sum_eq;
                exact Peano.no_succ_eq_zero (σ k) h_zero_eq_sk;
              }
            · -- Caso (BLt n' m') es false.
              -- h_blt_eval es (BLt n' m') = false.
              -- h_cond_eq simplificada con esto se convierte en σ n' = σ m'.
              simp only [h_blt_eval, if_false] at h_cond_eq
              have h_preds_eq : n' = m' := ℕ₀.succ.inj h_cond_eq -- Corregido
              -- Esto contradice directamente h_eq_or_neq : n' ≠ m'.
              exact h_eq_or_neq h_preds_eq

theorem max_is_any(n m : ℕ₀) :
    max n m = n ∨ max n m = m
        := by
        sorry

theorem min_is_any(n m : ℕ₀) :
    min n m = n ∨ min n m = m
        := by
        sorry

theorem if_neq_then_max_xor(n m : ℕ₀) :
    n ≠ m ↔
    ((max n m = n)∧¬(max n m = m))
    ∨
    (¬(max n m = n)∨(max n m = m))
        := by
        sorry

theorem if_neq_then_min_xor(n m : ℕ₀) :
    n ≠ m ↔
    ((min n m = n)∧¬(min n m = m))
    ∨
    (¬(min n m = n)∨(min n m = m))
        := by
        sorry

theorem neq_args_then_lt_min_max(n m : ℕ₀) :
    n ≠ m ↔ Lt (min n m) (max n m )
        := by
        sorry

theorem max_comm(n m : ℕ₀) :
    max n m = max m n
        := by
        sorry

theorem min_comm(n m : ℕ₀) :
    min n m = min m n
        := by
        sorry

theorem max_assoc(n m k : ℕ₀) :
    max (max n m) k = max n (max m k)
        := by
        sorry

theorem min_assoc(n m k : ℕ₀) :
    min (min n m) k = min n (min n k)
        := by
        sorry

theorem max_distrib_min(n m k : ℕ₀) :
    max n (min m k) = min (max n m) (max n k)
        := by
        sorry

theorem min_distrib_max(n m k : ℕ₀) :
    min n (max m k) = max (min n m) (min n k)
        := by
        sorry

theorem min_zero_absorb(n : ℕ₀) :
    min n 𝟘 = 𝟘
        := by
        sorry

theorem max_zero_neutral(n : ℕ₀) :
    max n 𝟘 = n
        := by
        sorry

theorem isomorph_max_Λ(n m : Nat) :
    max (Λ n) (Λ m) = Λ (Nat.max n m)
        := by
        sorry

theorem isomorph_min_Λ(n m : Nat) :
    min (Λ n) (Λ m) = Λ (Nat.min n m)
        := by
        sorry

theorem isomorph_max_Ψ(n m : ℕ₀) :
    max (Ψ n) (Ψ m) = Ψ (max n m)
        := by
        sorry

theorem isomorph_min_Ψ(n m : ℕ₀) :
    min (Ψ n) (Ψ m) = Ψ (min n m)
        := by
        sorry

end Peano
