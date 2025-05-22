import PeanoNatLib.PeanoNatAxioms
import PeanoNatLib.PeanoNatStrictOrder
import PeanoNatLib.PeanoNatOrder
import Init.Prelude
import Init.Data.Nat.Basic
import Init.Data.Nat.Lemmas

open Peano
namespace Peano

    /--! def Λ(n : Nat) : ℕ₀  de_Nat_a_Pea
         def Ψ(n : ℕ₀) : Nat  de_Pea_a_Nat !--/
    def max (n m : ℕ₀) : ℕ₀ :=
        match n, m with
        | 𝟘 , m => m
        | n , 𝟘 => n
        | σ n' , σ m' =>
            if n' = m' then
                σ m'
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

    /--! def Λ(n : Nat) : ℕ₀  de_Nat_a_Pea
         def Ψ(n : ℕ₀) : Nat  de_Pea_a_Nat !--/
    def max_min (n m : ℕ₀) : ℕ₀×ℕ₀ :=
        match n, m with
        | 𝟘 , m => (m , 𝟘)
        | n , 𝟘 => (n , 𝟘)
        | σ n' , σ m' =>
            if n' = m' then
                (σ n' , σ n')
            else if BLt n' m' then
                (σ m' , σ n')
            else
                (σ n' , σ m')


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
    rfl
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

theorem eq_then_eq_max_min(n m : ℕ₀) :
    (n = m) → (max n m = min n m)
    := by
    intro h_eq_args
    rw [h_eq_args] -- El objetivo se convierte en: max m m = min m m
    rw [max_idem m]  -- El lado izquierdo (max m m) se convierte en m. Objetivo: m = min m m
    rw [min_idem m]  -- El lado derecho (min m m) se convierte en m. Objetivo: m = m
    -- Esto se cierra por reflexividad.

theorem eq_iff_eq_max_min(n m : ℕ₀) :
    n = m ↔ max n m = min n m
        := by
        constructor
        · -- Caso n = m → max n m = min n m
          intro h_eq_args
          exact eq_then_eq_max_min n m h_eq_args
        · -- Caso max n m = min n m → n = m
          intro h_hyp_max_eq_min
          exact eq_max_min_then_eq n m h_hyp_max_eq_min

theorem min_of_min_max(n m : ℕ₀) :
    min n m = min (max n m) (min n m)
      := by
        induction n with
        | zero =>
            induction m with
            | zero =>
                simp [min, max]
            | succ m' =>
                simp [min, max]
        | succ n' n_ih =>
            induction m with
            | zero =>
                simp [min, max]
            | succ m' =>
                by_cases h_eq_preds : (n' = m')
                · -- Caso: n' = m'
                  simp [min, max, h_eq_preds]
                · -- Caso: n' ≠ m'
                  by_cases h_blt_bool : (BLt n' m')
                  · -- Caso: BLt n' m' = true
                    have h_lt_n_prime_m_prime : Lt n' m' := by
                      rw [← BLt_iff_Lt]
                      exact h_blt_bool
                    have h_not_lt_m_prime_n_prime : ¬ (Lt m' n') := by
                      apply lt_asymm
                      exact h_lt_n_prime_m_prime
                    have h_blt_m_prime_n_prime_is_false :
                      BLt m' n' = false
                      := by
                         rw [← Bool.not_eq_true]
                         --   Meta: ¬ (BLt m' n' = true)
                         rw [BLt_iff_Lt]
                         --   Meta: ¬ (Lt m' n')
                         exact h_not_lt_m_prime_n_prime
                    simp [
                          min,
                          max,
                          h_eq_preds,
                          Ne.symm h_eq_preds,
                          h_blt_bool, h_blt_m_prime_n_prime_is_false
                    ]
                  · -- Caso: ¬ (BLt n' m')
                    simp [
                            min,
                            max,
                            h_eq_preds,
                            h_blt_bool
                    ]

theorem max_of_min_max(n m : ℕ₀) :
    max n m = max (min n m) (max n m)
      := by
        induction n with
        | zero =>
            induction m with
            | zero =>
                simp [min, max]
            | succ m' =>
                simp only [min, max]
        | succ n' n_ih =>
            induction m with
            | zero =>
                simp [min, max]
            | succ m' =>
                by_cases h_eq_preds : (n' = m')
                · -- Caso: n' = m'
                  simp [min, max, h_eq_preds]
                · -- Caso: n' ≠ m'
                  by_cases h_blt_bool : (BLt n' m')
                  · -- Caso: BLt n' m' = true
                    have h_lt_n_prime_m_prime : Lt n' m' := by
                      rw [← BLt_iff_Lt]
                      exact h_blt_bool
                    have h_not_lt_m_prime_n_prime : ¬ (Lt m' n') := by
                      apply lt_asymm
                      exact h_lt_n_prime_m_prime
                    have h_blt_m_prime_n_prime_is_false :
                      BLt m' n' = false
                      := by
                         rw [← Bool.not_eq_true]
                         rw [BLt_iff_Lt]
                         exact h_not_lt_m_prime_n_prime
                    simp [min, max, h_eq_preds, Ne.symm h_eq_preds, h_blt_bool, h_blt_m_prime_n_prime_is_false]
                  · -- Caso: ¬ (BLt n' m')
                    have h_blt_m_n_is_true : BLt m' n' = true := by
                      rcases trichotomy n' m' with h_lt_n_m | h_eq_n_m | h_lt_m_n
                      · -- Caso Lt n' m', contradice h_blt_bool
                        exfalso
                        apply h_blt_bool
                        rw [BLt_iff_Lt] -- o usa BLt_iff_Lt.mpr
                        exact h_lt_n_m
                      · -- Caso n' = m', contradice h_eq_preds
                        exfalso
                        exact h_eq_preds h_eq_n_m
                      · -- Caso Lt m' n', esto es lo que necesitamos
                        rw [BLt_iff_Lt] -- o usa BLt_iff_Lt.mpr
                        exact h_lt_m_n
                    simp [
                      min,
                      max,
                      h_eq_preds,
                      h_blt_bool,
                      h_blt_m_n_is_true
                    ]

theorem max_is_any(n m : ℕ₀) :
    max n m = n ∨ max n m = m
        := by
        cases n with
        | zero =>
          cases m with
          | zero => simp [max]
          | succ m' => simp [max]
        | succ n' =>
          cases m with
          | zero => simp [max]
          | succ m' =>
              dsimp [max]
              by_cases h_eq_cond : (n' = m')
              ·
                rw [if_pos h_eq_cond]
                left
                rw [h_eq_cond]
              ·
                rw [if_neg h_eq_cond]
                by_cases h_blt_cond : (BLt n' m')
                ·
                  rw [if_pos h_blt_cond]
                  right
                  rfl
                ·
                  rw [if_neg h_blt_cond]
                  left -- Revertido a `left`
                  rfl

theorem min_is_any(n m : ℕ₀) :
    min n m = n ∨ min n m = m
        := by
        cases n with
        | zero =>
          cases m with
          | zero => simp [min]
          | succ m' => simp [min]
        | succ n' =>
          cases m with
          | zero => simp [min]
          | succ m' =>
              dsimp [min]
              by_cases h_eq_cond : (n' = m')
              ·
                rw [if_pos h_eq_cond]
                left
                rfl
              ·
                rw [if_neg h_eq_cond]
                by_cases h_blt_cond : (BLt n' m')
                ·
                  rw [if_pos h_blt_cond]
                  left
                  rfl
                ·
                  rw [if_neg h_blt_cond]
                  right
                  rfl



theorem lt_then_min (a b : ℕ₀) :
    Lt a b → min a b = a
    := by
      intro h_lt
      cases a with
      | zero => -- a = 𝟘
        simp [min]
      | succ a' =>
        cases b with
        | zero => exfalso; exact nlt_n_0 (σ a') h_lt
        | succ b' =>
          have h_lt_a'_b' : Lt a' b' := by simp [Lt] at h_lt; exact h_lt
          have h_a'_ne_b' : a' ≠ b' := lt_then_neq a' b' h_lt_a'_b'
          simp [min, if_neg h_a'_ne_b']
          rw [(BLt_iff_Lt a' b').mpr h_lt_a'_b']
          simp

theorem min_then_le (a b : ℕ₀) :
    min a b = a → Le a b
    := by
      intro h_min_eq
      -- h_min_eq : min a b = a
      cases a with
      | zero => -- a = 𝟘
        -- Si a es cero, entonces min 𝟘 b es 𝟘 por la definición de `min`.
        -- h_min_eq se convierte en `𝟘 = 𝟘`, que es trivial.
        simp only [min] at h_min_eq -- Usamos `simp only` para ser más específicos
        -- Queremos probar `Le 𝟘 b`. Esto se cumple por el teorema `zero_le`.
        -- Usamos `exact` porque `zero_le b` ya es una prueba de `Le 𝟘 b`.
        exact zero_le b
      | succ a' =>
        -- a = σ a'
        -- Si 'a' es un sucesor, 'b' no puede ser cero. Si `b` fuera `𝟘`, entonces `min (σ a') 𝟘` sería `𝟘`.
        -- Esto haría que `h_min_eq` fuera `σ a' = 𝟘`, lo cual es una contradicción por `succ_neq_zero`.
        cases b with
        | zero =>
          exfalso
          simp only [min] at h_min_eq -- simplifica min (σ a') 𝟘 a 𝟘
          -- h_min_eq : σ a' = 𝟘. Esto es una contradicción.
          -- Usamos .symm para que la igualdad tenga la dirección esperada por `succ_neq_zero`.
          exact succ_neq_zero a' h_min_eq.symm
        | succ b' =>
          -- a = σ a' y b = σ b'.
          -- Ahora tenemos h_min_eq : min (σ a') (σ b') = σ a'.
          -- Usaremos `by_cases` para considerar si `a' = b'` o no.
          by_cases h_eq_preds : (a' = b')
          · -- Caso h_eq_preds : a' = b'
            -- Si a' = b', entonces min (σ a') (σ b') se convierte en min (σ a') (σ a').
            -- Por `min_idem`, min (σ a') (σ a') es σ a'.
            -- Esto hace que `h_min_eq` sea `σ a' = σ a'`, que es `rfl`.
            simp only [min, h_eq_preds] at h_min_eq -- h_min_eq se resuelve como `rfl`
            -- Queremos demostrar `Le (σ a') (σ b')`. Como `a' = b'`, esto es `Le (σ a') (σ a')`.
            -- Esto se cumple por la definición de `Le` y `rfl`.
            rw [h_eq_preds] -- Aplicar la igualdad al objetivo para que sea Le (σ a') (σ a')
            exact Or.inr rfl -- Le X X es X = X, que es rfl.
          · -- Caso ¬ h_eq_preds : a' ≠ b'
            -- En este caso, el primer `if` en la definición de `min` es falso.
            simp only [min, if_neg h_eq_preds] at h_min_eq
            -- Ahora h_min_eq es `(if BLt a' b' then σ a' else σ b') = σ a'`.
            -- Esto implica que `BLt a' b'` debe ser `true`. Si fuera `false`, entonces `σ b'` sería igual a `σ a'`, lo que contradiría `a' ≠ b'`.
            have h_blt_a'_b' : BLt a' b' = true := by
              by_cases h_blt_eval : BLt a' b'
              · -- h_blt_eval : BLt a' b' = true. Este es el caso que queremos.
                exact h_blt_eval
              · -- h_blt_eval : BLt a' b' = false
                -- Si `BLt a' b'` es `false`, entonces `min (σ a') (σ b')` es `σ b'`.
                simp only [h_blt_eval] at h_min_eq
                -- h_min_eq : σ b' = σ a'.
                -- Aplicamos AXIOM_succ_inj directamente a h_min_eq para obtener b' = a'.
                have h_b'_eq_a' : b' = a' := AXIOM_succ_inj b' a' h_min_eq
                -- Ahora tenemos `h_b'_eq_a' : b' = a'` y `h_eq_preds : a' ≠ b'`.
                -- Queremos probar `BLt a' b' = true` (el objetivo de este `have` bloque).
                -- Tenemos una contradicción: `h_eq_preds` (a' ≠ b') y `h_b'_eq_a'` (b' = a', que es lo mismo que a' = b').
                -- Aplicamos `False.elim` para resolver el objetivo de este sub-prueba.
                exact False.elim (h_eq_preds h_b'_eq_a'.symm) -- Usamos .symm para que la igualdad coincida con h_eq_preds
            -- Ahora que sabemos que `BLt a' b' = true`, por `BLt_iff_Lt`, tenemos `Lt a' b'`.
            have h_lt_a'_b' : Lt a' b' := (BLt_iff_Lt a' b').mp h_blt_a'_b'
            -- Queremos demostrar `Le (σ a') (σ b')`.
            -- Esto es equivalente a `Le a' b'` por `succ_le_succ_iff`.
            rw [succ_le_succ_iff]
            -- Y `Le a' b'` se cumple porque `Lt a' b'` implica `Le a' b'` por `lt_imp_le`.
            exact lt_imp_le a' b' h_lt_a'_b'

theorem min_eq_of_gt {a b : ℕ₀} (h_gt : Lt b a) :
    min a b = b := by
      cases a with
      | zero =>
        exfalso
        exact nlt_n_0 b h_gt
      | succ a' =>
        cases b with
        | zero =>
          simp [min]
        | succ b' =>
          have h_lt_b'_a' : Lt b' a' := (lt_iff_lt_σ_σ b' a').mp h_gt
          have h_b'_ne_a' : b' ≠ a' := lt_then_neq b' a' h_lt_b'_a'
          have h_not_lt_a'_b' : ¬(Lt a' b') := lt_asymm b' a' h_lt_b'_a'
          have h_blt_a'_b'_is_false : BLt a' b' = false := (nBLt_iff_nLt a' b').mpr h_not_lt_a'_b'

          -- Simplify the first `if` condition (n' = m')
          simp only [min, if_neg h_b'_ne_a'.symm]
          -- The goal is now `(if BLt a' b' then σ a' else σ b') = σ b'`.
          -- We know `BLt a' b' = false`, so the `if` should evaluate to `σ b'`.
          -- Use `rw` to replace `BLt a' b'` with `false` in the goal, then `simp`.
          rw [h_blt_a'_b'_is_false]
          simp

theorem max_eq_of_lt {a b : ℕ₀} (h_lt : Lt a b) :
    max a b = b := by
      cases a with
      | zero => -- a = 𝟘
        simp [max]
      | succ a' => -- a = σ a'
        cases b with
        | zero => -- b = 𝟘
          exfalso
          exact nlt_n_0 (σ a') h_lt
        | succ b' => -- a = σ a', b = σ b'
          -- Lt (σ a') (σ b') ↔ Lt a' b'
          have h_lt_preds : Lt a' b' := (lt_iff_lt_σ_σ a' b').mp h_lt
          have h_a'_ne_b' : a' ≠ b' := lt_then_neq a' b' h_lt_preds
          simp [max, if_neg h_a'_ne_b']
          have h_blt_a'_b'_is_true : BLt a' b' = true := (BLt_iff_Lt a' b').mpr h_lt_preds
          rw [h_blt_a'_b'_is_true]
          simp


theorem max_eq_of_gt {a b : ℕ₀} (h_gt : Lt b a) :
    max a b = a := by
      cases a with
      | zero =>
        exfalso
        exact nlt_n_0 b h_gt
      | succ a' =>
        cases b with
        | zero =>
          simp [max]
        | succ b' =>
          have h_lt_b'_a' : Lt b' a' := (lt_iff_lt_σ_σ b' a').mp h_gt
          have h_b'_ne_a' : b' ≠ a' := lt_then_neq b' a' h_lt_b'_a'
          have h_not_lt_a'_b' : ¬(Lt a' b') := lt_asymm b' a' h_lt_b'_a'
          have h_blt_a'_b'_is_false : BLt a' b' = false := (nBLt_iff_nLt a' b').mpr h_not_lt_a'_b'

          -- Simplify the first `if` condition (n' = m')
          simp only [max, if_neg h_b'_ne_a'.symm]
          -- The goal is now `(if BLt a' b' then σ b' else σ a') = σ a'`.
          -- We know `BLt a' b' = false`, so the `if` should evaluate to `σ a'`.
          -- Use `rw` to replace `BLt a' b'` with `false` in the goal, then `simp`.
          rw [h_blt_a'_b'_is_false]
          simp

theorem if_neq_then_max_xor(n m : ℕ₀) :
    n ≠ m ↔
    ((max n m = n) ∧ ¬(max n m = m))
    ∨
    (¬(max n m = n) ∧ (max n m = m))
    := by
      constructor
      · -- Dirección →: n ≠ m → ((max n m = n) ∧ ¬(max n m = m)) ∨ (¬(max n m = n) ∧ (max n m = m))
        intro h_neq_nm
        -- Usamos by_cases para la igualdad, y luego neq_then_lt_or_gt.
        by_cases h_eq_nm_case : n = m
        · -- Caso: n = m. Esto contradice h_neq_nm.
          exfalso
          exact h_neq_nm h_eq_nm_case
        · -- Caso: n ≠ m (que es h_eq_nm_case, si lo renombramos)
          -- Sabemos que si n ≠ m, entonces o Lt n m o Lt m n (por neq_then_lt_or_gt).
          have h_lt_or_gt := neq_then_lt_or_gt n m h_eq_nm_case
          cases h_lt_or_gt with
          | inl h_lt_nm => -- Caso: Lt n m (n < m)
            -- Esperamos la segunda disyunción: (¬(max n m = n) ∧ (max n m = m))
            apply Or.inr
            constructor
            · -- Subobjetivo 1: ¬(max n m = n)
              intro h_max_eq_n_contra
              -- Sabemos que max n m = m por max_eq_of_lt h_lt_nm
              have h_max_eq_m_true : max n m = m := max_eq_of_lt h_lt_nm
              -- Entonces, si max n m = n, se sigue que n = m. Contradice h_eq_nm_case.
              exact h_eq_nm_case (h_max_eq_n_contra.symm.trans h_max_eq_m_true)
            · -- Subobjetivo 2: max n m = m
              exact max_eq_of_lt h_lt_nm
          | inr h_lt_mn => -- Caso: Lt m n (m < n)
            -- Esperamos la primera disyunción: ((max n m = n) ∧ ¬(max n m = m))
            apply Or.inl
            constructor
            · -- Subobjetivo 1: max n m = n
              exact max_eq_of_gt h_lt_mn
            · -- Subobjetivo 2: ¬(max n m = m)
              intro h_max_eq_m_contra
              -- Sabemos que max n m = n por max_eq_of_gt h_lt_mn
              have h_max_eq_n_true : max n m = n := max_eq_of_gt h_lt_mn
              -- Entonces, si max n m = m, se sigue que m = n. Contradice h_eq_nm_case.
              exact h_eq_nm_case (h_max_eq_m_contra.symm.trans h_max_eq_n_true).symm

      · -- Dirección ←: ((max n m = n) ∧ ¬(max n m = m)) ∨ (¬(max n m = n) ∧ (max n m = m)) → n ≠ m
        intro h_disj
        -- Queremos probar n ≠ m. Asumimos n = m y derivamos False.
        intro h_eq_nm_contra -- h_eq_nm_contra : n = m
        cases h_disj with
        | inl h_and1 =>
          -- h_and1 : (max n m = n) ∧ ¬(max n m = m)
          have h_not_max_eq_m : ¬(max n m = m) := h_and1.right
          -- Si n = m, entonces max n m = max n n = n (por max_idem).
          -- Y como n = m, max n m = m. Esto contradice h_not_max_eq_m.
          have h_max_n_m_eq_m_true : max n m = m := by rw [h_eq_nm_contra]; exact max_idem m
          exact h_not_max_eq_m h_max_n_m_eq_m_true
        | inr h_and2 =>
          -- h_and2 : (¬(max n m = n) ∧ (max n m = m))
          have h_not_max_eq_n : ¬(max n m = n) := h_and2.left
          -- Si n = m, entonces max n m = n (por max_idem).
          -- Esto contradice h_not_max_eq_n.
          have h_max_n_m_eq_n_true : max n m = n
            := by
              rw [h_eq_nm_contra]
              exact max_idem m
          exact h_not_max_eq_n h_max_n_m_eq_n_true



theorem if_neq_then_min_xor(n m : ℕ₀) :
    n ≠ m ↔
    ((min n m = n) ∧ ¬(min n m = m))
    ∨
    (¬(min n m = n) ∧ (min n m = m))
    := by
      constructor
      · -- Dirección →: n ≠ m → ((min n m = n) ∧ ¬(min n m = m)) ∨ (¬(min n m = n) ∧ (min n m = m))
        intro h_neq_nm
        by_cases h_eq_nm_case : n = m
        · -- Caso: n = m. Esto contradice h_neq_nm.
          exfalso
          exact h_neq_nm h_eq_nm_case
        · -- Caso: n ≠ m
          have h_lt_or_gt := neq_then_lt_or_gt n m h_eq_nm_case
          cases h_lt_or_gt with
          | inl h_lt_nm => -- Caso: Lt n m (n < m)
            -- Esperamos la primera disyunción: ((min n m = n) ∧ ¬(min n m = m))
            apply Or.inl
            constructor
            · -- Subobjetivo 1: min n m = n
              exact lt_then_min n m h_lt_nm
            · -- Subobjetivo 2: ¬(min n m = m)
              intro h_min_eq_m_contra
              -- Sabemos que min n m = n por lt_then_min h_lt_nm
              have h_min_eq_n_true : min n m = n := lt_then_min n m h_lt_nm
              -- Si min n m = m, entonces n = m. Contradice h_eq_nm_case.
              exact h_eq_nm_case ((h_min_eq_m_contra.symm.trans h_min_eq_n_true).symm)
          | inr h_lt_mn => -- Caso: Lt m n (m < n)
            -- Esperamos la segunda disyunción: (¬(min n m = n) ∧ (min n m = m))
            apply Or.inr
            constructor
            · -- Subobjetivo 1: ¬(min n m = n)
              intro h_min_eq_n_contra
              -- Sabemos que min n m = m por min_eq_of_gt h_lt_mn
              have h_min_eq_m_true : min n m = m := min_eq_of_gt h_lt_mn
              -- Si min n m = n, entonces m = n. Contradice h_eq_nm_case.
              exact h_eq_nm_case (h_min_eq_n_contra.symm.trans h_min_eq_m_true)
            · -- Subobjetivo 2: min n m = m
              exact min_eq_of_gt h_lt_mn

      · -- Dirección ←: ((min n m = n) ∧ ¬(min n m = m)) ∨ (¬(min n m = n) ∧ (min n m = m)) → n ≠ m
        intro h_disj
        -- Queremos probar n ≠ m. Asumimos n = m y derivamos False.
        intro h_eq_nm_contra -- h_eq_nm_contra : n = m
        cases h_disj with
        | inl h_and1 =>
          -- h_and1 : (min n m = n) ∧ ¬(min n m = m)
          have h_not_min_eq_m : ¬(min n m = m) := h_and1.right
          -- Si n = m, entonces min n m = min n n = n (por min_idem).
          -- Y como n = m, min n m = m. Esto contradice h_not_min_eq_m.
          have h_min_n_m_eq_m_true : min n m = m := by rw [h_eq_nm_contra]; exact min_idem m
          exact h_not_min_eq_m h_min_n_m_eq_m_true
        | inr h_and2 =>
          -- h_and2 : (¬(min n m = n) ∧ (min n m = m))
          have h_not_min_eq_n : ¬(min n m = n) := h_and2.left
          -- Si n = m, entonces min n m = n (por min_idem).
          -- Esto contradice h_not_min_eq_n.
          have h_min_n_m_eq_n_true : min n m = n := by rw [h_eq_nm_contra]; exact min_idem m
          exact h_not_min_eq_n h_min_n_m_eq_n_true

theorem neq_args_then_lt_min_max(n m : ℕ₀) :
    n ≠ m ↔ Lt (min n m) (max n m)
    := by
      constructor
      · -- Dirección →: n ≠ m → Lt (min n m) (max n m)
        intro h_neq_nm
        -- Si n ≠ m, entonces o Lt n m o Lt m n por neq_then_lt_or_gt
        have h_lt_or_gt := neq_then_lt_or_gt n m h_neq_nm
        cases h_lt_or_gt with
        | inl h_lt_nm => -- Caso: Lt n m (n < m)
          -- En este caso, min n m = n y max n m = m
          have h_min_eq_n : min n m = n := lt_then_min n m h_lt_nm
          have h_max_eq_m : max n m = m := max_eq_of_lt h_lt_nm
          -- Reescribimos el objetivo usando estas igualdades
          rw [h_min_eq_n, h_max_eq_m]
          -- Ahora el objetivo es Lt n m, que es h_lt_nm
          exact h_lt_nm
        | inr h_lt_mn => -- Caso: Lt m n (m < n)
          -- En este caso, min n m = m y max n m = n
          have h_min_eq_m : min n m = m := min_eq_of_gt h_lt_mn
          have h_max_eq_n : max n m = n := max_eq_of_gt h_lt_mn
          -- Reescribimos el objetivo usando estas igualdades
          rw [h_min_eq_m, h_max_eq_n]
          -- Ahora el objetivo es Lt m n, que es h_lt_mn
          exact h_lt_mn

      · -- Dirección ←: Lt (min n m) (max n m) → n ≠ m
        intro h_lt_min_max
        -- Queremos probar n ≠ m por contradicción
        intro h_eq_nm
        -- Si n = m, entonces min n m = max n m = n (por min_idem y max_idem)
        have h_min_eq_n : min n m = n := by rw [h_eq_nm]; exact min_idem m
        have h_max_eq_n : max n m = n := by rw [h_eq_nm]; exact max_idem m
        -- Reescribimos h_lt_min_max con estas igualdades
        rw [h_min_eq_n, h_max_eq_n] at h_lt_min_max
        -- h_lt_min_max se convierte en Lt n n, pero sabemos que ¬(Lt n n) por lt_irrefl
        exact lt_irrefl n h_lt_min_max

theorem max_comm(n m : ℕ₀) :
    max n m = max m n
        := by
          induction n with
          | zero =>
              induction m with
              | zero =>
                  rfl
              | succ m' =>
                  simp [max]
          | succ n' ih_n =>
              induction m with
              | zero =>
                  simp [max]
              | succ m' =>
                  -- Objetivo original: max (σ n') (σ m') = max (σ m') (σ n')
                  -- Desplegando max:
                  -- (if n' = m' then σ m' else if BLt n' m' then σ m' else σ n') =
                  -- (if m' = n' then σ n' else if BLt m' n' then σ n' else σ m')
                  simp only [max] -- Muestra el objetivo desplegado
                  by_cases h_eq_preds : (n' = m')
                  · -- Caso: n' = m'
                    -- Sustituimos n' = m' en el objetivo.
                    -- Ambas expresiones 'if' se evalúan a la rama 'then'.
                    -- (if n' = n' then σ n' else ...) = (if n' = n' then σ n' else ...)
                    -- σ n' = σ n'
                    simp [h_eq_preds] -- simp usa h_eq_preds y su simétrico
                  · -- Caso: n' ≠ m'
                    -- Los primeros 'if' en ambas expresiones son falsos.
                    rw [if_neg h_eq_preds, if_neg (Ne.symm h_eq_preds)]
                    -- Objetivo ahora:
                    -- (if BLt n' m' then σ m' else σ n') =
                    -- (if BLt m' n' then σ n' else σ m')
                    by_cases h_blt_n_m_is_true : (BLt n' m' = true)
                    · -- Subcaso: BLt n' m' = true (es decir, Lt n' m')
                      -- El lado izquierdo se convierte en σ m'.
                      rw [if_pos h_blt_n_m_is_true]
                      -- Objetivo: σ m' = (if BLt m' n' then σ n' else σ m')
                      -- Como Lt n' m', entonces ¬ (Lt m' n') por asimetría.
                      have h_lt_n_m : Lt n' m' := (BLt_iff_Lt n' m').mp h_blt_n_m_is_true
                      have h_not_lt_m_n : ¬ (Lt m' n') := lt_asymm n' m' h_lt_n_m
                      -- Por lo tanto, BLt m' n' = false.
                      have h_blt_m_n_is_false : BLt m' n' = false := (nBLt_iff_nLt m' n').mpr h_not_lt_m_n
                      -- El lado derecho se convierte en σ m'.
                      rw [if_neg h_blt_m_n_is_false]
                      -- Objetivo: σ m' = σ m', que es trivial (rfl).
                    · -- Subcaso: BLt n' m' = false (es decir, ¬ (Lt n' m'))
                      -- h_blt_n_m_is_true es en realidad la hipótesis BLt n' m' = false aquí.
                      -- El lado izquierdo se convierte en σ n'.
                      rw [if_neg h_blt_n_m_is_true] -- h_blt_n_m_is_true es (BLt n' m' = false)
                      -- Objetivo: σ n' = (if BLt m' n' then σ n' else σ m')
                      -- Como n' ≠ m' y ¬ (Lt n' m'), por tricotomía, debe ser Lt m' n'.
                      have h_not_lt_n_m : ¬ (Lt n' m') := (nBLt_iff_nLt n' m').mp h_blt_n_m_is_true
                      have h_lt_m_n : Lt m' n' := by
                        cases trichotomy n' m' with
                        | inl h_lt_n_m_contra => -- Lt n' m'
                          -- Esto contradice h_not_lt_n_m (que vino de BLt n' m' = false)
                          exact False.elim (h_not_lt_n_m h_lt_n_m_contra)
                        | inr h_eq_or_gt =>
                          cases h_eq_or_gt with
                          | inl h_eq_contra => -- n' = m'
                            -- Esto contradice h_eq_preds (n' ≠ m')
                            exact False.elim (h_eq_preds h_eq_contra)
                          | inr h_gt_n_m => -- Lt m' n'
                            exact h_gt_n_m
                      -- Por lo tanto, BLt m' n' = true.
                      have h_blt_m_n_is_true : BLt m' n' = true := (BLt_iff_Lt m' n').mpr h_lt_m_n
                      -- El lado derecho se convierte en σ n'.
                      rw [if_pos h_blt_m_n_is_true]
                      -- Objetivo: σ n' = σ n', que es trivial (rfl).

theorem min_comm(n m : ℕ₀) :
    min n m = min m n
        := by sorry

theorem max_assoc(n m k : ℕ₀) :
    max (max n m) k = max n (max m k)
        := by sorry

theorem min_assoc(n m k : ℕ₀) :
    min (min n m) k = min n (min n k)
        := by sorry

theorem max_distrib_min(n m k : ℕ₀) :
    max n (min m k) = min (max n m) (max n k)
        := by sorry

theorem min_distrib_max(n m k : ℕ₀) :
    min n (max m k) = max (min n m) (min n k)
        := by sorry

theorem min_zero_absorb(n : ℕ₀) :
    min n 𝟘 = 𝟘
        := by sorry

theorem max_zero_neutral(n : ℕ₀) :
    max n 𝟘 = n
        := by sorry

theorem nexists_max_abs:
    ∀ (k: ℕ₀), ∃ (n: ℕ₀) , max n k = n ∧ n ≠ k
        := by
          intro k
          -- Queremos probar que existe n tal que max n k = n
          -- Usamos el caso trivial: n = k
          use n := σ k
          -- Queremos probar max k k = k
          -- Esto es cierto por la propiedad de max_idem
          exact max_idem k

theorem isomorph_max_Λ(n m : Nat) :
    max (Λ n) (Λ m) = Λ (Nat.max n m)
        := by sorry

theorem isomorph_min_Λ(n m : Nat) :
    min (Λ n) (Λ m) = Λ (Nat.min n m)
        := by sorry

theorem isomorph_max_Ψ(n m : ℕ₀) :
    max (Ψ n) (Ψ m) = Ψ (max n m)
        := by sorry

theorem isomorph_min_Ψ(n m : ℕ₀) :
    min (Ψ n) (Ψ m) = Ψ (min n m)
        := by sorry

end Peano
