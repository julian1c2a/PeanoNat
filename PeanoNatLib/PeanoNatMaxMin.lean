import PeanoNatLib.PeanoNatAxioms

import PeanoNatLib.PeanoNatStrictOrder
--import Mathlib.Tactic.SplitIfs -- Añadir esta línea

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
                  left -- Cambiado de left a right
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

-- USAR BLT_IFF_LT PARA HACERLO MAS LIMPIO
theorem min_lt_iff_min_eq_left_when_neq (a b : ℕ₀) : -- Renombrado para claridad y evitar colisión de nombres
    a ≠ b → (Lt a b ↔ min a b = a)
    := by
    intro h_neq -- Hipótesis: a ≠ b
    -- Dividimos la prueba según la tricotomía de a y b.
    rcases trichotomy a b with h_lt_a_b | h_eq_a_b | h_lt_b_a
    · -- Caso 1: Lt a b (h_lt_a_b)
      -- El objetivo es (Lt a b ↔ min a b = a).
      -- Dado que Lt a b es verdadero, esto se simplifica a (True ↔ min a b = a), es decir, (min a b = a).
      simp only [h_lt_a_b, iff_true]
      -- Ahora el objetivo es: min a b = a.
      -- Probamos esto directamente. Podríamos usar el lema `min_eq_of_lt` si estuviera probado antes y correctamente.
      -- Para hacerlo autocontenido aquí:
      cases a with
      | zero => -- a = 𝟘. Entonces h_lt_a_b es Lt 𝟘 b.
        -- min 𝟘 b se simplifica a 𝟘 por definición de min.
        -- El objetivo es 𝟘 = 𝟘.
        simp [min]
      | succ a' => -- a = σ a'. Entonces h_lt_a_b es Lt (σ a') b.
        -- b no puede ser 𝟘, porque Lt (σ a') 𝟘 es falso.
        cases b with
        | zero => -- b = 𝟘. h_lt_a_b es Lt (σ a') 𝟘. Esto es una contradicción.
          exfalso
          exact lt_succ_zero_is_false _ h_lt_a_b
        | succ b' => -- b = σ b'. h_lt_a_b es Lt (σ a') (σ b').
          -- De Lt (σ a') (σ b'), se deduce Lt a' b'.
          have h_lt_preds : Lt a' b' := succ_lt_succ_iff.mp h_lt_a_b
          -- min (σ a') (σ b') se define como:
          -- if a' = b' then σ a' else if BLt a' b' then σ a' else σ b'
          -- Dado Lt a' b', sabemos que a' ≠ b' (por ne_of_lt) y BLt a' b' es true (por BLt_iff_Lt).
          -- Entonces min (σ a') (σ b') se simplifica a σ a'.
          -- El objetivo es σ a' = σ a'.
          simp [min, BLt_iff_Lt, h_lt_preds, ne_of_lt h_lt_preds]
    · -- Caso 2: a = b (h_eq_a_b)
      -- Tenemos h_neq : a ≠ b y h_eq_a_b : a = b. Esto es una contradicción.
      -- El objetivo (Lt a b ↔ min a b = a) se puede cerrar por exfalso.
      exfalso; exact h_neq h_eq_a_b
    · -- Caso 3: Lt b a (h_lt_b_a)
      -- El objetivo es (Lt a b ↔ min a b = a).
      -- Dado Lt b a, sabemos que ¬ (Lt a b) por asimetría.
      have h_not_lt_a_b : ¬ Lt a b := lt_asymm h_lt_b_a
      -- El objetivo se convierte en (False ↔ min a b = a).
      -- Esto es equivalente a ¬ (min a b = a).
      simp only [h_not_lt_a_b, iff_false]
      -- Ahora el objetivo es: min a b ≠ a.
      -- Dado Lt b a, sabemos que min a b = b (por el lema min_eq_of_gt, que está probado más abajo).
      rw [min_eq_of_gt h_lt_b_a] -- El objetivo se convierte en ¬ (b = a), o b ≠ a.
      -- b ≠ a es lo mismo que a ≠ b (nuestra hipótesis h_neq). Usamos la simetría de la desigualdad.
      exact Ne.symm h_neq

lemma min_eq_of_lt {a b : ℕ₀} (h : Lt a b) : min a b = a := by -- Declaración corregida: el original decía `max a b = b`
  induction a generalizing b with
  | zero => -- a = 𝟘. h : Lt 𝟘 b. min 𝟘 b = 𝟘. Objetivo: 𝟘 = 𝟘.
    simp [min] -- min 𝟘 b se simplifica a 𝟘.

lemma max_eq_of_lt {a b : ℕ₀} (h : Lt a b) : max a b = b := by
  induction a generalizing b with
  | zero => simp [max]
  | succ a' iha =>
    cases b with
    | zero => exfalso; exact lt_zero_is_false h
    | succ b' =>
      simp only [max] -- Expands to: (if a' = b' then σ a' else if BLt a' b' then σ b' else σ a') = σ b'
      have h_a'_lt_b' : Lt a' b' := succ_lt_succ_iff.mp h
      have h_a'_ne_b' : a' ≠ b' := Ne.symm (ne_of_lt h_a'_lt_b')
      rw [if_neg h_a'_ne_b']
      -- Goal: (if BLt a' b' then σ b' else σ a') = σ b'
      -- We need to prove BLt a' b' = true from h_a'_lt_b' : Lt a' b'
      rw [if_pos ((BLt_iff_Lt _ _).mpr h_a'_lt_b')]
      -- Goal: σ b' = σ b', which is true by rfl

lemma min_eq_of_gt {a b : ℕ₀} (h_gt : Lt b a) : min a b = b := by
  induction b generalizing a with
  | zero => simp [min]
  | succ b' ihb =>
    cases a with
    | zero => exfalso; exact lt_zero_is_false h_gt
    | succ a' =>
      simp only [min] -- Expands to: (if a' = b' then σ a' else if BLt a' b' then σ a' else σ b') = σ b'
      have h_b'_lt_a' : Lt b' a' := succ_lt_succ_iff.mp h_gt
      have h_a'_ne_b' : a' ≠ b' := ne_of_lt h_b'_lt_a' -- a' ≠ b' because b' < a'
      rw [if_neg h_a'_ne_b']
      -- Goal: (if BLt a' b' then σ a' else σ b') = σ b'
      -- We need to prove BLt a' b' = false from h_b'_lt_a' : Lt b' a'
      have h_not_lt_a'_b' : ¬ Lt a' b' := not_lt_of_gt h_b'_lt_a'
      rw [if_neg ((BLt_iff_Lt _ _).not.mpr h_not_lt_a'_b')]
      -- Goal: σ b' = σ b', which is true by rfl

lemma max_eq_of_gt {a b : ℕ₀} (h_gt : Lt b a) : max a b = a := by
  induction b generalizing a with
  | zero => simp [max]
  | succ b' ihb =>
    cases a with
    | zero => exfalso; exact lt_zero_is_false h_gt
    | succ a' =>
      simp only [max] -- Expands to: (if a' = b' then σ a' else if BLt a' b' then σ b' else σ a') = σ a'
      have h_b'_lt_a' : Lt b' a' := succ_lt_succ_iff.mp h_gt
      have h_a'_ne_b' : a' ≠ b' := ne_of_lt h_b'_lt_a'
      rw [if_neg h_a'_ne_b']
      -- Goal: (if BLt a' b' then σ b' else σ a') = σ a'
      -- We need to prove BLt a' b' = false from h_b'_lt_a' : Lt b' a'
      have h_not_lt_a'_b' : ¬ Lt a' b' := not_lt_of_gt h_b'_lt_a'
      rw [if_neg ((BLt_iff_Lt _ _).not.mpr h_not_lt_a'_b')]
      -- Goal: σ a' = σ a', which is true by rfl

theorem if_neq_then_max_xor(n m : ℕ₀) :
    n ≠ m ↔
    ((max n m = n) ∧ ¬(max n m = m))
    ∨
    (¬(max n m = n) ∨ (max n m = m))
        := by
        by_cases h_eq_n_m : (n = m)
        · -- Caso n = m
          -- LHS (n ≠ m) es Falso.
          -- RHS: Si n = m, max n m = n y max n m = m.
          -- ((True) ∧ ¬(True)) ∨ (¬(True) ∨ (True))
          -- (False           ) ∨ (False    ∨ True )
          -- False              ∨ True
          -- True
          -- Entonces, Falso ↔ True, lo cual es Falso. Esto es correcto.
          -- El objetivo se convierte en (n ≠ m) ↔ True, que es n ≠ m.
          -- Pero queremos probar (n = m) → ((n ≠ m) ↔ RHS_eval_true)
          -- (n = m) → (False ↔ True) which is (n = m) → False.
          -- Esto significa que si n=m es verdadero, obtenemos una falsedad, lo cual es correcto.
          simp only [h_eq_n_m, max_idem, not_true, and_false, false_or, or_true, iff_false]
          exact Ne.symm h_eq_n_m
        · -- Caso n ≠ m
          -- LHS (n ≠ m) es Verdadero.
          -- Necesitamos mostrar que RHS es Verdadero.
          simp only [h_eq_n_m, iff_true] -- El objetivo es ahora RHS
          have h_max_any := max_is_any n m
          rcases h_max_any with h_max_is_n | h_max_is_m
          · -- Caso max n m = n
            -- Como n ≠ m, entonces max n m ≠ m.
            have h_max_not_m : ¬(max n m = m) := by
              intro h_contra_max_eq_m
              apply h_eq_n_m -- n ≠ m
              rw [← h_max_is_n, h_contra_max_eq_m] -- n = m, contradicción
            left
            exact ⟨h_max_is_n, h_max_not_m⟩
          · -- Caso max n m = m
            -- Como n ≠ m, entonces max n m ≠ n.
            -- (¬(max n m = n) ∨ (max n m = m))
            -- (¬(m = n) ∨ True) -> True
            right
            right -- Para probar la segunda parte de la disyunción (max n m = m)
            exact h_max_is_m

theorem if_neq_then_min_xor(n m : ℕ₀) :
    n ≠ m ↔
    ((min n m = n) ∧ ¬(min n m = m))
    ∨
    (¬(min n m = n) ∨ (min n m = m))
        := by
        by_cases h_eq_n_m : (n = m)
        · -- Caso n = m
          simp only [h_eq_n_m, min_idem, not_true, and_false, false_or, or_true, iff_false]
          exact Ne.symm h_eq_n_m
        · -- Caso n ≠ m
          simp only [h_eq_n_m, iff_true] -- El objetivo es ahora RHS
          have h_min_any := min_is_any n m
          rcases h_min_any with h_min_is_n | h_min_is_m
          · -- Caso min n m = n
            have h_min_not_m : ¬(min n m = m) := by
              intro h_contra_min_eq_m
              apply h_eq_n_m
              rw [← h_min_is_n, h_contra_min_eq_m]
            left
            exact ⟨h_min_is_n, h_min_not_m⟩
          · -- Caso min n m = m
            right
            right
            exact h_min_is_m

theorem neq_args_then_lt_min_max(n m : ℕ₀) :
    n ≠ m ↔ Lt (min n m) (max n m )
        := by
        constructor
        · -- Dirección →: n ≠ m → Lt (min n m) (max n m)
          intro h_neq_n_m
          -- Por tricotomía, si n ≠ m, entonces Lt n m o Lt m n.
          -- Usamos trichotomy_alt que asume n ≠ m.
          rcases trichotomy_alt n m h_neq_n_m with h_lt_n_m | h_lt_m_n
          · -- Caso Lt n m
            -- Entonces min n m = n y max n m = m.
            -- Queremos mostrar Lt n m, lo cual es h_lt_n_m.
            rw [min_eq_of_lt h_lt_n_m]
            rw [max_eq_of_lt h_lt_n_m]
            exact h_lt_n_m
          · -- Caso Lt m n
            -- Entonces min n m = m y max n m = n.
            -- Queremos mostrar Lt m n, lo cual es h_lt_m_n.
            rw [min_eq_of_gt h_lt_m_n]
            rw [max_eq_of_gt h_lt_m_n]
            exact h_lt_m_n
        · -- Dirección ←: Lt (min n m) (max n m) → n ≠ m
          intro h_lt_min_max
          -- Probamos por contradicción: suponemos n = m.
          by_contra h_eq_n_m
          -- Sustituimos n = m en h_lt_min_max:
          rw [h_eq_n_m] at h_lt_min_max -- Lt (min m m) (max m m)
          -- Simplificamos usando min_idem y max_idem:
          rw [min_idem m, max_idem m] at h_lt_min_max -- Lt m m
          -- Esto es una contradicción, ya que Lt m m es falso.
          exact lt_irrefl m h_lt_min_max

theorem max_comm(n m : ℕ₀) :
    max n m = max m n
        := by
        simp only [max, BLt_iff_Lt, eq_comm] -- eq_comm para normalizar n'=m' y m'=n'
        -- Considerar casos para n y m (cero o sucesor)
        cases n with
        | zero =>
          cases m with
          | zero => simp -- max 𝟘 𝟘 = max 𝟘 𝟘
          | succ m' => simp -- max 𝟘 (σ m') = max (σ m') 𝟘
        | succ n' =>
          cases m with
          | zero => simp -- max (σ n') 𝟘 = max 𝟘 (σ n')
          | succ m' => -- Caso principal: max (σ n') (σ m') = max (σ m') (σ n')
            -- La meta es:
            -- ite (n' = m') (σ n') (ite (Lt n' m') (σ m') (σ n')) =
            -- ite (m' = n') (σ m') (ite (Lt m' n') (σ n'))
            -- Usamos split_ifs para dividir según las condiciones booleanas.
            -- simp_all intentará resolver cada sub-meta usando las hipótesis generadas.
            split_ifs <;> simp_all [lt_asymm, lt_trichotomy]
            -- lt_asymm: Lt x y → ¬ Lt y x
            -- lt_trichotomy: dado x, y, se cumple Lt x y ∨ x = y ∨ Lt y x

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
