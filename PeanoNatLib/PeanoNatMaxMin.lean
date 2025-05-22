import PeanoNatLib.PeanoNatAxioms
import PeanoNatLib.PeanoNatStrictOrder
import PeanoNatLib.PeanoNatOrder

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

theorem lt_then_min (a b : ℕ₀) :
    Lt a b → min a b = a
    := by
      intro h_lt
      cases a with
      | zero =>
        cases b with
        | zero => simp [min]
        | succ m' => simp [min]
      | succ a' =>
        cases b with
        | zero => exfalso; exact nlt_n_0 _ h_lt
        | succ b' =>
          have h_lt_a'_b' : Lt a' b'
              := by simp [Lt] at h_lt; exact h_lt
          have h_a'_ne_b' : a' ≠ b'
              := lt_then_neq a' b' h_lt_a'_b'
          simp [min, if_neg h_a'_ne_b']
          rw [(BLt_iff_Lt a' b').mpr h_lt_a'_b']
          simp

theorem min_then_le (a b : ℕ₀) :
    min a b = a → Le a b
    := by sorry

theorem min_eq_of_lt {a b : ℕ₀} (h : Lt a b) :
    min a b = a := by sorry

theorem max_eq_of_lt {a b : ℕ₀} (h : Lt a b) :
    max a b = b := by sorry

theorem min_eq_of_gt {a b : ℕ₀} (h_gt : Lt b a) :
    min a b = b := by sorry

theorem max_eq_of_gt {a b : ℕ₀} (h_gt : Lt b a) :
    max a b = a := by sorry

theorem if_neq_then_max_xor(n m : ℕ₀) :
    n ≠ m ↔
    ((max n m = n) ∧ ¬(max n m = m))
    ∨
    (¬(max n m = n) ∨ (max n m = m))
        := by sorry

theorem if_neq_then_min_xor(n m : ℕ₀) :
    n ≠ m ↔
    ((min n m = n) ∧ ¬(min n m = m))
    ∨
    (¬(min n m = n) ∨ (min n m = m))
        := by sorry

theorem neq_args_then_lt_min_max(n m : ℕ₀) :
    n ≠ m ↔ Lt (min n m) (max n m )
        := by sorry

theorem max_comm(n m : ℕ₀) :
    max n m = max m n
        := by sorry

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
