import PeanoNatLib.PeanoNatAxioms


open PeanoNat
namespace PeanoNat
        --set_option diagnostics true
        --set_option trace.Meta.Tactic.simp true


    def Lt (n m : ℕ₀) : Prop :=
        match n, m with
        | _    , zero       => False
        | zero , σ _        => True
        | σ n' , σ m'       => Lt n' m'
    --instance : LT PeanoNat := ⟨Lt⟩

    --notation "<" => Lt

    def BLt (n m : ℕ₀) : Bool :=
        match n, m with
        | _    , zero       => false
        | zero , σ _        => true
        | σ n' , σ m'       => BLt n' m'

    theorem neg_lt_zero_zero:
        ¬(Lt zero zero)
            := by
                unfold Lt  -- Despliega Lt en el objetivo. El objetivo se convierte en ¬False.
                -- En este punto, el objetivo es `¬False`.
                -- `¬False` es equivalente a `False → False`.
                simp       -- `simp` puede probar `¬False` o `False → False` trivialmente.

    theorem lt_succ_succ(n m : ℕ₀) :
        Lt n m ↔ Lt (σ n) (σ m)
            := by
                induction m generalizing n with
                | zero =>
                    cases n with
                    | zero =>
                        rfl
                    | succ n' =>
                        cases n' with
                        | zero =>
                            rfl
                        | succ n'' =>
                            rfl
                | succ m' ih_m' =>
                    cases n with
                    | zero =>
                        rfl
                    | succ n' =>
                        let m := succ m'
                        let n := succ n'
                        let motive := Lt (σ n) (σ m) ↔ Lt n m
                        exact ih_m' n'

    theorem neg_lt_self(n : ℕ₀) :
        ¬(Lt n n)
            := by
                induction n with
                | zero =>
                    unfold Lt
                    simp
                | succ n' ih_n' =>
                    unfold Lt
                    simp [ih_n']


    theorem lt_then_neq(n m : ℕ₀) :
        Lt n m → n ≠ m
            := by
                intro h
                induction n with
                | zero =>
                    intro heq -- heq : zero = m
                    rw [Eq.symm heq] at h -- Ahora h : Lt zero zero
                    exact (neg_lt_zero_zero h)
                | succ n' =>
                    intro heq -- heq : σ n' = m
                    rw [Eq.symm heq] at h -- Ahora h : Lt (σ n') (σ n')
                    exact ((neg_lt_self (σ n')) h)

    theorem neq_then_lt_or_gt(n m : ℕ₀) :
        n ≠ m → (Lt n m ∨ Lt m n)
            := by
                intro h_neq -- h_neq : n ≠ m
                induction n generalizing m with
                | zero => -- n = zero
                    -- h_neq : zero ≠ m
                    -- Goal: Lt zero m ∨ Lt m zero
                    cases m with
                    | zero =>
                        exact False.elim (h_neq rfl)
                    | succ m' =>
                        apply Or.inl -- Probamos el lado izquierdo.
                        unfold Lt    -- El objetivo se convierte en True.
                        simp         -- simp prueba True.
                | succ n' ih_n' =>
                    cases m with
                    | zero =>
                        apply Or.inr -- Probamos el lado derecho.
                        unfold Lt    -- El objetivo se convierte en True.
                        simp
                    | succ m' =>
                        have h_neq_prime : n' ≠ m' := by
                            apply mt ((congrArg succ) :
                                n' = m' → σ n' = σ m')
                            exact h_neq
                        let spec_ih := ih_n' m' h_neq_prime
                        dsimp only [Lt]
                        exact spec_ih

    theorem lt_nor_gt_then_eq(n m : ℕ₀) :
        ¬(Lt n m) ∧ ¬(Lt m n) → n = m
            := by
                intro h_conj
                cases h_conj with
                | intro h_not_lt_nm h_not_lt_mn =>
                    induction n generalizing m with
                    | zero =>
                        cases m with
                        | zero =>
                            rfl
                        | succ m' =>
                            apply False.elim
                            apply h_not_lt_nm
                            dsimp [Lt]
                    | succ n' ih_n' => -- n = σ n'
                        cases m with
                        | zero =>
                            apply False.elim
                            apply h_not_lt_mn
                            dsimp [Lt]
                        | succ m' =>
                            have h_not_lt_n_prime_m_prime : ¬(Lt n' m') := by
                                unfold Lt at h_not_lt_nm
                                exact h_not_lt_nm
                            have h_not_lt_m_prime_n_prime : ¬(Lt m' n') := by
                                unfold Lt at h_not_lt_mn
                                exact h_not_lt_mn
                            have h_eq_prime : n' = m' := by
                                apply ih_n' m'
                                . exact h_not_lt_n_prime_m_prime
                                . exact h_not_lt_m_prime_n_prime
                            rw [h_eq_prime]

    theorem trichotomy (n m : ℕ₀) :
        (Lt n m) ∨ (n = m) ∨ (Lt m n)
            := by
                by_cases h_eq : n = m
                · -- Caso n = m
                  rw [h_eq]
                  apply Or.inr
                  apply Or.inl
                  rfl
                · -- Caso n ≠ m
                  have h_lt_or_gt := neq_then_lt_or_gt n m h_eq
                  cases h_lt_or_gt with
                  | inl h_lt_nm => -- Caso Lt n m
                    apply Or.inl
                    exact h_lt_nm
                  | inr h_lt_mn => -- Caso Lt m n
                    apply Or.inr
                    apply Or.inr
                    exact h_lt_mn

    theorem lt_n_m_then_not_lt_m_n(n m : ℕ₀) :
        Lt n m → ¬(Lt m n)
            := by
                intro h_lt_nm
                induction n generalizing m with
                | zero =>
                    cases m with
                    | zero =>
                        unfold Lt at h_lt_nm
                        exact False.elim h_lt_nm
                    | succ m' =>
                        unfold Lt
                        simp
                | succ n' ih_n' => -- Añadir ih_n' aquí
                    cases m with
                    | zero =>
                        unfold Lt at h_lt_nm
                        exact False.elim h_lt_nm
                    | succ m' =>
                        unfold Lt at h_lt_nm
                        exact ih_n' m' h_lt_nm

    theorem strong_trichotomy (n m : ℕ₀) :
          ((Lt n m)∧¬(Lt m n)∧(n ≠ m))
        ∨ ((Lt m n)∧¬(Lt n m)∧(n ≠ m))
        ∨ ((n = m)∧¬(Lt n m)∧¬(Lt m n))
            := by
                by_cases h_eq : n = m
                · -- Caso n = m
                  rw [h_eq]
                  apply Or.inr
                  apply Or.inr
                  exact ⟨
                    rfl,
                    neg_lt_self m,
                    neg_lt_self m
                  ⟩
                · -- Caso n ≠ m
                  have h_lt_or_gt := neq_then_lt_or_gt n m h_eq
                  cases h_lt_or_gt with
                  | inl h_lt_nm => -- Caso Lt n m
                    apply Or.inl
                    exact ⟨
                        h_lt_nm,
                        lt_n_m_then_not_lt_m_n n m h_lt_nm,
                        h_eq
                    ⟩
                  | inr h_lt_mn => -- Caso Lt m n
                    apply Or.inr
                    apply Or.inl
                    exact ⟨
                        h_lt_mn,
                        lt_n_m_then_not_lt_m_n m n h_lt_mn,
                        h_eq
                    ⟩

    theorem lt_transitivity(n m k : ℕ₀) :
        Lt n m → Lt m k → Lt n k
            := by
                intro h_lt_nm h_lt_mk
                induction n generalizing m k with
                | zero => -- n = zero
                    cases m with
                    | zero => -- m = zero
                        -- h_lt_nm es Lt zero zero, que es False
                        unfold Lt at h_lt_nm
                        exact False.elim h_lt_nm
                    | succ m' => -- m = σ m'
                        cases k with
                        | zero => -- k = zero
                            unfold Lt at h_lt_mk
                            exact False.elim h_lt_mk
                        | succ k' => -- k = σ k'
                            unfold Lt
                            trivial
                | succ n' ih_n' =>
                    cases m with
                    | zero =>
                        unfold Lt at h_lt_nm
                        exact False.elim h_lt_nm
                    | succ m' =>
                        cases k with
                        | zero =>
                            unfold Lt at h_lt_mk
                            exact False.elim h_lt_mk
                        | succ k' =>
                            dsimp only [Lt] at *
                            apply ih_n'
                            . exact h_lt_nm
                            . exact h_lt_mk

    theorem lt_equiv_exists_succ(n m : ℕ₀) :
        Lt n m ↔ (m = σ n) ∨ (∃ k : ℕ₀, Lt n k ∧ Lt k m)  := by
            induction n generalizing m with
            | zero =>
                cases m with
                | zero =>
                    simp [Lt]
                | succ m' =>
                    simp [Lt]
                    cases m' with
                    | zero =>
                        apply Or.inl
                        rfl
                    | succ m_double_prime =>
                        apply Or.inr
                        exists (σ zero)
            | succ n' ih_n' =>
                cases m with
                | zero =>
                    simp [Lt]
                | succ m' =>
                    simp [Lt]
                    rw [ih_n' m']
                    have h_ex_equiv : (∃ k, Lt n' k ∧ Lt k m') ↔ (∃ k', Lt (σ n') k' ∧ Lt k' (σ m')) := by
                        constructor
                        · intro h_ex_lhs
                          rcases h_ex_lhs with ⟨k_val, h_lt_nk, h_lt_km⟩
                          apply Exists.intro (σ k_val)
                          apply And.intro
                          · dsimp only [Lt]
                            exact h_lt_nk
                          · dsimp only [Lt]
                            exact h_lt_km
                        · intro h_ex_rhs
                          rcases h_ex_rhs with ⟨k_prime_val, h_lt_snk_prime, h_lt_k_prime_sm⟩
                          cases k_prime_val with
                          | zero =>
                            simp only [Lt] at h_lt_snk_prime
                          | succ k_inner =>
                            apply Exists.intro k_inner
                            simp [Lt] at *
                            exact And.intro h_lt_snk_prime h_lt_k_prime_sm
                    apply or_congr
                    · apply Iff.intro
                      · intro h_eq
                        rw [h_eq]
                      · intro h_eq_succ
                        injection h_eq_succ with h_inj_m_eq_sigma_n'
                    · exact h_ex_equiv

    theorem lt_self_succ_self(n : ℕ₀) :
        Lt n (σ n)
            := by
        induction n with
        | zero =>
          unfold Lt
          simp
        | succ n' ih_n' =>  -- Modificado: añadido ih_n' para nombrar la hipótesis de inducción
          -- Goal: Lt (σ n') (σ (σ n')), IH: Lt n' (σ n')
          unfold Lt      -- Transforms goal to Lt n' (σ n')
          exact ih_n'     -- Apply IH

    theorem BLt_iff_Lt (n m : ℕ₀) :
        BLt n m = true ↔ Lt n m
        := by
          induction n generalizing m with
          | zero =>
            cases m with
            | zero =>
              simp [BLt, Lt]
            | succ m' =>
              simp [BLt, Lt]
          | succ n' ih_n' =>
            cases m with
            | zero =>
              simp [BLt, Lt]
            | succ m' =>
              simp [BLt, Lt]
              exact ih_n' m'

    theorem isomorphism_lt_nat_lt_pea (n m : Nat) :
        (n < m) ↔ (Lt (nat2pea n) (nat2pea m))
            := by
                constructor
                · intro h_lt_nm -- h_lt_nm : n < m
                  induction n generalizing m with
                  | zero => -- Caso n = 0
                    simp [nat2pea]
                    cases m with -- Analizamos m
                    | zero =>
                      exact False.elim (Nat.lt_irrefl 0 h_lt_nm)
                    | succ m' =>
                      unfold Lt
                      trivial
                  | succ n' ih => -- Modificado: Nombrada la HI como 'ih'
                    simp [nat2pea]
                    cases m with
                    | zero =>
                      exact False.elim (Nat.not_lt_zero _ h_lt_nm)
                    | succ m' =>
                      simp [nat2pea]
                      unfold Lt
                      apply ih -- Modificado: Usar la HI local 'ih'
                      exact (Nat.lt_of_succ_lt_succ h_lt_nm)
                · intro h_lt_pn_pm
                  induction n generalizing m with -- Modificado: Eliminado el punto al inicio de la línea
                  | zero => -- Caso n = 0
                    simp [nat2pea] at h_lt_pn_pm
                    cases m with -- Analizamos m
                    | zero => -- Caso m = 0.
                      -- h_lt_pn_pm es Lt PeanoNat.zero PeanoNat.zero (después de simplificaciones anteriores como simp [nat2pea] at h_lt_pn_pm y la estructura cases m).
                      -- La táctica 'unfold Lt' original fallaba porque intentaba desplegar PeanoNat.Lt en la meta (0 : Nat) < (0 : Nat), que es de tipo Nat.lt.
                      -- En lugar de eso, simplificamos la hipótesis h_lt_pn_pm.
                      -- Por definición, Lt PeanoNat.zero PeanoNat.zero es False.
                      -- Cuando una hipótesis se simplifica a False, la táctica `simp` cierra la meta automáticamente.
                      unfold Lt at h_lt_pn_pm -- Reemplaza simp [Lt] at h_lt_pn_pm
                      contradiction          -- Añadido para usar la hipótesis False
                    | succ m' =>
                      unfold Lt
                      trivial
                  | succ n' ih_n' => -- Modificado: añadido ih_n' (ya estaba pero se confirma su uso correcto)
                    simp [nat2pea] at h_lt_pn_pm
                    cases m with -- Analizamos m
                    | zero => -- Caso m = 0.
                      unfold Lt at h_lt_pn_pm
                      exact False.elim h_lt_pn_pm
                    | succ m' =>
                      -- h_lt_pn_pm : pea2nat (σ n') < pea2nat (σ m')
                      -- ih_n'      : ∀ k, pea2nat n' < pea2nat k → Lt n' k
                      -- Goal       : Lt (σ n') (σ m')
                      simp only [pea2nat] at h_lt_pn_pm -- h_lt_pn_pm : (pea2nat n').succ < (pea2nat m').succ
                      rw [← lt_succ_succ n' m'] -- Cambia el objetivo a Lt n' m'
                      apply ih_n' m'          -- Aplica la HI, nuevo objetivo: pea2nat n' < pea2nat m'
                      exact (Nat.lt_of_succ_lt_succ h_lt_pn_pm) -- Provee la prueba necesaria

     theorem isomorphism_lt_pea_lt_nat (n m : ℕ₀) :
        (Lt n m) ↔ (pea2nat n < pea2nat m)
        := by
            constructor
            · intro h_lt_nm -- h_lt_nm : Lt n m
              induction n generalizing m with
              | zero =>
                cases m with
                | zero =>
                  unfold Lt at h_lt_nm
                  exact False.elim h_lt_nm
                | succ m' =>
                  apply Nat.zero_lt_succ
              | succ n' ih_n' =>
                cases m with
                | zero =>
                  unfold Lt at h_lt_nm
                  exact False.elim h_lt_nm
                | succ m' =>
                  unfold Lt at h_lt_nm -- h_lt_nm ahora es Lt n' m'
                  -- El objetivo aquí es pea2nat (σ n') < pea2nat (σ m'),
                  -- que es (pea2nat n').succ < (pea2nat m').succ por definición de pea2nat.
                  apply Nat.succ_lt_succ -- Objetivo se transforma a: pea2nat n' < pea2nat m'
                  apply ih_n'          -- Objetivo: Lt n' m' (después de que m' se infiera para el parámetro de ih_n')
                  exact h_lt_nm
            · intro h_lt_pn_pm -- h_lt_pn_pm : pea2nat n < pea2nat m
              induction n generalizing m with
              | zero =>
                cases m with
                | zero =>
                  -- h_lt_pn_pm es pea2nat zero < pea2nat zero, que es 0 < 0, False.
                  -- No necesitamos unfold Lt aquí.
                  -- simp [pea2nat] at h_lt_pn_pm -- convierte h_lt_pn_pm a 0 < 0
                  -- exact False.elim (Nat.lt_irrefl 0 h_lt_pn_pm)
                  -- La prueba original con unfold Lt at h_lt_pn_pm era incorrecta, pero el resultado es el mismo
                  -- porque Lt zero zero es False.
                  -- Para mantenerlo simple y alineado con la estructura original:
                  unfold Lt -- El objetivo es False
                  simp [pea2nat] at h_lt_pn_pm -- h_lt_pn_pm se simplifica a (0 < 0), que es False.
                                               -- `simp at` cierra el objetivo cuando una hipótesis se vuelve False.
                | succ m' =>
                  unfold Lt
                  trivial
              | succ n' ih_n' =>
                cases m with
                | zero =>
                  -- h_lt_pn_pm es pea2nat (σ n') < pea2nat zero, que es (pea2nat n').succ < 0, False.
                  unfold Lt -- El objetivo es False
                  simp [pea2nat] at h_lt_pn_pm -- h_lt_pn_pm : (pea2nat n').succ < 0
                                               -- simp at h_lt_pn_pm cierra el objetivo porque h_lt_pn_pm se vuelve False.
                | succ m' =>
                  -- h_lt_pn_pm : pea2nat (σ n') < pea2nat (σ m')
                  -- ih_n'      : ∀ k, pea2nat n' < pea2nat k → Lt n' k
                  -- Goal       : Lt (σ n') (σ m')
                  simp only [pea2nat] at h_lt_pn_pm -- h_lt_pn_pm : (pea2nat n').succ < (pea2nat m').succ
                  rw [← lt_succ_succ n' m'] -- Cambia el objetivo a Lt n' m'
                  apply ih_n' m'          -- Aplica la HI, nuevo objetivo: pea2nat n' < pea2nat m'
                  exact (Nat.lt_of_succ_lt_succ h_lt_pn_pm) -- Provee la prueba necesaria

    instance decidableLt (n m : ℕ₀) :
      Decidable (Lt n m) :=
      if h_blt_is_true : BLt n m then
        isTrue ((BLt_iff_Lt n m).mp h_blt_is_true)
      else
        isFalse (fun h_lt_nm : Lt n m =>
            have proof_blt_should_be_true : BLt n m = true
                := (BLt_iff_Lt n m).mpr h_lt_nm
            h_blt_is_true proof_blt_should_be_true)

    instance : LT ℕ₀ := ⟨Lt⟩

end PeanoNat

export PeanoNat(..)
