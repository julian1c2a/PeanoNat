import PeanoNatLib.PeanoNatAxioms


open PeanoNat
namespace PeanoNat
        --set_option diagnostics true
        --set_option trace.Meta.Tactic.simp true


    def Lt (n m : ℕ₀) : Prop :=
        match n, m with
        | _    , 𝟘       => False
        | 𝟘 , σ _        => True
        | σ n' , σ m'       => Lt n' m'

    def BLt (n m : ℕ₀) : Bool :=
        match n, m with
        | _    ,   𝟘       => false
        | 𝟘    , σ _       => true
        | σ n' , σ m'      => BLt n' m'

    theorem neg_lt_zero_zero:
        ¬(Lt 𝟘 𝟘)
            := by
                unfold Lt
                trivial

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
                        let m := σ m'
                        let n := σ n'
                        let motive := Lt (σ n) (σ m) ↔ Lt n m
                        exact ih_m' n'

    theorem neg_lt_self(n : ℕ₀) :
        ¬(Lt n n)
            := by
                induction n with
                | zero =>
                    unfold Lt
                    trivial
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
                    rw [Eq.symm heq] at h
                    exact ((neg_lt_self (σ n')) h)

    theorem neq_then_lt_or_gt(n m : ℕ₀) :
        n ≠ m → (Lt n m ∨ Lt m n)
            := by
                intro h_neq -- h_neq : n ≠ m
                induction n generalizing m with
                | zero =>
                    cases m with
                    | zero =>
                        exact False.elim (h_neq rfl)
                    | succ m' =>
                        apply Or.inl
                        unfold Lt
                        simp
                | succ n' ih_n' =>
                    cases m with
                    | zero =>
                        apply Or.inr
                        unfold Lt
                        simp
                    | succ m' =>
                        have h_neq_prime : n' ≠ m' := by
                            apply mt ((congrArg ℕ₀.succ) :
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
        Lt n m ↔ (m = σ n) ∨ (∃ k : ℕ₀, Lt n k ∧ Lt k m)
        := by
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
                        exists (σ 𝟘)
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
                        assumption
                    · exact h_ex_equiv

    theorem lt_self_succ_self(n : ℕ₀) :
        Lt n (σ n)
            := by
        induction n with
        | zero =>
          unfold Lt
          simp
        | succ n' ih_n' =>
          unfold Lt
          exact ih_n'

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
                · intro h_lt_nm
                  induction n generalizing m with
                  | zero =>
                    cases m with
                    | zero =>
                      exact (Nat.lt_irrefl 0 h_lt_nm)
                    | succ m' =>
                      simp [Lt, nat2pea]
                  | succ n' ih_n' =>
                    cases m with
                    | zero =>
                      exact (
                        (
                          Nat.not_lt_zero (Nat.succ n')
                        )
                        h_lt_nm
                      )
                    | succ m' =>
                      simp only [nat2pea]
                      rw [← lt_succ_succ]
                      apply ih_n'
                      exact (Nat.lt_of_succ_lt_succ h_lt_nm)
                · intro h_lt_pn_pm
                  induction n generalizing m with
                  | zero =>
                    cases m with
                    | zero =>
                      unfold Lt at h_lt_pn_pm
                      exact False.elim h_lt_pn_pm
                    | succ m' =>
                      unfold Lt at h_lt_pn_pm
                      apply Nat.zero_lt_succ
                  | succ n' ih_n' =>
                    cases m with
                    | zero =>
                      unfold Lt at h_lt_pn_pm
                      exact False.elim h_lt_pn_pm
                    | succ m' =>
                      apply Nat.succ_lt_succ
                      apply ih_n' m'
                      dsimp only [nat2pea] at h_lt_pn_pm
                      dsimp only [Lt] at h_lt_pn_pm
                      exact h_lt_pn_pm

     theorem isomorphism_lt_pea_lt_nat (n m : ℕ₀) :
        (Lt n m) ↔ (pea2nat n < pea2nat m)
        := by
            constructor
            · intro h_lt_nm
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
                  unfold Lt at h_lt_nm
                  apply Nat.succ_lt_succ
                  apply ih_n'
                  exact h_lt_nm
            · intro h_lt_pn_pm
              induction n generalizing m with
              | zero =>
                cases m with
                | zero =>
                  unfold Lt
                  simp [pea2nat] at h_lt_pn_pm
                | succ m' =>
                  unfold Lt
                  trivial
              | succ n' ih_n' =>
                cases m with
                | zero =>
                  unfold Lt
                  simp [pea2nat] at h_lt_pn_pm
                | succ m' =>
                  dsimp only [pea2nat] at h_lt_pn_pm
                  rw [← lt_succ_succ n' m']
                  apply ih_n' m'
                  exact (Nat.lt_of_succ_lt_succ h_lt_pn_pm)

    def maximum (n m : ℕ₀) : ℕ₀ :=
        match n, m with
        | 𝟘 , _ => m
        | _ , 𝟘 => n
        | σ n' , σ m' =>
            σ (maximum n' m')

    def minimum (n m : ℕ₀) : ℕ₀ :=
        match n, m with
        | 𝟘 , _ => 𝟘
        | _ , 𝟘 => 𝟘
        | σ n' , σ m' =>
            σ (minimum n' m')

    def min_max (n m : ℕ₀) : ℕ₀×ℕ₀ :=
        match n, m with
        | 𝟘 , m => (𝟘 , m)
        | n , 𝟘 => (𝟘 , n)
        | σ n' , σ m' =>
            (σ (minimum n' m'), σ (maximum n' m'))

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
