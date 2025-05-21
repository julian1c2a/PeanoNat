import PeanoNatLib.PeanoNatAxioms
import PeanoNatLib.PeanoNatStrictOrder -- Importa Lt y sus propiedades

open Peano
namespace Peano

    -- Definiciones y teoremas para Le (menor o igual)

    /-- Definición de "menor o igual que" para ℕ₀. -/
    def Le (n m : ℕ₀) : Prop := Lt n m ∨ n = m
    def Ge (n m : ℕ₀) : Prop := Lt m n ∨ n = m
    /-- Instancia Decidable para Le n m.
        Se construye a partir de las instancias
        Decidable para Lt n m y n = m.
    -/
    instance decidableLe (n m : ℕ₀) :
      Decidable (Le n m)
      :=
      match decidableLt n m with
      | isTrue h_lt => isTrue (Or.inl h_lt)
      | isFalse h_nlt =>
        match decEq n m with
        -- decEq proviene de `deriving DecidableEq` para ℕ₀
        | isTrue h_eq => isTrue (Or.inr h_eq)
        | isFalse h_neq =>
          isFalse (fun h_le_contra =>
          -- Asumimos Le n m para llegar a una contradicción
            match h_le_contra with
            | Or.inl h_lt_ev => h_nlt h_lt_ev
            -- contradicción con ¬(Lt n m)
            | Or.inr h_eq_ev => h_neq h_eq_ev
            -- contradicción con n ≠ m
          )

    -- Lemas útiles para Le

    theorem le_refl (n : ℕ₀) :
      Le n n
      :=
      Or.inr rfl

    theorem lt_imp_le (n m : ℕ₀) :
      Lt n m → Le n m
      :=
      fun h_lt => Or.inl h_lt

    theorem le_trans (n m k : ℕ₀) :
      Le n m → Le m k → Le n k
      :=
      fun h_le_nm h_le_mk =>
      match h_le_nm with
      | Or.inl h_lt_nm => -- Caso n < m
        match h_le_mk with
        | Or.inl h_lt_mk =>
          Or.inl (lt_trans n m k h_lt_nm h_lt_mk)
          -- m < k => n < k
        | Or.inr h_eq_mk =>
            by rw [h_eq_mk] at h_lt_nm; exact Or.inl h_lt_nm
            -- m = k => n < k (que es n < m)
      | Or.inr h_eq_nm => -- Caso n = m
          by rw [h_eq_nm]; exact h_le_mk -- n = m => (m ≤ k)

    theorem le_antisymm (n m : ℕ₀) :
      Le n m → Le m n → n = m
      :=
      fun h_le_nm h_le_mn =>
      match h_le_nm with
      | Or.inl h_lt_nm => -- n < m
        match h_le_mn with
        | Or.inl h_lt_mn =>
            (lt_asymm n m h_lt_nm h_lt_mn).elim
            -- n < m y m < n es contradicción
        | Or.inr h_eq_mn =>
            h_eq_mn.symm
            -- n < m y m = n es contradicción con lt_then_neq
      | Or.inr h_eq_nm =>
          h_eq_nm
          -- n = m, entonces trivialmente n = m

    theorem le_total (n m : ℕ₀) :
      Le n m ∨ Le m n
      :=
      match trichotomy n m with
      | Or.inl h_lt_nm =>
          Or.inl (lt_imp_le n m h_lt_nm)
          -- n < m => n ≤ m
      | Or.inr (Or.inl h_eq_nm) =>
          Or.inl (Or.inr h_eq_nm)
          -- n = m => n ≤ m
      | Or.inr (Or.inr h_lt_mn) =>
          Or.inr (lt_imp_le m n h_lt_mn)
          -- m < n => m ≤ n

    -- Relación entre Le y σ

    -- El teorema zero_le se mueve aquí porque se usa en le_iff_lt_succ.
    theorem zero_le (n : ℕ₀) :
      Le 𝟘 n
      :=
      match n with
      | 𝟘    => Or.inr rfl
      | σ n' => Or.inl (lt_0_n (σ n') (succ_neq_zero n'))

    theorem le_iff_lt_succ (n m : ℕ₀) :
      Le n m ↔ Lt n (σ m)
      := by
      constructor
      · intro h_le_nm
        rcases h_le_nm with h_lt_nm | h_eq_nm
        · -- Caso Lt n m. Queremos Lt n (σ m).
          -- Sabemos Lt m (σ m). Por transitividad: Lt n m → Lt m (σ m) → Lt n (σ m).
          exact lt_trans n m (σ m) h_lt_nm (lt_self_σ_self m)
        · -- Caso n = m. Queremos Lt m (σ m).
          rw [h_eq_nm]
          exact lt_self_σ_self m
      · intro h_lt_n_succ_m -- Lt n (σ m). Queremos Le n m.
        -- Usamos inducción sobre m generalizando n.
        induction m generalizing n with
        | zero => -- m = 𝟘. h_lt_n_succ_m : Lt n (σ 𝟘) (i.e. Lt n 𝟙).
                  -- Queremos Le n 𝟘.
          cases n with
          | zero => -- n = 𝟘. Lt 𝟘 𝟙 es true. Queremos Le 𝟘 𝟘.
            exact Or.inr rfl
          | succ n' => -- n = σ n'. h_lt_n_succ_m : Lt (σ n') (σ 𝟘).
                       -- Por lt_iff_lt_σ_σ, esto es Lt n' 𝟘.
            have h_lt_n_prime_zero : Lt n' 𝟘 := (lt_iff_lt_σ_σ n' 𝟘).mp h_lt_n_succ_m
            -- Lt n' 𝟘 contradice nlt_n_0 n'.
            exact (nlt_n_0 n' h_lt_n_prime_zero).elim
        | succ m' ih_m' => -- m = σ m'. h_lt_n_succ_m : Lt n (σ (σ m')).
                           -- Queremos Le n (σ m').
          cases n with
          | zero => -- n = 𝟘. h_lt_n_succ_m : Lt 𝟘 (σ (σ m')). Queremos Le 𝟘 (σ m').
            exact zero_le (σ m') -- Usamos el teorema zero_le.
          | succ n' => -- n = σ n'. h_lt_n_succ_m : Lt (σ n') (σ (σ m')).
                       -- Por lt_iff_lt_σ_σ, esto es Lt n' (σ m').
            have h_lt_n_prime_succ_m_prime : Lt n' (σ m') :=
              (lt_iff_lt_σ_σ n' (σ m')).mp h_lt_n_succ_m
            -- Hipótesis inductiva: ih_m' (k : ℕ₀) (h_lt_k_succ_m_prime : Lt k (σ m')) : Le k m'.
            -- Aplicamos IH a n' y h_lt_n_prime_succ_m_prime:
            have h_le_n_prime_m_prime : Le n' m' := ih_m' n' h_lt_n_prime_succ_m_prime
            -- Queremos Le (σ n') (σ m'). Sabemos Le n' m'.
            -- Esto se sigue de Le n' m' → Le (σ n') (σ m'), que es una parte de succ_le_succ_iff.
            -- Lo probamos inline:
            rcases h_le_n_prime_m_prime with h_lt_n_p_m_p | h_eq_n_p_m_p
            · -- Caso Lt n' m'. Entonces Lt (σ n') (σ m') por (lt_iff_lt_σ_σ n' m').mp.
              apply Or.inl
              exact (lt_iff_lt_σ_σ n' m').mp h_lt_n_p_m_p
            · -- Caso n' = m'. Entonces σ n' = σ m'.
              apply Or.inr
              rw [h_eq_n_p_m_p]

    theorem succ_le_succ_iff (n m : ℕ₀) : Le (σ n) (σ m) ↔ Le n m := by
      constructor
      · intro h_le_succ
        unfold Le at *
        rcases h_le_succ with h_lt_succ | h_eq_succ
        · -- Lt (σ n) (σ m) => Lt n m => Le n m
          apply Or.inl
          exact (lt_iff_lt_σ_σ n m).mpr h_lt_succ
        · -- σ n = σ m => n = m => Le n m
          apply Or.inr
          -- h_eq_succ es una prueba de σ n = σ m.
          -- σ.inj h_eq_succ es una prueba de n = m.
          -- (σ.inj h_eq_succ) ▸ rfl es una prueba de n = m.
          exact (ℕ₀.succ.inj h_eq_succ) ▸ rfl
      · intro h_le
        unfold Le at *
        rcases h_le with h_lt | h_eq
        · -- Lt n m => Lt (σ n) (σ m) => Le (σ n) (σ m)
          apply Or.inl
          exact (lt_iff_lt_σ_σ n m).mp h_lt
        · -- n = m => σ n = σ m => Le (σ n) (σ m)
          apply Or.inr
          exact h_eq ▸ rfl

    theorem not_succ_le_zero (n : ℕ₀) :
      ¬Le (σ n) 𝟘
      := by
      intro h_contra
      unfold Le at h_contra
      -- h_contra : (Lt (σ n) 𝟘) ∨ (σ n = 𝟘)
      -- Lt (σ n) 𝟘 es False.
      -- σ n = 𝟘 es False (por succ_neq_zero).
      -- Entonces False ∨ False, que es False. Contradicción.
      cases h_contra with
      | inl h_lt => exact (nlt_n_0 (σ n) h_lt).elim
      | inr h_eq => exact (succ_neq_zero n h_eq).elim

    theorem le_zero_eq (n : ℕ₀) :
      Le n 𝟘 → n = 𝟘
      := by
      intro h_le_n_zero
      unfold Le at h_le_n_zero
      rcases h_le_n_zero with h_lt_n_zero | h_eq_n_zero
      · -- Lt n 𝟘. Esto solo es posible si n no es sucesor,
        --   pero Lt n 𝟘 es siempre False.
        exact (nlt_n_0 n h_lt_n_zero).elim
      · -- n = 𝟘
        exact h_eq_n_zero

  theorem isomorph_Ψ_le (n m : ℕ₀) :
    Ψ n ≤ Ψ m ↔ Le n m
    := by
    constructor
    · -- Dirección →: (Ψ n ≤ Ψ m) → Le n m
      intro h_psi_le_psi_m -- h_psi_le_psi_m : Ψ n ≤ Ψ m
      -- Descomponemos Ψ n ≤ Ψ m usando el lema estándar para Nat.
      rw [Nat.le_iff_lt_or_eq] at h_psi_le_psi_m
      cases h_psi_le_psi_m with
      | inl h_psi_lt_psi_m => -- Caso Ψ n < Ψ m
        -- Queremos probar Le n m, específicamente Lt n m.
        apply Or.inl
        -- Asumimos que lt_iff_lt_Ψ_σ es (Ψ n < Ψ m) ↔ Lt n m.
        -- Entonces, (lt_iff_lt_Ψ_σ n m).mp transforma (Ψ n < Ψ m) en (Lt n m).
        exact (lt_iff_lt_Ψ_σ n m).mp h_psi_lt_psi_m
      | inr h_psi_eq_psi_m => -- Caso Ψ n = Ψ m
        -- Queremos probar Le n m, específicamente n = m.
        apply Or.inr
        -- Ψ_inj es la prueba de que Ψ es inyectiva: (Ψ n = Ψ m) → (n = m).
        exact Ψ_inj h_psi_eq_psi_m
    · -- Dirección ←: Le n m → (Ψ n ≤ Ψ m)
      intro h_le_nm -- h_le_nm : Le n m
      -- Por definición, Le n m es Lt n m ∨ n = m.
      cases h_le_nm with
      | inl h_lt_nm => -- Caso Lt n m
        -- Queremos probar Ψ n ≤ Ψ m, específicamente Ψ n < Ψ m.
        -- Asumimos que lt_iff_lt_Ψ_σ es (Ψ n < Ψ m) ↔ Lt n m.
        -- Entonces, (lt_iff_lt_Ψ_σ n m).mpr transforma (Lt n m) en (Ψ n < Ψ m).
        have h_psi_lt_psi_m : Ψ n < Ψ m := (lt_iff_lt_Ψ_σ n m).mpr h_lt_nm
        -- De Ψ n < Ψ m se sigue Ψ n ≤ Ψ m.
        exact Nat.le_of_lt h_psi_lt_psi_m
      | inr h_eq_nm => -- Caso n = m
        -- Queremos probar Ψ n ≤ Ψ m.
        -- Sustituimos n por m usando h_eq_nm. El objetivo se vuelve Ψ m ≤ Ψ m.
        rw [h_eq_nm]
        -- Esto es verdadero por reflexividad de ≤ para Nat.
        exact Nat.le_refl (Ψ m)

  theorem isomorph_Λ_le (n m : Nat) :
    n ≤ m ↔ Le (Λ n) (Λ m)
    := by
    sorry


  instance : LE ℕ₀ := ⟨Le⟩

  --instance : Ge ℕ₀ := ⟨Ge⟩

end Peano
