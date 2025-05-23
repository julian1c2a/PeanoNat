import PeanoNatLib.PeanoNatAxioms
import PeanoNatLib.PeanoNatStrictOrder -- Importa Lt y sus propiedades

open Peano
namespace Peano

    -- Definiciones y teoremas para Le (menor o igual)

    /-- Definición de "menor o igual que" para ℕ₀. -/
    def Le (n m : ℕ₀) : Prop := Lt n m ∨ n = m
    def Ge (n m : ℕ₀) : Prop := Lt m n ∨ n = m

    /--
    Función de ayuda para Le con repuesta buleana
    -/
    def BLe (n m : ℕ₀) : Bool :=
      match n , m with
      | 𝟘 , _ => true
      | _ , 𝟘 => false
      | σ n' , σ m' => BLe n' m'

    -- El teorema zero_le se mueve aquí porque se usa en BLe_iff_Le.
    theorem zero_le (n : ℕ₀) :
      Le 𝟘 n
      :=
      match n with
      | 𝟘    => Or.inr rfl
      | σ n' => Or.inl (lt_0_n (σ n') (succ_neq_zero n'))

    /--
    Función de ayuda para Ge con repuesta buleana
    -/
    def BGe (n m : ℕ₀) : Bool :=
      match n , m with
      |   _    ,   𝟘  => true
      |   𝟘    ,   _  => false
      | σ n'   , σ m' => BGe n' m'


/--!
    FALTA ESTE TEOREMA POR COMPLETITUD
    -- El teorema BLe_iff_Le se mueve aquí porque se usa
    -- en decidableLe.
    theorem BLe_iff_Le (n m : ℕ₀) :
    BLe n m = true ↔ Le n m
!--/


    instance decidableLe (n m : ℕ₀) :
      Decidable (Le n m)
      :=
      match decidableLt n m with
      | isTrue h_lt => isTrue (Or.inl h_lt)
      | isFalse h_nlt =>
        match decEq n m with
        | isTrue h_eq => isTrue (Or.inr h_eq)
        | isFalse h_neq =>
          isFalse (
            fun h_le_contra =>
              match h_le_contra with
              | Or.inl h_lt_ev => h_nlt h_lt_ev
              | Or.inr h_eq_ev => h_neq h_eq_ev
          )



/--!
    FALTA ESTE TEOREMA POR COMPLETITUD
    -- El teorema BGe_iff_Ge se mueve aquí porque se usa
    -- en decidableGe.
    theorem BGe_iff_Ge (n m : ℕ₀) :
    BGe n m = true ↔ Ge n m


-- El teorema BGe_iff_Ge se mueve aquí porque se usa
-- en decidableGe.

        Instancia Decidable para Ge n m.
        Se construye a partir de las instancias
        Decidable para Lt m n y n = m.
    -/
    instance decidableGe (n m : ℕ₀) :
      Decidable (Ge n m)
      :=
      match decidableLt m n with
      | isTrue h_lt => isTrue (Or.inl h_lt)
      | isFalse h_nlt =>
        match decEq n m with
        -- decEq proviene de `deriving DecidableEq` para ℕ₀
        | isTrue h_eq => isTrue (Or.inr h_eq)
        | isFalse h_neq =>
          isFalse (fun h_ge_contra =>
          -- Asumimos Ge n m para llegar a una contradicción
            match h_ge_contra with
            | Or.inl h_lt_ev => h_nlt h_lt_ev
            -- contradicción con ¬(Lt m n)
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
        | Or.inr h_eq_mk =>
            by rw [h_eq_mk] at h_lt_nm; exact Or.inl h_lt_nm
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
        | Or.inr h_eq_mn =>
            h_eq_mn.symm
      | Or.inr h_eq_nm =>
          h_eq_nm

    theorem le_total (n m : ℕ₀) :
      Le n m ∨ Le m n
      :=
      match trichotomy n m with
      | Or.inl h_lt_nm =>
          Or.inl (lt_imp_le n m h_lt_nm)
      | Or.inr (Or.inl h_eq_nm) =>
          Or.inl (Or.inr h_eq_nm)
      | Or.inr (Or.inr h_lt_mn) =>
          Or.inr (lt_imp_le m n h_lt_mn)

    theorem le_iff_lt_succ (n m : ℕ₀) :
      Le n m ↔ Lt n (σ m)
      := by
      constructor
      · intro h_le_nm
        rcases h_le_nm with h_lt_nm | h_eq_nm
        · -- Caso Lt n m. Queremos Lt n (σ m).
          exact lt_trans n m (σ m) h_lt_nm (lt_self_σ_self m)
        · -- Caso n = m. Queremos Lt m (σ m).
          rw [h_eq_nm]
          exact lt_self_σ_self m
      · intro h_lt_n_succ_m -- Lt n (σ m). Queremos Le n m.
        revert n h_lt_n_succ_m
        induction m with
        | zero => -- m = 𝟘.
          intro n h_lt_n_succ_zero_case
          cases n with
          | zero =>
            exact Or.inr rfl
          | succ n' =>
            have h_lt_n_prime_zero : Lt n' 𝟘 := (lt_iff_lt_σ_σ n' 𝟘).mp h_lt_n_succ_zero_case
            exact (nlt_n_0 n' h_lt_n_prime_zero).elim
        | succ m' ih_m' => -- m = σ m'.
          intro n h_lt_n_succ_sigma_m_prime_case
          cases n with
          | zero =>
            exact zero_le (σ m')
          | succ n' =>
            have h_lt_n_prime_succ_m_prime : Lt n' (σ m') :=
              (lt_iff_lt_σ_σ n' (σ m')).mp h_lt_n_succ_sigma_m_prime_case
            have h_le_n_prime_m_prime : Le n' m'
                := ih_m' n' h_lt_n_prime_succ_m_prime
            rcases h_le_n_prime_m_prime with h_lt_n_p_m_p | h_eq_n_p_m_p
            · -- Caso Lt n' m'.
              apply Or.inl
              exact (lt_iff_lt_σ_σ n' m').mpr h_lt_n_p_m_p
            · -- Caso n' = m'. Entonces σ n' = σ m'.
              apply Or.inr
              rw [h_eq_n_p_m_p]

    theorem succ_le_succ_iff (n m : ℕ₀) :
      Le (σ n) (σ m) ↔ Le n m
      := by
      constructor
      · intro h_le_succ
        unfold Le at *
        rcases h_le_succ with h_lt_succ | h_eq_succ
        · -- Lt (σ n) (σ m) => Lt n m => Le n m
          apply Or.inl
          exact (lt_iff_lt_σ_σ n m).mpr h_lt_succ
        · -- σ n = σ m => n = m => Le n m
          apply Or.inr
          exact ℕ₀.succ.inj h_eq_succ
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
      cases h_contra with
      | inl h_lt => exact (nlt_n_0 (σ n) h_lt).elim
      | inr h_eq => exact (succ_neq_zero n h_eq).elim

  theorem lt_then_le (a b : ℕ₀) :
    Lt a b → Le a b
      := by
        intro h_lt_a_b
        exact Or.inl h_lt_a_b

  theorem lt_of_le_neq (a b : ℕ₀) :
    Le a b → a ≠ b → Lt a b
      := by
        intro h_le h_neq
        cases h_le with
        | inl h_lt =>
          exact h_lt
        | inr h_eq =>
          exfalso
          exact h_neq h_eq

    theorem le_zero_eq (n : ℕ₀) :
      Le n 𝟘 → n = 𝟘
      := by
      intro h_le_n_zero
      unfold Le at h_le_n_zero
      rcases h_le_n_zero with h_lt_n_zero | h_eq_n_zero
      · -- Lt n 𝟘. Esto solo es posible si n no es sucesor,
        exact (nlt_n_0 n h_lt_n_zero).elim
      · -- n = 𝟘
        exact h_eq_n_zero

  theorem le_succ_self (n : ℕ₀) :
    Le n (σ n)
    := by
    unfold Le
    apply Or.inl
    exact lt_self_σ_self n

  theorem le_succ (n m : ℕ₀) :
      Le n m → Le n (σ m)
        := by
        intro h_le_nm
        unfold Le at *
        rcases h_le_nm with h_lt_nm | h_eq_nm
        · -- Caso Lt n m
          apply Or.inl
          exact lt_trans n m (σ m) h_lt_nm (lt_self_σ_self m)
        · -- Caso n = m
          apply Or.inl
          rw [h_eq_nm]
          exact lt_self_σ_self m

  theorem le_of_succ_le_succ (n m : ℕ₀):
      Le (σ n) (σ m) ↔ Le n m
      := by
    constructor
    · -- Dirección →: Le (σ n) (σ m) → Le n m
      intro h_le_σn_σm
      unfold Le at h_le_σn_σm
      rcases h_le_σn_σm with
        (h_lt_succ_n_succ_m | h_eq_succ_n_succ_m)
      · -- Caso Lt (σ n) (σ m)
        apply Or.inl
        exact (lt_iff_lt_σ_σ n m).mpr h_lt_succ_n_succ_m
      · -- Caso σ n = σ m
        apply Or.inr
        exact ℕ₀.succ.inj h_eq_succ_n_succ_m
    · -- Dirección ←: Le n m → Le (σ n) (σ m)
      intro h_le_nm
      unfold Le at h_le_nm ⊢
      cases h_le_nm with
        | inl h_lt_nm =>
          -- Caso Lt n m
          apply Or.inl
          exact (lt_iff_lt_σ_σ n m).mp h_lt_nm
        | inr h_eq_nm =>
          -- Caso n = m
          apply Or.inr
          rw [h_eq_nm]

  theorem isomorph_Ψ_le (n m : ℕ₀) :
    Ψ n ≤ Ψ m ↔ Le n m
    := by
    constructor
    · -- Dirección →: (Ψ n ≤ Ψ m) → Le n m
      intro h_psi_le_psi_m -- h_psi_le_psi_m : Ψ n ≤ Ψ m
      rw [Nat.le_iff_lt_or_eq] at h_psi_le_psi_m
      cases h_psi_le_psi_m with
      | inl h_psi_lt_psi_m => -- Caso Ψ n < Ψ m
        apply Or.inl
        exact (isomorph_lt_pea_lt_nat n m).mpr h_psi_lt_psi_m
      | inr h_psi_eq_psi_m => -- Caso Ψ n = Ψ m
        apply Or.inr
        exact (Ψ_inj n m h_psi_eq_psi_m)
    · -- Dirección ←: Le n m → (Ψ n ≤ Ψ m)
      intro h_le_nm -- h_le_nm : Le n m
      cases h_le_nm with
      | inl h_lt_nm => -- Caso Lt n m
        have h_psi_lt_psi_m : Ψ n < Ψ m
            := (isomorph_lt_pea_lt_nat n m).mp h_lt_nm
        exact Nat.le_of_lt h_psi_lt_psi_m
      | inr h_eq_nm => -- Caso n = m
        rw [h_eq_nm]
        exact Nat.le_refl (Ψ m)

  theorem isomorph_Λ_le (n m : Nat) :
    n ≤ m ↔ Le (Λ n) (Λ m)
    := by
    constructor
    · -- Dirección →: n ≤ m → Le (Λ n) (Λ m)
      intro h_n_le_m -- h_n_le_m : n ≤ m
      rw [Nat.le_iff_lt_or_eq] at h_n_le_m
      cases h_n_le_m with
      | inl h_lt_nm => -- Caso n < m
        apply Or.inl
        exact (isomorph_lt_pea_lt_nat (Λ n) (Λ m)).mpr (by { rw [ΨΛ, ΨΛ]; exact h_lt_nm })
      | inr h_eq_nm => -- Caso n = m
        apply Or.inr -- El objetivo es ahora Λ n = Λ m.
        rw [h_eq_nm] -- El objetivo se convierte en Λ m = Λ m.
    · -- Dirección ←: Le (Λ n) (Λ m) → n ≤ m
      intro h_le_Λn_Λm
      cases h_le_Λn_Λm with
      | inl h_lt_Λn_Λm => -- Caso Lt (Λ n) (Λ m)
        have h_psi_lt_psi_m : Ψ (Λ n) < Ψ (Λ m)
            := (isomorph_lt_pea_lt_nat (Λ n) (Λ m)).mp h_lt_Λn_Λm
        rw [ΨΛ, ΨΛ] at h_psi_lt_psi_m
        exact Nat.le_of_lt h_psi_lt_psi_m
      | inr h_eq_Λn_Λm => -- Caso Λ n = Λ m
        have h_n_eq_m : n = m := by
          have h_psi_eq : Ψ (Λ n) = Ψ (Λ m) := by rw [h_eq_Λn_Λm]
          rwa [ΨΛ, ΨΛ] at h_psi_eq
        rw [h_n_eq_m] -- El objetivo se convierte en m ≤ m.
        exact Nat.le_refl m

  instance : LE ℕ₀ := ⟨Le⟩

end Peano

export Peano (
  Le Ge BLe BGe
  decidableLe decidableGe
  le_refl
  lt_imp_le
  le_trans
  le_antisymm
  le_total
  le_iff_lt_succ
  succ_le_succ_iff
  not_succ_le_zero
  lt_then_le
  lt_of_le_neq
  le_zero_eq
  isomorph_Ψ_le
  isomorph_Λ_le
  lt_iff_lt_σ_σ
)
