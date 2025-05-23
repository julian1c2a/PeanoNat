import PeanoNatLib.PeanoNatAxioms
import PeanoNatLib.PeanoNatStrictOrder
import PeanoNatLib.PeanoNatOrder
import PeanoNatLib.PeanoNatMaxMin

namespace PeanoNat

  def add (n m : ℕ₀) : ℕ₀ :=
    match m with
    | 𝟘 => n
    | σ m' => σ (add n m')

  instance : Add ℕ₀ where
    add := PeanoNat.add

  theorem add_zero (n : ℕ₀) : add n 𝟘 = n
    := by
      induction n with
      | zero => simp [add]
      | succ n' ih => simp [add]

  theorem zero_add (n : ℕ₀) : add 𝟘 n = n
    := by
      induction n with
      | zero => simp [add]
      | succ n' ih => simp [add]; exact ih

  theorem add_one (n : ℕ₀) : add n 𝟙 = σ n
    := by
      induction n with
      | zero => rfl
      | succ n' ih => unfold add; rw [<-ih]; rfl

  theorem one_add (n : ℕ₀) : add 𝟙 n = σ n
    := by
      induction n with
      | zero => rfl
      | succ n' ih => unfold add; rw [<-ih]

  theorem add_succ (n m : ℕ₀) : add n (σ m) = σ (add n m)
    := by
      induction n with
      | zero => simp [add]
      | succ n' ih => simp [add]

  theorem succ_add (n m : ℕ₀) : add (σ n) m = σ (add n m)
    := by
      induction m with
      | zero => rw [add, add]
      | succ n' ih => simp [add]; rw [ih]

  theorem add_comm (n m : ℕ₀) : add n m = add m n
    := by
      induction n with
      | zero => rw [zero_add]; rw [add_zero]
      | succ n' ih => rw [succ_add]; rw [ih]; exact add_succ m n'

  theorem add_assoc (n m k : ℕ₀) : add n (add m k) = add (add n m) k
    := by
      induction n with
      | zero => rw [zero_add]; rw [zero_add]
      | succ n' ih => rw [succ_add]; rw [ih]; rw [succ_add]; rw [succ_add]

  theorem add_le (a b c : ℕ₀) : Le a b → Le a (add b c) := by
    intro h_le
    induction c with
    | zero => rw [add_zero]; exact h_le
    | succ c' ih => rw [add_succ]; exact le_succ a (add b c') ih

  theorem add_lt (n m k : ℕ₀) : Lt n m → Lt n (add m k)
    := by
      intro h_lt
      induction k with
      | zero => rw [add_zero]; exact h_lt
      | succ k' ih => rw [add_succ]; exact lt_succ n (add m k') ih

  theorem add_cancelation (n m k : ℕ₀) :
    add n m = add n k → m = k
      := by
        intro h_eq
        induction n with
        | zero => rw [zero_add, zero_add] at h_eq; exact h_eq
        | succ n' ih => rw [succ_add, succ_add] at h_eq; injection h_eq with h_m_eq_k; exact ih h_m_eq_k

  theorem cancelation_add (n m k : ℕ₀) :
    add m n = add k n → m = k
      := by
        intro h_eq
        induction n with
        | zero => rw [add_zero, add_zero] at h_eq; exact h_eq
        | succ n' ih => rw [add_succ, add_succ] at h_eq; injection h_eq with h_m_eq_k; exact ih h_m_eq_k

  theorem add_lt_cancelation (n m k : ℕ₀) :
    add n m < add n k → m < k
      := by
        intro h_lt
        induction n with
        | zero => rw [zero_add, zero_add] at h_lt; exact h_lt
        | succ n' ih => rw [succ_add, succ_add] at h_lt; exact ih h_lt

  theorem add_le_cancelation (n m k : ℕ₀) :
    Le (add n m) (add n k) → Le m k
      := by
        intro h_le
        induction n with
        | zero => rw [zero_add, zero_add] at h_le; exact h_le
        | succ n' ih => rw [succ_add, succ_add] at h_le; exact ih (le_of_succ_le_succ h_le)

  theorem add_eq_zero_iff (a b : ℕ₀) :
    add a b = 𝟘 ↔ a = 𝟘 ∧ b = 𝟘
      := by
        constructor
        · intro h_eq
          induction a with
          | zero => rw [zero_add] at h_eq; exact ⟨rfl, h_eq⟩
          | succ a' ih => rw [succ_add] at h_eq; exact PeanoNat.noConfusion h_eq
        · intro ⟨h_a_eq_zero, h_b_eq_zero⟩; rw [h_a_eq_zero, h_b_eq_zero]; rfl

  theorem le_iff_exists_add (a b : ℕ₀) :
    Le a b ↔ ∃ p, b = add a p
    := by
    constructor
    · intro h_le_a_b
      revert a
      induction b with
      | zero =>
        intro a_val h_a_le_zero
        have h_a_eq_zero : a_val = 𝟘 := le_n_zero_eq_zero a_val h_a_le_zero
        rw [h_a_eq_zero]
        exact Exists.intro 𝟘 rfl
      | succ k ih_k =>
        intro a_val h_a_le_succ_k
        have lemma_lt_succ_imp_le (curr_a curr_k_lemma : ℕ₀) : Lt curr_a (σ curr_k_lemma) → Le curr_a curr_k_lemma := by
          intro h_curr_a_lt_succ_curr_k_lemma
          induction curr_k_lemma generalizing curr_a with
          | zero =>
            cases curr_a with
            | zero => exact Le.refl_le
            | succ ca' =>
              unfold Lt at h_curr_a_lt_succ_curr_k_lemma
              exact False.elim (zero_is_the_minor ca' h_curr_a_lt_succ_curr_k_lemma)
          | succ k_prime ih_k_prime =>
            cases curr_a with
            | zero => exact le_zero (σ k_prime)
            | succ ca' =>
              unfold Lt at h_curr_a_lt_succ_curr_k_lemma
              apply le_succ_succ
              exact ih_k_prime ca' h_curr_a_lt_succ_curr_k_lemma
        cases (le_then_eq_xor_lt a_val (σ k)) h_a_le_succ_k with
        | inl h_a_eq_succ_k =>
          rw [h_a_eq_succ_k]
          exact Exists.intro 𝟘 (add_zero (σ k))
        | inr h_a_lt_succ_k =>
          have h_a_le_k : Le a_val k := lemma_lt_succ_imp_le a_val k h_a_lt_succ_k
          specialize ih_k a_val h_a_le_k
          cases ih_k with | intro p_prime h_k_eq_add_a_p_prime =>
            rw [h_k_eq_add_a_p_prime]
            exact Exists.intro (σ p_prime) rfl
    · intro h_exists
      cases h_exists with | intro p_val h_b_eq_add_a_p_val =>
        rw [h_b_eq_add_a_p_val]
        clear h_b_eq_add_a_p_val
        induction p_val with
        | zero => rw [add_zero]; exact Le.refl_le
        | succ p_prime ih_p_prime => rw [add_succ]; exact le_succ a (add a p_prime) ih_p_prime

  theorem lt_add_cancel (a b : ℕ₀) :
    Lt a b ↔ ∀ (k: ℕ₀), Lt (add a k) (add b k)
      := by
        constructor
        · intro h_lt_a_b; intro k_val
          induction k_val with
          | zero => rw [add_zero]; exact h_lt_a_b
          | succ k' ih_k' => rw [add_succ, add_succ]; unfold Lt; exact ih_k'
        · intro h_add_lt; have h_add_lt_zero : Lt (add a 𝟘) (add b 𝟘) := h_add_lt 𝟘; exact h_add_lt_zero

  theorem lt_iff_exists_add_succ (a b : ℕ₀) :
    Lt a b ↔ ∃ p, b = add a (σ p)
      := by
        constructor
        · intro h_lt_a_b
          have h_le_a_b : Le a b := Le.strict_lt h_lt_a_b
          have h_exists_q := (le_iff_exists_add a b).mp h_le_a_b
          cases h_exists_q with | intro q h_b_eq_add_a_q =>
            have h_a_neq_b : a ≠ b := lt_n_m_then_neq_n_m a b h_lt_a_b
            cases q with
            | zero => rw [h_b_eq_add_a_q, add_zero] at h_a_neq_b; exact False.elim (h_a_neq_b rfl)
            | succ p => exists p
        · intro h_exists
          cases h_exists with | intro p h_b_eq_add_a_succ_p =>
            subst h_b_eq_add_a_succ_p
            induction p with
            | zero => rw [add_succ, add_zero]; exact lt_n_succ_n a
            | succ p' ih => rw [add_succ]; exact lt_succ a (add a (succ p')) ih

end PeanoNat
