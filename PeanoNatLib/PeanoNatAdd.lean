import PeanoNatLib.PeanoNatAxioms
import PeanoNatLib.PeanoNatStrictOrder
import PeanoNatLib.PeanoNatOrder
import PeanoNatLib.PeanoNatMaxMin

open Peano
namespace Peano

  def add (n m : ℕ₀) : ℕ₀ :=
    match m with
    | 𝟘 => n
    | σ m' => σ (add n m')

  instance : Add ℕ₀ where
    add := Peano.add

  def add_l (n m : ℕ₀) : ℕ₀ :=
    match n with
    | 𝟘 => m
    | σ n' => σ (add n' m)



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
    | succ c' ih =>
        exact le_trans a (add b c') (add b (σ c')) ih (le_succ_self (add b c'))

  theorem add_lt (n m k : ℕ₀) : Lt n m → Lt n (add m k)
    := by
      intro h_lt
      induction k with
      | zero => rw [add_zero]; exact h_lt
      | succ k' ih => rw [add_succ]; exact Peano.lt_succ n (add m k') ih

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
        | zero =>
            rw [zero_add, zero_add] at h_le;
            exact h_le
        | succ n' ih =>
            rw [succ_add, succ_add] at h_le;
            exact ih ((le_of_succ_le_succ (add n' m) (add n' k)).mp h_le)

  theorem add_eq_zero_iff (a b : ℕ₀) :
    add a b = 𝟘 ↔ a = 𝟘 ∧ b = 𝟘
      := by
        constructor
        · intro h_eq
          induction a with
          | zero =>
            rw [zero_add] at h_eq;
            exact ⟨rfl, h_eq⟩
          | succ a' ih =>
            rw [succ_add] at h_eq;
            have h_contradiction : σ (add a' b) = 𝟘
              := h_eq
            have h_absurd : σ (add a' b) ≠ 𝟘
              := succ_neq_zero (add a' b)
            contradiction
        · intro ⟨h_a_eq_zero, h_b_eq_zero⟩;
          rw [h_a_eq_zero, h_b_eq_zero];
          rfl

  theorem le_then_le_add_zero (a b : ℕ₀) :
    Le a b → Le (add a 𝟘) (add b 𝟘)
      := by
        intro h_le
        induction b with
        | zero =>
            rw [add_zero, add_zero];
            exact h_le
        | succ b' ih =>
            rw [add_zero, add_zero] -- Reescribe el objetivo Le (add a 0) (add (σ b') 0) a Le a (σ b')
            exact h_le -- Ahora el objetivo coincide con la hipótesis h_le

  theorem le_then_le_add_one (a b : ℕ₀) :
    Le a b → Le (add a 𝟙) (add b 𝟙)
      := by
        intro h_le
        induction b with
        | zero =>
            rw [add_one, add_one]
            apply (le_of_succ_le_succ _ _).mpr
            exact h_le
        | succ b' ih =>
            rw [add_one, add_one]
            apply (le_of_succ_le_succ _ _).mpr
            exact h_le


  theorem le_add_then_le_add_succ (a b n: ℕ₀) :
    Le (add a n) (add b n) → Le (add a (σ n)) (add b (σ n))
      := by
        intro h_le
        induction n with
        | zero =>
            rw [add_zero, add_zero] at h_le
            rw [add_succ, add_succ] -- Objetivo: Le (σ (add a 𝟘)) (σ (add b 𝟘))
            rw [add_zero, add_zero] -- Objetivo: Le (σ a) (σ b)
            apply (le_of_succ_le_succ a b).mpr -- Objetivo: Le a b
            exact h_le
        | succ n' ih =>
            rw [add_succ, add_succ]
            -- Reescribe el objetivo a Le (σ (add a (σ n'))) (σ (add b (σ n')))
            apply (le_of_succ_le_succ (add a (σ n')) (add b (σ n'))).mpr
            -- Cambia el objetivo a Le (add a (σ n')) (add b (σ n'))
            exact h_le
            -- Esto es la hipótesis original h_le : Le (add a (σ n')) (add b (σ n'))

  theorem le_then_le_add (a b c: ℕ₀) :
    Le a b → Le (add a c) (add b c)
      := by
      intro h_le -- Añadir intro h_le para que la hipótesis esté disponible
      induction c with
      | zero =>
          rw [add_zero, add_zero]
          exact (le_then_le_add_zero a b h_le)
          -- Usar el nombre correcto del teorema y pasar la hipótesis
      | succ c' ih =>
          rw [add_succ, add_succ]
          apply (le_of_succ_le_succ _ _).mpr -- Reemplaza la línea original
          exact ih -- La hipótesis inductiva 'ih' ya es el objetivo actual

theorem le_add_zero_then_le (a b : ℕ₀) :
    Le (add a 𝟘) (add b 𝟘) → Le a b
      := by
        intro h_le
        rw [add_zero, add_zero] at h_le
        exact h_le

theorem le_add_one_then_le (a b : ℕ₀) :
    Le (add a 𝟙) (add b 𝟙) → Le a b
      := by
        intro h_le
        rw [add_one, add_one] at h_le
        exact (le_of_succ_le_succ a b).mp h_le

theorem le_add_then_le_add_succ_then_le (a b n: ℕ₀) :
    Le (add a n) (add b n) → (Le a b)
      := by
        intro h_le_add_implies_succ -- Renombrar h_le_add para mayor claridad
        induction n with
        | zero =>
            rw [add_zero, add_zero] at h_le_add_implies_succ
            exact h_le_add_implies_succ
        | succ n' ih =>
            rw [add_succ, add_succ] at h_le_add_implies_succ
            -- Aplicamos le_of_succ_le_succ para "quitar" los σ.
            have h_base_le : Le (add a n') (add b n')
                := (le_of_succ_le_succ _ _).mp h_le_add_implies_succ
            exact ih h_base_le

  theorem le_add_then_le (a b c: ℕ₀) :
    Le (add a c) (add b c) → Le a b
      := by
        intro h_le_add
        induction c with
        | zero =>
            rw [add_zero, add_zero] at h_le_add
            exact h_le_add
        | succ c' ih =>
            rw [add_succ, add_succ] at h_le_add
            -- Aplicamos le_of_succ_le_succ para "quitar" los σ.
            have h_base_le : Le (add a c') (add b c')
                := (le_of_succ_le_succ _ _).mp h_le_add
            exact ih h_base_le

  theorem le_iff_le_add(a b c: ℕ₀) :
    Le a b ↔ Le (add a c) (add b c)
      := by
        constructor
        · intro h_le
          exact le_then_le_add a b c h_le
        · intro h_le_add
          exact le_add_then_le a b c h_le_add

  theorem le_iff_le_add_forall(a b : ℕ₀) :
    ∀ (k : ℕ₀), Le a b ↔ Le (add a k) (add b k)
      := by
        intro k
        constructor
        · intro h_le
          exact le_then_le_add a b k h_le
        · intro h_le_add
          exact le_add_then_le a b k h_le_add


  theorem le_add_cancel (a b : ℕ₀) :
      ∀ (k: ℕ₀), Le a b ↔ Le (add a k) (add b k)
        := by
        exact le_iff_le_add_forall a b

  theorem le_then_exists_zero_add (a : ℕ₀) :
    Le a (add a 𝟘) → Le a a
      := by
        intro h_le
        induction a with
        | zero =>
            rw [add_zero] at h_le
            exact Or.inr rfl
        | succ a' ih =>
            rw [add_zero] at h_le
            exact h_le

  theorem le_self_add (a p : ℕ₀) : Le a (add a p) := by
    induction p with
    | zero =>
      rw [add_zero]
      exact le_refl a -- Corregido de 'reflexivity'
    | succ p' ih =>
      rw [add_succ]    -- Meta aquí es Le a (σ (add a p'))
      apply le_succ    -- Aplicar Le.succ transforma la meta a Le a (add a p')
      exact ih         -- ih tiene tipo Le a (add a p'), que ahora coincide con la meta

  theorem le_self_add_forall (a : ℕ₀) :
    ∀ (p : ℕ₀), Le a (add a p)
      := by
    intro p
    -- Aquí se usa la inducción sobre p para demostrar Le a (add a p)
    induction p with
    | zero =>
      rw [add_zero]
      exact le_refl a -- Corregido de 'reflexivity'
    | succ p' ih =>
      rw [add_succ]    -- Meta aquí es Le a (σ (add a p'))
      apply le_succ    -- Aplicar Le.succ transforma la meta a Le a (add a p')
      exact ih         -- ih tiene tipo Le a (add a p'), que ahora coincide con la meta

  theorem le_iff_exists_add (a b: ℕ₀) :
    (Le a b) ↔ ∃ (p : ℕ₀), b = add a p
      := by
        constructor
        · intro h_le
          induction h_le with
          | refl a => -- En este caso, b se unifica con a (constructor Le.refl).
            exact ⟨𝟘, by rw [add_zero]⟩ -- Objetivo: a = add a 𝟘
          | succ b h_le_a_m ih_m => -- En este caso, b = σ m (constructor Le.succ), y tenemos h_le_a_m : Le a m.
            -- m : ℕ₀ (el valor tal que b = σ m en este caso de la inducción)
            -- h_le_a_m : Le a m (la premisa de la regla Le.succ)
            -- ih_m : ∃ p', m = add a p' (la hipótesis inductiva para h_le_a_m)
            rcases ih_m with ⟨p', h_m_eq_add_a_p'⟩
            -- Objetivo: ∃ p, b = add a p. Como b = σ m, es ∃ p, σ m = add a p
            -- Elegimos p = σ p'. Objetivo: σ m = add a (σ p')
            -- Usamos h_m_eq_add_a_p' para reescribir m: σ (add a p') = add a (σ p')
            -- Esto es una instancia de add_succ a p'.
            exact ⟨σ p', by rw [h_m_eq_add_a_p', add_succ]⟩
        · rintro ⟨p, h_eq⟩
          rw [h_eq] -- Objetivo: Le a (add a p)
          exact le_self_add_forall a p

  theorem lt_add_cancel (a b : ℕ₀) :
      ∀ (k: ℕ₀), Lt (add a k) (add b k) ↔ Lt a b
        := by sorry

  theorem lt_iff_exists_add_succ (a b : ℕ₀) :
    Lt a b ↔ ∃ p, b = add a (σ p)
      := by sorry

end Peano
