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

  theorem add_zero_l (n : ℕ₀) :
      add_l n 𝟘 = n
    := by
      induction n with
      | zero =>
              rfl
            | succ n' ih =>
        calc
          add_l (σ n') 𝟘 = σ (add n' 𝟘) := by simp [add_l]
          _ = σ n' := by rw [add_zero]
          _ = σ n' := rfl

  theorem zero_add (n : ℕ₀) : add 𝟘 n = n
    := by
      induction n with
      | zero => simp [add]
      | succ n' ih => simp [add]; exact ih

  theorem zero_add_l (n : ℕ₀) :
      add_l 𝟘 n = n
          := by
            induction n with
            | zero =>
              simp [add_l]
            | succ n' ih =>
              calc
                add_l 𝟘 (σ n') = σ (add_l 𝟘 n') := by
                  simp [add_l]
                _ = σ n' := rfl

  theorem add_zero_eq_add_l_zero (n : ℕ₀) :
    add n 𝟘 = add_l n 𝟘
      := by
        induction n with
        | zero => rfl
        | succ n' ih =>
          simp [add, add_l, add_zero, add_zero_l]

  theorem add_one (n : ℕ₀) : add n 𝟙 = σ n
    := by
      induction n with
      | zero => rfl
      | succ n' ih => unfold add; rw [<-ih]; rfl

  theorem add_one_l (n : ℕ₀) : add_l n 𝟙 = σ n
    := by
      induction n with
      | zero =>
          rfl
      | succ n' ih => -- ih: add_l n' 𝟙 = σ n'
                      -- Objetivo: add_l (σ n') 𝟙 = σ (σ n')
          calc
            add_l (σ n') 𝟙 = σ (add n' 𝟙) := by simp [add_l]
            _ = σ (σ n') := by rw [add_one]

  theorem one_add (n : ℕ₀) : add 𝟙 n = σ n
    := by
      induction n with
      | zero => rfl
      | succ n' ih => unfold add; rw [<-ih]

  theorem one_add_l (n : ℕ₀) : add_l 𝟙 n = σ n
    := by
      induction n with
      | zero =>
          simp [add_l, one, add_zero]
      | succ n' ih => -- ih: add_l 𝟙 n' = σ n'
                      -- Objetivo: add_l 𝟙 (σ n') = σ (σ n')
          calc
            add_l 𝟙 (σ n') = σ (add_l 𝟙 n') := by simp [add_l, one, zero_add]
            _ = σ (σ n') := by rw [ih]

  theorem add_one_eq_add_l_one (n : ℕ₀) :
    add n 𝟙 = add_l n 𝟙
      := by
        induction n with
        | zero => rfl
        | succ n' ih =>
          calc
            add (σ n') (σ 𝟘) = σ (add (σ n') 𝟘) := by rfl
            _ = σ (σ n') := by rw [add_zero]
            _ = σ (add_l (σ n') 𝟘) := by simp [add_zero_l]

  theorem add_succ (n m : ℕ₀) : add n (σ m) = σ (add n m)
    := by
      induction n with
      | zero => simp [add]
      | succ n' ih => simp [add]

  theorem add_succ_l (n m : ℕ₀) : add_l n (σ m) = σ (add_l n m)
    := by
      induction n with
      | zero =>
        simp [add_l]
      | succ n' ih =>
        simp [add_l] -- Esto transforma el objetivo add_l (σ n') (σ m) = σ (add_l (σ n') m)
                     -- en σ (add n' (σ m)) = σ (σ (add n' m)).
                     -- Por inyectividad de σ, esto es equivalente a add n' (σ m) = σ (add n' m).
        exact add_succ n' m -- Este es el teorema add_succ aplicado a n' y m.
      -- La hipótesis inductiva ih: add_l n' (σ m) = σ (add_l n' m) no se usa directamente aquí,
      -- ya que la simplificación del objetivo lo alinea con otro teorema existente.

  theorem succ_add (n m : ℕ₀) : add (σ n) m = σ (add n m)
    := by
      induction m with
      | zero => rw [add, add]
      | succ n' ih => simp [add]; rw [ih]

  theorem succ_add_l (n m : ℕ₀) : add_l (σ n) m = σ (add_l n m) := by
    unfold add_l -- Desplegamos la definición de add_l en ambos lados.
    cases n with
    | zero =>
      calc
        σ (add 𝟘 m) = σ m := by rw [zero_add]
        _ = σ (match 𝟘 with | 𝟘 => m | σ n' => σ (add n' m)) := by simp
    | succ n' =>
      dsimp
      rw [succ_add n' m]

    theorem add_succ_eq_add_l_succ (n m: ℕ₀) :
        add n (σ m) = add_l n (σ m)
            := by
        induction n with
        | zero => simp [add, add_l, zero_add]
        | succ n' ih =>
          calc
            add (σ n') (σ m) = σ (add (σ n') m)    := by rw [add_succ]
            _ = σ (σ (add n' m))                  := by rw [succ_add]
            _ = σ (add n' (σ m))                  := by rw [add_succ]
            _ = σ (add_l n' (σ m))                := by rw [ih]
            _ = add_l (σ n') (σ m)                := by rw [succ_add_l]

  theorem add_eq_add_l (n m : ℕ₀) :
    add n m = add_l n m
      := by
        induction n with
        | zero => rw [zero_add, zero_add_l]
        | succ n' ih =>
          calc
            add (σ n') m = σ (add n' m) := by rw [succ_add] -- Corregido: add_succ -> succ_add
            _ = σ (add_l n' m) := by rw [ih]
            _ = add_l (σ n') m := by rw [succ_add_l]

  theorem eq_fn_add_add_l :
    ∀ (n m : ℕ₀), add n m = add_l n m
      := by
        intro n m
        exact add_eq_add_l n m

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
      intro h_lt   -- Solo introducimos la hipótesis h_lt, no las variables que ya están en el contexto
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
    (add n m) ≤ (add n k) → m ≤ k
      := by
        intro h_le
        induction n with
        | zero =>
            rw [zero_add, zero_add] at h_le;
            exact h_le
        | succ n' ih => -- ih : (add n' m) ≤ (add n' k) → m ≤ k
                        -- h_le : (add (σ n') m) ≤ (add (σ n') k)
            -- El objetivo es demostrar m ≤ k
            -- Primero, reescribimos h_le usando las propiedades de la suma con el sucesor.
            rw [succ_add, succ_add] at h_le -- Ahora h_le : σ (add n' m) ≤ σ (add n' k)
            -- Aplicamos la hipótesis inductiva 'ih'. Esto cambia el objetivo a (add n' m) ≤ (add n' k).
            apply ih
            -- Para demostrar (add n' m) ≤ (add n' k), usamos h_le y el hecho de que σ x ≤ σ y → x ≤ y.
            -- Esta propiedad es provista por succ_le_succ_iff.
            exact (succ_le_succ_iff (add n' m) (add n' k)).mp h_le


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
            apply (succ_le_succ_iff _ _).mpr
            exact h_le
        | succ b' ih =>
            rw [add_one, add_one]
            apply (succ_le_succ_iff _ _).mpr
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
            apply (succ_le_succ_iff a b).mpr -- Objetivo: Le a b
            exact h_le
        | succ n' ih =>
            rw [add_succ, add_succ]
            -- Reescribe el objetivo a Le (σ (add a (σ n'))) (σ (add b (σ n')))
            apply (succ_le_succ_iff (add a (σ n')) (add b (σ n'))).mpr
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
          apply (succ_le_succ_iff _ _).mpr -- Reemplaza la línea original
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
        exact (succ_le_succ_iff a b).mp h_le

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
                := (succ_le_succ_iff _ _).mp h_le_add_implies_succ
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
                := (succ_le_succ_iff _ _).mp h_le_add
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
            exact Or.inr (Eq.refl 𝟘)
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

-- Define el teorema lt_of_le_of_ne que establece que si a ≤ b y a ≠ b entonces a < b
  theorem lt_of_le_of_ne (a b : ℕ₀) :
    Le a b → a ≠ b → Lt a b
      := by
        -- Le a b está definido como Lt a b ∨ a = b en PeanoNatOrder
        -- Si Le a b ∧ a ≠ b, entonces a < b
        intro h_le h_ne
        cases h_le with
        | inl h_lt => exact h_lt
        | inr h_eq => contradiction

  theorem zero_lt_succ (n : ℕ₀) :
    Lt 𝟘 (σ n)
      := by
        induction n with
        | zero =>
          -- Caso n = 𝟘, entonces σ n = 𝟙
          calc
            Lt 𝟘 𝟙 := lt_succ_self 𝟘
            _ = σ 𝟘 := rfl
        | succ n' ih =>
          -- Caso n = σ n', entonces σ n = σ (σ n')
          calc
            Lt 𝟘 (σ (σ n')) := lt_succ_self 𝟘
            _ = σ (σ n') := rfl

  theorem lt_add_succ (a p : ℕ₀) :
    Lt a (σ (add a p))
      := by
      induction p with
      | zero =>
        -- Caso p = 𝟘, entonces σ (add a 𝟘) = σ a
        rw [add_zero]
        exact lt_succ_self a
      | succ p' ih =>
        -- Caso p = σ p', entonces σ (add a (σ p')) = σ (σ (add a p'))
        rw [add_succ]
        -- Ahora el objetivo es Lt a (σ (σ (add a p')))))
        -- Aplicamos la transitividad de Lt con σ (add a p') como intermediario
        apply lt_trans a (σ (add a p')) (σ (σ (add a p')))
        · exact ih  -- Lt a (σ (add a p'))
        · exact lt_succ_self (σ (add a p'))

  theorem lt_succ_iff_lt_or_eq(n m : ℕ₀) :
    Lt n (σ m) ↔ Lt n m ∨ n = m
      := by
        constructor
        · -- Prueba de: Lt n (σ m) → Lt n m ∨ n = m
          intro h_lt_n_sm -- h_lt_n_sm: Lt n (σ m)
          induction m generalizing n with -- Inducción sobre m, n es general para la HI
          | zero => -- m = 𝟘
            -- h_lt_n_sm es Lt n (σ 𝟘)
            -- Objetivo: Lt n 𝟘 ∨ n = 𝟘
            -- Sin pérdida de generalidad, supongamos que n es σ n' para algún n'.
            cases n with
            | zero => -- n = 𝟘
              -- h_lt_n_sm se convierte en Lt 𝟘 (σ 𝟘) (lo cual es cierto).
              -- El objetivo se convierte en Lt 𝟘 𝟘 ∨ 𝟘 = 𝟘.
              -- Lt 𝟘 𝟘 es falso. 𝟘 = 𝟘 es verdadero.
              apply Or.inr
              rfl -- Prueba 𝟘 = 𝟘, ahora válido.
            | succ n' => -- n = σ n'
              -- h_lt_n_sm es Lt (σ n') (σ 𝟘).
              -- El objetivo es Lt (σ n') 𝟘 ∨ σ n' = 𝟘.
              -- De h_lt_n_sm: Lt (σ n') (σ 𝟘), por (succ_lt_succ_iff n' 𝟘).mp, obtenemos Lt n' 𝟘.
              have h_n'_lt_zero : Lt n' 𝟘 := (succ_lt_succ_iff n' 𝟘).mp h_lt_n_sm
              -- Lt n' 𝟘 es falso (por Peano.lt_zero n' o Peano.not_lt_zero n').
              exfalso
              -- Asumiendo que Peano.lt_zero está definido como ∀ k, Lt k 𝟘 → False o similar.
              -- O usar Peano.not_lt_zero n' h_n'_lt_zero si esa es la forma disponible.
              exact (Peano.lt_zero n' h_n'_lt_zero)
          | succ m' ih_m' => -- m = σ m'
            -- ih_m' : ∀ (k : ℕ₀), Lt k (σ m') → Lt k m' ∨ k = m'
            -- h_lt_n_sm es Lt n (σ (σ m'))
            -- Objetivo: Lt n (σ m') ∨ n = σ m'
            cases n with
            | zero => -- n = 𝟘
              -- h_lt_n_sm es Lt 𝟘 (σ (σ m')) (verdadero por zero_lt_succ (σ m'))
              -- Objetivo: Lt 𝟘 (σ m') ∨ 𝟘 = σ m'
              -- Lt 𝟘 (σ m') es verdadero por zero_lt_succ m'
              exact Or.inl (zero_lt_succ m')
            | succ n' => -- n = σ n' (este n' es local a este caso `succ n'`)
              -- h_lt_n_sm es Lt (σ n') (σ (σ m'))
              -- Objetivo: Lt (σ n') (σ m') ∨ σ n' = σ m'
              -- De h_lt_n_sm (i.e. Lt (σ n') (σ (σ m'))), por succ_lt_succ_iff: Lt n' (σ m')
              have h_lt_n'_sm' : Lt n' (σ m') := (succ_lt_succ_iff n' (σ m')).mp h_lt_n_sm
              -- Aplicar HI: ih_m' n' h_lt_n'_sm' da (Lt n' m' ∨ n' = m')
              cases ih_m' n' h_lt_n'_sm' with
              | inl h_lt_n'_m' => -- Caso 1: Lt n' m'
                -- Objetivo: Lt (σ n') (σ m') ∨ σ n' = σ m'
                -- Si Lt n' m', entonces Lt (σ n') (σ m') por succ_lt_succ_iff n' m'
                have h_lt_sn'_sm' : Lt (σ n') (σ m') := (succ_lt_succ_iff n' m').mpr h_lt_n'_m'
                exact Or.inl h_lt_sn'_sm'
              | inr h_n'_eq_m' => -- Caso 2: n' = m'
                -- Objetivo: Lt (σ n') (σ m') ∨ σ n' = σ m'
                -- Si n' = m', entonces σ n' = σ m'
                have h_sn'_eq_sm' : σ n' = σ m' := by rw [h_n'_eq_m']
                exact Or.inr h_sn'_eq_sm'
        · intro h
          cases h with
          | inl h_lt => exact lt_trans n m (σ m) h_lt (lt_succ_self m)
          | inr h_eq => rw [h_eq]; exact lt_succ_self m

  theorem le_succ_iff_le_or_eq (a b : ℕ₀) :
    Le a (σ b) ↔ Le a b ∨ a = σ b
      := by
        constructor
        · intro h_le
          induction b with
          | zero =>
            -- Caso b = 𝟘, entonces σ b = 𝟙 (o σ 𝟘). h_le es Le a (σ 𝟘).
            -- Objetivo: Le a 𝟘 ∨ a = σ 𝟘.
            -- El bloque calc demuestra Le a (σ 𝟘) ↔ (a = 𝟘 ∨ a = 𝟙)
            have equiv_calc : Le a (σ 𝟘) ↔ (a = 𝟘 ∨ a = 𝟙) := calc
              Le a (σ 𝟘) ↔ Le a 𝟙 := by simp [Peano.one] -- Usamos 𝟙 como alias de σ 𝟘
              _ ↔ Lt a 𝟙 ∨ a = 𝟙 := by rfl
              _ ↔ (a = 𝟘 ∨ a = 𝟙) := by -- Probamos esta equivalencia
                constructor
                · intro h_lt_or_eq_one -- Hipótesis: Lt a 𝟙 ∨ a = 𝟙
                  -- Objetivo: a = 𝟘 ∨ a = 𝟙
                  cases h_lt_or_eq_one with
                  | inl h_a_lt_one => -- Caso: Lt a 𝟙
                    -- Objetivo: a = 𝟘 (para la parte izquierda de la disyunción final)
                    apply Or.inl
                    -- Probamos a = 𝟘 a partir de Lt a 𝟙 (que es Lt a (σ 𝟘))
                    -- Por lt_succ_iff_lt_or_eq: Lt a (σ 𝟘) ↔ (Lt a 𝟘 ∨ a = 𝟘)
                    -- Como Lt a 𝟘 es falso, se sigue que a = 𝟘.
                    cases (lt_succ_iff_lt_or_eq a 𝟘).mp h_a_lt_one with
                    | inl h_lt_a_zero => exfalso; exact Peano.lt_zero a h_lt_a_zero
                    | inr h_a_eq_zero => exact h_a_eq_zero
                  | inr h_a_eq_one => -- Caso: a = 𝟙
                    -- Objetivo: a = 𝟙 (para la parte derecha de la disyunción final)
                    exact Or.inr h_a_eq_one
                · intro h_zero_or_one -- Hipótesis: a = 𝟘 ∨ a = 𝟙
                  -- Objetivo: Lt a 𝟙 ∨ a = 𝟙
                  cases h_zero_or_one with
                  | inl h_a_eq_zero => -- Caso: a = 𝟘
                    rw [h_a_eq_zero] -- Sustituimos a por 𝟘
                    -- Objetivo: Lt 𝟘 𝟙 ∨ 𝟘 = 𝟙. Lt 𝟘 𝟙 es verdadero.
                    exact Or.inl (lt_succ_self 𝟘)
                  | inr h_a_eq_one => -- Caso: a = 𝟙
                    rw [h_a_eq_one] -- Sustituimos a por 𝟙
                    -- Objetivo: Lt 𝟙 𝟙 ∨ 𝟙 = 𝟙. 𝟙 = 𝟙 es verdadero.
                    exact Or.inr (Eq.refl 𝟙)

            -- Usamos la equivalencia demostrada por el calc block.
            -- h_le es Le a (σ 𝟘). equiv_calc.mp h_le nos da (a = 𝟘 ∨ a = 𝟙).
            -- El objetivo es (Le a 𝟘 ∨ a = σ 𝟘).
            cases equiv_calc.mp h_le with
            | inl h_a_eq_zero => -- Caso: a = 𝟘
              rw [h_a_eq_zero] -- Sustituimos a por 𝟘 en el objetivo.
              -- Objetivo: Le 𝟘 𝟘 ∨ 𝟘 = σ 𝟘. Le 𝟘 𝟘 es verdadero.
              exact Or.inl (le_refl 𝟘)
            | inr h_a_eq_one => -- Caso: a = 𝟙 (que es σ 𝟘)
              rw [h_a_eq_one] -- Sustituimos a por 𝟙 en el objetivo.
              -- Objetivo: Le (σ 𝟘) 𝟘 ∨ σ 𝟘 = σ 𝟘. σ 𝟘 = σ 𝟘 es verdadero.
              exact Or.inr (Eq.refl (σ 𝟘))
          | succ b' ih =>
            -- h_le es Le a (σ (σ b'))
            -- El objetivo es Le a (σ b') ∨ a = σ (σ b')
            -- Por definición, Le a (σ (σ b')) es (Lt a (σ (σ b'))) ∨ (a = σ (σ b')).
            cases h_le with
            | inl h_lt_a_ssb' => -- Caso Lt a (σ (σ b'))
              -- Usamos lt_succ_iff_lt_or_eq para a y (σ b'):
              -- Lt a (σ (σ b')) ↔ Lt a (σ b') ∨ a = σ b'
              have h_choices := (lt_succ_iff_lt_or_eq a (σ b')).mp h_lt_a_ssb'
              cases h_choices with
              | inl h_lt_a_sb' => -- Subcaso Lt a (σ b')
                -- Probamos el lado izquierdo del objetivo: Le a (σ b').
                -- Le a (σ b') se define como Lt a (σ b') ∨ a = σ b'.
                -- Tenemos Lt a (σ b'), así que Or.inl h_lt_a_sb' prueba Le a (σ b').
                exact Or.inl (Or.inl h_lt_a_sb')
              | inr h_a_eq_sb' => -- Subcaso a = σ b'
                -- Probamos el lado izquierdo del objetivo: Le a (σ b').
                -- Si a = σ b', entonces Le a (σ b') es Le (σ b') (σ b').
                -- Le (σ b') (σ b') se prueba por reflexividad (Or.inr rfl).
                -- Usamos h_a_eq_sb' ▸ para sustituir 'a' en la prueba de Le (σ b') (σ b').
                exact Or.inl (h_a_eq_sb' ▸ (Or.inr rfl : Le (σ b') (σ b')))
            | inr h_a_eq_ssb' => -- Caso a = σ (σ b')
              -- Probamos el lado derecho del objetivo: a = σ (σ b').
              exact Or.inr h_a_eq_ssb'
        · intro h
          cases h with
          | inl h_a_le_b' =>
            exact le_trans a b (σ b) h_a_le_b' (le_succ_self b)
          | inr h_a_eq_succ_b =>
            rw [h_a_eq_succ_b]
            exact (le_refl (σ b))

  theorem lt_then_exists_add_succ (a b : ℕ₀) :
    Lt a b → ∃ (p : ℕ₀), b = add a (σ p) := by
      intro h_lt -- Assume Lt a b
    -- We proceed by induction on b, generalizing a.
    -- This means the inductive hypothesis will hold for any 'a_ih'.
      induction b generalizing a with
      | zero =>
        -- Case b = 𝟘.
        -- h_lt becomes Lt a 𝟘.
        -- We need to show ∃ (p : ℕ₀), 𝟘 = add a (σ p).
        -- However, Lt a 𝟘 is false for any a. We can use this to prove anything   (exfalso).
        exfalso -- We want to prove False
        exact Peano.lt_zero a h_lt -- This uses h_lt : Lt a 𝟘 and not_lt_zero : ¬ (Lt a   𝟘) to derive False
      | succ b' ih =>
        -- Case b = σ b'.
        -- ih (the inductive hypothesis) is:
        --   ∀ (a_ih : ℕ₀), Lt a_ih b' → ∃ (p : ℕ₀), b' = add a_ih (σ p)
        -- h_lt is Lt a (σ b').
        -- We need to show ∃ (p : ℕ₀), σ b' = add a (σ p).

        -- From Peano.lt_succ_iff_lt_or_eq (n m : ℕ₀) : Lt n (σ m) ↔ Lt n m ∨ n = m
        -- So h_lt : Lt a (σ b') gives Lt a b' ∨ a = b'
        have h_cases : Lt a b' ∨ a = b' := (lt_succ_iff_lt_or_eq a b').mp h_lt

        cases h_cases with
        | inl h_a_lt_b' =>
          -- Case 1: Lt a b'
          -- We can apply the inductive hypothesis 'ih' with 'a' and 'h_a_lt_b''.
          obtain ⟨p_val, h_b_prime_eq_add⟩ : ∃ p, b' = add a (σ p) := ih a h_a_lt_b'
          -- So, b' = add a (σ p_val).
          -- We want to show ∃ (p_new : ℕ₀), σ b' = add a (σ p_new).
          -- Let's try p_new = σ p_val.
          exists (σ p_val)
          -- Goal is now: σ b' = add a (σ (σ p_val))
          rw [h_b_prime_eq_add] -- Goal: σ (add a (σ p_val)) = add a (σ (σ p_val))
          -- Apply add_succ to the RHS: add a (σ (σ p_val)) = σ (add a (σ p_val))
          rw [Peano.add_succ a (σ p_val)] -- Goal: σ (add a (σ p_val)) = σ (add a (σ p_val))
                                          -- This is true by reflexivity (rfl implied)
        | inr h_a_eq_b' =>        -- Case 2: a = b'
          -- We want to show ∃ (p : ℕ₀), σ b' = add a (σ p)
          -- Substitute a = b': ∃ (p : ℕ₀), σ b' = add b' (σ p)
          -- Let p be 𝟘.
          exists 𝟘
          -- Goal is now: σ b' = add a 𝟘
          rw [h_a_eq_b'] -- Goal: σ b' = add b' (σ 𝟘)
          -- Using Peano.add_succ b' 𝟘, which is add b' (σ 𝟘) = σ (add b' 𝟘)
          rw [Peano.add_succ b' 𝟘] -- Goal: σ b' = σ (add b' 𝟘)
          -- Using Peano.add_zero b', which is add b' 𝟘 = b'
          rw [Peano.add_zero b'] -- Goal: σ b' = σ b'
                                 -- This is true by reflexivity (rfl implied)


  theorem le_iff_exists_add (a b: ℕ₀) :
      (Le a b) ↔ (∃ (p : ℕ₀), b = add a p)
      := by
        constructor
        · intro h_le
          induction b generalizing a with
          | zero =>
            -- Caso b = 𝟘, entonces a debe ser 𝟘 para que Le a b sea verdadero.
            cases a with
            | zero =>
              exists 𝟘
            | succ a' => -- Cambiado _ a a' para tener un nombre
              exfalso
              -- El bloque de código incorrecto que comenzaba con comentarios y un 'cases' se reemplaza.
              -- h_le es Le (σ a') 𝟘.
              -- (Peano.succ_neq_zero a') es σ a' ≠ 𝟘.
              -- Por lt_of_le_of_ne, esto da Lt (σ a') 𝟘.
              -- Por Peano.lt_zero (σ a'), esto da False.
              apply Peano.lt_zero (σ a')
              exact Peano.lt_of_le_of_ne (σ a') 𝟘 h_le (Peano.succ_neq_zero a')
          | succ b' ih =>
            -- h_le es Le a (σ b')
            -- ih es ∀ (a_ih : ℕ₀), Le a_ih b' → (∃ p, b' = add a_ih p)
            -- Usamos el teorema le_succ_iff_le_or_eq para dividir los casos de h_le
            -- Este teorema establece: Le a (σ b') ↔ Le a b' ∨ a = σ b'
            cases (Peano.le_succ_iff_le_or_eq a b').mp h_le with
            | inl h_a_le_b' => -- Caso Le a b'
              obtain ⟨p_val, h_b_prime_eq_add⟩ := ih a h_a_le_b'
              exists (σ p_val)
              rw [h_b_prime_eq_add, Peano.add_succ a p_val]
            | inr h_a_eq_succ_b' => -- Caso a = σ b'
              exists 𝟘
              rw [h_a_eq_succ_b', Peano.add_zero]
        · intro ⟨p, h_eq⟩
          -- Si `rw [h_eq]` da "no goals to be solved", el objetivo `Le a b`
          -- (estado después de `intro`) ya está resuelto.
          -- Por lo tanto, las siguientes líneas son innecesarias.
          -- rw [h_eq] -- Esta línea causaba el error.
          -- exact Peano.le_self_add a p -- Esta línea también sería innecesaria.
          -- Si el objetivo se resuelve con `intro`, no se necesita nada más.
          -- Sin embargo, para que la prueba sea lógicamente completa si `intro` no cierra el objetivo:
          rw [h_eq]
          exact Peano.le_self_add a p

  theorem lt_iff_exists_add_succ (a b : ℕ₀) :
    (Lt a b) ↔ (∃ (p : ℕ₀), b = add a (σ p))
      := by
        constructor
        · intro h_lt
          obtain ⟨p, h_eq⟩ : ∃ p, b = add a (σ p) := lt_then_exists_add_succ a b h_lt
          exists p
          rw [h_eq]
          rfl
        · intro ⟨p, h_eq⟩
          rw [h_eq]
          exact Peano.lt_add_succ a p -- Eliminado argumento espurio h_lt


  theorem lt_iff_add_cancel (a b : ℕ₀) :
      ∀ (k: ℕ₀), Lt (add a k) (add b k) ↔ Lt a b
        := by sorry

end Peano
