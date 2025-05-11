-- PeanoNat.lean

inductive PeanoNat : Type where
  | zero : PeanoNat
  | succ : PeanoNat -> PeanoNat
  deriving Repr, BEq, DecidableEq

-- Namespace para todo lo relacionado directamente con el tipo PeanoNat
namespace PeanoNat

  -- === Definiciones básicas para PeanoNat ===
  def one : PeanoNat := succ zero
  def two : PeanoNat := succ one
  def three : PeanoNat := succ two
  def four : PeanoNat := succ three
  def five : PeanoNat := succ four
  def six : PeanoNat := succ five
  def seven : PeanoNat := succ six
  def eight : PeanoNat := succ seven
  def nine : PeanoNat := succ eight
  def ten : PeanoNat := succ nine
  def eleven : PeanoNat := succ ten
  def twelve : PeanoNat := succ eleven
  def thirteen : PeanoNat := succ twelve
  def fourteen : PeanoNat := succ thirteen
  def fifteen : PeanoNat := succ fourteen
  def sixteen : PeanoNat := succ fifteen

  def pred (n : PeanoNat) : PeanoNat :=
    match n with
    | zero => zero
    | succ k => k

  @[simp] theorem pred_succ_eq_self (n : PeanoNat) : pred (succ n) = n := by simp [pred]

  def nat0 : PeanoNat := zero
  def nat1 : PeanoNat := one
  def nat2 : PeanoNat := two

  -- === Teoremas básicos y propiedades de PeanoNat (definidos ANTES de usarlos en subtipos) ===
  @[simp]
  theorem succ_neq_zero (m : PeanoNat) : succ m ≠ zero :=
    fun h_eq_zero => PeanoNat.noConfusion h_eq_zero

  theorem neq_succ (k : PeanoNat) : k ≠ succ k := by
    induction k with
    | zero =>
      intro h_eq_zero_succ_zero
      exact PeanoNat.succ_neq_zero zero h_eq_zero_succ_zero.symm
    | succ k' ih_k' =>
      intro h_eq_succ_k_succ_succ_k
      have h_k_eq_succ_k : k' = succ k' := PeanoNat.succ.inj h_eq_succ_k_succ_succ_k
      exact ih_k' h_k_eq_succ_k

  theorem succ_uni_th : ∀ n m: PeanoNat, n = m → succ n = succ m :=
    fun _ _ h_eq => congrArg PeanoNat.succ h_eq

  theorem succ_fun_th : ∀ n: PeanoNat, ∃ m: PeanoNat, m = succ n :=
    fun n => Exists.intro (PeanoNat.succ n) rfl

  theorem succ_inj_th : ∀ n m : PeanoNat, succ n = succ m → n = m :=
    fun _ _ h_eq => PeanoNat.succ.inj h_eq

  theorem succ_inj_neg_th : ∀ n m : PeanoNat, succ n ≠ succ m → n ≠ m :=
    fun n m h_neq_succ h_eq =>
      have h_succ_eq : succ n = succ m := congrArg PeanoNat.succ h_eq
      absurd h_succ_eq h_neq_succ

  def is_zero (n: PeanoNat): Prop := n = zero
  instance is_zero_inst_decidable (n : PeanoNat) : Decidable (is_zero n) :=
    inferInstanceAs (Decidable (n = zero))

  def is_succ (n: PeanoNat): Prop := ∃ k, n = succ k
  instance is_succ_inst_decidable (n : PeanoNat) : Decidable (is_succ n) :=
    match n with
    | zero => isFalse (fun h_exists => by cases h_exists with | intro k hk => cases hk)
    | succ k => isTrue (Exists.intro k rfl)

  theorem no_confu (n: PeanoNat) : (is_zero n → ¬ is_succ n) ∧ (is_succ n → ¬ is_zero n) := by
    constructor
    · intro h_is_zero_n h_is_succ_n
      rw [is_zero] at h_is_zero_n
      subst h_is_zero_n
      cases h_is_succ_n with | intro k hk_zero_eq_succ_k =>
        exact PeanoNat.succ_neq_zero k hk_zero_eq_succ_k.symm
    · intro h_is_succ_n h_is_zero_n
      rw [is_zero] at h_is_zero_n
      subst h_is_zero_n
      cases h_is_succ_n with | intro k hk_zero_eq_succ_k =>
        exact PeanoNat.succ_neq_zero k hk_zero_eq_succ_k.symm

  theorem neq_zero_then_succ (n : PeanoNat) : n ≠ zero → ∃ k, n = succ k := by
    intro h_neq_zero
    cases n with
    | zero => exact False.elim (h_neq_zero rfl)
    | succ k' => exact Exists.intro k' rfl

  theorem full_induction (P : PeanoNat → Prop)
      (h_P_zero : P PeanoNat.zero)
      (h_P_succ : ∀ n : PeanoNat, P n → P (PeanoNat.succ n))
      (n_target : PeanoNat) : P n_target :=
    PeanoNat.rec h_P_zero h_P_succ n_target

  -- === Subtipos: PosPeanoNat y FacPeanoNat (definidos DESPUÉS de los teoremas base que usan) ===
  def PosPeanoNat := { n : PeanoNat // n ≠ zero }
    deriving Repr, BEq, DecidableEq

  namespace PosPeanoNat
    def one : PosPeanoNat :=
      ⟨PeanoNat.one, PeanoNat.succ_neq_zero PeanoNat.zero⟩

    def two : PosPeanoNat :=
      ⟨PeanoNat.two, PeanoNat.succ_neq_zero PeanoNat.one⟩

    def pred (p : PosPeanoNat) : PeanoNat :=
      match h_val_eq : p.val with
      | PeanoNat.zero => False.elim (p.property h_val_eq)
      | PeanoNat.succ k => k

    def succ (p : PosPeanoNat) : PosPeanoNat :=
      ⟨PeanoNat.succ p.val, PeanoNat.succ_neq_zero p.val⟩

    def FacPeanoNat := { n : PosPeanoNat // n ≠ one }
      deriving Repr, BEq, DecidableEq

    namespace FacPeanoNat
      theorem one_neq_two_prop : PosPeanoNat.one ≠ PosPeanoNat.two := by
        intro h_eq
        have h_val_eq : PosPeanoNat.one.val = PosPeanoNat.two.val := by rw [h_eq]
        simp only [PosPeanoNat.one, PosPeanoNat.two, PeanoNat.one, PeanoNat.two] at h_val_eq
        injection h_val_eq with h_succ_inj
        exact PeanoNat.succ_neq_zero PeanoNat.zero h_succ_inj.symm

      def two : FacPeanoNat :=
        ⟨PosPeanoNat.two, Ne.symm one_neq_two_prop⟩
    end FacPeanoNat
  end PosPeanoNat

  -- === Definición de Lt y Teoremas Relacionados ===
  def Lt (n m : PeanoNat) : Prop :=
    match n, m with
    | PeanoNat.zero, PeanoNat.zero      => False
    | PeanoNat.zero, PeanoNat.succ _    => True
    | PeanoNat.succ _, PeanoNat.zero    => False
    | PeanoNat.succ n', PeanoNat.succ m' => Lt n' m'

  infix:50 "<" => Lt

  def lt_decidable : ∀ (n m : PeanoNat), Decidable (n < m)
    | zero, zero        => isFalse (fun h => by { unfold Lt at h; cases h })
    | zero, succ _      => isTrue  (by { unfold Lt; exact True.intro })
    | succ _, zero      => isFalse (fun h => by { unfold Lt at h; cases h })
    | succ n', succ m'  => lt_decidable n' m'
  instance : ∀ (n m : PeanoNat), Decidable (n < m) := lt_decidable

  @[simp] theorem not_lt_zero_self : ¬ (zero < zero) := by intro h; unfold Lt at h; cases h
  @[simp] theorem not_succ_lt_zero (n: PeanoNat): ¬(succ n < zero) := by intro h; unfold Lt at h; cases h
  @[simp] theorem lt_zero_succ (m: PeanoNat): zero < succ m := by unfold Lt; exact True.intro

  theorem zero_is_the_minor (n: PeanoNat): n < zero → False := by
    intro h_n_lt_zero
    cases n with
    | zero => unfold Lt at h_n_lt_zero; exact h_n_lt_zero
    | succ _ => unfold Lt at h_n_lt_zero; exact h_n_lt_zero

  theorem lt_n_succ_n (n: PeanoNat): n < succ n := by
    induction n with
    | zero => exact lt_zero_succ zero
    | succ n' ih => unfold Lt; exact ih

  theorem lt_not_refl (n : PeanoNat) : ¬(n < n) := by
    induction n with
    | zero => intro h; unfold Lt at h; cases h
    | succ n_prime ih_n_prime =>
      intro h_succ_lt_succ
      unfold Lt at h_succ_lt_succ
      exact ih_n_prime h_succ_lt_succ

  theorem lt_n_m_then_neq_n_m (n m: PeanoNat): n < m → n ≠ m := by
    intro h_lt; intro h_eq; rw [h_eq] at h_lt; exact lt_not_refl m h_lt

  theorem trichotomy (n m : PeanoNat) : n < m ∨ n = m ∨ m < n := by
    induction n generalizing m with
    | zero =>
      cases m with
      | zero =>           apply Or.inr; apply Or.inl; rfl
      | succ m_prime => apply Or.inl; unfold Lt; exact True.intro
    | succ n_k ih_nk =>
      cases m with
      | zero =>           apply Or.inr; apply Or.inr; unfold Lt; exact True.intro
      | succ m_k =>
        let h_ih_disjunction := ih_nk m_k
        cases h_ih_disjunction with
        | inl h_nk_lt_mk => apply Or.inl; unfold Lt; exact h_nk_lt_mk
        | inr h_eq_or_mk_lt_nk =>
          cases h_eq_or_mk_lt_nk with
          | inl h_nk_eq_mk => apply Or.inr; apply Or.inl; exact congrArg PeanoNat.succ h_nk_eq_mk
          | inr h_mk_lt_nk => apply Or.inr; apply Or.inr; unfold Lt; exact h_mk_lt_nk

  def BTrichotomy (n m : PeanoNat) : Bool :=
    match n, m with
    | zero, zero => true
    | zero, _ => true
    | _, zero => false
    | succ n', succ m' => BTrichotomy n' m'

  def PropTrichotomy (n m : PeanoNat) : Prop :=
    match n, m with
    | zero, zero => (n = m)
    | zero, _ => (n < m)
    | _, zero => ¬(n < m)
    | succ n', succ m' => PropTrichotomy n' m'

  def BLe (n m : PeanoNat) : Bool :=
    match n, m with
    | zero, _          => true
    | succ _, zero     => false
    | succ n', succ m' => BLe n' m'

  def EqDef (f g : PeanoNat → PeanoNat) : Prop := ∀ x, f x = g x

  theorem eq_of_eq_on_induct (f g : PeanoNat → PeanoNat) :
      ((f zero)=(g zero)) ∧ (∀ n, (f n = g n) → (f (succ n) = g (succ n))) →
      ( EqDef f g ) := by
    intro h_hypotheses
    intro x
    induction x with
    | zero => exact h_hypotheses.left
    | succ n ih => exact h_hypotheses.right n ih

  theorem lt_succ (n m : PeanoNat) : Lt n m → Lt n (PeanoNat.succ m) := by
    revert m
    induction n with
    | zero =>
      intro m_val; intro h_zero_lt_m_val
      unfold Lt; exact True.intro
    | succ n_k ih_nk =>
      intro m_val; intro h_succ_nk_lt_m_val
      cases m_val with
      | zero =>
        unfold Lt at h_succ_nk_lt_m_val; exact False.elim h_succ_nk_lt_m_val
      | succ m_k_inner =>
        have h_nk_lt_mk_inner : Lt n_k m_k_inner := by
          unfold Lt at h_succ_nk_lt_m_val; exact h_succ_nk_lt_m_val
        unfold Lt;
        exact (ih_nk m_k_inner) h_nk_lt_mk_inner

  theorem lt_not_symm (n m: PeanoNat) : (n < m) → ¬(m < n) := by
    revert m
    induction n with
    | zero =>
      intro m_val; intro h_zero_lt_m_val; intro h_m_val_lt_zero
      exact zero_is_the_minor m_val h_m_val_lt_zero
    | succ n_k ih_nk =>
      intro m_val; intro h_succ_nk_lt_m_val; intro h_m_val_lt_succ_nk
      cases m_val with
      | zero =>
        unfold Lt at h_succ_nk_lt_m_val; exact False.elim h_succ_nk_lt_m_val
      | succ m_k_inner =>
        have h_nk_lt_mk_inner : Lt n_k m_k_inner := by unfold Lt at h_succ_nk_lt_m_val; assumption
        have h_mk_inner_lt_nk : Lt m_k_inner n_k := by unfold Lt at h_m_val_lt_succ_nk; assumption
        exact (ih_nk m_k_inner h_nk_lt_mk_inner) h_mk_inner_lt_nk

  theorem lt_trans {n m k : PeanoNat} (h1 : Lt n m) (h2 : Lt m k) : Lt n k := by
    cases k with
    | zero => exact False.elim (zero_is_the_minor m h2)
    | succ k_prime =>
      cases m with
      | zero => exact False.elim (zero_is_the_minor n h1)
      | succ m_prime =>
        cases n with
        | zero => exact lt_zero_succ k_prime
        | succ n_prime =>
          unfold Lt at h1; unfold Lt at h2; unfold Lt
          exact lt_trans h1 h2

  theorem lt_n_m_then_exists_k_eq_succ_k_m (n m: PeanoNat) :
    n < m → (succ n = m) ∨ (∃ k_ex: PeanoNat, n < k_ex ∧ succ k_ex = m) :=
  by
    revert n
    induction m with
    | zero =>
      intro n_gen h_n_lt_zero
      exact False.elim (zero_is_the_minor n_gen h_n_lt_zero)
    | succ m_prime ih_m_prime =>
      intro n_gen h_n_lt_succ_m_prime
      cases n_gen with
      | zero =>
        by_cases h_m_prime_is_zero : (m_prime = zero)
        · rw [h_m_prime_is_zero]; apply Or.inl; rfl
        · apply Or.inr
          apply Exists.intro m_prime
          apply And.intro
          · have h_exists_pred_m_prime : ∃ m_p_p, m_prime = succ m_p_p :=
              (neq_zero_then_succ m_prime) h_m_prime_is_zero
            cases h_exists_pred_m_prime with | intro m_p_p h_m_prime_eq_succ_m_p_p =>
              rw [h_m_prime_eq_succ_m_p_p]
              exact lt_zero_succ m_p_p
          · rfl
      | succ n_k =>
        have h_nk_lt_mprime : n_k < m_prime := by unfold Lt at h_n_lt_succ_m_prime; assumption
        let ih_result := ih_m_prime n_k h_nk_lt_mprime
        cases ih_result with
        | inl h_succ_nk_eq_mprime =>
          apply Or.inl
          rw [h_succ_nk_eq_mprime]
        | inr h_exists_kih =>
          cases h_exists_kih with | intro k0 h_and_k0 =>
            apply Or.inr
            apply Exists.intro m_prime
            apply And.intro
            · -- Objetivo: succ n_k < m_prime
              -- Sabemos: h_and_k0.right : succ k0 = m_prime
              --          h_and_k0.left  : n_k < k0
              rw [h_and_k0.right.symm] -- Objetivo: succ n_k < succ k0
              unfold Lt                -- Objetivo: n_k < k0
              exact h_and_k0.left
            · rfl

  -- === Definición de Le (menor o igual) y sus Teoremas ===
  inductive Le : PeanoNat -> PeanoNat -> Prop where
    | strict_lt {n m : PeanoNat} (h : Lt n m) : Le n m
    | refl_le {n : PeanoNat} : Le n n

  infix:50 "<=" => Le
  infix:50 "≤"  => Le

  theorem le_zero_zero : Le zero zero := by
    apply Le.refl_le

  theorem le_if_eq (n m : PeanoNat) : n = m → Le n m := by
    intro h_eq
    rw [h_eq]
    apply Le.refl_le

  theorem le_if_lt (n m : PeanoNat) : n < m → Le n m := by
    intro h_lt
    apply Le.strict_lt
    exact h_lt

  theorem le_succ (n m : PeanoNat) : Le n m → Le n (succ m) := by
    intro h_n_le_m
    cases h_n_le_m with
    | strict_lt h_n_lt_m_inner =>
      apply Le.strict_lt
      exact lt_succ n m h_n_lt_m_inner
    | refl_le =>
      apply Le.strict_lt
      exact lt_n_succ_n n

  theorem ble_then_le (n m : PeanoNat) :
    (BLe n m = true) →  (n <= m) := by
    induction n generalizing m with
    | zero =>
      intro h_ble_true -- BLe zero m = true
      cases m with
      | zero => -- BLe zero zero = true
        exact Le.refl_le -- Goal: zero <= zero
      | succ m' => -- BLe zero (succ m') = true
        -- Goal: zero <= succ m'
        apply Le.strict_lt
        exact lt_zero_succ m'
    | succ n' ih_n' => -- ih_n' : ∀ m_ih, (BLe n' m_ih = true) → (n' <= m_ih)
      intro h_ble_true -- BLe (succ n') m = true
      cases m with
      | zero => -- BLe (succ n') zero = true. But BLe (succ n') zero is false.
        -- So h_ble_true is (false = true), which is a contradiction.
        exact False.elim (Bool.noConfusion h_ble_true)
      | succ m' => -- BLe (succ n') (succ m') = true. This means BLe n' m' = true.
        -- Goal: succ n' <= succ m'
        -- From h_ble_true (i.e. BLe n' m' = true), by ih_n', we get (n' <= m').
        have h_n_prime_le_m_prime : n' <= m' := ih_n' m' h_ble_true
        -- Now we need to prove (succ n' <= succ m') from (n' <= m').
        cases h_n_prime_le_m_prime with
        | strict_lt h_lt_inner => -- n' < m'
          apply Le.strict_lt
          unfold Lt -- Lt (succ n') (succ m') is Lt n' m'
          exact h_lt_inner
        | refl_le => -- n' = m'
          apply Le.refl_le -- succ n' <= succ n'

  theorem le_of_succ_le_succ {n m : PeanoNat} (h_succ_n_le_succ_m : Le (succ n) (succ m)) : Le n m := by
    cases h_succ_n_le_succ_m with
    | strict_lt h_succ_n_lt_succ_m_inner =>
      apply Le.strict_lt; unfold Lt at h_succ_n_lt_succ_m_inner; assumption
    | refl_le => apply Le.refl_le

  theorem le_then_ble (n m : PeanoNat) :
    (n <= m)  → (BLe n m = true) := by
    induction n generalizing m with
    | zero =>
      induction m with
      | zero =>
        -- Goal: (zero <= zero) → (BLe zero zero = true)
        -- BLe zero zero is true. Goal: (zero <= zero) → (true = true)
        intro h_le_zz -- h_le_zz : zero <= zero
        simp [BLe] -- Optional: simplifies BLe zero zero to true-- Proves true = true
      | succ m' =>
        -- Goal: (zero <= succ m') → (BLe zero (succ m') = true)
        -- BLe zero (succ m') is true. Goal: (zero <= succ m') → (true = true)
        intro h_le_zsm -- h_le_zsm : zero <= succ m'
        simp [BLe] -- Optional: simplifies BLe zero (succ m') to true
    | succ n' ih_n' => -- ih_n' : ∀ (m_ih : PeanoNat), (n' <= m_ih) → (BLe n' m_ih = true)
      induction m with
      | zero =>
        -- Goal: (succ n' <= zero) → (BLe (succ n') zero = true)
        -- BLe (succ n') zero is false. Goal: (succ n' <= zero) → (false = true)
        -- This means we need to prove (succ n' <= zero) → False
        intro h_le_snz -- h_le_snz : succ n' <= zero
        simp [BLe] -- Optional: simplifies BLe (succ n') zero to false. Goal becomes (false = true)
        -- Now prove False from h_le_snz
        cases h_le_snz with
        | strict_lt h_lt => exact False.elim (not_succ_lt_zero n' h_lt)
        -- The refl_le branch was removed as succ n' = zero is impossible.
      | succ m' =>
        -- Goal: (succ n' <= succ m') → (BLe (succ n') (succ m') = true)
        -- BLe (succ n') (succ m') is BLe n' m'.
        -- Goal: (succ n' <= succ m') → (BLe n' m' = true)
        intro h_le_snsm -- h_le_snsm : succ n' <= succ m'
        simp [BLe] -- Optional: simplifies BLe (succ n') (succ m') to BLe n' m'. Goal becomes BLe n' m' = true
        -- We need to prove BLe n' m' = true.
        -- We have ih_n' m' : (n' <= m') → (BLe n' m' = true).
        -- We need a proof of n' <= m'.
        -- We can get this from h_le_snsm (succ n' <= succ m') using le_of_succ_le_succ.
        have h_n_prime_le_m_prime : n' <= m' := le_of_succ_le_succ h_le_snsm
        exact ih_n' m' h_n_prime_le_m_prime

  theorem ble_iff_le (n m : PeanoNat) : (BLe n m = true) ↔ (n <= m)
    := by
      constructor
      · exact ble_then_le n m
      · exact le_then_ble n m

  def le_decidable : ∀ (n m : PeanoNat), Decidable (n <= m) :=
    fun n m =>
    if h_ble_eq_true : BLe n m = true then
      isTrue ((ble_iff_le n m).mp h_ble_eq_true)
    else -- h_ble_eq_true es una prueba de ¬(BLe n m = true), que es BLe n m = false
      isFalse (
        fun h_n_le_m_proof => -- Asumimos (n <= m) para derivar una contradicción
        -- De (n <= m), usando (ble_iff_le n m).mpr, obtenemos (BLe n m = true)
        have h_ble_should_be_true : BLe n m = true := (ble_iff_le n m).mpr h_n_le_m_proof
        -- h_ble_eq_true es ¬(BLe n m = true)
        -- h_ble_should_be_true es (BLe n m = true)
        -- Aplicar el primero al segundo da False
        h_ble_eq_true h_ble_should_be_true
      )

  instance : ∀ (n m : PeanoNat), Decidable (n <= m) := le_decidable

  theorem le_refl (n : PeanoNat) : Le n n := Le.refl_le

  theorem le_succ_self (n : PeanoNat) : Le n (succ n) :=
    Le.strict_lt (lt_n_succ_n n)

  theorem le_succ_succ (n m : PeanoNat) : Le n m → Le (succ n) (succ m) := by
    intro h_n_le_m
    cases h_n_le_m with
    | strict_lt h_n_lt_m_inner =>
      apply Le.strict_lt; unfold Lt; exact h_n_lt_m_inner
    | refl_le => apply Le.refl_le

  theorem le_then_eq_xor_lt (n m : PeanoNat) : Le n m → n = m ∨ n < m := by
    intro h_n_le_m
    cases h_n_le_m with
    | strict_lt h_n_lt_m_inner =>
      apply Or.inr;
      exact h_n_lt_m_inner
    | refl_le =>
      apply Or.inl;
      rfl

  theorem le_trans {n m k : PeanoNat} (h1 : Le n m) (h2 : Le m k) : Le n k := by
    match h1, h2 with
    | Le.refl_le, h_m_le_k => exact h_m_le_k
    | h_n_le_m, Le.refl_le => exact h_n_le_m
    | Le.strict_lt h_n_lt_m, Le.strict_lt h_m_lt_k =>
      exact Le.strict_lt (lt_trans h_n_lt_m h_m_lt_k)
    -- Los casos mixtos están cubiertos por los patrones anteriores si se analizan en orden.

  theorem le_zero (n : PeanoNat) : Le zero n := by
    cases n with
    | zero => exact Le.refl_le
    | succ n_prime => exact Le.strict_lt (lt_zero_succ n_prime)

  theorem le_n_zero_eq_zero (n : PeanoNat) (h_n_le_zero : Le n zero) : n = zero := by
    cases n with
    | zero => rfl
    | succ n' => -- n' is the predecessor of n
      -- We are in the case where n = succ n'. The goal is succ n' = zero.
      -- This is impossible, so we derive a contradiction (False).
      exfalso
      -- The hypothesis h_n_le_zero is Le (succ n') zero.
      -- This can be Le.strict_lt (succ n' < zero) or Le.refl_le (implying succ n' = zero).
      cases h_n_le_zero with
      | strict_lt h_lt => -- Case 1: succ n' < zero
        -- This contradicts 'not_succ_lt_zero n''.
        exact not_succ_lt_zero n' h_lt
      -- The refl_le case is impossible because (succ n' = zero) contradicts (succ_neq_zero n').
      -- Lean's `cases` tactic infers this, so the branch is not needed.

  theorem le_antisymm {n m : PeanoNat} (h1 : Le n m) (h2 : Le m n) : n = m := by
    match h1, h2 with
    | Le.refl_le, _ => rfl
    | _, Le.refl_le => rfl
    | Le.strict_lt h_n_lt_m, Le.strict_lt h_m_lt_n =>
        exact False.elim ((lt_not_symm n m h_n_lt_m) h_m_lt_n)
    -- Los casos mixtos están cubiertos por los dos primeros patrones.

  theorem le_lt_succ (n m : PeanoNat) : Le n m → Lt n (succ m) := by
    intro h_n_le_m
    cases h_n_le_m with
    | strict_lt h_n_lt_m_inner => exact lt_succ n m h_n_lt_m_inner
    | refl_le => exact lt_n_succ_n n

  theorem lt_le_succ (n m : PeanoNat) : Lt n m → Le n m := Le.strict_lt

  theorem not_exists_maximum : ¬(∃ k : PeanoNat, ∀ m : PeanoNat, m < k) := by
    intro h_exists_k
    cases h_exists_k with | intro k hk_is_max =>
      have h_succ_k_lt_k : succ k < k := hk_is_max (succ k)
      have h_k_lt_succ_k : k < succ k := lt_n_succ_n k
      exact (lt_not_symm k (succ k) h_k_lt_succ_k) h_succ_k_lt_k

  def add (n m : PeanoNat) : PeanoNat :=
    match m with
    | zero => n
    | succ m' => succ (add n m')

  infix:50 "+" => add

-- #eval add zero zero
-- #eval add zero one
-- #eval add one zero
-- #eval add one one
-- #eval add one two
-- #eval add two one
-- #eval add two two
-- #eval add one three
-- #eval add three one
-- #eval add two three
-- #eval add three two
-- #eval add three three

  theorem add_zero (n : PeanoNat) : add n zero = n
    := by
      induction n with
      | zero =>
        simp [add]
      | succ n' ih =>
        simp [add]

  theorem zero_add (n : PeanoNat) : add zero n = n
    := by
      induction n with
      | zero =>
        simp [add]
      | succ n' ih =>
        simp [add]
        exact ih

  theorem add_one (n : PeanoNat) : add n one = succ n
    := by
      induction n with
      | zero =>
        rfl
      | succ n' ih =>
        unfold add
        rw [<-ih]
        rfl

  theorem one_add (n : PeanoNat) : add one n = succ n
    := by
      induction n with
      | zero =>
        rfl
      | succ n' ih =>
        unfold add
        rw [<-ih]

  theorem add_succ (n m : PeanoNat) : add n (succ m) = succ (add n m)
    := by
      induction n with
      | zero =>
        simp [add]
      | succ n' ih =>
        simp [add]

  theorem succ_add (n m : PeanoNat) : add (succ n) m = succ (add n m)
    := by
      induction m with
      | zero =>
        rw [add, add]
      | succ n' ih =>
        simp [add]
        rw [ih]

  theorem add_comm (n m : PeanoNat) : add n m = add m n
    := by
      induction n with
      | zero =>
        rw [zero_add]
        rw [add_zero]
      | succ n' ih =>
        rw [succ_add]
        rw [ih]
        exact add_succ m n'

  theorem add_assoc (n m k : PeanoNat) : add n (add m k) = add (add n m) k
    := by
      induction n with
      | zero =>
        rw [zero_add]
        rw [zero_add]
      | succ n' ih =>
        rw [succ_add]
        rw [ih]
        rw [succ_add]
        rw [succ_add]

  theorem add_le (a b c : PeanoNat) : Le a b → Le a (add b c) := by
    intro h_le
    induction c with
    | zero =>
      rw [add_zero]; exact h_le
    | succ c' ih =>
      rw [add_succ]
      exact le_succ a (add b c') ih

  theorem add_lt (n m k : PeanoNat) : Lt n m → Lt n (add m k)
    := by
      intro h_lt
      induction k with
      | zero =>
        rw [add_zero]
        exact h_lt
      | succ k' ih =>
        rw [add_succ]
        exact lt_succ n (add m k') ih

  theorem add_cancelation (n m k : PeanoNat) :
    add n m = add n k → m = k
      := by
        intro h_eq
        induction n with
        | zero =>
          rw [zero_add, zero_add] at h_eq
          exact h_eq
        | succ n' ih =>
          rw [succ_add] at h_eq
          rw [succ_add] at h_eq
          injection h_eq with h_m_eq_k
          exact ih h_m_eq_k

  theorem cancelation_add (n m k : PeanoNat) :
    add m n = add k n → m = k
      := by
        intro h_eq
        induction n with
        | zero =>
          rw [add_zero, add_zero] at h_eq
          exact h_eq
        | succ n' ih =>
          rw [add_succ] at h_eq
          rw [add_succ] at h_eq
          injection h_eq with h_m_eq_k
          exact ih h_m_eq_k

  theorem add_lt_cancelation (n m k : PeanoNat) :
    add n m < add n k → m < k
      := by
        intro h_lt
        induction n with
        | zero =>
          rw [zero_add, zero_add] at h_lt
          exact h_lt
        | succ n' ih =>
          rw [succ_add] at h_lt
          rw [succ_add] at h_lt
          exact ih h_lt

  theorem add_le_cancelation (n m k : PeanoNat) :
    Le (add n m) (add n k) → Le m k
      := by
        intro h_le
        induction n with
        | zero =>
          rw [zero_add, zero_add] at h_le
          exact h_le
        | succ n' ih =>
          rw [succ_add] at h_le
          rw [succ_add] at h_le
          exact ih (le_of_succ_le_succ h_le)

theorem add_eq_zero_iff (a b : PeanoNat) :
  add a b = zero ↔ a = zero ∧ b = zero
    := by
      constructor
      · intro h_eq
        induction a with
        | zero =>
          rw [zero_add] at h_eq
          exact ⟨rfl, h_eq⟩
        | succ a' ih =>
          rw [succ_add] at h_eq
          exact PeanoNat.noConfusion h_eq
      · intro ⟨h_a_eq_zero, h_b_eq_zero⟩
        rw [h_a_eq_zero, h_b_eq_zero]
        rfl

  theorem le_iff_exists_add (a b : PeanoNat) :
    Le a b ↔ ∃ p, b = add a p
    := by
    constructor
    · -- Forward direction: Le a b → ∃ p, b = add a p
      intro h_le_a_b
      revert a -- Generalize a before inducting on b for this implication direction
      induction b with
      | zero =>
        intro a_val h_a_le_zero -- a_val <= 0
        have h_a_eq_zero : a_val = zero := le_n_zero_eq_zero a_val h_a_le_zero
        rw [h_a_eq_zero] -- Goal: ∃ p, zero = add zero p
        exact Exists.intro zero rfl -- p = 0, zero = add zero zero
      | succ k ih_k => -- ih_k : ∀ (a_val' : PeanoNat), a_val' <= k → (∃ p_val, k = add a_val' p_val)
        intro a_val h_a_le_succ_k -- a_val <= succ k

        -- Local lemma: Lt x (succ y) → Le x y
        have lemma_lt_succ_imp_le (curr_a curr_k_lemma : PeanoNat) : Lt curr_a (succ curr_k_lemma) → Le curr_a curr_k_lemma := by
          intro h_curr_a_lt_succ_curr_k_lemma
          induction curr_k_lemma generalizing curr_a with -- h_curr_a_lt_succ_curr_k_lemma is implicitly generalized
          | zero => -- curr_k_lemma = 0.
                    -- Context: curr_a : PeanoNat, h_curr_a_lt_succ_curr_k_lemma : Lt curr_a (succ zero)
                    -- Goal: Le curr_a zero
            cases curr_a with
            | zero => exact Le.refl_le
            | succ ca' => -- curr_a = succ ca'. h_curr_a_lt_succ_curr_k_lemma is Lt (succ ca') (succ zero)
              unfold Lt at h_curr_a_lt_succ_curr_k_lemma -- h_curr_a_lt_succ_curr_k_lemma becomes Lt ca' zero
              exact False.elim (zero_is_the_minor ca' h_curr_a_lt_succ_curr_k_lemma)
          | succ k_prime ih_k_prime => -- The hypothesis h_curr_a_lt_succ_curr_k_lemma : curr_a < succ (succ k_prime) is already in context.
            -- intro h_curr_a_lt_succ_succ_k_prime -- This line was causing the error and is removed.
            cases curr_a with
            | zero => exact le_zero (succ k_prime)
            | succ ca' => -- curr_a = succ ca'. h_curr_a_lt_succ_curr_k_lemma is Lt (succ ca') (succ (succ k_prime))
              unfold Lt at h_curr_a_lt_succ_curr_k_lemma -- Now h_curr_a_lt_succ_curr_k_lemma is Lt ca' (succ k_prime)
              apply le_succ_succ -- Goal: Le (succ ca') (succ k_prime). Needs Le ca' k_prime.
              exact ih_k_prime ca' h_curr_a_lt_succ_curr_k_lemma -- ih_k_prime needs (Lt ca' (succ k_prime))

        cases (le_then_eq_xor_lt a_val (succ k)) h_a_le_succ_k with
        | inl h_a_eq_succ_k => -- Case 1: a_val = succ k
          rw [h_a_eq_succ_k] -- Goal: ∃ p, succ k = add (succ k) p
          exact Exists.intro zero (add_zero (succ k)) -- p = 0
        | inr h_a_lt_succ_k => -- Case 2: a_val < succ k
          have h_a_le_k : Le a_val k := lemma_lt_succ_imp_le a_val k h_a_lt_succ_k
          specialize ih_k a_val h_a_le_k
          cases ih_k with | intro p_prime h_k_eq_add_a_p_prime =>
            rw [h_k_eq_add_a_p_prime] -- Goal: ∃ p, succ (add a_val p_prime) = add a_val p
            exact Exists.intro (succ p_prime) rfl
    · -- Backward direction: (∃ p, b = add a p) → Le a b
      intro h_exists
      cases h_exists with | intro p_val h_b_eq_add_a_p_val =>
        rw [h_b_eq_add_a_p_val] -- Goal: Le a (add a p_val)
        clear h_b_eq_add_a_p_val -- Prevent h_b_eq_add_a_p_val from being generalized by induction
        induction p_val with
        | zero =>
          rw [add_zero]
          exact Le.refl_le
        | succ p_prime ih_p_prime => -- ih_p_prime: Le a (add a p_prime)
          rw [add_succ] -- Goal: Le a (succ (add a p_prime))
          exact le_succ a (add a p_prime) ih_p_prime

  theorem lt_iff_exists_add_succ (a b : PeanoNat) :
    Lt a b ↔ ∃ p, b = add a (succ p)
      := by
        constructor
        · -- Dirección →: Lt a b → ∃ p, b = add a (succ p)
          intro h_lt_a_b
          -- Sabemos que si a < b, entonces a ≤ b
          have h_le_a_b : Le a b := Le.strict_lt h_lt_a_b
          -- Por le_iff_exists_add, tenemos ∃ q, b = add a q
          have h_exists_q := (le_iff_exists_add a b).mp h_le_a_b
          cases h_exists_q with | intro q h_b_eq_add_a_q =>
            -- Debemos mostrar que q = succ p para algún p
            -- Si a < b, entonces a ≠ b por lt_n_m_then_neq_n_m
            have h_a_neq_b : a ≠ b := lt_n_m_then_neq_n_m a b h_lt_a_b
            -- Si q = 0, entonces b = add a zero = a, contradiciendo       h_a_neq_b
            -- Por lo tanto, q = succ p para algún p
            cases q with
            | zero => -- Caso q = zero (imposible)
              rw [h_b_eq_add_a_q, add_zero] at h_a_neq_b
              exact False.elim (h_a_neq_b rfl)
            | succ p => -- Caso q = succ p
              -- Tenemos b = add a (succ p), exactamente lo que       necesitamos
              exists p

        · -- Dirección ←: (∃ p, b = add a (succ p)) → Lt a b
          intro h_exists
          cases h_exists with | intro p h_b_eq_add_a_succ_p =>
            subst h_b_eq_add_a_succ_p
            -- Necesitamos mostrar Lt a (add a (succ p))
            -- Primero probamos Lt a (add a one)
            have h_lt_a_add_a_one : Lt a (add a one) := by
              rw [add_one]
              exact lt_n_succ_n a
            -- Ahora probamos que add a (succ p) = add a one + add a p
            -- y usamos lt_trans y add_lt
            induction p with
            | zero =>
              -- Para p = zero, succ p = one
              rw [add_succ]
              rw [add_zero]
              exact lt_n_succ_n a
            | succ p' ih =>
              -- Para p = succ p', necesitamos Lt a (add a (succ (succ       p')))
              rw [add_succ]
              -- Usando la hipótesis inductiva ih: Lt a (add a (succ p'))
              exact lt_succ a (add a (succ p')) ih


  def mul (n m : PeanoNat) : PeanoNat :=
    match m with
    | zero => zero
    | succ m' => add (mul n m') n

  infix:70 "*" => mul

  theorem mul_zero (n : PeanoNat) : mul n zero = zero
    := by
      simp [mul]

  theorem zero_mul (n : PeanoNat) : mul zero n = zero
    := by
      induction n with
      | zero =>
        simp [mul]
      | succ n' ih =>
        simp [mul, ih, add_zero]

  theorem succ_mul (n m : PeanoNat) : mul (succ n) m = add (mul n m) m
    := by
      induction m with
      | zero =>
        rw [mul_zero, mul_zero, add_zero]
      | succ m' ih =>
        simp [mul]
        rw [ih]
        -- Goal: ((n*m') + m') + n.succ = ((n*m') + n) + m'.succ
        -- Transform LHS: ((X+Y)+Z) to X+(Y+Z)
        rw [←add_assoc (mul n m') m' n.succ]
        -- Transform RHS: ((A+B)+C) to A+(B+C)
        rw [←add_assoc (mul n m') n m'.succ]
        -- Goal: (n*m') + (m' + n.succ) = (n*m') + (n + m'.succ)
        -- Apply congruence for the outer 'add (mul n m')'
        apply congrArg (add (mul n m'))
        -- Goal: m' + n.succ = n + m'.succ
        -- Apply add_succ to both sides: m' + succ n = succ (m' + n) and n + succ m' = succ (n + m')
        rw [add_succ m' n, add_succ n m']
        -- Goal: succ (m' + n) = succ (n + m')
        -- Apply congruence for 'succ'
        apply congrArg succ
        -- Goal: m' + n = n + m'
        exact add_comm m' n

  theorem mul_succ (n m : PeanoNat) : mul n (succ m) = add (mul n m) n := by
    rfl

  theorem mul_one (n : PeanoNat) :
    mul n one = n
      := by
        induction n with
        | zero =>
          rfl
        | succ n' ih =>
          rw [succ_mul, ih, add_one]

  theorem one_mul (m : PeanoNat) :
    mul one m = m
      := by
        induction m with
        | zero =>
          rfl
        | succ m' ih =>
          rw [mul_succ, ih, add_one]

  theorem mul_two (n : PeanoNat):
    mul n two = add n n
      := by
        induction n with
        | zero =>
          rfl
        | succ n' ih =>
          rw [succ_mul, ih, PeanoNat.two]
          rw [add_succ, add_one]
          rw [succ_add, add_succ]

  theorem mul_comm (n m : PeanoNat) : mul n m = mul m n
    := by
      induction m with
      | zero =>
        rw [mul_zero, zero_mul]
      | succ m' ih =>
        simp [mul]
        rw [ih]
        -- After simp [mul] and rw [ih], the goal is:
        -- add (mul m' n) n = mul (succ m') n
        -- We use succ_mul to rewrite the RHS.
        rw [succ_mul m' n]
        -- The goal becomes: add (mul m' n) n = add (mul m' n) n
        -- This is true by reflexivity.
  theorem two_mul (m : PeanoNat) :
    mul two m = add m m
      := by
        rw [mul_comm, mul_two]

  theorem mul_ldistr (m n k : PeanoNat) :
    mul m (add n k) = add (mul m n) (mul m k)
    := by
      induction k with
      | zero =>
        rw [add_zero, mul_zero, add_zero]
      | succ k' ih =>
        rw [add_succ] -- LHS: mul m (succ (add n k'))
        rw [mul_succ] -- LHS: add (mul m (add n k')) m
        rw [ih]       -- LHS: add (add (mul m n) (mul m k')) m
        rw [mul_succ] -- RHS: add (mul m n) (add (mul m k') m)
        rw [add_assoc (mul m n) (mul m k') m] -- LHS: add (mul m n) (add (mul m k') m)
        -- Goal: add (mul m n) (add (mul m k') m) = add (mul m n) (add (mul m k')   m)
        -- Proof finished by reflexivity

  theorem mul_rdistr (m n k : PeanoNat) :
    mul (add m n) k = add (mul m k) (mul n k)
      := by
        induction k with
        | zero =>
          -- Goal: mul (add m n) zero = add (mul m zero) (mul n zero)
          rw [mul_zero, mul_zero, mul_zero, add_zero]
          -- Goal: zero = zero. Proof finished by reflexivity.
        | succ k' ih => -- ih: mul (add m n) k' = add (mul m k') (mul n k')
          -- Goal: mul (add m n) (succ k') = add (mul m (succ k')) (mul n (succ   k'))
          -- LHS = add (add (mul m k') (mul n k')) (add m n)  [Using ih] Let   a:=mul m k', b:=mul n k', c:=m, d:=n. LHS = (a+b)+(c+d)
          -- RHS = add (add (mul m k') m) (add (mul n k') n)  [Using mul_succ].   RHS = (a+c)+(b+d)
          -- Proof: (a+b)+(c+d) = a+(b+(c+d)) = a+((b+c)+d) = a+((c+b)+d) = a+(c  +(b+d)) = (a+c)+(b+d)
          calc
            mul (add m n) (succ k')
              = add (mul (add m n) k') (add m n) := by rw [mul_succ]
            _ = add (add (mul m k') (mul n k')) (add m n) := by rw [ih] -- (a+b)  +(c+d)
            _ = add (mul m k') (add (mul n k') (add m n)) := by rw [←add_assoc]   -- a+(b+(c+d))
            _ = add (mul m k') (add (add (mul n k') m) n) := by rw [add_assoc   (mul n k') m n] -- a+((b+c)+d)
            _ = add (mul m k') (add (add m (mul n k')) n) := by rw [add_comm (mul   n k') m] -- a+((c+b)+d)
            _ = add (mul m k') (add m (add (mul n k') n)) := by rw [add_assoc m   (mul n k') n] -- a+(c+(b+d))
            _ = add (add (mul m k') m) (add (mul n k') n) := by rw [←add_assoc]   -- (a+c)+(b+d)
            _ = add (mul m (succ k')) (mul n (succ k')) := by rw [←mul_succ,   ←mul_succ]

 theorem neq_then_lt (n m : PeanoNat) :
    n ≠ m → (n < m) ∨ (m < n)
      := by
        intro h_neq
        -- Goal: n ≠ m → (n < m) ∨ (m < n)
        -- We can use trichotomy to prove this.
        -- trichotomy n m = n < m ∨ n = m ∨ m < n
        -- We need to prove that n = m is false.
        -- This is equivalent to proving ¬(n = m).
        have h_n_eq_m_is_false : ¬(n = m) := by
          intro h_eq
          exact h_neq h_eq
        -- Now we can apply trichotomy.
        cases trichotomy n m with
        | inl h_n_lt_m => exact Or.inl h_n_lt_m
        | inr h_rest =>
          cases h_rest with
          | inl h_n_eq_m => exact False.elim (h_n_eq_m_is_false h_n_eq_m)
          | inr h_m_lt_n => exact Or.inr h_m_lt_n

  theorem lt_then_neq (n m : PeanoNat) :
    n < m → n ≠ m
      := by
        intro h_lt
        exact lt_n_m_then_neq_n_m n m h_lt

  theorem mul_cancelation (n m k : PeanoNat) :
    n ≠ zero → (mul n m = mul n k → m = k)
      := by
        intro h_n_neq_zero
        intro h_mul_eq_nk -- h_mul_eq_nk : mul n m = mul n k
        induction m generalizing k with
        | zero => -- m = 0. We want to prove 0 = k.
          rw [mul_zero] at h_mul_eq_nk -- h_mul_eq_nk is now `zero = mul n k`
          -- We need to show that if `n ≠ zero` and `mul n k = zero`, then `k = zero`.
          -- This sub-proof is by induction on k.
          revert h_mul_eq_nk -- Generalize over the equality for the inner induction.
          induction k with
          | zero => -- k = 0.
            intro _hyp_zero_eq_mul_n_zero -- Hypothesis `zero = mul n zero` is `zero = zero`.
            rfl -- Goal `0 = 0` is true by reflexivity.
          | succ k' => -- k = succ k'.
            intro h_zero_eq_mul_n_succ_k -- Hypothesis `zero = mul n (succ k')`.
            -- The goal is `0 = succ k'`. This is impossible.
            -- So we must show `zero = mul n (succ k')` is also impossible if `n ≠ 0`.
            rw [mul_succ] at h_zero_eq_mul_n_succ_k -- `zero = add (mul n k') n`.
            -- We use `n` from the outer scope, for which `h_n_neq_zero` holds.
            cases n with
            | zero => -- n = 0. This contradicts h_n_neq_zero.
              exact False.elim (h_n_neq_zero rfl)
            | succ n_val => -- n = succ n_val. So n ≠ 0.
              -- h_zero_eq_mul_n_succ_k is `zero = add (mul (succ n_val) k') (succ n_val)`.
              -- By commutativity of add: `zero = add (succ n_val) (mul (succ n_val) k')`.
              -- By succ_add: `zero = succ (add n_val (mul (succ n_val) k'))`.
              rw [add_comm, succ_add] at h_zero_eq_mul_n_succ_k
              -- This is of the form `zero = succ X`, which is impossible.
              -- `PeanoNat.noConfusion` derives `False` from `succ X = zero`.
              -- Our hypothesis is `zero = succ X`, so we use `.symm`.
              exact False.elim (PeanoNat.noConfusion h_zero_eq_mul_n_succ_k.symm)
        | succ m' ih_m' => -- m = succ m'. We want to prove `succ m' = k`.
          -- ih_m' is `∀ k_target, mul n m' = mul n k_target → m' = k_target`.
          -- h_mul_eq_nk is `mul n (succ m') = mul n k`.
          cases k with
          | zero => -- k = 0. The goal is `succ m' = 0`. This is impossible.
            -- So we must show `mul n (succ m') = mul n zero` (i.e. `mul n (succ m') = 0`)
            -- is also impossible if `n ≠ 0`.
            rw [mul_zero] at h_mul_eq_nk -- h_mul_eq_nk is now `mul n (succ m') = 0`.
            -- We use `n` from the outer scope.
            cases n with
            | zero => -- n = 0. This contradicts h_n_neq_zero.
              exact False.elim (h_n_neq_zero rfl)
            | succ n_val => -- n = succ n_val. So n ≠ 0.
              -- h_mul_eq_nk is `mul (succ n_val) (succ m') = 0`.
              rw [mul_succ] at h_mul_eq_nk -- `add (mul (succ n_val) m') (succ n_val) = 0`.
              -- By `add_eq_zero_iff`, both terms of the sum must be zero.
              have h_add_parts_eq_zero := (add_eq_zero_iff _ _).mp h_mul_eq_nk
              -- `h_add_parts_eq_zero.right` is `succ n_val = 0`. This is impossible.
              -- `PeanoNat.noConfusion` derives `False` from `succ X = zero`.
              exact False.elim (PeanoNat.noConfusion h_add_parts_eq_zero.right)
          | succ k' => -- k = succ k'. The goal is `succ m' = succ k'`.
            -- h_mul_eq_nk is `mul n (succ m') = mul n (succ k')`.
            rw [mul_succ, mul_succ] at h_mul_eq_nk
            -- Now h_mul_eq_nk is `add (mul n m') n = add (mul n k') n`.
            -- By `cancelation_add a b x : add a x = add b x → a = b`.
            -- Let a := mul n m', b := mul n k', x := n.
            have h_mul_nm_eq_mul_nk : mul n m' = mul n k' :=
              cancelation_add n (mul n m') (mul n k') h_mul_eq_nk
            -- Apply the induction hypothesis ih_m'.
            have h_m'_eq_k' : m' = k' := ih_m' k' h_mul_nm_eq_mul_nk
            -- Since m' = k', then succ m' = succ k'.
            exact congrArg succ h_m'_eq_k'

    theorem mul_assoc (n m k : PeanoNat) :
      mul (mul m n) k = mul m (mul n k)
        := by
          induction n with
          | zero =>
            rw [mul_zero, zero_mul] -- Simplifies LHS to zero: (m*0)*k -> 0*k -> 0. Also simplifies RHS m*(0*k) to m*0. Goal: 0 = m*0.
            rw [mul_zero]           -- Simplifies RHS (m*0) to zero. Goal: 0 = 0.
          | succ n' ih =>
            -- Goal: ((succ n')*m)*k = m*((succ n')*k)
            -- ih: (n'*m)*k = m*(n'*k)
            rw [succ_mul]       -- Applies to (succ n')*k on RHS.
                                -- Goal: (m*(succ n'))*k = m*((n'*k)+k)
            rw [mul_succ]       -- Applies to m*(succ n') on LHS.
                                -- Goal: ((m*n')+m)*k = m*((n'*k)+k)
            rw [mul_rdistr]     -- Applies to LHS.
                                -- Goal: (m*n')*k + m*k = m*((n'*k)+k)
            rw [ih]             -- Applies to (m*n')*k on LHS.
                                -- Goal: m*(n'*k) + m*k = m*((n'*k)+k)
            -- The following rw [succ_mul] is now redundant because the first one handled (succ n')*k on RHS.
            -- rw [succ_mul]       -- Was intended for (succ n')*k on RHS.
                                -- Goal was: m*(n'*k) + m*k = m*((n'*k)+k)
            rw [mul_ldistr]     -- Applies to RHS.
                                -- Goal: m*(n'*k) + m*k = m*(n'*k) + m*k
                                -- This is true by reflexivity.

end PeanoNat
