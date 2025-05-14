-- PeanoNat.lean
-- import Mathlib.Tactic
-- Definición inductiva del tipo PeanoNat
-- (incluye el 0->zero)

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

  -- === Teoremas básicos y propiedades de PeanoNat ===
  -- === (definidos ANTES de usarlos en subtipos)   ===
  @[simp]
  theorem succ_neq_zero (m : PeanoNat) : succ m ≠ zero :=
    fun h_eq_zero => PeanoNat.noConfusion h_eq_zero

  -- Define Lt early for forward declarations
  def Lt (n m : PeanoNat) : Prop :=
    match n, m with
    | PeanoNat.zero, PeanoNat.zero      => False
    | PeanoNat.zero, PeanoNat.succ _    => True
    | PeanoNat.succ _, PeanoNat.zero    => False
    | PeanoNat.succ n', PeanoNat.succ m' => Lt n' m'

  infix:50 "<" => Lt

  -- These theorems are declared here but will be proved after Lt is defined
  -- Forward declaration only - implementation is provided later
  theorem not_lt_zero_self : ¬ (zero < zero) := by
    intro h_lt
    unfold Lt at h_lt
    exact False.elim h_lt

  theorem not_succ_lt_zero (n: PeanoNat): ¬(PeanoNat.succ n < zero) := by
    intro h_lt
    unfold Lt at h_lt
    exact False.elim h_lt

  theorem neq_succ (k : PeanoNat) : k ≠ succ k := by
    induction k with
    | zero =>
      intro h_eq_zero_succ_zero
      exact PeanoNat.succ_neq_zero zero h_eq_zero_succ_zero.symm
    | succ k' ih_k' =>
      intro h_eq_succ_k_succ_succ_k
      have h_k_eq_succ_k : k' = succ k' := PeanoNat.succ.inj h_eq_succ_k_succ_succ_k
      exact ih_k' h_k_eq_succ_k

  theorem succ_lt_succ (a b : PeanoNat) :
    Lt a b → Lt (succ a) (succ b) := by
    intro h_lt
    induction a generalizing b with
    | zero =>
      cases b with
      | zero => exact False.elim (not_lt_zero_self h_lt)
      | succ b' => unfold Lt; exact h_lt
    | succ a' ih =>
      cases b with
      | zero => exact False.elim (not_succ_lt_zero a' h_lt)
      | succ b' => unfold Lt at h_lt ⊢; exact h_lt

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

      def pred (p : FacPeanoNat) : PosPeanoNat :=
        if h_is_two : p.val = PosPeanoNat.two then
          PosPeanoNat.one
        else
          have pred_val_neq_zero : PeanoNat.pred p.val.val ≠ PeanoNat.zero := by
            intro h_pred_val_eq_zero
            have p_val_val_eq_one : p.val.val = PeanoNat.one := by
              cases h_pvv_eq : p.val.val with
              | zero => exact absurd h_pvv_eq p.val.property
              | succ k_pn =>
                simp [PeanoNat.pred, h_pvv_eq] at h_pred_val_eq_zero
                rw [h_pred_val_eq_zero]
                congr
            have p_val_eq_pos_one : p.val = PosPeanoNat.one := Subtype.eq p_val_val_eq_one
            exact p.property p_val_eq_pos_one
          ⟨PeanoNat.pred p.val.val, pred_val_neq_zero⟩

      theorem succ_neq_one_proof (p_arg : PosPeanoNat) :
        PosPeanoNat.succ p_arg ≠ PosPeanoNat.one
          := by
            intro h_eq
            have h_val_eq : (PosPeanoNat.succ p_arg).val = PosPeanoNat.one.val := by
              rw [h_eq]
            simp [PosPeanoNat.succ, PosPeanoNat.one] at h_val_eq
            have h_p_arg_val_eq_zero : p_arg.val = PeanoNat.zero := by
              injection h_val_eq with h_p_arg_val_eq_zero_inner
            exact p_arg.property h_p_arg_val_eq_zero

      def succ_to_fac (p_arg : PosPeanoNat) : FacPeanoNat := -- Renamed from succ
        ⟨PosPeanoNat.succ p_arg, succ_neq_one_proof p_arg⟩
    end FacPeanoNat
  end PosPeanoNat

  -- === Teoremas Relacionados con Lt ===
  def lt_decidable : ∀ (n m : PeanoNat), Decidable (n < m)
    | zero, zero               => isFalse (fun h => by { unfold Lt at h; cases h })
    | zero, PeanoNat.succ _    => isTrue  (by { unfold Lt; exact True.intro })
    | PeanoNat.succ _, zero    => isFalse (fun h => by { unfold Lt at h; cases h })
    | PeanoNat.succ n', PeanoNat.succ m'  => lt_decidable n' m'
  instance : ∀ (n m : PeanoNat), Decidable (n < m) := lt_decidable

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
            · rw [h_and_k0.right.symm]
              unfold Lt
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
      intro h_ble_true
      cases m with
      | zero => exact Le.refl_le
      | succ m' => apply Le.strict_lt; exact lt_zero_succ m'
    | succ n' ih_n' =>
      intro h_ble_true
      cases m with
      | zero => exact False.elim (Bool.noConfusion h_ble_true)
      | succ m' =>
        have h_n_prime_le_m_prime : n' <= m' := ih_n' m' h_ble_true
        cases h_n_prime_le_m_prime with
        | strict_lt h_lt_inner => apply Le.strict_lt; unfold Lt; exact h_lt_inner
        | refl_le => apply Le.refl_le

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
      | zero => intro h_le_zz; simp [BLe]
      | succ m' => intro h_le_zsm; simp [BLe]
    | succ n' ih_n' =>
      induction m with
      | zero =>
        intro h_le_snz; simp [BLe]
        cases h_le_snz with
        | strict_lt h_lt => exact False.elim (not_succ_lt_zero n' h_lt)
      | succ m' =>
        intro h_le_snsm; simp [BLe]
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
    else
      isFalse (
        fun h_n_le_m_proof =>
        have h_ble_should_be_true : BLe n m = true := (ble_iff_le n m).mpr h_n_le_m_proof
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

  theorem le_zero (n : PeanoNat) : Le zero n := by
    cases n with
    | zero => exact Le.refl_le
    | succ n_prime => exact Le.strict_lt (lt_zero_succ n_prime)

  theorem le_n_zero_eq_zero (n : PeanoNat) (h_n_le_zero : Le n zero) : n = zero := by
    cases n with
    | zero => rfl
    | succ n' =>
      exfalso
      cases h_n_le_zero with
      | strict_lt h_lt =>
        exact not_succ_lt_zero n' h_lt

  theorem le_antisymm {n m : PeanoNat} (h1 : Le n m) (h2 : Le m n) : n = m := by
    match h1, h2 with
    | Le.refl_le, _ => rfl
    | _, Le.refl_le => rfl
    | Le.strict_lt h_n_lt_m, Le.strict_lt h_m_lt_n =>
        exact False.elim ((lt_not_symm n m h_n_lt_m) h_m_lt_n)

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

  theorem add_zero (n : PeanoNat) : add n zero = n
    := by
      induction n with
      | zero => simp [add]
      | succ n' ih => simp [add]

  theorem zero_add (n : PeanoNat) : add zero n = n
    := by
      induction n with
      | zero => simp [add]
      | succ n' ih => simp [add]; exact ih

  theorem add_one (n : PeanoNat) : add n one = succ n
    := by
      induction n with
      | zero => rfl
      | succ n' ih => unfold add; rw [<-ih]; rfl

  theorem one_add (n : PeanoNat) : add one n = succ n
    := by
      induction n with
      | zero => rfl
      | succ n' ih => unfold add; rw [<-ih]

  theorem add_succ (n m : PeanoNat) : add n (succ m) = succ (add n m)
    := by
      induction n with
      | zero => simp [add]
      | succ n' ih => simp [add]

  theorem succ_add (n m : PeanoNat) : add (succ n) m = succ (add n m)
    := by
      induction m with
      | zero => rw [add, add]
      | succ n' ih => simp [add]; rw [ih]

  theorem add_comm (n m : PeanoNat) : add n m = add m n
    := by
      induction n with
      | zero => rw [zero_add]; rw [add_zero]
      | succ n' ih => rw [succ_add]; rw [ih]; exact add_succ m n'

  theorem add_assoc (n m k : PeanoNat) : add n (add m k) = add (add n m) k
    := by
      induction n with
      | zero => rw [zero_add]; rw [zero_add]
      | succ n' ih => rw [succ_add]; rw [ih]; rw [succ_add]; rw [succ_add]

  theorem add_le (a b c : PeanoNat) : Le a b → Le a (add b c) := by
    intro h_le
    induction c with
    | zero => rw [add_zero]; exact h_le
    | succ c' ih => rw [add_succ]; exact le_succ a (add b c') ih

  theorem add_lt (n m k : PeanoNat) : Lt n m → Lt n (add m k)
    := by
      intro h_lt
      induction k with
      | zero => rw [add_zero]; exact h_lt
      | succ k' ih => rw [add_succ]; exact lt_succ n (add m k') ih

  theorem add_cancelation (n m k : PeanoNat) :
    add n m = add n k → m = k
      := by
        intro h_eq
        induction n with
        | zero => rw [zero_add, zero_add] at h_eq; exact h_eq
        | succ n' ih => rw [succ_add, succ_add] at h_eq; injection h_eq with h_m_eq_k; exact ih h_m_eq_k

  theorem cancelation_add (n m k : PeanoNat) :
    add m n = add k n → m = k
      := by
        intro h_eq
        induction n with
        | zero => rw [add_zero, add_zero] at h_eq; exact h_eq
        | succ n' ih => rw [add_succ, add_succ] at h_eq; injection h_eq with h_m_eq_k; exact ih h_m_eq_k

  theorem add_lt_cancelation (n m k : PeanoNat) :
    add n m < add n k → m < k
      := by
        intro h_lt
        induction n with
        | zero => rw [zero_add, zero_add] at h_lt; exact h_lt
        | succ n' ih => rw [succ_add, succ_add] at h_lt; exact ih h_lt

  theorem add_le_cancelation (n m k : PeanoNat) :
    Le (add n m) (add n k) → Le m k
      := by
        intro h_le
        induction n with
        | zero => rw [zero_add, zero_add] at h_le; exact h_le
        | succ n' ih => rw [succ_add, succ_add] at h_le; exact ih (le_of_succ_le_succ h_le)

  theorem add_eq_zero_iff (a b : PeanoNat) :
    add a b = zero ↔ a = zero ∧ b = zero
      := by
        constructor
        · intro h_eq
          induction a with
          | zero => rw [zero_add] at h_eq; exact ⟨rfl, h_eq⟩
          | succ a' ih => rw [succ_add] at h_eq; exact PeanoNat.noConfusion h_eq
        · intro ⟨h_a_eq_zero, h_b_eq_zero⟩; rw [h_a_eq_zero, h_b_eq_zero]; rfl

  theorem le_iff_exists_add (a b : PeanoNat) :
    Le a b ↔ ∃ p, b = add a p
    := by
    constructor
    · intro h_le_a_b
      revert a
      induction b with
      | zero =>
        intro a_val h_a_le_zero
        have h_a_eq_zero : a_val = zero := le_n_zero_eq_zero a_val h_a_le_zero
        rw [h_a_eq_zero]
        exact Exists.intro zero rfl
      | succ k ih_k =>
        intro a_val h_a_le_succ_k
        have lemma_lt_succ_imp_le (curr_a curr_k_lemma : PeanoNat) : Lt curr_a (succ curr_k_lemma) → Le curr_a curr_k_lemma := by
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
            | zero => exact le_zero (succ k_prime)
            | succ ca' =>
              unfold Lt at h_curr_a_lt_succ_curr_k_lemma
              apply le_succ_succ
              exact ih_k_prime ca' h_curr_a_lt_succ_curr_k_lemma
        cases (le_then_eq_xor_lt a_val (succ k)) h_a_le_succ_k with
        | inl h_a_eq_succ_k =>
          rw [h_a_eq_succ_k]
          exact Exists.intro zero (add_zero (succ k))
        | inr h_a_lt_succ_k =>
          have h_a_le_k : Le a_val k := lemma_lt_succ_imp_le a_val k h_a_lt_succ_k
          specialize ih_k a_val h_a_le_k
          cases ih_k with | intro p_prime h_k_eq_add_a_p_prime =>
            rw [h_k_eq_add_a_p_prime]
            exact Exists.intro (succ p_prime) rfl
    · intro h_exists
      cases h_exists with | intro p_val h_b_eq_add_a_p_val =>
        rw [h_b_eq_add_a_p_val]
        clear h_b_eq_add_a_p_val
        induction p_val with
        | zero => rw [add_zero]; exact Le.refl_le
        | succ p_prime ih_p_prime => rw [add_succ]; exact le_succ a (add a p_prime) ih_p_prime

  theorem lt_add_cancel (a b : PeanoNat) :
    Lt a b ↔ ∀ (k: PeanoNat), Lt (add a k) (add b k)
      := by
        constructor
        · intro h_lt_a_b; intro k_val
          induction k_val with
          | zero => rw [add_zero]; exact h_lt_a_b
          | succ k' ih_k' => rw [add_succ, add_succ]; unfold Lt; exact ih_k'
        · intro h_add_lt; have h_add_lt_zero : Lt (add a zero) (add b zero) := h_add_lt zero; exact h_add_lt_zero

  theorem lt_iff_exists_add_succ (a b : PeanoNat) :
    Lt a b ↔ ∃ p, b = add a (succ p)
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

  def mul (n m : PeanoNat) : PeanoNat :=
    match m with
    | zero => zero
    | succ m' => add (mul n m') n

  infix:70 "*" => mul

  theorem mul_zero (n : PeanoNat) : mul n zero = zero := by simp [mul]
  theorem zero_mul (n : PeanoNat) : mul zero n = zero := by
    induction n with
    | zero => simp [mul]
    | succ n' ih => simp [mul, ih, add_zero]

  theorem succ_mul (n m : PeanoNat) : mul (succ n) m = add (mul n m) m := by
    induction m with
    | zero => rw [mul_zero, mul_zero, add_zero]
    | succ m' ih =>
      simp [mul]; rw [ih]; rw [←add_assoc (mul n m') m' n.succ]; rw [←add_assoc (mul n m') n m'.succ]
      apply congrArg (add (mul n m')); rw [add_succ m' n, add_succ n m']; apply congrArg succ; exact add_comm m' n

  theorem mul_succ (n m : PeanoNat) : mul n (succ m) = add (mul n m) n := by rfl
  theorem mul_one (n : PeanoNat) : mul n one = n := by
    induction n with
    | zero => rfl
    | succ n' ih => rw [succ_mul, ih, add_one]
  theorem one_mul (m : PeanoNat) : mul one m = m := by
    induction m with
    | zero => rfl
    | succ m' ih => rw [mul_succ, ih, add_one]

  theorem mul_two (n : PeanoNat): mul n two = add n n := by
    induction n with
    | zero => rfl
    | succ n' ih => rw [succ_mul, ih, PeanoNat.two]; rw [add_succ, add_one]; rw [succ_add, add_succ]
  theorem mul_comm (n m : PeanoNat) : mul n m = mul m n := by
    induction m with
    | zero => rw [mul_zero, zero_mul]
    | succ m' ih => simp [mul]; rw [ih]; rw [succ_mul m' n]
  theorem two_mul (m : PeanoNat) : mul two m = add m m := by rw [mul_comm, mul_two]

  theorem mul_ldistr (m n k : PeanoNat) : mul m (add n k) = add (mul m n) (mul m k) := by
    induction k with
    | zero => rw [add_zero, mul_zero, add_zero]
    | succ k' ih => rw [add_succ, mul_succ, ih, mul_succ, add_assoc (mul m n) (mul m k') m]

  theorem mul_rdistr (m n k : PeanoNat) : mul (add m n) k = add (mul m k) (mul n k) := by
    induction k with
    | zero => rw [mul_zero, mul_zero, mul_zero, add_zero]
    | succ k' ih =>
      calc
        mul (add m n) (succ k')
          = add (mul (add m n) k') (add m n) := by rw [mul_succ]
        _ = add (add (mul m k') (mul n k')) (add m n) := by rw [ih]
        _ = add (mul m k') (add (mul n k') (add m n)) := by rw [←add_assoc]
        _ = add (mul m k') (add (add (mul n k') m) n) := by rw [add_assoc (mul n k') m n]
        _ = add (mul m k') (add (add m (mul n k')) n) := by rw [add_comm (mul n k') m]
        _ = add (mul m k') (add m (add (mul n k') n)) := by rw [add_assoc m (mul n k') n]
        _ = add (add (mul m k') m) (add (mul n k') n) := by rw [←add_assoc]
        _ = add (mul m (succ k')) (mul n (succ k')) := by rw [←mul_succ, ←mul_succ]

  theorem neq_then_lt (n m : PeanoNat) : n ≠ m → (n < m) ∨ (m < n) := by
    intro h_neq; have h_n_eq_m_is_false : ¬(n = m) := by intro h_eq; exact h_neq h_eq
    cases trichotomy n m with
    | inl h_n_lt_m => exact Or.inl h_n_lt_m
    | inr h_rest => cases h_rest with | inl h_n_eq_m => exact False.elim (h_n_eq_m_is_false h_n_eq_m) | inr h_m_lt_n => exact Or.inr h_m_lt_n
  theorem lt_then_neq (n m : PeanoNat) : n < m → n ≠ m := by intro h_lt; exact lt_n_m_then_neq_n_m n m h_lt

  theorem mul_cancelation (n m k : PeanoNat) : n ≠ zero → (mul n m = mul n k → m = k) := by
    intro h_n_neq_zero h_mul_eq_nk
    induction m generalizing k with
    | zero =>
      rw [mul_zero] at h_mul_eq_nk
      cases k with
      | zero => rfl
      | succ k' =>
        rw [mul_succ] at h_mul_eq_nk
        cases n with
        | zero => exact False.elim (h_n_neq_zero rfl)
        | succ n_val =>
          -- mul (succ n_val) (succ k') = add (mul (succ n_val) k') (succ n_val)
          -- This is never zero, so contradiction
          have : add (mul (succ n_val) k') (succ n_val) ≠ zero := by
            intro h
            -- add ... (succ n_val) = 0, so both must be zero, but succ n_val ≠ 0
            exact PeanoNat.succ_neq_zero n_val ((add_eq_zero_iff _ _).mp h).2
          exact False.elim (this h_mul_eq_nk.symm)
    | succ m' ih =>
      cases k with
      | zero =>
        rw [mul_zero] at h_mul_eq_nk
        cases n with
        | zero => exact False.elim (h_n_neq_zero rfl)
        | succ n_val =>
          rw [mul_succ] at h_mul_eq_nk
          -- add (mul (succ n_val) m') (succ n_val) = 0, so contradiction as above
          have : add (mul (succ n_val) m') (succ n_val) ≠ zero := by
            intro h
            exact PeanoNat.noConfusion ((add_eq_zero_iff _ _).mp h).right
          exact False.elim (this h_mul_eq_nk)
      | succ k' =>
        rw [mul_succ, mul_succ] at h_mul_eq_nk
        -- add (mul n m') n = add (mul n k') n
        have h_eq : mul n m' = mul n k' := cancelation_add n (mul n m') (mul n k') h_mul_eq_nk
        have h_m'_eq_k' : m' = k' := ih k' h_eq
        exact congrArg succ h_m'_eq_k'

  theorem mul_assoc (n m k : PeanoNat) : mul (mul m n) k = mul m (mul n k) := by
    induction n with
    | zero => rw [mul_zero, zero_mul]; rw [mul_zero]
    | succ n' ih => rw [succ_mul]; rw [mul_succ]; rw [mul_rdistr]; rw [ih]; rw [mul_ldistr]

  def substract (n m : PeanoNat) (h : m <= n) : PeanoNat :=
    match n, m with
    | k, PeanoNat.zero => k
    | PeanoNat.zero, succ m' => False.elim (succ_neq_zero m' (le_n_zero_eq_zero (succ m') h))
    | succ n_s, succ m_s => substract n_s m_s (le_of_succ_le_succ h)
  termination_by n

  infix:50 "-" => substract

  theorem substract_zero (n : PeanoNat) : substract n zero (le_zero n) = n := by
    induction n with
    | zero => simp [substract, le_zero]
    | succ n' ih => simp [substract]

  theorem substract_eq_zero (n m : PeanoNat) (h : m <= n) : substract n m h = zero → n = m := by
    induction n generalizing m with
    | zero => intro h_sub_eq_zero; cases m with | zero => rfl | succ m' => have h_m_eq_zero := le_n_zero_eq_zero (succ m') h; exact False.elim (succ_neq_zero m' h_m_eq_zero)
    | succ n' ih_n' =>
      intro h_sub_eq_zero; cases m with
      | zero =>
        -- substract (succ n') zero (le_zero (succ n')) = succ n' by substract_zero
        have : substract (succ n') zero (le_zero (succ n')) = succ n' := substract_zero (succ n')
        have h_succ_n'_eq_zero : succ n' = zero := by
          rw [←h_sub_eq_zero]
          exact this.symm
        exact False.elim (succ_neq_zero n' h_succ_n'_eq_zero)
                                        | succ m' => have h' : m' <= n' := le_of_succ_le_succ h; unfold substract at h_sub_eq_zero; have h_n'_eq_m' := ih_n' m' h' h_sub_eq_zero; exact congrArg succ h_n'_eq_m'


  theorem substract_succ (n k : PeanoNat) (h_le : k <= succ n) : substract (succ n) k h_le = match k with | zero => succ n | succ k' => substract n k' (le_of_succ_le_succ h_le) := by
    cases k with
    | zero =>
      unfold substract
      rfl
    | succ k' =>
      simp [substract]

  theorem substract_k_add_k (n: PeanoNat): ∀ (k : PeanoNat) (h_le : k <= n), add (substract n k h_le) k = n := by
    intro k h_le
    induction n generalizing k with
    | zero =>
      have h_k_eq_zero : k = zero := le_n_zero_eq_zero k h_le
      subst h_k_eq_zero
      simp [substract, add]
    | succ n' ih =>
      cases k with
      | zero =>
        simp [substract, add]
      | succ k' =>
        simp only [substract_succ, add_succ]
        let h_le' := le_of_succ_le_succ h_le
        specialize ih k' h_le'
        rw [ih]

  theorem le_one_add_one (n: PeanoNat): Le one (add n one) := by
    rw [add_one]; cases n with | zero => exact Le.refl_le | succ n' => exact Le.strict_lt (lt_zero_succ n')

  theorem le_succ_add_succ (n k: PeanoNat): Le k (add n k) := by
    induction n with | zero => rw [zero_add]; exact le_refl k | succ n' ih => rw [succ_add]; exact le_succ k (add n' k) ih
  theorem le_add (n k: PeanoNat): Le k (add n k) := by
    induction n with | zero => rw [zero_add]; exact le_refl k | succ n' ih => rw [succ_add]; exact le_succ k (add n' k) ih
  theorem le_add_r (n k: PeanoNat): Le n (add n k) := by
    induction n with
    | zero => rw [zero_add]; exact le_zero k
    | succ n' ih => rw [succ_add]; apply le_succ_succ; exact ih

  theorem add_k_substract_k (n: PeanoNat): ∀ (k : PeanoNat), substract (add n k) k (le_add n k) = n := by
    intro k; induction k with
    | zero => simp [add_zero, substract_zero]
    | succ k' ih => simp [add_succ, substract_succ]; exact ih

  theorem substract_n_m_k_eq_n_m (n m k : PeanoNat) (kn_proof: Le k n) (km_proof: Le k m) : substract n k kn_proof = substract m k km_proof → n = m := by
    induction k generalizing n m with
    | zero => intro h_sub_eq; rw [substract_zero n, substract_zero m] at h_sub_eq; exact h_sub_eq
    | succ k' ih_k' =>
      intro h_sub_eq
      cases n with
      | zero => have h_succ_k_eq_zero := le_n_zero_eq_zero (succ k') kn_proof; exact False.elim (succ_neq_zero k' h_succ_k_eq_zero)
      | succ n' =>
        cases m with
        | zero => have h_succ_k_eq_zero := le_n_zero_eq_zero (succ k') km_proof; exact False.elim (succ_neq_zero k' h_succ_k_eq_zero)
        | succ m' =>
          rw [substract_succ] at h_sub_eq; conv at h_sub_eq => rhs; rw [substract_succ]
          have h_le_n'_k' : Le k' n' := le_of_succ_le_succ kn_proof
          have h_le_m'_k' : Le k' m' := le_of_succ_le_succ km_proof
          have h_n'_eq_m' := ih_k' n' m' h_le_n'_k' h_le_m'_k' h_sub_eq
          rw [h_n'_eq_m']

  theorem eq_n_m_substract_n_m_k (n m k : PeanoNat) (kn_proof: Le k n) (km_proof: Le k m) : n = m → substract n k kn_proof = substract m k km_proof := by
    induction k generalizing n m with
    | zero => intro h_n_eq_m; rw [substract_zero n, substract_zero m]; exact h_n_eq_m
    | succ k' ih_k' =>
      intro h_n_eq_m
      cases n with
      | zero => have h_succ_k_eq_zero := le_n_zero_eq_zero (succ k') kn_proof; exact False.elim (succ_neq_zero k' h_succ_k_eq_zero)
      | succ n' =>
        cases m with
        | zero => have h_succ_k_eq_zero := le_n_zero_eq_zero (succ k') km_proof; exact False.elim (succ_neq_zero k' h_succ_k_eq_zero)
        | succ m' =>
          have h_n_prime_eq_m_prime : n' = m' := PeanoNat.succ.inj h_n_eq_m
          rw [substract_succ]; conv => rhs; rw[substract_succ]
          have h_le_n'_k' : Le k' n' := le_of_succ_le_succ kn_proof
          have h_le_m'_k' : Le k' m' := le_of_succ_le_succ km_proof
          exact ih_k' n' m' h_le_n'_k' h_le_m'_k' h_n_prime_eq_m_prime

  theorem substract_one (n : PeanoNat) (h_le : one <= n) : substract n one h_le = pred n := by
    cases n with
    | zero => have h_one_eq_zero : PeanoNat.one = PeanoNat.zero := le_n_zero_eq_zero PeanoNat.one h_le; exact False.elim (succ_neq_zero PeanoNat.zero h_one_eq_zero)
    | succ n' => simp only [pred, substract, PeanoNat.one]

  theorem neq_0_1_then_gt_1 (n : PeanoNat): (n ≠ zero) ∧ (n ≠ one) → Lt one n := by
    intro h_all_neq; have h_n_neq_zero := h_all_neq.left; have h_n_neq_one := h_all_neq.right
    cases PeanoNat.trichotomy n one with
    | inl h_n_lt_one =>
      have h_n_eq_zero_from_lt_one : n = zero :=
        by cases n with
        | zero => rfl
        | succ n_plus =>
          unfold Lt at h_n_lt_one
          exact False.elim (PeanoNat.zero_is_the_minor n_plus h_n_lt_one)
      exact False.elim (h_n_neq_zero h_n_eq_zero_from_lt_one)
    | inr h_eq_or_gt =>
      cases h_eq_or_gt with
      | inl h_n_eq_one => exact False.elim (h_n_neq_one h_n_eq_one)
      | inr h_one_lt_n => exact h_one_lt_n

  theorem sub_one_lt_self (n : PeanoNat) (h_lt_one_n : Lt one n) : Lt (substract n one (Le.strict_lt h_lt_one_n)) n := by
    cases n with | zero => exact False.elim h_lt_one_n | succ n' => rw [substract_one (succ n') (Le.strict_lt h_lt_one_n)]; rw [pred_succ_eq_self n']; exact lt_n_succ_n n'

  theorem sub_succ_succ_lt_self (n m: PeanoNat) (h_lt_one_m : Lt one m) (h_le_m_n : Le m n) : Lt (substract n m h_le_m_n) n := by
    cases m with
    | zero => exact False.elim h_lt_one_m
    | succ m' =>
      cases m' with
      | zero => exact False.elim (lt_not_refl PeanoNat.one h_lt_one_m)
      | succ m'' =>
        let m := succ (succ m'')
        have h_zero_lt_m : Lt zero m := PeanoNat.lt_trans (PeanoNat.lt_n_succ_n PeanoNat.zero) h_lt_one_m
        have h_exists_p : ∃ p, n = add m p := (le_iff_exists_add m n).mp h_le_m_n
        cases h_exists_p with
        | intro p h_n_eq_add_m_p =>
          subst h_n_eq_add_m_p
          -- Now n = add m p
          have m_neq_zero : m ≠ zero := by
            intro hmz
            rw [hmz] at h_zero_lt_m
            exact lt_not_refl zero h_zero_lt_m

          -- Use the correct order of arguments and proper indentation
          -- h_le_m_n is Le m (add m p) from the context after `subst h_n_eq_add_m_p`
          have h_subst_eq : substract (add m p) m h_le_m_n = p := by
            revert h_le_m_n -- Generalizes h_le_m_n to an arbitrary proof of Le m (add m p)
            rw [add_comm m p] -- Changes goal to: ∀ (h_proof : Le m (add p m)), substract (add p m) m h_proof = p
            intro h_le_m_add_p_m_proof -- Introduces h_le_m_add_p_m_proof : Le m (add p m)
            exact add_k_substract_k p m -- This is substract (add p m) m (le_add p m) = p.
                                        -- Since substract's value is independent of the specific proof of Le m (add p m),
                                        -- and h_le_m_add_p_m_proof is such a proof, this holds.

          -- Simplify the goal using h_subst_eq
          rw [h_subst_eq]
          -- Goal is now: Lt p (add m p)
          rw [add_comm m p] -- Goal: Lt p (add p m)

          -- Now we need to prove Lt p (add p m)
          -- We need ∃ x, (add p m) = add p (succ x).
          -- Since m = succ (succ m''), we choose x = succ m''.
          -- Then (add p m) = add p (succ (succ m'')), which is true by rfl because m is succ (succ m'').
          exact (lt_iff_exists_add_succ p (add p m)).mpr (Exists.intro (succ m'') rfl)

  theorem sub_lt_self (n m : PeanoNat) (h_m_neq_0 : m ≠ PeanoNat.zero) (h_le_m_n : PeanoNat.Le m n) : PeanoNat.Lt (substract n m h_le_m_n) n := by
    cases m with
    | zero => exact False.elim (h_m_neq_0 rfl)
    | succ m_pred =>
      cases m_pred with
      | zero => -- m = one
        have h_one_le_n_cases := PeanoNat.le_then_eq_xor_lt PeanoNat.one n h_le_m_n
        cases h_one_le_n_cases with
        | inl h_n_eq_one =>
          subst h_n_eq_one
          simp only [PeanoNat.one, substract]
          exact PeanoNat.lt_zero_succ PeanoNat.zero
        | inr h_one_lt_n => exact sub_one_lt_self n h_one_lt_n
      | succ m_pred_pred => --
        let m := succ (succ m_pred_pred)
        have h_lt_one_m : PeanoNat.Lt PeanoNat.one m := by simp [PeanoNat.Lt, PeanoNat.one, m]
        exact sub_succ_succ_lt_self n m h_lt_one_m h_le_m_n

/-!
  BEGIN    ⟨ISOMOMORFISMOS ENTRE PEANONAR Y NAT DEL PRELUDE O DEL CORE DE LEAN4⟩
  !-/

-- Función auxiliar para convertir PeanoNat a Nat (para SizeOf y otras interacciones)
  def nat_to_peano (a :Nat): PeanoNat :=
    match a with
    | 0 => zero
    | Nat.succ a' => PeanoNat.succ (nat_to_peano a')

  def peano_to_nat (a :PeanoNat): Nat :=
    match a with
    | zero => 0
    | PeanoNat.succ a' => Nat.succ (peano_to_nat a')

  def identity_Nat_by_Peano : Nat -> Nat
      :=
          peano_to_nat ∘ nat_to_peano

  def identity_Peano_by_Nat : PeanoNat -> PeanoNat
      :=
          nat_to_peano ∘ peano_to_nat

/-- ESTUDIO DE    NAT_TO_PEANO: NAT -> PEANONAT    INYECTIVIDAD 1 -/
  theorem nat_to_peano_inj (a b: Nat) :
    nat_to_peano a ≠ nat_to_peano b → a ≠ b := by
    intro h_neq_peano_ab -- Hypothesis: nat_to_peano a ≠ nat_to_peano b
    -- Goal: a ≠ b
    induction a generalizing b with
    | zero => -- Case a = 0
      -- h_neq_peano_ab: nat_to_peano 0 ≠ nat_to_peano b
      -- Goal: 0 ≠ b
      cases b with
      | zero => -- Case b = 0
        -- h_neq_peano_ab: nat_to_peano 0 ≠ nat_to_peano 0
        -- This simplifies to: PeanoNat.zero ≠ PeanoNat.zero, which is False.
        -- Goal: 0 ≠ 0, which is False.
        simp only [nat_to_peano] at h_neq_peano_ab
        intro h_contra_b_eq_0 -- Assume 0 = 0 for the goal 0 ≠ 0. This is `rfl`.
        exact h_neq_peano_ab rfl
      | succ b' => -- Case b = Nat.succ b'
        -- h_neq_peano_ab: nat_to_peano 0 ≠ nat_to_peano (Nat.succ b') (true)
        -- Goal: 0 ≠ Nat.succ b' (true)
        exact (fun h : 0 = Nat.succ b' => Nat.noConfusion h)
    | succ a' ih_a' => -- Case a = Nat.succ a'
      -- h_neq_peano_ab: nat_to_peano (Nat.succ a') ≠ nat_to_peano b
      -- Goal: Nat.succ a' ≠ b
      -- ih_a' : ∀ (b_1 : Nat), nat_to_peano a' ≠ nat_to_peano b_1 → a' ≠ b_1
      cases b with
      | zero => -- Case b = 0
        -- h_neq_peano_ab: nat_to_peano (Nat.succ a') ≠ nat_to_peano 0 (true)
        -- Goal: Nat.succ a' ≠ 0 (true)
        exact Nat.succ_ne_zero a'
      | succ b' => -- Case b = Nat.succ b'
        -- h_neq_peano_ab: PeanoNat.succ (nat_to_peano a') ≠ PeanoNat.succ (nat_to_peano b')
        -- Goal: Nat.succ a' ≠ Nat.succ b'
        have h_neq_peano_inner : nat_to_peano a' ≠ nat_to_peano b' := by
          simp only [nat_to_peano] at h_neq_peano_ab
          exact PeanoNat.succ_inj_neg_th _ _ h_neq_peano_ab
        have h_a'_neq_b' : a' ≠ b' := ih_a' b' h_neq_peano_inner
        intro h_succ_a_eq_succ_b -- Assume Nat.succ a' = Nat.succ b'
        exact h_a'_neq_b' (Nat.succ.inj h_succ_a_eq_succ_b)

/-- ESTUDIO DE    NAT_TO_PEANO: NAT -> PEANONAT    INYECTIVIDAD 2 -/
  theorem nat2peano_inj:
    ∀ a b: Nat, nat_to_peano a ≠ nat_to_peano b → a ≠ b
      := by
        intro a b h_eq
        have h_neq := nat_to_peano_inj a b
        exact h_neq h_eq

/-- ESTUDIO DE    NAT_TO_PEANO: NAT -> PEANONAT    SOBREYECTIVIDAD 1 -/
  theorem nat_to_peano_sobr (a : PeanoNat) :
    ∃ b: Nat, nat_to_peano b = a := by
    induction a with
    | zero => exact Exists.intro 0 rfl
    | succ a' ih_a' =>
      cases ih_a' with
      | intro b' h_eq =>
        exact Exists.intro (Nat.succ b')
          (by simp [nat_to_peano, h_eq])

/-- ESTUDIO DE    NAT_TO_PEANO: NAT -> PEANONAT    SOBREYECTIVIDAD 2 -/
  theorem nat2peano_sobr:
      ∀ a: Nat, ∃ b: PeanoNat, nat_to_peano a = b
        := by
          intro a
          induction a with
          | zero =>
            exact Exists.intro PeanoNat.zero rfl
          | succ a' ih_a' =>
            cases ih_a' with | intro b_ih h_eq_b_ih =>
              exact Exists.intro (PeanoNat.succ b_ih)
                (by simp [nat_to_peano, h_eq_b_ih])

/-!***!
      ESTUDIO DE    NAT_TO_PEANO: NAT -> PEANONAT    BIYECTIVIDAD
  !***!-/
  theorem nat_to_peano_is_bijective:
    (∀ a b: Nat, nat_to_peano a = nat_to_peano b → a = b)
    ∧
    (∀ a : PeanoNat, ∃ b : Nat, nat_to_peano b = a)
    := by
      constructor
      · -- Proof of injectivity: ∀ a b: Nat, nat_to_peano a = nat_to_peano b → a = b
        intro a b h_eq_peano
        -- This logic is similar to the backward direction of eq_nat_then_eq_peano
        induction a generalizing b with
        | zero =>
          cases b with
          | zero => rfl
          | succ b' =>
            simp only [nat_to_peano] at h_eq_peano
            exact False.elim (PeanoNat.succ_neq_zero (nat_to_peano b') h_eq_peano.symm)
        | succ a' ih_a' =>
          cases b with
          | zero =>
            simp only [nat_to_peano] at h_eq_peano
            exact False.elim (PeanoNat.succ_neq_zero (nat_to_peano a') h_eq_peano)
          | succ b' =>
            simp only [nat_to_peano] at h_eq_peano
            have h_inner_eq : nat_to_peano a' = nat_to_peano b' := PeanoNat.succ.inj h_eq_peano
            have h_a'_eq_b' : a' = b' := ih_a' b' h_inner_eq
            exact congrArg Nat.succ h_a'_eq_b'
      · -- Proof of surjectivity: ∀ a : PeanoNat, ∃ b : Nat, nat_to_peano b = a
        exact nat_to_peano_sobr


/-- ESTUDIO DE    PEANONAT_TO_NAT: PEANONAT -> NAT    INYECTIVIDAD 1 -/
  theorem peano_to_nat_inj (a b: PeanoNat) :
    peano_to_nat a ≠ peano_to_nat b → a ≠ b := by
    intro h_neq_nat_images -- h_neq_nat_images : peano_to_nat a ≠ peano_to_nat b
    induction a generalizing b with
    | zero => -- a = PeanoNat.zero
      cases b with
      | zero => -- b = PeanoNat.zero
        -- h_neq_nat_images is `peano_to_nat zero ≠ peano_to_nat zero`, i.e., `0 ≠ 0`.
        -- Goal is `PeanoNat.zero ≠ PeanoNat.zero`.
        intro h_eq_peano_zero -- Assume PeanoNat.zero = PeanoNat.zero
        apply h_neq_nat_images
        exact congrArg peano_to_nat h_eq_peano_zero
      | succ b' => -- b = PeanoNat.succ b'
        -- h_neq_nat_images is `0 ≠ Nat.succ (peano_to_nat b')`. This is true.
        -- Goal is `PeanoNat.zero ≠ PeanoNat.succ b'`. This is true.
        intro h_eq_zero_succ -- Assume PeanoNat.zero = PeanoNat.succ b'
        cases h_eq_zero_succ -- Contradiction
    | succ a' ih_a' => -- a = PeanoNat.succ a'
      -- ih_a' : ∀ (b_1 : PeanoNat), peano_to_nat a' ≠ peano_to_nat b_1 → a' ≠ b_1
      cases b with
      | zero => -- b = PeanoNat.zero
        -- h_neq_nat_images is `Nat.succ (peano_to_nat a') ≠ 0`. This is true.
        -- Goal is `PeanoNat.succ a' ≠ PeanoNat.zero`. This is true.
        intro h_eq_succ_zero -- Assume PeanoNat.succ a' = PeanoNat.zero
        cases h_eq_succ_zero -- Contradiction
      | succ b' => -- b = PeanoNat.succ b'
        -- h_neq_nat_images is `Nat.succ (peano_to_nat a') ≠ Nat.succ (peano_to_nat b')`
        -- Goal is `PeanoNat.succ a' ≠ PeanoNat.succ b'`.
        have h_inner_nat_neq : peano_to_nat a' ≠ peano_to_nat b' := fun h_eq =>
          h_neq_nat_images (congrArg Nat.succ h_eq)
        have h_a_prime_neq_b_prime : a' ≠ b' := ih_a' b' h_inner_nat_neq
        intro h_eq_succ_a_succ_b -- Assume PeanoNat.succ a' = PeanoNat.succ b'
        have h_eq_a_b : a' = b' := PeanoNat.succ.inj h_eq_succ_a_succ_b
        exact h_a_prime_neq_b_prime h_eq_a_b

/-- ESTUDIO DE    PEANONAT_TO_NAT: PEANONAT -> NAT    INYECTIVIDAD 2 -/
  theorem peano2nat_inj:
    ∀ a b: PeanoNat, peano_to_nat a ≠ peano_to_nat b → a ≠ b
      := by
        intro a b h_eq
        have h_neq := peano_to_nat_inj a b
        exact h_neq h_eq

/-- ESTUDIO DE    PEANONAT_TO_NAT: PEANONAT -> NAT    SOBREYECTIVIDAD 1 -/
  theorem peano_to_nat_sobr (a : Nat) :
    ∃ (b: PeanoNat), peano_to_nat b = a := by
    induction a with
    | zero => exact Exists.intro PeanoNat.zero rfl
    | succ a' ih_a' =>
      cases ih_a' with
      | intro b' h_eq =>
        exact Exists.intro (PeanoNat.succ b')
          (by simp [peano_to_nat, h_eq])

/-- ESTUDIO DE    PEANONAT_TO_NAT: PEANONAT -> NAT    SOBREYECTUIVIDAD 2 -/
  theorem peano2nat_sobr:
      ∀ (a: Nat), ∃ (b: PeanoNat), peano_to_nat b = a
        := by
          intro a
          induction a with
          | zero =>
            exact Exists.intro PeanoNat.zero rfl
          | succ a' ih_a' =>
            cases ih_a' with | intro b_ih h_eq_b_ih =>
              exact Exists.intro (PeanoNat.succ b_ih)
                (by simp [peano_to_nat, h_eq_b_ih])

/-!***!
      ESTUDIO DE    PEANO_TO_NAT: PEANONAT -> NAT    BIYECTIVIDAD
  !***!-/
  theorem peano_to_nat_is_bijective:
    (∀ a b: PeanoNat, peano_to_nat a = peano_to_nat b → a = b)
    ∧
    (∀ a : Nat, ∃ b : PeanoNat, peano_to_nat b = a)
    := by
      constructor
      · intro a b h_eq_nat
        induction a generalizing b with
        | zero =>
          cases b with
          | zero => rfl
          | succ b' =>
              simp [peano_to_nat] at h_eq_nat
        | succ a' ih_a' =>
          cases b with
          | zero =>
            simp [peano_to_nat] at h_eq_nat
          | succ b' =>
            -- Need to properly handle the equality
            simp only [peano_to_nat] at h_eq_nat
            have h_nat_eq : peano_to_nat a' = peano_to_nat b' := by
              injection h_eq_nat with h_eq_inner
            have h_a'_eq_b' : a' = b' := ih_a' b' h_nat_eq
            exact congrArg PeanoNat.succ h_a'_eq_b'
      · intro a
        exact peano_to_nat_sobr a

/-!***!
       A CONTINUACIÓN VEREMOS EL ISOMORFISMO DE IGUALDAD
       NAT.EQ IMPLICA PEANONAT.EQ (1(er) TEOREMA ISOMORFISMO EN NAT A PEANONAT
       PEANONAT.EQ IMPLICA NAT.EQ (2(do) TEOREMA ISOMORFISMO EN PEANONAT A NAT
       PEANONAT_TO_NAT ∘ NAT_TO_PEANO = ID: PEANONAT -> PEANONAT (3(er) TEOREMA ISOMORFISMO)
       NAT_TO_PEANONAT ∘ PEANONAT_TO_NAT = ID: NAT -> NAT (4(er) TEOREMA ISOMORFISMO)
  !***!-/

  def PeanoNat.id: PeanoNat -> PeanoNat := λ a => a

end PeanoNat

  def Nat.id: Nat -> Nat := λ a => a
namespace PeanoNat

-- NAT_TO_PEANONAT ∘ PEANONAT_TO_NAT = ID: NAT -> NAT (4(to) TEOREMA ISOMORFISMO)
  def nat2peano2nat: Nat -> Nat := peano_to_nat ∘ nat_to_peano

  theorem nat2peano2nat_eq_idnat_by_elem(a : Nat): nat2peano2nat a = a := by
    induction a with
    | zero => rfl
    | succ a' ih =>
      unfold nat2peano2nat
      simp only [Function.comp_apply, nat_to_peano, peano_to_nat]
      rw [←Nat.add_one]
      congr

-- AHORA VAMOS A DEMOSTRAR QUE NAT2PEANO2NAT = NAT.ID
  theorem nat2peano2nat_eq_idnat: nat2peano2nat = Nat.id := by
    ext a
    unfold nat2peano2nat Nat.id
    induction a with
    | zero => rfl
    | succ a' ih =>
      simp only [Function.comp_apply, nat_to_peano, peano_to_nat]
      rw [←Nat.add_one]
      congr

-- PEANO_TO_NAT ∘ NAT_TO_PEANO = ID: PEANONAT ->PEANO NAT (3(er) TEOREMA ISOMORFISMO)
  def peano2nat2peano: PeanoNat -> PeanoNat := nat_to_peano ∘ peano_to_nat
-- AHORA VAMOS A DEMOSTRAR QUE NAT2PEANO2NAT = NAT.ID
  theorem peano2nat2peano_eq_idpeano: peano2nat2peano = PeanoNat.id := by
    ext a
    unfold peano2nat2peano PeanoNat.id
    induction a with
    | zero => rfl
    | succ a' ih =>
      simp only [Function.comp_apply, nat_to_peano, peano_to_nat]
      -- Use the induction hypothesis
      congr

  theorem peano2nat2peano_eq_idpeano_by_elem(a : PeanoNat): peano2nat2peano a = a := by
    induction a with
    | zero => rfl
    | succ a' ih =>
      unfold peano2nat2peano
      simp only [Function.comp_apply, nat_to_peano, peano_to_nat]
      -- Use the induction hypothesis
      congr

/--!   NAT.EQ IMPLICA PEANONAT.EQ (1(er) TEOREMA ISOMORFISMO EN PEANONAT A NAT
       Define the eq_peano_then_eq_nat theorem first
   !--/
  theorem eq_peano_then_eq_nat (a b: PeanoNat) :
    a = b ↔ (peano_to_nat a) = (peano_to_nat b)
    := by
      constructor
      · -- Forward direction: a = b → peano_to_nat a = peano_to_nat b
        intro h_eq
        exact congrArg peano_to_nat h_eq
      · -- Backward direction: peano_to_nat a = peano_to_nat b → a = b
        intro h_eq_nat_images
        induction a generalizing b with
        | zero => -- a is PeanoNat.zero, so peano_to_nat a is 0
          cases b with
          | zero => rfl -- b is PeanoNat.zero, peano_to_nat b is 0. 0 = 0 implies PeanoNat.zero = PeanoNat.zero.
          | succ b' => -- b is PeanoNat.succ b', peano_to_nat b is Nat.succ (peano_to_nat b')
            simp only [peano_to_nat] at h_eq_nat_images -- h_eq_nat_images becomes 0 = Nat.succ (peano_to_nat b')
            exact Nat.noConfusion h_eq_nat_images -- This is a contradiction in Nat (0 cannot be succ).
        | succ a' ih_a' => -- a is PeanoNat.succ a', peano_to_nat a is Nat.succ (peano_to_nat a')
          cases b with
          | zero => -- b is PeanoNat.zero, peano_to_nat b is 0
            simp only [peano_to_nat] at h_eq_nat_images -- h_eq_nat_images becomes Nat.succ (peano_to_nat a') = 0
            exact Nat.noConfusion h_eq_nat_images -- This is a contradiction in Nat (succ cannot be 0).
          | succ b' => -- b is PeanoNat.succ b', peano_to_nat b is Nat.succ (peano_to_nat b')
            simp only [peano_to_nat] at h_eq_nat_images -- h_eq_nat_images becomes Nat.succ (peano_to_nat a') = Nat.succ (peano_to_nat b')
            have h_inner_nat_eq : peano_to_nat a' = peano_to_nat b' := Nat.succ.inj h_eq_nat_images
            have h_a'_eq_b' : a' = b' := ih_a' b' h_inner_nat_eq
            exact congrArg PeanoNat.succ h_a'_eq_b'

  theorem isomorfism_PeanoNat_Nat_Lt (a b: PeanoNat) :
    Lt a b ↔ (peano_to_nat a) < (peano_to_nat b) := by
    constructor
    · -- Forward direction: Lt a b → (peano_to_nat a) < (peano_to_nat b)
      induction a generalizing b with
      | zero =>
        intro h_lt
        cases b with
        | zero =>
          -- Goal: Lt zero zero → 0 < 0
          -- This is vacuously true since Lt zero zero is false
          exact False.elim (PeanoNat.lt_not_refl zero h_lt)
        | succ b' =>
            -- Goal: Lt zero (succ b') → 0 < (succ b')
            -- This is true.
            simp [peano_to_nat]
            -- Nat.zero_lt_succ is automatically applied by simp
      | succ a' ih_a' =>
        intro h_lt
        cases b with
        | zero =>
          -- Goal: Lt (succ a') zero → (succ a') < 0
          -- This is vacuously true since Lt (succ a') zero is false
          exact False.elim (PeanoNat.not_succ_lt_zero a' h_lt)
        | succ b' =>
          -- Goal: Lt (succ a') (succ b') → (succ a') < (succ b')
          -- Need to use the induction hypothesis and apply Nat.succ_lt_succ
          -- h_lt has type (peano_to_nat (succ a') < peano_to_nat (succ b'))
          -- We need to simplify this using the definition of peano_to_nat
          -- Unfold the definition of peano_to_nat for succ cases
          have h_iso_succ_a : peano_to_nat (succ a') = Nat.succ (peano_to_nat a') := rfl
          have h_iso_succ_b : peano_to_nat (succ b') = Nat.succ (peano_to_nat b') := rfl

          -- Extract Lt a' b' from Lt (succ a') (succ b')
          -- Since Lt (succ a') (succ b') is defined to be Lt a' b'
          have h_a_lt_b : peano_to_nat a' < peano_to_nat b' := ih_a' b' h_lt

          -- Now show that Nat.succ (peano_to_nat a') < Nat.succ (peano_to_nat b')
          rw [h_iso_succ_a, h_iso_succ_b]
          exact Nat.succ_lt_succ h_a_lt_b
    · -- Backward direction: (peano_to_nat a) < (peano_to_nat b) → Lt a b
      induction b generalizing a with
      | zero    =>
        intro h_lt
        cases a with
        | zero =>
          -- Goal: 0 < 0 → Lt zero zero
          -- This is vacuously true since 0 < 0 is false
          exact False.elim (Nat.not_lt_zero (peano_to_nat zero) h_lt)
        | succ a' =>
          -- Goal: (succ a') < 0 → Lt (succ a') zero
          -- This is vacuously true since (succ a') < 0 is false
          -- Nat.not_lt_zero proves that we can't have a natural number less than zero
          exact False.elim (Nat.not_lt_zero (peano_to_nat (succ a')) h_lt)
      | succ b' ih_b' =>
        intro h_lt
        cases a with
        | zero =>
          -- Goal: peano_to_nat zero < peano_to_nat (succ b') → Lt zero (succ b')
          -- This is true.
          exact PeanoNat.lt_zero_succ b'
        | succ a' =>
          -- h_lt is (peano_to_nat (succ a')) < (peano_to_nat (succ b'))
          -- Goal is Lt (succ a') (succ b')
          simp [peano_to_nat] at h_lt
          -- After simp, h_lt becomes (peano_to_nat a' < peano_to_nat b')
          -- due to peano_to_nat unfolding and Nat.succ_lt_succ_iff.
          have h_lt_inner_nat : peano_to_nat a' < peano_to_nat b' := h_lt
          have h_lt_inner_peano : Lt a' b' := ih_b' a' h_lt_inner_nat
          -- The goal Lt (succ a') (succ b') is by definition Lt a' b',
          -- so we can provide a proof of Lt a' b'.
          -- Alternatively, PeanoNat.succ_lt_succ h_lt_inner_peano proves Lt (succ a') (succ b').
          exact h_lt_inner_peano

  theorem isomorfism_Nat_PeanoNat_Lt (a b: Nat) :
    a < b ↔ (nat_to_peano a) < (nat_to_peano b)
    := by
    constructor
    · -- Forward direction: a < b → (nat_to_peano a) < (nat_to_peano b)
      intro h_a_lt_b
      induction a generalizing b with
      | zero =>
        cases b with
        | zero => exact False.elim (Nat.lt_irrefl 0 h_a_lt_b)
        | succ b' =>
          simp only [nat_to_peano]
          exact PeanoNat.lt_zero_succ (nat_to_peano b')
      | succ a' ih_a' =>
        cases b with
        | zero => exact False.elim ((Nat.not_lt_zero (Nat.succ a')) h_a_lt_b)
        | succ b' =>
          have h_a_prime_lt_b_prime : a' < b' := Nat.succ_lt_succ_iff.mp h_a_lt_b
          simp only [nat_to_peano, PeanoNat.Lt]
          exact ih_a' b' h_a_prime_lt_b_prime
    · -- Backward direction: (nat_to_peano a) < (nat_to_peano b) → a < b
      intro h_lt_peano
      induction b generalizing a with
      | zero =>
        cases a with
        | zero => exact False.elim (PeanoNat.lt_not_refl PeanoNat.zero h_lt_peano)
        | succ a' => exact False.elim (PeanoNat.not_succ_lt_zero (nat_to_peano a') h_lt_peano)
      | succ b' ih_b' =>
        cases a with
        | zero => exact Nat.zero_lt_succ b'
        | succ a' =>
          simp only [nat_to_peano, PeanoNat.Lt] at h_lt_peano
          apply Nat.succ_lt_succ
          exact ih_b' a' h_lt_peano

  theorem isomorfism_PeanoNat_Nat_Le (a b: PeanoNat) :
    Le a b ↔ (peano_to_nat a) ≤ (peano_to_nat b) := by
    constructor
    · -- Forward direction: Le a b → (peano_to_nat a) ≤ (peano_to_nat b)
      induction a generalizing b with
      | zero =>
        intro h_le -- h_le : Le zero b
        cases b with
        | zero => -- b = zero, h_le : Le zero zero
          -- Goal before simp: (peano_to_nat zero) ≤ (peano_to_nat zero)
          simp only [peano_to_nat] -- Goal after simp: 0 ≤ 0
          exact Nat.le_refl 0
        | succ b' => -- b = succ b', h_le : Le zero (succ b')
          -- Goal before simp: (peano_to_nat zero) ≤ (peano_to_nat (succ b'))
          simp only [peano_to_nat] -- Goal after simp: 0 ≤ Nat.succ (peano_to_nat b')
          exact Nat.zero_le (Nat.succ (peano_to_nat b'))
      | succ a' ih_a' =>
        intro h_le
        cases b with
        | zero =>
          -- Goal: (peano_to_nat (succ a')) ≤ (peano_to_nat zero)
          -- h_le is Le (succ a') zero, which implies succ a' = zero by le_n_zero_eq_zero.
          -- This contradicts succ_neq_zero a'.
          exact False.elim (PeanoNat.succ_neq_zero a' (PeanoNat.le_n_zero_eq_zero (succ a') h_le))
        | succ b' =>
          -- h_le : Le (succ a') (succ b')
          -- Goal: peano_to_nat (succ a') ≤ peano_to_nat (succ b')
          simp only [peano_to_nat]
          apply Nat.succ_le_succ_iff.mpr
          apply ih_a'
          exact PeanoNat.le_of_succ_le_succ h_le
    · -- Backward direction: (peano_to_nat a) ≤ (peano_to_nat b) → Le a b
      induction b generalizing a with
      | zero =>
        intro h_le
        cases a with
        | zero =>
          -- Goal: Le zero zero := by
          exact PeanoNat.le_refl zero
        | succ a' =>
          -- Goal: Le (succ a') zero (i.e., PeanoNat.Le (PeanoNat.succ a') PeanoNat.zero)
          -- h_le is (peano_to_nat (succ a')) ≤ (peano_to_nat zero), which simplifies to Nat.succ (peano_to_nat a') ≤ 0.
          -- This is impossible in Nat.
          exact False.elim ((Nat.not_succ_le_zero (peano_to_nat a')) h_le)
      | succ b' ih_b' =>
        intro h_le
        cases a with
        | zero =>
          -- Goal: Le zero (succ b') := by
          exact PeanoNat.le_zero (PeanoNat.succ b')
        | succ a' =>
          -- Goal: Le (succ a') (succ b')
          simp only [peano_to_nat] at h_le
          apply PeanoNat.le_succ_succ
          exact ih_b' a' (Nat.succ_le_succ_iff.mp h_le)

  theorem isomorfism_Nat_PeanoNat_Le (a b: Nat) :
    a ≤ b ↔ (nat_to_peano a) ≤ (nat_to_peano b) := by
    constructor
    · -- Forward direction: Le a b → (nat_to_peano a) ≤ (nat_to_peano b)
      induction a generalizing b with
      | zero =>
        intro h_le
        cases b with
        | zero =>
          -- Goal: Le zero zero := by
          exact PeanoNat.le_refl zero
        | succ b' =>
          -- Goal: PeanoNat.Le (nat_to_peano Nat.zero) (nat_to_peano (Nat.succ b'))
          -- This simplifies to PeanoNat.Le PeanoNat.zero (PeanoNat.succ (nat_to_peano b'))
          -- We use PeanoNat.le_zero, which proves `Le zero n` for any `n : PeanoNat`.
          -- Here, n is `nat_to_peano (Nat.succ b')`.
          exact PeanoNat.le_zero (nat_to_peano (Nat.succ b'))
      | succ a' ih_a' =>
        intro h_le
        cases b with
        | zero =>
          -- Goal: (nat_to_peano (Nat.succ a')) ≤ (nat_to_peano Nat.zero)
          -- h_le is Nat.le (Nat.succ a') Nat.zero. This is impossible.
          exact False.elim ((Nat.not_succ_le_zero a') h_le)
        | succ b' =>
          -- Goal: (nat_to_peano (succ a')) ≤ (nat_to_peano (succ b'))
          simp only [nat_to_peano]
          apply PeanoNat.le_succ_succ
          exact ih_a' b' (Nat.succ_le_succ_iff.mp h_le)
    · -- Backward direction: (nat_to_peano a) ≤ (nat_to_peano b) → Nat.le a b
      induction b generalizing a with
      | zero => -- b is Nat.zero
        intro h_le_peano -- h_le_peano : PeanoNat.Le (nat_to_peano a) (nat_to_peano Nat.zero)
        cases a with
        | zero => -- a is Nat.zero
          -- Goal: Nat.le Nat.zero Nat.zero
          exact Nat.le_refl Nat.zero
        | succ a' => -- a is Nat.succ a'
          -- Goal: Nat.le (Nat.succ a') Nat.zero
          -- h_le_peano is PeanoNat.Le (PeanoNat.succ (nat_to_peano a')) PeanoNat.zero
          have h_eq_zero : PeanoNat.succ (nat_to_peano a') = PeanoNat.zero :=
            PeanoNat.le_n_zero_eq_zero _ h_le_peano
          exact False.elim (PeanoNat.succ_neq_zero (nat_to_peano a') h_eq_zero)
      | succ b' ih_b' => -- b is Nat.succ b'
        intro h_le_peano -- h_le_peano : PeanoNat.Le (nat_to_peano a) (nat_to_peano (Nat.succ b'))
        cases a with
        | zero => -- a is Nat.zero
          -- Goal: Nat.le Nat.zero (Nat.succ b')
          exact Nat.zero_le (Nat.succ b')
        | succ a' => -- a is Nat.succ a'
          -- Goal: Nat.le (Nat.succ a') (Nat.succ b')
          -- h_le_peano is PeanoNat.Le (nat_to_peano (Nat.succ a')) (nat_to_peano (Nat.succ b'))
          apply Nat.succ_le_succ_iff.mpr -- Goal becomes Nat.le a' b'
          exact ih_b' a' (PeanoNat.le_of_succ_le_succ h_le_peano)

    theorem peano2nat_succ_comm (a: PeanoNat) :
      peano_to_nat (PeanoNat.succ a) = Nat.succ (peano_to_nat a) := by
      induction a with
      | zero => rfl
      | succ a' ih_a' =>
        simp only [peano_to_nat]

    def idnat(a: Nat) : Nat := a
    def idpeano(a: PeanoNat) : PeanoNat := a

    theorem idnat_eq_id_Nat (a: Nat) :
      idnat a = Nat.id a := by
      induction a with
      | zero => rfl
      | succ a' ih_a' =>
        simp only [idnat]
        rfl

    theorem idnat_eq_nat2peano_peano2nat (a : Nat) :
      idnat a = peano_to_nat (nat_to_peano a)
        := by
          calc
            idnat a = a := by
              unfold idnat
              rfl
            _ = (peano_to_nat ∘ nat_to_peano) a := by
              exact (nat2peano2nat_eq_idnat_by_elem a).symm

            -- Goal: a = peano_to_nat (nat_to_peano a)
            -- This is true since peano_to_nat (nat_to_peano a) = a
            -- by definition of peano_to_nat and nat_to_peano.

    theorem nat2peano_succ_comm (a: Nat) :
      nat_to_peano (Nat.succ a) = PeanoNat.succ (nat_to_peano a) := by
      induction a with
      | zero => rfl
      | succ a' ih_a' =>
        simp only [nat_to_peano]

    theorem idnat_through_peano (a: Nat) :
      Nat.succ a = peano_to_nat (PeanoNat.succ (nat_to_peano a)) := by
      induction a with
      | zero =>
        simp [nat_to_peano, peano_to_nat]
      | succ a' ih_a' =>
        -- Goal: Nat.succ (Nat.succ a') = peano_to_nat (PeanoNat.succ (nat_to_peano (Nat.succ a')))
        -- simp unfolds definitions and simplifies peano_to_nat(nat_to_peano x) to x.
        -- RHS becomes: peano_to_nat (PeanoNat.succ (PeanoNat.succ (nat_to_peano a')))
        -- which simplifies to Nat.succ (Nat.succ (nat_to_peano (nat_to_peano a')))
        -- which simplifies to Nat.succ (Nat.succ a')
        simp [nat_to_peano, peano_to_nat]


  theorem isomorfism_Nat_PeanoNat_add (a b: Nat) :
      Nat.add a b = peano_to_nat (add (nat_to_peano a) (nat_to_peano b)) := by
    induction b with
    | zero =>
      simp only [Nat.add_zero, nat_to_peano, PeanoNat.add_zero, peano_to_nat, nat2peano2nat_eq_idnat_by_elem]
    | succ b' ih =>
      simp only [Nat.add_succ, nat_to_peano, PeanoNat.add_succ, peano_to_nat, nat2peano_succ_comm, peano2nat_succ_comm, ih]

  theorem isomorfism_PeanoNat_Nat_add (a b: PeanoNat) :
      peano_to_nat (PeanoNat.add a b) = Nat.add (peano_to_nat a) (peano_to_nat b) := by
    induction b with
    | zero =>
      simp only [PeanoNat.add_zero, peano_to_nat, Nat.add_zero]
    | succ b' ih =>
      simp only [PeanoNat.add_succ, peano2nat_succ_comm, Nat.add_succ, ih]

  theorem isomorfism_PeanoNat_Nat_mul (a b: PeanoNat) :
      peano_to_nat (PeanoNat.mul a b) = Nat.mul (peano_to_nat a) (peano_to_nat b) := by
    induction b with
    | zero =>
      simp only [PeanoNat.mul_zero, peano_to_nat, Nat.mul_zero]
    | succ b' ih =>
      simp only [PeanoNat.mul_succ, peano2nat_succ_comm, Nat.mul_succ, isomorfism_PeanoNat_Nat_add, ih]

  theorem nat_to_peano_add_distrib (x y : Nat) :
    nat_to_peano (Nat.add x y) = PeanoNat.add (nat_to_peano x) (nat_to_peano y) := by
    induction y with
    | zero => simp only [Nat.add_zero, nat_to_peano, PeanoNat.add_zero]
    | succ y' ih =>
      simp only [Nat.add_succ, nat2peano_succ_comm, PeanoNat.add_succ, ih]

  theorem isomorfism_Nat_PeanoNat_mul (a b: Nat) :
        PeanoNat.nat_to_peano (Nat.mul a b)
          =
        PeanoNat.mul
          (PeanoNat.nat_to_peano a)
          (PeanoNat.nat_to_peano b) := by
    induction b with
    | zero =>
      simp only [Nat.mul_zero, nat_to_peano, PeanoNat.mul_zero]
    | succ b' ih =>
      simp only [Nat.mul_succ, PeanoNat.mul_succ, nat2peano_succ_comm, nat_to_peano_add_distrib, ih]

  theorem isomorfism_PeanoNat_Nat_sub (a b: PeanoNat)  (h_le_b_a: b ≤ a) :
      peano_to_nat (substract a b h_le_b_a) = peano_to_nat a - peano_to_nat b := by
    revert a
    induction b with
    | zero =>
      intro a_val h_le_zero_a
      simp only [substract_zero, peano_to_nat, Nat.sub_zero]
    | succ b' ih_b' =>
      intro a_val h_le_succ_b_a
      cases a_val with
      | zero =>
        exact False.elim (PeanoNat.succ_neq_zero b' (PeanoNat.le_n_zero_eq_zero (succ b') h_le_succ_b_a))
      | succ a_val' =>
        have h_le_b_a' : Le b' a_val' := PeanoNat.le_of_succ_le_succ h_le_succ_b_a
        simp only [substract, peano2nat_succ_comm]
        rw [ih_b' a_val' h_le_b_a']
        rw [Nat.succ_sub_succ_eq_sub]


  -- theorem isomorfism_Nat_PeanoNat_sub (a b: Nat) (h_le_b_a : b ≤ a) :
  --     nat_to_peano (Nat.sub a b) =
  --       peano_to_nat (substract (nat_to_peano a) (nat_to_peano b)
  --         ((isomorfism_Nat_PeanoNat_Le b a).mp h_le_b_a)) :=
  --   by sorry

/-!
  END      ⟨ISOMOMORFISMOS ENTRE PEANONAT Y NAT DEL CORE DE LEAN4⟩
  !-/



  -- Teorema que relaciona Lt de PeanoNat con < de Nat via peano_to_nat
  -- Es crucial para que la instancia SizeOf funcione correctamente con `termination_by`
  -- cuando la relación de disminución original es PeanoNat.Lt.
  -- IGUAL QUE isomorfism_PeanoNat_Nat_Lt pero solo de un lado
  theorem lt_implies_peano_to_nat_lt (a b : PeanoNat) :
    Lt a b → peano_to_nat a < peano_to_nat b := by
    intro h_lt_ab
    induction a generalizing b with
    | zero => -- a = PeanoNat.zero
      cases b with
      | zero => -- b = PeanoNat.zero. Lt zero zero es False.
        simp [Lt] at h_lt_ab -- h_lt_ab se convierte en False, lo que cierra la meta.
      | succ b' => -- b = PeanoNat.succ b'. Lt zero (succ b') es True.
        change peano_to_nat PeanoNat.zero < peano_to_nat (PeanoNat.succ b')
        rw [peano_to_nat, peano_to_nat] -- Despliega las definiciones
        exact Nat.zero_lt_succ (peano_to_nat b')
    | succ a' ih_a' => -- a = PeanoNat.succ a'
      cases b with
      | zero => -- b = PeanoNat.zero. Lt (succ a') zero es False.
        simp [Lt] at h_lt_ab
      | succ b' => -- b = PeanoNat.succ b'.
        -- h_lt_ab es Lt (succ a') (succ b')
        -- El objetivo es peano_to_nat (succ a') < peano_to_nat (succ b')
        change peano_to_nat (PeanoNat.succ a') < peano_to_nat (PeanoNat.succ b')
        rw [peano_to_nat, peano_to_nat] -- Despliega para obtener Nat.succ (..) < Nat.succ (..)
        -- Ahora el objetivo es Nat.succ (peano_to_nat a') < Nat.succ (peano_to_nat b')
        -- La hipótesis h_lt_ab es Lt (succ a') (succ b'), que por definición de Lt es Lt a' b'
        apply Nat.succ_lt_succ_iff.mpr
        -- El nuevo objetivo es peano_to_nat a' < peano_to_nat b'
        -- La hipótesis h_lt_ab se puede simplificar a Lt a' b'
        have h_a'_lt_b' : Lt a' b' := by unfold Lt at h_lt_ab; exact h_lt_ab
        exact ih_a' b' h_a'_lt_b' -- Llamada recursiva (hipótesis inductiva)

  -- Instancia de SizeOf para PeanoNat, para ayudar con la comprobación de terminación.
  instance : SizeOf PeanoNat where
    sizeOf p := peano_to_nat p

  def substract_one_repeat -- Definición existente del usuario
    (n : PeanoNat) (h_le_1_n: one <= n) : PeanoNat :=
      match n with
      | zero =>
        have h_one_eq_zero : PeanoNat.one = PeanoNat.zero :=
          PeanoNat.le_n_zero_eq_zero PeanoNat.one h_le_1_n
        False.elim ((PeanoNat.succ_neq_zero PeanoNat.zero) h_one_eq_zero)
      | succ n' =>
        match n' with
        | zero => one
        | succ n'' =>
          match n'' with
          | zero => two
          | succ n_minus_2 =>
            match n_minus_2 with
            | zero => three
            | succ n_rec_arg =>
              add (substract_one_repeat
                      (succ n_rec_arg)
                      (le_one_add_one n_rec_arg)
                  ) three

  /-!***
  Función auxiliar para contar cuántas veces se puede restar `m` de `current_n`.
  Devuelve el cociente.
  `h_m_neq_0` es una prueba de que el divisor no es cero.
  La terminación está garantizada porque `current_n` disminuye en cada paso recursivo
  (probado por `sub_lt_self` y justificado por `lt_implies_peano_to_nat_lt`).
  ***!-/
  def count_subtractions_aux (current_n m : PeanoNat) (count_so_far : PeanoNat)
    (h_m_neq_0 : m ≠ PeanoNat.zero) : PeanoNat :=
    if h_n_lt_m : current_n < m then -- Si el dividendo actual es menor que el divisor
      count_so_far -- Se devuelve el cociente acumulado
    else
      -- En este punto, sabemos que ¬(current_n < m).
      -- Por tricotomía, esto implica m <= current_n.
      have h_m_le_current_n : Le m current_n := by
        cases trichotomy current_n m with
        | inl h_cn_lt_m => exact False.elim (h_n_lt_m h_cn_lt_m) -- Contradice h_n_lt_m
        | inr h_eq_or_gt =>
          cases h_eq_or_gt with
          | inl h_cn_eq_m => rw [h_cn_eq_m]; exact Le.refl_le -- Corregido: Le.refl_le sin argumento
          | inr h_m_lt_cn => exact Le.strict_lt h_m_lt_cn
      let next_n := substract current_n m h_m_le_current_n
      -- La llamada recursiva se hace con next_n.
      -- El teorema `sub_lt_self current_n m h_m_neq_0 h_m_le_current_n`
      -- prueba `Lt next_n current_n`.
      -- El teorema `lt_implies_peano_to_nat_lt next_n current_n (sub_lt_self ...)`
      -- prueba `peano_to_nat next_n < peano_to_nat current_n`.
      -- Esto es lo que `termination_by current_n` usa a través de `SizeOf`.
      count_subtractions_aux next_n m (succ count_so_far) h_m_neq_0
  termination_by current_n -- Especifica que la terminación depende de current_n
  decreasing_by -- Proporciona la prueba de que current_n disminuye
    simp_wf -- Simplifica el objetivo de la prueba de terminación
    -- El objetivo es: sizeOf next_n < sizeOf current_n
    -- que se traduce a: peano_to_nat next_n < peano_to_nat current_n
     /-- MEJOR apply isomorfism_PeanoNat_Nat_Lt.mp -/
    apply lt_implies_peano_to_nat_lt -- Usa el teorema que relaciona PeanoNat.Lt con Nat.<
    -- El nuevo objetivo es: Lt next_n current_n
    exact sub_lt_self current_n m h_m_neq_0 h_m_le_current_n -- Prueba que next_n < current_n

-- Ejemplos de #eval y otras funciones que el usuario tenía.
-- Estos pueden necesitar ajustes si las definiciones han cambiado o si dependen de funciones no mostradas aquí.
-- #eval substract_one_repeat five (le_one_add_one (pred five))
-- #eval substract_one_repeat four (le_one_add_one (pred four))
-- #eval substract_one_repeat three (le_one_add_one (pred three))
-- #eval substract_one_repeat two (le_one_add_one (pred two))
-- #eval substract_one_repeat one (le_one_add_one (pred one))

end PeanoNat

-- export PeanoNat (..) -- Si se desea exportar todo el namespace
