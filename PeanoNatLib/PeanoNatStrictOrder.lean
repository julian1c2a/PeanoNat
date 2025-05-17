import PeanoNatLib.PeanoNatAxioms


open PeanoNat
namespace PeanoNat


    def Lt (n m : ℕ₀) : Prop :=
        match n, m with
        | _    , zero       => False
        | zero , σ _        => True
        | σ n' , σ m'       => Lt n' m'
    instance : LT ℕ₀ := ⟨Lt⟩

    def BLt (n m : ℕ₀) : Bool :=
        match n, m with
        | _    , zero       => false
        | zero , σ _        => true
        | σ n' , σ m'       => BLt n' m'

    theorem BLt_iff_Lt (n m : ℕ₀) :
        BLt n m = true ↔ n < m
        := by
        induction n with
        | zero =>
            induction m with
            | zero =>
              calc (BLt zero zero = true)
                _ ↔ (false = true)    := by simp [BLt]
                _ ↔ False             := by simp
                _ ↔ (zero < zero)     := by simp [Lt]
            | σ m' =>
              calc (BLt zero (σ m') = true)
                _ ↔ (true = true)     := by simp [BLt]
                _ ↔ True              := by simp
                _ ↔ (zero < σ m')     := by simp [Lt]
        | σ n' =>
            induction m with
            | zero =>
              calc (BLt (σ n') zero = true)
                _ ↔ (false = true)    := by simp [BLt]
                _ ↔ False             := by simp
                _ ↔ (σ n' < zero)     := by simp [Lt]
            | σ m' =>
              simp [BLt, Lt, BLt_iff_Lt n' m']

    -- #eval σ 𝟎
    -- #eval σ 𝟏
    -- #eval σ 𝟐
    -- #eval σ 𝟑
    -- #eval σ 𝟒
    -- #eval σ 𝟓
    -- #eval σ 𝟔
    -- #eval σ 𝟕
    -- #eval σ 𝟖
    -- #eval σ 𝟗
    -- #eval σ 𝐀
    -- #eval σ 𝐁
    -- #eval σ 𝐂
    -- #eval σ 𝐃
    -- #eval σ 𝐄
    -- #eval σ 𝐅
    -- #eval σ 𝐆
    -- #eval σ 𝐇
    -- #eval σ 𝐈
    -- #eval σ 𝐉
    -- #eval σ 𝐊
    -- #eval σ 𝚪
    -- #eval σ 𝐌
    -- #eval σ 𝐍
    -- #eval σ 𝐎
    -- #eval σ 𝐏
    -- #eval σ 𝐐
    -- #eval σ 𝐑
    -- #eval σ 𝐒
    -- #eval σ 𝐓
    -- #eval σ 𝐔
    -- #eval σ 𝐕
    -- #eval σ 𝐖
    -- #eval σ 𝐗
    -- #eval σ 𝐘
    -- #eval σ 𝐙
    -- #eval σ 𝛂
    -- #eval σ 𝛃
    -- #eval σ 𝛄
    -- #eval σ 𝛅
    -- #eval σ 𝛆
    -- #eval σ 𝛇
    -- #eval σ 𝛈
    -- #eval σ 𝛉
    -- #eval σ 𝛊
    -- #eval σ 𝛋
    -- #eval σ 𝛌
    -- #eval σ 𝛍
    -- #eval σ 𝛏
    -- #eval σ 𝛚
    -- #eval σ 𝐚
    -- #eval σ 𝐛
    -- #eval σ 𝐜
    -- #eval σ 𝐝
    -- #eval σ 𝐞
    -- #eval σ 𝐟
    -- #eval σ 𝐠
    -- #eval σ 𝐡
    -- #eval σ 𝐣
    -- #eval σ 𝐤
    -- #eval σ 𝐦
    -- #eval σ 𝐧
    -- #eval σ 𝐩
    -- #eval σ 𝐪
    -- #eval σ 𝐫
    -- #eval σ 𝐬





end PeanoNat
