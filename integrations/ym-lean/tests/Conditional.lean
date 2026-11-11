import YangMills.ExistenceOnly

/-! Negative control: merely assuming the full target must NOT pass
existence admission. This is not a proposed Yang--Mills proof. -/
universe u

theorem YMYMGControl.conditional
    (missingProof : YangMills.YangMillsExistenceOnly.{u}) :
    YangMills.YangMillsExistenceOnly.{u} := missingProof
