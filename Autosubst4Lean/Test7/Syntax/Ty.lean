import Autosubst4Lean.Test7.Debruijn

namespace RefCalc

inductive Ty : Sig -> Type where
| unit : Ty s
| arrow : Ty s -> Ty s -> Ty s
| prod : Ty s -> Ty s -> Ty s
| ref : BVar s .lvar -> Ty s -> Ty s
| forallL : Ty (s,l) -> Ty s

def Ty.rename : Ty s1 -> Rename s1 s2 -> Ty s2
| .unit, _ => .unit
| .arrow a0 a1, f => .arrow (a0.rename f) (a1.rename f)
| .prod a0 a1, f => .prod (a0.rename f) (a1.rename f)
| .ref x0 a1, f => .ref (f.var x0) (a1.rename f)
| .forallL a0, f => .forallL (a0.rename f.lift)

theorem Ty.rename_id {t : Ty s} :
    t.rename (Rename.id) = t := by
  induction t
  case unit => rfl
  case arrow =>
    simp_all [Ty.rename]
  case prod =>
    simp_all [Ty.rename]
  case ref =>
    simp_all [Ty.rename, Rename.id]
  case forallL =>
    simp_all [Ty.rename, Rename.lift_id]

theorem Ty.rename_comp {t : Ty s1} {f : Rename s1 s2} {g : Rename s2 s3} :
    (t.rename f).rename g = t.rename (f.comp g) := by
  induction t generalizing s2 s3
  case unit => rfl
  case arrow =>
    simp_all [Ty.rename]
  case prod =>
    simp_all [Ty.rename]
  case ref =>
    simp_all [Ty.rename, Rename.comp]
  case forallL =>
    simp_all [Ty.rename, Rename.lift_comp]

end RefCalc
