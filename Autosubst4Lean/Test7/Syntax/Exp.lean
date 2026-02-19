import Autosubst4Lean.Test7.Debruijn
import Autosubst4Lean.Test7.Syntax.Ty

namespace RefCalc

inductive Exp : Sig -> Type where
| var : BVar s .var -> Exp s
| unit : Exp s
| pair : Exp s -> Exp s -> Exp s
| abs : Ty s -> Exp (s,x) -> Exp s
| labs : Exp (s,l) -> Exp s
| ret : Exp s -> Exp s
| bind : Exp s -> Exp (s,x) -> Exp s
| app : Exp s -> Exp s -> Exp s
| lapp : Exp s -> BVar s .lvar -> Exp s
| fst : Exp s -> Exp s
| snd : Exp s -> Exp s
| newrgn : Exp (s,l) -> Exp s
| read : BVar s .lvar -> Exp s -> Exp s
| write : BVar s .lvar -> Exp s -> Exp s -> Exp s
| alloc : BVar s .lvar -> Exp s -> Exp s

def Exp.rename : Exp s1 -> Rename s1 s2 -> Exp s2
| .var x0, f => .var (f.var x0)
| .unit, _ => .unit
| .pair a0 a1, f => .pair (a0.rename f) (a1.rename f)
| .abs a0 a1, f => .abs (a0.rename f) (a1.rename f.lift)
| .labs a0, f => .labs (a0.rename f.lift)
| .ret a0, f => .ret (a0.rename f)
| .bind a0 a1, f => .bind (a0.rename f) (a1.rename f.lift)
| .app a0 a1, f => .app (a0.rename f) (a1.rename f)
| .lapp a0 x1, f => .lapp (a0.rename f) (f.var x1)
| .fst a0, f => .fst (a0.rename f)
| .snd a0, f => .snd (a0.rename f)
| .newrgn a0, f => .newrgn (a0.rename f.lift)
| .read x0 a1, f => .read (f.var x0) (a1.rename f)
| .write x0 a1 a2, f => .write (f.var x0) (a1.rename f) (a2.rename f)
| .alloc x0 a1, f => .alloc (f.var x0) (a1.rename f)

theorem Exp.rename_id {t : Exp s} :
    t.rename (Rename.id) = t := by
  induction t
  case var => rfl
  case unit => rfl
  case pair =>
    simp_all [Exp.rename]
  case abs =>
    simp_all [Exp.rename, Ty.rename_id, Rename.lift_id]
  case labs =>
    simp_all [Exp.rename, Rename.lift_id]
  case ret =>
    simp_all [Exp.rename]
  case bind =>
    simp_all [Exp.rename, Rename.lift_id]
  case app =>
    simp_all [Exp.rename]
  case lapp =>
    simp_all [Exp.rename, Rename.id]
  case fst =>
    simp_all [Exp.rename]
  case snd =>
    simp_all [Exp.rename]
  case newrgn =>
    simp_all [Exp.rename, Rename.lift_id]
  case read =>
    simp_all [Exp.rename, Rename.id]
  case write =>
    simp_all [Exp.rename, Rename.id]
  case alloc =>
    simp_all [Exp.rename, Rename.id]

theorem Exp.rename_comp {t : Exp s1} {f : Rename s1 s2} {g : Rename s2 s3} :
    (t.rename f).rename g = t.rename (f.comp g) := by
  induction t generalizing s2 s3
  case var => rfl
  case unit => rfl
  case pair =>
    simp_all [Exp.rename]
  case abs =>
    simp_all [Exp.rename, Ty.rename_comp, Rename.lift_comp]
  case labs =>
    simp_all [Exp.rename, Rename.lift_comp]
  case ret =>
    simp_all [Exp.rename]
  case bind =>
    simp_all [Exp.rename, Rename.lift_comp]
  case app =>
    simp_all [Exp.rename]
  case lapp =>
    simp_all [Exp.rename, Rename.comp]
  case fst =>
    simp_all [Exp.rename]
  case snd =>
    simp_all [Exp.rename]
  case newrgn =>
    simp_all [Exp.rename, Rename.lift_comp]
  case read =>
    simp_all [Exp.rename, Rename.comp]
  case write =>
    simp_all [Exp.rename, Rename.comp]
  case alloc =>
    simp_all [Exp.rename, Rename.comp]

end RefCalc
