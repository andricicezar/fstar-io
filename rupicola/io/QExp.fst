module QExp

open FStar.Tactics
open QTyp

(** For now, it is just assumed. Check `SimpleQExp` to see a quotation of IO **)

assume type exp_quotation : #a:qType -> g:typ_env -> fs_oexp g a -> Type
