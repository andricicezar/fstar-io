module Common

open FStar.Exn

type maybe a = either a exn
