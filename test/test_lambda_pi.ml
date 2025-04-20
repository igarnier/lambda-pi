open Lambda_pi.Stlc

let id' = lam (inf (bound 0))

let const' = lam (lam (inf (bound 1)))

let term1 = annot id' (global_ty "a" @-> global_ty "a") <@ free "y"

let term2 =
  annot
    const'
    ((global_ty "b" @-> global_ty "b")
    @-> global_ty "a" @-> global_ty "b" @-> global_ty "b")
  <@ id' <@ free "y"

let env1 = [(Global "y", HasType (global_ty "a")); (Global "a", HasKind Star)]

let env2 = [(Global "b", HasKind Star)] @ env1

let () =
  assert (eval_inferrable term1 [] |> quote_value 0 = Inf (Free (Global "y")))

let () =
  assert (eval_inferrable term2 [] |> quote_value 0 = Lam (Inf (Bound 0)))

let () = assert (infer 0 env1 term1 = Ok (global_ty "a"))

let () = assert (infer 0 env2 term2 = Ok (global_ty "b" @-> global_ty "b"))
