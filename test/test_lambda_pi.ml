open Lambda_pi.Stlc

let id' = lam (inf (bound 0))

let const' = lam (lam (inf (bound 1)))

let term1 = annot id' (int_ty @-> int_ty) <@ free "y"

let term2 =
  annot const' ((int_ty @-> int_ty) @-> int_ty @-> int_ty @-> int_ty)
  <@ id' <@ free "y"

let env1 = [(Global "y", HasType int_ty); (Global "a", HasKind Star)]

let env2 = [(Global "b", HasKind Star)] @ env1

let () =
  assert (eval_inferrable term1 [] |> quote_value 0 = Inf (Free (Global "y")))

let () =
  assert (eval_inferrable term2 [] |> quote_value 0 = Lam (Inf (Bound 0)))

let () = assert (infer 0 env1 term1 = Ok int_ty)

let () = assert (infer 0 env2 term2 = Ok (int_ty @-> int_ty))

open Lambda_pi.Meta_stlc

let eta =
  lam (bracket (lam (escape (inf (app (bound 1) (bracket (inf (bound 0))))))))

let expected_eta_type =
  (code int_ty @-> code int_ty) @-> code (int_ty @-> int_ty)

let () =
  match check 0 [] eta expected_eta_type with
  | Ok () -> Format.printf "success"
  | Error msg -> failwith msg

let test = app (annot eta expected_eta_type) (lam (bracket (inf (bound 0))))

let res = eval_inferrable ~stage:0 test []

let () = quote_value 0 res |> Format.printf "%a" pp_checkable
