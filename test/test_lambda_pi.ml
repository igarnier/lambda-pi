open Lambda_pi.Stlc

let const = lam (lam (inf (bound 1)))

let () =
  match
    check0
      const
      (arrow_ty (global_ty "a") (arrow_ty (global_ty "b") (global_ty "a")))
  with
  | Ok () -> ()
  | Error s -> failwith s
