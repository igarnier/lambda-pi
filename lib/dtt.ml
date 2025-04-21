(** {1 A dependent type theory} *)

(** {2 Type definitions} *)

type name = Global of string | Local of int | Quote of int

type inferrable_term =
  | Star
  | Pi of checkable_term * checkable_term
  | Annot of { e : checkable_term; typ : checkable_term }
  | Bound of int
  | Free of name
  | App of inferrable_term * checkable_term

and checkable_term = Inf of inferrable_term | Lam of checkable_term

type value =
  | VNeutral of neutral
  | VLam of (value -> value)
  | VStar
  | VPi of value * (value -> value)

and neutral = NFree of name | NApp of neutral * value

type context = (name * value) list

(** {2 Helpers} *)

let error format = Fmt.kstr Result.error format

(** {2 Constructors} *)

(** {3 Constructors: names} *)

let global n = Global n

let local i = Local i

let quote i = Quote i

(** {3 Constructors: terms and types} *)

let global_ty n = Free (global n)

let local_ty i = Free (local i)

let quote_ty i = Free (quote i)

let arrow_ty dom range = Pi (dom, range)

let ( @-> ) = arrow_ty

let pi dom body = Pi (dom, body)

let annot e typ = Annot { e; typ }

let bound i = Bound i

let free s = Inf (Free (Global s))

let app it ct = App (it, ct)

let ( <@ ) = app

let inf it = Inf it

let lam b = Lam b

(** {2 Quoting values back to terms} *)

let rec quote_value : int -> value -> checkable_term =
 fun depth value ->
  match value with
  | VStar -> Inf Star
  | VPi (vdom, f) ->
      Inf
        (Pi
           ( quote_value depth vdom,
             quote_value (depth + 1) (f (VNeutral (NFree (Quote depth)))) ))
  | VNeutral n -> Inf (quote_neutral depth n)
  | VLam f -> Lam (quote_value (depth + 1) (f (VNeutral (NFree (Quote depth)))))

and quote_neutral : int -> neutral -> inferrable_term =
 fun depth neutral ->
  match neutral with
  | NFree (Quote i) -> Bound (depth - i - 1)
  | NFree n -> Free n
  | NApp (n, v) -> App (quote_neutral depth n, quote_value depth v)

(** {2 Printers} *)

(** {3 Printers: names} *)

let pp_name fmtr = function
  | Global s -> Fmt.pf fmtr "%s" s
  | Local i -> Fmt.pf fmtr "%d" i
  | Quote i -> Fmt.pf fmtr "'%d" i

(** {3 Printers: terms and types} *)

let pp_fragile fragile fmtr ppf =
  if fragile then Fmt.pf fmtr "(%a)" ppf () else ppf fmtr ()

let rec pp_inferrable fragile fmtr it =
  match it with
  | Star -> Fmt.pf fmtr "*"
  | Annot { e; typ } ->
      pp_fragile fragile fmtr @@ fun fmtr () ->
      Fmt.pf fmtr "%a : %a" (pp_checkable true) e (pp_checkable true) typ
  | Pi (dom, range) ->
      pp_fragile fragile fmtr @@ fun fmtr () ->
      Fmt.pf fmtr "∀ %a . %a" (pp_checkable true) dom (pp_checkable true) range
  | Bound i -> Fmt.pf fmtr "%d" i
  | Free n -> Fmt.pf fmtr "free(%a)" pp_name n
  | App (it, ct) ->
      Fmt.pf fmtr "%a %a" (pp_inferrable true) it (pp_checkable true) ct

and pp_checkable fragile fmtr ct =
  match ct with
  | Inf it -> pp_inferrable fragile fmtr it
  | Lam body ->
      pp_fragile fragile fmtr @@ fun fmtr () ->
      Fmt.pf fmtr "λ. %a" (pp_checkable fragile) body

let pp_inferrable fmtr it = pp_inferrable false fmtr it

let pp_checkable fmtr it = pp_checkable false fmtr it

(** {3 Printers: values} *)

let pp_value fmtr v = pp_checkable fmtr (quote_value 0 v)

(** {3 Printers: contexts} *)

let pp_context : context Fmt.t = Fmt.Dump.(list (pair pp_name pp_value))

(** {2 Evaluation} *)

let vapp (vf : value) (varg : value) =
  match vf with
  | VLam f -> f varg
  | VPi (v, f) -> f v
  | VStar -> assert false
  | VNeutral n -> VNeutral (NApp (n, varg))

let rec eval_inferrable : inferrable_term -> value list -> value =
 fun inferrable_term env ->
  match inferrable_term with
  | Star -> VStar
  | Pi (ty, body) ->
      VPi (eval_checkable ty env, fun v -> eval_checkable body (v :: env))
  | Annot { e; typ = _ } -> eval_checkable e env
  | Bound i -> List.nth env i
  | Free n -> VNeutral (NFree n)
  | App (it, ct) -> vapp (eval_inferrable it env) (eval_checkable ct env)

and eval_checkable : checkable_term -> value list -> value =
 fun checkable_term env ->
  match checkable_term with
  | Inf it -> eval_inferrable it env
  | Lam ct -> VLam (fun v -> eval_checkable ct (v :: env))

(** {2 Typechecking} *)

let ( let* ) = Result.bind

let name_eq n1 n2 =
  match (n1, n2) with
  | (Global s1, Global s2) -> String.equal s1 s2
  | (Local i1, Local i2) -> Int.equal i1 i2
  | (Quote i1, Quote i2) -> Int.equal i1 i2
  | _ -> false

let rec subst_checkable :
    int -> inferrable_term -> checkable_term -> checkable_term =
 fun i name ct ->
  match ct with
  | Inf it -> Inf (subst_inferrable i name it)
  | Lam ct -> Lam (subst_checkable (i + 1) name ct)

and subst_inferrable :
    int -> inferrable_term -> inferrable_term -> inferrable_term =
 fun i name it ->
  match it with
  | Star -> Star
  | Annot { e; typ } ->
      Annot { e = subst_checkable i name e; typ = subst_checkable i name typ }
  | Pi (ty, body) ->
      Pi (subst_checkable i name ty, subst_checkable (i + 1) name body)
  | Bound j -> if i = j then name else it
  | Free _ -> it
  | App (it, ct) -> App (subst_inferrable i name it, subst_checkable i name ct)

let rec infer : int -> context -> inferrable_term -> (value, string) result =
 fun depth ctxt inferrable_term ->
  match inferrable_term with
  | Star -> Result.ok VStar
  | Pi (typ, body) ->
      (* Check that [typ] is a type *)
      let* () = check depth ctxt typ VStar in
      (* Normalize [typ] *)
      let typ_nf = eval_checkable typ [] in
      (* Substitute bound variable in [body] *)
      let body_subst = subst_checkable 0 (Free (Local depth)) body in
      (* Check that [body] is a type in extended context *)
      let* () =
        check (depth + 1) ((Local depth, typ_nf) :: ctxt) body_subst VStar
      in
      Result.ok VStar
  | Annot { e; typ } ->
      let* () = check depth ctxt typ VStar in
      (* [typ] is closed. All binding variables are substituted for free variables. *)
      let typ_nf = eval_checkable typ [] in
      let* () = check depth ctxt e typ_nf in
      Result.ok typ_nf
  | Bound _ -> error "infer: unexpected bound variable"
  | Free n -> (
      match List.assoc_opt n ctxt with
      | Some ty -> Result.ok ty
      | None ->
          error "infer: %a not found in context %a" pp_name n pp_context ctxt)
  | App (it, ct) -> (
      let* fty = infer depth ctxt it in
      match fty with
      | VPi (dom, range) ->
          let* () = check depth ctxt ct dom in
          let ct_nf = eval_checkable ct [] in
          Result.ok (range ct_nf)
      | _ -> error "infer: expected arrow type, got %a" pp_value fty)

and check : int -> context -> checkable_term -> value -> (unit, string) result =
 fun depth ctxt checkable_term vty ->
  match (checkable_term, vty) with
  | (Inf it, _) ->
      let* ty' = infer depth ctxt it in
      if quote_value 0 vty = quote_value 0 ty' then Result.ok ()
      else error "check: expected %a, got %a" pp_value vty pp_value ty'
  | (Lam ct, VPi (dom, range)) ->
      check
        (depth + 1)
        ((Local depth, dom) :: ctxt)
        (subst_checkable 0 (Free (Local depth)) ct)
        (range (VNeutral (NFree (Local depth))))
  | _ ->
      error
        "check: %a has incorrect type %a"
        pp_checkable
        checkable_term
        pp_value
        vty

let check0 term typ = check 0 [] term typ
