(** {1 Simply-typed lambda calculus} *)

(** {2 Type definitions} *)

type name =
  | Global of string
  | Local of int
  | Quote of int  (** Used when interpreting values as terms *)

type kind = Star

type typ = TInt | TArrow of typ * typ | TCode of typ

type info = HasKind of kind | HasType of typ

type context = (name * info) list

type inferrable_term =
  | Annot of checkable_term * typ
  | Bound of int
  | Free of name
  | App of inferrable_term * checkable_term
  | Int of int

and checkable_term = Inf of inferrable_term | Lam of checkable_term

type value = VNeutral of neutral | VLam of (value -> value) | VInt of int

and neutral = NFree of name | NApp of neutral * value

type env = value list

(** {2 Helpers} *)

let error format = Fmt.kstr Result.error format

(** {2 Constructors} *)

(** {3 Constructors: names} *)

let global n = Global n

let local i = Local i

let quote i = Quote i

(** {3 Constructors: types} *)

(* let global_ty n = TFree (global n) *)

(* let local_ty i = TFree (local i) *)

(* let quote_ty i = TFree (quote i) *)

let int_ty = TInt

let arrow_ty dom range = TArrow (dom, range)

let ( @-> ) = arrow_ty

(** {3 Constructors: terms} *)

let annot ct ty = Annot (ct, ty)

let bound i = Bound i

let free s = Inf (Free (Global s))

let app it ct = App (it, ct)

let ( <@ ) = app

let inf it = Inf it

let lam b = Lam b

(** {2 Printers} *)

(** {3 Printers: names} *)

let pp_name fmtr = function
  | Global s -> Fmt.pf fmtr "%s" s
  | Local i -> Fmt.pf fmtr "%d" i
  | Quote i -> Fmt.pf fmtr "'%d" i

(** {3 Printers: types} *)

let pp_kind fmtr Star = Fmt.pf fmtr "*"

let pp_fragile fragile fmtr ppf =
  if fragile then Fmt.pf fmtr "(%a)" ppf () else ppf fmtr ()

let rec pp_typ_aux fragile fmtr typ =
  match typ with
  | TInt -> Fmt.pf fmtr "int"
  | TArrow (dom, range) ->
      pp_fragile fragile fmtr @@ fun fmtr () ->
      Fmt.pf fmtr "%a -> %a" (pp_typ_aux true) dom (pp_typ_aux false) range
  | TCode ty -> Fmt.pf fmtr "code %a" (pp_typ_aux true) ty

let pp_typ fmtr typ = pp_typ_aux false fmtr typ

(** {3 Printers: terms} *)

let rec pp_inferrable fragile fmtr it =
  match it with
  | Annot (ct, ty) ->
      pp_fragile fragile fmtr @@ fun fmtr () ->
      Fmt.pf fmtr "%a : %a" (pp_checkable true) ct pp_typ ty
  | Bound i -> Fmt.pf fmtr "%d" i
  | Free n -> Fmt.pf fmtr "free(%a)" pp_name n
  | App (it, ct) ->
      Fmt.pf fmtr "%a %a" (pp_inferrable true) it (pp_checkable true) ct
  | Int i -> Fmt.pf fmtr "%d" i

and pp_checkable fragile fmtr ct =
  match ct with
  | Inf it -> pp_inferrable fragile fmtr it
  | Lam body ->
      pp_fragile fragile fmtr @@ fun fmtr () ->
      Fmt.pf fmtr "λ. %a" (pp_checkable fragile) body

let pp_inferrable fmtr it = pp_inferrable false fmtr it

let pp_checkable fmtr it = pp_checkable false fmtr it

(** {3 Printers: contexts} *)

let pp_info fmtr info =
  match info with
  | HasKind Star -> pp_kind fmtr Star
  | HasType ty -> pp_typ fmtr ty

let pp_context : context Fmt.t = Fmt.Dump.(list (pair pp_name pp_info))

(** {2 Evaluation} *)

let vapp (vf : value) (varg : value) =
  match vf with
  | VLam f -> f varg
  | VNeutral n -> VNeutral (NApp (n, varg))
  | VInt _ -> failwith "vapp: expected a function, got integer"

let rec eval_inferrable : inferrable_term -> value list -> value =
 fun inferrable_term env ->
  match inferrable_term with
  | Annot (checkable_term, _) -> eval_checkable checkable_term env
  | Bound i -> List.nth env i
  | Free n -> VNeutral (NFree n)
  | App (it, ct) -> vapp (eval_inferrable it env) (eval_checkable ct env)
  | Int i -> VInt i

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

let kind_eq Star Star = true

let rec typ_eq ty1 ty2 =
  match (ty1, ty2) with
  | (TInt, TInt) -> true
  | (TArrow (d1, r1), TArrow (d2, r2)) -> typ_eq d1 d2 && typ_eq r1 r2
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
  | Annot (ct, ty) -> Annot (subst_checkable i name ct, ty)
  | Bound j -> if i = j then name else it
  | Free _ -> it
  | App (it, ct) -> App (subst_inferrable i name it, subst_checkable i name ct)
  | Int _ -> it

let rec type_wf : context -> typ -> (unit, string) result =
 fun ctxt typ ->
  match typ with
  | TInt -> Result.ok ()
  | TArrow (dom, range) ->
      let* () = type_wf ctxt dom in
      type_wf ctxt range
  | TCode ty -> type_wf ctxt ty

let rec infer : int -> context -> inferrable_term -> (typ, string) result =
 fun depth ctxt inferrable_term ->
  match inferrable_term with
  | Annot (checkable_term, ty) ->
      let* () = type_wf ctxt ty in
      let* () = check depth ctxt checkable_term ty in
      Result.ok ty
  | Bound _ -> error "infer: unexpected bound variable"
  | Free n -> (
      match List.assoc_opt n ctxt with
      | Some (HasType ty) -> Result.ok ty
      | Some (HasKind _) ->
          error "%a is expected to have a type but instead has kind *" pp_name n
      | None ->
          error "infer: %a not found in context %a" pp_name n pp_context ctxt)
  | App (it, ct) -> (
      let* fty = infer depth ctxt it in
      match fty with
      | TArrow (dom, range) ->
          let* () = check depth ctxt ct dom in
          Result.ok range
      | _ -> error "infer: expected arrow type, got %a" pp_typ fty)
  | Int _ -> Result.ok TInt

and check : int -> context -> checkable_term -> typ -> (unit, string) result =
 fun depth ctxt checkable_term ty ->
  match (checkable_term, ty) with
  | (Inf it, _) ->
      let* ty' = infer depth ctxt it in
      if typ_eq ty ty' then Result.ok ()
      else error "Expected %a, got %a" pp_typ ty pp_typ ty'
  | (Lam ct, TArrow (dom, range)) ->
      check
        (depth + 1)
        ((Local depth, HasType dom) :: ctxt)
        (subst_checkable 0 (Free (Local depth)) ct)
        range
  | _ -> error "Incorrect type %a" pp_typ ty

let check0 term typ = check 0 [] term typ

let rec quote_value : int -> value -> checkable_term =
 fun depth value ->
  match value with
  | VNeutral n -> Inf (quote_neutral depth n)
  | VLam f -> Lam (quote_value (depth + 1) (f (VNeutral (NFree (Quote depth)))))
  | VInt i -> Inf (Int i)

and quote_neutral : int -> neutral -> inferrable_term =
 fun depth neutral ->
  match neutral with
  | NFree (Quote i) -> Bound (depth - i - 1)
  | NFree n -> Free n
  | NApp (n, v) -> App (quote_neutral depth n, quote_value depth v)
