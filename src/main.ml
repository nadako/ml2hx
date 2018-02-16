open Printf
open Asttypes
open Types
open Typedtree
open Path
open HaxeAst

exception Error of Location.t * string

let error loc msg = raise (Error (loc, msg))

let s_typepath path =
	match Path.name path with
	| "int" -> "Int"
	| "string" -> "String"
	| "bool" -> "Bool"
	| "unit" -> "Unit"
	| other -> other

let mk_param_ident env param t loc =
	let param_name = Ident.name param in
	let param_longident = { txt = Longident.Lident param_name; loc = loc} in
	{
			exp_desc = Texp_ident (Pident param, param_longident, {
				val_type = t;
				val_kind = Val_reg;
				val_loc = loc;
				val_attributes = [];
			});
			exp_loc = loc;
			exp_extra = [];
			exp_type = t;
			exp_env = env;
			exp_attributes = [];
	}

let mk_lets bindings expr =
	if bindings = [] then expr else
	{
		exp_desc = Texp_let (Nonrecursive,bindings,expr);
		exp_loc = expr.exp_loc;
		exp_extra = [];
		exp_type = expr.exp_type;
		exp_env = expr.exp_env;
		exp_attributes = [];
	}

(*
	Functions are represented in OCaml differently than in Haxe:
	 * they are always curried, meaning function always take single argument, so multi-arg functions are really nested Texp_functions
	 * functions always use pattern-matching and can several cases

	We traverse the function and rewrite it so:
	 * argument patterns become let bindings (since haxe doesn't support patterns in arguments)
	 * multiple cases become a match expression

	In the end this function returns a list of flattened arguments, return type and a modified expression so one
	can construct Haxe-looking function from this.
*)
let rewrite_func f env loc =
	let rec loop args_acc let_acc (arg_label, param, cases, partial) =
		match cases with
		| [c] -> (* single-case function - most common *)
			let let_acc = {
				vb_pat = c.c_lhs;
				vb_expr = mk_param_ident env param c.c_lhs.pat_type loc;
				vb_attributes = [];
				vb_loc = loc;
			} :: let_acc in
			(match c with
			| { c_rhs = { exp_desc = Texp_function f} } -> (* curried function - collect args until we get some real expression *)
				loop ((arg_label, param, c.c_lhs.pat_type) :: args_acc) let_acc (f.arg_label, f.param, f.cases, f.partial)
			| _ -> (* actual function body after flattening curried functions  \o/ *)
				(arg_label, param, c.c_lhs.pat_type) :: args_acc, c.c_rhs.exp_type, let_acc, c.c_rhs)
		| _ -> (* multi-case function - transform into single-case + match *)
			let c = List.hd cases in
			let param_ident = mk_param_ident env param c.c_lhs.pat_type loc in
			let expr = {
				exp_desc = Texp_match (param_ident, cases, [], partial);
				exp_loc = loc;
				exp_extra = [];
				exp_type = c.c_rhs.exp_type;
				exp_env = env;
				exp_attributes = [];
			} in
			(arg_label, param, c.c_lhs.pat_type) :: args_acc, c.c_rhs.exp_type, let_acc, expr
	in
	let args, t, lets, expr = loop [] [] f in
	List.rev args, t, mk_lets (List.rev lets) expr

let rec follow t =
	match t.desc with
	| Tlink t -> follow t
	| _ -> t

let rec type_expr t =
	let t = follow t in
	match t.desc with
	| Tvar _ -> TPath ([], "T" ^ (string_of_int t.id), [])
	| Tarrow (_,a,b,_) ->
		let rec loop acc t =
			let t = follow t in
			match t.desc with
			| Tarrow (_,a,b,_) -> loop (a :: acc) b
			| _ -> TFunction (List.map type_expr (List.rev acc), type_expr t)
		in
		loop [a] b
	| Ttuple tl -> TTuple (List.map type_expr tl)
	| Tconstr (path,pl,_) -> TPath ([], s_typepath path, List.map type_expr pl)
	| Tobject _ -> failwith "Tobject"
	| Tfield _ -> failwith "Tfield"
	| Tnil -> failwith "Tnil"
	| Tlink _ -> assert false
	| Tsubst _ -> failwith "Tsubst"
	| Tvariant _ -> failwith "Tvariant"
	| Tunivar _ -> failwith "Tunivar"
	| Tpoly (t,pl) -> type_expr t (* TODO *)
	| Tpackage _ -> failwith "Tpackage"

let core_type t = type_expr t.ctyp_type

let mk_structure label_declarations =
	let fields = List.map (fun l ->
		(match l.ld_mutable with Immutable -> FFinal | Mutable -> FVar),
		l.ld_name.txt,
		core_type l.ld_type
	) label_declarations in
	TAnonymous fields

let type_declaration t =
	let name = t.typ_name.txt in
	let kind =
		match t.typ_kind with
		| Ttype_variant cl ->
			let ctors = List.map (fun c ->
				let name = c.cd_name.txt in
				let args =
					match c.cd_args with
					| Cstr_tuple tl ->
						let c = ref (Char.code 'a') in
						List.map (fun t -> String.make 1 (Char.chr !c), core_type t) tl
					| Cstr_record ll ->
						[("v", mk_structure ll)]
				in
				name, args
			) cl in
			TDEnum ctors
		| Ttype_record ll ->
			TDTypedef (mk_structure ll)
		| Ttype_open ->
			failwith "TODO: Ttype_open"
		| Ttype_abstract ->
			match t.typ_manifest with
			| None -> failwith "TODO: Ttype_abstract"
			| Some t -> TDTypedef (core_type t)
	in
	{ td_name = name; td_kind = kind }

let constant = function
	| Const_int v -> EConst (CInt (Int32.of_int v))
	| Const_char v -> EField (EConst (CString (String.make 1 v)), "code")
	| Const_string (v,_) -> EConst (CString v)
	| Const_float v -> EConst (CFloat v)
	| Const_int32 v -> EConst (CInt v)
	| Const_int64 v -> failwith "TODO: Const_int64"
	| Const_nativeint v -> failwith "TODO: Const_nativeint"

let rec pattern p =
	match p.pat_desc with
	| Tpat_any -> PAny
	| Tpat_var (_, n) -> PVar n.txt
	| Tpat_alias (pat,_,n) -> PAlias (n.txt, pattern pat)
	| Tpat_constant c -> PConst (constant c)
	| Tpat_tuple pl -> PTuple (List.map pattern pl)
	| Tpat_construct (_,ctor,pl) -> PEnumCtor (ctor.cstr_name, List.map pattern pl)
	| Tpat_variant _ -> failwith "TODO: Tpat_variant"
	| Tpat_record (fields,_) -> PFields (List.map (fun (_,l,p) -> l.lbl_name, pattern p) fields)
	| Tpat_array pl -> PArray (List.map pattern pl)
	| Tpat_or (a,b,_) -> POr (pattern a, pattern b)
	| Tpat_lazy _ -> failwith "TODO: Tpat_lazy"

let rec mk_ident p = match p with
	| Pident i -> EIdent i.name
	| Pdot (p,f,_) -> EField (mk_ident p, f)
	| Papply _ -> assert false

let rec expression e =
	let inner e =
		match e.exp_desc with
		| Texp_ident (path, ident, desc) -> mk_ident path
		| Texp_constant c -> constant c
		| Texp_let (_,bindings,expr) ->
			(match value_bindings bindings with
			| [] ->
				expression expr
			| parts ->
				let tail = match expression expr with
					| EBlock el -> el
					| e -> [ e ]
				in
				EBlock (parts @ tail);
			)
		| Texp_function f -> texp_function (f.arg_label, f.param, f.cases, f.partial) e.exp_env e.exp_loc
		| Texp_apply (e, args) ->
			texp_apply e args
		| Texp_match (expr,cases,exccases,partial) ->
			if exccases <> [] then failwith "exception match is not supported";
			switch (expression expr) cases partial
		| Texp_try (e,cases) ->
			let catches = List.map (fun c -> "TODO", TPath ([],"TODO",[]), expression c.c_rhs) cases in
			ETry (expression e, catches)
		| Texp_tuple exprs ->
			ETuple (List.map expression exprs)
		| Texp_construct (_,ctor,args) ->
			(match (follow e.exp_type).desc with
			| Tconstr (p, _, _) when Path.same p Predef.path_unit ->
				EIdent "Unit"
			| Tconstr (p, _, _) when Path.same p Predef.path_list ->
				(match ctor.cstr_name, args with
				| "[]", [] -> EIdent "Tl"
				| "::", [hd; tl] -> ECall (EIdent "Hd", [expression hd; expression tl])
				| _ -> assert false)
			| _ ->
				let ector = EIdent ctor.cstr_name in
				if args = [] then ector
				else ECall (ector, List.map expression args)
			)
		| Texp_variant _ -> failwith "TODO: Texp_variant"
		| Texp_record { fields = fields; extended_expression = extends } ->
			let fields = Array.to_list fields in
			(match extends with
			| None ->
				let fields = List.map (fun (d,r) ->
					let v = match r with
						| Kept _ -> assert false
						| Overridden (_,e) -> expression e
					in
					d.lbl_name, v
				) fields in
				EObjectDecl fields
			| Some expr ->
				let fields = List.map (fun (d,r) ->
					let v = match r with
						| Kept _ -> EField (EIdent "__obj", d.lbl_name)
						| Overridden (_,e) -> expression e
					in
					d.lbl_name, v
				) fields in
				EBlock [
					EVar ("__obj", None, expression expr);
					EObjectDecl fields;
				];
			)
		| Texp_field (eobj,_,label) ->
			EField (expression eobj, label.lbl_name)
		| Texp_setfield (eobj,_,label,evalue) ->
			EBinop (OpAssign, EField (expression eobj, label.lbl_name), expression evalue)
		| Texp_array _ -> failwith "TODO: Texp_array"
		| Texp_ifthenelse (econd,ethen,eelse) ->
			EIf (expression econd, expression ethen, match eelse with None -> None | Some e -> Some (expression e))
		| Texp_sequence _ -> assert false
		| Texp_while (econd,ebody) -> EWhile (expression econd, expression ebody)
		| Texp_for _ -> failwith "TODO: Texp_for"
		| Texp_send _ -> failwith "TODO: Texp_send"
		| Texp_new _ -> failwith "TODO: Texp_new"
		| Texp_instvar _ -> failwith "TODO: Texp_instvar"
		| Texp_setinstvar _ -> failwith "TODO: Texp_setinstvar"
		| Texp_override _ -> failwith "TODO: Texp_override"
		| Texp_letmodule _ -> failwith "TODO: Texp_letmodule"
		| Texp_letexception _ -> failwith "TODO: Texp_letexception"
		| Texp_assert expr -> ECall (EIdent "assert", [expression expr])
		| Texp_lazy _ -> failwith "TODO: Texp_lazy"
		| Texp_object _ -> failwith "TODO: Texp_object"
		| Texp_pack _ -> failwith "TODO: Texp_pack"
		| Texp_unreachable -> failwith "TODO: Texp_unreachable"
		| Texp_extension_constructor _ -> failwith "TODO: Texp_extension_constructor"
	in
	let rec loop acc e =
		match e.exp_desc with
		| Texp_sequence (a,b) ->
			loop (loop acc a) b
		| _ -> inner e :: acc
	in
	match loop [] e with
	| [e] -> e
	| el -> EBlock (List.rev el)

and switch sexpr cases partial =
	let cases = List.map (fun c ->
		let pattern = pattern c.c_lhs in
		let guard = match c.c_guard with None -> None | Some e -> Some (expression e) in
		let e = expression c.c_rhs in
		pattern, guard, e
	) cases in
	let cases =
		if partial = Partial then
			cases @ [(PAny, None, EThrow (EConst (CString "match failure")))]
		else
			cases
	in
	ESwitch (sexpr, cases)

and texp_function f env loc =
	let args, ret_type, expr = rewrite_func f env loc in
	let args = List.map (fun (label, param, t) ->
		assert (label = Nolabel);
		Ident.name param, type_expr t
	) args in
	EFunction {
		args = args;
		ret = type_expr ret_type;
		expr = expression expr;
	}

and texp_apply e args =
	let i = ref 0 in
	let args = List.map (fun (l, e2) ->
		if l <> Nolabel then error e.exp_loc "Labeled arguments are not yet supported";
		incr i;
		match e2 with
		| None -> failwith "Arguments without expression are not yet supported";
		| Some e -> expression e
	) args in
	let se = expression e in
	if !i = (Ctype.arity e.exp_type) then
		match se with
		| EField (EIdent "Pervasives", field) ->
			(match field, args with
			| "not", [e] -> EUnop (OpNot, e)
			| "&&", [a; b] -> EBinop (OpAnd, a, b)
			| "||", [a; b] -> EBinop (OpOr, a, b)
			| "==", [a; b] -> EBinop (OpEq, a, b)
			| "!=", [a; b] -> EBinop (OpNeq, a, b)
			| "=", [a; b] -> ECall (EIdent "structEq", [a; b])
			| "<>", [a; b] -> EUnop (OpNot, ECall (EIdent "structEq", [a; b]))

			| ">", [a; b] -> EBinop (OpGt, a, b)
			| "<", [a; b] -> EBinop (OpLt, a, b)
			| ">=", [a; b] -> EBinop (OpGte, a, b)
			| "<=", [a; b] -> EBinop (OpLte, a, b)

			| ("+" | "+."), [a; b] -> EBinop (OpAdd, a, b)
			| ("-" | "-."), [a; b] -> EBinop (OpSub, a, b)
			| ("*" | "*."), [a; b] -> EBinop (OpMul, a, b)
			| "/", [a; b] -> ECall (EField (EIdent "Std", "int"), [EBinop (OpDiv, a, b)])
			| "/.", [a; b] -> EBinop (OpDiv, a, b)
			| "**", [a; b] -> ECall (EField (EIdent "Math", "pow"), [a; b])
			| "mod", [a; b] -> EBinop (OpMod, a, b)
			| "land", [a; b] -> EBinop (OpBitAnd, a, b)
			| "lor", [a; b] -> EBinop (OpBitOr, a, b)
			| "lxor", [a; b] -> EBinop (OpBitXor, a, b)
			| "lnot", [e] -> EUnop (OpBitNeg, e)
			| "lsl", [a; b] -> EBinop (OpShiftLeft, a, b)
			| "asr", [a; b] -> EBinop (OpShiftRight, a, b)
			| "lsr", [a; b] -> EBinop (OpShiftRightUnsigned, a, b)
			| "^", [a; b] -> EBinop (OpAdd, a, b)

			| "fst", [e] -> ETupleAccess (e, 0)
			| "snd", [e] -> ETupleAccess (e, 1)

			(* TODO: analyze whether ref is not used outside of the function and use normal mutable var *)
			| "ref", [e] -> ECall (EIdent "ref", [e])
			| ":=", [a; b] -> EBinop (OpAssign, EField (a, "value"), b)
			| "!", [e] -> EField (e, "value")
			| "incr", [e] -> EUnop (OpIncr, (EField (e, "value")))
			| "decr", [e] -> EUnop (OpDecr, (EField (e, "value")))
			| _ -> ECall (se, args))
		| _ ->
			ECall (se, args)
	else
		ECall (EField (se,"bind"), args)

and value_binding v =
	match v.vb_pat.pat_desc with
	| Tpat_any -> None
	| Tpat_var (_, name) ->
		(match v.vb_expr.exp_desc with
		| Texp_ident (p,_,_) when Path.name p = name.txt -> None (* don't generate `var a = a` *)
		| _ -> Some (EVar (name.txt, None, (expression v.vb_expr)))
		)
	| Tpat_alias _ -> failwith "TODO: Tpat_alias"
	| Tpat_constant _ -> failwith "TODO: Tpat_constant"
	| Tpat_tuple _ -> failwith "TODO: Tpat_tuple"
	| Tpat_construct (_,ctor,pl) ->
		(match (follow v.vb_pat.pat_type).desc with
		| Tconstr (p, _, _) when Path.same p Predef.path_unit ->
			None
		| _ ->
			failwith "TODO: Tpat_construct")
	| Tpat_variant _ -> failwith "TODO: Tpat_variant"
	| Tpat_record _ -> failwith "TODO: Tpat_record"
	| Tpat_array _ -> failwith "TODO: Tpat_array"
	| Tpat_or _ -> failwith "TODO: Tpat_or"
	| Tpat_lazy _ -> failwith "TODO: Tpat_lazy"

and value_bindings vl =
	let vl = List.map value_binding vl in
	List.fold_left (fun acc v -> match v with
		| None -> acc
		| Some v -> v :: acc
	) [] vl

type structitem =
	| SType of type_decl
	| SExpr of expr

let structure_item item =
	match item.str_desc with
	| Tstr_type (_, dl) ->
		List.map (fun d -> SType (type_declaration d)) dl
	| Tstr_value (_, vl) ->
		List.map (fun v -> SExpr v) (value_bindings vl)
	| Tstr_eval _ -> failwith "TODO: Tstr_eval"
	| Tstr_primitive _ -> failwith "TODO: Tstr_primitive"
	| Tstr_typext _ -> failwith "TODO: Tstr_typext"
	| Tstr_exception _ -> failwith "TODO: Tstr_exception"
	| Tstr_module _ -> failwith "TODO: Tstr_module"
	| Tstr_recmodule _ -> failwith "TODO: Tstr_recmodule"
	| Tstr_modtype _ -> failwith "TODO: Tstr_modtype"
	| Tstr_open _ -> failwith "TODO: Tstr_open"
	| Tstr_class _ -> failwith "TODO: Tstr_class"
	| Tstr_class_type _ -> failwith "TODO: Tstr_class_type"
	| Tstr_include _ -> failwith "TODO: Tstr_include"
	| Tstr_attribute _ -> failwith "TODO: Tstr_attribute"


let implementation imp =
	let rec loop acc = function
		| [] -> acc
		| item :: rest ->
			structure_item item @ loop acc rest
	in
	loop [] imp.str_items

let tool_name = "ml2hx"
let ppf = Format.err_formatter

let mk_module_class items =
	let fields = List.map (fun e -> { cf_name = "_"; cf_expr = e }) items in
	{ td_name = "MODULE"; td_kind = TDClass fields }

let print_ast items =
	let decls, fields = List.fold_left (fun (decls, fields) item ->
		match item with
		| SType t -> t :: decls, fields
		| SExpr e -> decls, e :: fields
	) ([], []) items in
	let decls = if items = [] then decls else (mk_module_class (List.rev fields)) :: decls in
	String.concat "\n\n" (List.map s_type_decl (List.rev decls))

let main () =
	Clflags.color := Some Never;
	Location.register_error_of_exn (function
		| Error (loc,  err) -> Some (Location.error ~loc err)
		| _ -> None);

	(* sorry, i have no idea how to properly use Arg module *)
	let file = ref None in
	let anon s =
		if !file <> None then raise (Arg.Bad "file already specified");
		file := Some s;
	in
	let incl s = Clflags.include_dirs := s :: !Clflags.include_dirs in
	let filename =
		try
			Arg.parse [
				("-I", Arg.String incl, "Include directory")
			] anon "Usage: main.exe <file.ml>";
			match !file with Some f -> f | None -> raise (Arg.Bad "<file.ml> is required")
		with Arg.Bad msg -> begin
			prerr_endline msg;
			exit 2
		end
	in

	let outputprefix = Compenv.output_prefix filename in
	let modulename = Compenv.module_of_filename ppf filename outputprefix in
	Compmisc.init_path true;
	Env.set_unit_name modulename;
	let env = Compmisc.initial_env() in
	Compilenv.reset modulename;
	let items =
		try
			let ast = Pparse.parse_implementation ppf ~tool_name filename in
			let typedtree, _ = Typemod.type_implementation filename outputprefix modulename env ast in
			(* Printtyped.implementation ppf typedtree; *)
			implementation typedtree
		with x ->
			Location.report_exception ppf x;
			exit 2
	in
	let out = print_ast items in
	let f = open_out (modulename ^ ".hx") in
	output_string f out;
	close_out f

let _ = main ()
