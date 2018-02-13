open Printf
open Asttypes
open Types
open Typedtree

exception Error of Location.t * string

let error loc msg = raise (Error (loc, msg))

let istr = ref ""
let indent () =
	let old = !istr in
	istr := old ^ "\t";
	fun () -> istr := old

let with_ident f v =
	let unindent = indent () in
	let istr = !istr in
	let r = f v in
	unindent ();
	r, istr

let s_typepath path =
	match Path.name path with
	| "int" -> "Int"
	| "string" -> "String"
	| "unit" -> "Void"
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
	{
		exp_desc = Texp_let (Nonrecursive,bindings,expr);
		exp_loc = expr.exp_loc;
		exp_extra = [];
		exp_type = expr.exp_type;
		exp_env = expr.exp_env;
		exp_attributes = [];
	}

let rewrite_func f env loc =
	let rec loop args_acc let_acc (arg_label, param, cases, partial) =
		match cases with
		| [{ c_rhs = { exp_desc = Texp_function f} } as c] ->
			let args_acc = (arg_label, param, c.c_lhs.pat_type) :: args_acc in
			let let_acc = {
				vb_pat = c.c_lhs;
				vb_expr = mk_param_ident env param c.c_lhs.pat_type loc;
				vb_attributes = [];
				vb_loc = loc;
			} :: let_acc in
			loop args_acc let_acc (f.arg_label, f.param, f.cases, f.partial)
		| _ ->
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
			List.rev ((arg_label, param, c.c_lhs.pat_type) :: args_acc), c.c_rhs.exp_type, mk_lets (List.rev let_acc) expr
	in
	loop [] [] f

let rec type_expr t =
	match t.desc with
	| Tvar _ -> sprintf "TODO<\"Tvar\">"
	| Tarrow (Nolabel,a,b,_) -> sprintf "%s -> %s" (type_expr a) (type_expr b)
	| Tarrow _ -> sprintf "TODO<\"Tarrow\">"
	| Ttuple tl -> sprintf "Tuple%d<%s>" (List.length tl) (String.concat ", " (List.map type_expr tl))
	| Tconstr (path,pl,_) -> (s_typepath path) ^ (if pl = [] then "" else sprintf "<%s>" (String.concat ", " (List.map type_expr pl)))
	| Tobject _ -> sprintf "TODO<\"Tobject\">"
	| Tfield _ -> sprintf "TODO<\"Tfield\">"
	| Tnil -> sprintf "TODO<\"Tnil\">"
	| Tlink t -> type_expr t
	| Tsubst _ -> sprintf "TODO<\"Tsubst\">"
	| Tvariant _ -> sprintf "TODO<\"Tvariant\">"
	| Tunivar _ -> sprintf "TODO<\"Tunivar\">"
	| Tpoly (t,pl) -> (type_expr t) ^ (if pl = [] then "" else sprintf "<%s>" (String.concat ", " (List.map type_expr pl)))
	| Tpackage _ -> sprintf "TODO<\"Tpackage\">"

let core_type t = type_expr t.ctyp_type

let label_declaration l =
	let kw = if l.ld_mutable = Immutable then "final" else "var" in
	let t = core_type l.ld_type in
	sprintf "%s %s:%s;" kw l.ld_name.txt t

let type_declaration t =
	let name = t.typ_name.txt in
	match t.typ_kind with
	| Ttype_variant cl ->
		let ctors = List.map (fun c ->
			let name = c.cd_name.txt in
			let args = match c.cd_args with
			| Cstr_tuple tl ->
				let c = ref (Char.code 'a') in
				let args = List.map (fun t -> sprintf "%c:%s" (Char.chr !c) (core_type t)) tl in
				if args = [] then "" else sprintf "(%s)" (String.concat ", " args)
			| Cstr_record ll ->
				sprintf "(v:{ %s })" (String.concat " " (List.map label_declaration ll))
			in
			name ^ args
		) cl in
		sprintf "enum %s {\n\t%s\n}" name (String.concat "\n\t" ctors)
	| Ttype_record ll ->
		let fields = List.map label_declaration ll in
		sprintf "typedef %s = {\n\t%s\n}" name (String.concat "\n\t" fields)
	| Ttype_open -> failwith "TODO: Ttype_open"
	| Ttype_abstract ->
		match t.typ_manifest with
		| None -> failwith "TODO: Ttype_abstract"
		| Some t -> sprintf "typedef %s = %s;" name (core_type t)

let constant = function
	| Const_int v -> sprintf "%d" v
	| Const_char v -> sprintf "\"%c\".code" v
	| Const_string (v,_) -> sprintf "%S" v
	| Const_float v -> v
	| Const_int32 v -> sprintf "%ld" v
	| Const_int64 v -> sprintf "%Ld /*TODO: int64*/" v
	| Const_nativeint v -> sprintf "%nd /*TODO: nativeint*/" v

let rec pattern p =
	match p.pat_desc with
	| Tpat_any -> "_"
	| Tpat_var (_, n) -> n.txt
	| Tpat_alias (pat,_,n) -> sprintf "%s = (%s)" n.txt (pattern pat)
	| Tpat_constant c -> constant c
	| Tpat_tuple pl ->
		let i = ref 0 in
		let fields = List.map (fun p ->
			let s = sprintf "_%d: %s" !i (pattern p) in
			incr i;
			s
		) pl in
		sprintf "{ %s }" (String.concat ", " fields)
	| Tpat_construct (_,ctor,pl) ->
		if pl = [] then
			if ctor.cstr_name = "()" then "null /* TODO: unit? */"
			else ctor.cstr_name
		else
			sprintf "%s(%s)" ctor.cstr_name (String.concat ", " (List.map pattern pl))
	| Tpat_variant _ -> failwith "polymorphic variants are unsupported"
	| Tpat_record (fields,_) ->
		let fields = List.map (fun (_,l,p) -> sprintf "%s: %s" (l.lbl_name) (pattern p)) fields in
		sprintf "{ %s }" (String.concat ", " fields)
	| Tpat_array pl -> sprintf "[ %s ]" (String.concat ", " (List.map pattern pl))
	| Tpat_or (a,b,_) -> sprintf "%s | %s" (pattern a) (pattern b)
	| Tpat_lazy _ -> failwith "lazy patterns are unsupported"

let rec expression e =
	match e.exp_desc with
	| Texp_ident (path, ident, desc) -> Path.name path
	| Texp_constant c -> constant c
	| Texp_let (_,bindings,expr) ->
		let parts = List.map value_binding bindings in
		let parts = parts @ [expression expr] in
		String.concat ("\n" ^ !istr) parts
	| Texp_function f -> texp_function (f.arg_label, f.param, f.cases, f.partial) e.exp_env e.exp_loc
	| Texp_apply (e, args) ->
		(* TODO: handle partial application using .bind *)
		let args = List.map (fun (l, e2) ->
			if l <> Nolabel then error e.exp_loc "Labeled arguments are not yet supported";
			match e2 with
			| None -> failwith "Arguments without expression are not yet supported";
			| Some e -> expression e
		) args in
		sprintf "%s(%s)" (expression e) (String.concat ", " args)
	| Texp_match (expr,cases,exccases,partial) ->
		if exccases <> [] then failwith "exception match is not supported";
		switch (expression expr) cases partial
	| Texp_try (e,cases) ->
		let e,i = with_ident expression e in
		let catches = List.map (fun c ->
			let body,i = with_ident expression c.c_rhs in
			sprintf "%scatch (TODO)\n%s%s" !istr i body
		) cases in
		sprintf "try\n%s%s\n%s" i e (String.concat "\n" catches)
	| Texp_tuple exprs ->
		let i = ref 0 in
		let fields = List.map (fun e ->
			let s = sprintf "_%d: %s" !i (expression e) in
			incr i;
			s
		) exprs in
		sprintf "{ %s }" (String.concat ", " fields)
	| Texp_construct (_,ctor,args) ->
		if args = [] then (
			if ctor.cstr_name = "()" then "null /* TODO: unit? */"
			else ctor.cstr_name
		) else
			sprintf "%s(%s)" ctor.cstr_name (String.concat ", " (List.map expression args))
	| Texp_variant _ -> "TODO: Texp_variant"
	| Texp_record { fields = fields; extended_expression = extends } ->
		let fields = Array.to_list fields in
		(match extends with
		| None ->
			let fields = List.map (fun (d,r) ->
				let v = match r with
					| Kept _ -> assert false
					| Overridden (_,e) -> expression e
				in
				sprintf "%s: %s" d.lbl_name v
			) fields in
			sprintf "{ %s }" (String.concat ", " fields)
		| Some expr ->
			let fields = List.map (fun (d,r) ->
				let v = match r with
					| Kept _ -> sprintf "__obj.%s" d.lbl_name
					| Overridden (_,e) -> expression e
				in
				sprintf "%s: %s" d.lbl_name v
			) fields in
			sprintf "{ var __obj = %s; { %s } }" (expression expr) (String.concat ", " fields)
		)
	| Texp_field (eobj,_,label) ->
		sprintf "%s.%s" (expression eobj) label.lbl_name
	| Texp_setfield (eobj,_,label,evalue) ->
		sprintf "%s.%s = %s" (expression eobj) label.lbl_name (expression evalue)
	| Texp_array _ -> "TODO: Texp_array"
	| Texp_ifthenelse (econd,ethen,None) ->
		sprintf "if (%s) %s" (expression econd) (expression ethen)
	| Texp_ifthenelse (econd,ethen,Some eelse) ->
		sprintf "if (%s) %s else %s" (expression econd) (expression ethen) (expression eelse)
	| Texp_sequence (a,b) -> sprintf "%s; %s" (expression a) (expression b)
	| Texp_while (econd,ebody) -> sprintf "while (%s) %s" (expression econd) (expression ebody)
	| Texp_for _ -> "TODO: Texp_for"
	| Texp_send _ -> "TODO: Texp_send"
	| Texp_new _ -> "TODO: Texp_new"
	| Texp_instvar _ -> "TODO: Texp_instvar"
	| Texp_setinstvar _ -> "TODO: Texp_setinstvar"
	| Texp_override _ -> "TODO: Texp_override"
	| Texp_letmodule _ -> "TODO: Texp_letmodule"
	| Texp_letexception _ -> "TODO: Texp_letexception"
	| Texp_assert expr -> sprintf "assert(%s)" (expression expr)
	| Texp_lazy _ -> "TODO: Texp_lazy"
	| Texp_object _ -> "TODO: Texp_object"
	| Texp_pack _ -> "TODO: Texp_pack"
	| Texp_unreachable -> "TODO: Texp_unreachable"
	| Texp_extension_constructor _ -> "TODO: Texp_extension_constructor"

and switch sexpr cases partial =
	let case c =
		let pattern = pattern c.c_lhs in
		let guard = match c.c_guard with None -> "" | Some e -> sprintf " if (%s)" (expression e) in
		let unindent = indent () in
		let e = expression c.c_rhs in
		let r = sprintf "case %s%s:\n%s%s;" pattern guard !istr e in
		unindent ();
		r
	in
	let unindent = indent () in
	let ind = !istr in
	let cases = List.map case cases in
	unindent ();
	let cases = if partial = Partial then cases @ ["case _: throw \"match failure\";"] else cases in
	sprintf "switch %s {\n%s%s\n%s}" sexpr ind (String.concat ("\n" ^ ind) cases) !istr

and texp_function f env loc =
	let args, ret_type, expr = rewrite_func f env loc in
	let args = List.map (fun (label, param, t) ->
		assert (label = Nolabel);
		sprintf "%s:%s" (Ident.name param) (type_expr t)
	) args in
	let ret_type = type_expr ret_type in
	sprintf "function(%s):%s return %s" (String.concat ", " args) ret_type (expression expr)

and value_binding v =
	match v.vb_pat.pat_desc, v.vb_expr.exp_desc with
 	| Tpat_var (_, name), _ -> sprintf "var %s = %s;" name.txt (expression v.vb_expr)
	| _ -> failwith "TODO"

let class_declaration (c,pub_methods) =
	"TODO: class_declaration"

let structure_item item =
	match item.str_desc with
	| Tstr_type (_, dl) ->
		String.concat "\n\n" (List.map type_declaration dl)
	| Tstr_value (_, vl) ->
		String.concat "\n\n" (List.map value_binding vl)
	| Tstr_eval _ -> "TODO: Tstr_eval"
	| Tstr_primitive _ -> "TODO: Tstr_primitive"
	| Tstr_typext _ -> "TODO: Tstr_typext"
	| Tstr_exception _ -> "TODO: Tstr_exception"
	| Tstr_module _ -> "TODO: Tstr_module"
	| Tstr_recmodule _ -> "TODO: Tstr_recmodule"
	| Tstr_modtype _ -> "TODO: Tstr_modtype"
	| Tstr_open _ -> "TODO: Tstr_open"
	| Tstr_class (cl) ->
		String.concat "\n\n" (List.map class_declaration cl)
	| Tstr_class_type _ -> "TODO: Tstr_class_type"
	| Tstr_include _ -> "TODO: Tstr_include"
	| Tstr_attribute _ -> "TODO: Tstr_attribute"


let implementation imp =
	String.concat "\n\n" (List.map structure_item imp.str_items)

let tool_name = "ml2hx"
let ppf = Format.err_formatter

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
	let out =
		try
			let ast = Pparse.parse_implementation ppf ~tool_name filename in
			let typedtree, _ = Typemod.type_implementation filename outputprefix modulename env ast in
			(* Printtyped.implementation ppf typedtree; *)
			implementation typedtree
		with x ->
			Location.report_exception ppf x;
			exit 2
	in
	let f = open_out (modulename ^ ".hx") in
	output_string f out;
	close_out f

let _ = main ()
