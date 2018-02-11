open Printf
open Asttypes
open Types
open Typedtree

let s_typepath path =
	match Path.name path with
	| "int" -> "Int"
	| "string" -> "String"
	| other -> other

let rec core_type t =
	match t.ctyp_desc with
	| Ttyp_any -> assert false
	| Ttyp_var _ -> assert false
	| Ttyp_arrow _ -> assert false
	| Ttyp_tuple _ -> assert false
	| Ttyp_constr (path,_,pl) -> (s_typepath path) ^ (if pl = [] then "" else sprintf "<%s>" (String.concat ", " (List.map core_type pl)))
	| Ttyp_object _ -> assert false
	| Ttyp_class _ -> assert false
	| Ttyp_alias _ -> assert false
	| Ttyp_variant _ -> assert false
	| Ttyp_poly (pl,t) -> (core_type t) ^ (if pl = [] then "" else sprintf "<%s>" (String.concat ", " pl))
	| Ttyp_package _ -> assert false

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
	| _ ->
		"TODO: " ^ name

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
			ctor.cstr_name
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
	| Texp_let _ -> "TODO: Texp_let"
	| Texp_function _ -> "TODO: Texp_function"
	| Texp_apply _ -> "TODO: Texp_apply"
	| Texp_match (expr,cases,exccases,partial) ->
		if exccases <> [] then failwith "exception match is not supported";
		let cases = List.map (fun c ->
			let pattern = pattern c.c_lhs in
			let guard = match c.c_guard with None -> "" | Some e -> sprintf " if (%s)" (expression e) in
			sprintf "\tcase %s%s: %s" pattern guard (expression c.c_rhs)
		) cases in
		sprintf "switch %s {\n%s\n}" (expression expr) (String.concat "\n" cases)
	| Texp_try _ -> "TODO: Texp_try"
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

let value_binding v =
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
	let filename = "test.ml" in
	let outputprefix = Compenv.output_prefix filename in
	let modulename = Compenv.module_of_filename ppf filename outputprefix in
	Compmisc.init_path true;
	Env.set_unit_name modulename;
	let env = Compmisc.initial_env() in
	Compilenv.reset modulename;
	let typedtree =
		try
			let ast = Pparse.parse_implementation ppf ~tool_name filename in
			let typedtree, _ = Typemod.type_implementation filename outputprefix modulename env ast in
			typedtree
		with x ->
			Location.report_exception ppf x;
			exit 2
	in
	let out = implementation typedtree in
	let f = open_out (modulename ^ ".hx") in
	output_string f out;
	close_out f

let _ = main ()
