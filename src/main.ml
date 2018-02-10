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

let rec expression e =
	match e.exp_desc with
	| Texp_ident (path, ident, desc) -> Path.name path
	| Texp_constant c -> constant c
	| Texp_let _ -> "TODO: Texp_let"
	| Texp_function _ -> "TODO: Texp_function"
	| Texp_apply _ -> "TODO: Texp_apply"
	| Texp_match _ -> "TODO: Texp_match"
	| Texp_try _ -> "TODO: Texp_try"
	| Texp_tuple _ -> "TODO: Texp_tuple"
	| Texp_construct _ -> "TODO: Texp_construct"
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
	| Texp_field _ -> "TODO: Texp_field"
	| Texp_setfield _ -> "TODO: Texp_setfield"
	| Texp_array _ -> "TODO: Texp_array"
	| Texp_ifthenelse _ -> "TODO: Texp_ifthenelse"
	| Texp_sequence _ -> "TODO: Texp_sequence"
	| Texp_while _ -> "TODO: Texp_while"
	| Texp_for _ -> "TODO: Texp_for"
	| Texp_send _ -> "TODO: Texp_send"
	| Texp_new _ -> "TODO: Texp_new"
	| Texp_instvar _ -> "TODO: Texp_instvar"
	| Texp_setinstvar _ -> "TODO: Texp_setinstvar"
	| Texp_override _ -> "TODO: Texp_override"
	| Texp_letmodule _ -> "TODO: Texp_letmodule"
	| Texp_letexception _ -> "TODO: Texp_letexception"
	| Texp_assert _ -> "TODO: Texp_assert"
	| Texp_lazy _ -> "TODO: Texp_lazy"
	| Texp_object _ -> "TODO: Texp_object"
	| Texp_pack _ -> "TODO: Texp_pack"
	| Texp_unreachable -> "TODO: Texp_unreachable"
	| Texp_extension_constructor _ -> "TODO: Texp_extension_constructor"

let value_binding v =
	match v.vb_pat.pat_desc, v.vb_expr.exp_desc with
 	| Tpat_var (_, name), _ -> sprintf "var %s = %s;" name.txt (expression v.vb_expr)
	| _ -> failwith "TODO"

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
	| Tstr_class _ -> "TODO: Tstr_class"
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
