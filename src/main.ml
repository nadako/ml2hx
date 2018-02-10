open Printf
open Typedtree

let s_longident i =
	match Longident.flatten i with
	| ["int"] -> "Int"
	| ["string"] -> "String"
	| parts -> String.concat "." parts

let rec core_type t =
	match t.ctyp_desc with
	| Ttyp_any -> assert false
	| Ttyp_var _ -> assert false
	| Ttyp_arrow _ -> assert false
	| Ttyp_tuple _ -> assert false
	| Ttyp_constr (_,i,pl) -> (s_longident i.txt) ^ (if pl = [] then "" else sprintf "<%s>" (String.concat ", " (List.map core_type pl)))
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

let value_binding v =
	match v.vb_pat.pat_desc, v.vb_expr.exp_desc with
	| Tpat_var (_, name), Texp_function f ->
		sprintf "function %s(%s) return switch %s {}" name.txt f.param.name f.param.name
	| _ -> "TODO"

let structure_item item =
	match item.str_desc with
	| Tstr_type (_, dl) ->
		String.concat "\n\n" (List.map type_declaration dl)
	| Tstr_value (_, vl) ->
		String.concat "\n\n" (List.map value_binding vl)
	| _ -> "TODO"

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
