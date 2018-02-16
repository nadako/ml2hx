open Printf
let indent_string = "\t"

type field_kind =
	| FVar
	| FFinal

type type_hint =
	| TPath of string list * string * type_hint list
	| TAnonymous of (field_kind * string * type_hint) list
	| TFunction of type_hint list * type_hint
	| TTuple of type_hint list

type constant =
	| CString of string
	| CInt of int32
	| CFloat of string

type expr =
	| EIdent of string
	| EConst of constant
	| EBlock of expr list
	| EVar of string * type_hint option * expr
	| EIf of expr * expr * expr option
	| ECall of expr * expr list
	| EObjectDecl of (string * expr) list
	| EField of expr * string
	| EBinop of binop * expr * expr
	| EUnop of unop * expr
	| EFunction of func
	| ESwitch of expr * case list
	| ETry of expr * catch list
	| ETuple of expr list
	| ETupleAccess of expr * int
	| EWhile of expr * expr
	| EThrow of expr

and case = pattern * expr option * expr

and catch = string * type_hint * expr

and pattern =
	| PAny
	| PVar of string
	| PAlias of string * pattern
	| PTuple of pattern list
	| PEnumCtor of string * pattern list
	| PFields of (string * pattern) list
	| POr of pattern * pattern
	| PArray of pattern list
	| PConst of expr

and func = {
	args : (string * type_hint) list;
	ret : type_hint;
	expr : expr;
}

and binop =
	| OpAssign
	| OpEq
	| OpNeq
	| OpGt
	| OpGte
	| OpLt
	| OpLte
	| OpAnd
	| OpOr
	| OpAdd
	| OpSub
	| OpMul
	| OpDiv
	| OpMod
	| OpBitAnd
	| OpBitOr
	| OpBitXor
	| OpShiftLeft
	| OpShiftRight
	| OpShiftRightUnsigned

and unop =
	| OpNot
	| OpBitNeg
	| OpIncr
	| OpDecr

type type_decl = {
	td_name : string;
	td_kind : type_decl_kind;
}

and type_decl_kind =
	| TDEnum of (string * (string * type_hint) list) list
	| TDTypedef of type_hint
	| TDClass of class_field list

and class_field = {
	cf_name : string;
	cf_expr : expr;
}

let rec s_type_hint ?(format_anon=false) t  =
	match t with
	| TPath (sl, s, pl) ->
		(if sl = [] then s else (String.concat "." sl) ^ "." ^ s) ^
		(if pl = [] then "" else sprintf "<%s>" (String.concat ", " (List.map (fun t -> s_type_hint t) pl)))
	| TAnonymous fields ->
		let fields = List.map (fun (k,n,t) ->
			sprintf "%s %s:%s;" (match k with FVar -> "var" | FFinal -> "final") n (s_type_hint t)
		) fields in
		if format_anon then
			sprintf "{\n%s%s\n}" indent_string (String.concat ("\n" ^ indent_string) fields)
		else
			sprintf "{%s}" (String.concat " " fields)
	| TFunction (args,ret) ->
		(match args with
		| [t] -> sprintf "%s->%s" (s_type_hint t) (s_type_hint ret)
		| _ -> sprintf "(%s)->%s" (String.concat "," (List.map (fun t -> s_type_hint t) args)) (s_type_hint ret)
		)
	| _ ->
		assert false

let s_enum name ctors =
	let ctors = List.map (fun (n,args) ->
		if args = [] then n ^ ";"
		else sprintf "%s(%s);" n (String.concat "," (List.map (fun (n,t) -> sprintf "%s:%s" n (s_type_hint t)) args))
	) ctors in
	sprintf "enum %s {\n%s%s\n}" name indent_string (String.concat ("\n" ^ indent_string) ctors)

let s_typedef name t =
	sprintf "typedef %s = %s;" name (s_type_hint ~format_anon:true t)

let s_const = function
	| CString s -> sprintf "%S" s
	| CInt i -> sprintf "%ld" i
	| CFloat f -> f

let s_binop = function
	| OpAssign -> "="
	| OpEq -> "=="
	| OpNeq -> "!="
	| OpGt -> ">"
	| OpGte -> ">="
	| OpLt -> "<"
	| OpLte -> "<="
	| OpAnd -> "&&"
	| OpOr -> "||"
	| OpAdd -> "+"
	| OpSub -> "-"
	| OpMul -> "*"
	| OpDiv -> "/"
	| OpMod -> "%"
	| OpBitAnd -> "&"
	| OpBitOr -> "|"
	| OpBitXor -> "^"
	| OpShiftLeft -> "<<"
	| OpShiftRight -> ">>"
	| OpShiftRightUnsigned -> ">>>"

let s_unop = function
	| OpNot -> "!"
	| OpBitNeg -> "~"
	| OpIncr -> "++"
	| OpDecr -> "--"

let rec s_expr ind = function
	| EIdent s -> s
	| EConst c -> s_const c
	| EBlock el ->
		let ind2 = ind ^ indent_string in
		let el = List.map (fun e -> sprintf "%s%s;" ind2 (s_expr ind2 e)) el in
		sprintf "{\n%s\n%s}"(String.concat "\n" el) ind
	| EVar (n,t,e) ->
		let t = match t with None -> "" | Some t -> s_type_hint t in
		sprintf "var %s%s = %s" n t (s_expr ind e)
	| EField (e,f) -> (s_expr ind e) ^ "." ^ f
	| EIf (econd,ethen,None) ->
		sprintf "if (%s) %s" (s_expr ind econd) (s_expr ind ethen)
	| EIf (econd,ethen,Some eelse) ->
		sprintf "if (%s) %s else %s" (s_expr ind econd) (s_expr ind ethen) (s_expr ind eelse)
	| ECall (e, args) ->
		sprintf "%s(%s)" (s_expr ind e) (String.concat ", " (List.map (s_expr ind) args))
	| EBinop (op, a, b) ->
		sprintf "%s %s %s" (s_expr ind a) (s_binop op) (s_expr ind b)
	| EUnop (op, e) ->
		sprintf "%s(%s)" (s_unop op) (s_expr ind e)
	| EObjectDecl fl ->
		let ind2 = ind ^ indent_string in
		let fl = List.map (fun (n,e) -> sprintf "%s%s: %s," ind2 n (s_expr ind2 e)) fl in
		sprintf "{\n%s\n%s}" (String.concat "\n" fl) ind
	| EFunction f ->
		let args = List.map (fun (n,t) ->
			sprintf "%s:%s" n (s_type_hint t)
		) f.args in
		sprintf "function(%s):%s return %s" (String.concat ", " args) (s_type_hint f.ret) (s_expr ind f.expr)
	| ESwitch (e,cases) ->
		let ind2 = ind ^ indent_string in
		let cases = List.map (fun (pat,guard,e) ->
			let guard = match guard with None -> "" | Some e -> sprintf " if (%s)" (s_expr ind e) in
			sprintf "%scase %s%s: %s;" ind2 (s_pattern pat) guard (s_expr ind2 e)
		) cases in
		sprintf "switch %s {\n%s\n%s}" (s_expr ind e) (String.concat "\n" cases) ind
	| ETuple el ->
		let i = ref 0 in
		let fl = List.map (fun e ->
			let n = (let n = sprintf "_%d" !i in incr i; n) in
			n,e
		) el in
		s_expr ind (EObjectDecl fl)
	| ETupleAccess (e,n) ->
		s_expr ind (EField (e, sprintf "_%d" n))
	| EThrow e -> "throw " ^ (s_expr ind e)
	| EWhile (cond,body) ->
		sprintf "while (%s) %s" (s_expr ind cond) (s_expr ind body)
	| ETry (body,catches) ->
		sprintf "try %s catch (TODO) {}" (s_expr ind body)

and s_pattern = function
	| PAny -> "_"
	| PVar s -> s
	| PAlias (n, p) -> sprintf "%s = %s" n (s_pattern p)
	| PTuple pl ->
		let i = ref 0 in
		let fl = List.map (fun p ->
			let n = (let n = sprintf "_%d" !i in incr i; n) in
			n,p
		) pl in
		s_pattern (PFields fl)
	| PFields fl ->
		let fl = List.map (fun (n,p) -> sprintf "%s: %s" n (s_pattern p)) fl in
		sprintf "{%s}" (String.concat ", " fl)
	| PEnumCtor (n,pl) ->
		if pl = [] then n
		else sprintf "%s(%s)" n (String.concat ", " (List.map s_pattern pl))
	| PArray pl -> sprintf "[%s]" (String.concat ", " (List.map s_pattern pl))
	| POr (a,b) -> sprintf "%s | %s" (s_pattern a) (s_pattern b)
	| PConst e -> s_expr "" e

let s_class name fl =
	let fields = List.map (fun f ->
		let indent2 = indent_string ^ indent_string in
		sprintf "%svar %s = {\n%s%s;\n%s}" indent_string f.cf_name indent2 (s_expr indent2 f.cf_expr) indent_string
	) fl in
	sprintf "class %s {\n%s\n}" name (String.concat "\n\n" fields)

let s_type_decl td =
	match td.td_kind with
	| TDEnum ctors -> s_enum td.td_name ctors
	| TDTypedef t -> s_typedef td.td_name t
	| TDClass fl -> s_class td.td_name fl
