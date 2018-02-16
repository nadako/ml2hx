SOURCES = src/haxeAst.ml src/main.ml
RESULT = main
PACKS = compiler-libs
LIBS = ocamlcommon ocamloptcomp
OCAMLFLAGS = -color never

all: byte-code
	./main.exe test.ml

-include OCamlMakefile
