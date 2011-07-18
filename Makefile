
FILES= SfLib.v sva_ast.v sva_typing.v 

all: $(FILES:.v=.vo)

.SUFFIXES: .v .vo

.v.vo:
	@echo "COQC $*.v"
	@coqc -dump-glob doc/$(*F).glob $*.v

depend: $(FILES)
	coqdep -I . $(FILES) > .depend

clean:
	rm -f *.vo
	rm -f doc/*.glob