VFILES := Base.v Byte.v VM.v Token.v Ook.v AST.v IR.v MIR.v

build: Makefile.coq
	$(MAKE) -f Makefile.coq

clean::
	@if [ -e Makefile.coq ]; then $(MAKE) -f Makefile.coq cleanall; fi
	$(RM) -f Makefile.coq Makefile.coq.conf

Makefile.coq:
	coq_makefile -f _CoqProject -o Makefile.coq $(VFILES)

.PHONY: build clean

-include Makefile.coq
