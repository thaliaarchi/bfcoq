build: Makefile.coq
	$(MAKE) -f Makefile.coq

clean::
	@if [ -e Makefile.coq ]; then $(MAKE) -f Makefile.coq cleanall; fi
	$(RM) -f Makefile.coq Makefile.coq.conf

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

.PHONY: build clean

-include Makefile.coq
