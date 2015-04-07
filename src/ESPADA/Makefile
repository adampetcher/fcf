
MODULES := TSet ESPADA_TSet ESPADA_TSet_Once_Games ESPADA_TSet_Once ESPADA_TSet_Secure SSE ESPADA_TSet_Correct_Once_Games ESPADA_TSet_Correct_Once ESPADA_TSet_Correct ESPADA_SSE_SKS ESPADA_SSE_SKS_Secure ESPADA_SSE_SKS_Secure_tacs

VS      := $(MODULES:%=%.v)

.PHONY: coq clean

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS)
	coq_makefile -I "../FCF" $(VS) -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq
