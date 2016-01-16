
MODULES := EqDec Limit Blist StdNat Rat Fold Comp DetSem DistSem DistRules DistTacs ProgTacs GenTacs Crypto SemEquiv ProgramLogic RndNat Bernoulli FCF HasDups CompFold RepeatCore PRF Array Encryption Asymptotic Admissibility RndInList OTP RndGrpElem GroupTheory WC_PolyTime RndListElem RndPerm NoDup_gen Hybrid OracleCompFold Encryption_PK DiffieHellman NotationV1 NotationV2 Tactics OracleHybrid

VS      := $(MODULES:%=%.v)

.PHONY: coq clean

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS)
	coq_makefile $(VS) -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq
