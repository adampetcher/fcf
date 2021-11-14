.PHONY: coq
coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject  > $@
	
install: coq

SORT_COQPROJECT = sed 's,[^/]*/,~&,g' | env LC_COLLATE=C sort | sed 's,~,,g'
.PHONY: update-_CoqProject
update-_CoqProject::
	(echo '-R src ""'; (git ls-files 'src/*.v' | $(SORT_COQPROJECT))) > _CoqProject

.PHONY: clean
clean:
	$(MAKE) -f Makefile.coq clean || true
	rm -f Makefile.coq || true
