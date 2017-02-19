.PHONY: coq
coq: Makefile.coq
	make -f Makefile.coq

Makefile.coq: Makefile _CoqProject
	coq_makefile -f _CoqProject  > $@

SORT_COQPROJECT = sed 's,[^/]*/,~&,g' | env LC_COLLATE=C sort | sed 's,~,,g'
.PHONY: update-_CoqProject
update-_CoqProject::
	(echo '-R src ""'; (git ls-files 'src/*.v' | $(SORT_COQPROJECT))) > _CoqProject

.PHONY: clean
clean:
	make -f Makefile.coq clean || true
	rm -f Makefile.coq || true
