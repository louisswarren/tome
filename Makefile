MINTED=_minted.Decidable.gen _minted.Nat.gen _minted.List.gen _minted.Vec.gen _minted.Formula.gen _minted.Ensemble.gen _minted.Deduction.gen _minted.equivalence.gen _minted.Scheme.gen _minted.drinkerexample.gen _minted.no-ensemble.gen

MINTCODE='s/\\begin{code}/\\begin{minted}{agda}/; s/\\end{code}/\\end{minted}/'

tome.pdf: tome.tex introduction.tex $(MINTED) agda.sty tome.bbl
	xelatex -shell-escape tome.tex

tome.bbl: tome.tex introduction.tex $(MINTED) agda.sty bib.bib
	xelatex -shell-escape tome.tex
	bibtex tome

agda.sty:
	cp /usr/share/agda/agda.sty .

_minted.%.gen: %.lagda
	sed $(MINTCODE) $< > $@

.PHONY: clean
clean:
	rm -f *.agdai
	rm -f  *.gen agda.sty tome.aux tome.bbl tome.blg tome.log tome.pdf
	rm -f _minted-tome/*.pygtex _minted-tome/*.pygstyle
	rmdir _minted-tome

.PHONY: test
test:
	agda --safe appendix.agda
	agda --safe no-ensemble.lagda
	agda drinkerexample.lagda
	agda drinker.agda
