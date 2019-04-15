MINTED=_minted.Decidable.gen _minted.Nat.gen _minted.List.gen _minted.Vec.gen _minted.Formula.gen _minted.Ensemble.gen _minted.Deduction.gen _minted.Scheme.gen

MINTCODE='s/\\begin{code}/\\begin{minted}{agda}/; s/\\end{code}/\\end{minted}/'

tome.pdf: tome.tex $(MINTED) agda.sty tome.bbl
	xelatex -shell-escape tome.tex

tome.bbl: tome.tex $(MINTED) agda.sty bib.bib
	xelatex -shell-escape tome.tex
	bibtex tome

agda.sty:
	cp /usr/share/agda/agda.sty .

_minted.%.gen: %.lagda
	sed $(MINTCODE) $< > $@

.PHONY: clean
clean:
	rm *.gen agda.sty tome.bbl tome.blg tome.pdf
	rm -f _minted-tome/*.pygtex _minted-tome/*.pygstyle
	rmdir _minted-tome
