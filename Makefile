MINTED=_minted.Decidable.gen _minted.Nat.gen _minted.List.gen _minted.Vec.gen _minted.Formula.gen _minted.Ensemble.gen _minted.Deduction.gen

MINTCODE='s/\\begin{code}/\\begin{minted}{agda}/; s/\\end{code}/\\end{minted}/'

tome.pdf: tome.tex $(MINTED) agda.sty
	xelatex -shell-escape tome.tex

agda.sty:
	cp /usr/share/agda/agda.sty .

_minted.%.gen: %.lagda
	sed $(MINTCODE) $< > $@

.PHONY: clean
clean:
	rm *.gen agda.sty tome.pdf
