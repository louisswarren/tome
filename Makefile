tome.pdf: tome.tex *.lagda agda.sty
	xelatex tome.tex

agda.sty: agda.sty.arch.patch
	cp /usr/share/agda/agda.sty .
	patch < agda.sty.arch.patch

