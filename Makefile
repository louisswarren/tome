tome.pdf: tome.tex *.lagda agda.sty
	xelatex tome.tex

agda.sty:
	cp /usr/share/agda/agda.sty .

