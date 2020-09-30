parse: parse.hs moo.txt
	ghc parse.hs -o parse
	./parse

docs:
	pdflatex notes.tex
	rm notes.log
	rm notes.aux
	rm notes.out
	evince notes.pdf
