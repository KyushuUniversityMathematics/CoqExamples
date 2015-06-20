.SUFFIXES: .tex .v .pdf
.v.tex:
	coqdoc -latex -utf8 --bodyonly $<
.tex.pdf:
	latexmk -pdfdvi $<

sources = 01CertifiedFunction.v 02DeMorgansLaw.v 03ElementaryTactics.v 04TPPmark2014.v
intermediates = 01CertifiedFunction.tex 02DeMorgansLaw.tex 03ElementaryTactics.tex 04TPPmark2014.tex

all: $(intermediates) CoqExercise.tex
	coqdoc -latex -utf8 --bodyonly $<
	latexmk -pdfdvi CoqExercise.tex
open:
	open CoqExercise.pdf
clean:
	-rm *.fls *.dvi *.log *.aux *.toc *~ *.fdb_latexmk \
		*.glob *.v.d *.out *.ps *.sol
	-rm $(intermediates)
cleanall:
	make clean
	-rm CoqExercise.pdf coqdoc.sty


