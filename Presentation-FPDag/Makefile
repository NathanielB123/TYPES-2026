.PHONY: default update clean

default: main.pdf

latex/Presentation-FPDag/presentation.tex: presentation.lagda
	agda --latex $<
	sed -i "s/{code}/{myagda}/g" latex/Presentation-FPDag/presentation.tex
	sed -i "s/@/@@/g" latex/Presentation-FPDag/presentation.tex
	sed -i "s/\AgdaSymbol{|}/\AgdaSymbol{||}/g" latex/Presentation-FPDag/presentation.tex

Emojis/AAA.pdf: Emojis/AAA.tex
	latexmk -xelatex $< -jobname=Emojis/AAA

Emojis/Think.pdf: Emojis/Think.tex
	latexmk -xelatex $< -jobname=Emojis/Think

Emojis/Sad.pdf: Emojis/Sad.tex
	latexmk -xelatex $< -jobname=Emojis/Sad

presentation.tex: latex/Presentation-FPDag/presentation.tex lib.fmt
	lhs2TeX --agda $< > $@

agda.sty: latex/agda.sty
	cp $< $@

main.pdf : presentation.tex main.bib agda.sty Emojis/AAA.pdf Emojis/Think.pdf  Emojis/Sad.pdf
	latexmk -pdf $<

# main.tex : presentation.lagda lib.fmt
# 	lhs2TeX --agda $< > $@

clean:
	rm -f *.aux
	rm -f *.log
	rm -f *.out
	rm -f *.pdf
	rm -f *.toc
	rm -f *.bbl
	rm -f *.blg
	rm -f *.ptb
	rm -f *.mw
	rm -f *.run.xml
	rm -f *.bcf
	rm -f *.fdb_latexmk
	rm -f *.fls
	rm -f *.nav
	rm -f *.snm
	rm -f *.bbl-SAVE-ERROR
	rm -f *.bcf-SAVE-ERROR
	rm -f latex/Presentation-FPDag/presentation.tex
	rm -f presentation.tex
	rm -f ./Emojis/*.aux
	rm -f ./Emojis/*.fdb_latexmk
	rm -f ./Emojis/*.fls
	rm -f ./Emojis/*.log
	rm -f ./Emojis/*.pdf
	rm -f ./Emojis/*.xdv
