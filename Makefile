.PHONY: clean

default: paper.pdf

latex/paper.tex: paper.lagda
	agda --latex $<
	sed -i "s/{code}/{myagda}/g" latex/paper.tex
	sed -i "s/@/@@/g" latex/paper.tex
	sed -i "s/\AgdaSymbol{|}/\AgdaSymbol{||}/g" latex/paper.tex

paper.tex: latex/paper.tex lib.fmt
	lhs2TeX --agda $< > $@

#paper.tex: paper.lagda lib.fmt
#	lhs2TeX --agda $< > $@

agda.sty: latex/agda.sty
	cp $< $@

%.pdf : %.tex main.bib agda.sty
	latexmk -pdf $<

clean:
	rm -f paper.tex
	rm -f *.aux
	rm -f *.fdb_latexmk
	rm -f *.fls
	rm -f *.log
	rm -f *.out
	rm -f *.ptb
	rm -f paper.pdf
	rm -f *.zip
	rm -f *.bbl
	rm -f *.blg
	rm -f *.pag
	rm -f *.vtc
	rm -f latex/paper.tex
	rm -f agda.sty
