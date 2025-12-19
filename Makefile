.PHONY: clean

default: paper.pdf

latex/paper.tex: paper.lagda
	agda --latex $<
	sed -i "s/{code}/{myagda}/g" latex/paper.tex
	sed -i "s/@/@@/g" latex/paper.tex

paper.tex: latex/paper.tex lib.fmt
	lhs2TeX --agda $< > $@

#paper.tex: paper.lagda lib.fmt
#	lhs2TeX --agda $< > $@

agda.sty: latex/agda.sty
	cp $< $@

%.pdf : %.tex main.bib agda.sty
	latexmk -pdf $<

clean:
	rm paper.tex || true
	rm *.aux || true
	rm *.fdb_latexmk || true
	rm *.fls || true
	rm *.log || true
	rm *.out || true
	rm *.ptb || true
	rm paper.pdf || true
	rm *.zip || true
	rm *.bbl || true
	rm *.blg || true
	rm *.pag || true
	rm *.vtc || true
	rm latex/paper.tex || true
	rm agda.sty
