all: linear-constraints.pdf

clean:
	rm -f *.tex *.aux *.bbl *.ptb *.pdf *.toc *.out *.run.xml

%.tex: %.lhs
	lhs2TeX -o $@ $<

%.pdf: %.tex
	cd $(dir $<) && latexmk $(notdir $*)
