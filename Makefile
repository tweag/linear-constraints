# To continuously build the pdf, here is a one-liner
#
# $ while inotifywait -e modify linear-constraints.lhs; do make; done
#
# With nix
#
# $ while inotifywait -e modify linear-constraints.lhs shell.nix; do nix-shell --pure --run make; done

all: linear-constraints.pdf

clean:
	rm -f *.tex *.aux *.bbl *.ptb *.pdf *.toc *.out *.run.xml

%.tex: %.lhs
	lhs2TeX -o $@ $<

%.pdf: %.tex bibliography.bib
	cd $(dir $<) && latexmk $(notdir $*)
