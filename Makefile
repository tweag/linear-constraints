# To continuously build the pdf, here is a one-liner
#
# $ while inotifywait -e modify linear-constraints.lhs; do make; done
#
# With nix
#
# $ while inotifywait -e modify linear-constraints.lhs shell.nix; do nix-shell --pure --run make; done

OTT_FILES = grammar.ott rules.ott
OTT_OPTS = -tex_show_meta false -tex_wrap false -picky_multiple_parses false
OTT_TEX = ott.tex

all: linear-constraints.pdf

clean:
	rm -f *.tex *.aux *.bbl *.ptb *.pdf *.toc *.out *.run.xml

%.lhs: %.mng $(OTT_FILES)
	ott $(OTT_OPTS) -tex_filter $< $@ $(OTT_FILES)

$(OTT_TEX): $(OTT_FILES)
	ott $(OTT_OPTS) -o $@ $^

%.tex: %.lhs
	lhs2TeX -o $@ $<

%.pdf: %.tex bibliography.bib $(OTT_TEX)
	cd $(dir $<) && latexmk $(notdir $*)

nix::
	nix-shell --pure --run make

continous-nix:: nix
	nix-shell --run "while inotifywait -e modify linear-constraints.lhs shell.nix; do make nix; done"

