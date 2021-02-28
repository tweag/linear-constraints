OTT_FILES = grammar.ott rules.ott
OTT_OPTS = -tex_show_meta false -tex_wrap false -picky_multiple_parses false
OTT_TEX = ott.tex

all: linear-constraints.pdf

submission:
	touch no-editing-marks
	$(MAKE) clean
	$(MAKE) linear-constraints-submission.pdf linear-constraints-supplementary.pdf

submission-nix:
	nix-shell --pure --run "make submission"

.PHONY: submission submission-nix

clean:
	rm -f *.aux *.bbl *.ptb *.pdf *.toc *.out *.run.xml

%.lhs: %.mng $(OTT_FILES)
	ott $(OTT_OPTS) -tex_filter $< $@ $(OTT_FILES)

$(OTT_TEX): $(OTT_FILES)
	ott $(OTT_OPTS) -o $@ $^

%.tex: %.lhs
	lhs2TeX -o $@ $<

linear-constraints-submission.pdf: linear-constraints.pdf
	pdftk $< cat 1-27 output temp.pdf
	pdftk $< dump_data_utf8 | pdftk temp.pdf update_info_utf8 - output $@
	rm -f temp.pdf

linear-constraints-supplementary.pdf: linear-constraints.pdf
	pdftk $< cat 28-end output $@

%.pdf: %.tex bibliography.bib $(OTT_TEX)
	cd $(dir $<) && latexmk $(notdir $*)

nix::
	nix-shell --pure --run make

continous-nix:: nix
	nix-shell --run "while inotifywait -e modify linear-constraints.mng $(OTT_FILES) shell.nix; do make nix; done"
