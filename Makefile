OTT_FILES = grammar.ott rules.ott
OTT_OPTS = -tex_show_meta false -tex_wrap false -picky_multiple_parses false -tex_suppress_ntr Q
OTT_TEX = ott.tex

all: linear-constraints.pdf

submission:
	touch no-editing-marks
	$(MAKE) clean
	$(MAKE) linear-constraints-submission.pdf linear-constraints-supplementary.pdf

# Manual steps to submit to Arxiv:
# - the no-editing-mark trick isn't used on Arxiv submission. Make
#   sure that the editing marks are deactivated. Or that there is no
#   mark left in the pdf.
arxiv:
	$(MAKE) clean
	$(MAKE) linear-constraints.tar.gz

arxiv-nix:
	nix-shell --pure --run "make arxiv"

submission-nix:
	nix-shell --pure --run "make submission"

.PHONY: submission submission-nix

clean:
	rm -f *.aux *.bbl *.ptb *.pdf *.toc *.out *.run.xml
	rm -f *.log *.bcf *.fdb_latexmk *.fls *.blg
	rm -f linear-constraints.pdf
	rm -f linear-constraints.lhs
	rm -f linear-constraints.tex
	rm -f linear-constraints.tar.gz

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

linear-constraints.tar.gz: linear-constraints.tex linear-constraints.bbl newunicodedefs.tex ott.tex ottalt.sty listproc.sty acmart.cls acmauthoryear.bbx acmauthoryear.cbx acmdatamodel.dbx
	tar -cvzf $@ $^

%.pdf %.bbl : %.tex bibliography.bib $(OTT_TEX)
	cd $(dir $<) && latexmk $(notdir $*)

nix::
	nix-shell --pure --run make

continous-nix:: nix
	nix-shell --pure --run "ls linear-constraints.mng bibliography.bib $(OTT_FILES) | entr make"

.SECONDARY:
# the line above prevents deletion of temporary files, which can be helpful for debugging build problems
