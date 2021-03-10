$pdf_mode = "1";
$pdflatex = "xelatex --shell-escape -halt-on-error -interaction nonstop -file-line-error";
$clean_ext = "bbl synctex.gz synctex.gz(busy)";

# When a file required for the compilation of the main latex file
# (such as an image for `\includegraphics`) latexmk will call `make`
# in order to have it built.
#
# This option is not suitable for Arxiv submission, so it's better to
# explicitly build the dependencies in the Makefile.
#
# $use_make_for_missing_files = "1";
