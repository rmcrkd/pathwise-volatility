# pdfLaTeX, which arXiv uses for this thesis.
$pdf_mode = 1;
@default_files = ('main.tex');

# Builds in place rather than in a separate output directory, so that BibTeX
# regenerates the tracked main.bbl (the file arXiv consumes) from bib/thesis.bib and
# bibliography changes show up in git. 1 = run BibTeX when the .bib exists,
# and never delete the .bbl on cleanup.
$bibtex_use = 1;
