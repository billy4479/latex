OUTDIR = build

.PHONY: all build clean

all: build

build:
	latexmk \
		-lualatex \
		-shell-escape \
		-auxdir=${OUTDIR}/aux \
		-outdir=${OUTDIR} \
		-interaction=nonstopmode \
		*.tex

clean:
	latexmk -C
	rm -f *.bbl *.run.xml *.synctex.gz *.pdfsync *.fls *.fdb_latexmk *.aux *.log *.out *.blg *.bcf *.toc *.lof *.lot *.nav *.snm *.vrb *.pdf
	rm -rf build svg-inkscape _minted-*