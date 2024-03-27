all: build

build:
	latexmk -lualatex -shell-escape *.tex

clean:
	latexmk -c
	rm -f *.bbl *.run.xml *.synctex.gz *.pdfsync *.fls *.fdb_latexmk *.aux *.log *.out *.blg *.bcf *.toc *.lof *.lot *.nav *.snm *.vrb *.pdf