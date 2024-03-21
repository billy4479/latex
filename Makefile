all: build

build:
	latexmk -lualatex -shell-escape *.tex