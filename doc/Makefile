all:
	mkdir -p __build/
	rm -f main.pdf
	cp *.tex *.sty *.pdf *.bib *.cls __build/
	cd __build && latexmk -bibtex -pdf main.tex
	ln -sf __build/main.pdf

clean:
	rm -rf __build/ main.pdf
