paper:
	mkdir -p __build/
	cp *.tex *.bib *.cls *.sed __build/
	cd __build/ && sed -i -f subst.sed types17.tex && latexmk -bibtex -pdf types17.tex
	ln -sf __build/types17.pdf
	xdotool search --class mupdf key --window %@ r > /dev/null 2>&1

clean:
	rm -rf __build/
