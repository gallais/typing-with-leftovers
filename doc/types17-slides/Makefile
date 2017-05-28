SLIDES=types17

all:
	mkdir -p __build
	cp *.tex *.sed __build/
	cd __build/ \
	&& sed -f subst.sed -i ${SLIDES}.tex \
	&& latexmk -shell-escape -pdf -e '$$pdflatex=q/xelatex %O %S/' ${SLIDES}.tex
	ln -sf __build/${SLIDES}.pdf
	xdotool search --class mupdf key --window %@ r > /dev/null 2>&1

clean:
	rm -rf __build/ ${SLIDES}.pdf
