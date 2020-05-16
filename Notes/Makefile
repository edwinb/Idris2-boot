# Makefile to render documents

CC=pandoc
DOCS=implementation-notes.md Directives.md IDE-mode.md
PDFS=$(patsubst %.md,%.pdf,$(DOCS))

%.pdf: %.md
	$(CC) $< -o $@

all: $(PDFS)

clean:
	rm $(PDFS)